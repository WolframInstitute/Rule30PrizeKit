module

public import Ruliology.CellularAutomata.Rule30MixedGapClocks
public import Ruliology.CellularAutomata.Rule30Certificates.SevenNineReset

/-!
# Seven- and nine-white gaps: a ten-gap reset excludes infinitely many centre clocks

Write `pulse q` for one black tick followed by `q` white ticks, and `blocks qs` for the pulses of a list of gaps
(`Rule30MixedGapClocks`). `EventuallyWord w` says that the centre column of Rule 30 from a single black cell equals
`w` repeated from some time on. A gap is safe when it is seven or at least nine (`Rule30MixedGapClocks.Strip.Safe`).

* `reset_motif`: the ten gaps `9, 9, 7, 9, 9, 7, 9, 9, 7, 9` carry Galindo's width-12 invariant set `F` into his
  set `E`, for both colours of the exterior cell at every one of the 94 ticks. The masks are in
  `Rule30Certificates.SevenNineReset`.
* `excludes_motif`: for any two finite lists of safe gaps, the centre cannot eventually repeat the first list, then
  the motif, then the second. Since a later onset turns any rotation into this one, no phase of such a cyclic
  word occurs either.
* `excludes_of_reset`, `excludes_of_iterate`: the criterion behind it. Any nonempty list of safe gaps that carries
  `F` into `E`, between any two safe lists, is excluded; so is any cyclic list of safe gaps whose repetition does.
  The motif is the unique shortest reset using only gaps of seven and nine, by finite enumeration.
  `excludes_cyclic` covers a motif appearing inside two copies of the written period.
* `seven_nine_family`: in particular the motif followed by `m` seven-white gaps is excluded for every `m`. These
  words use only gaps of seven and nine; for `m ≥ 2` the run of `m` sevens occurs once in each cycle, so their least
  periods `94 + 8 m` are all different.
* `nine_nine_seven`: the 28-tick clock `1 0^9 1 0^9 1 0^7`, whose fourfold repetition contains the motif
  (`eventuallyWord_twice`).

`Rule30MixedGapClocks` excludes safe lists that contain a gap of at least 22. This module reaches lists with no long
gap by the same passage from `F` into `E` and the same ranking on `E` (`ranked_gaps`, `no_word_ranked`).
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30SevenNineReset

open Ruliology.CellularAutomata Rule30StripCertificates Rule30RunEnvelopes
open Rule30RankedWords Rule30MixedGapClocks Rule30MixedGapClocks.Strip
open Rule30MixedGapClocks.Rank

def motif : List Nat := [9, 9, 7, 9, 9, 7, 9, 9, 7, 9]


private def check : List Bool → Nat → List Nat → Bool
  | [], a, [] => a &&& E == a
  | c :: w, a, b :: rest => covers 12 c a b && check w b rest
  | _, _, _ => false

private theorem sound (w : List Bool) (a : Nat) (ms : List Nat)
    (h : check w a ms = true) : Sub (applyWord 12 w a) E := by
  induction w generalizing a ms with
  | nil =>
    cases ms with
    | cons => simp [check] at h
    | nil =>
      have eq : a &&& E = a := beq_iff_eq.mp h
      intro i hi
      change a.testBit i = true at hi
      have v := congrArg (fun n : Nat => n.testBit i) eq
      simpa only [Nat.testBit_and, hi, Bool.true_and] using v
  | cons c w ih =>
    cases ms with
    | nil => simp [check] at h
    | cons b rest =>
      obtain ⟨hstep, htail⟩ := Bool.and_eq_true_iff.mp h
      exact cover_cons (covers_sound hstep) (ih b rest htail)

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem reset_motif : Sub (applyWord 12 (blocks motif) F) E :=
  sound _ _ Data.masks (by decide +kernel)

/-- Any written period containing the motif, with arbitrary other gaps of
seven or at least nine whites, is excluded at every singleton onset. -/
theorem excludes_motif (left right : List Nat)
    (hl : ∀ q ∈ left, Safe q) (hr : ∀ q ∈ right, Safe q) :
    ¬ EventuallyWord (blocks (left ++ motif ++ right)) := by
  let qs := left ++ motif ++ right
  have safe : ∀ q ∈ qs, Safe q := by
    intro q h
    rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · exact hl _ h
      · have fixed : motif.all (fun x => x == 7 || decide (9 ≤ x)) = true := by decide
        simpa [Safe] using List.all_eq_true.mp fixed q h
    · exact hr _ h
  have hn : qs ≠ [] := by simp [qs, motif]
  have hp : 0 < (blocks qs).length := by
    cases he : qs with
    | nil => exact (hn he).elim
    | cons q rest => simp [blocks, pulse]
  have cap : Sub (applyWord 12 (blocks qs) F) E := by
    simp only [qs, blocks, List.flatMap_append, apply_append]
    exact sub_trans (word_mono 12
      (sub_trans (word_mono 12 (preserves F stableF left hl) _) reset_motif) _)
      (preserves E stableE right hr)
  obtain ⟨g, ranked⟩ := ranked_gaps qs safe
  apply no_word_ranked 12 E 2 (fun _ => 0) (blocks qs) g hp _ ranked
  exact sub_trans (word_mono 12 (first_period qs hn safe) _) cap

/-- A family that uses only seven- and nine-white gaps: the motif followed by `m` seven-white gaps. -/
theorem seven_nine_family (m : Nat) : ¬ EventuallyWord (blocks (motif ++ List.replicate m 7)) := by
  have h := excludes_motif [] (List.replicate m 7) (by simp)
    (fun q hq => Or.inl (List.eq_of_mem_replicate hq))
  simpa using h

/-- An eventual word is also an eventual word when written twice. -/
theorem eventuallyWord_twice {w : List Bool} (h : EventuallyWord w) : EventuallyWord (w ++ w) := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T, fun t ht => ?_⟩
  rw [hT t ht]
  rcases Nat.eq_zero_or_pos w.length with hz | hp
  · simp [List.length_eq_zero_iff.mp hz]
  · have hl : (w ++ w).length = 2 * w.length := by simp; omega
    rw [hl]
    have hm : (t - T) % (2 * w.length) % w.length = (t - T) % w.length :=
      Nat.mod_mod_of_dvd _ (Nat.dvd_mul_left _ _)
    have hlt : (t - T) % (2 * w.length) < 2 * w.length := Nat.mod_lt _ (by omega)
    by_cases hi : (t - T) % (2 * w.length) < w.length
    · rw [← hm, Nat.mod_eq_of_lt hi]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
    · have hge : w.length ≤ (t - T) % (2 * w.length) := by omega
      rw [← hm, Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hge]

/-- The 28-tick clock `1 0^9 1 0^9 1 0^7`: four periods contain the motif. -/
theorem nine_nine_seven : ¬ EventuallyWord (blocks [9, 9, 7]) := by
  intro h
  have h4 := eventuallyWord_twice (eventuallyWord_twice h)
  have e : blocks [9, 9, 7] ++ blocks [9, 9, 7] ++ (blocks [9, 9, 7] ++ blocks [9, 9, 7]) =
      blocks ([] ++ motif ++ [9, 7]) := by decide
  rw [e] at h4
  exact excludes_motif [] [9, 7] (by simp)
    (fun q hq => by simp at hq; rcases hq with rfl | rfl <;> simp [Safe]) h4

/-- **The criterion.** Any list of safe gaps that carries `F` into `E`, between any two lists of safe gaps. -/
theorem excludes_of_reset (u left right : List Nat) (hne : u ≠ []) (hu : ∀ q ∈ u, Safe q)
    (hl : ∀ q ∈ left, Safe q) (hr : ∀ q ∈ right, Safe q)
    (reset : Sub (applyWord 12 (blocks u) F) E) :
    ¬ EventuallyWord (blocks (left ++ u ++ right)) := by
  let qs := left ++ u ++ right
  have safe : ∀ q ∈ qs, Safe q := by
    intro q h
    rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · exact hl _ h
      · exact hu _ h
    · exact hr _ h
  have hn : qs ≠ [] := by simp [qs, hne]
  have hp : 0 < (blocks qs).length := by
    cases he : qs with
    | nil => exact (hn he).elim
    | cons q rest => simp [blocks, pulse]
  have cap : Sub (applyWord 12 (blocks qs) F) E := by
    simp only [qs, blocks, List.flatMap_append, apply_append]
    exact sub_trans (word_mono 12
      (sub_trans (word_mono 12 (preserves F stableF left hl) _) reset) _)
      (preserves E stableE right hr)
  obtain ⟨g, ranked⟩ := ranked_gaps qs safe
  apply no_word_ranked 12 E 2 (fun _ => 0) (blocks qs) g hp _ ranked
  exact sub_trans (word_mono 12 (first_period qs hn safe) _) cap

theorem iter_mono (w : List Bool) : ∀ k {A B : Nat}, Sub A B → Sub (iterW 12 w k A) (iterW 12 w k B)
  | 0, _, _, h => h
  | k + 1, _, _, h => iter_mono w k (word_mono 12 h w)

/-- **The repeated criterion.** A cyclic list of safe gaps whose `k`-fold repetition carries `F` into `E`. -/
theorem excludes_of_iterate (qs : List Nat) (safe : ∀ q ∈ qs, Safe q) (hn : qs ≠ []) (k : Nat)
    (reset : Sub (iterW 12 (blocks qs) k F) E) : ¬ EventuallyWord (blocks qs) := by
  have hp : 0 < (blocks qs).length := by
    cases he : qs with
    | nil => exact (hn he).elim
    | cons q rest => simp [blocks, pulse]
  obtain ⟨g, ranked⟩ := ranked_gaps qs safe
  apply no_word_ranked 12 E (k + 1) (fun _ => 0) (blocks qs) g hp _ ranked
  exact sub_trans (iter_mono (blocks qs) k (first_period qs hn safe)) reset

/-- **The motif across the seam.** A cyclic list of safe gaps that contains the motif cyclically. -/
theorem excludes_cyclic (qs l r : List Nat) (safe : ∀ q ∈ qs, Safe q) (h : qs ++ qs = l ++ motif ++ r) :
    ¬ EventuallyWord (blocks qs) := by
  intro hw
  have h2 := eventuallyWord_twice hw
  have e : blocks qs ++ blocks qs = blocks (l ++ motif ++ r) := by
    rw [← h]; simp [blocks, List.flatMap_append]
  rw [e] at h2
  have hs : ∀ q ∈ l ++ motif ++ r, Safe q := by
    intro q hq
    rw [← h] at hq
    rcases List.mem_append.mp hq with h1 | h1 <;> exact safe q h1
  exact excludes_motif l r (fun q hq => hs q (by simp [hq])) (fun q hq => hs q (by simp [hq])) h2

end Ruliology.CellularAutomata.Rule30SevenNineReset
