module

public import Ruliology.CellularAutomata.Rule30Certificates.MixedGapClocks
public import Ruliology.CellularAutomata.Rule30Certificates.MixedGapClocksSeven
public import Ruliology.CellularAutomata.Rule30RankedWords

/-!
# Excluding cyclic mixtures of isolated black ticks with seven-white gaps

For every finite list of gaps, each equal to seven or at least nine and some at least 22,
the pulse blocks of this list cannot form an eventual period of the singleton center.
The independent rank certificate imported here also excludes the pure seven-white clock.

Contributors: Dusty Galindo; OpenAI Codex (GPT-6.2 Astra).
-/

@[expose] public section

/-! The invariant twelve-cell strip prescribes the masked response to each admissible pulse
and to each concatenation of them. -/
namespace Ruliology.CellularAutomata.Rule30MixedGapClocks.Rank
open Ruliology.CellularAutomata Rule30StripCertificates Rule30RunEnvelopes Rule30RankedWords
open Rule30Jen Rule30MaskedJen

def pulse (q : Nat) : List Bool := true :: List.replicate q false

theorem apply_whites (q A : Nat) : applyWord 12 (List.replicate q false) A = Strip.W q A := by
  induction q with
  | zero => rfl
  | succ q ih => rw [whites_add 12 q 1 A,ih]; rfl

theorem apply_pulse (q A : Nat) : applyWord 12 (pulse q) A = Strip.mac q A :=
  apply_whites q _

private theorem reads_take {t : Nat} {w : List Bool} (h : Reads t w) (i : Nat) :
    Reads t (w.take i) := by
  intro k hk
  have hi : k<i := by simp only [List.length_take] at hk; omega
  have hw : k<w.length := by simp only [List.length_take] at hk; omega
  simpa [List.getD_eq_getElem?_getD,List.getElem?_take,hi] using h k hw

/-- The black letter has masked output true. Within the ensuing white run the third and all
later white phases have output true. -/
theorem ranked_pulse (q : Nat) (safe : Strip.Safe q) :
    Ranked 12 Strip.E (fun _ => 0) (pulse q) (fun _ i => decide (i=0 ∨ 3≤i)) := by
  intro t h hs
  have end_mem := code_word h hs
  rw [apply_pulse] at end_mem
  refine ⟨Strip.stableE q safe _ end_mem,Nat.le_refl _,fun _ i hi => ?_⟩
  have hc := h i hi
  cases i with
  | zero =>
    have hc' : cell t 0=true := by simpa [pulse] using hc
    simp [orCol,hc']
  | succ j =>
    have jq : j<q := by simpa [pulse] using hi
    have hc' : cell (t+(j+1)) 0=false := by simpa [pulse,List.getD_eq_getElem?_getD,List.getElem?_replicate,jq] using hc
    have cut_eq : (pulse q).take (j+1)=pulse j := by simp [pulse,List.take_replicate,Nat.min_eq_left (by omega : j≤q)]
    have mid := code_word (reads_take h (j+1)) hs
    rw [cut_eq,apply_pulse] at mid
    have hm : (Strip.mac j Strip.E).testBit (code 12 (t+(j+1)))=true := by
      simpa [pulse] using mid
    have val := Strip.mask j (code 12 (t+(j+1))) (enc_encRow 12 _ 0).1 hm
    have bit := (enc_encRow 12 (t+(j+1)) 0).2 0 (by decide)
    change (code 12 (t+(j+1))).testBit 0=cell (t+(j+1)) 1 at bit
    rw [bit] at val
    simp [orCol,hc',val,show (3≤j+1) ↔ 2≤j by omega]

/-- A single phase table exists for every listed concatenation, including the empty one. -/
theorem ranked_gaps (gaps : List Nat) (safe : ∀ q ∈ gaps, Strip.Safe q) :
    ∃ g, Ranked 12 Strip.E (fun _ => 0) (gaps.flatMap pulse) g := by
  induction gaps with
  | nil => exact ⟨fun _ _ => false,ranked_nil _ _ _ _⟩
  | cons q qs ih =>
    obtain ⟨g,hg⟩ := ih (fun r hr => safe r (by simp [hr]))
    exact ⟨_,ranked_append (ranked_pulse q (safe q (by simp))) hg⟩

end Ruliology.CellularAutomata.Rule30MixedGapClocks.Rank

/-! Excluding periodic mixtures of isolated black ticks for the singleton center.
The two finite sets and their masked responses are certified in Strip. -/

namespace Ruliology.CellularAutomata.Rule30MixedGapClocks
open Ruliology.CellularAutomata
open Rule30StripCertificates Rule30RunEnvelopes Rule30RankedWords Strip Rank

abbrev blocks (gaps : List Nat) := gaps.flatMap pulse

theorem preserves (B : Nat) (one : ∀ q, Safe q → Sub (mac q B) B)
    (qs : List Nat) (safe : ∀ q ∈ qs, Safe q) : Sub (applyWord 12 (blocks qs) B) B := by
  induction qs with
  | nil => exact sub_refl B
  | cons q qs ih =>
    change Sub (applyWord 12 (pulse q ++ blocks qs) B) B
    rw [apply_append, apply_pulse]
    exact sub_trans (word_mono 12 (one q (safe q (by simp))) _) (ih (fun r hr => safe r (by simp [hr])))

theorem first_period (qs : List Nat) (hn : qs ≠ []) (safe : ∀ q ∈ qs, Safe q) :
    Sub (applyWord 12 (blocks qs) (fullSet 12)) F := by
  cases qs with
  | nil => exact (hn rfl).elim
  | cons q qs =>
    change Sub (applyWord 12 (pulse q ++ blocks qs) (fullSet 12)) F
    rw [apply_append, apply_pulse]
    exact sub_trans (word_mono 12 (entry q (safe q (by simp))) _)
      (preserves F stableF qs (fun r hr => safe r (by simp [hr])))

theorem reset_period (qs : List Nat) (safe : ∀ q ∈ qs, Safe q) (large : ∃ q ∈ qs, 22 ≤ q) :
    Sub (applyWord 12 (blocks qs) F) E := by
  induction qs with
  | nil => obtain ⟨q,h,_⟩ := large; simp at h
  | cons q qs ih =>
    have rest : ∀ r ∈ qs, Safe r := fun r hr => safe r (by simp [hr])
    change Sub (applyWord 12 (pulse q ++ blocks qs) F) E
    rw [apply_append, apply_pulse]
    by_cases h : 22 ≤ q
    · exact sub_trans (word_mono 12 (reset q h) _) (preserves E stableE _ rest)
    · have next : ∃ r ∈ qs, 22 ≤ r := by
        obtain ⟨r,hr,hl⟩ := large
        rcases List.mem_cons.mp hr with he | hm
        · exact (h (he ▸ hl)).elim
        · exact ⟨r,hm,hl⟩
      exact sub_trans (word_mono 12 (stableF q (safe q (by simp))) _) (ih rest next)

/-- The center of the single black cell cannot eventually repeat any such word,
even if the proposed onset is arbitrarily late. -/
theorem excluded (qs : List Nat) (safe : ∀ q ∈ qs, q = 7 ∨ 9 ≤ q)
    (large : ∃ q ∈ qs, 22 ≤ q) : ¬ EventuallyWord (blocks qs) := by
  have hn : qs ≠ [] := by rintro rfl; obtain ⟨q,h,_⟩ := large; simp at h
  have hp : 0 < (blocks qs).length := by
    cases qs with
    | nil => exact (hn rfl).elim
    | cons q qs => simp [blocks, pulse]
  obtain ⟨g,hr⟩ := ranked_gaps qs safe
  apply no_word_ranked 12 E 2 (fun _ => 0) (blocks qs) g hp _ hr
  exact sub_trans (word_mono 12 (first_period qs hn safe) _) (reset_period qs safe large)

/-- One gap of length 22, with any number of gaps of length 7.
The unique long gap identifies a single phase of each cycle. -/
theorem marked_family (m : Nat) :
    ¬ EventuallyWord (blocks (22 :: List.replicate m 7)) := by
  apply excluded
  · intro q h
    rcases List.mem_cons.mp h with he | hm
    · omega
    · exact Or.inl (List.eq_of_mem_replicate hm)
  · exact ⟨22, by simp, by decide⟩

/-- There is a two-gap exclusion with a seven-white gap at every length at least 31. -/
theorem two_gaps (q : Nat) (h : 22 ≤ q) : ¬ EventuallyWord (blocks [7, q]) := by
  apply excluded
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    omega
  · exact ⟨q, by simp, h⟩

end Ruliology.CellularAutomata.Rule30MixedGapClocks
