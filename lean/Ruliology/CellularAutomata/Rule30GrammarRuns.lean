module
public import Ruliology.CellularAutomata.Rule30Certificates.Grammar
public import Ruliology.CellularAutomata.Rule30RankedWords
/-!
# Four-category block grammars

For every nonempty list of blocks `(r, q)`, each with `r = 1, q ≥ 10`, `r = 2, q ≥ 8`, `r = 4, q ≥ 7`
or `r ≥ 9, q ≥ 9`, chosen independently, the single-seed center column is not eventually the
repeating word `1^(r₁) 0^(q₁) … 1^(rₖ) 0^(qₖ)`, whatever the transient (`not_eventually_grammar`).
The number of blocks and every run length in the unbounded categories are arbitrary.

Four capture stages take every fourteen-cell strip into an envelope `E` of 1791 strips, split into
seven rank regions (`Rule30GrammarData`). No admissible block raises the rank (`rank_block`), and a
rank-keeping block starts at rank `0`, or at rank `6` with `r = 4`; its column-1 response along the
white run is then prescribed (`ranked_driver`). The composition rule `Rule30RankedWords.no_word_ranked`
concludes through masked Jen.
-/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30GrammarRuns
open Rule30StripCertificates Rule30RunEnvelopes Rule30RankedWords Rule30GrammarData
open Rule30Jen Rule30MaskedJen

def Good (a : Nat × Nat) : Prop := Admissible a.1 a.2
abbrev driver (a : Nat × Nat) : List Bool := word a.1 a.2
def blocks (as : List (Nat × Nat)) : List Bool := as.flatMap driver

theorem rank_block (t r q : Nat) (hg : Admissible r q)
    (h : Reads t (word r q)) (hs : E.testBit (code 14 t) = true) :
    E.testBit (code 14 (t + (word r q).length)) = true ∧
    rank (code 14 (t + (word r q).length)) ≤ rank (code 14 t) ∧
    (rank (code 14 (t + (word r q).length)) = rank (code 14 t) →
      rank (code 14 t) = 0 ∨ (rank (code 14 t) = 6 ∧ r = 4)) := by
  have hslt : code 14 t < 2^14 := (enc_encRow 14 t 0).1
  obtain ⟨hbound,hregion⟩ := partition (code 14 t) hslt hs
  have hendlt : code 14 (t + (word r q).length) < 2^14 :=
    (enc_encRow 14 (t + (word r q).length) 0).1
  have cases : rank (code 14 t) = 0 ∨ rank (code 14 t) = 1 ∨
    rank (code 14 t) = 2 ∨ rank (code 14 t) = 3 ∨ rank (code 14 t) = 4 ∨
    rank (code 14 t) = 5 ∨ rank (code 14 t) = 6 := by omega
  rcases cases with hj | hj | hj | hj | hj | hj | hj
  · rw [hj] at hregion ⊢
    have hm := code_word h hregion
    have hh := target0 _ hendlt (advance0 r q hg _ hm)
    exact ⟨hh.1,hh.2,fun _ => Or.inl rfl⟩
  · rw [hj] at hregion ⊢
    have hm := code_word h hregion
    have hh := target1 _ hendlt (advance1 r q hg _ hm)
    exact ⟨hh.1,by omega,fun he => by omega⟩
  · rw [hj] at hregion ⊢
    have hm := code_word h hregion
    have hh := target2 _ hendlt (advance2 r q hg _ hm)
    exact ⟨hh.1,by omega,fun he => by omega⟩
  · rw [hj] at hregion ⊢
    have hm := code_word h hregion
    have hh := target3 _ hendlt (advance3 r q hg _ hm)
    exact ⟨hh.1,by omega,fun he => by omega⟩
  · rw [hj] at hregion ⊢
    have hm := code_word h hregion
    have hh := target4 _ hendlt (advance4 r q hg _ hm)
    exact ⟨hh.1,by omega,fun he => by omega⟩
  · rw [hj] at hregion ⊢
    have hm := code_word h hregion
    have hh := target5 _ hendlt (advance5 r q hg _ hm)
    exact ⟨hh.1,by omega,fun he => by omega⟩
  · rw [hj] at hregion ⊢
    have hm := code_word h hregion
    have hh := target6 _ hendlt (advance6 r q hg _ hm)
    refine ⟨hh.1,hh.2,fun he => ?_⟩
    have hr4 : r = 4 := by
      by_cases hn : r = 4
      · exact hn
      have hx := exitTarget6 _ hendlt (exit6 r q hg hn _ hm)
      omega
    exact Or.inr ⟨rfl,hr4⟩

def delayAt (j r : Nat) : Nat := if j = 6 then 1 else delay r

def response (a : Nat × Nat) (j i : Nat) : Bool :=
  if i < a.1 then true else decide (delayAt j a.1 ≤ i - a.1)

theorem reads_take {t : Nat} {w : List Bool} (h : Reads t w) (i : Nat) :
    Reads t (w.take i) := by
  intro k hk
  have hk' : k < w.length := by simp only [List.length_take] at hk; omega
  have hh := h k hk'
  simpa [List.getD_eq_getElem?_getD,List.getElem?_take,
    show k < i by simp only [List.length_take] at hk; omega] using hh

theorem driver_observation (t r q j : Nat) (h : Reads t (word r q))
    (hs : (region j).testBit (code 14 t) = true)
    (hp : ∀ i, Const 14 (applyWord 14 (List.replicate i false)
      (applyWord 14 (List.replicate r true) (region j))) (decide (delayAt j r ≤ i))) :
    ∀ i, i < (word r q).length → orCol 0 (t+i) = response (r,q) j i := by
  intro i hi
  have hc := h i hi
  rw [word_getD] at hc
  unfold orCol response
  simp only [Int.zero_add]
  rw [hc]
  by_cases hir : i < r
  · simp [hir]
  · have htake : (word r q).take i =
        List.replicate r true ++ List.replicate (i-r) false := by
      have hi' : i-r ≤ q := by
        simp only [word,List.length_append,List.length_replicate] at hi
        omega
      simp [word,List.take_append,List.take_replicate,
        Nat.min_eq_right (by omega : r ≤ i),Nat.min_eq_left hi']
    have hm := code_word (reads_take h i) hs
    rw [List.length_take,Nat.min_eq_left (Nat.le_of_lt hi),htake,apply_append] at hm
    have hh := hp (i-r) (code 14 (t+i)) (enc_encRow 14 (t+i) 0).1 hm
    have hb := (enc_encRow 14 (t+i) 0).2 0 (by decide)
    change (code 14 (t+i)).testBit 0 = cell (t+i) 1 at hb
    simpa [hir,←hb] using hh

theorem ranked_driver (a : Nat × Nat) (ha : Good a) :
    Ranked 14 E rank (driver a) (response a) := by
  intro t ht hs
  obtain ⟨he,hle,hallow⟩ := rank_block t a.1 a.2 ha ht hs
  refine ⟨he,hle,fun heq => ?_⟩
  have hreg := (partition _ (enc_encRow 14 t 0).1 hs).2
  apply driver_observation t a.1 a.2 (rank (code 14 t)) ht hreg
  intro i
  rcases hallow heq with h0 | ⟨h6,hr⟩
  · simpa [h0,region,delayAt] using profile a.1 a.2 ha i
  · simpa [h6,hr,region,delayAt] using exception6 i

def outputs : List (Nat × Nat) → Nat → Nat → Bool
  | [],_,_ => false
  | a::as,j,i => if i < (driver a).length then response a j i
      else outputs as j (i-(driver a).length)

theorem ranked_blocks (as : List (Nat × Nat)) (ha : ∀ a ∈ as, Good a) :
    Ranked 14 E rank (blocks as) (outputs as) := by
  induction as with
  | nil => exact ranked_nil 14 E rank _
  | cons a as ih =>
    have h0 := ha a (by simp)
    have has : ∀ b ∈ as, Good b := fun b hb => ha b (by simp [hb])
    exact ranked_append (ranked_driver a h0) (ih has)

theorem stableA1 (a : Nat × Nat) (ha : Good a) : Sub (applyWord 14 (driver a) A1) A1 :=
  sub_trans (word_mono 14 nested1 _) (capture0 a.1 a.2 ha)

theorem stableA2 (a : Nat × Nat) (ha : Good a) : Sub (applyWord 14 (driver a) A2) A2 :=
  sub_trans (word_mono 14 nested2 _) (capture1 a.1 a.2 ha)

theorem stableA3 (a : Nat × Nat) (ha : Good a) : Sub (applyWord 14 (driver a) A3) A3 :=
  sub_trans (word_mono 14 nested3 _) (capture2 a.1 a.2 ha)

theorem stableE (a : Nat × Nat) (ha : Good a) : Sub (applyWord 14 (driver a) E) E :=
  sub_trans (word_mono 14 nested4 _) (capture3 a.1 a.2 ha)

theorem stable_blocks (B : Nat)
    (h : ∀ a, Good a → Sub (applyWord 14 (driver a) B) B)
    (as : List (Nat × Nat)) (ha : ∀ a ∈ as, Good a) :
    Sub (applyWord 14 (blocks as) B) B := by
  induction as with
  | nil => exact sub_refl B
  | cons a as ih =>
    change Sub (applyWord 14 (driver a ++ blocks as) B) B
    rw [apply_append]
    exact sub_trans (word_mono 14 (h a (ha a (by simp))) _)
      (ih (fun b hb => ha b (by simp [hb])))

theorem capture_blocks (A B : Nat)
    (h : ∀ a, Good a → Sub (applyWord 14 (driver a) A) B)
    (stable : ∀ a, Good a → Sub (applyWord 14 (driver a) B) B)
    (as : List (Nat × Nat)) (hne : as ≠ []) (ha : ∀ a ∈ as, Good a) :
    Sub (applyWord 14 (blocks as) A) B := by
  cases as with
  | nil => exact (hne rfl).elim
  | cons a as =>
    change Sub (applyWord 14 (driver a ++ blocks as) A) B
    rw [apply_append]
    exact sub_trans (word_mono 14 (h a (ha a (by simp))) _)
      (stable_blocks B stable as (fun b hb => ha b (by simp [hb])))

theorem blocks_warm (as : List (Nat × Nat)) (hne : as ≠ []) (ha : ∀ a ∈ as, Good a) :
    Sub (iterW 14 (blocks as) 4 (fullSet 14)) E := by
  have h0 := capture_blocks (fullSet 14) A1
    (fun a h => capture0 a.1 a.2 h) stableA1 as hne ha
  have h1 := capture_blocks A1 A2
    (fun a h => capture1 a.1 a.2 h) stableA2 as hne ha
  have h2 := capture_blocks A2 A3
    (fun a h => capture2 a.1 a.2 h) stableA3 as hne ha
  have h3 := capture_blocks A3 E
    (fun a h => capture3 a.1 a.2 h) stableE as hne ha
  have h01 : Sub (iterW 14 (blocks as) 2 (fullSet 14)) A2 :=
    sub_trans (word_mono 14 h0 _) h1
  have h012 : Sub (iterW 14 (blocks as) 3 (fullSet 14)) A3 :=
    sub_trans (word_mono 14 h01 _) h2
  exact sub_trans (word_mono 14 h012 _) h3

/-- Arbitrary independently chosen blocks in four unbounded run categories. -/
theorem not_eventually_grammar (as : List (Nat × Nat)) (hne : as ≠ [])
    (ha : ∀ a ∈ as, (a.1 = 1 ∧ 10 ≤ a.2) ∨ (a.1 = 2 ∧ 8 ≤ a.2) ∨
      (a.1 = 4 ∧ 7 ≤ a.2) ∨ (9 ≤ a.1 ∧ 9 ≤ a.2)) :
    ¬ EventuallyWord (as.flatMap (fun a =>
      List.replicate a.1 true ++ List.replicate a.2 false)) := by
  change ¬ EventuallyWord (blocks as)
  have hgood : ∀ a ∈ as, Good a := ha
  have hw : 0 < (blocks as).length := by
    cases as with
    | nil => exact (hne rfl).elim
    | cons a as =>
      have h := admissible_pos (hgood a (by simp))
      change 0 < (driver a ++ blocks as).length
      simp only [List.length_append,word,List.length_replicate]
      omega
  exact no_word_ranked 14 E 4 rank (blocks as) (outputs as) hw
    (blocks_warm as hne hgood) (ranked_blocks as hgood)

/-! ## Single-block and two-block four-category grammar exclusions and multi-period `iterW` stability -/

/-- **Single-Block and Two-Block Grammar Exclusions and Multi-Period `iterW` Envelope Stability (`grammar_single_and_two_block_and_iterW_E`).** -/
theorem grammar_single_and_two_block_and_iterW_E
    (as : List (Nat × Nat)) (ha : ∀ a ∈ as, Good a) (m r1 q1 r2 q2 : Nat)
    (hg1 : Admissible r1 q1) (hg2 : Admissible r2 q2) :
    Sub (iterW 14 (blocks as) m E) E ∧
    ¬ EventuallyWord (List.replicate r1 true ++ List.replicate q1 false) ∧
    ¬ EventuallyWord ((List.replicate r1 true ++ List.replicate q1 false) ++
                      (List.replicate r2 true ++ List.replicate q2 false)) := by
  have hmono : ∀ (k : Nat) {X Y : Nat}, Sub X Y →
      Sub (iterW 14 (blocks as) k X) (iterW 14 (blocks as) k Y) := by
    intro k
    induction k with
    | zero => intro X Y h; exact h
    | succ k ih => intro X Y h; exact ih (word_mono 14 h (blocks as))
  have hiter : ∀ k : Nat, Sub (iterW 14 (blocks as) k E) E := by
    intro k
    induction k with
    | zero => exact sub_refl E
    | succ k ih =>
      unfold iterW
      exact sub_trans (hmono k (stable_blocks E stableE as ha)) ih
  refine ⟨hiter m, ?_, ?_⟩
  · have h1 := not_eventually_grammar [(r1, q1)] (by simp) (by
      intro a hmem
      have ha1 : a = (r1, q1) := by simpa using hmem
      subst ha1; exact hg1)
    simpa [List.flatMap] using h1
  · have h2 := not_eventually_grammar [(r1, q1), (r2, q2)] (by simp) (by
      intro a hmem
      rcases List.mem_cons.mp hmem with rfl | hmem2
      · exact hg1
      · have ha2 : a = (r2, q2) := by simpa using hmem2
        subst ha2; exact hg2)
    simpa [List.flatMap] using h2

end Ruliology.CellularAutomata.Rule30GrammarRuns
