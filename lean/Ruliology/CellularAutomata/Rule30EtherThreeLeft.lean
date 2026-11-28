module

public import Ruliology.CellularAutomata.Rule30EtherThree
public import Ruliology.CellularAutomata.Rule30DrivenLeft
public import Ruliology.CellularAutomata.Rule30PeriodTwo

/-!
# Rule 30, least period 3: reductions to the left half

If the center column is eventually `001^∞` or `011^∞`, the left half (columns `p < 0`) is, from
that time on, rule 30 driven by the *effective boundary* `c'(t) = c(t) && c(t + 1)`
(`Rule30MaskedJen.effective_step`, `Rule30DrivenLeft.cell_eq_L_effective`), and column `-1` is
forced at the black phases of the center by left permutivity.

* `001`: `c' = 000`, so the left half is the zero-boundary left half (ZBL). Column `-1` is black at
  the black phase and equal to column `1` (phase `0`) or its complement (phase `1`) at the white
  phases (`col_m1_001`). The left-only statement is `Q001`: **no start of the ZBL with a leftmost
  black cell keeps column `-1` black at every third step** (the analog of
  `Rule30PeriodTwo.Q01`). `not_eventually_001_of_Q001`: `Q001` excludes `001^∞` for every
  transient. Finiteness is essential: the stripe keeps column `-1` black forever
  (`Q001_stripe`).
* `011`: `c' = 010`, and column `-1` is (`!` column `1`, white, black) at phases (`0, 1, 2`)
  (`col_m1_011`). The left-only statement is `C3w w011` (the analog of
  `Rule30PeriodFourSkeleton.C3`): **no finitely supported left configuration, driven by the
  boundary `010`, keeps column `-1` equal to `(*, 0, 1)` for all large times.**
  `not_eventually_011_of_C3w`. Finiteness is essential here too: the left part of the
  period-3 ether is a solution for ever (`C3w_011_ether`).

Both statements are open. Evidence (a C search, not kernel-checked):
every start of width `W ≤ 37` violates `Q001`'s constraint by time `94`, and every start of width
`W ≤ 70` violates the `011` constraint by time `99` (all three phases).

For every word `w`, `C3w w` is equivalent to its all-times form `C3w0 w`, which only forbids a
finitely supported start that fits `P_w` at every time (`C3w_iff_C3w0`): a start that fits from
time `K` on gives, after `3 K` steps, a finitely supported row that fits at every time, since the
driver has period `3`. So the reduction for `011` needs only the all-times form
(`not_eventually_011_of_C3w0`), and so does the reduction for `001` through `C3w w001`
(`not_eventually_001_of_C3w0`).
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30EtherThree

open Rule30Jen Rule30Prize Rule30MaskedJen Rule30DrivenLeft

theorem wordAt3_001 (x : Nat) : wordAt3 w001 x = decide (x % 3 = 2) := by
  unfold wordAt3
  have : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by omega
  rcases this with h | h | h <;> rw [h] <;> rfl

theorem wordAt3_011 (x : Nat) : wordAt3 w011 x = decide (1 ≤ x % 3) := by
  unfold wordAt3
  have : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by omega
  rcases this with h | h | h <;> rw [h] <;> rfl

theorem col_m1 (t : Nat) : cell t (-1) = xor (cell (t + 1) 0) (cell t 0 || cell t 1) := by
  have := cell_left t 0
  rw [show (0 : Int) - 1 = -1 by rfl, show (0 : Int) + 1 = 1 by rfl] at this
  exact this

/-! ### The word `001` -/

/-- **Column `-1` under `001`.** If `c(t) = [ (t - T) % 3 = 2 ]` for `t ≥ T`, column `-1` is
(`=` column `1`, `!` column `1`, black) at the phases (`0, 1, 2`). -/
theorem col_m1_001 (T : Nat) (h : ∀ t, T ≤ t → cell t 0 = wordAt3 w001 (t - T)) (t : Nat)
    (ht : T ≤ t) :
    ((t - T) % 3 = 0 → cell t (-1) = cell t 1) ∧
    ((t - T) % 3 = 1 → cell t (-1) = !cell t 1) ∧
    ((t - T) % 3 = 2 → cell t (-1) = true) := by
  have c0 := h t ht
  have c1 := h (t + 1) (by omega)
  rw [wordAt3_001] at c0 c1
  rw [show t + 1 - T = (t - T) + 1 by omega] at c1
  refine ⟨fun hφ => ?_, fun hφ => ?_, fun hφ => ?_⟩
  · rw [col_m1, c1, c0, show ((t - T) + 1) % 3 = 1 by omega, hφ]; cases cell t 1 <;> rfl
  · rw [col_m1, c1, c0, show ((t - T) + 1) % 3 = 2 by omega, hφ]; cases cell t 1 <;> rfl
  · rw [col_m1, c1, c0, show ((t - T) + 1) % 3 = 0 by omega, hφ]; rfl

/-- **`Q001`** (open). No start of the zero-driven left half with a leftmost black cell (at `-m`,
`m ≥ 1`, white beyond) keeps column `-1` black at every third step. -/
def Q001 : Prop :=
  ∀ (m : Nat) (s : Int → Bool), 0 < m → (∀ p : Int, p < -(m : Int) → s p = false) →
    s (-(m : Int)) = true → ¬ ∀ k, L (fun _ => false) s (3 * k) (-1) = true

/-- **`Q001` excludes `001^∞`** as a tail of the center column, for every transient. -/
theorem not_eventually_001_of_Q001 (hQ : Q001) :
    ¬ ∃ T, ∀ t, T ≤ t → cell t 0 = wordAt3 w001 (t - T) := by
  rintro ⟨T, hT⟩
  -- start at a black phase, at least one step in
  let T' := T + 5
  have hfun : (fun k => center (T' + k) && center (T' + k + 1)) = fun _ => false := by
    funext k
    show (cell (T' + k) 0 && cell (T' + k + 1) 0) = false
    rw [hT (T' + k) (by omega), hT (T' + k + 1) (by omega), wordAt3_001, wordAt3_001]
    by_cases h2 : (T' + k - T) % 3 = 2
    · rw [show (T' + k + 1 - T) % 3 = 0 by omega]; simp
    · simp [h2]
  refine hQ T' (fun p => cell T' p) (by omega) (fun p hp => cell_eq_false_of_lt T' p hp)
    (cell_left_edge T') (fun k => ?_)
  have e := cell_eq_L_effective T' (3 * k) (-1) (by omega)
  rw [hfun] at e
  rw [e]
  exact (col_m1_001 T hT (T' + 3 * k) (by omega)).2.2 (by omega)

/-- **Finiteness is essential in `Q001`**: from the infinite stripe the zero-driven left half
keeps column `-1` black at every step. -/
theorem Q001_stripe (k : Nat) : L (fun _ => false) Rule30PeriodTwo.stripe (3 * k) (-1) = true :=
  Rule30PeriodTwo.stripe_col _

/-! ### The word `011` and the C3-type statement -/

/-- The 3-periodic effective boundary `c'_w(φ) = w(φ) && w(φ + 1)`. -/
def effWord3 (w : List Bool) : List Bool :=
  (List.range 3).map fun φ => wordAt3 w φ && wordAt3 w (φ + 1)

theorem effWord3_001 : effWord3 w001 = [false, false, false] := by decide
theorem effWord3_011 : effWord3 w011 = [false, true, false] := by decide

theorem wordAt3_effWord3 (w : List Bool) (k : Nat) :
    wordAt3 (effWord3 w) k = (wordAt3 w k && wordAt3 w (k + 1)) := by
  show ((List.range 3).map fun φ => wordAt3 w φ && wordAt3 w (φ + 1)).getD (k % 3) false = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (Nat.mod_lt _ (by decide))]
  simp only [Option.map_some, Option.getD_some]
  unfold wordAt3
  rw [Nat.mod_mod, show (k % 3 + 1) % 3 = (k + 1) % 3 by omega]

/-- Whether `b` fits the pattern `P` at phase `φ` (`none` = unconstrained). -/
def fits3 (P : List (Option Bool)) (φ : Nat) (b : Bool) : Bool :=
  match P.getD φ none with
  | none => true
  | some v => b == v

/-- `P_w`: the values of column `-1` fixed by left permutivity at the black phases of `w`. -/
def colPattern3 : List Bool → List (Option Bool)
  | [false, true, true] => [none, some false, some true]
  | [false, false, true] => [none, none, some true]
  | _ => [none, none, none]

/-- **`C3w w`** (open). No finitely supported left configuration, run as rule 30 on `p ≤ -1` with
column `0` replaced by the 3-periodic effective boundary `c'_w`, keeps column `-1` equal to `P_w`
at its fixed phases for all large times. -/
def C3w (w : List Bool) : Prop :=
  ∀ s : Int → Bool, (∃ M : Nat, ∀ p : Int, p < -(M : Int) → s p = false) →
    ¬ ∃ K, ∀ k, K ≤ k → fits3 (colPattern3 w) (k % 3) (L (fun k => wordAt3 (effWord3 w) k) s k (-1)) = true

/-- **Column `-1` under `011`.** If `c(t) = [ (t - T) % 3 ≥ 1 ]` for `t ≥ T`, column `-1` is
(`!` column `1`, white, black) at the phases (`0, 1, 2`). -/
theorem col_m1_011 (T : Nat) (h : ∀ t, T ≤ t → cell t 0 = wordAt3 w011 (t - T)) (t : Nat)
    (ht : T ≤ t) :
    ((t - T) % 3 = 0 → cell t (-1) = !cell t 1) ∧
    ((t - T) % 3 = 1 → cell t (-1) = false) ∧
    ((t - T) % 3 = 2 → cell t (-1) = true) := by
  have c0 := h t ht
  have c1 := h (t + 1) (by omega)
  rw [wordAt3_011] at c0 c1
  rw [show t + 1 - T = (t - T) + 1 by omega] at c1
  refine ⟨fun hφ => ?_, fun hφ => ?_, fun hφ => ?_⟩
  · rw [col_m1, c1, c0, show ((t - T) + 1) % 3 = 1 by omega, hφ]; cases cell t 1 <;> rfl
  · rw [col_m1, c1, c0, show ((t - T) + 1) % 3 = 2 by omega, hφ]; rfl
  · rw [col_m1, c1, c0, show ((t - T) + 1) % 3 = 0 by omega, hφ]; rfl

/-- The common step: a `w`-periodic tail whose column `-1` eventually fits `P_w` contradicts
`C3w w`. -/
theorem not_tail_of_C3w (w : List Bool) (hC : C3w w) (T : Nat)
    (hT : ∀ t, T ≤ t → cell t 0 = wordAt3 w (t - T))
    (hskel : ∃ T', T ≤ T' ∧ ∀ t, T' ≤ t → fits3 (colPattern3 w) ((t - T) % 3) (cell t (-1)) = true) :
    False := by
  obtain ⟨T', hT', hP⟩ := hskel
  have hdrv : (fun k => center (T + k) && center (T + k + 1)) = fun k => wordAt3 (effWord3 w) k := by
    funext k
    rw [wordAt3_effWord3]
    show (cell (T + k) 0 && cell (T + k + 1) 0) = _
    rw [hT (T + k) (by omega), hT (T + k + 1) (by omega), show T + k - T = k by omega,
      show T + k + 1 - T = k + 1 by omega]
  refine hC (fun p => cell T p) ⟨T, fun p hp => cell_eq_false_of_lt T p hp⟩ ⟨T' - T, fun k hk => ?_⟩
  have e := cell_eq_L_effective T k (-1) (by omega)
  rw [hdrv] at e
  rw [e]
  have := hP (T + k) (by omega)
  rwa [show T + k - T = k by omega] at this

theorem fits3_011 (φ : Nat) (b : Bool) :
    fits3 (colPattern3 w011) φ b =
      (if φ = 1 then b == false else if φ = 2 then b == true else true) := by
  rcases Nat.lt_or_ge φ 3 with h | h
  · have : φ = 0 ∨ φ = 1 ∨ φ = 2 := by omega
    rcases this with rfl | rfl | rfl <;> rfl
  · unfold fits3
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [colPattern3, w011]; omega)]
    simp [show φ ≠ 1 by omega, show φ ≠ 2 by omega]

/-- **`C3w w011` excludes `011^∞`** as a tail of the center column, for every transient. -/
theorem not_eventually_011_of_C3w (hC : C3w w011) :
    ¬ ∃ T, ∀ t, T ≤ t → cell t 0 = wordAt3 w011 (t - T) := by
  rintro ⟨T, hT⟩
  refine not_tail_of_C3w w011 hC T hT ⟨T, Nat.le_refl T, fun t ht => ?_⟩
  obtain ⟨-, s1, s2⟩ := col_m1_011 T hT t ht
  rw [fits3_011]
  have : (t - T) % 3 = 0 ∨ (t - T) % 3 = 1 ∨ (t - T) % 3 = 2 := by omega
  rcases this with h | h | h
  · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  · rw [ite_eq_left h, s1 h]; rfl
  · rw [ite_eq_right (by omega), ite_eq_left h, s2 h]; rfl

/-! ### Finiteness is essential for `C3w w011`: the ether -/

/-- The left part of the period-3 ether next to its column `2` (a `011` column): position `p < 0`
carries ether column `2 + p` (indices modulo `12`). -/
def etherLeft (p : Int) : Bool := ether3 (((p + 2) % 12).toNat) 0

theorem etherLeft_idx (p : Int) : (((p - 1 + 2) % 12).toNat + 1) % 12 = ((p + 2) % 12).toNat % 12 ∧
    (((p + 2) % 12).toNat + 1) % 12 = ((p + 1 + 2) % 12).toNat % 12 := by
  constructor <;> omega

/-- The ether left half evolves under the boundary `010` (the effective boundary of `011`). -/
theorem etherLeft_evolves : ∀ (k : Nat) (p : Int), p < 0 →
    L (fun k => wordAt3 (effWord3 w011) k) etherLeft k p = ether3 (((p + 2) % 12).toNat) k := by
  intro k
  induction k with
  | zero => intro p hp; rw [L_zero hp]; rfl
  | succ k ih =>
    intro p hp
    rw [L_succ hp, ih (p - 1) (by omega), ih p hp]
    have hl : ether3 (((p - 1 + 2) % 12).toNat) k = ether3 (((p + 2) % 12).toNat + 11) k :=
      ether3_congr (by omega) rfl
    rw [hl]
    by_cases hp1 : p = -1
    · subst hp1
      rw [show (-1 : Int) + 1 = 0 by rfl, L_col0, wordAt3_effWord3, wordAt3_011, wordAt3_011]
      show rule (ether3 (((-1 + 2 : Int) % 12).toNat + 11) k) (ether3 (((-1 + 2 : Int) % 12).toNat) k)
          (decide (1 ≤ k % 3) && decide (1 ≤ (k + 1) % 3)) = ether3 (((-1 + 2 : Int) % 12).toNat) (k + 1)
      have e1 : ((-1 + 2 : Int) % 12).toNat = 1 := by decide
      rw [e1, ether3_rule 1 k]
      have : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
      have hk : ∀ j, ether3 j k = ether3 j (k % 3) := fun j => ether3_congr rfl (by omega)
      rw [hk (1 + 11), hk 1, hk (1 + 1)]
      rcases this with h | h | h <;> rw [h] <;> simp [show (k + 1) % 3 = (k % 3 + 1) % 3 by omega, h] <;> decide
    · rw [ih (p + 1) (by omega)]
      rw [ether3_rule]
      congr 1
      exact ether3_congr (by omega) rfl

/-- **Finiteness is essential in `C3w w011`**: the (infinite) left part of the ether, driven by the
boundary `010`, keeps column `-1` equal to `(*, 0, 1)` for ever. -/
theorem C3w_011_ether (k : Nat) :
    fits3 (colPattern3 w011) (k % 3) (L (fun k => wordAt3 (effWord3 w011) k) etherLeft k (-1)) = true := by
  rw [etherLeft_evolves k (-1) (by omega), fits3_011]
  have e1 : ((-1 + 2 : Int) % 12).toNat = 1 := by decide
  rw [e1]
  have hk : ether3 1 k = ether3 1 (k % 3) := ether3_congr rfl (by omega)
  rw [hk]
  have : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases this with h | h | h <;> rw [h] <;> decide

/-! ### Period-3 Normalization, `C3w w001` Reduction, and Full Period-3 Center Exclusion -/

/-- **Iterated Period-3 Shift (`period_three_add_mul`):** if `center (t + 3) = center t` for all
`t ≥ T0`, then `center (s + 3 * q) = center s` for all `s ≥ T0` and `q : Nat`. -/
theorem period_three_add_mul {T0 : Nat} (hp : ∀ t, T0 ≤ t → center (t + 3) = center t)
    {s : Nat} (hs : T0 ≤ s) : ∀ q : Nat, center (s + 3 * q) = center s
  | 0 => by simp
  | q + 1 => by
    rw [show s + 3 * (q + 1) = (s + 3 * q) + 3 by omega, hp _ (by omega),
      period_three_add_mul hp hs q]

/-- **Period-3 Propagation from Base Window (`period_three_at_mod`):** if `center (t + 3) = center t`
for all `t ≥ T0`, then for every `t ≥ T0`, `center t = center (T0 + (t - T0) % 3)`. -/
theorem period_three_at_mod {T0 : Nat} (hp : ∀ t, T0 ≤ t → center (t + 3) = center t) :
    ∀ t, T0 ≤ t → center t = center (T0 + (t - T0) % 3) := by
  intro t ht
  have heq : t = (T0 + (t - T0) % 3) + 3 * ((t - T0) / 3) := by omega
  have h := period_three_add_mul hp (s := T0 + (t - T0) % 3) (by omega) ((t - T0) / 3)
  rwa [← heq] at h

/-- **Period-3 Center Normalization into `w001` or `w011` (`normalize_period_three`):** if the center
column is eventually 3-periodic (`∀ t ≥ T0, center (t + 3) = center t`), then there exists `T ≥ T0`
such that from `T` onward the center column is either `w001`-periodic or `w011`-periodic. -/
theorem normalize_period_three {T0 : Nat} (hp : ∀ t, T0 ≤ t → center (t + 3) = center t) :
    (∃ T, T0 ≤ T ∧ ∀ t, T ≤ t → cell t 0 = wordAt3 w001 (t - T)) ∨
    (∃ T, T0 ≤ T ∧ ∀ t, T ≤ t → cell t 0 = wordAt3 w011 (t - T)) := by
  have hmod := period_three_at_mod hp
  have hstep : ∀ T, T0 ≤ T → ∀ t, T ≤ t → cell t 0 = center (T + (t - T) % 3) := by
    intro T hT t ht
    show center t = center (T + (t - T) % 3)
    rw [hmod t (by omega), hmod (T + (t - T) % 3) (by omega)]
    congr 1
    omega
  cases h0 : center T0 <;> cases h1 : center (T0 + 1) <;> cases h2 : center (T0 + 2)
  · exfalso
    apply center_not_eventually_constant
    refine ⟨T0, false, fun t ht => ?_⟩
    rw [hmod t ht]
    rcases (show (t - T0) % 3 = 0 ∨ (t - T0) % 3 = 1 ∨ (t - T0) % 3 = 2 by omega) with h | h | h
    · rw [h, Nat.add_zero, h0]
    · rw [h, h1]
    · rw [h, h2]
  · left
    refine ⟨T0, Nat.le_refl T0, fun t ht => ?_⟩
    rw [hstep T0 (Nat.le_refl T0) t ht, wordAt3_001]
    rcases (show (t - T0) % 3 = 0 ∨ (t - T0) % 3 = 1 ∨ (t - T0) % 3 = 2 by omega) with h | h | h <;>
      rw [h] <;> simp [h0, h1, h2]
  · left
    refine ⟨T0 + 2, by omega, fun t ht => ?_⟩
    rw [hstep (T0 + 2) (by omega) t ht, wordAt3_001, hmod (T0 + 2 + (t - (T0 + 2)) % 3) (by omega)]
    rcases (show (t - (T0 + 2)) % 3 = 0 ∨ (t - (T0 + 2)) % 3 = 1 ∨ (t - (T0 + 2)) % 3 = 2 by omega) with h | h | h
    · rw [h, show (T0 + 2 + 0 - T0) % 3 = 2 by omega, h2]; rfl
    · rw [h, show (T0 + 2 + 1 - T0) % 3 = 0 by omega, Nat.add_zero, h0]; rfl
    · rw [h, show (T0 + 2 + 2 - T0) % 3 = 1 by omega, h1]; rfl
  · right
    refine ⟨T0, Nat.le_refl T0, fun t ht => ?_⟩
    rw [hstep T0 (Nat.le_refl T0) t ht, wordAt3_011]
    rcases (show (t - T0) % 3 = 0 ∨ (t - T0) % 3 = 1 ∨ (t - T0) % 3 = 2 by omega) with h | h | h <;>
      rw [h] <;> simp [h0, h1, h2]
  · left
    refine ⟨T0 + 1, by omega, fun t ht => ?_⟩
    rw [hstep (T0 + 1) (by omega) t ht, wordAt3_001, hmod (T0 + 1 + (t - (T0 + 1)) % 3) (by omega)]
    rcases (show (t - (T0 + 1)) % 3 = 0 ∨ (t - (T0 + 1)) % 3 = 1 ∨ (t - (T0 + 1)) % 3 = 2 by omega) with h | h | h
    · rw [h, show (T0 + 1 + 0 - T0) % 3 = 1 by omega, h1]; rfl
    · rw [h, show (T0 + 1 + 1 - T0) % 3 = 2 by omega, h2]; rfl
    · rw [h, show (T0 + 1 + 2 - T0) % 3 = 0 by omega, Nat.add_zero, h0]; rfl
  · right
    refine ⟨T0 + 1, by omega, fun t ht => ?_⟩
    rw [hstep (T0 + 1) (by omega) t ht, wordAt3_011, hmod (T0 + 1 + (t - (T0 + 1)) % 3) (by omega)]
    rcases (show (t - (T0 + 1)) % 3 = 0 ∨ (t - (T0 + 1)) % 3 = 1 ∨ (t - (T0 + 1)) % 3 = 2 by omega) with h | h | h
    · rw [h, show (T0 + 1 + 0 - T0) % 3 = 1 by omega, h1]; rfl
    · rw [h, show (T0 + 1 + 1 - T0) % 3 = 2 by omega, h2]; rfl
    · rw [h, show (T0 + 1 + 2 - T0) % 3 = 0 by omega, Nat.add_zero, h0]; rfl
  · right
    refine ⟨T0 + 2, by omega, fun t ht => ?_⟩
    rw [hstep (T0 + 2) (by omega) t ht, wordAt3_011, hmod (T0 + 2 + (t - (T0 + 2)) % 3) (by omega)]
    rcases (show (t - (T0 + 2)) % 3 = 0 ∨ (t - (T0 + 2)) % 3 = 1 ∨ (t - (T0 + 2)) % 3 = 2 by omega) with h | h | h
    · rw [h, show (T0 + 2 + 0 - T0) % 3 = 2 by omega, h2]; rfl
    · rw [h, show (T0 + 2 + 1 - T0) % 3 = 0 by omega, Nat.add_zero, h0]; rfl
    · rw [h, show (T0 + 2 + 2 - T0) % 3 = 1 by omega, h1]; rfl
  · exfalso
    apply center_not_eventually_constant
    refine ⟨T0, true, fun t ht => ?_⟩
    rw [hmod t ht]
    rcases (show (t - T0) % 3 = 0 ∨ (t - T0) % 3 = 1 ∨ (t - T0) % 3 = 2 by omega) with h | h | h
    · rw [h, Nat.add_zero, h0]
    · rw [h, h1]
    · rw [h, h2]

/-- **Explicit Characterization of `fits3 (colPattern3 w001)` (`fits3_001`):** `fits3 (colPattern3 w001) φ b`
is `b == true` at phase `φ = 2` and `true` otherwise. -/
theorem fits3_001 (φ : Nat) (b : Bool) :
    fits3 (colPattern3 w001) φ b = (if φ = 2 then b == true else true) := by
  rcases Nat.lt_or_ge φ 3 with h | h
  · have : φ = 0 ∨ φ = 1 ∨ φ = 2 := by omega
    rcases this with rfl | rfl | rfl <;> rfl
  · unfold fits3
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [colPattern3, w001]; omega)]
    simp [show φ ≠ 2 by omega]

/-- **`C3w w001` Excludes `001^∞` (`not_eventually_001_of_C3w`):** `C3w w001` rules out `001^∞` as a
tail of the center column, for every transient. -/
theorem not_eventually_001_of_C3w (hC : C3w w001) :
    ¬ ∃ T, ∀ t, T ≤ t → cell t 0 = wordAt3 w001 (t - T) := by
  rintro ⟨T, hT⟩
  refine not_tail_of_C3w w001 hC T hT ⟨T, Nat.le_refl T, fun t ht => ?_⟩
  obtain ⟨-, -, s2⟩ := col_m1_001 T hT t ht
  rw [fits3_001]
  by_cases h2 : (t - T) % 3 = 2
  · rw [ite_eq_left h2, s2 h2]; rfl
  · rw [ite_eq_right h2]

/-- **Stripe Witness for `C3w w001` (`C3w_001_stripe`):** from the infinite stripe, the zero-driven
left half satisfies `fits3 (colPattern3 w001) (k % 3)` for every `k : Nat`. -/
theorem C3w_001_stripe (k : Nat) :
    fits3 (colPattern3 w001) (k % 3) (L (fun k => wordAt3 (effWord3 w001) k) Rule30PeriodTwo.stripe k (-1)) = true := by
  have heff : (fun k => wordAt3 (effWord3 w001) k) = (fun _ => false) := by
    funext j
    rw [effWord3_001]
    unfold wordAt3
    have : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
    rcases this with h | h | h <;> rw [h] <;> rfl
  rw [heff, Rule30PeriodTwo.stripe_col k, fits3_001]
  split <;> rfl

/-- **Full Period-3 Exclusion from `Q001` and `C3w w011` (`no_eventual_period_three_of_Q001_and_C3w`):**
if both `Q001` and `C3w w011` hold, then the center column is not eventually 3-periodic. -/
theorem no_eventual_period_three_of_Q001_and_C3w (hQ : Q001) (hC : C3w w011) :
    ¬ ∃ T0, ∀ t, T0 ≤ t → center (t + 3) = center t := by
  rintro ⟨T0, hT0⟩
  rcases normalize_period_three hT0 with ⟨T, -, h001⟩ | ⟨T, -, h011⟩
  · exact not_eventually_001_of_Q001 hQ ⟨T, h001⟩
  · exact not_eventually_011_of_C3w hC ⟨T, h011⟩

/-- **Full Period-3 Exclusion from `C3w w001` and `C3w w011` (`no_eventual_period_three_of_C3w`):**
if both `C3w w001` and `C3w w011` hold, then the center column is not eventually 3-periodic. -/
theorem no_eventual_period_three_of_C3w (h001 : C3w w001) (h011 : C3w w011) :
    ¬ ∃ T0, ∀ t, T0 ≤ t → center (t + 3) = center t := by
  rintro ⟨T0, hT0⟩
  rcases normalize_period_three hT0 with ⟨T, -, h1⟩ | ⟨T, -, h2⟩
  · exact not_eventually_001_of_C3w h001 ⟨T, h1⟩
  · exact not_eventually_011_of_C3w h011 ⟨T, h2⟩

/-- **Spatial Period 12 of `etherLeft` (`etherLeft_sub_twelve`):** `etherLeft (p - 12) = etherLeft p`. -/
theorem etherLeft_sub_twelve (p : Int) :
    etherLeft (p - 12) = etherLeft p := by
  unfold etherLeft
  exact ether3_congr (by omega) rfl

/-! ### The all-times form of `C3w` -/

/-- **`C3w0 w`**, the all-times form of `C3w w` (open for `w011` and `w001`). No finitely
supported left configuration, run as in `C3w w`, keeps column `-1` equal to `P_w` at its fixed
phases at every time. -/
def C3w0 (w : List Bool) : Prop :=
  ∀ s : Int → Bool, (∃ M : Nat, ∀ p : Int, p < -(M : Int) → s p = false) →
    ¬ ∀ k, fits3 (colPattern3 w) (k % 3) (L (fun k => wordAt3 (effWord3 w) k) s k (-1)) = true

/-- Finite support spreads by one cell per step: if the start is white left of `-M`, the driven
left half is white left of `-(M + t)` at time `t`, whatever the driver. -/
theorem L_eq_false_of_lt (c : Nat → Bool) (s : Int → Bool) (M : Nat)
    (hs : ∀ p : Int, p < -(M : Int) → s p = false) :
    ∀ t (p : Int), p < -((M + t : Nat) : Int) → L c s t p = false := by
  intro t
  induction t with
  | zero => intro p hp; rw [L_zero (by omega)]; exact hs p (by omega)
  | succ t ih =>
    intro p hp
    rw [L_succ (by omega), ih (p - 1) (by omega), ih p (by omega), ih (p + 1) (by omega)]
    rfl

/-- `wordAt3` has period `3`. -/
theorem wordAt3_three_mul_add (w : List Bool) (K k : Nat) :
    wordAt3 w (3 * K + k) = wordAt3 w k := by
  unfold wordAt3; rw [show (3 * K + k) % 3 = k % 3 by omega]

/-- **The two forms of `C3w` are equivalent**, for every word `w`. A start that fits `P_w` from
time `K` on gives, after `3 K` steps (`L_add`), a row that is again finitely supported
(`L_eq_false_of_lt`) and fits at every time, since the driver has period `3`. -/
theorem C3w_iff_C3w0 (w : List Bool) : C3w w ↔ C3w0 w := by
  constructor
  · intro h s hs hall
    exact h s hs ⟨0, fun k _ => hall k⟩
  · rintro h s ⟨M, hM⟩ ⟨K, hK⟩
    refine h (L (fun k => wordAt3 (effWord3 w) k) s (3 * K)) ⟨M + 3 * K, fun p hp => ?_⟩
      (fun k => ?_)
    · exact L_eq_false_of_lt _ s M hM (3 * K) p hp
    · have hk := hK (3 * K + k) (by omega)
      rw [show (3 * K + k) % 3 = k % 3 by omega, L_add _ s (3 * K) k (-1) (by omega)] at hk
      have hdrv : (fun j => wordAt3 (effWord3 w) (3 * K + j)) = fun j => wordAt3 (effWord3 w) j :=
        funext fun j => wordAt3_three_mul_add (effWord3 w) K j
      rw [hdrv] at hk
      exact hk

/-- **`C3w0 w011` excludes `011^∞`** as a tail of the center column, for every transient: the
reduction `not_eventually_011_of_C3w` needs only the all-times form. -/
theorem not_eventually_011_of_C3w0 (hC : C3w0 w011) :
    ¬ ∃ T, ∀ t, T ≤ t → cell t 0 = wordAt3 w011 (t - T) :=
  not_eventually_011_of_C3w ((C3w_iff_C3w0 w011).mpr hC)

/-- **`C3w0 w001` excludes `001^∞`** as a tail of the center column, for every transient: the
reduction `not_eventually_001_of_C3w` needs only the all-times form. -/
theorem not_eventually_001_of_C3w0 (hC : C3w0 w001) :
    ¬ ∃ T, ∀ t, T ≤ t → cell t 0 = wordAt3 w001 (t - T) :=
  not_eventually_001_of_C3w ((C3w_iff_C3w0 w001).mpr hC)

/-! ### General driven sideways reconstruction, `Theta011` bijection, `2^n` prefix law -/

/-- Sideways reconstruction on `p ≤ 0` from prescribed boundary `c` (column `0`) and column-`-1` trace `a`. -/
def reconC (c a : Nat → Bool) : Nat → Nat → Bool
  | 0, t => c t
  | 1, t => a t
  | k + 2, t => xor (reconC c a (k + 1) (t + 1)) (reconC c a (k + 1) t || reconC c a k t)

theorem reconC_two (c a : Nat → Bool) (k t : Nat) :
    reconC c a (k + 2) t = xor (reconC c a (k + 1) (t + 1)) (reconC c a (k + 1) t || reconC c a k t) := rfl

/-- Initial left configuration reconstructed from boundary `c` and column-`-1` trace `a`. -/
def lamC (c a : Nat → Bool) (p : Int) : Bool := if p < 0 then reconC c a (-p).toNat 0 else false

theorem L_lamC (c a : Nat → Bool) : ∀ (t k : Nat), L c (lamC c a) t (-(k : Int)) = reconC c a k t := by
  intro t
  induction t with
  | zero =>
    intro k
    cases k with
    | zero => simp [L_col0, reconC]
    | succ j =>
      have hp : -((j + 1 : Nat) : Int) < 0 := by omega
      rw [L_zero hp]; unfold lamC; rw [ite_eq_left hp, show (- -((j + 1 : Nat) : Int)).toNat = j + 1 by omega]
  | succ t ih =>
    intro k
    cases k with
    | zero => simp [L_col0, reconC]
    | succ j =>
      have hp : -((j + 1 : Nat) : Int) < 0 := by omega
      rw [L_succ hp]
      have h1 : -((j + 1 : Nat) : Int) - 1 = -((j + 2 : Nat) : Int) := by omega
      have h2 : -((j + 1 : Nat) : Int) + 1 = -((j : Nat) : Int) := by omega
      rw [h1, h2, ih (j + 2), ih (j + 1), ih j, reconC_two]
      unfold rule
      cases reconC c a (j + 1) (t + 1) <;> cases (reconC c a (j + 1) t || reconC c a j t) <;> rfl

theorem history_eq_reconC (c : Nat → Bool) (s : Int → Bool) :
    ∀ (k t : Nat), L c s t (-(k : Int)) = reconC c (fun t => L c s t (-1)) k t := by
  have key : ∀ k : Nat,
      (∀ t, L c s t (-(k : Int)) = reconC c (fun t => L c s t (-1)) k t) ∧
      (∀ t, L c s t (-((k + 1 : Nat) : Int)) = reconC c (fun t => L c s t (-1)) (k + 1) t) := by
    intro k
    induction k with
    | zero => exact ⟨fun t => by simp [L_col0, reconC], fun _ => rfl⟩
    | succ k ih =>
      refine ⟨ih.2, fun t => ?_⟩
      have hp : -((k + 1 : Nat) : Int) < 0 := by omega
      have hstep := L_succ (c := c) (s := s) (t := t) hp
      have h1 : -((k + 1 : Nat) : Int) - 1 = -((k + 2 : Nat) : Int) := by omega
      have h2 : -((k + 1 : Nat) : Int) + 1 = -((k : Nat) : Int) := by omega
      rw [h1, h2] at hstep
      unfold rule at hstep
      rw [reconC_two, ← ih.2 (t + 1), ← ih.2 t, ← ih.1 t, hstep]
      cases L c s t (-((k + 2 : Nat) : Int)) <;> cases (L c s t (-((k + 1 : Nat) : Int)) || L c s t (-(k : Int))) <;> rfl
  exact fun k t => (key k).1 t

theorem L_neg_local (c : Nat → Bool) (s s' : Int → Bool) :
    ∀ (t k : Nat), 1 ≤ k → (∀ j : Nat, 1 ≤ j → j ≤ k + t → s (-(j : Int)) = s' (-(j : Int))) →
      L c s t (-(k : Int)) = L c s' t (-(k : Int))
  | 0, k, hk, h => by
    have hp : -(k : Int) < 0 := by omega
    rw [L_zero hp, L_zero hp]; exact h k hk (by omega)
  | t + 1, k, hk, h => by
    have hp : -(k : Int) < 0 := by omega
    rw [L_succ hp, L_succ hp]
    have h1 : -(k : Int) - 1 = -((k + 1 : Nat) : Int) := by omega
    have h2 : -(k : Int) + 1 = -((k - 1 : Nat) : Int) := by omega
    rw [h1, h2,
      L_neg_local c s s' t (k + 1) (by omega) (fun j hj1 hj2 => h j hj1 (by omega)),
      L_neg_local c s s' t k hk (fun j hj1 hj2 => h j hj1 (by omega))]
    cases hk_eq : k - 1 with
    | zero => simp [L_col0]
    | succ m =>
      rw [L_neg_local c s s' t (m + 1) (by omega) (fun j hj1 hj2 => h j hj1 (by omega))]

theorem L_neg_flip_top (c : Nat → Bool) (s s' : Int → Bool) :
    ∀ (t k : Nat), 1 ≤ k →
      (∀ j : Nat, 1 ≤ j → j < k + t → s (-(j : Int)) = s' (-(j : Int))) →
      s' (-((k + t : Nat) : Int)) = !(s (-((k + t : Nat) : Int))) →
      L c s' t (-(k : Int)) = !(L c s t (-(k : Int)))
  | 0, k, _, _, htop => by
    have hp : -(k : Int) < 0 := by omega
    rw [L_zero hp, L_zero hp]; simpa using htop
  | t + 1, k, hk, hlow, htop => by
    have hp : -(k : Int) < 0 := by omega
    rw [L_succ hp, L_succ hp]
    have h1 : -(k : Int) - 1 = -((k + 1 : Nat) : Int) := by omega
    have h2 : -(k : Int) + 1 = -((k - 1 : Nat) : Int) := by omega
    rw [h1, h2]
    have hflip := L_neg_flip_top c s s' t (k + 1) (by omega)
      (fun j hj1 hj2 => hlow j hj1 (by omega))
      (by simpa [show k + 1 + t = k + (t + 1) by omega] using htop)
    have hmid := L_neg_local c s s' t k hk (fun j hj1 hj2 => hlow j hj1 (by omega))
    have hright : L c s t (-((k - 1 : Nat) : Int)) = L c s' t (-((k - 1 : Nat) : Int)) := by
      cases hk_eq : k - 1 with
      | zero => simp [L_col0]
      | succ m => exact L_neg_local c s s' t (m + 1) (by omega) (fun j hj1 hj2 => hlow j hj1 (by omega))
    rw [hflip, ← hmid, ← hright]
    unfold rule
    cases L c s t (-((k + 1 : Nat) : Int)) <;> cases (L c s t (-(k : Int)) || L c s t (-((k - 1 : Nat) : Int))) <;> rfl

/-- The effective boundary `010` of `w011`. -/
def eff011 (k : Nat) : Bool := wordAt3 (effWord3 w011) k

/-- Column-`-1` stream of a `C3w0 w011`-admissible configuration with phase-`0` free bits `f`. -/
def trace011 (f : Nat → Bool) (t : Nat) : Bool :=
  if t % 3 = 0 then f (t / 3) else if t % 3 = 1 then false else true

/-- Forced-row parameterization `Theta011` for `011` under effective boundary `010`. -/
def Theta011 (f : Nat → Bool) : Int → Bool := lamC eff011 (trace011 f)

theorem L_Theta011_col_m1 (f : Nat → Bool) (t : Nat) :
    L eff011 (Theta011 f) t (-1) = trace011 f t := by
  simpa [Theta011, reconC] using L_lamC eff011 (trace011 f) t 1

theorem Theta011_fits (f : Nat → Bool) (k : Nat) :
    fits3 (colPattern3 w011) (k % 3) (L eff011 (Theta011 f) k (-1)) = true := by
  rw [L_Theta011_col_m1, fits3_011]
  unfold trace011
  have : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases this with h | h | h <;> simp [h]

private theorem zero_start_dies_011 :
    fits3 (colPattern3 w011) (5 % 3) (L eff011 (fun _ => false) 5 (-1)) = false := by decide

private theorem last_black_neg {s : Int → Bool} {M : Nat}
    (hM : ∀ p : Int, p < -(M : Int) → s p = false)
    (hne : ∃ k : Nat, 1 ≤ k ∧ k ≤ M ∧ s (-(k : Int)) = true) :
    ∃ m : Nat, 0 < m ∧ (∀ p : Int, p < -(m : Int) → s p = false) ∧ s (-(m : Int)) = true := by
  induction M with
  | zero => obtain ⟨k, hk1, hk0, _⟩ := hne; omega
  | succ M ih =>
    by_cases htop : s (-((M + 1 : Nat) : Int)) = true
    · exact ⟨M + 1, by omega, hM, htop⟩
    · have hM' : ∀ p : Int, p < -(M : Int) → s p = false := by
        intro p hp
        by_cases heq : p = -((M + 1 : Nat) : Int)
        · subst heq; cases hs : s (-((M + 1 : Nat) : Int)) <;> simp_all
        · exact hM p (by omega)
      refine ih hM' ?_
      obtain ⟨k, hk1, hkM, hsk⟩ := hne
      refine ⟨k, hk1, ?_, hsk⟩
      by_cases hk_top : k = M + 1
      · subst hk_top; exact absurd hsk htop
      · omega

/-- **Headline 1 (`C3w0_011_iff_nonzero`):** The all-white start violates `C3w0 w011` at tick `5`,
so `C3w0 w011` is equivalent to excluding nonzero finite left starts with a leftmost black cell `-m`. -/
theorem C3w0_011_iff_nonzero :
    C3w0 w011 ↔
      ∀ (m : Nat) (s : Int → Bool), 0 < m → (∀ p : Int, p < -(m : Int) → s p = false) →
        s (-(m : Int)) = true →
        ¬ ∀ k, fits3 (colPattern3 w011) (k % 3) (L eff011 s k (-1)) = true := by
  constructor
  · intro h m s _ hs0 _ hall
    exact h s ⟨m, hs0⟩ hall
  · intro h s ⟨M, hM⟩ hall
    by_cases hne : ∃ k : Nat, 1 ≤ k ∧ k ≤ M ∧ s (-(k : Int)) = true
    · obtain ⟨m, hm, hs0, hs1⟩ := last_black_neg hM hne
      exact h m s hm hs0 hs1 hall
    · have hzero : ∀ j : Nat, 1 ≤ j → s (-(j : Int)) = false := by
        intro j hj
        by_cases hjM : j ≤ M
        · cases hsj : s (-(j : Int))
          · rfl
          · exact absurd ⟨j, hj, hjM, hsj⟩ hne
        · exact hM (-(j : Int)) (by omega)
      have heq := L_neg_local eff011 s (fun _ => false) 5 1 (by omega) (fun j hj _ => hzero j hj)
      have h5 := hall 5
      change fits3 (colPattern3 w011) (5 % 3) (L eff011 s 5 (-1)) = true at h5
      rw [show (-1 : Int) = -((1 : Nat) : Int) by rfl, heq, show -((1 : Nat) : Int) = -1 by rfl,
        zero_start_dies_011] at h5
      exact Bool.noConfusion h5

/-- **Headline 2 (`Theta011_bijection_and_C3w0_iff`):** Exact forced-row parameterization of `C3w0 w011`.
A configuration `s` fits `colPattern3 w011` at every tick iff `s` agrees on `p < 0` with `Theta011 f`,
and `C3w0 w011` holds iff no `Theta011 f` is finitely supported on the left. -/
theorem Theta011_bijection_and_C3w0_iff :
    (∀ s : Int → Bool,
      (∀ k, fits3 (colPattern3 w011) (k % 3) (L eff011 s k (-1)) = true) ↔
        ∃ f : Nat → Bool, ∀ p : Int, p < 0 → s p = Theta011 f p) ∧
    (C3w0 w011 ↔ ∀ f : Nat → Bool, ¬ ∃ M : Nat, ∀ p : Int, p < -(M : Int) → Theta011 f p = false) := by
  have hbij : ∀ s : Int → Bool,
      (∀ k, fits3 (colPattern3 w011) (k % 3) (L eff011 s k (-1)) = true) ↔
        ∃ f : Nat → Bool, ∀ p : Int, p < 0 → s p = Theta011 f p := by
    intro s
    constructor
    · intro hall
      refine ⟨fun q => L eff011 s (3 * q) (-1), fun p hp => ?_⟩
      have htr : (fun t => L eff011 s t (-1)) = trace011 (fun q => L eff011 s (3 * q) (-1)) := by
        funext t
        have ht := hall t
        rw [fits3_011] at ht
        unfold trace011
        have hmod : t % 3 = 0 ∨ t % 3 = 1 ∨ t % 3 = 2 := by omega
        rcases hmod with h0 | h1 | h2
        · rw [ite_eq_left h0]; dsimp only; rw [show 3 * (t / 3) = t by omega]
        · simp [h1] at ht ⊢; exact ht
        · simp [h2] at ht ⊢; exact ht
      have hk : -((-p).toNat : Int) = p := by omega
      have h0 := L_zero (c := eff011) (s := s) hp
      rw [← h0, ← hk, history_eq_reconC eff011 s (-p).toNat 0, htr]
      unfold Theta011 lamC; rw [hk, ite_eq_left hp]
    · rintro ⟨f, hf⟩ k
      have heq := L_neg_local eff011 s (Theta011 f) k 1 (by omega) (fun j hj _ => hf (-(j : Int)) (by omega))
      change fits3 (colPattern3 w011) (k % 3) (L eff011 s k (-1)) = true
      rw [show (-1 : Int) = -((1 : Nat) : Int) by rfl, heq, show -((1 : Nat) : Int) = -1 by rfl]
      exact Theta011_fits f k
  refine ⟨hbij, ?_⟩
  constructor
  · intro hC f ⟨M, hM⟩
    exact hC (Theta011 f) ⟨M, hM⟩ (Theta011_fits f)
  · intro hno s ⟨M, hM⟩ hall
    obtain ⟨f, hf⟩ := (hbij s).mp hall
    exact hno f ⟨M, fun p hp => by rw [← hf p (by omega)]; exact hM p hp⟩

/-- **Headline 3 (`Theta011_ether_eq_etherLeft`):** `Theta011` applied to the period-3 ether's
phase-`0` column-`-1` readings recovers `etherLeft` identically on all `p < 0`. -/
theorem Theta011_ether_eq_etherLeft (p : Int) (hp : p < 0) :
    Theta011 (fun q => L eff011 etherLeft (3 * q) (-1)) p = etherLeft p := by
  have hall : ∀ k, fits3 (colPattern3 w011) (k % 3) (L eff011 etherLeft k (-1)) = true := C3w_011_ether
  have htr : (fun t => L eff011 etherLeft t (-1)) = trace011 (fun q => L eff011 etherLeft (3 * q) (-1)) := by
    funext t
    have ht := hall t
    rw [fits3_011] at ht
    unfold trace011
    have hmod : t % 3 = 0 ∨ t % 3 = 1 ∨ t % 3 = 2 := by omega
    rcases hmod with h0 | h1 | h2
    · rw [ite_eq_left h0]; dsimp only; rw [show 3 * (t / 3) = t by omega]
    · simp [h1] at ht ⊢; exact ht
    · simp [h2] at ht ⊢; exact ht
  have hk : -((-p).toNat : Int) = p := by omega
  have h0 := L_zero (c := eff011) (s := etherLeft) hp
  symm
  rw [← h0, ← hk, history_eq_reconC eff011 etherLeft (-p).toNat 0, htr]
  unfold Theta011 lamC; rw [hk, ite_eq_left hp]

/-! ### Single-pass packed integer dynamics `step010`, exact `2^n` prefix law -/

def ofNatLeft (Y : Nat) (p : Int) : Bool := if p < 0 then Y.testBit ((-p).toNat - 1) else false

def step010 (t Y : Nat) : Nat := (Y >>> 1) ^^^ (Y ||| ((Y <<< 1) ||| (if t % 3 = 1 then 1 else 0)))

def iter010 : Nat → Nat → Nat
  | 0, Y => Y
  | t + 1, Y => step010 t (iter010 t Y)

private theorem eff011_eq_decide (t : Nat) : eff011 t = decide (t % 3 = 1) := by
  unfold eff011 effWord3 wordAt3
  have : t % 3 = 0 ∨ t % 3 = 1 ∨ t % 3 = 2 := by omega
  rcases this with h | h | h <;> simp [h, w011]

private theorem bit_one_zero_succ (c : Prop) [Decidable c] (m : Nat) :
    (if c then 1 else 0).testBit (m + 1) = false := by
  by_cases hc : c
  · rw [ite_eq_left hc]; change (2 ^ 0).testBit (m + 1) = false; rw [Nat.testBit_two_pow]; simp
  · rw [ite_eq_right hc]; simp

theorem L_ofNatLeft_eq_iter010 (Y : Nat) : ∀ (t : Nat) (k : Nat), 1 ≤ k →
    L eff011 (ofNatLeft Y) t (-(k : Int)) = (iter010 t Y).testBit (k - 1) := by
  intro t
  induction t with
  | zero =>
    intro k _
    have hp : -(k : Int) < 0 := by omega
    rw [L_zero hp]; unfold ofNatLeft iter010; rw [ite_eq_left hp, show (- -(k : Int)).toNat = k by omega]
  | succ t ih =>
    intro k hk
    have hp : -(k : Int) < 0 := by omega
    rw [L_succ hp]
    have h1 : -(k : Int) - 1 = -((k + 1 : Nat) : Int) := by omega
    have h2 : -(k : Int) + 1 = -((k - 1 : Nat) : Int) := by omega
    rw [h1, h2, ih (k + 1) (by omega), ih k hk]
    simp only [iter010, step010, Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_shiftLeft]
    rw [show 1 + (k - 1) = k by omega]
    cases hk_eq : k - 1 with
    | zero =>
      have hk1 : k = 1 := by omega
      subst hk1
      have hz0 : (-((0 : Nat) : Int)) = 0 := by omega
      rw [hz0, L_col0, eff011_eq_decide]
      have hsh0 : (decide (1 ≤ 0) && (iter010 t Y).testBit (0 - 1)) = false := rfl
      have hif0 : (if t % 3 = 1 then 1 else 0).testBit 0 = decide (t % 3 = 1) := by
        by_cases ht1 : t % 3 = 1
        · rw [ite_eq_left ht1, decide_eq_true ht1]; rfl
        · rw [ite_eq_right ht1, decide_eq_false ht1]; rfl
      rw [hsh0, Bool.false_or, hif0]; rfl
    | succ m =>
      rw [ih (m + 1) (by omega), bit_one_zero_succ (t % 3 = 1) m, Bool.or_false]
      rfl

def fitsBit011 (t Y : Nat) : Bool := fits3 (colPattern3 w011) (t % 3) ((iter010 t Y).testBit 0)

def expandStep011 (t : Nat) : List Nat → List Nat
  | [] => []
  | Y :: Ys =>
    let rest := expandStep011 t Ys
    let r1 := if fitsBit011 t (Y + 2 ^ t) then (Y + 2 ^ t) :: rest else rest
    if fitsBit011 t Y then Y :: r1 else r1

def survPrefixes011 : Nat → List Nat
  | 0 => [0]
  | t + 1 => expandStep011 t (survPrefixes011 t)

private theorem mem_expandStep011 (t : Nat) (xs : List Nat) (Z : Nat) :
    Z ∈ expandStep011 t xs ↔
      (Z ∈ xs ∧ fitsBit011 t Z = true) ∨ (∃ X ∈ xs, Z = X + 2 ^ t ∧ fitsBit011 t Z = true) := by
  induction xs with
  | nil => simp [expandStep011]
  | cons Y Ys ih =>
    unfold expandStep011
    cases h0 : fitsBit011 t Y <;> cases h1 : fitsBit011 t (Y + 2 ^ t)
    · simp only [Bool.false_eq_true, ite_false, List.mem_cons, ih]
      constructor
      · rintro (⟨hz, hfz⟩ | ⟨X, hX, rfl, hfz⟩)
        · exact Or.inl ⟨Or.inr hz, hfz⟩
        · exact Or.inr ⟨X, Or.inr hX, rfl, hfz⟩
      · rintro (⟨rfl | hz, hfz⟩ | ⟨X, rfl | hX, rfl, hfz⟩)
        · rw [h0] at hfz; exact Bool.noConfusion hfz
        · exact Or.inl ⟨hz, hfz⟩
        · rw [h1] at hfz; exact Bool.noConfusion hfz
        · exact Or.inr ⟨X, hX, rfl, hfz⟩
    · simp only [Bool.false_eq_true, ite_true, ite_false, List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨hz, hfz⟩ | ⟨X, hX, rfl, hfz⟩)
        · exact Or.inr ⟨Y, Or.inl rfl, rfl, h1⟩
        · exact Or.inl ⟨Or.inr hz, hfz⟩
        · exact Or.inr ⟨X, Or.inr hX, rfl, hfz⟩
      · rintro (⟨rfl | hz, hfz⟩ | ⟨X, rfl | hX, rfl, hfz⟩)
        · rw [h0] at hfz; exact Bool.noConfusion hfz
        · exact Or.inr (Or.inl ⟨hz, hfz⟩)
        · exact Or.inl rfl
        · exact Or.inr (Or.inr ⟨X, hX, rfl, hfz⟩)
    · simp only [Bool.false_eq_true, ite_true, ite_false, List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨hz, hfz⟩ | ⟨X, hX, rfl, hfz⟩)
        · exact Or.inl ⟨Or.inl rfl, h0⟩
        · exact Or.inl ⟨Or.inr hz, hfz⟩
        · exact Or.inr ⟨X, Or.inr hX, rfl, hfz⟩
      · rintro (⟨rfl | hz, hfz⟩ | ⟨X, rfl | hX, rfl, hfz⟩)
        · exact Or.inl rfl
        · exact Or.inr (Or.inl ⟨hz, hfz⟩)
        · rw [h1] at hfz; exact Bool.noConfusion hfz
        · exact Or.inr (Or.inr ⟨X, hX, rfl, hfz⟩)
    · simp only [ite_true, List.mem_cons, ih]
      constructor
      · rintro (rfl | rfl | ⟨hz, hfz⟩ | ⟨X, hX, rfl, hfz⟩)
        · exact Or.inl ⟨Or.inl rfl, h0⟩
        · exact Or.inr ⟨Y, Or.inl rfl, rfl, h1⟩
        · exact Or.inl ⟨Or.inr hz, hfz⟩
        · exact Or.inr ⟨X, Or.inr hX, rfl, hfz⟩
      · rintro (⟨rfl | hz, hfz⟩ | ⟨X, rfl | hX, rfl, hfz⟩)
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (Or.inl ⟨hz, hfz⟩))
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inr ⟨X, hX, rfl, hfz⟩))

private theorem survPrefixes011_lt : ∀ (t Y : Nat), Y ∈ survPrefixes011 t → Y < 2 ^ t
  | 0, Y, h => by simp [survPrefixes011] at h; omega
  | t + 1, Y, h => by
    change Y ∈ expandStep011 t (survPrefixes011 t) at h
    rw [mem_expandStep011] at h
    rcases h with ⟨hY, _⟩ | ⟨X, hX, rfl, _⟩
    · have := survPrefixes011_lt t Y hY; rw [Nat.pow_succ]; omega
    · have := survPrefixes011_lt t X hX; rw [Nat.pow_succ]; omega

private theorem iter010_flip_top (t Y : Nat) (hY : Y < 2 ^ t) :
    (iter010 t (Y + 2 ^ t)).testBit 0 = !((iter010 t Y).testBit 0) := by
  rw [← L_ofNatLeft_eq_iter010 (Y + 2 ^ t) t 1 (by omega), ← L_ofNatLeft_eq_iter010 Y t 1 (by omega)]
  refine L_neg_flip_top eff011 (ofNatLeft Y) (ofNatLeft (Y + 2 ^ t)) t 1 (by omega) (fun j hj1 hj2 => ?_) ?_
  · have hp : -(j : Int) < 0 := by omega
    simp only [ofNatLeft, hp, ite_true, show (- -(j : Int)).toNat = j by omega]
    rw [← Nat.or_two_pow_eq_add_of_lt hY, Nat.testBit_or, Nat.testBit_two_pow]
    simp [show t ≠ j - 1 by omega]
  · have hp : -((1 + t : Nat) : Int) < 0 := by omega
    simp only [ofNatLeft, hp, ite_true, show (- -((1 + t : Nat) : Int)).toNat = 1 + t by omega,
      show 1 + t - 1 = t by omega]
    rw [← Nat.or_two_pow_eq_add_of_lt hY, Nat.testBit_or, Nat.testBit_two_pow]
    have hfalse : Y.testBit t = false := Nat.testBit_lt_two_pow hY
    simp [hfalse]

private theorem iter010_local (t W Y1 Y2 : Nat) (ht : t < W) (hmod : Y1 % 2 ^ W = Y2 % 2 ^ W) :
    (iter010 t Y1).testBit 0 = (iter010 t Y2).testBit 0 := by
  rw [← L_ofNatLeft_eq_iter010 Y1 t 1 (by omega), ← L_ofNatLeft_eq_iter010 Y2 t 1 (by omega)]
  refine L_neg_local eff011 (ofNatLeft Y1) (ofNatLeft Y2) t 1 (by omega) (fun j hj1 hj2 => ?_)
  have hp : -(j : Int) < 0 := by omega
  simp only [ofNatLeft, hp, ite_true, show (- -(j : Int)).toNat = j by omega]
  have hjW : j - 1 < W := by omega
  have h1 := Nat.testBit_mod_two_pow Y1 W (j - 1)
  have h2 := Nat.testBit_mod_two_pow Y2 W (j - 1)
  simp only [hjW, decide_true, Bool.true_and] at h1 h2
  rw [← h1, ← h2, hmod]

private theorem mem_survPrefixes011_iff : ∀ (W Y : Nat),
    Y ∈ survPrefixes011 W ↔ Y < 2 ^ W ∧ ∀ t, t < W → fitsBit011 t Y = true
  | 0, Y => by simp [survPrefixes011]
  | t + 1, Y => by
    change Y ∈ expandStep011 t (survPrefixes011 t) ↔ _
    rw [mem_expandStep011]
    constructor
    · rintro (⟨hY, hft⟩ | ⟨X, hX, rfl, hft⟩)
      · obtain ⟨hYlt, hall⟩ := (mem_survPrefixes011_iff t Y).mp hY
        refine ⟨by rw [Nat.pow_succ]; omega, fun k hk => if hkt : k = t then hkt ▸ hft else hall k (by omega)⟩
      · obtain ⟨hXlt, hall⟩ := (mem_survPrefixes011_iff t X).mp hX
        refine ⟨by rw [Nat.pow_succ]; omega, fun k hk => ?_⟩
        by_cases hkt : k = t
        · subst hkt; exact hft
        · unfold fitsBit011
          rw [iter010_local k t (X + 2 ^ t) X (by omega) (by rw [Nat.add_mod_right])]
          exact hall k (by omega)
    · rintro ⟨hlt, hall⟩
      let X := Y % 2 ^ t
      have hXlt : X < 2 ^ t := Nat.mod_lt Y (Nat.two_pow_pos t)
      have hXmem : X ∈ survPrefixes011 t := by
        refine (mem_survPrefixes011_iff t X).mpr ⟨hXlt, fun k hk => ?_⟩
        unfold fitsBit011
        rw [iter010_local k t X Y hk (Nat.mod_mod Y (2 ^ t))]
        exact hall k (by omega)
      have hq2 : Y / 2 ^ t < 2 := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos t)).mpr
        (by rw [Nat.mul_comm, ← Nat.pow_succ]; exact hlt)
      have hsplit : 2 ^ t * (Y / 2 ^ t) + X = Y := Nat.div_add_mod Y (2 ^ t)
      rcases hq_eq : Y / 2 ^ t with _ | _ | k
      · rw [hq_eq, Nat.mul_zero, Nat.zero_add] at hsplit
        exact Or.inl ⟨hsplit ▸ hXmem, hall t (by omega)⟩
      · rw [hq_eq, Nat.mul_one, Nat.add_comm] at hsplit
        exact Or.inr ⟨X, hXmem, hsplit.symm, hall t (by omega)⟩
      · rw [hq_eq] at hq2; omega

private theorem expandStep011_len_free (t : Nat) (h0 : t % 3 = 0) : ∀ xs : List Nat,
    (expandStep011 t xs).length = 2 * xs.length
  | [] => rfl
  | Y :: Ys => by
    have hf0 : fitsBit011 t Y = true := by unfold fitsBit011; rw [fits3_011]; simp [h0]
    have hf1 : fitsBit011 t (Y + 2 ^ t) = true := by unfold fitsBit011; rw [fits3_011]; simp [h0]
    simp only [expandStep011, hf0, hf1, ite_true, List.length_cons, expandStep011_len_free t h0 Ys]
    omega

private theorem expandStep011_len_pin (t : Nat) (hpin : t % 3 = 1 ∨ t % 3 = 2) :
    ∀ xs : List Nat, (∀ Y ∈ xs, Y < 2 ^ t) → (expandStep011 t xs).length = xs.length
  | [], _ => rfl
  | Y :: Ys, hlt => by
    have hYlt : Y < 2 ^ t := hlt Y (List.mem_cons_self ..)
    have hflip : fitsBit011 t (Y + 2 ^ t) = !(fitsBit011 t Y) := by
      unfold fitsBit011; rw [fits3_011, fits3_011, iter010_flip_top t Y hYlt]
      rcases hpin with h1 | h2
      · simp [h1]
      · simp [h2]
    have ih := expandStep011_len_pin t hpin Ys (fun X hX => hlt X (List.mem_cons_of_mem Y hX))
    unfold expandStep011
    rw [hflip]
    cases fitsBit011 t Y <;> simp [ih]

/-- **Headline 4 (`c3w0_011_prefix_count_two_pow`):** Out of all `8^n` (`2^(3*n)`) prefixes `Y < 2^(3*n)`
of width `3 * n`, **exact count `2^n`** satisfy the `011` column-`-1` pattern across `0 .. 3*n - 1`
(exponential survival fraction `(1/4)^n`). -/
theorem c3w0_011_prefix_count_two_pow (n : Nat) :
    (survPrefixes011 (3 * n)).length = 2 ^ n ∧
    ∀ Y : Nat, Y ∈ survPrefixes011 (3 * n) ↔ Y < 2 ^ (3 * n) ∧ ∀ t, t < 3 * n → fitsBit011 t Y = true := by
  refine ⟨?_, fun Y => mem_survPrefixes011_iff (3 * n) Y⟩
  induction n with
  | zero => rfl
  | succ n ih =>
    have s3 : survPrefixes011 (3 * (n + 1)) = expandStep011 (3 * n + 2) (survPrefixes011 (3 * n + 2)) := rfl
    have s2 : survPrefixes011 (3 * n + 2) = expandStep011 (3 * n + 1) (survPrefixes011 (3 * n + 1)) := rfl
    have s1 : survPrefixes011 (3 * n + 1) = expandStep011 (3 * n) (survPrefixes011 (3 * n)) := rfl
    have h1 := expandStep011_len_pin (3 * n + 2) (Or.inr (by omega)) (survPrefixes011 (3 * n + 2)) (survPrefixes011_lt _)
    have h2 := expandStep011_len_pin (3 * n + 1) (Or.inl (by omega)) (survPrefixes011 (3 * n + 1)) (survPrefixes011_lt _)
    have h3 := expandStep011_len_free (3 * n) (by omega) (survPrefixes011 (3 * n))
    rw [s3, h1, s2, h2, s1, h3, ih, Nat.pow_succ]; omega

end Rule30EtherThree
end Ruliology.CellularAutomata
