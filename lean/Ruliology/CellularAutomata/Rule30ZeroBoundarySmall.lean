module

public import Ruliology.CellularAutomata.Rule30ZeroBoundary

/-!
# Rule 30, zero-boundary left half: `Q01` for all starts of width at most `16`

A kernel-checked exhaustive search. Rows of the ZBL (`Rule30ZeroBoundary.zrow`) supported at
depths `1, …, W` are packed into natural numbers below `2 ^ W` (`toFun`, `exists_pack`), and one ZBL
step is a bit operation on the packed row (`step_toFun`).

* `q01_width_le_16`: every start supported at depths `≤ 16` has a white cell at depth `1` at some
  even step `< 34`. So no start of width `≤ 16` is constrained forever (`Q01` for these widths).
* `q01_width_le_15_odd`: the other phase, for widths `≤ 15`.

These are kernel-checked instances of `Q01` at small sizes. Exhaustive searches outside Lean go
further, but are not kernel-checked; `Q01` itself is open.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30ZeroBoundarySmall

open Rule30Jen Rule30ZeroBoundary

/-- The row packed in `r`: depth `k ≥ 1` is bit `k - 1`, the wall is white. -/
def toFun (r : Nat) : Nat → Bool := fun k => if k = 0 then false else r.testBit (k - 1)

/-- One ZBL step on packed rows. -/
def pstep (r : Nat) : Nat := (r >>> 1) ^^^ (r ||| (r <<< 1))

theorem step_toFun (r : Nat) : zrow (toFun r) 1 = toFun (pstep r) := by
  funext k
  cases k with
  | zero => rfl
  | succ k =>
    rw [zrow_succ, zrow_zero_self (show toFun r 0 = false from rfl)]
    simp only [toFun, pstep, Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftRight,
      Nat.testBit_shiftLeft]
    cases k with
    | zero => simp
    | succ j => simp [show 1 + (j + 1) = j + 2 by omega]

def prun (r : Nat) : Nat → Nat
  | 0 => r
  | t + 1 => pstep (prun r t)

theorem run_toFun (r t : Nat) : zrow (toFun r) t = toFun (prun r t) := by
  induction t with
  | zero => exact zrow_zero_self rfl
  | succ t ih =>
    funext k
    rw [zrow_shift (toFun r) t 1 k, ih, step_toFun]
    rfl

theorem testBit_ge_of_lt {r W j : Nat} (h : r < 2 ^ W) (hj : W ≤ j) : r.testBit j = false := by
  apply Nat.testBit_lt_two_pow
  exact Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) hj)

/-- Every row supported at depths `1, …, W` is packed by some `r < 2 ^ W`. -/
theorem exists_pack (W : Nat) : ∀ x : Nat → Bool, (∀ k, W < k → x k = false) →
    ∃ r, r < 2 ^ W ∧ ∀ k, 1 ≤ k → toFun r k = x k := by
  induction W with
  | zero =>
    intro x hx
    refine ⟨0, by decide, fun k hk => ?_⟩
    simp [toFun, show k ≠ 0 by omega, hx k (by omega)]
  | succ W ih =>
    intro x hx
    let x' : Nat → Bool := fun k => if k = W + 1 then false else x k
    have hx' : ∀ k, W < k → x' k = false := by
      intro k hk
      by_cases h : k = W + 1
      · simp [x', h]
      · simp only [x', h, ite_false]; exact hx k (by omega)
    obtain ⟨r', hr', hr'x⟩ := ih x' hx'
    have hrx : ∀ k, 1 ≤ k → k ≠ W + 1 → toFun r' k = x k := by
      intro k hk1 hk; rw [hr'x k hk1]; simp [x', hk]
    cases hb : x (W + 1) with
    | false =>
      refine ⟨r', by rw [Nat.pow_succ]; omega, fun k hk1 => ?_⟩
      by_cases hk : k = W + 1
      · subst hk; rw [hb]; simp [toFun, testBit_ge_of_lt hr' (Nat.le_refl W)]
      · exact hrx k hk1 hk
    | true =>
      refine ⟨2 ^ W + r', by rw [Nat.pow_succ]; omega, fun k hk1 => ?_⟩
      by_cases hk : k = W + 1
      · subst hk; rw [hb]
        simp [toFun, Nat.testBit_two_pow_add_eq, testBit_ge_of_lt hr' (Nat.le_refl W)]
      · rw [← hrx k hk1 hk]
        simp only [toFun, show k ≠ 0 by omega, ite_false]
        by_cases hlt : k - 1 < W
        · exact Nat.testBit_two_pow_add_gt hlt r'
        · have h1 : (2 ^ W + r').testBit (k - 1) = false := by
            apply testBit_ge_of_lt (W := W + 1) (by rw [Nat.pow_succ]; omega) (by omega)
          rw [h1, testBit_ge_of_lt hr' (by omega)]

/-- `diesBy n t r`: within `n` steps from time `t`, depth `1` is white at some even time. -/
def diesBy : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | n + 1, t, r => (t % 2 == 0 && r % 2 == 0) || diesBy n (t + 1) (pstep r)

theorem prun_succ (r : Nat) : ∀ i, prun r (i + 1) = prun (pstep r) i := by
  intro i
  induction i generalizing r with
  | zero => rfl
  | succ i ihi => show pstep (prun r (i + 1)) = pstep (prun (pstep r) i); rw [ihi]

theorem diesBy_sound : ∀ n t r, diesBy n t r = true →
    ∃ i, i < n ∧ (t + i) % 2 = 0 ∧ prun r i % 2 = 0 := by
  intro n
  induction n with
  | zero => intro t r h; simp [diesBy] at h
  | succ n ih =>
    intro t r h
    simp only [diesBy, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨h1, h2⟩ | h
    · exact ⟨0, by omega, by simpa using h1, h2⟩
    · obtain ⟨i, hi, hti, hpi⟩ := ih (t + 1) (pstep r) h
      refine ⟨i + 1, by omega, by rw [show t + (i + 1) = t + 1 + i by omega]; exact hti, ?_⟩
      rw [prun_succ]; exact hpi

/-- Check all packed rows `r < m`. -/
def checkBelow (n : Nat) : Nat → Bool
  | 0 => true
  | m + 1 => diesBy n 0 m && checkBelow n m

theorem checkBelow_sound (n : Nat) : ∀ m, checkBelow n m = true → ∀ r, r < m → diesBy n 0 r = true := by
  intro m
  induction m with
  | zero => intro _ r hr; omega
  | succ m ih =>
    intro h r hr
    simp only [checkBelow, Bool.and_eq_true] at h
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hr) with hr | hr
    · exact ih h.2 r hr
    · subst hr; exact h.1

/-- Soundness: a successful check certifies `Q01` for all starts of width `≤ W` (death before
time `n`). -/
theorem q01_of_check (W n : Nat) (h : checkBelow n (2 ^ W) = true) (x : Nat → Bool)
    (hx : ∀ k, W < k → x k = false) : ∃ j, 2 * j < n ∧ zrow x (2 * j) 1 = false := by
  obtain ⟨r, hr, hrx⟩ := exists_pack W x hx
  obtain ⟨i, hi, hti, hpi⟩ := diesBy_sound n 0 r (checkBelow_sound n _ h r hr)
  refine ⟨i / 2, by omega, ?_⟩
  rw [show 2 * (i / 2) = i by omega, ← zrow_congr hrx, run_toFun]
  simp only [toFun]
  simp [hpi]

theorem check_16 : checkBelow 34 (2 ^ 16) = true := by decide +kernel

/-- **`Q01` for every start of width at most `16`** (kernel-checked): every start supported at
depths `≤ 16` has a white cell at depth `1` at some even step `< 34`. -/
theorem q01_width_le_16 (x : Nat → Bool) (hx : ∀ k, 16 < k → x k = false) :
    ∃ j, 2 * j < 34 ∧ zrow x (2 * j) 1 = false :=
  q01_of_check 16 34 check_16 x hx

/-- The other phase: a start of width `≤ 15` cannot keep depth `1` black at every odd step. -/
theorem q01_width_le_15_odd (x : Nat → Bool) (hx : ∀ k, 15 < k → x k = false) :
    ∃ j, 2 * j < 34 ∧ zrow x (2 * j + 1) 1 = false := by
  obtain ⟨j, hj, h⟩ := q01_width_le_16 (zrow x 1) (fun k hk => zrow_fin hx 1 k (by omega))
  refine ⟨j, hj, ?_⟩
  rw [show 2 * j + 1 = 1 + 2 * j by omega, zrow_shift]
  exact h

/-! ### Exact Isomorphism with `IntegerForm`, Semiflow, and One-Step Bitwise Light-Cone Bounds -/

/-- `toFun r` coincides with `IntegerForm.rowOfNat r`. -/
theorem toFun_eq_rowOfNat (r : Nat) : toFun r = IntegerForm.rowOfNat r := by
  funext k
  cases k with
  | zero => rfl
  | succ j => rfl

/-- `pstep r` coincides with `IntegerForm.F r`. -/
theorem pstep_eq_F (r : Nat) : pstep r = IntegerForm.F r := rfl

/-- `prun r t` coincides with `IntegerForm.iter IntegerForm.F t r`. -/
theorem prun_eq_iter_F (r : Nat) : ∀ t : Nat, prun r t = IntegerForm.iter IntegerForm.F t r
  | 0 => rfl
  | t + 1 => by
    show pstep (prun r t) = IntegerForm.F (IntegerForm.iter IntegerForm.F t r)
    rw [prun_eq_iter_F r t, pstep_eq_F]

/-- `prun r (2 * s)` coincides with `IntegerForm.iter IntegerForm.G s r`. -/
theorem prun_two_mul_eq_iter_G (r s : Nat) :
    prun r (2 * s) = IntegerForm.iter IntegerForm.G s r := by
  rw [prun_eq_iter_F, ← IntegerForm.iter_G_eq_iter_F_two_mul]

/-- Time-additivity semiflow of `prun`: `prun r (s + t) = prun (prun r s) t`. -/
theorem prun_add (r s : Nat) : ∀ t : Nat, prun r (s + t) = prun (prun r s) t
  | 0 => rfl
  | t + 1 => by
    show pstep (prun r (s + t)) = pstep (prun (prun r s) t)
    rw [prun_add r s t]

/-- `0` is a fixed point of `pstep`. -/
theorem pstep_zero : pstep 0 = 0 := by decide

/-- `0` is a fixed point of `prun` at every step `t`. -/
theorem prun_zero : ∀ t : Nat, prun 0 t = 0
  | 0 => rfl
  | t + 1 => by show pstep (prun 0 t) = 0; rw [prun_zero t, pstep_zero]

/-- If `checkBelow n m = true`, then every natural number `Y < m` reaches an even integer under
`IntegerForm.iter IntegerForm.G s Y` at some step `s` with `2 * s < n`. -/
theorem iter_G_even_of_check {n m Y : Nat} (h : checkBelow n m = true) (hY : Y < m) :
    ∃ s : Nat, 2 * s < n ∧ IntegerForm.iter IntegerForm.G s Y % 2 = 0 := by
  obtain ⟨i, hi, hti, hpi⟩ := diesBy_sound n 0 Y (checkBelow_sound n m h Y hY)
  refine ⟨i / 2, by omega, ?_⟩
  rw [← prun_two_mul_eq_iter_G, show 2 * (i / 2) = i by omega]
  exact hpi

/-- **Bitwise light-cone bound for `pstep` (`testBit_pstep_ge_of_lt`):** if `Y < 2 ^ W`, then
every bit `k ≥ W + 1` of `pstep Y` is `false`. -/
theorem testBit_pstep_ge_of_lt {Y W k : Nat} (hY : Y < 2 ^ W) (hk : W + 1 ≤ k) :
    (pstep Y).testBit k = false := by
  unfold pstep
  simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_shiftLeft]
  have h1 : Y.testBit (1 + k) = false := testBit_ge_of_lt hY (by omega)
  have h2 : Y.testBit k = false := testBit_ge_of_lt hY (by omega)
  have h3 : Y.testBit (k - 1) = false := testBit_ge_of_lt hY (by omega)
  rw [h1, h2, h3]
  simp

end Rule30ZeroBoundarySmall
end Ruliology.CellularAutomata
