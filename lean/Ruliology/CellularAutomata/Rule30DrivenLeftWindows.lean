module

public import Ruliology.CellularAutomata.Rule30DrivenLeft

/-!
# Quantitative periodic windows in the driven left half

For a `P`-periodic driver and a start whose leftmost black cell is at `-m`, a
period-`P` agreement window of column `-1` starting at `T` has length at most
`T + P + m - 1`. Equivalently, a disagreement occurs before `2 * T + P + m`.
The bound holds for every positive `P` and `m`, every onset, and every such start.

The finite-window reconstruction lemma propagates trace agreement leftward
using the inverse local rule, then the bound contradicts the moving left edge.
It supplies a quantitative form of driven-left Jen,
not a new exclusion of a center-column period.

Original quantitative statement and proof: David Condrey,
`Rule30DrivenLHPRate.column_one_period_window_bound` (2026-10-02).
This port uses the kit's evolution and reconstruction theorems throughout.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30DrivenLeftWindows

open Rule30DrivenLeft

theorem window_columns_periodic (c : Nat → Bool) (s : Int → Bool)
    {P T N : Nat}
    (hc : ∀ t, T ≤ t → t ≤ T + N → c (t + P) = c t)
    (hwindow : ∀ t, T ≤ t → t < T + N → L c s (t + P) (-1) = L c s t (-1)) :
    ∀ n t, T ≤ t → t + n ≤ T + N →
      L c s (t + P) (-(n : Int)) = L c s t (-(n : Int)) := by
  have pair : ∀ n,
      (∀ t, T ≤ t → t + n ≤ T + N →
        L c s (t + P) (-(n : Int)) = L c s t (-(n : Int))) ∧
      (∀ t, T ≤ t → t + (n + 1) ≤ T + N →
        L c s (t + P) (-((n + 1 : Nat) : Int)) = L c s t (-((n + 1 : Nat) : Int))) := by
    intro n
    induction n with
    | zero =>
      constructor
      · intro t ht hw
        change L c s (t + P) 0 = L c s t 0
        rw [L_col0, L_col0]
        exact hc t ht (by omega)
      · intro t ht hw
        exact hwindow t ht (by omega)
    | succ n ih =>
      obtain ⟨hA, hB⟩ := ih
      refine ⟨hB, ?_⟩
      intro t ht hw
      have hposition : -((n + 1 + 1 : Nat) : Int) = -((n + 1 : Nat) : Int) - 1 := by omega
      have hright : -((n + 1 : Nat) : Int) + 1 = -(n : Int) := by omega
      rw [hposition, L_left (c := c) (s := s) (t + P) (by omega),
        L_left (c := c) (s := s) t (by omega),
        show t + P + 1 = (t + 1) + P by omega,
        hB (t + 1) (by omega) (by omega), hB t ht (by omega), hright,
        hA t ht (by omega)]
  exact fun n => (pair n).1

theorem column_neg_one_period_window_bound (c : Nat → Bool) (s : Int → Bool)
    {P m T N : Nat} (hP : 0 < P) (hm : 0 < m)
    (hc : ∀ t, c (t + P) = c t)
    (hs0 : ∀ p : Int, p < -(m : Int) → s p = false)
    (hs1 : s (-(m : Int)) = true)
    (hwindow : ∀ t, T ≤ t → t < T + N → L c s (t + P) (-1) = L c s t (-1)) :
    N + 1 ≤ T + P + m := by
  apply Nat.gt_of_not_le
  intro hN
  have hdeep := window_columns_periodic c s (fun t _ _ => hc t) hwindow
    (m + (T + P)) T (Nat.le_refl _) (by omega)
  have hblack := (edge (c := c) hs0 hs1 hm (T + P)).2
  have hwhite := (edge (c := c) hs0 hs1 hm T).1 (-((m + (T + P) : Nat) : Int)) (by omega)
  rw [hblack, hwhite] at hdeep
  exact Bool.noConfusion hdeep

theorem exists_period_disagreement_before (c : Nat → Bool) (s : Int → Bool)
    {P m : Nat} (hP : 0 < P) (hm : 0 < m)
    (hc : ∀ t, c (t + P) = c t)
    (hs0 : ∀ p : Int, p < -(m : Int) → s p = false)
    (hs1 : s (-(m : Int)) = true) (T : Nat) :
    ∃ t, T ≤ t ∧ t < 2 * T + P + m ∧ L c s (t + P) (-1) ≠ L c s t (-1) := by
  classical
  apply Classical.byContradiction
  intro hnone
  have hwindow : ∀ t, T ≤ t → t < T + (T + P + m) →
      L c s (t + P) (-1) = L c s t (-1) := by
    intro t ht1 ht2
    apply Classical.byContradiction
    intro hne
    exact hnone ⟨t, ht1, by omega, hne⟩
  have hbound := column_neg_one_period_window_bound c s hP hm hc hs0 hs1 hwindow
  omega

/-! ### Finite-window driver periodicity, arbitrary-depth column-pair propagation, and depth-sharpened window bounds -/

/-- **Finite-Window Driver Periodicity Bound (`column_neg_one_period_window_bound_local`):**
weakens the global driver periodicity hypothesis `∀ t, c (t + P) = c t` of
`column_neg_one_period_window_bound` to the finite interval `T ≤ t ≤ T + N`, proving
`N + 1 ≤ T + P + m`. -/
theorem column_neg_one_period_window_bound_local (c : Nat → Bool) (s : Int → Bool)
    {P m T N : Nat} (hP : 0 < P) (hm : 0 < m)
    (hc : ∀ t, T ≤ t → t ≤ T + N → c (t + P) = c t)
    (hs0 : ∀ p : Int, p < -(m : Int) → s p = false)
    (hs1 : s (-(m : Int)) = true)
    (hwindow : ∀ t, T ≤ t → t < T + N → L c s (t + P) (-1) = L c s t (-1)) :
    N + 1 ≤ T + P + m := by
  apply Classical.byContradiction
  intro hN
  have hdeep := window_columns_periodic c s hc hwindow
    (m + (T + P)) T (Nat.le_refl _) (by omega)
  have hblack := (edge (c := c) hs0 hs1 hm (T + P)).2
  have hwhite := (edge (c := c) hs0 hs1 hm T).1 (-((m + (T + P) : Nat) : Int)) (by omega)
  rw [hblack, hwhite] at hdeep
  exact Bool.noConfusion hdeep

/-- **Finite-Horizon Driver Disagreement Witness (`exists_period_disagreement_before_local`):**
if `c (t + P) = c t` merely for `T ≤ t ≤ 2 * T + P + m`, then column `-1` must disagree with its
`P`-translate at some tick `t ∈ [T, 2 * T + P + m)`. -/
theorem exists_period_disagreement_before_local (c : Nat → Bool) (s : Int → Bool)
    {P m T : Nat} (hP : 0 < P) (hm : 0 < m)
    (hc : ∀ t, T ≤ t → t ≤ 2 * T + P + m → c (t + P) = c t)
    (hs0 : ∀ p : Int, p < -(m : Int) → s p = false)
    (hs1 : s (-(m : Int)) = true) :
    ∃ t, T ≤ t ∧ t < 2 * T + P + m ∧ L c s (t + P) (-1) ≠ L c s t (-1) := by
  classical
  apply Classical.byContradiction
  intro hnone
  have hwindow : ∀ t, T ≤ t → t < T + (T + P + m) →
      L c s (t + P) (-1) = L c s t (-1) := by
    intro t ht1 ht2
    apply Classical.byContradiction
    intro hne
    exact hnone ⟨t, ht1, by omega, hne⟩
  have hc_win : ∀ t, T ≤ t → t ≤ T + (T + P + m) → c (t + P) = c t :=
    fun t ht1 ht2 => hc t ht1 (by omega)
  have hbound := column_neg_one_period_window_bound_local c s hP hm hc_win hs0 hs1 hwindow
  omega

/-- **Arbitrary-Depth Column-Pair Periodicity Propagation (`window_columns_periodic_from_col`):**
if two adjacent columns `-(k : Int)` and `-((k + 1 : Nat) : Int)` agree with period `P` on
`[T, T + N]` and `[T, T + N)` respectively, then for every `n, t` with `T ≤ t` and
`t + n ≤ T + N`, column `-((k + n : Nat) : Int)` agrees with period `P` at tick `t`. -/
theorem window_columns_periodic_from_col (c : Nat → Bool) (s : Int → Bool)
    {P T N k : Nat}
    (hcol0 : ∀ t, T ≤ t → t ≤ T + N →
      L c s (t + P) (-(k : Int)) = L c s t (-(k : Int)))
    (hcol1 : ∀ t, T ≤ t → t < T + N →
      L c s (t + P) (-((k + 1 : Nat) : Int)) = L c s t (-((k + 1 : Nat) : Int))) :
    ∀ n t, T ≤ t → t + n ≤ T + N →
      L c s (t + P) (-((k + n : Nat) : Int)) = L c s t (-((k + n : Nat) : Int)) := by
  have pair : ∀ n,
      (∀ t, T ≤ t → t + n ≤ T + N →
        L c s (t + P) (-((k + n : Nat) : Int)) = L c s t (-((k + n : Nat) : Int))) ∧
      (∀ t, T ≤ t → t + (n + 1) ≤ T + N →
        L c s (t + P) (-((k + (n + 1) : Nat) : Int)) = L c s t (-((k + (n + 1) : Nat) : Int))) := by
    intro n
    induction n with
    | zero =>
      constructor
      · intro t ht hw
        simpa using hcol0 t ht (by omega)
      · intro t ht hw
        simpa using hcol1 t ht (by omega)
    | succ n ih =>
      obtain ⟨hA, hB⟩ := ih
      refine ⟨hB, ?_⟩
      intro t ht hw
      have hpos : -((k + (n + 1 + 1) : Nat) : Int) = -((k + (n + 1) : Nat) : Int) - 1 := by omega
      have hright : -((k + (n + 1) : Nat) : Int) + 1 = -((k + n : Nat) : Int) := by omega
      rw [hpos, L_left (c := c) (s := s) (t + P) (by omega),
        L_left (c := c) (s := s) t (by omega),
        show t + P + 1 = (t + 1) + P by omega,
        hB (t + 1) (by omega) (by omega), hB t ht (by omega), hright,
        hA t ht (by omega)]
  exact fun n => (pair n).1

/-- **Depth-Sharpened Period-Window Bound (`column_pair_period_window_bound`):**
for a start `s` with leftmost black cell at `-m` (`0 < m`) and any depth `k ≤ m + T`, if
columns `-(k : Int)` and `-((k + 1 : Nat) : Int)` agree with period `P > 0` on `[T, T + N]` and
`[T, T + N)`, then `N + 1 + k ≤ T + P + m`. -/
theorem column_pair_period_window_bound (c : Nat → Bool) (s : Int → Bool)
    {P m T N k : Nat} (hP : 0 < P) (hm : 0 < m) (hk : k ≤ m + T)
    (hs0 : ∀ p : Int, p < -(m : Int) → s p = false)
    (hs1 : s (-(m : Int)) = true)
    (hcol0 : ∀ t, T ≤ t → t ≤ T + N →
      L c s (t + P) (-(k : Int)) = L c s t (-(k : Int)))
    (hcol1 : ∀ t, T ≤ t → t < T + N →
      L c s (t + P) (-((k + 1 : Nat) : Int)) = L c s t (-((k + 1 : Nat) : Int))) :
    N + 1 + k ≤ T + P + m := by
  apply Classical.byContradiction
  intro hN
  have hdeep := window_columns_periodic_from_col c s hcol0 hcol1
    (m + (T + P) - k) T (Nat.le_refl _) (by omega)
  have hidx : k + (m + (T + P) - k) = m + (T + P) := by omega
  rw [hidx] at hdeep
  have hblack := (edge (c := c) hs0 hs1 hm (T + P)).2
  have hwhite := (edge (c := c) hs0 hs1 hm T).1 (-((m + (T + P) : Nat) : Int)) (by omega)
  rw [hblack, hwhite] at hdeep
  exact Bool.noConfusion hdeep

/-- **Depth-Sharpened Column-Pair Disagreement Horizon (`exists_column_pair_disagreement_before`):**
for any `0 < P`, `0 < m`, and `k ≤ m + T`, if column `-(k : Int)` has period `P` on
`[T, 2 * T + P + m - k]`, then column `-((k + 1 : Nat) : Int)` must disagree with its
`P`-translate at some tick `t ∈ [T, 2 * T + P + m - k)`. -/
theorem exists_column_pair_disagreement_before (c : Nat → Bool) (s : Int → Bool)
    {P m T k : Nat} (hP : 0 < P) (hm : 0 < m) (hk : k ≤ m + T)
    (hs0 : ∀ p : Int, p < -(m : Int) → s p = false)
    (hs1 : s (-(m : Int)) = true)
    (hcol0 : ∀ t, T ≤ t → t ≤ 2 * T + P + m - k →
      L c s (t + P) (-(k : Int)) = L c s t (-(k : Int))) :
    ∃ t, T ≤ t ∧ t < 2 * T + P + m - k ∧
      L c s (t + P) (-((k + 1 : Nat) : Int)) ≠ L c s t (-((k + 1 : Nat) : Int)) := by
  classical
  apply Classical.byContradiction
  intro hnone
  have hcol1 : ∀ t, T ≤ t → t < T + (T + P + m - k) →
      L c s (t + P) (-((k + 1 : Nat) : Int)) = L c s t (-((k + 1 : Nat) : Int)) := by
    intro t ht1 ht2
    apply Classical.byContradiction
    intro hne
    exact hnone ⟨t, ht1, by omega, hne⟩
  have hcol0' : ∀ t, T ≤ t → t ≤ T + (T + P + m - k) →
      L c s (t + P) (-(k : Int)) = L c s t (-(k : Int)) :=
    fun t ht1 ht2 => hcol0 t ht1 (by omega)
  have hbound := column_pair_period_window_bound c s hP hm hk hs0 hs1 hcol0' hcol1
  omega

end Ruliology.CellularAutomata.Rule30DrivenLeftWindows
