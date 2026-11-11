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

end Ruliology.CellularAutomata.Rule30DrivenLeftWindows
