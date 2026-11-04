module

public import Ruliology.CellularAutomata.Rule30BlackRunErosion
public import Ruliology.CellularAutomata.Rule30LeftUnbounded

/-!
# Rule30SettledBarrier

Settled white diagonals and their black companions bound actual center runs. Both linear run bounds admit every fixed additive margin at sufficiently late times.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30SettledBarrier

open Ruliology.CellularAutomata
open Rule30Jen Rule30Prize Rule30Diagonals Rule30CenterRuns
open Rule30BlackRunErosion Rule30LeftReset Rule30LeftUnbounded

theorem no_stripe_at_constant (t k : Nat) (b : Bool)
    (h0 : D k t = b) (h1 : D k (t + 1) = b)
    (hrow : ∀ i : Int, (k : Int) - t - 2 ≤ i → i ≤ (k : Int) - t →
      cell t i = alt i) : False := by
  have hc : D k t = alt ((k : Int) - t) := hrow _ (by omega) (by omega)
  have hnext : D k (t + 1) = !(alt ((k : Int) - t)) := by
    show rule (cell t ((k : Int) - (t + 1) - 1))
      (cell t ((k : Int) - (t + 1)))
      (cell t ((k : Int) - (t + 1) + 1)) = _
    rw [hrow _ (by omega) (by omega), hrow _ (by omega) (by omega),
      hrow _ (by omega) (by omega)]
    rw [show (k : Int) - (t + 1) - 1 = ((k : Int) - t - 1) - 1 by omega,
      show (k : Int) - (t + 1) = (k : Int) - t - 1 by omega,
      show (k : Int) - t - 1 + 1 = (k : Int) - t by omega]
    rw [alt_pred, alt_pred]
    unfold rule
    cases alt ((k : Int) - t) <;> rfl
  rw [h0] at hc
  rw [h1, ← hc] at hnext
  cases b <;> cases hnext

theorem black_run_at_white_depth (a L k T s r : Nat)
    (ha : a = k + 5 * s + r) (hT : T ≤ a - s)
    (hw : ∀ t, T ≤ t → D k t = false)
    (h : ∀ i, i < L → center (a + i) = true) :
    L ≤ 3 * s + r + 2 := by
  refine Classical.byContradiction fun hlarge => ?_
  have hb := black_block_back a L h s (by omega)
  apply no_stripe_at_constant (a - s) k false (hw _ hT) (hw _ (by omega))
  intro i hi1 hi2
  exact hb i (by omega) (by omega)

theorem black_run_bound_at_white (k T : Nat)
    (hw : ∀ t, T ≤ t → D k t = false)
    (a L : Nat) (ha : k ≤ a) (hT : 5 * T ≤ 4 * a + k)
    (h : ∀ i, i < L → center (a + i) = true) :
    5 * L + 3 * k ≤ 3 * a + 18 := by
  let s := (a - k) / 5
  let r := (a - k) % 5
  have hsplit : a = k + 5 * s + r := by dsimp [s, r]; omega
  have hr : r < 5 := by dsimp [r]; omega
  have htime : T ≤ a - s := by dsimp [s]; omega
  have hb := black_run_at_white_depth a L k T s r hsplit htime hw h
  omega

theorem black_run_margin_unbounded (M : Nat) :
    ∃ A, ∀ a, A ≤ a → ∀ L,
      (∀ i, i < L → center (a + i) = true) → 5 * L + M ≤ 3 * a := by
  obtain ⟨k, hk, T, hT⟩ := D_infinitely_many_white (M + 18)
  refine ⟨k + 5 * T, ?_⟩
  intro a ha L h
  have hb := black_run_bound_at_white k T hT a L (by omega) (by omega) h
  omega

theorem preRow_pair_pin (n ell : Nat) (hn : 2 ≤ n)
    (hw : preRow n ell = false) (hb : preRow (n - 2) ell = true) :
    ell + 3 = n := by
  have hp := preRow_eq_true hb
  have hz := preRow_eq_false hw
  omega

theorem white_run_pair_front (a L j ell : Nat) (hj : j + 2 ≤ a)
    (hlen : a - j < L)
    (hrow : ∀ n, n < L → cell a (-(n : Int)) = preRow n ell)
    (hw : D j a = false) (hb : D (j + 2) a = true) :
    ell + 3 = a - j := by
  have hz := hrow (a - j) hlen
  rw [cell_neg_eq_D a (a - j) (by omega),
    show a - (a - j) = j by omega, hw] at hz
  have hp := hrow ((a - j) - 2) (by omega)
  rw [cell_neg_eq_D a ((a - j) - 2) (by omega),
    show a - ((a - j) - 2) = j + 2 by omega, hb] at hp
  exact preRow_pair_pin (a - j) ell (by omega) hz.symm hp.symm

theorem white_run_bound_two_pairs (j k a L : Nat) (hjk : j < k) (hka : k + 2 ≤ a)
    (hwj : D j a = false) (hbj : D (j + 2) a = true)
    (hwk : D k a = false) (hbk : D (k + 2) a = true)
    (h : ∀ i, i < L → center (a + i) = false) :
    L + j ≤ a := by
  refine Classical.byContradiction fun hlarge => ?_
  obtain ⟨ell, hrow⟩ := row_at_start a L (by omega) h
  have hj := white_run_pair_front a L j ell (by omega) (by omega) hrow hwj hbj
  have hk := white_run_pair_front a L k ell hka (by omega) hrow hwk hbk
  omega

theorem white_run_margin_unbounded (M : Nat) :
    ∃ A, ∀ a, A ≤ a → ∀ L,
      (∀ i, i < L → center (a + i) = false) → L + M ≤ a := by
  obtain ⟨j, hj, hwj⟩ := D_infinitely_many_white M
  obtain ⟨k, hk, hwk⟩ := D_infinitely_many_white j
  obtain ⟨Tbj, hbj⟩ := D_black_after_white hwj
  obtain ⟨Tbk, hbk⟩ := D_black_after_white hwk
  obtain ⟨Twj, hwj⟩ := hwj
  obtain ⟨Twk, hwk⟩ := hwk
  refine ⟨k + 2 + Tbj + Tbk + Twj + Twk, ?_⟩
  intro a ha L h
  have hb := white_run_bound_two_pairs j k a L hk (by omega)
    (hwj a (by omega)) (hbj a (by omega))
    (hwk a (by omega)) (hbk a (by omega)) h
  omega

theorem center_run_margins_unbounded (M : Nat) :
    ∃ A, ∀ a, A ≤ a → ∀ L,
      ((∀ i, i < L → center (a + i) = true) → 5 * L + M ≤ 3 * a) ∧
      ((∀ i, i < L → center (a + i) = false) → L + M ≤ a) := by
  obtain ⟨Ab, hb⟩ := black_run_margin_unbounded M
  obtain ⟨Aw, hw⟩ := white_run_margin_unbounded M
  exact ⟨Ab + Aw, fun a ha L => ⟨hb a (by omega) L, hw a (by omega) L⟩⟩

/-! ### Single-Pair Parity Obstruction for White Runs and Generalized Constant-Diagonal Barriers -/

/-- **General Alternating-Stripe Obstruction at a 1-Step Constant Diagonal (`no_pat_at_constant`):**
for any alternating pattern `f : Int → Bool` (`∀ i, f (i - 1) = !f i`), if `D k t = D k (t + 1)`,
then row `t` cannot equal `f` on the 3-cell window `[k - t - 2, k - t]`. -/
theorem no_pat_at_constant (f : Int → Bool) (hf : ∀ i, f (i - 1) = !f i) (t k : Nat)
    (hconst : D k (t + 1) = D k t)
    (hrow : ∀ i : Int, (k : Int) - t - 2 ≤ i → i ≤ (k : Int) - t →
      cell t i = f i) : False := by
  have hc : D k t = f ((k : Int) - t) := hrow _ (by omega) (by omega)
  have hnext : D k (t + 1) = !(f ((k : Int) - t)) := by
    show rule (cell t ((k : Int) - (t + 1) - 1))
      (cell t ((k : Int) - (t + 1)))
      (cell t ((k : Int) - (t + 1) + 1)) = _
    rw [hrow _ (by omega) (by omega), hrow _ (by omega) (by omega),
      hrow _ (by omega) (by omega)]
    rw [show (k : Int) - (t + 1) - 1 = ((k : Int) - t - 1) - 1 by omega,
      show (k : Int) - (t + 1) = (k : Int) - t - 1 by omega,
      show (k : Int) - t - 1 + 1 = (k : Int) - t by omega]
    rw [hf, hf]
    unfold rule
    cases f ((k : Int) - t) <;> rfl
  rw [hconst, hc] at hnext
  revert hnext; cases f ((k : Int) - t) <;> decide

/-- **Opposite-Phase (`nalt`) Obstruction at a 1-Step Constant Diagonal (`no_nalt_at_constant`):**
if `D k (t + 1) = D k t`, then row `t` cannot equal `nalt` on `[k - t - 2, k - t]`. -/
theorem no_nalt_at_constant (t k : Nat) (hconst : D k (t + 1) = D k t)
    (hrow : ∀ i : Int, (k : Int) - t - 2 ≤ i → i ≤ (k : Int) - t →
      cell t i = nalt i) : False :=
  no_pat_at_constant nalt nalt_pred t k hconst hrow

/-- **Black-Run Bound from a Single 1-Step Diagonal Repetition (`black_run_at_const_step`):**
if `a = k + 5 * s + r` and diagonal `k` repeats its value once at `D k (a - s + 1) = D k (a - s)`,
then any black center run starting at `a` has length `L ≤ 3 * s + r + 2`. -/
theorem black_run_at_const_step (a L k s r : Nat)
    (ha : a = k + 5 * s + r)
    (hconst : D k (a - s + 1) = D k (a - s))
    (h : ∀ i, i < L → center (a + i) = true) :
    L ≤ 3 * s + r + 2 := by
  refine Classical.byContradiction fun hlarge => ?_
  have hb := black_block_back a L h s (by omega)
  apply no_pat_at_constant alt alt_pred (a - s) k hconst
  intro i hi1 hi2
  exact hb i (by omega) (by omega)

/-- **Black-Run Linear Bound at a Settled Black Diagonal (`black_run_bound_at_black`):**
if `D k t = true` for all `t ≥ T`, then for every `a ≥ k` with `5 * T ≤ 4 * a + k`, any black
center run of length `L` starting at `a` satisfies `5 * L + 3 * k ≤ 3 * a + 18`. -/
theorem black_run_bound_at_black (k T : Nat)
    (hb_diag : ∀ t, T ≤ t → D k t = true)
    (a L : Nat) (ha : k ≤ a) (hT : 5 * T ≤ 4 * a + k)
    (h : ∀ i, i < L → center (a + i) = true) :
    5 * L + 3 * k ≤ 3 * a + 18 := by
  let s := (a - k) / 5
  let r := (a - k) % 5
  have hsplit : a = k + 5 * s + r := by dsimp [s, r]; omega
  have hr : r < 5 := by dsimp [r]; omega
  have htime : T ≤ a - s := by dsimp [s]; omega
  have hconst : D k (a - s + 1) = D k (a - s) := by
    rw [hb_diag _ (by omega), hb_diag _ htime]
  have hb := black_run_at_const_step a L k s r hsplit hconst h
  omega

/-- **Parity-Refined `preRow` Pinning (`preRow_pair_pin_even`):** if `2 ≤ n`, `preRow n ell = false`,
and `preRow (n - 2) ell = true`, then both `ell + 3 = n` and `n % 2 = 0` hold. -/
theorem preRow_pair_pin_even (n ell : Nat) (hn : 2 ≤ n)
    (hw : preRow n ell = false) (hb : preRow (n - 2) ell = true) :
    ell + 3 = n ∧ n % 2 = 0 := by
  have hp := preRow_eq_true hb
  have hz := preRow_eq_false hw
  omega

/-- **Parity-Refined White-Run Front Pinning (`white_run_pair_front_even`):** if `j + 2 ≤ a`,
`a - j < L`, `D j a = false`, and `D (j + 2) a = true` at the start of a white center run of
length `L`, then `ell + 3 = a - j` and `(a - j) % 2 = 0`. -/
theorem white_run_pair_front_even (a L j ell : Nat) (hj : j + 2 ≤ a)
    (hlen : a - j < L)
    (hrow : ∀ n, n < L → cell a (-(n : Int)) = preRow n ell)
    (hw : D j a = false) (hb : D (j + 2) a = true) :
    ell + 3 = a - j ∧ (a - j) % 2 = 0 := by
  have hz := hrow (a - j) hlen
  rw [cell_neg_eq_D a (a - j) (by omega),
    show a - (a - j) = j by omega, hw] at hz
  have hp := hrow ((a - j) - 2) (by omega)
  rw [cell_neg_eq_D a ((a - j) - 2) (by omega),
    show a - ((a - j) - 2) = j + 2 by omega, hb] at hp
  exact preRow_pair_pin_even (a - j) ell (by omega) hz.symm hp.symm

/-- **Single-Time Single-Pair White-Run Bound for Odd `a - k` (`white_run_bound_one_pair_odd`):**
if `k + 2 ≤ a`, `(a - k) % 2 = 1`, `D k a = false`, and `D (k + 2) a = true`, then a single
white-black diagonal pair at time `a` forces `L + k ≤ a` for any white center run starting at `a`. -/
theorem white_run_bound_one_pair_odd (k a L : Nat) (hka : k + 2 ≤ a)
    (hodd : (a - k) % 2 = 1)
    (hwk : D k a = false) (hbk : D (k + 2) a = true)
    (h : ∀ i, i < L → center (a + i) = false) :
    L + k ≤ a := by
  refine Classical.byContradiction fun hlarge => ?_
  obtain ⟨ell, hrow⟩ := row_at_start a L (by omega) h
  have hk := white_run_pair_front_even a L k ell hka (by omega) hrow hwk hbk
  omega

/-- **Single-Pair White-Run Bound Across Two Consecutive Steps (`white_run_bound_single_pair`):**
if a single white-black diagonal pair `(k, k + 2)` (`k + 2 ≤ a`) holds at times `a` and `a + 1`
(`D k a = false`, `D (k + 2) a = true`, `D k (a + 1) = false`, `D (k + 2) (a + 1) = true`), then
any white center run of length `L` starting at `a` satisfies `L + k ≤ a + 2` (eliminating the
second settled pair required by `white_run_bound_two_pairs`). -/
theorem white_run_bound_single_pair (k a L : Nat) (hka : k + 2 ≤ a)
    (hw0 : D k a = false) (hb0 : D (k + 2) a = true)
    (hw1 : D k (a + 1) = false) (hb1 : D (k + 2) (a + 1) = true)
    (h : ∀ i, i < L → center (a + i) = false) :
    L + k ≤ a + 2 := by
  by_cases hpar : (a - k) % 2 = 1
  · have := white_run_bound_one_pair_odd k a L hka hpar hw0 hb0 h
    omega
  · have hodd1 : (a + 1 - k) % 2 = 1 := by omega
    have hshift : ∀ i, i < L - 1 → center (a + 1 + i) = false := by
      intro i hi
      rw [show a + 1 + i = a + (i + 1) by omega]
      exact h (i + 1) (by omega)
    have := white_run_bound_one_pair_odd k (a + 1) (L - 1) (by omega) hodd1 hw1 hb1 hshift
    omega

end Ruliology.CellularAutomata.Rule30SettledBarrier
