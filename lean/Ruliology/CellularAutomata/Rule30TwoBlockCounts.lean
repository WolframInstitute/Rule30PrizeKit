module

public import Ruliology.CellularAutomata.Rule30Prize
public import Ruliology.CellularAutomata.Rule30Diagonals

/-!
# Rule 30 Two-Block Transition Counts, Single-Row Three-Column Identities, and Problem 2 Equivalences

This module defines the four temporal 2-block transition counts (`count00`, `count01`, `count10`,
`count11`) for any Boolean sequence `f : Nat → Bool` and proves their unconditional conservation
identities and single-row spatial characterizations for the Rule 30 center column `center`:

* **General 2-block conservation laws (`block_counts_sum`, `blackCount_step_decomposition`,
  `transition_balance_10_01`, `discrepancy_eq_homogeneous_block_diff`,
  `heterogeneous_balance_eq_four_count10`):**
  For every horizon `n : Nat`,
  - `count00 f n + count01 f n + count10 f n + count11 f n = n`
  - `2 * (blackCount n : Int) - n = (count11 center n - count00 center n) + (1 - bit center n)`
  - `(count01 center n + count10 center n) - (count11 center n + count00 center n) =
      4 * count10 center n - n + 2 * (bit center n - 1)`
* **Single-row three-column characterizations (`center_block_11_eq_left_white`,
  `center_block_10_eq_left_black`, `center_block_01_eq_neighbors_diff`,
  `center_block_00_eq_white_symmetric`, `discrepancy_eq_spatial_three_column_diff`):**
  By the Rule 30 local update `center (t + 1) = rule (cell t (-1)) (center t) (cell t 1)`, each of
  the four temporal 2-blocks `(center t, center (t + 1))` is determined by the three middle cells
  `(-1, 0, 1)` of single row `t`. Summing over `t < n` gives the unconditional identity
  `2 * (blackCount n : Int) - n =
    (spatialBlackLeftWhiteCount n - spatialWhiteSymmetricCount n) + (1 - bit center n)`.
* **Equivalent forms of Problem 2 (`problem2_iff_block_imbalance_sublinear`,
  `problem2_iff_spatial_three_column_sublinear`):**
  `Rule30Prize.Problem2` holds if and only if `|count11 center n - count00 center n| = o(n)`, and
  if and only if `|spatialBlackLeftWhiteCount n - spatialWhiteSymmetricCount n| = o(n)`.

Contributed by Matthew Payton Ulrey with Antigravity (Google DeepMind) as Rule 30 Prize submission
`R30-20261106-2b2509`.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30TwoBlockCounts

open Rule30Jen Rule30Prize

-- ============================================================================
-- SECTION 1: General 2-Block Transition Counts & Algebraic Conservation Laws
-- ============================================================================

/-- Integer indicator of `f t` (`1` if `true`, `0` if `false`). -/
def bit (f : Nat → Bool) (t : Nat) : Int :=
  if f t then 1 else 0

/-- Count of `(false, false)` transitions in `[0, n)`. -/
def count00 (f : Nat → Bool) (n : Nat) : Nat :=
  ((List.range n).filter (fun i => !(f i) && !(f (i + 1)))).length

/-- Count of `(false, true)` transitions in `[0, n)`. -/
def count01 (f : Nat → Bool) (n : Nat) : Nat :=
  ((List.range n).filter (fun i => !(f i) && f (i + 1))).length

/-- Count of `(true, false)` transitions in `[0, n)`. -/
def count10 (f : Nat → Bool) (n : Nat) : Nat :=
  ((List.range n).filter (fun i => f i && !(f (i + 1)))).length

/-- Count of `(true, true)` transitions in `[0, n)`. -/
def count11 (f : Nat → Bool) (n : Nat) : Nat :=
  ((List.range n).filter (fun i => f i && f (i + 1))).length

/-- Count of `true` values of `f` in `[0, n)`. -/
def onesCount (f : Nat → Bool) (n : Nat) : Nat :=
  ((List.range n).filter f).length

theorem onesCount_center_eq_blackCount (n : Nat) :
    onesCount center n = blackCount n := rfl

private theorem filter_singleton_length (p : Nat → Bool) (n : Nat) :
    (List.filter p [n]).length = if p n then 1 else 0 := by
  cases h : p n <;> simp [List.filter, h]

theorem onesCount_succ (f : Nat → Bool) (n : Nat) :
    onesCount f (n + 1) = onesCount f n + if f n then 1 else 0 := by
  simp [onesCount, List.range_succ, List.filter_append, filter_singleton_length]

theorem count00_succ (f : Nat → Bool) (n : Nat) :
    count00 f (n + 1) = count00 f n + if (!(f n) && !(f (n + 1))) then 1 else 0 := by
  rw [count00, List.range_succ, List.filter_append, List.length_append, filter_singleton_length]
  rfl

theorem count01_succ (f : Nat → Bool) (n : Nat) :
    count01 f (n + 1) = count01 f n + if (!(f n) && f (n + 1)) then 1 else 0 := by
  rw [count01, List.range_succ, List.filter_append, List.length_append, filter_singleton_length]
  rfl

theorem count10_succ (f : Nat → Bool) (n : Nat) :
    count10 f (n + 1) = count10 f n + if (f n && !(f (n + 1))) then 1 else 0 := by
  rw [count10, List.range_succ, List.filter_append, List.length_append, filter_singleton_length]
  rfl

theorem count11_succ (f : Nat → Bool) (n : Nat) :
    count11 f (n + 1) = count11 f n + if (f n && f (n + 1)) then 1 else 0 := by
  rw [count11, List.range_succ, List.filter_append, List.length_append, filter_singleton_length]
  rfl

/-- **2-Block Partition Identity:** The four transition counts partition `[0, n)`. -/
theorem block_counts_sum (f : Nat → Bool) (n : Nat) :
    count00 f n + count01 f n + count10 f n + count11 f n = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [count00_succ, count01_succ, count10_succ, count11_succ]
    cases f k <;> cases f (k + 1) <;> simp <;> omega

/-- **First-Coordinate Marginal Identity:** `onesCount f n = count10 f n + count11 f n`. -/
theorem onesCount_step_decomposition (f : Nat → Bool) (n : Nat) :
    onesCount f n = count10 f n + count11 f n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [onesCount_succ, count10_succ, count11_succ]
    cases f k <;> cases f (k + 1) <;> simp <;> omega

/-- Center-column specialization of `onesCount_step_decomposition`. -/
theorem blackCount_step_decomposition (n : Nat) :
    blackCount n = count10 center n + count11 center n :=
  onesCount_step_decomposition center n

/-- **Alternating-Run Parity Conservation Law:**
`count10 f n - count01 f n = bit f 0 - bit f n`. -/
theorem transition_balance_10_01_general (f : Nat → Bool) (n : Nat) :
    (count10 f n : Int) - (count01 f n : Int) = bit f 0 - bit f n := by
  induction n with
  | zero => simp [count10, count01, bit]
  | succ k ih =>
    rw [count10_succ, count01_succ]
    unfold bit at *
    cases h0 : f 0 <;> cases hk : f k <;> cases hk1 : f (k + 1) <;> simp_all <;> omega

/-- Center-column specialization of `transition_balance_10_01_general` (using `center 0 = true`). -/
theorem transition_balance_10_01 (n : Nat) :
    (count10 center n : Int) - (count01 center n : Int) = 1 - bit center n := by
  have h := transition_balance_10_01_general center n
  have h0 : bit center 0 = 1 := rfl
  omega

/-- **General 2-Block Discrepancy Conservation Identity:**
For any sequence `f : Nat → Bool`, the discrepancy `2 * onesCount f n - n` equals the homogeneous
2-block difference `count11 f n - count00 f n` plus the boundary term `bit f 0 - bit f n`. -/
theorem discrepancy_eq_homogeneous_block_diff_general (f : Nat → Bool) (n : Nat) :
    2 * (onesCount f n : Int) - (n : Int) =
      ((count11 f n : Int) - (count00 f n : Int)) + (bit f 0 - bit f n) := by
  have h_sum : (count00 f n : Int) + (count01 f n : Int) + (count10 f n : Int) + (count11 f n : Int) = (n : Int) := by
    exact_mod_cast block_counts_sum f n
  have h_ones : (onesCount f n : Int) = (count10 f n : Int) + (count11 f n : Int) := by
    exact_mod_cast onesCount_step_decomposition f n
  have h_bal := transition_balance_10_01_general f n
  omega

/-- **Headline Theorem 1 (`discrepancy_eq_homogeneous_block_diff`):**
For all `n : Nat`, the Rule 30 center-column discrepancy `2 * blackCount n - n` equals the
homogeneous 2-block transition difference `count11 center n - count00 center n` up to the bounded
boundary bit `1 - bit center n ∈ {0, 1}`. -/
theorem discrepancy_eq_homogeneous_block_diff (n : Nat) :
    2 * (blackCount n : Int) - (n : Int) =
      ((count11 center n : Int) - (count00 center n : Int)) + (1 - bit center n) := by
  have h := discrepancy_eq_homogeneous_block_diff_general center n
  have h0 : bit center 0 = 1 := rfl
  rw [← onesCount_center_eq_blackCount]
  omega

/-- **Second-Order Derivative Discrepancy Identity:**
The balance between heterogeneous transitions (`01`, `10`, where `center t ≠ center (t+1)`) and
homogeneous transitions (`00`, `11`, where `center t = center (t+1)`) equals
`2 * (count01 + count10) - n`. -/
theorem derivative_discrepancy_identity (n : Nat) :
    ((count01 center n : Int) + (count10 center n : Int)) -
      ((count11 center n : Int) + (count00 center n : Int)) =
      2 * ((count01 center n : Int) + (count10 center n : Int)) - (n : Int) := by
  have h_sum : (count00 center n : Int) + (count01 center n : Int) +
      (count10 center n : Int) + (count11 center n : Int) = (n : Int) := by
    exact_mod_cast block_counts_sum center n
  omega

/-- **Headline Theorem 2 (`heterogeneous_balance_eq_four_count10`):**
The second-order transition balance `(count01 + count10) - (count11 + count00)` is governed up to
`2 * (bit center n - 1)` by `4 * count10 center n - n`. -/
theorem heterogeneous_balance_eq_four_count10 (n : Nat) :
    ((count01 center n : Int) + (count10 center n : Int)) -
      ((count11 center n : Int) + (count00 center n : Int)) =
      4 * (count10 center n : Int) - (n : Int) + 2 * (bit center n - 1) := by
  have h_deriv := derivative_discrepancy_identity n
  have h_bal := transition_balance_10_01 n
  omega

-- ============================================================================
-- SECTION 2: Exact Single-Row Three-Column Characterizations of Center 2-Blocks
-- ============================================================================

/-- **Rule 30 Local Characterization of `(1, 1)` Center Transitions:**
Because `center (t + 1) = xor (cell t (-1)) (center t || cell t 1)`, when `center t = true` we have
`center (t + 1) = !(cell t (-1))`. Thus `(center t, center (t + 1)) = (true, true)` holds if and
only if `center t = true` and the left neighbor `cell t (-1)` is white (`false`). -/
theorem center_block_11_eq_left_white (t : Nat) :
    (center t && center (t + 1)) = (center t && !(cell t (-1))) := by
  change (cell t 0 && rule (cell t (-1)) (cell t 0) (cell t 1)) = (cell t 0 && !(cell t (-1)))
  cases cell t (-1) <;> cases cell t 0 <;> cases cell t 1 <;> rfl

/-- **Rule 30 Local Characterization of `(1, 0)` Center Transitions:**
`(center t, center (t + 1)) = (true, false)` holds if and only if both `center t` and its left
neighbor `cell t (-1)` are black (`true`). -/
theorem center_block_10_eq_left_black (t : Nat) :
    (center t && !(center (t + 1))) = (center t && cell t (-1)) := by
  change (cell t 0 && !(rule (cell t (-1)) (cell t 0) (cell t 1))) = (cell t 0 && cell t (-1))
  cases cell t (-1) <;> cases cell t 0 <;> cases cell t 1 <;> rfl

/-- **Rule 30 Local Characterization of `(0, 1)` Center Transitions:**
When `center t = false`, `center (t + 1) = xor (cell t (-1)) (cell t 1)`. Thus
`(center t, center (t + 1)) = (false, true)` holds if and only if `center t = false` and its two
spatial neighbors `cell t (-1)` and `cell t 1` have opposite colors. -/
theorem center_block_01_eq_neighbors_diff (t : Nat) :
    (!(center t) && center (t + 1)) = (!(center t) && xor (cell t (-1)) (cell t 1)) := by
  change (!(cell t 0) && rule (cell t (-1)) (cell t 0) (cell t 1)) =
    (!(cell t 0) && xor (cell t (-1)) (cell t 1))
  cases cell t (-1) <;> cases cell t 0 <;> cases cell t 1 <;> rfl

/-- **Rule 30 Local Characterization of `(0, 0)` Center Transitions:**
When `center t = false`, `center (t + 1) = false` holds if and only if the two spatial neighbors
`cell t (-1)` and `cell t 1` have the same color (`cell t (-1) == cell t 1`). -/
theorem center_block_00_eq_white_symmetric (t : Nat) :
    (!(center t) && !(center (t + 1))) = (!(center t) && (cell t (-1) == cell t 1)) := by
  change (!(cell t 0) && !(rule (cell t (-1)) (cell t 0) (cell t 1))) =
    (!(cell t 0) && (cell t (-1) == cell t 1))
  cases cell t (-1) <;> cases cell t 0 <;> cases cell t 1 <;> rfl

/-- Single-time spatial count of steps `t < n` where `center t = true` and `cell t (-1) = false`. -/
def spatialBlackLeftWhiteCount (n : Nat) : Nat :=
  ((List.range n).filter (fun t => center t && !(cell t (-1)))).length

/-- Single-time spatial count of steps `t < n` where `center t = true` and `cell t (-1) = true`. -/
def spatialBlackLeftBlackCount (n : Nat) : Nat :=
  ((List.range n).filter (fun t => center t && cell t (-1))).length

/-- Single-time spatial count of steps `t < n` where `center t = false` and `cell t (-1) == cell t 1`. -/
def spatialWhiteSymmetricCount (n : Nat) : Nat :=
  ((List.range n).filter (fun t => !(center t) && (cell t (-1) == cell t 1))).length

/-- Single-time spatial count of steps `t < n` where `center t = false` and `xor (cell t (-1)) (cell t 1)`. -/
def spatialWhiteAsymmetricCount (n : Nat) : Nat :=
  ((List.range n).filter (fun t => !(center t) && xor (cell t (-1)) (cell t 1))).length

theorem count11_eq_spatialBlackLeftWhiteCount (n : Nat) :
    count11 center n = spatialBlackLeftWhiteCount n := by
  unfold count11 spatialBlackLeftWhiteCount
  congr 1
  apply List.filter_congr
  intro t _
  exact center_block_11_eq_left_white t

theorem count10_eq_spatialBlackLeftBlackCount (n : Nat) :
    count10 center n = spatialBlackLeftBlackCount n := by
  unfold count10 spatialBlackLeftBlackCount
  congr 1
  apply List.filter_congr
  intro t _
  exact center_block_10_eq_left_black t

theorem count00_eq_spatialWhiteSymmetricCount (n : Nat) :
    count00 center n = spatialWhiteSymmetricCount n := by
  unfold count00 spatialWhiteSymmetricCount
  congr 1
  apply List.filter_congr
  intro t _
  exact center_block_00_eq_white_symmetric t

theorem count01_eq_spatialWhiteAsymmetricCount (n : Nat) :
    count01 center n = spatialWhiteAsymmetricCount n := by
  unfold count01 spatialWhiteAsymmetricCount
  congr 1
  apply List.filter_congr
  intro t _
  exact center_block_01_eq_neighbors_diff t

/-- **Headline Theorem 3 (`discrepancy_eq_spatial_three_column_diff`):**
Unconditional identity expressing the temporal center-column discrepancy `2 * blackCount n - n`
purely in terms of single-time spatial three-column patterns `(cell t (-1), cell t 0, cell t 1)`
summed over `t < n`. -/
theorem discrepancy_eq_spatial_three_column_diff (n : Nat) :
    2 * (blackCount n : Int) - (n : Int) =
      ((spatialBlackLeftWhiteCount n : Int) - (spatialWhiteSymmetricCount n : Int)) +
        (1 - bit center n) := by
  rw [← count11_eq_spatialBlackLeftWhiteCount, ← count00_eq_spatialWhiteSymmetricCount]
  exact discrepancy_eq_homogeneous_block_diff n

-- ============================================================================
-- SECTION 3: Unconditional Bidirectional Equivalences for Problem 2
-- ============================================================================

/-- Pointwise triangle-inequality bound between `|2 * blackCount n - n|` and
`|count11 center n - count00 center n|`: they differ by at most `1` for every `n`. -/
theorem natAbs_discrepancy_sub_block_imbalance_le_one (n : Nat) :
    (2 * (blackCount n : Int) - (n : Int)).natAbs ≤
      ((count11 center n : Int) - (count00 center n : Int)).natAbs + 1 ∧
    ((count11 center n : Int) - (count00 center n : Int)).natAbs ≤
      (2 * (blackCount n : Int) - (n : Int)).natAbs + 1 := by
  have h := discrepancy_eq_homogeneous_block_diff n
  unfold bit at h
  cases hcn : center n <;> simp [hcn] at h <;> omega

private theorem two_mul_mul_succ (k x : Nat) : 2 * (k * (x + 1)) = (2 * k) * x + 2 * k := by
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_add, ← Nat.mul_assoc]

/-- **Headline Theorem 4 (`problem2_iff_block_imbalance_sublinear`):**
Unconditional equivalence: `Rule30Prize.Problem2` holds if and only if the homogeneous 2-block
transition imbalance `|count11 center n - count00 center n|` grows sublinearly (`o(n)`). -/
theorem problem2_iff_block_imbalance_sublinear :
    Problem2 ↔
      ∀ k : Nat, 0 < k → ∃ N : Nat, ∀ n : Nat, N ≤ n →
        k * ((count11 center n : Int) - (count00 center n : Int)).natAbs ≤ n := by
  constructor
  · intro hp2 k hk
    obtain ⟨N, hN⟩ := hp2 (2 * k) (by omega)
    refine ⟨max N (2 * k), fun n hn => ?_⟩
    have hnN : N ≤ n := by omega
    have hnk : 2 * k ≤ n := by omega
    have h_step := hN n hnN
    have h_diff := (natAbs_discrepancy_sub_block_imbalance_le_one n).2
    have h1 := Nat.mul_le_mul_left k h_diff
    have h2 := two_mul_mul_succ k (2 * (blackCount n : Int) - (n : Int)).natAbs
    omega
  · intro himb k hk
    obtain ⟨N, hN⟩ := himb (2 * k) (by omega)
    refine ⟨max N (2 * k), fun n hn => ?_⟩
    have hnN : N ≤ n := by omega
    have hnk : 2 * k ≤ n := by omega
    have h_step := hN n hnN
    have h_diff := (natAbs_discrepancy_sub_block_imbalance_le_one n).1
    have h1 := Nat.mul_le_mul_left k h_diff
    have h2 := two_mul_mul_succ k ((count11 center n : Int) - (count00 center n : Int)).natAbs
    omega

/-- **Headline Theorem 5 (`problem2_iff_spatial_three_column_sublinear`):**
Unconditional equivalence: `Rule30Prize.Problem2` holds if and only if the single-time spatial
three-column balance `|spatialBlackLeftWhiteCount n - spatialWhiteSymmetricCount n|` grows
sublinearly (`o(n)`). -/
theorem problem2_iff_spatial_three_column_sublinear :
    Problem2 ↔
      ∀ k : Nat, 0 < k → ∃ N : Nat, ∀ n : Nat, N ≤ n →
        k * ((spatialBlackLeftWhiteCount n : Int) - (spatialWhiteSymmetricCount n : Int)).natAbs ≤ n := by
  rw [problem2_iff_block_imbalance_sublinear]
  constructor <;> intro h k hk <;> obtain ⟨N, hN⟩ := h k hk <;> refine ⟨N, fun n hn => ?_⟩
  · rw [← count11_eq_spatialBlackLeftWhiteCount, ← count00_eq_spatialWhiteSymmetricCount]
    exact hN n hn
  · rw [count11_eq_spatialBlackLeftWhiteCount, count00_eq_spatialWhiteSymmetricCount]
    exact hN n hn

-- ============================================================================
-- SECTION 4: Bitwise Complement Duality, Second-Coordinate Marginals, and
--            Incoming-Black Problem 2 Equivalence
-- ============================================================================

/-- **Bitwise Complement Duality for `count00` and `count11` (`count00_not`).** -/
theorem count00_not (f : Nat → Bool) (n : Nat) :
    count00 (fun i => !(f i)) n = count11 f n := by
  unfold count00 count11
  congr 1
  apply List.filter_congr
  intro i _
  dsimp only
  cases f i <;> cases f (i + 1) <;> rfl

/-- **Bitwise Complement Duality for `count11` and `count00` (`count11_not`).** -/
theorem count11_not (f : Nat → Bool) (n : Nat) :
    count11 (fun i => !(f i)) n = count00 f n := rfl

/-- **Bitwise Complement Duality for `count01` and `count10` (`count01_not`).** -/
theorem count01_not (f : Nat → Bool) (n : Nat) :
    count01 (fun i => !(f i)) n = count10 f n := by
  unfold count01 count10
  congr 1
  apply List.filter_congr
  intro i _
  dsimp only
  cases f i <;> cases f (i + 1) <;> rfl

/-- **Bitwise Complement Duality for `count10` and `count01` (`count10_not`).** -/
theorem count10_not (f : Nat → Bool) (n : Nat) :
    count10 (fun i => !(f i)) n = count01 f n := by
  unfold count10 count01
  congr 1
  apply List.filter_congr
  intro i _
  dsimp only
  cases f i <;> cases f (i + 1) <;> rfl

/-- **Complement Partition Identity for `onesCount` (`onesCount_not_add_onesCount`).** -/
theorem onesCount_not_add_onesCount (f : Nat → Bool) (n : Nat) :
    onesCount (fun i => !(f i)) n + onesCount f n = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [onesCount_succ, onesCount_succ]
    cases f k <;> simp <;> omega

/-- **Sign-Reversal of Homogeneous 2-Block Imbalance Under Bitwise Complement (`homogeneous_imbalance_not`).** -/
theorem homogeneous_imbalance_not (f : Nat → Bool) (n : Nat) :
    (count11 (fun i => !(f i)) n : Int) - (count00 (fun i => !(f i)) n : Int) =
      -((count11 f n : Int) - (count00 f n : Int)) := by
  rw [count11_not, count00_not]
  omega

/-- **First-Coordinate Zero-Marginal Identity (`zeros_marginal_eq_count00_add_count01`):**
`count00 f n + count01 f n + onesCount f n = n`. -/
theorem zeros_marginal_eq_count00_add_count01 (f : Nat → Bool) (n : Nat) :
    count00 f n + count01 f n + onesCount f n = n := by
  have h1 := block_counts_sum f n
  have h2 := onesCount_step_decomposition f n
  omega

/-- **Second-Coordinate Marginal Identity (`onesCount_shift_one_eq_count01_add_count11`):**
`onesCount (fun i => f (i + 1)) n = count01 f n + count11 f n`. -/
theorem onesCount_shift_one_eq_count01_add_count11 (f : Nat → Bool) (n : Nat) :
    onesCount (fun i => f (i + 1)) n = count01 f n + count11 f n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [onesCount_succ, count01_succ, count11_succ]
    cases f k <;> cases f (k + 1) <;> simp <;> omega

/-- **Shifted Center-Column Black-Count Decomposition (`blackCount_succ_eq_one_add_count01_add_count11`):**
for every `n : Nat`, `blackCount (n + 1) = 1 + count01 center n + count11 center n`. -/
theorem blackCount_succ_eq_one_add_count01_add_count11 (n : Nat) :
    blackCount (n + 1) = 1 + count01 center n + count11 center n := by
  rw [← onesCount_center_eq_blackCount]
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [onesCount_succ, count01_succ, count11_succ]
    cases center k <;> cases center (k + 1) <;> simp <;> omega

/-- **Universal `±1` Bound Between `count10` and `count01` (`natAbs_count10_sub_count01_le_one`).** -/
theorem natAbs_count10_sub_count01_le_one (f : Nat → Bool) (n : Nat) :
    ((count10 f n : Int) - (count01 f n : Int)).natAbs ≤ 1 := by
  have h := transition_balance_10_01_general f n
  unfold bit at h
  cases h0 : f 0 <;> cases hn : f n <;> simp [h0, hn] at h <;> omega

/-- **One-Sided Alternating-Switch Sandwich for the Center Column (`center_count01_le_count10_and_le_succ`):**
because `center 0 = true`, `count01 center n ≤ count10 center n ≤ count01 center n + 1`. -/
theorem center_count01_le_count10_and_le_succ (n : Nat) :
    count01 center n ≤ count10 center n ∧ count10 center n ≤ count01 center n + 1 := by
  have h := transition_balance_10_01 n
  unfold bit at h
  cases hcn : center n <;> simp [hcn] at h <;> omega

/-- **Spatial Three-Column Partition Identity (`spatial_four_counts_sum`)** and
**Spatial Decomposition of `blackCount` (`blackCount_eq_spatial_black_sum`).** -/
theorem spatial_four_counts_sum_and_blackCount (n : Nat) :
    spatialWhiteSymmetricCount n + spatialWhiteAsymmetricCount n +
      spatialBlackLeftBlackCount n + spatialBlackLeftWhiteCount n = n ∧
    blackCount n = spatialBlackLeftBlackCount n + spatialBlackLeftWhiteCount n := by
  rw [← count00_eq_spatialWhiteSymmetricCount, ← count01_eq_spatialWhiteAsymmetricCount,
    ← count10_eq_spatialBlackLeftBlackCount, ← count11_eq_spatialBlackLeftWhiteCount]
  exact ⟨block_counts_sum center n, blackCount_step_decomposition n⟩

/-- Pointwise bound between `|2 * blackCount n - n|` and the incoming-black 2-block discrepancy
`|2 * (count01 center n + count11 center n) - n|`: they differ by at most `2`. -/
theorem natAbs_discrepancy_sub_incoming_black_le_two (n : Nat) :
    (2 * (blackCount n : Int) - (n : Int)).natAbs ≤
      (2 * ((count01 center n : Int) + (count11 center n : Int)) - (n : Int)).natAbs + 2 ∧
    (2 * ((count01 center n : Int) + (count11 center n : Int)) - (n : Int)).natAbs ≤
      (2 * (blackCount n : Int) - (n : Int)).natAbs + 2 := by
  have h_ones : (blackCount n : Int) = (count10 center n : Int) + (count11 center n : Int) := by
    exact_mod_cast blackCount_step_decomposition n
  have h_bal := transition_balance_10_01 n
  unfold bit at h_bal
  cases hcn : center n <;> simp [hcn] at h_bal <;> omega

private theorem two_mul_mul_add_two (k x : Nat) : 2 * (k * (x + 2)) = (2 * k) * x + 4 * k := by
  rw [Nat.mul_add, Nat.mul_add, ← Nat.mul_assoc]
  omega

/-- **Incoming-Black Marginal Equivalence for `Problem2` (`problem2_iff_incoming_black_sublinear`):**
`Rule30Prize.Problem2` holds iff `|2 * (count01 center n + count11 center n) - n| = o(n)`. -/
theorem problem2_iff_incoming_black_sublinear :
    Problem2 ↔
      ∀ k : Nat, 0 < k → ∃ N : Nat, ∀ n : Nat, N ≤ n →
        k * (2 * ((count01 center n : Int) + (count11 center n : Int)) - (n : Int)).natAbs ≤ n := by
  constructor
  · intro hp2 k hk
    obtain ⟨N, hN⟩ := hp2 (2 * k) (by omega)
    refine ⟨max N (4 * k), fun n hn => ?_⟩
    have hnN : N ≤ n := by omega
    have hnk : 4 * k ≤ n := by omega
    have h_step := hN n hnN
    have h_diff := (natAbs_discrepancy_sub_incoming_black_le_two n).2
    have h1 := Nat.mul_le_mul_left k h_diff
    have h2 := two_mul_mul_add_two k (2 * (blackCount n : Int) - (n : Int)).natAbs
    omega
  · intro hin k hk
    obtain ⟨N, hN⟩ := hin (2 * k) (by omega)
    refine ⟨max N (4 * k), fun n hn => ?_⟩
    have hnN : N ≤ n := by omega
    have hnk : 4 * k ≤ n := by omega
    have h_step := hN n hnN
    have h_diff := (natAbs_discrepancy_sub_incoming_black_le_two n).1
    have h1 := Nat.mul_le_mul_left k h_diff
    have h2 := two_mul_mul_add_two k (2 * ((count01 center n : Int) + (count11 center n : Int)) - (n : Int)).natAbs
    omega

/-! ### Main-diagonal `D t t` identities and right-neighbour masking -/

/-- **Main-Diagonal Identity for `center` (`center_eq_D_diag`):**
for every tick `t`, `center t = Rule30Diagonals.D t t`. -/
theorem center_eq_D_diag (t : Nat) : center t = Rule30Diagonals.D t t := by
  unfold center Rule30Diagonals.D
  congr 1
  omega

/-- **Sub-Diagonal Identity for the Left Neighbour `cell t (-1)` (`cell_neg_one_eq_D_sub_one`):**
for every tick `t ≥ 1`, `cell t (-1) = Rule30Diagonals.D (t - 1) t`. -/
theorem cell_neg_one_eq_D_sub_one (t : Nat) (ht : 1 ≤ t) :
    cell t (-1) = Rule30Diagonals.D (t - 1) t := by
  unfold Rule30Diagonals.D
  congr 1
  omega

/-- **Super-Diagonal Identity for the Right Neighbour `cell t 1` (`cell_one_eq_D_add_one`):**
for every tick `t`, `cell t 1 = Rule30Diagonals.D (t + 1) t`. -/
theorem cell_one_eq_D_add_one (t : Nat) :
    cell t 1 = Rule30Diagonals.D (t + 1) t := by
  unfold Rule30Diagonals.D
  congr 1
  omega

/-- **One-Step Center Evolution in Terms of Spatial Neighbours (`center_succ_eq_rule`):**
`center (t + 1) = rule (cell t (-1)) (center t) (cell t 1)`. -/
theorem center_succ_eq_rule (t : Nat) :
    center (t + 1) = rule (cell t (-1)) (center t) (cell t 1) := rfl

/-- **Right-Neighbour Masking When `center t = true` (`center_succ_of_center_true`):**
whenever `center t = true`, the next center bit is the complement of the left neighbour (`!cell t (-1)`),
independently of the right neighbour `cell t 1`. -/
theorem center_succ_of_center_true (t : Nat) (hc : center t = true) :
    center (t + 1) = !cell t (-1) := by
  rw [center_succ_eq_rule, hc]
  unfold rule
  cases cell t (-1) <;> cases cell t 1 <;> rfl

end Rule30TwoBlockCounts
end Ruliology.CellularAutomata
