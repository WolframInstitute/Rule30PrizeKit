module

public import Ruliology.CellularAutomata.Rule30Prize
public import Ruliology.CellularAutomata.Rule30Diagonals

/-!
# Rule 30 Two-Block Transition Counts, Single-Row Three-Column Identities, and Problem 2 Equivalences

This module defines the four temporal 2-block transition counts (`count00`, `count01`, `count10`,
`count11`) for any Boolean sequence `f : Nat → Bool` and proves their unconditional conservation
identities, quadratic-variation and increment orthogonality laws, 2-step five-column left-shielding
identities for center 3-blocks (`count000`..`count111`), 4-to-8 palindrome 3-block reconstruction
and 4D Walsh-Hadamard parity identities, and single-row spatial characterizations for the Rule 30
center column `center`:

* **General 2-block conservation laws (`block_counts_sum`, `blackCount_step_decomposition`,
  `transition_balance_10_01`, `discrepancy_eq_homogeneous_block_diff`,
  `heterogeneous_balance_eq_four_count10`):**
  For every horizon `n : Nat`,
  - `count00 f n + count01 f n + count10 f n + count11 f n = n`
  - `2 * (blackCount n : Int) - n = (count11 center n - count00 center n) + (1 - bit center n)`
  - `(count01 center n + count10 center n) - (count11 center n + count00 center n) =
      4 * count10 center n - n + 2 * (bit center n - 1)`
* **Quadratic-variation conservation & increment orthogonality (`stepImb_sq_eq_homogeneous_step`,
  `two_mul_stepImb_sq_eq_one_sub_stepDeriv`, `stepImb_mul_stepDeriv_eq_neg_stepImb`,
  `two_mul_homogeneous_sum_eq_sub_derivativeDiscrepancy`,
  `sum_stepImb_mul_stepDeriv_eq_neg_block_imbalance`):**
  For the step increments `stepImb f t = bit11 f t - bit00 f t ∈ {-1, 0, 1}` and
  `stepDeriv f t = (bit01 f t + bit10 f t) - (bit11 f t + bit00 f t) ∈ {-1, 1}`, every step `t`
  satisfies `2 * (stepImb f t) ^ 2 = 1 - stepDeriv f t` and
  `stepImb f t * stepDeriv f t = - stepImb f t`, so cumulatively
  `2 * (count11 center n + count00 center n) = n - derivativeDiscrepancy center n`.
* **Single-row three-column characterizations (`center_block_11_eq_left_white`,
  `center_block_10_eq_left_black`, `center_block_01_eq_neighbors_diff`,
  `center_block_00_eq_white_symmetric`, `discrepancy_eq_spatial_three_column_diff`):**
  By the Rule 30 local update `center (t + 1) = rule (cell t (-1)) (center t) (cell t 1)`, each of
  the four temporal 2-blocks `(center t, center (t + 1))` is determined by the three middle cells
  `(-1, 0, 1)` of single row `t`. Summing over `t < n` gives the unconditional identity
  `2 * (blackCount n : Int) - n =
    (spatialBlackLeftWhiteCount n - spatialWhiteSymmetricCount n) + (1 - bit center n)`.
* **Center 3-block left-shielding & five-column characterizations (`center_block_111_eq_left_101`,
  `center_block_110_eq_left_001`, `center_two_step_black_independent_of_right`,
  `three_block_counts_sum`, `count11_step_decomposition`, `count00_step_decomposition`,
  `count111_eq_spatialLeft101Count`, `count110_eq_spatialLeft001Count`):**
  When `center t = true` and `cell t (-1) = false`, `center (t + 1) = true` acts as an OR-shield
  blocking all right-cone cells `x ≥ 1`, so `(center t, center (t + 1), center (t + 2)) = (1, 1, 1)`
  holds iff `(cell t (-2), cell t (-1), cell t 0) = (true, false, true)` (`center_block_111_eq_left_101`),
  and `(1, 1, 0)` holds iff `(cell t (-2), cell t (-1), cell t 0) = (false, false, true)`
  (`center_block_110_eq_left_001`), both completely independent of `(cell t 1, cell t 2)`.
* **De Bruijn flow conservation & cross-cone spatial conservation (`count011_sub_count110_eq_boundary`,
  `count001_sub_count100_eq_boundary`, `three_block_imbalance_decomposition`,
  `center_block_011_eq_spatial_cross`, `center_block_010_eq_spatial_cross`,
  `spatialCross011Count_sub_spatialLeft001Count_eq`):**
  For every horizon `n`, De Bruijn entry-exit conservation locks `count011 - count110 ∈ {-1, 0, 1}`
  and `count001 - count100 ∈ {-1, 0, 1}`, yielding the exact 3-block discrepancy decomposition
  `(c111 - c000) - (c010 - c101) = (c11 - c00) - (c01 - c10) + O(1)` and the unconditional
  Cross-Cone Conservation Law locking 4-cell left-right cross-cone patterns within `±1` of purely
  left-cone patterns (`spatialCross011Count n - spatialLeft001Count n ∈ {-1, 0}`).
* **4-to-8 Palindrome 3-block reconstruction & 4D Walsh-Hadamard spectral identities
  (`singleton_imbalance_add_chiral_diff_eq_transition_balance`,
  `center_singleton_imbalance_add_chiral_diff`, `derivativeDiscrepancy_eq_palindrome_three_block_diff`,
  `rotated_palindrome_white_identity`, `rotated_palindrome_black_identity`,
  `four_mul_count100_eq_palindrome_reconstruction`, `four_mul_count011_eq_palindrome_reconstruction`,
  `walshParity3`, `walshParity3_eq_discrepancy_add_four_singleton_imbalance`):**
  The four chiral 3-blocks (`001, 011, 100, 110`) cancel identically out of `derivativeDiscrepancy`,
  decouple via `D ± D_∂` into pure white/black palindrome pairs (`c101 - c000` and `c010 - c111`),
  and are uniquely reconstructed up to `O(1)` from `n` and the four palindrome 3-blocks
  `(000, 010, 101, 111)`. In the 4D Walsh-Hadamard basis, `walshParity3` satisfies
  `W_111 = D + 4*(c010 - c101) + O(1)`.
* **Equivalent forms of Problem 2 and second-order balance (`problem2_iff_block_imbalance_sublinear`,
  `problem2_iff_spatial_three_column_sublinear`,
  `derivative_sublinear_iff_four_count10_sublinear`):**
  `Rule30Prize.Problem2` holds if and only if `|count11 center n - count00 center n| = o(n)`, and
  if and only if `|spatialBlackLeftWhiteCount n - spatialWhiteSymmetricCount n| = o(n)`.

Contributed by Matthew Payton Ulrey with Antigravity (Google DeepMind) as Rule 30 Prize submissions
`R30-20261106-2b2509` and `R30-20261118-e6618f`.
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

-- ============================================================================
-- SECTION 5: Quadratic-Variation Conservation & Increment Orthogonality Laws
-- ============================================================================

/-- Step indicator (`0` or `1`) of a `(false, false)` transition at step `t`. -/
def bit00 (f : Nat → Bool) (t : Nat) : Int :=
  if !(f t) && !(f (t + 1)) then 1 else 0

/-- Step indicator (`0` or `1`) of a `(false, true)` transition at step `t`. -/
def bit01 (f : Nat → Bool) (t : Nat) : Int :=
  if !(f t) && f (t + 1) then 1 else 0

/-- Step indicator (`0` or `1`) of a `(true, false)` transition at step `t`. -/
def bit10 (f : Nat → Bool) (t : Nat) : Int :=
  if f t && !(f (t + 1)) then 1 else 0

/-- Step indicator (`0` or `1`) of a `(true, true)` transition at step `t`. -/
def bit11 (f : Nat → Bool) (t : Nat) : Int :=
  if f t && f (t + 1) then 1 else 0

/-- Step increment of homogeneous 2-block imbalance `count11 - count00` at step `t`,
taking values in `{-1, 0, 1}`. -/
def stepImb (f : Nat → Bool) (t : Nat) : Int :=
  bit11 f t - bit00 f t

/-- Step increment of the second-order derivative discrepancy `(count01 + count10) - (count11 + count00)`
at step `t`, taking values in `{-1, 1}`. -/
def stepDeriv (f : Nat → Bool) (t : Nat) : Int :=
  (bit01 f t + bit10 f t) - (bit11 f t + bit00 f t)

/-- Cumulative second-order derivative discrepancy `(count01 + count10) - (count11 + count00)`. -/
def derivativeDiscrepancy (f : Nat → Bool) (n : Nat) : Int :=
  ((count01 f n : Int) + (count10 f n : Int)) - ((count11 f n : Int) + (count00 f n : Int))

/-- Cumulative cross-product of `stepImb f t` and `stepDeriv f t` over `t < n`. -/
def stepCrossSum (f : Nat → Bool) : Nat → Int
  | 0 => 0
  | n + 1 => stepCrossSum f n + stepImb f n * stepDeriv f n

/-- **Pointwise Quadratic Variation of Homogeneous Imbalance:**
Because `bit11 f t` and `bit00 f t` are mutually exclusive `{0, 1}` indicators, the squared step
increment `(stepImb f t) ^ 2` equals `bit11 f t + bit00 f t`. -/
theorem stepImb_sq_eq_homogeneous_step (f : Nat → Bool) (t : Nat) :
    stepImb f t * stepImb f t = bit11 f t + bit00 f t := by
  unfold stepImb bit11 bit00
  cases f t <;> cases f (t + 1) <;> rfl

/-- **Pointwise Quadratic-Variation Conservation Law:**
At every step `t`, twice the squared imbalance increment equals `1 - stepDeriv f t`. -/
theorem two_mul_stepImb_sq_eq_one_sub_stepDeriv (f : Nat → Bool) (t : Nat) :
    2 * (stepImb f t * stepImb f t) = 1 - stepDeriv f t := by
  unfold stepImb stepDeriv bit00 bit01 bit10 bit11
  cases f t <;> cases f (t + 1) <;> rfl

/-- **Pointwise Increment Orthogonality Law (`stepImb_mul_stepDeriv_eq_neg_stepImb`):**
Whenever `stepImb f t ≠ 0` (a homogeneous transition `00` or `11`), `stepDeriv f t = -1`, whereas
whenever `stepDeriv f t = +1` (a heterogeneous transition `01` or `10`), `stepImb f t = 0`. Hence
`stepImb f t * stepDeriv f t = - stepImb f t` identically at every step `t`. -/
theorem stepImb_mul_stepDeriv_eq_neg_stepImb (f : Nat → Bool) (t : Nat) :
    stepImb f t * stepDeriv f t = - stepImb f t := by
  unfold stepImb stepDeriv bit00 bit01 bit10 bit11
  cases f t <;> cases f (t + 1) <;> rfl

/-- **Unit Modulus of Derivative Step Increments:**
Every step `t` is either homogeneous (`stepDeriv = -1`) or heterogeneous (`stepDeriv = +1`), so
`stepDeriv f t * stepDeriv f t = 1`. -/
theorem stepDeriv_sq_eq_one (f : Nat → Bool) (t : Nat) :
    stepDeriv f t * stepDeriv f t = 1 := by
  unfold stepDeriv bit00 bit01 bit10 bit11
  cases f t <;> cases f (t + 1) <;> rfl

/-- **Headline Theorem 6 (`two_mul_homogeneous_sum_eq_sub_derivativeDiscrepancy`):**
Unconditional cumulative quadratic-variation conservation law: for any Boolean sequence `f` and
horizon `n`, twice the homogeneous 2-block count `2 * (count11 f n + count00 f n)` equals
`n - derivativeDiscrepancy f n`. -/
theorem two_mul_homogeneous_sum_eq_sub_derivativeDiscrepancy (f : Nat → Bool) (n : Nat) :
    2 * ((count11 f n : Int) + (count00 f n : Int)) = (n : Int) - derivativeDiscrepancy f n := by
  unfold derivativeDiscrepancy
  have h_sum : (count00 f n : Int) + (count01 f n : Int) +
      (count10 f n : Int) + (count11 f n : Int) = (n : Int) := by
    exact_mod_cast block_counts_sum f n
  omega

/-- Dual form for heterogeneous transitions: `2 * (count01 f n + count10 f n) = n + derivativeDiscrepancy f n`. -/
theorem two_mul_heterogeneous_sum_eq_add_derivativeDiscrepancy (f : Nat → Bool) (n : Nat) :
    2 * ((count01 f n : Int) + (count10 f n : Int)) = (n : Int) + derivativeDiscrepancy f n := by
  unfold derivativeDiscrepancy
  have h_sum : (count00 f n : Int) + (count01 f n : Int) +
      (count10 f n : Int) + (count11 f n : Int) = (n : Int) := by
    exact_mod_cast block_counts_sum f n
  omega

/-- **Exact Equipartition at Derivative Zero Crossings:**
At any horizon `n` where `derivativeDiscrepancy f n = 0`, the homogeneous and heterogeneous 2-block
sums are exactly equal: `count11 f n + count00 f n = count01 f n + count10 f n`. -/
theorem homogeneous_sum_eq_heterogeneous_sum_iff_derivativeDiscrepancy_zero (f : Nat → Bool) (n : Nat) :
    count11 f n + count00 f n = count01 f n + count10 f n ↔ derivativeDiscrepancy f n = 0 := by
  unfold derivativeDiscrepancy
  omega

/-- **Headline Theorem 7 (`sum_stepImb_mul_stepDeriv_eq_neg_block_imbalance`):**
The cumulative cross-product of `stepImb f t` and `stepDeriv f t` over `t < n` equals
`- (count11 f n - count00 f n)`. -/
theorem sum_stepImb_mul_stepDeriv_eq_neg_block_imbalance (f : Nat → Bool) (n : Nat) :
    stepCrossSum f n = - ((count11 f n : Int) - (count00 f n : Int)) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [stepCrossSum, ih, stepImb_mul_stepDeriv_eq_neg_stepImb, count11_succ, count00_succ]
    unfold stepImb bit11 bit00
    cases f k <;> cases f (k + 1) <;> simp <;> omega

/-- Pointwise bound between `|derivativeDiscrepancy center n|` and `|4 * count10 center n - n|`:
they differ by at most `2` for every `n`. -/
theorem natAbs_derivativeDiscrepancy_sub_four_count10_le_two (n : Nat) :
    (derivativeDiscrepancy center n).natAbs ≤
      (4 * (count10 center n : Int) - (n : Int)).natAbs + 2 ∧
    (4 * (count10 center n : Int) - (n : Int)).natAbs ≤
      (derivativeDiscrepancy center n).natAbs + 2 := by
  have h := heterogeneous_balance_eq_four_count10 n
  change derivativeDiscrepancy center n = 4 * (count10 center n : Int) - (n : Int) + 2 * (bit center n - 1) at h
  unfold bit at h
  cases hcn : center n <;> simp [hcn] at h <;> omega

/-- **Second-Order Sublinear Equivalence (`derivative_sublinear_iff_four_count10_sublinear`):**
The second-order derivative discrepancy `|derivativeDiscrepancy center n|` grows sublinearly (`o(n)`)
if and only if `|4 * count10 center n - n|` grows sublinearly (`o(n)`, i.e., `(1, 0)` transitions
have asymptotic density `1/4`). -/
theorem derivative_sublinear_iff_four_count10_sublinear :
    (∀ k : Nat, 0 < k → ∃ N : Nat, ∀ n : Nat, N ≤ n →
      k * (derivativeDiscrepancy center n).natAbs ≤ n) ↔
    (∀ k : Nat, 0 < k → ∃ N : Nat, ∀ n : Nat, N ≤ n →
      k * (4 * (count10 center n : Int) - (n : Int)).natAbs ≤ n) := by
  constructor
  · intro hderiv k hk
    obtain ⟨N, hN⟩ := hderiv (2 * k) (by omega)
    refine ⟨max N (4 * k), fun n hn => ?_⟩
    have hnN : N ≤ n := by omega
    have hnk : 4 * k ≤ n := by omega
    have h_step := hN n hnN
    have h_diff := (natAbs_derivativeDiscrepancy_sub_four_count10_le_two n).2
    have h1 := Nat.mul_le_mul_left k h_diff
    have h2 := two_mul_mul_add_two k (derivativeDiscrepancy center n).natAbs
    omega
  · intro hc10 k hk
    obtain ⟨N, hN⟩ := hc10 (2 * k) (by omega)
    refine ⟨max N (4 * k), fun n hn => ?_⟩
    have hnN : N ≤ n := by omega
    have hnk : 4 * k ≤ n := by omega
    have h_step := hN n hnN
    have h_diff := (natAbs_derivativeDiscrepancy_sub_four_count10_le_two n).1
    have h1 := Nat.mul_le_mul_left k h_diff
    have h2 := two_mul_mul_add_two k (4 * (count10 center n : Int) - (n : Int)).natAbs
    omega

-- ============================================================================
-- SECTION 6: Center 3-Block Left-Shielding & Five-Column Spatial Identities
-- ============================================================================

/-- Count of `(0, 0, 0)` 3-block transitions in `[0, n)`. -/
def count000 (f : Nat → Bool) (n : Nat) : Nat :=
  ((List.range n).filter (fun i => !(f i) && !(f (i + 1)) && !(f (i + 2)))).length

/-- Count of `(0, 0, 1)` 3-block transitions in `[0, n)`. -/
def count001 (f : Nat → Bool) (n : Nat) : Nat :=
  ((List.range n).filter (fun i => !(f i) && !(f (i + 1)) && f (i + 2))).length

/-- Count of `(0, 1, 0)` 3-block transitions in `[0, n)`. -/
def count010 (f : Nat → Bool) (n : Nat) : Nat :=
  ((List.range n).filter (fun i => !(f i) && f (i + 1) && !(f (i + 2)))).length

/-- Count of `(0, 1, 1)` 3-block transitions in `[0, n)`. -/
def count011 (f : Nat → Bool) (n : Nat) : Nat :=
  ((List.range n).filter (fun i => !(f i) && f (i + 1) && f (i + 2))).length

/-- Count of `(1, 0, 0)` 3-block transitions in `[0, n)`. -/
def count100 (f : Nat → Bool) (n : Nat) : Nat :=
  ((List.range n).filter (fun i => f i && !(f (i + 1)) && !(f (i + 2)))).length

/-- Count of `(1, 0, 1)` 3-block transitions in `[0, n)`. -/
def count101 (f : Nat → Bool) (n : Nat) : Nat :=
  ((List.range n).filter (fun i => f i && !(f (i + 1)) && f (i + 2))).length

/-- Count of `(1, 1, 0)` 3-block transitions in `[0, n)`. -/
def count110 (f : Nat → Bool) (n : Nat) : Nat :=
  ((List.range n).filter (fun i => f i && f (i + 1) && !(f (i + 2)))).length

/-- Count of `(1, 1, 1)` 3-block transitions in `[0, n)`. -/
def count111 (f : Nat → Bool) (n : Nat) : Nat :=
  ((List.range n).filter (fun i => f i && f (i + 1) && f (i + 2))).length

theorem count000_succ (f : Nat → Bool) (n : Nat) :
    count000 f (n + 1) = count000 f n + if (!(f n) && !(f (n + 1)) && !(f (n + 2))) then 1 else 0 := by
  rw [count000, List.range_succ, List.filter_append, List.length_append, filter_singleton_length]
  rfl

theorem count001_succ (f : Nat → Bool) (n : Nat) :
    count001 f (n + 1) = count001 f n + if (!(f n) && !(f (n + 1)) && f (n + 2)) then 1 else 0 := by
  rw [count001, List.range_succ, List.filter_append, List.length_append, filter_singleton_length]
  rfl

theorem count010_succ (f : Nat → Bool) (n : Nat) :
    count010 f (n + 1) = count010 f n + if (!(f n) && f (n + 1) && !(f (n + 2))) then 1 else 0 := by
  rw [count010, List.range_succ, List.filter_append, List.length_append, filter_singleton_length]
  rfl

theorem count011_succ (f : Nat → Bool) (n : Nat) :
    count011 f (n + 1) = count011 f n + if (!(f n) && f (n + 1) && f (n + 2)) then 1 else 0 := by
  rw [count011, List.range_succ, List.filter_append, List.length_append, filter_singleton_length]
  rfl

theorem count100_succ (f : Nat → Bool) (n : Nat) :
    count100 f (n + 1) = count100 f n + if (f n && !(f (n + 1)) && !(f (n + 2))) then 1 else 0 := by
  rw [count100, List.range_succ, List.filter_append, List.length_append, filter_singleton_length]
  rfl

theorem count101_succ (f : Nat → Bool) (n : Nat) :
    count101 f (n + 1) = count101 f n + if (f n && !(f (n + 1)) && f (n + 2)) then 1 else 0 := by
  rw [count101, List.range_succ, List.filter_append, List.length_append, filter_singleton_length]
  rfl

theorem count110_succ (f : Nat → Bool) (n : Nat) :
    count110 f (n + 1) = count110 f n + if (f n && f (n + 1) && !(f (n + 2))) then 1 else 0 := by
  rw [count110, List.range_succ, List.filter_append, List.length_append, filter_singleton_length]
  rfl

theorem count111_succ (f : Nat → Bool) (n : Nat) :
    count111 f (n + 1) = count111 f n + if (f n && f (n + 1) && f (n + 2)) then 1 else 0 := by
  rw [count111, List.range_succ, List.filter_append, List.length_append, filter_singleton_length]
  rfl

/-- **3-Block Partition Identity:** The eight 3-block counts partition `[0, n)`. -/
theorem three_block_counts_sum (f : Nat → Bool) (n : Nat) :
    count000 f n + count001 f n + count010 f n + count011 f n +
      count100 f n + count101 f n + count110 f n + count111 f n = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [count000_succ, count001_succ, count010_succ, count011_succ,
      count100_succ, count101_succ, count110_succ, count111_succ]
    cases f k <;> cases f (k + 1) <;> cases f (k + 2) <;> simp <;> omega

/-- **2-Block `(1, 1)` Marginal Decomposition:** `count11 f n = count110 f n + count111 f n`. -/
theorem count11_step_decomposition (f : Nat → Bool) (n : Nat) :
    count11 f n = count110 f n + count111 f n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [count11_succ, count110_succ, count111_succ]
    cases f k <;> cases f (k + 1) <;> cases f (k + 2) <;> simp <;> omega

/-- **2-Block `(0, 0)` Marginal Decomposition:** `count00 f n = count000 f n + count001 f n`. -/
theorem count00_step_decomposition (f : Nat → Bool) (n : Nat) :
    count00 f n = count000 f n + count001 f n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [count00_succ, count000_succ, count001_succ]
    cases f k <;> cases f (k + 1) <;> cases f (k + 2) <;> simp <;> omega

/-- Explicit two-step expansion of `center (t + 2)` in terms of the five cells
`(-2, -1, 0, 1, 2)` of row `t`. -/
theorem center_add_two_eq_five_column (t : Nat) :
    center (t + 2) =
      rule
        (rule (cell t (-2)) (cell t (-1)) (cell t 0))
        (rule (cell t (-1)) (cell t 0) (cell t 1))
        (rule (cell t 0) (cell t 1) (cell t 2)) := rfl

/-- **Headline Theorem 8 (`center_two_step_black_independent_of_right`):**
Whenever `center t = true` and `cell t (-1) = false` (so `center (t + 1) = true`), both `center t`
and `center (t + 1)` act as absorbing OR-shields blocking all right-cone cells `x ≥ 1`. Consequently,
`center (t + 2)` equals `cell t (-2)`—completely independent of `cell t 1` and `cell t 2`. -/
theorem center_two_step_black_independent_of_right (t : Nat)
    (hc0 : center t = true) (hm1 : cell t (-1) = false) :
    center (t + 2) = cell t (-2) := by
  rw [center_add_two_eq_five_column]
  change cell t 0 = true at hc0
  rw [hc0, hm1]
  cases cell t (-2) <;> cases cell t 1 <;> cases cell t 2 <;> rfl

/-- **Headline Theorem 9 (`center_block_111_eq_left_101`):**
A 3-step black run `(center t, center (t + 1), center (t + 2)) = (true, true, true)` occurs at time `t`
if and only if the three left-half cells `(cell t (-2), cell t (-1), cell t 0)` equal `(true, false, true)`,
completely independent of the right-cone cells `cell t 1` and `cell t 2`. -/
theorem center_block_111_eq_left_101 (t : Nat) :
    (center t && center (t + 1) && center (t + 2)) =
      (cell t (-2) && !(cell t (-1)) && center t) := by
  change (cell t 0 && rule (cell t (-1)) (cell t 0) (cell t 1) &&
      rule (rule (cell t (-2)) (cell t (-1)) (cell t 0))
           (rule (cell t (-1)) (cell t 0) (cell t 1))
           (rule (cell t 0) (cell t 1) (cell t 2))) =
    (cell t (-2) && !(cell t (-1)) && cell t 0)
  cases cell t (-2) <;> cases cell t (-1) <;> cases cell t 0 <;>
    cases cell t 1 <;> cases cell t 2 <;> rfl

/-- **Headline Theorem 10 (`center_block_110_eq_left_001`):**
A `(true, true, false)` center 3-block occurs at time `t` if and only if the three left-half cells
`(cell t (-2), cell t (-1), cell t 0)` equal `(false, false, true)`, completely independent of
`cell t 1` and `cell t 2`. -/
theorem center_block_110_eq_left_001 (t : Nat) :
    (center t && center (t + 1) && !(center (t + 2))) =
      (!(cell t (-2)) && !(cell t (-1)) && center t) := by
  change (cell t 0 && rule (cell t (-1)) (cell t 0) (cell t 1) &&
      !(rule (rule (cell t (-2)) (cell t (-1)) (cell t 0))
             (rule (cell t (-1)) (cell t 0) (cell t 1))
             (rule (cell t 0) (cell t 1) (cell t 2)))) =
    (!(cell t (-2)) && !(cell t (-1)) && cell t 0)
  cases cell t (-2) <;> cases cell t (-1) <;> cases cell t 0 <;>
    cases cell t 1 <;> cases cell t 2 <;> rfl

/-- Single-time spatial count of steps `t < n` where `(cell t (-2), cell t (-1), center t) = (true, false, true)`. -/
def spatialLeft101Count (n : Nat) : Nat :=
  ((List.range n).filter (fun t => cell t (-2) && !(cell t (-1)) && center t)).length

/-- Single-time spatial count of steps `t < n` where `(cell t (-2), cell t (-1), center t) = (false, false, true)`. -/
def spatialLeft001Count (n : Nat) : Nat :=
  ((List.range n).filter (fun t => !(cell t (-2)) && !(cell t (-1)) && center t)).length

/-- Cumulative identity: `count111 center n = spatialLeft101Count n`. -/
theorem count111_eq_spatialLeft101Count (n : Nat) :
    count111 center n = spatialLeft101Count n := by
  unfold count111 spatialLeft101Count
  congr 1
  apply List.filter_congr
  intro t _
  exact center_block_111_eq_left_101 t

/-- Cumulative identity: `count110 center n = spatialLeft001Count n`. -/
theorem count110_eq_spatialLeft001Count (n : Nat) :
    count110 center n = spatialLeft001Count n := by
  unfold count110 spatialLeft001Count
  congr 1
  apply List.filter_congr
  intro t _
  exact center_block_110_eq_left_001 t

/-- **2-Block `(0, 1)` Marginal Decomposition:** `count01 f n = count010 f n + count011 f n`. -/
theorem count01_step_decomposition (f : Nat → Bool) (n : Nat) :
    count01 f n = count010 f n + count011 f n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [count01_succ, count010_succ, count011_succ]
    cases f k <;> cases f (k + 1) <;> cases f (k + 2) <;> simp <;> omega

/-- **2-Block `(1, 0)` Marginal Decomposition:** `count10 f n = count100 f n + count101 f n`. -/
theorem count10_step_decomposition (f : Nat → Bool) (n : Nat) :
    count10 f n = count100 f n + count101 f n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [count10_succ, count100_succ, count101_succ]
    cases f k <;> cases f (k + 1) <;> cases f (k + 2) <;> simp <;> omega

/-- **Headline Theorem 11 (`count011_sub_count110_eq_boundary` — De Bruijn `(1,1)` Run Entry-Exit Conservation):**
For any boolean sequence `f`, every `(0, 1, 1)` block enters a `(1, 1)` 2-block and every `(1, 1, 0)` block
exits a `(1, 1)` 2-block. Consequently, `count011 f n - count110 f n` equals the boundary indicator difference
between step `n` and step `0`, taking values strictly in `{-1, 0, 1}`. -/
theorem count011_sub_count110_eq_boundary (f : Nat → Bool) (n : Nat) :
    (count011 f n : Int) - (count110 f n : Int) =
      (if f n && f (n + 1) then (1 : Int) else 0) -
        (if f 0 && f 1 then (1 : Int) else 0) := by
  induction n with
  | zero =>
    simp [count011, count110]
  | succ k ih =>
    rw [count011_succ, count110_succ]
    push_cast
    cases h0 : f 0 <;> cases h1 : f 1 <;>
      cases hk : f k <;> cases hk1 : f (k + 1) <;> cases f (k + 2) <;>
      simp [h0, h1, hk, hk1] at ih ⊢ <;> omega

/-- **Headline Theorem 12 (`count001_sub_count100_eq_boundary` — De Bruijn `(0,0)` Run Entry-Exit Conservation):**
For any boolean sequence `f`, `count001 f n - count100 f n` equals the `(0, 0)` boundary indicator difference
between step `0` and step `n`, taking values strictly in `{-1, 0, 1}`. -/
theorem count001_sub_count100_eq_boundary (f : Nat → Bool) (n : Nat) :
    (count001 f n : Int) - (count100 f n : Int) =
      (if !(f 0) && !(f 1) then (1 : Int) else 0) -
        (if !(f n) && !(f (n + 1)) then (1 : Int) else 0) := by
  induction n with
  | zero =>
    simp [count001, count100]
  | succ k ih =>
    rw [count001_succ, count100_succ]
    push_cast
    cases h0 : f 0 <;> cases h1 : f 1 <;>
      cases hk : f k <;> cases hk1 : f (k + 1) <;> cases f (k + 2) <;>
      simp [h0, h1, hk, hk1] at ih ⊢ <;> omega

/-- **Headline Theorem 13 (`three_block_imbalance_decomposition` — Exact 3-Block Discrepancy Decomposition):**
For any boolean sequence `f`, the difference between the homogeneous 3-block persistence imbalance
`count111 f n - count000 f n` and the alternating 3-block singleton imbalance `count010 f n - count101 f n`
equals `(count11 f n - count00 f n) - (count01 f n - count10 f n)` plus the two bounded De Bruijn boundary
terms `(count011 f n - count110 f n) + (count001 f n - count100 f n)`. -/
theorem three_block_imbalance_decomposition (f : Nat → Bool) (n : Nat) :
    ((count111 f n : Int) - (count000 f n : Int)) -
      ((count010 f n : Int) - (count101 f n : Int)) =
      ((count11 f n : Int) - (count00 f n : Int)) -
        ((count01 f n : Int) - (count10 f n : Int)) +
        ((count011 f n : Int) - (count110 f n : Int)) +
        ((count001 f n : Int) - (count100 f n : Int)) := by
  have h11 := count11_step_decomposition f n
  have h00 := count00_step_decomposition f n
  have h01 := count01_step_decomposition f n
  have h10 := count10_step_decomposition f n
  omega

/-- **Headline Theorem 14 (`center_block_011_eq_spatial_cross`):**
A `(false, true, true)` center 3-block occurs at time `t` if and only if `center t = false`, the immediate
neighbors `cell t (-1)` and `cell t 1` are opposite (`xor = true`), and the left pair `cell t (-2)` and
`cell t (-1)` are equal (`!(xor) = true`), completely independent of `cell t 2`. -/
theorem center_block_011_eq_spatial_cross (t : Nat) :
    (!(center t) && center (t + 1) && center (t + 2)) =
      (!(center t) && Bool.xor (cell t (-1)) (cell t 1) && !(Bool.xor (cell t (-2)) (cell t (-1)))) := by
  change (!(cell t 0) && rule (cell t (-1)) (cell t 0) (cell t 1) &&
      rule (rule (cell t (-2)) (cell t (-1)) (cell t 0))
           (rule (cell t (-1)) (cell t 0) (cell t 1))
           (rule (cell t 0) (cell t 1) (cell t 2))) =
    (!(cell t 0) && Bool.xor (cell t (-1)) (cell t 1) && !(Bool.xor (cell t (-2)) (cell t (-1))))
  cases cell t (-2) <;> cases cell t (-1) <;> cases cell t 0 <;>
    cases cell t 1 <;> cases cell t 2 <;> rfl

/-- **Headline Theorem 15 (`center_block_010_eq_spatial_cross`):**
A `(false, true, false)` center 3-block occurs at time `t` if and only if `center t = false`, the immediate
neighbors `cell t (-1)` and `cell t 1` are opposite (`xor = true`), and the left pair `cell t (-2)` and
`cell t (-1)` are opposite (`xor = true`), completely independent of `cell t 2`. -/
theorem center_block_010_eq_spatial_cross (t : Nat) :
    (!(center t) && center (t + 1) && !(center (t + 2))) =
      (!(center t) && Bool.xor (cell t (-1)) (cell t 1) && Bool.xor (cell t (-2)) (cell t (-1))) := by
  change (!(cell t 0) && rule (cell t (-1)) (cell t 0) (cell t 1) &&
      !(rule (rule (cell t (-2)) (cell t (-1)) (cell t 0))
             (rule (cell t (-1)) (cell t 0) (cell t 1))
             (rule (cell t 0) (cell t 1) (cell t 2)))) =
    (!(cell t 0) && Bool.xor (cell t (-1)) (cell t 1) && Bool.xor (cell t (-2)) (cell t (-1)))
  cases cell t (-2) <;> cases cell t (-1) <;> cases cell t 0 <;>
    cases cell t 1 <;> cases cell t 2 <;> rfl

/-- Spatial cross-cone count of steps `t < n` where `center t = false`, `cell t (-1) ≠ cell t 1`, and `cell t (-2) = cell t (-1)`. -/
def spatialCross011Count (n : Nat) : Nat :=
  ((List.range n).filter (fun t =>
    !(center t) && Bool.xor (cell t (-1)) (cell t 1) && !(Bool.xor (cell t (-2)) (cell t (-1))))).length

/-- Cumulative identity: `count011 center n = spatialCross011Count n`. -/
theorem count011_eq_spatialCross011Count (n : Nat) :
    count011 center n = spatialCross011Count n := by
  unfold count011 spatialCross011Count
  congr 1
  apply List.filter_congr
  intro t _
  exact center_block_011_eq_spatial_cross t

/-- **Headline Theorem 16 (`spatialCross011Count_sub_spatialLeft001Count_eq` — Unconditional Cross-Cone Conservation Law):**
For every horizon `n`, the cumulative count of the 4-cell left-right cross-cone configuration
`spatialCross011Count n` (which couples `cell t 1` in the right half-cone with `cell t (-2) = cell t (-1)`
in the left half-cone) and the purely left-cone 3-cell configuration `spatialLeft001Count n`
(`(cell t (-2), cell t (-1), center t) = (false, false, true)`) are locked within `±1` of each other. -/
theorem spatialCross011Count_sub_spatialLeft001Count_eq (n : Nat) :
    (spatialCross011Count n : Int) - (spatialLeft001Count n : Int) =
      (if center n && center (n + 1) then (1 : Int) else 0) - 1 := by
  rw [← count011_eq_spatialCross011Count, ← count110_eq_spatialLeft001Count]
  have h := count011_sub_count110_eq_boundary center n
  have h01 : (center 0 && center 1) = true := rfl
  rw [h01] at h
  exact h

-- ============================================================================
-- SECTION 7: Palindrome 3-Block Reconstruction & Walsh-Hadamard Spectral Identities
-- ============================================================================

/-- **Headline Theorem 17 (`singleton_imbalance_add_chiral_diff_eq_transition_balance` — Singleton-Chiral Duality):**
For any boolean sequence `f` and horizon `n`, the singleton 3-block imbalance `(count010 f n - count101 f n)`
plus the chiral imbalance `(count011 f n - count100 f n)` equals the 2-block parity balance
`count01 f n - count10 f n`. Every excess singleton black run (`010` over `101`) is balanced
one-for-one by a chiral white-entry excess (`100` over `011`) up to `±1`. -/
theorem singleton_imbalance_add_chiral_diff_eq_transition_balance (f : Nat → Bool) (n : Nat) :
    ((count010 f n : Int) - (count101 f n : Int)) +
      ((count011 f n : Int) - (count100 f n : Int)) =
      (count01 f n : Int) - (count10 f n : Int) := by
  have h01 := count01_step_decomposition f n
  have h10 := count10_step_decomposition f n
  omega

/-- Center-column specialization of `singleton_imbalance_add_chiral_diff_eq_transition_balance`:
`(count010 center n - count101 center n) + (count011 center n - count100 center n) = bit center n - 1 ∈ {-1, 0}`. -/
theorem center_singleton_imbalance_add_chiral_diff (n : Nat) :
    ((count010 center n : Int) - (count101 center n : Int)) +
      ((count011 center n : Int) - (count100 center n : Int)) =
      bit center n - 1 := by
  have h := singleton_imbalance_add_chiral_diff_eq_transition_balance center n
  have hbal := transition_balance_10_01 n
  omega

/-- **Headline Theorem 18 (`derivativeDiscrepancy_eq_palindrome_three_block_diff` — Palindrome Decomposition of `D_∂`):**
All four chiral 3-blocks (`001`, `011`, `100`, `110`) cancel in pairs out of the second-order
derivative discrepancy `derivativeDiscrepancy f n`, leaving the pure palindrome difference
`(count010 f n + count101 f n) - (count000 f n + count111 f n)` plus the two bounded
De Bruijn boundary terms `(count011 f n - count110 f n) - (count001 f n - count100 f n) ∈ {-1, 0, 1}`. -/
theorem derivativeDiscrepancy_eq_palindrome_three_block_diff (f : Nat → Bool) (n : Nat) :
    derivativeDiscrepancy f n =
      ((count010 f n : Int) + (count101 f n : Int)) -
        ((count000 f n : Int) + (count111 f n : Int)) +
        ((count011 f n : Int) - (count110 f n : Int)) -
        ((count001 f n : Int) - (count100 f n : Int)) := by
  unfold derivativeDiscrepancy
  have h00 := count00_step_decomposition f n
  have h11 := count11_step_decomposition f n
  have h01 := count01_step_decomposition f n
  have h10 := count10_step_decomposition f n
  omega

/-- **Headline Theorem 19a (`rotated_palindrome_white_identity`):**
Adding the first-order discrepancy `2 * onesCount f n - n` and the second-order derivative discrepancy
`derivativeDiscrepancy f n` decouples the white-centered palindrome imbalance `2 * (count101 - count000)`
up to the single bounded `(0,0)` boundary term `2 * (count001 - count100) ∈ {-2, 0, 2}`. -/
theorem rotated_palindrome_white_identity (f : Nat → Bool) (n : Nat) :
    (2 * (onesCount f n : Int) - (n : Int)) + derivativeDiscrepancy f n =
      2 * ((count101 f n : Int) - (count000 f n : Int)) -
        2 * ((count001 f n : Int) - (count100 f n : Int)) := by
  unfold derivativeDiscrepancy
  have h_sum : (count00 f n : Int) + (count01 f n : Int) +
      (count10 f n : Int) + (count11 f n : Int) = (n : Int) := by
    exact_mod_cast block_counts_sum f n
  have h_ones : (onesCount f n : Int) = (count10 f n : Int) + (count11 f n : Int) := by
    exact_mod_cast onesCount_step_decomposition f n
  have h00 := count00_step_decomposition f n
  have h10 := count10_step_decomposition f n
  omega

/-- **Headline Theorem 19b (`rotated_palindrome_black_identity`):**
Subtracting `2 * onesCount f n - n` from `derivativeDiscrepancy f n` decouples the black-centered
palindrome imbalance `2 * (count010 - count111)` up to the single bounded `(1,1)` boundary term
`2 * (count011 - count110) ∈ {-2, 0, 2}`. -/
theorem rotated_palindrome_black_identity (f : Nat → Bool) (n : Nat) :
    derivativeDiscrepancy f n - (2 * (onesCount f n : Int) - (n : Int)) =
      2 * ((count010 f n : Int) - (count111 f n : Int)) +
        2 * ((count011 f n : Int) - (count110 f n : Int)) := by
  unfold derivativeDiscrepancy
  have h_sum : (count00 f n : Int) + (count01 f n : Int) +
      (count10 f n : Int) + (count11 f n : Int) = (n : Int) := by
    exact_mod_cast block_counts_sum f n
  have h_ones : (onesCount f n : Int) = (count10 f n : Int) + (count11 f n : Int) := by
    exact_mod_cast onesCount_step_decomposition f n
  have h01 := count01_step_decomposition f n
  have h11 := count11_step_decomposition f n
  omega

/-- **Headline Theorem 20a (`four_mul_count100_eq_palindrome_reconstruction` — 4-to-8 Palindrome Reconstruction Law for Chiral `(1,0,0)`):**
For any boolean sequence `f`, `4 * count100 f n` is uniquely reconstructed up to `O(1)` boundary terms
(`≤ 4` in absolute value) purely from the horizon `n` and the four palindrome 3-blocks
`(count000, count010, count101, count111)`:
`4 * count100 = n - count000 + count010 - 3 * count101 - count111 - (count001 - count100) + (count011 - count110) - 2 * (count01 - count10)`. -/
theorem four_mul_count100_eq_palindrome_reconstruction (f : Nat → Bool) (n : Nat) :
    4 * (count100 f n : Int) =
      (n : Int) - (count000 f n : Int) + (count010 f n : Int) -
        3 * (count101 f n : Int) - (count111 f n : Int) -
        ((count001 f n : Int) - (count100 f n : Int)) +
        ((count011 f n : Int) - (count110 f n : Int)) -
        2 * ((count01 f n : Int) - (count10 f n : Int)) := by
  have h3 := three_block_counts_sum f n
  have h01 := count01_step_decomposition f n
  have h10 := count10_step_decomposition f n
  omega

/-- **Headline Theorem 20b (`four_mul_count011_eq_palindrome_reconstruction` — 4-to-8 Palindrome Reconstruction Law for Chiral `(0,1,1)`):**
For any boolean sequence `f`, `4 * count011 f n` is uniquely reconstructed up to `O(1)` boundary terms
purely from `n` and the four palindrome 3-blocks `(count000, count010, count101, count111)`. -/
theorem four_mul_count011_eq_palindrome_reconstruction (f : Nat → Bool) (n : Nat) :
    4 * (count011 f n : Int) =
      (n : Int) - (count000 f n : Int) - 3 * (count010 f n : Int) +
        (count101 f n : Int) - (count111 f n : Int) -
        ((count001 f n : Int) - (count100 f n : Int)) +
        ((count011 f n : Int) - (count110 f n : Int)) +
        2 * ((count01 f n : Int) - (count10 f n : Int)) := by
  have h3 := three_block_counts_sum f n
  have h01 := count01_step_decomposition f n
  have h10 := count10_step_decomposition f n
  omega

/-- 3-body Walsh-Hadamard spectral mode `W_111(f, n) = sum_{t < n} s_t s_{t+1} s_{t+2}`,
where `s_t = 2 * bit f t - 1 ∈ {-1, +1}`: counts odd-black-parity 3-blocks (`001, 010, 100, 111`)
minus even-black-parity 3-blocks (`000, 011, 101, 110`). -/
def walshParity3 (f : Nat → Bool) (n : Nat) : Int :=
  ((count001 f n : Int) + (count010 f n : Int) + (count100 f n : Int) + (count111 f n : Int)) -
    ((count000 f n : Int) + (count011 f n : Int) + (count101 f n : Int) + (count110 f n : Int))

/-- **Headline Theorem 21 (`walshParity3_eq_discrepancy_add_four_singleton_imbalance`):**
In the 4D Walsh-Hadamard spectral basis `(D, D_∂, D_lag2, W_111)`, the 3-body mode `walshParity3 f n`
equals the 1-body discrepancy `2 * onesCount f n - n` plus `4 * (count010 f n - count101 f n)` plus
`O(1)` boundary terms `2 * ((count10 - count01) + (count001 - count100) + (count011 - count110))`.
Because `D` and `W_111` are orthogonal martingales of equal variance `t`, this forces the exact
asymptotic variance ratio `Var(count111 - count000) : Var(count010 - count101) = 5 : 1` and
correlation `-1 / sqrt(5)`. -/
theorem walshParity3_eq_discrepancy_add_four_singleton_imbalance (f : Nat → Bool) (n : Nat) :
    walshParity3 f n =
      (2 * (onesCount f n : Int) - (n : Int)) +
        4 * ((count010 f n : Int) - (count101 f n : Int)) +
        2 * ((count10 f n : Int) - (count01 f n : Int)) +
        2 * ((count001 f n : Int) - (count100 f n : Int)) +
        2 * ((count011 f n : Int) - (count110 f n : Int)) := by
  unfold walshParity3
  have h_sum : (count00 f n : Int) + (count01 f n : Int) +
      (count10 f n : Int) + (count11 f n : Int) = (n : Int) := by
    exact_mod_cast block_counts_sum f n
  have h_ones : (onesCount f n : Int) = (count10 f n : Int) + (count11 f n : Int) := by
    exact_mod_cast onesCount_step_decomposition f n
  have h00 := count00_step_decomposition f n
  have h01 := count01_step_decomposition f n
  have h10 := count10_step_decomposition f n
  have h11 := count11_step_decomposition f n
  omega

end Rule30TwoBlockCounts
end Ruliology.CellularAutomata
