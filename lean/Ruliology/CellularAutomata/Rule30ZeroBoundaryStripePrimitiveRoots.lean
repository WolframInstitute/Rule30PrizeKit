module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeStructure

/-!
# Backward Operators, the Period-3 NOR Wave Trichotomy, and Projective Orbit Laws for Stripe Primitive Roots

`Rule30ZeroBoundaryStripeStructure` shows that the two-step forward clone map `F_shift` carries any
closed front-window cycle along the ray `W → F_shift W → F_shift² W → …` of tail lengths `k + 4j`.
This module characterizes the windows off a clone ray—the algebraic primitive roots (`IsPrimRoot`),
including the computed horizon-31 exceptional roots noted in `Rule30ZeroBoundaryStripeStructure`
(`13` at four bits, `97` at seven bits, and twelve off-ray roots at eight bits)—by constructing the
explicit one-step and two-step backward operators on `Fin (2^K)` and proving their bitwise
recurrence laws:

1. **Constructive One-Step and Two-Step Backward Operators (`bstep1`, `bstep0`, `B_shift`)**:
   - `bstep1 K W` and `bstep0 K U` invert `fstep K · 1` and `fstep K · 0` on `Fin (2^K)`
     (`fstep_bstep1`, `bstep1_fstep`, `fstep_bstep0`, `bstep0_fstep`), with bit `i` given by
     `W.testBit (i - 1) ^^ (bstep1 K W).testBit (i - 1) || (bstep1 K W).testBit (i - 2)` and
     `U.testBit (i - 1) ^^ !((bstep0 K U).testBit (i - 1) || (bstep0 K U).testBit (i - 2))`
     (`bstep1_testBit_ge`, `bstep0_testBit_ge`).
   - `B_shift K W = bstep0 K (bstep1 K W)` is the two-sided inverse of two front steps `orb K 2 · 0`
     (`orb_two_B_shift`, `B_shift_orb_two`), equals `(orb_inv K 2 (W, 0)).1` (`B_shift_eq_orb_inv_two`),
     and satisfies `B_shift K (F_shift V) = V` for every `k`-bit window `V < 2^k` with leading bit `1`
     when `k + 4 ≤ K` (`B_shift_F_shift`).
2. **Two-Step Backward Trichotomy and the Period-3 NOR Wave (`backward_nor_recurrence`,
   `backward_nor_period_three`, `primitive_or_clone_trichotomy`, `exists_F_shift_eq_iff`)**:
   - Whenever `(bstep1 K W).testBit (i - 1) = true` (`2 ≤ i < K`), bit `i` of `V = B_shift K W`
     satisfies the backward NOR recurrence `V.testBit i = !(V.testBit (i - 1) || V.testBit (i - 2))`
     (`backward_nor_recurrence`), which forces the upper bits of `V` into a period-3 `(100)^∞` wave
     `V.testBit (i + 3) = V.testBit i` (`backward_nor_period_three`).
   - Every window `W < 2^k` (`4 ≤ k ≤ K`) with `U = bstep1 K W` and `V = B_shift K W` falls into one
     of three regimes (`primitive_or_clone_trichotomy`, `isPrimRoot_iff_avalanche`, with exhaustive
     eight-bit classification in `eight_bit_odd_trichotomy_exhaustive` and regime checks on the
     computed horizon-31 exceptional eight-bit list in `eight_cell_primitive_root_classification`):
     * **Clone (`0^∞` tail):** `U < 2^(k - 2) ∧ V < 2^(k - 4)`, which holds for an odd `k`-bit window
       iff `W = F_shift V₀` for some `(k - 4)`-bit window `V₀ < 2^(k - 4)` with leading bit `1`
       (`exists_F_shift_eq_iff`; at eight bits the four odd clones are `195, 205, 209, 223`, with
       `223 = F_shift 13` on the computed horizon-31 exceptional ray of `13`).
     * **Type I primitive root (`1^∞` tail):** `U < 2^(k - 2)` and `V.testBit i = true` for all
       `k - 2 ≤ i < K` (at eight bits the twelve odd Type I roots are `197, 199, 201, 203, 211, 213, 215, 217, 225, 239, 251, 253`, of which
       `201, 225, 253` belong to the computed horizon-31 exceptional list).
     * **Type II primitive root (`(100)^∞` NOR wave):** `U.testBit i = true` for all `k ≤ i < K` and
       `V.testBit (i + 3) = V.testBit i` for all `k ≤ i` with `i + 3 < K` (the remaining forty-eight
       odd eight-bit windows; among the computed horizon-31 exceptional windows: `13` at four bits,
       `97` at seven bits, and `131, 143, 159, 165, 169, 181, 189, 245, 255` at eight bits).
3. **The `win3pow n = 3 · 2^n + 1` Shift-Template Law (`bstep1_win3pow_shift_13`,
   `B_shift_win3pow_shift_13`, `B_shift_win3pow_low_ones`)**:
   For `win3pow n = 1 ||| (3 <<< n)` (`win3pow 2 = 13`, `win3pow 5 = 97`), every `n ≥ 2` and width `K`
   satisfies `(bstep1 K (win3pow n)).testBit (n - 2 + d) = (bstep1 K 13).testBit d` and
   `(B_shift K (win3pow n)).testBit (n - 2 + d) = (B_shift K 13).testBit d`, with the low `n` bits of
   `B_shift K (win3pow n)` all `true`. Because the upper NOR wave of `B_shift K 13` has period 3,
   shifting by `n - 2 = 3` (`n = 5`, `win3pow 5 = 97`) is the minimal shift that preserves the upper
   boundary phase of `13` (`bstep1_97_eq_shift_13`, `B_shift_97_eq_shift_13`).
4. **Projective Orbit Reduction Modulo `2^K` (`fstep_mod_pow`, `orb_mod_pow`,
   `orb_even_eq_F_shiftIter_mod`, `orb_7_4_13_eq_97`, `orb_8_4_13_eq_225`, `cycle165_iff_cycle245`)**:
   For `K ≤ K'`, `(orb K' t (W, p)).1 % 2^K = (orb K t (W % 2^K, p)).1`, and for `k + 4 * j ≤ K'`,
   `(orb K (2 * j) (W % 2^K, 0)).1 = F_shiftIter j W % 2^K`. At `W = 13, j = 2`, `F_shiftIter 2 13 = 3553`
   projects modulo `2^7` to `97` (`orb 7 4 (13, 0) = (97, 0)`) and modulo `2^8` to `225`
   (`orb 8 4 (13, 0) = (225, 0)`). At width `32`, `orb 32 4760 (165, 0) = (245, 0)`, so
   `Cycle 32 S 165 0 (2^32) ↔ Cycle 32 S 245 0 (2^32)`.
5. **Ray-97 Transfer and the Survivor-Avalanche Criterion for Primitive Exceptions
   (`rowTail_ray97_of_cycle97`, `prim_exception_iff_survivor_avalanche`)**:
   `rowTail_ray97_of_cycle97` lifts any certificate `Cycle K S 97 0 L` (`7 ≤ K`, `S + 1 ≤ K`) to
   every `(7 + 4j)`-bit clone `F_shiftIter j 97` (`97, 1659, 25757, …`) and every odd prefix `m`.
   `prim_exception_iff_survivor_avalanche` proves that `(w, 0)` (`w < 2^k`) is a primitive root that
   fails to close at width `K + 1` and horizon `S` iff `w = (orb_inv K r (x, 1)).1` for some odd step
   `r < 2^(K + 1)` and horizon-`S` survivor `x` whose two-step preimage triggers a Type I (`1^∞`) or
   Type II (`(100)^∞`) avalanche.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30ZeroBoundaryStripePrimitiveRoots

open Rule30ZeroBoundary
open Rule30ZeroBoundarySmall
open Rule30ZeroBoundaryStripe
open Rule30ZeroBoundaryStripeFront
open Rule30ZeroBoundaryStripeFrontLift
open Rule30ZeroBoundaryStripeStructure

/-! ## 1. Constructive 1-Step and 2-Step Backward Operators (`bstep1`, `bstep0`, `B_shift`) -/

/-- Constructive 1-step backward preimage of `W` under `fstep K · 1`, computed bit-by-bit from
bit `0` to bit `K - 1`. -/
def bstep1 : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, W =>
    let U := bstep1 n W
    let pred :=
      if n = 0 then true
      else if n = 1 then U.testBit 0
      else (U.testBit (n - 1) || U.testBit (n - 2))
    U ||| ((if xor (W.testBit n) pred then 1 else 0) <<< n)

/-- Constructive 1-step backward preimage of `U` under `fstep K · 0`, computed bit-by-bit from
bit `0` to bit `K - 1`. -/
def bstep0 : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, U =>
    let V := bstep0 n U
    let pred :=
      if n = 0 then true
      else if n = 1 then true
      else (V.testBit (n - 1) || V.testBit (n - 2))
    V ||| ((if xor (U.testBit n) pred then 1 else 0) <<< n)

/-- The constructive 2-step backward front-window operator `B_shift K W = bstep0 K (bstep1 K W)`:
the exact 2-step inverse of `(fS K)^2` on even phase `(W, 0)` and the left-inverse of `F_shift`. -/
def B_shift (K W : Nat) : Nat :=
  bstep0 K (bstep1 K W)

private theorem testBit_bit_shiftLeft (b : Bool) (n i : Nat) :
    ((if b then 1 else 0) <<< n).testBit i = (if i = n then b else false) := by
  cases b
  · simp
  · simp only [↓reduceIte, Nat.testBit_shiftLeft]
    by_cases h : i = n
    · subst h; simp
    · by_cases hge : n ≤ i
      · rw [decide_eq_true hge, Bool.true_and, ite_eq_right h, testBit_one_ge_one (by omega)]
      · rw [decide_eq_false hge, Bool.false_and, ite_eq_right h]

/-- All bits of `bstep1 n W` at index `i ≥ n` are `false`. -/
theorem bstep1_testBit_ge {n W i : Nat} (hi : n ≤ i) :
    (bstep1 n W).testBit i = false := by
  induction n with
  | zero => exact Nat.zero_testBit i
  | succ n ih =>
    rw [bstep1, Nat.testBit_or, testBit_bit_shiftLeft, ih (by omega), ite_eq_right (by omega)]
    rfl

/-- All bits of `bstep0 n U` at index `i ≥ n` are `false`. -/
theorem bstep0_testBit_ge {n U i : Nat} (hi : n ≤ i) :
    (bstep0 n U).testBit i = false := by
  induction n with
  | zero => exact Nat.zero_testBit i
  | succ n ih =>
    rw [bstep0, Nat.testBit_or, testBit_bit_shiftLeft, ih (by omega), ite_eq_right (by omega)]
    rfl

/-- `bstep1 K W` is bounded by `2^K`. -/
theorem bstep1_lt (K W : Nat) : bstep1 K W < 2 ^ K :=
  Nat.lt_pow_two_of_testBit (bstep1 K W) (fun _ hi => bstep1_testBit_ge hi)

/-- `bstep0 K U` is bounded by `2^K`. -/
theorem bstep0_lt (K U : Nat) : bstep0 K U < 2 ^ K :=
  Nat.lt_pow_two_of_testBit (bstep0 K U) (fun _ hi => bstep0_testBit_ge hi)

/-- `B_shift K W` is bounded by `2^K`. -/
theorem B_shift_lt (K W : Nat) : B_shift K W < 2 ^ K :=
  bstep0_lt K (bstep1 K W)

/-- Width-stability of `bstep1`: for `n ≤ K`, `bstep1 K W` and `bstep1 n W` agree on all bits `< n`. -/
theorem bstep1_low {n K W : Nat} (hn : n ≤ K) :
    LowEq n (bstep1 K W) (bstep1 n W) := by
  induction K with
  | zero =>
    intro i hi
    omega
  | succ K ih =>
    rcases Nat.eq_or_lt_of_le hn with rfl | hlt
    · intro _ _; rfl
    · intro i hi
      have hstep : (bstep1 (K + 1) W).testBit i = (bstep1 K W).testBit i := by
        rw [bstep1, Nat.testBit_or, testBit_bit_shiftLeft, ite_eq_right (by omega), Bool.or_false]
      rw [hstep, ih (by omega) i hi]

/-- Width-stability of `bstep0`: for `n ≤ K`, `bstep0 K U` and `bstep0 n U` agree on all bits `< n`. -/
theorem bstep0_low {n K U : Nat} (hn : n ≤ K) :
    LowEq n (bstep0 K U) (bstep0 n U) := by
  induction K with
  | zero =>
    intro i hi
    omega
  | succ K ih =>
    rcases Nat.eq_or_lt_of_le hn with rfl | hlt
    · intro _ _; rfl
    · intro i hi
      have hstep : (bstep0 (K + 1) U).testBit i = (bstep0 K U).testBit i := by
        rw [bstep0, Nat.testBit_or, testBit_bit_shiftLeft, ite_eq_right (by omega), Bool.or_false]
      rw [hstep, ih (by omega) i hi]

/-- Bitwise recurrence for bit `i < K` of `bstep1 K W`. -/
theorem bstep1_testBit_lt {K W i : Nat} (hi : i < K) :
    (bstep1 K W).testBit i =
      xor (W.testBit i)
        (if i = 0 then true
         else if i = 1 then (bstep1 K W).testBit 0
         else ((bstep1 K W).testBit (i - 1) || (bstep1 K W).testBit (i - 2))) := by
  have h1 : (bstep1 K W).testBit i = (bstep1 (i + 1) W).testBit i :=
    bstep1_low (by omega) i (by omega)
  have htop : (bstep1 (i + 1) W).testBit i =
      xor (W.testBit i)
        (if i = 0 then true
         else if i = 1 then (bstep1 i W).testBit 0
         else ((bstep1 i W).testBit (i - 1) || (bstep1 i W).testBit (i - 2))) := by
    rw [bstep1, Nat.testBit_or, testBit_bit_shiftLeft, ite_eq_left rfl,
      bstep1_testBit_ge (Nat.le_refl i), Bool.false_or]
  rw [h1, htop]
  rcases (show i = 0 ∨ i = 1 ∨ 2 ≤ i by omega) with rfl | rfl | hi2
  · rfl
  · simp [bstep1_low (by omega : 1 ≤ K) 0 (by decide)]
  · have h_1 : (bstep1 i W).testBit (i - 1) = (bstep1 K W).testBit (i - 1) :=
      (bstep1_low (by omega : i ≤ K) (i - 1) (by omega)).symm
    have h_2 : (bstep1 i W).testBit (i - 2) = (bstep1 K W).testBit (i - 2) :=
      (bstep1_low (by omega : i ≤ K) (i - 2) (by omega)).symm
    simp [show i ≠ 0 by omega, show i ≠ 1 by omega, h_1, h_2]

/-- Bitwise recurrence for bit `i < K` of `bstep0 K U`. -/
theorem bstep0_testBit_lt {K U i : Nat} (hi : i < K) :
    (bstep0 K U).testBit i =
      xor (U.testBit i)
        (if i = 0 then true
         else if i = 1 then true
         else ((bstep0 K U).testBit (i - 1) || (bstep0 K U).testBit (i - 2))) := by
  have h1 : (bstep0 K U).testBit i = (bstep0 (i + 1) U).testBit i :=
    bstep0_low (by omega) i (by omega)
  have htop : (bstep0 (i + 1) U).testBit i =
      xor (U.testBit i)
        (if i = 0 then true
         else if i = 1 then true
         else ((bstep0 i U).testBit (i - 1) || (bstep0 i U).testBit (i - 2))) := by
    rw [bstep0, Nat.testBit_or, testBit_bit_shiftLeft, ite_eq_left rfl,
      bstep0_testBit_ge (Nat.le_refl i), Bool.false_or]
  rw [h1, htop]
  rcases (show i = 0 ∨ i = 1 ∨ 2 ≤ i by omega) with rfl | rfl | hi2
  · rfl
  · rfl
  · have h_1 : (bstep0 i U).testBit (i - 1) = (bstep0 K U).testBit (i - 1) :=
      (bstep0_low (by omega : i ≤ K) (i - 1) (by omega)).symm
    have h_2 : (bstep0 i U).testBit (i - 2) = (bstep0 K U).testBit (i - 2) :=
      (bstep0_low (by omega : i ≤ K) (i - 2) (by omega)).symm
    simp [show i ≠ 0 by omega, show i ≠ 1 by omega, h_1, h_2]

private theorem testBit_fstep_one_lt {K U i : Nat} (hi : i < K) :
    (fstep K U 1).testBit i =
      xor (U.testBit i)
        (if i = 0 then true
         else if i = 1 then U.testBit 0
         else (U.testBit (i - 1) || U.testBit (i - 2))) := by
  rw [testBit_fstep K U 1 i (by decide), decide_eq_true hi, Bool.true_and]
  rcases (show i = 0 ∨ i = 1 ∨ 2 ≤ i by omega) with rfl | rfl | hi2
  · rfl
  · simp
  · simp [show i ≠ 0 by omega, show i ≠ 1 by omega]

private theorem testBit_fstep_zero_lt {K V i : Nat} (hi : i < K) :
    (fstep K V 0).testBit i =
      xor (V.testBit i)
        (if i = 0 then true
         else if i = 1 then true
         else (V.testBit (i - 1) || V.testBit (i - 2))) := by
  rw [testBit_fstep K V 0 i (by decide), decide_eq_true hi, Bool.true_and]
  rcases (show i = 0 ∨ i = 1 ∨ 2 ≤ i by omega) with rfl | rfl | hi2
  · rfl
  · simp
  · simp [show i ≠ 0 by omega, show i ≠ 1 by omega]

/-- `bstep1 K` is the right-inverse of `fstep K · 1` on `Fin (2^K)`. -/
theorem fstep_bstep1 (K W : Nat) (hW : W < 2 ^ K) :
    fstep K (bstep1 K W) 1 = W := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < K
  · rw [testBit_fstep_one_lt hi, bstep1_testBit_lt hi]
    cases W.testBit i <;>
      cases (if i = 0 then true else if i = 1 then (bstep1 K W).testBit 0
        else ((bstep1 K W).testBit (i - 1) || (bstep1 K W).testBit (i - 2))) <;> rfl
  · rw [Rule30ZeroBoundarySmall.testBit_ge_of_lt (fstep_bound K (bstep1 K W) 1) (by omega),
      Rule30ZeroBoundarySmall.testBit_ge_of_lt hW (by omega)]

/-- `bstep1 K` is the left-inverse of `fstep K · 1` on `Fin (2^K)`. -/
theorem bstep1_fstep (K U : Nat) (hU : U < 2 ^ K) :
    bstep1 K (fstep K U 1) = U := by
  apply Nat.eq_of_testBit_eq
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    by_cases hi : i < K
    · rw [bstep1_testBit_lt hi, testBit_fstep_one_lt hi]
      rcases (show i = 0 ∨ i = 1 ∨ 2 ≤ i by omega) with rfl | rfl | hi2
      · simp
      · have h0 := ih 0 (by decide)
        simp only [show (1 : Nat) ≠ 0 by decide, ↓reduceIte, h0]
        cases U.testBit 1 <;> cases U.testBit 0 <;> rfl
      · have h1 := ih (i - 1) (by omega)
        have h2 := ih (i - 2) (by omega)
        simp only [show i ≠ 0 by omega, show i ≠ 1 by omega, ↓reduceIte, h1, h2]
        cases U.testBit i <;> cases (U.testBit (i - 1) || U.testBit (i - 2)) <;> rfl
    · rw [bstep1_testBit_ge (by omega),
        Rule30ZeroBoundarySmall.testBit_ge_of_lt hU (by omega)]

/-- `bstep0 K` is the right-inverse of `fstep K · 0` on `Fin (2^K)`. -/
theorem fstep_bstep0 (K U : Nat) (hU : U < 2 ^ K) :
    fstep K (bstep0 K U) 0 = U := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < K
  · rw [testBit_fstep_zero_lt hi, bstep0_testBit_lt hi]
    cases U.testBit i <;>
      cases (if i = 0 then true else if i = 1 then true
        else ((bstep0 K U).testBit (i - 1) || (bstep0 K U).testBit (i - 2))) <;> rfl
  · rw [Rule30ZeroBoundarySmall.testBit_ge_of_lt (fstep_bound K (bstep0 K U) 0) (by omega),
      Rule30ZeroBoundarySmall.testBit_ge_of_lt hU (by omega)]

/-- `bstep0 K` is the left-inverse of `fstep K · 0` on `Fin (2^K)`. -/
theorem bstep0_fstep (K V : Nat) (hV : V < 2 ^ K) :
    bstep0 K (fstep K V 0) = V := by
  apply Nat.eq_of_testBit_eq
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    by_cases hi : i < K
    · rw [bstep0_testBit_lt hi, testBit_fstep_zero_lt hi]
      rcases (show i = 0 ∨ i = 1 ∨ 2 ≤ i by omega) with rfl | rfl | hi2
      · simp
      · simp
      · have h1 := ih (i - 1) (by omega)
        have h2 := ih (i - 2) (by omega)
        simp only [show i ≠ 0 by omega, show i ≠ 1 by omega, ↓reduceIte, h1, h2]
        cases V.testBit i <;> cases (V.testBit (i - 1) || V.testBit (i - 2)) <;> rfl
    · rw [bstep0_testBit_ge (by omega),
        Rule30ZeroBoundarySmall.testBit_ge_of_lt hV (by omega)]

/-- Two forward steps of `orb K` from `(B_shift K W, 0)` recover `(W, 0)`. -/
theorem orb_two_B_shift (K W : Nat) (hW : W < 2 ^ K) :
    orb K 2 (B_shift K W, 0) = (W, 0) := by
  unfold B_shift
  show (fstep K (fstep K (bstep0 K (bstep1 K W)) 0) 1, 0) = (W, 0)
  rw [fstep_bstep0 K (bstep1 K W) (bstep1_lt K W), fstep_bstep1 K W hW]

/-- `B_shift K` is the left-inverse of 2-step forward evolution `(orb K 2 (V, 0)).1`. -/
theorem B_shift_orb_two (K V : Nat) (hV : V < 2 ^ K) :
    B_shift K (orb K 2 (V, 0)).1 = V := by
  unfold B_shift
  show bstep0 K (bstep1 K (fstep K (fstep K V 0) 1)) = V
  rw [bstep1_fstep K (fstep K V 0) (fstep_bound K V 0), bstep0_fstep K V hV]

/-- **Exact Left-Inverse of `F_shift`:** For any `k`-bit window `V < 2^k` (`k ≥ 1`) and any width
`K ≥ k + 4`, `B_shift K (F_shift V) = V`. -/
theorem B_shift_F_shift {k K V : Nat} (hk : 1 ≤ k) (hV : V < 2 ^ k) (hK : k + 4 ≤ K) :
    B_shift K (F_shift V) = V := by
  have hV_K : V < 2 ^ K :=
    Nat.lt_of_lt_of_le hV (Nat.pow_le_pow_right (by decide) (by omega))
  have horb := orb_two_eq_F_shift hk hV hK
  have h1 : F_shift V = (orb K 2 (V, 0)).1 := by rw [horb]
  rw [h1, B_shift_orb_two K V hV_K]

/-- `B_shift (K + 1) W` coincides with the universal-period 2-step inverse `(orb_inv K 2 (W, 0)).1`. -/
theorem B_shift_eq_orb_inv_two (K W : Nat) (hW : W < 2 ^ (K + 1)) :
    B_shift (K + 1) W = (orb_inv K 2 (W, 0)).1 := by
  have hcan := orb_inv_cancel_right K 2 W 0 hW (by decide)
  have hphase : (orb_inv K 2 (W, 0)).2 = 0 := by
    unfold orb_inv
    have heven : (2 ^ (K + 1) - 2 % 2 ^ (K + 1)) % 2 = 0 := by
      rcases K with _ | K
      · decide
      · have hpos : 0 < 2 ^ K := Nat.two_pow_pos K
        have hlt2 : 2 < 2 ^ (K + 1 + 1) := by
          rw [Nat.pow_succ, Nat.pow_succ]
          omega
        rw [Nat.mod_eq_of_lt hlt2, Nat.pow_succ, Nat.pow_succ]
        omega
    exact orb_even_phase (K + 1) W 0 _ (by decide) heven
  have hpair : orb_inv K 2 (W, 0) = ((orb_inv K 2 (W, 0)).1, 0) :=
    Prod.ext rfl hphase
  have hbound : (orb_inv K 2 (W, 0)).1 < 2 ^ (K + 1) := by
    unfold orb_inv
    exact orbit_bound hW _
  have hW_eq : W = (orb (K + 1) 2 ((orb_inv K 2 (W, 0)).1, 0)).1 := by
    rw [← hpair, hcan]
  have hcongr := congrArg (B_shift (K + 1)) hW_eq
  rwa [B_shift_orb_two (K + 1) (orb_inv K 2 (W, 0)).1 hbound] at hcongr

/-! ## 2. The 2-Step Backward Trichotomy & Universal Period-3 NOR Wave -/

/-- **The Backward NOR Recurrence for Type II Primitive Roots.**
Whenever the 1-step preimage `U = bstep1 K W` triggers the `1^∞` avalanche (`U.testBit i = true`
for `m ≤ i < K`), every bit `i` (`max 2 m ≤ i < K`) of the 2-step preimage `V = B_shift K W`
obeys the backward NOR recurrence `V.testBit i = !(V.testBit (i - 1) || V.testBit (i - 2))`. -/
theorem backward_nor_recurrence {K W i : Nat} (hi2 : 2 ≤ i) (hiK : i < K)
    (hU : (bstep1 K W).testBit i = true) :
    (B_shift K W).testBit i = !((B_shift K W).testBit (i - 1) || (B_shift K W).testBit (i - 2)) := by
  unfold B_shift
  rw [bstep0_testBit_lt hiK, hU, ite_eq_right (by omega), ite_eq_right (by omega)]
  cases ((bstep0 K (bstep1 K W)).testBit (i - 1) || (bstep0 K (bstep1 K W)).testBit (i - 2)) <;> rfl

/-- **Universal Period-3 `(100)^∞` Wave of Type II Primitive Roots.**
Whenever `bstep1 K W` is `true` at bits `i, i + 1, i + 2, i + 3` (`2 ≤ i`, `i + 3 < K`),
the 2-step preimage `V = B_shift K W` satisfies `V.testBit (i + 3) = V.testBit i` and
`(V.testBit i || V.testBit (i + 1) || V.testBit (i + 2)) = true`. -/
theorem backward_nor_period_three {K W i : Nat} (hi2 : 2 ≤ i) (hiK : i + 3 < K)
    (hU0 : (bstep1 K W).testBit i = true)
    (hU1 : (bstep1 K W).testBit (i + 1) = true)
    (hU2 : (bstep1 K W).testBit (i + 2) = true)
    (hU3 : (bstep1 K W).testBit (i + 3) = true) :
    (B_shift K W).testBit (i + 3) = (B_shift K W).testBit i ∧
      ((B_shift K W).testBit i || (B_shift K W).testBit (i + 1) || (B_shift K W).testBit (i + 2)) = true := by
  have h0 := backward_nor_recurrence hi2 (by omega) hU0
  have h1 := backward_nor_recurrence (by omega : 2 ≤ i + 1) (by omega) hU1
  have h2 := backward_nor_recurrence (by omega : 2 ≤ i + 2) (by omega) hU2
  have h3 := backward_nor_recurrence (by omega : 2 ≤ i + 3) hiK hU3
  rw [show i + 1 - 1 = i by omega, show i + 1 - 2 = i - 1 by omega] at h1
  rw [show i + 2 - 1 = i + 1 by omega, show i + 2 - 2 = i by omega] at h2
  rw [show i + 3 - 1 = i + 2 by omega, show i + 3 - 2 = i + 1 by omega] at h3
  rw [h3, h2, h1, h0]
  cases (B_shift K W).testBit (i - 1) <;> cases (B_shift K W).testBit (i - 2) <;> decide

/-- **Complete 2-Step Backward Trichotomy (Clone vs. Type I Primitive vs. Type II Primitive).**
For any `k`-bit window `W < 2^k` (`4 ≤ k ≤ K`), its 1-step preimage `U = bstep1 K W` and 2-step
preimage `V = B_shift K W` fall into one of three regimes:
1. **Clone (`0^∞`):** `U < 2^(k - 2) ∧ V < 2^(k - 4)`.
2. **Type I Primitive Root (`1^∞`):** `U < 2^(k - 2) ∧ ∀ i, k - 2 ≤ i → i < K → V.testBit i = true`.
3. **Type II Primitive Root (`(100)^∞` NOR wave):**
   `(∀ i, k ≤ i → i < K → U.testBit i = true) ∧ (∀ i, k ≤ i → i < K → V.testBit i = !(V.testBit (i - 1) || V.testBit (i - 2)))`. -/
theorem primitive_or_clone_trichotomy {k K W : Nat} (hk : 4 ≤ k) (hK : k ≤ K) (hW : W < 2 ^ k) :
    (bstep1 K W < 2 ^ (k - 2) ∧ B_shift K W < 2 ^ (k - 4)) ∨
    (bstep1 K W < 2 ^ (k - 2) ∧ ∀ i, k - 2 ≤ i → i < K → (B_shift K W).testBit i = true) ∨
    ((∀ i, k ≤ i → i < K → (bstep1 K W).testBit i = true) ∧
      (∀ i, k ≤ i → i < K →
        (B_shift K W).testBit i = !((B_shift K W).testBit (i - 1) || (B_shift K W).testBit (i - 2)))) := by
  have hW_K : W < 2 ^ K :=
    Nat.lt_of_lt_of_le hW (Nat.pow_le_pow_right (by decide) hK)
  have hf1 : fstep K (bstep1 K W) 1 < 2 ^ k := by
    rw [fstep_bstep1 K W hW_K]
    exact hW
  rcases backward_zero_tail_dichotomy (by omega : 2 ≤ k) (bstep1_lt K W) (by decide) hf1 with hU_lt | hU_ones
  · have hf0 : fstep K (B_shift K W) 0 < 2 ^ (k - 2) := by
      unfold B_shift
      rw [fstep_bstep0 K (bstep1 K W) (bstep1_lt K W)]
      exact hU_lt
    rcases backward_zero_tail_dichotomy (by omega : 2 ≤ k - 2) (B_shift_lt K W) (by decide) hf0 with hV_lt | hV_ones
    · left
      exact ⟨by simpa using hU_lt, by rwa [show k - 2 - 2 = k - 4 by omega] at hV_lt⟩
    · right; left
      exact ⟨hU_lt, hV_ones⟩
  · right; right
    refine ⟨hU_ones, fun i hki hiK => ?_⟩
    exact backward_nor_recurrence (by omega) hiK (hU_ones i hki hiK)

/-- **Exact 4-Bit Clone Decision Rule.** A `k`-bit window `W < 2^k` (`5 ≤ k ≤ K`) is in the image of
`F_shift` on `(k - 4)`-bit windows (`∃ V < 2^(k - 4), F_shift V = W`) if and only if
`bstep1 K W < 2^(k - 2)` and `B_shift K W < 2^(k - 4)`. -/
theorem exists_F_shift_eq_iff {k K W : Nat} (hk : 5 ≤ k) (hK : k ≤ K) (hW : W < 2 ^ k) :
    (∃ V, V < 2 ^ (k - 4) ∧ F_shift V = W) ↔
      (bstep1 K W < 2 ^ (k - 2) ∧ B_shift K W < 2 ^ (k - 4)) := by
  constructor
  · rintro ⟨V, hV, rfl⟩
    have hK' : k - 4 + 4 ≤ K := by omega
    have hB : B_shift K (F_shift V) = V := B_shift_F_shift (by omega) hV hK'
    have hU : bstep1 K (F_shift V) = fstep0_unmasked V := by
      have hf1 : fstep1_unmasked (fstep0_unmasked V) < 2 ^ K := by
        change F_shift V < 2 ^ K
        exact Nat.lt_of_lt_of_le (F_shift_lt (by omega) hV) (Nat.pow_le_pow_right (by decide) hK')
      have heq : F_shift V = fstep K (fstep0_unmasked V) 1 := by
        change fstep1_unmasked (fstep0_unmasked V) = fstep K (fstep0_unmasked V) 1
        exact (fstep_one_eq_unmasked hf1).symm
      have h0_lt : fstep0_unmasked V < 2 ^ K :=
        Nat.lt_of_lt_of_le (fstep0_unmasked_lt (by omega) hV) (Nat.pow_le_pow_right (by decide) (by omega))
      rw [heq, bstep1_fstep K (fstep0_unmasked V) h0_lt]
    rw [hU, hB]
    refine ⟨?_, hV⟩
    have h0 := fstep0_unmasked_lt (by omega : 1 ≤ k - 4) hV
    rwa [show k - 4 + 2 = k - 2 by omega] at h0
  · rintro ⟨hU, hV⟩
    refine ⟨B_shift K W, hV, ?_⟩
    have hW_K : W < 2 ^ K :=
      Nat.lt_of_lt_of_le hW (Nat.pow_le_pow_right (by decide) hK)
    have hK' : k - 4 + 4 ≤ K := by omega
    have horb1 := orb_two_eq_F_shift (by omega : 1 ≤ k - 4) hV hK'
    have horb2 := orb_two_B_shift K W hW_K
    rw [horb2] at horb1
    exact (Prod.mk.inj horb1).1.symm

/-! ## 3. The `3 · 2^n + 1` Family (`win3pow`) Linking `13` (`n = 2`) and `97` (`n = 5`) -/

/-- The family of `(n + 2)`-bit odd front windows `win3pow n = 1 ||| (3 <<< n) = 3 · 2^n + 1`:
`win3pow 2 = 13` (`k = 4`) and `win3pow 5 = 97` (`k = 7`). -/
def win3pow (n : Nat) : Nat :=
  1 ||| (3 <<< n)

/-- At `n = 2`, `win3pow 2 = 13`. -/
theorem win3pow_2_eq_13 : win3pow 2 = 13 := by decide
/-- At `n = 5`, `win3pow 5 = 97`. -/
theorem win3pow_5_eq_97 : win3pow 5 = 97 := by decide

private theorem testBit_three (j : Nat) :
    (3 : Nat).testBit j = (if j = 0 ∨ j = 1 then true else false) := by
  rcases j with _ | _ | j
  · decide
  · decide
  · rw [ite_eq_right (by omega)]
    exact Rule30ZeroBoundarySmall.testBit_ge_of_lt (W := 2) (by decide) (by omega)

/-- Bit `i` of `win3pow n` (`n ≥ 1`) is `true` iff `i = 0`, `i = n`, or `i = n + 1`. -/
theorem testBit_win3pow {n i : Nat} (hn : 1 ≤ n) :
    (win3pow n).testBit i = (if i = 0 ∨ i = n ∨ i = n + 1 then true else false) := by
  unfold win3pow
  rw [Nat.testBit_or, Nat.testBit_shiftLeft]
  rcases i with _ | i
  · have hfalse : decide (n ≤ 0) = false := decide_eq_false (by omega)
    rw [hfalse]
    simp
  · rw [testBit_one_ge_one (by omega : 1 ≤ i + 1), Bool.false_or]
    by_cases hni : n ≤ i + 1
    · rw [decide_eq_true hni, Bool.true_and, testBit_three (i + 1 - n)]
      by_cases h01 : i + 1 = n ∨ i + 1 = n + 1
      · rw [ite_eq_left (by omega), ite_eq_left (by omega)]
      · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    · rw [decide_eq_false hni, Bool.false_and, ite_eq_right (by omega)]

private theorem testBit_win3pow_shift {n d : Nat} (hn : 2 ≤ n) (hd : 2 ≤ d) :
    (win3pow n).testBit (n - 2 + d) = (win3pow 2).testBit d := by
  rw [testBit_win3pow (by omega), testBit_win3pow (by decide)]
  by_cases h : d = 2 ∨ d = 3
  · rw [ite_eq_left (by omega), ite_eq_left (by omega)]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega)]

/-- For every `n ≥ 1` and `i < n` (`i < K`), `(bstep1 K (win3pow n)).testBit i = false`. -/
theorem bstep1_win3pow_lt_zero {K n i : Nat} (hn : 1 ≤ n) (hi : i < n) (hiK : i < K) :
    (bstep1 K (win3pow n)).testBit i = false := by
  induction i using Nat.strongRecOn with
  | ind i ih =>
    rw [bstep1_testBit_lt hiK, testBit_win3pow hn]
    rcases (show i = 0 ∨ i = 1 ∨ 2 ≤ i by omega) with rfl | rfl | hi2
    · simp
    · have h0 := ih 0 (by decide) (by omega) (by omega)
      rw [ite_eq_right (by omega), ite_eq_right (by decide), ite_eq_left rfl, h0]
      rfl
    · have h1 := ih (i - 1) (by omega) (by omega) (by omega)
      have h2 := ih (i - 2) (by omega) (by omega) (by omega)
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), h1, h2]
      rfl

/-- **Universal 1-Step Shift-Template Law for `win3pow n` (`∀ K n d, 2 ≤ n`).**
For every `n ≥ 2` and `d` with `n - 2 + d < K`, bit `n - 2 + d` of `bstep1 K (win3pow n)` equals
bit `d` of `bstep1 K 13`. -/
theorem bstep1_win3pow_shift_13 {K n d : Nat} (hn : 2 ≤ n) (hdK : n - 2 + d < K) :
    (bstep1 K (win3pow n)).testBit (n - 2 + d) = (bstep1 K 13).testBit d := by
  rw [← win3pow_2_eq_13]
  induction d using Nat.strongRecOn with
  | ind d ih =>
    rcases (show d = 0 ∨ d = 1 ∨ 2 ≤ d by omega) with rfl | rfl | hd2
    · rw [Nat.add_zero] at hdK ⊢
      rw [bstep1_win3pow_lt_zero (by omega) (by omega) hdK,
        bstep1_win3pow_lt_zero (by decide) (by decide) (by omega)]
    · rw [bstep1_win3pow_lt_zero (by omega) (by omega) hdK,
        bstep1_win3pow_lt_zero (by decide) (by decide) (by omega)]
    · have h1 := ih (d - 1) (by omega) (by omega)
      have h2 := ih (d - 2) (by omega) (by omega)
      rw [bstep1_testBit_lt hdK, bstep1_testBit_lt (by omega : d < K),
        testBit_win3pow_shift hn hd2,
        ite_eq_right (by omega : n - 2 + d ≠ 0), ite_eq_right (by omega : n - 2 + d ≠ 1),
        ite_eq_right (by omega : d ≠ 0), ite_eq_right (by omega : d ≠ 1),
        show n - 2 + d - 1 = n - 2 + (d - 1) by omega,
        show n - 2 + d - 2 = n - 2 + (d - 2) by omega, h1, h2]

/-- For every `n ≥ 1` and `i < n` (`i < K`), `(B_shift K (win3pow n)).testBit i = true`. -/
theorem B_shift_win3pow_low_ones {K n i : Nat} (hn : 1 ≤ n) (hi : i < n) (hiK : i < K) :
    (B_shift K (win3pow n)).testBit i = true := by
  unfold B_shift
  induction i using Nat.strongRecOn with
  | ind i ih =>
    rw [bstep0_testBit_lt hiK, bstep1_win3pow_lt_zero hn hi hiK]
    rcases (show i = 0 ∨ i = 1 ∨ 2 ≤ i by omega) with rfl | rfl | hi2
    · rfl
    · rfl
    · have h1 := ih (i - 1) (by omega) (by omega) (by omega)
      rw [ite_eq_right (by omega), ite_eq_right (by omega), h1]
      rfl

/-- **Universal 2-Step Shift-Template Law for `win3pow n` (`∀ K n d, 2 ≤ n`).**
For every `n ≥ 2` and `d` with `n - 2 + d < K`, bit `n - 2 + d` of `B_shift K (win3pow n)` equals
bit `d` of `B_shift K 13`. -/
theorem B_shift_win3pow_shift_13 {K n d : Nat} (hn : 2 ≤ n) (hdK : n - 2 + d < K) :
    (B_shift K (win3pow n)).testBit (n - 2 + d) = (B_shift K 13).testBit d := by
  rw [← win3pow_2_eq_13]
  induction d using Nat.strongRecOn with
  | ind d ih =>
    rcases (show d = 0 ∨ d = 1 ∨ 2 ≤ d by omega) with rfl | rfl | hd2
    · rw [Nat.add_zero] at hdK ⊢
      rw [B_shift_win3pow_low_ones (by omega) (by omega) hdK,
        B_shift_win3pow_low_ones (by decide) (by decide) (by omega)]
    · rw [B_shift_win3pow_low_ones (by omega) (by omega) hdK,
        B_shift_win3pow_low_ones (by decide) (by decide) (by omega)]
    · have h1 := ih (d - 1) (by omega) (by omega)
      have h2 := ih (d - 2) (by omega) (by omega)
      have hb1 := bstep1_win3pow_shift_13 (K := K) hn hdK
      rw [← win3pow_2_eq_13] at hb1
      unfold B_shift at h1 h2 ⊢
      rw [bstep0_testBit_lt hdK, bstep0_testBit_lt (by omega : d < K),
        ite_eq_right (by omega : n - 2 + d ≠ 0), ite_eq_right (by omega : n - 2 + d ≠ 1),
        ite_eq_right (by omega : d ≠ 0), ite_eq_right (by omega : d ≠ 1),
        show n - 2 + d - 1 = n - 2 + (d - 1) by omega,
        show n - 2 + d - 2 = n - 2 + (d - 2) by omega, h1, h2, hb1]

/-- `97` (`win3pow 5`) is the unique 3-bit period-preserving shift of `13` (`win3pow 2`) in the
`win3pow` family: at width `K = 46`, `bstep1 46 97` and `B_shift 46 97` are given by the exact
shift templates of `bstep1 46 13` and `B_shift 46 13`. -/
theorem bstep1_97_eq_shift_13 :
    bstep1 46 97 = (bstep1 46 13 <<< 3) % 2 ^ 46 := by decide

/-- At width `46`, `B_shift 46 97` equals `B_shift 46 13` shifted left by 3 bits with low 3 bits set (`7`). -/
theorem B_shift_97_eq_shift_13 :
    B_shift 46 97 = ((B_shift 46 13 <<< 3) ||| 7) % 2 ^ 46 := by decide

/-! ## 4. 2-Adic Projective Orbit Reduction & Orbit Stems -/

/-- `W % 2^K` and `W` agree on their lowest `K` bits (`LowEq K (W % 2^K) W`). -/
theorem lowEq_mod_pow (K W : Nat) :
    LowEq K (W % 2 ^ K) W := by
  intro i hi
  rw [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and]

/-- **2-Adic Projective Reduction of `fstep`.** For all `K ≤ K'` and `p < 2`,
`fstep K' W p % 2^K = fstep K (W % 2^K) p`. -/
theorem fstep_mod_pow {K K' W p : Nat} (hKK' : K ≤ K') (hp : p < 2) :
    fstep K' W p % 2 ^ K = fstep K (W % 2 ^ K) p := by
  have hlow := fstep_low (Nat.le_refl K) hKK' (lowEq_mod_pow K W) hp
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < K
  · rw [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and, hlow i hi]
  · rw [Nat.testBit_mod_two_pow, decide_eq_false hi, Bool.false_and,
      Rule30ZeroBoundarySmall.testBit_ge_of_lt (fstep_bound K (W % 2 ^ K) p) (by omega)]

/-- **2-Adic Projective Reduction of `orb`.** For all `K ≤ K'`, `p < 2`, and `t : Nat`,
`(orb K' t (W, p)).1 % 2^K = (orb K t (W % 2^K, p)).1`. -/
theorem orb_mod_pow {K K' W p : Nat} (hKK' : K ≤ K') (hp : p < 2) (t : Nat) :
    (orb K' t (W, p)).1 % 2 ^ K = (orb K t (W % 2 ^ K, p)).1 := by
  have hlow := (orbit_low (Nat.le_refl K) hKK' (lowEq_mod_pow K W) hp t).2.2
  have hbound : (orb K t (W % 2 ^ K, p)).1 < 2 ^ K :=
    orbit_bound (Nat.mod_lt W (Nat.two_pow_pos K)) t
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < K
  · rw [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and, hlow i hi]
  · rw [Nat.testBit_mod_two_pow, decide_eq_false hi, Bool.false_and,
      Rule30ZeroBoundarySmall.testBit_ge_of_lt hbound (by omega)]

/-- **Projective Image of `F_shiftIter`:** For any `k`-bit window `W < 2^k` (`k ≥ 1`) and any width
`K` and step `j`, `(orb K (2 * j) (W % 2^K, 0)).1 = F_shiftIter j W % 2^K`. -/
theorem orb_even_eq_F_shiftIter_mod {k W : Nat} (hk : 1 ≤ k) (hW : W < 2 ^ k) (K j : Nat) :
    (orb K (2 * j) (W % 2 ^ K, 0)).1 = F_shiftIter j W % 2 ^ K := by
  have hKK' : K ≤ k + 4 * j + K := by omega
  have horb := orb_mul_two_eq_F_shiftIter hk hW (K := k + 4 * j + K) (j := j) (by omega)
  rw [← orb_mod_pow hKK' (by decide) (2 * j), horb]

/-- **Emergence of `97` (`k = 7`) from `F_shift^2(13) = 3553`:**
The unique 7-cell primitive root `97` is the 7-bit projective truncation of `F_shiftIter 2 13 = 3553`,
appearing at step `4` on the width-7 orbit of `(13, 0)`. -/
theorem orb_7_4_13_eq_97 :
    orb 7 4 (13, 0) = (97, 0) ∧ F_shiftIter 2 13 % 2 ^ 7 = 97 := by decide

/-- **Emergence of `225` (`k = 8`) from `F_shift^2(13) = 3553`:**
The 8-cell Type I primitive root `225` is the 8-bit projective truncation of `F_shiftIter 2 13 = 3553`,
appearing at step `4` on the width-8 orbit of `(13, 0)`. -/
theorem orb_8_4_13_eq_225 :
    orb 8 4 (13, 0) = (225, 0) ∧ F_shiftIter 2 13 % 2 ^ 8 = 225 := by decide

/-- **Width-32 Orbit Equivalence of the 8-Bit Primitive Roots `165` and `245`.**
Even though `165` and `245` are distinct 8-bit Type II primitive roots, `(245, 0)` lies at even step
`4760` on the width-32 orbit of `(165, 0)`. -/
theorem orb_32_4760_165_eq_245 :
    orb 32 4760 (165, 0) = (245, 0) := by decide +kernel

/-- By `cycle_orb_even_iff`, `(165, 0)` and `(245, 0)` share identical `Cycle 32 S · 0 (2^32)` status
for every horizon `S`. -/
theorem cycle165_iff_cycle245 (S : Nat) :
    Cycle 32 S 165 0 (2 ^ 32) ↔ Cycle 32 S 245 0 (2 ^ 32) := by
  have hper : orb 32 (2 ^ 32) (165, 0) = (165, 0) :=
    universal_front_period 31 165 0 (by decide) (by decide)
  have h := cycle_orb_even_iff (K := 32) (S := S) (W := 165) (p := 0) (lam := 2 ^ 32) (t := 4760)
    (by decide) (by decide) hper
  have h1 : (orb 32 4760 (165, 0)).1 = 245 := by rw [orb_32_4760_165_eq_245]
  rwa [h1] at h

/-! ## 5. Unbounded Clone-Ray Lifting for `97` (`97 → 1659 → 25757 → …`) -/

/-- The second clone on the `97` ray is the 15-bit window `25757 = F_shift (F_shift 97)`. -/
theorem F_shiftIter_2_97_eq : F_shiftIter 2 97 = 25757 := by decide

/-- **Unbounded Ray-97 Mortality Transfer (`∀ j m : Nat`).**
Any horizon-`S` cycle certificate `Cycle K S 97 0 L` (`7 ≤ K`, `S + 1 ≤ K`) for the 7-cell
primitive root `97` automatically proves that for every `j : Nat` (all `(7 + 4 * j)`-bit clones
`97, 1659, 25757, …`) and every odd `m`, `rowTail m (F_shiftIter j 97)` turns depth `1` white at an
even time `t ≤ m + S`. -/
theorem rowTail_ray97_of_cycle97 {K S L : Nat} (hK : 7 ≤ K) (hSK : S + 1 ≤ K)
    (hcyc97 : Cycle K S 97 0 L) (j m : Nat) (hm : m % 2 = 1) :
    (∀ c, 1 ≤ c → c < m + 1 → rowTail m (F_shiftIter j 97) c = stripe c) ∧
      rowTail m (F_shiftIter j 97) (m + 1) ≠ stripe (m + 1) ∧
      ∃ t, t ≤ m + S ∧ t % 2 = 0 ∧ zrow (rowTail m (F_shiftIter j 97)) t 1 = false :=
  rowTail_F_shiftIter_sound (k := 7) (K := K) (S := S) (W := 97) (L := L)
    (by decide) (by decide) (by decide) hK hSK hcyc97 j m hm

/-! ## 6. Predictive Characterization of Horizon-`S` Primitive Exceptions -/

/-- A `k`-bit window `W < 2^k` (`5 ≤ k`) is an algebraic primitive root of the `F_shift` forest if
it has no `(k - 4)`-bit preimage under `F_shift`. -/
def IsPrimRoot (k W : Nat) : Prop :=
  ¬ ∃ V, V < 2 ^ (k - 4) ∧ F_shift V = W

/-- **Exact Characterization of Algebraic Primitive Roots (`5 ≤ k ≤ K`).**
A `k`-bit window `W < 2^k` is a primitive root (`IsPrimRoot k W`) if and only if its 2-step
backward preimage `(bstep1 K W, B_shift K W)` triggers either the Type I (`1^∞`) or Type II
(`(100)^∞` NOR) backward avalanche. -/
theorem isPrimRoot_iff_avalanche {k K W : Nat} (hk : 5 ≤ k) (hK : k < K) (hW : W < 2 ^ k) :
    IsPrimRoot k W ↔
      ((bstep1 K W < 2 ^ (k - 2) ∧ ∀ i, k - 2 ≤ i → i < K → (B_shift K W).testBit i = true) ∨
       ((∀ i, k ≤ i → i < K → (bstep1 K W).testBit i = true) ∧
        (∀ i, k ≤ i → i < K →
          (B_shift K W).testBit i = !((B_shift K W).testBit (i - 1) || (B_shift K W).testBit (i - 2))))) := by
  have hKle : k ≤ K := by omega
  unfold IsPrimRoot
  rw [exists_F_shift_eq_iff hk hKle hW]
  constructor
  · intro hnot
    rcases primitive_or_clone_trichotomy (by omega : 4 ≤ k) hKle hW with hcl | htype1 | htype2
    · exact absurd hcl hnot
    · exact Or.inl htype1
    · exact Or.inr htype2
  · rintro (⟨_, hV_ones⟩ | ⟨hU_ones, _⟩) ⟨hU_lt, hV_lt⟩
    · have hbit : (B_shift K W).testBit (k - 2) = true := hV_ones (k - 2) (by omega) (by omega)
      have hzero : (B_shift K W).testBit (k - 2) = false :=
        Rule30ZeroBoundarySmall.testBit_ge_of_lt hV_lt (by omega)
      rw [hbit] at hzero
      exact Bool.false_ne_true hzero.symm
    · have hbit : (bstep1 K W).testBit k = true := hU_ones k (by omega) hK
      have hzero : (bstep1 K W).testBit k = false :=
        Rule30ZeroBoundarySmall.testBit_ge_of_lt hU_lt (by omega)
      rw [hbit] at hzero
      exact Bool.false_ne_true hzero.symm

/-- **Predictive Rule for Horizon-`S` Primitive Roots (`5 ≤ k ≤ K + 1`).**
A `k`-bit window `w < 2^k` is both a horizon-`S` exception at width `K + 1`
(`¬ Cycle (K + 1) S w 0 (2^(K + 1))`) and an algebraic primitive root (`IsPrimRoot k w`) if and
only if:
1. `(w, 0) = orb_inv K r (x, 1)` for some odd step `r < 2^(K + 1)` and horizon-`S` zero-boundary
   survivor `x < 2^(K + 1)` (`IsOddSurvivor S x`), and
2. `(bstep1 (K + 1) w, B_shift (K + 1) w)` lies in the Type I (`1^∞`) or Type II (`(100)^∞` NOR)
   backward avalanche regime. -/
theorem prim_exception_iff_survivor_avalanche {k K S w : Nat}
    (hk : 5 ≤ k) (hK : k < K + 1) (hw : w < 2 ^ k) :
    (¬ Cycle (K + 1) S w 0 (2 ^ (K + 1)) ∧ IsPrimRoot k w) ↔
      ((∃ r, r < 2 ^ (K + 1) ∧ r % 2 = 1 ∧
          ∃ x, x < 2 ^ (K + 1) ∧ IsOddSurvivor S x ∧ orb_inv K r (x, 1) = (w, 0)) ∧
       ((bstep1 (K + 1) w < 2 ^ (k - 2) ∧
          ∀ i, k - 2 ≤ i → i < K + 1 → (B_shift (K + 1) w).testBit i = true) ∨
        ((∀ i, k ≤ i → i < K + 1 → (bstep1 (K + 1) w).testBit i = true) ∧
         (∀ i, k ≤ i → i < K + 1 →
           (B_shift (K + 1) w).testBit i =
             !((B_shift (K + 1) w).testBit (i - 1) || (B_shift (K + 1) w).testBit (i - 2)))))) := by
  have hwK : w < 2 ^ (K + 1) :=
    Nat.lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) (by omega))
  rw [not_cycle_iff_survivor_pullback K S w hwK, isPrimRoot_iff_avalanche hk hK hw]

/-- Regime verification on the thirteen computed horizon-31 exceptional eight-bit windows (`223` and
the twelve off-ray windows `201, 225, 253` and `131, 143, 159, 165, 169, 181, 189, 245, 255`):
`223 = F_shift 13` lies in the Clone regime (`B_shift 32 223 = 13 < 16`), `201, 225, 253` lie in the
Type I (`1^∞`) regime (`bstep1 32 w < 64`), and `131, 143, 159, 165, 169, 181, 189, 245, 255` lie
in the Type II (`(100)^∞` NOR) regime (`256 ≤ bstep1 32 w`). -/
theorem eight_cell_primitive_root_classification :
    B_shift 32 223 = 13 ∧
    (bstep1 32 201 < 64 ∧ bstep1 32 225 < 64 ∧ bstep1 32 253 < 64) ∧
    (256 ≤ bstep1 32 131 ∧ 256 ≤ bstep1 32 143 ∧ 256 ≤ bstep1 32 159 ∧
     256 ≤ bstep1 32 165 ∧ 256 ≤ bstep1 32 169 ∧ 256 ≤ bstep1 32 181 ∧
     256 ≤ bstep1 32 189 ∧ 256 ≤ bstep1 32 245 ∧ 256 ≤ bstep1 32 255) := by decide

/-- Exhaustive classification of all 64 odd eight-bit windows `w = 128 + 2 * u + 1` (`u : Fin 64`)
into the four algebraic clones `[195, 205, 209, 223]`, twelve Type I primitive roots
`[197, 199, 201, 203, 211, 213, 215, 217, 225, 239, 251, 253]`, and forty-eight Type II primitive roots (`256 ≤ bstep1 12 w`). -/
theorem eight_bit_odd_trichotomy_exhaustive (u : Fin 64) :
    let w := 128 + 2 * u.val + 1
    ((bstep1 12 w < 64 ∧ B_shift 12 w < 16) ↔ w ∈ [195, 205, 209, 223]) ∧
    ((bstep1 12 w < 64 ∧ 16 ≤ B_shift 12 w) ↔ w ∈ [197, 199, 201, 203, 211, 213, 215, 217, 225, 239, 251, 253]) := by
  revert u; decide

end Rule30ZeroBoundaryStripePrimitiveRoots
end Ruliology.CellularAutomata
