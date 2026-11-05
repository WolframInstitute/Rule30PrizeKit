module

public import Ruliology.CellularAutomata.Rule30Prize
public import Ruliology.CellularAutomata.Rule30LeftAntiPeriod

/-!
# Problem 2: the dyadic shell, block-energy and flexible-energy forms

Four exact equivalent forms of `Rule30Prize.Problem2`, for every Boolean sequence `c` and so for the
center column:

* `densityHalf_iff_shellMaxLittleO`: `A(T) - T/2 = o(T)` iff `M_k = o(N)` for the shell maximum
  `M_k` at `N = 2^k`;
* `shellMaxLittleO_iff_flexibleEnergyToZero`: `M_k = o(N)` iff the flexible block energy
  `F_k = min_{0 ≤ j ≤ k} (V_(k,j) + 4^(j-k))` tends to `0`;
* `shellMaxLittleO_iff_orderedEnergyLittleO`, `orderedEnergyLittleO_iff_maxBlockEnergyLittleO`: the
  ordered energy `H_k = o(N^2)`, the largest block energy `max_j E_(k,j) = o(N^2)` and `M_k = o(N)`
  are one statement.

`problem2_iff_densityHalf` ties `DensityHalf` to the official `Problem2`; the other forms follow.

Control, `weakened_hypotheses_do_not_give_densityHalf`: one explicit sequence has `S(2^k) = o(2^k)`
and `min_j V_(k,j) → 0` and fails `DensityHalf`. So the dyadic endpoints alone, and the flexible
energy with its `4^(j-k)` penalty dropped, are both too weak to carry the bridge.

The little-o statements are written over `Nat` and `Int` with denominators cleared; the comment on
each definition gives the translation. Nothing here bounds any of these quantities on the actual
center column. Problem 2 stays open; what is proved is that the four targets are one target.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30P2Bridge

open Rule30RightPeriods
open Rule30Jen Rule30Prize Rule30Diagonals Rule30LeftReset Rule30LeftUnbounded open Rule30LeftAntiPeriod

def sign (bit : Bool) : Int := if bit then -1 else 1

/-- `sumTo f n` is the sum of `f i` over `i < n`. -/
def sumTo (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => sumTo f n + f n

/-- `maxTo f n` is the maximum of `f u` over `u ≤ n`, both ends included. -/
def maxTo (f : Nat → Nat) : Nat → Nat
  | 0 => f 0
  | n + 1 => max (maxTo f n) (f (n + 1))

/-- `A(T)`: the number of ones among `c_0, ..., c_(T-1)`. -/
def ones (c : Nat → Bool) : Nat → Nat
  | 0 => 0
  | T + 1 => ones c T + (if c T then 1 else 0)

/-- `z_t = 1 - 2 c_t`. -/
def z (c : Nat → Bool) (t : Nat) : Int := sign (c t)

/-- `S(T)`: the sum of `z_t` over `t < T`. -/
def S (c : Nat → Bool) (T : Nat) : Int := sumTo (z c) T

/-- The sum of `z_(N+r)` over `r < u`, with `N = 2^k`. -/
def shellPrefix (c : Nat → Bool) (k u : Nat) : Int :=
  sumTo (fun r => z c (2 ^ k + r)) u

/-- `M_k`: the maximum over `0 ≤ u ≤ N` of `|shellPrefix k u|`, with `N = 2^k`. -/
def shellMax (c : Nat → Bool) (k : Nat) : Nat :=
  maxTo (fun u => (shellPrefix c k u).natAbs) (2 ^ k)

/-- `b_(k,j,a)`: the sum of `z` on aligned block `a` of length `2^j` inside shell `k`. -/
def blockSum (c : Nat → Bool) (k j a : Nat) : Int :=
  sumTo (fun r => z c (2 ^ k + a * 2 ^ j + r)) (2 ^ j)

/-- `E_(k,j)`: the sum over the `2^(k-j)` aligned blocks of `b_(k,j,a)^2`. Used only for `j ≤ k`. -/
def blockEnergy (c : Nat → Bool) (k j : Nat) : Int :=
  sumTo (fun a => blockSum c k j a * blockSum c k j a) (2 ^ (k - j))

/-- `H_k`: the sum of `E_(k,j)` over `0 ≤ j ≤ k`. -/
def orderedEnergy (c : Nat → Bool) (k : Nat) : Int :=
  sumTo (fun j => blockEnergy c k j) (k + 1)

/-- P2, `A(T) - T/2 = o(T)`. For `ε = 1/(2m)` the bound `|A(T) - T/2| ≤ εT` is
`m |2A(T) - T| ≤ T`, and every real `ε > 0` dominates some `1/(2m)`. -/
def DensityHalf (c : Nat → Bool) : Prop :=
  ∀ m : Nat, ∃ T0 : Nat, ∀ T : Nat, T0 ≤ T →
    m * (2 * (ones c T : Int) - (T : Int)).natAbs ≤ T

/-- `M_k = o(N)`, `N = 2^k`. -/
def ShellMaxLittleO (c : Nat → Bool) : Prop :=
  ∀ m : Nat, ∃ K : Nat, ∀ k : Nat, K ≤ k → m * shellMax c k ≤ 2 ^ k

/-- `F_k → 0` for `F_k = min over 0 ≤ j ≤ k of (V_(k,j) + 4^(j-k))`, `V_(k,j) = E_(k,j)/(N 2^j)`.
`m F_k ≤ 1` says some `j ≤ k` has `m (E_(k,j)/(2^k 2^j) + 4^j/4^k) ≤ 1`; multiplying by
`4^k 2^j` gives `m (E_(k,j) 2^k + 8^j) ≤ 4^k 2^j`. -/
def FlexibleEnergyToZero (c : Nat → Bool) : Prop :=
  ∀ m : Nat, ∃ K : Nat, ∀ k : Nat, K ≤ k → ∃ j : Nat, j ≤ k ∧
    (m : Int) * (blockEnergy c k j * 2 ^ k + 8 ^ j) ≤ 4 ^ k * 2 ^ j

/-- `H_k = o(N^2)`. -/
def OrderedEnergyLittleO (c : Nat → Bool) : Prop :=
  ∀ m : Nat, ∃ K : Nat, ∀ k : Nat, K ≤ k → (m : Int) * orderedEnergy c k ≤ 4 ^ k

/-- `max over j ≤ k of E_(k,j) = o(N^2)`. -/
def MaxBlockEnergyLittleO (c : Nat → Bool) : Prop :=
  ∀ m : Nat, ∃ K : Nat, ∀ k : Nat, K ≤ k → ∀ j : Nat, j ≤ k →
    (m : Int) * blockEnergy c k j ≤ 4 ^ k

/-- Weakened hypothesis for the control: only the dyadic endpoint sums `S(2^k)` are `o(2^k)`. -/
def DyadicEndpointsLittleO (c : Nat → Bool) : Prop :=
  ∀ m : Nat, ∃ K : Nat, ∀ k : Nat, K ≤ k → m * (S c (2 ^ k)).natAbs ≤ 2 ^ k

/-- Weakened hypothesis for the control: `min over j ≤ k of V_(k,j) → 0`, the flexible
energy with its scale penalty `4^(j-k)` dropped. -/
def UnpenalizedEnergyToZero (c : Nat → Bool) : Prop :=
  ∀ m : Nat, ∃ K : Nat, ∀ k : Nat, K ≤ k → ∃ j : Nat, j ≤ k ∧
    (m : Int) * blockEnergy c k j ≤ 2 ^ k * 2 ^ j

/-! ## Sums, maxima and aligned blocks -/

/-! Proof plan.
`blockSum c k j a = shellPrefix c k ((a+1)*2^j) - shellPrefix c k (a*2^j)` by additivity of
`sumTo`, so `|blockSum| ≤ 2 * shellMax` when `(a+1)*2^j ≤ 2^k`. Each `|z| = 1`, so a sum of
`n` of them has absolute value at most `n`.
Prefix estimate: `u ≤ N` attains `M`. Write `u = q*L + s`, `s < L`, `q ≤ Q = 2^(k-j)`.
`shellPrefix u = (Σ_{a<q} b_a) + tail`, `|tail| ≤ s < L`, so `M - L ≤ |Σ_{a<q} b_a|`.
Cauchy-Schwarz gives `(Σ_{a<q} b_a)^2 ≤ q Σ_{a<q} b_a^2 ≤ Q E`. Multiply by `L`, `Q L = N`. -/

theorem sumTo_succ (f : Nat → Int) (n : Nat) : sumTo f (n + 1) = sumTo f n + f n := rfl

theorem sumTo_add (f : Nat → Int) (m n : Nat) :
    sumTo f (m + n) = sumTo f m + sumTo (fun i => f (m + i)) n := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih =>
    rw [← Nat.add_assoc, sumTo_succ, sumTo_succ, ih]
    omega

theorem sumTo_congr (f g : Nat → Int) (n : Nat) (h : ∀ i, i < n → f i = g i) :
    sumTo f n = sumTo g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumTo_succ, sumTo_succ, ih (fun i hi => h i (by omega)), h n (by omega)]

theorem sumTo_nonneg (f : Nat → Int) (n : Nat) (h : ∀ i, 0 ≤ f i) : 0 ≤ sumTo f n := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih =>
    rw [sumTo_succ]
    have := h n
    omega

theorem sumTo_mono (f : Nat → Int) (h : ∀ i, 0 ≤ f i) (m n : Nat) (hmn : m ≤ n) :
    sumTo f m ≤ sumTo f n := by
  induction n with
  | zero =>
    have : m = 0 := by omega
    subst this
    exact Int.le_refl _
  | succ n ih =>
    by_cases hm : m = n + 1
    · subst hm
      exact Int.le_refl _
    · have h1 := ih (by omega)
      have h2 := h n
      rw [sumTo_succ]
      omega

theorem natAbs_sumTo_le (f : Nat → Int) (n : Nat) (h : ∀ i, (f i).natAbs ≤ 1) :
    (sumTo f n).natAbs ≤ n := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih =>
    rw [sumTo_succ]
    have := h n
    omega

theorem mul_self_nonneg (a : Int) : 0 ≤ a * a := by
  rw [← Int.natAbs_mul_self' a]
  exact Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)

theorem two_mul_le_sq_add_sq (a b : Int) : 2 * (a * b) ≤ a * a + b * b := by
  have h : 0 ≤ (a - b) * (a - b) := mul_self_nonneg _
  have e : (a - b) * (a - b) = a * a - 2 * (a * b) + b * b := by grind
  omega

/-- Cross-term helper for Cauchy-Schwarz. -/
theorem two_sumTo_mul_le (x : Nat → Int) (y : Int) (q : Nat) :
    2 * (sumTo x q * y) ≤ sumTo (fun a => x a * x a) q + (q : Int) * (y * y) := by
  induction q with
  | zero => simp [sumTo]
  | succ q ih =>
    rw [sumTo_succ, sumTo_succ]
    have h1 := two_mul_le_sq_add_sq (x q) y
    have e1 : (sumTo x q + x q) * y = sumTo x q * y + x q * y := by grind
    have e2 : ((q + 1 : Nat) : Int) * (y * y) = (q : Int) * (y * y) + y * y := by
      push_cast
      grind
    rw [e1, e2]
    omega

/-- Cauchy-Schwarz for `sumTo`: `(Σ_{a<q} x_a)^2 ≤ q Σ_{a<q} x_a^2`. -/
theorem sumTo_sq_le (x : Nat → Int) (q : Nat) :
    sumTo x q * sumTo x q ≤ (q : Int) * sumTo (fun a => x a * x a) q := by
  induction q with
  | zero => simp [sumTo]
  | succ q ih =>
    rw [sumTo_succ, sumTo_succ]
    have h1 := two_sumTo_mul_le x (x q) q
    have e1 : (sumTo x q + x q) * (sumTo x q + x q)
        = sumTo x q * sumTo x q + 2 * (sumTo x q * x q) + x q * x q := by grind
    have e2 : ((q + 1 : Nat) : Int) * (sumTo (fun a => x a * x a) q + x q * x q)
        = (q : Int) * sumTo (fun a => x a * x a) q + (q : Int) * (x q * x q)
          + sumTo (fun a => x a * x a) q + x q * x q := by
      push_cast
      grind
    rw [e1, e2]
    omega

theorem sq_le_sq_of_le_natAbs (d B : Int) (hd : 0 ≤ d) (h : d ≤ (B.natAbs : Int)) :
    d * d ≤ B * B := by
  rw [← Int.natAbs_mul_self' B]
  exact Int.mul_le_mul h h hd (Int.natCast_nonneg _)

theorem le_maxTo (f : Nat → Nat) (n u : Nat) (hu : u ≤ n) : f u ≤ maxTo f n := by
  induction n with
  | zero =>
    have : u = 0 := by omega
    subst this
    exact Nat.le_refl _
  | succ n ih =>
    show f u ≤ max (maxTo f n) (f (n + 1))
    by_cases h : u = n + 1
    · subst h
      omega
    · have := ih (by omega)
      omega

theorem maxTo_le (f : Nat → Nat) (n B : Nat) (h : ∀ u, u ≤ n → f u ≤ B) : maxTo f n ≤ B := by
  induction n with
  | zero => exact h 0 (Nat.le_refl _)
  | succ n ih =>
    show max (maxTo f n) (f (n + 1)) ≤ B
    have h1 := ih (fun u hu => h u (by omega))
    have h2 := h (n + 1) (Nat.le_refl _)
    omega

theorem exists_maxTo_attained (f : Nat → Nat) (n : Nat) : ∃ u, u ≤ n ∧ maxTo f n = f u := by
  induction n with
  | zero => exact ⟨0, Nat.le_refl _, rfl⟩
  | succ n ih =>
    rcases ih with ⟨u, hu, he⟩
    by_cases h : maxTo f n ≤ f (n + 1)
    · refine ⟨n + 1, Nat.le_refl _, ?_⟩
      show max (maxTo f n) (f (n + 1)) = f (n + 1)
      omega
    · refine ⟨u, by omega, ?_⟩
      show max (maxTo f n) (f (n + 1)) = f u
      omega

theorem natAbs_z (c : Nat → Bool) (t : Nat) : (z c t).natAbs = 1 := by
  unfold z sign
  split <;> rfl

theorem natAbs_z_le (c : Nat → Bool) (t : Nat) : (z c t).natAbs ≤ 1 :=
  Nat.le_of_eq (natAbs_z c t)

theorem natAbs_shellPrefix_le (c : Nat → Bool) (k u : Nat) : (shellPrefix c k u).natAbs ≤ u :=
  natAbs_sumTo_le _ u (fun _ => natAbs_z_le c _)

/-- `b_(k,j,a) = P((a+1) 2^j) - P(a 2^j)`, stated additively. -/
theorem shellPrefix_succ_block (c : Nat → Bool) (k j a : Nat) :
    shellPrefix c k ((a + 1) * 2 ^ j) = shellPrefix c k (a * 2 ^ j) + blockSum c k j a := by
  unfold shellPrefix blockSum
  have e : (a + 1) * 2 ^ j = a * 2 ^ j + 2 ^ j := by
    rw [Nat.add_mul, Nat.one_mul]
  rw [e, sumTo_add]
  have e2 : sumTo (fun i => (fun r => z c (2 ^ k + r)) (a * 2 ^ j + i)) (2 ^ j)
      = sumTo (fun r => z c (2 ^ k + a * 2 ^ j + r)) (2 ^ j) :=
    sumTo_congr _ _ _ (fun i _ => by
      show z c (2 ^ k + (a * 2 ^ j + i)) = z c (2 ^ k + a * 2 ^ j + i)
      rw [Nat.add_assoc])
  rw [e2]

/-- `Σ_{a<q} b_(k,j,a) = P(q 2^j)`. -/
theorem sumTo_blockSum (c : Nat → Bool) (k j q : Nat) :
    sumTo (fun a => blockSum c k j a) q = shellPrefix c k (q * 2 ^ j) := by
  induction q with
  | zero =>
    rw [Nat.zero_mul]
    rfl
  | succ q ih =>
    rw [sumTo_succ, ih, shellPrefix_succ_block]

theorem pow_sub_mul_pow (k j : Nat) (hj : j ≤ k) : 2 ^ (k - j) * 2 ^ j = 2 ^ k := by
  rw [← Nat.pow_add, Nat.sub_add_cancel hj]

theorem blockEnergy_nonneg (c : Nat → Bool) (k j : Nat) : 0 ≤ blockEnergy c k j := by
  unfold blockEnergy
  exact sumTo_nonneg _ _ (fun a => mul_self_nonneg _)

theorem natAbs_blockSum_le_pow (c : Nat → Bool) (k j a : Nat) :
    (blockSum c k j a).natAbs ≤ 2 ^ j := by
  unfold blockSum
  exact natAbs_sumTo_le _ _ (fun _ => natAbs_z_le c _)

theorem natAbs_shellPrefix_le_shellMax (c : Nat → Bool) (k u : Nat) (hu : u ≤ 2 ^ k) :
    (shellPrefix c k u).natAbs ≤ shellMax c k := by
  unfold shellMax
  exact le_maxTo (fun u => (shellPrefix c k u).natAbs) (2 ^ k) u hu

theorem natAbs_blockSum_le_two_shellMax (c : Nat → Bool) (k j a : Nat)
    (hj : j ≤ k) (ha : a < 2 ^ (k - j)) :
    (blockSum c k j a).natAbs ≤ 2 * shellMax c k := by
  have hN := pow_sub_mul_pow k j hj
  have h1 : (a + 1) * 2 ^ j ≤ 2 ^ k := by
    rw [← hN]
    exact Nat.mul_le_mul_right _ ha
  have h0 : a * 2 ^ j ≤ 2 ^ k := by
    have : a * 2 ^ j ≤ (a + 1) * 2 ^ j := Nat.mul_le_mul_right _ (Nat.le_succ a)
    omega
  have e := shellPrefix_succ_block c k j a
  have b1 := natAbs_shellPrefix_le_shellMax c k _ h1
  have b0 := natAbs_shellPrefix_le_shellMax c k _ h0
  omega

theorem shellMax_le_pow (c : Nat → Bool) (k : Nat) : shellMax c k ≤ 2 ^ k := by
  unfold shellMax
  exact maxTo_le _ _ _ (fun u hu => Nat.le_trans (natAbs_shellPrefix_le c k u) hu)

theorem exists_shellMax_attained (c : Nat → Bool) (k : Nat) :
    ∃ u : Nat, u ≤ 2 ^ k ∧ shellMax c k = (shellPrefix c k u).natAbs := by
  unfold shellMax
  exact exists_maxTo_attained (fun u => (shellPrefix c k u).natAbs) (2 ^ k)

/-- Splitting a prefix at the last aligned block boundary: with `q = u / 2^j`,
`|P(u)| ≤ |Σ_{a<q} b_a| + 2^j`, and `q ≤ 2^(k-j)` when `u ≤ 2^k`. -/
theorem natAbs_shellPrefix_le_blocks (c : Nat → Bool) (k j u : Nat) :
    (shellPrefix c k u).natAbs
      ≤ (sumTo (fun a => blockSum c k j a) (u / 2 ^ j)).natAbs + 2 ^ j := by
  have hL : 0 < 2 ^ j := Nat.two_pow_pos j
  have hdm : u / 2 ^ j * 2 ^ j + u % 2 ^ j = u := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod u (2 ^ j)
  have hs : u % 2 ^ j < 2 ^ j := Nat.mod_lt u hL
  rw [sumTo_blockSum]
  have split : shellPrefix c k u = shellPrefix c k (u / 2 ^ j * 2 ^ j)
      + sumTo (fun i => (fun r => z c (2 ^ k + r)) (u / 2 ^ j * 2 ^ j + i)) (u % 2 ^ j) := by
    have : shellPrefix c k u = shellPrefix c k (u / 2 ^ j * 2 ^ j + u % 2 ^ j) := by rw [hdm]
    rw [this]
    unfold shellPrefix
    exact sumTo_add _ _ _
  have tail : (sumTo (fun i => (fun r => z c (2 ^ k + r)) (u / 2 ^ j * 2 ^ j + i))
      (u % 2 ^ j)).natAbs ≤ u % 2 ^ j :=
    natAbs_sumTo_le _ _ (fun _ => natAbs_z_le c _)
  rw [split]
  omega

/-- The squared prefix estimate: with M = shellMax, L = 2^j, N = 2^k, if M > L then
(M - L)^2 * L ≤ N * E_(k,j). -/
theorem prefix_estimate (c : Nat → Bool) (k j : Nat) (hj : j ≤ k) :
    (shellMax c k : Int) ≤ 2 ^ j ∨
    ((shellMax c k : Int) - 2 ^ j) * ((shellMax c k : Int) - 2 ^ j) * 2 ^ j
      ≤ 2 ^ k * blockEnergy c k j := by
  by_cases hML : (shellMax c k : Int) ≤ 2 ^ j
  · exact Or.inl hML
  · refine Or.inr ?_
    rcases exists_shellMax_attained c k with ⟨u, hu, hM⟩
    have hN := pow_sub_mul_pow k j hj
    have hq : u / 2 ^ j ≤ 2 ^ (k - j) := by
      apply Nat.div_le_of_le_mul
      rw [Nat.mul_comm, hN]
      exact hu
    have hsplit := natAbs_shellPrefix_le_blocks c k j u
    have hLcast : ((2 ^ j : Nat) : Int) = (2 : Int) ^ j := by
      rw [Int.natCast_pow]
      rfl
    have hNcast : ((2 : Int) ^ (k - j)) * (2 : Int) ^ j = (2 : Int) ^ k := by
      rw [← Int.pow_add, Nat.sub_add_cancel hj]
    have hQcast : ((2 ^ (k - j) : Nat) : Int) = (2 : Int) ^ (k - j) := by
      rw [Int.natCast_pow]
      rfl
    -- d ≤ |B|
    have hd0 : 0 ≤ (shellMax c k : Int) - 2 ^ j := by omega
    have hdB : (shellMax c k : Int) - 2 ^ j
        ≤ ((sumTo (fun a => blockSum c k j a) (u / 2 ^ j)).natAbs : Int) := by
      rw [← hLcast]
      omega
    have h1 := sq_le_sq_of_le_natAbs _ _ hd0 hdB
    have h2 := sumTo_sq_le (fun a => blockSum c k j a) (u / 2 ^ j)
    have hsq : ∀ a, 0 ≤ (fun a => blockSum c k j a * blockSum c k j a) a :=
      fun a => mul_self_nonneg _
    have h3 : sumTo (fun a => blockSum c k j a * blockSum c k j a) (u / 2 ^ j)
        ≤ blockEnergy c k j := sumTo_mono _ hsq _ _ hq
    have h3' : 0 ≤ sumTo (fun a => blockSum c k j a * blockSum c k j a) (u / 2 ^ j) :=
      sumTo_nonneg _ _ hsq
    have hqc : ((u / 2 ^ j : Nat) : Int) ≤ (2 : Int) ^ (k - j) := by
      rw [← hQcast]
      exact Int.ofNat_le.mpr hq
    have hQ0 : (0 : Int) ≤ (2 : Int) ^ (k - j) := by
      rw [← hQcast]
      exact Int.natCast_nonneg _
    have hL0 : (0 : Int) ≤ (2 : Int) ^ j := by
      rw [← hLcast]
      exact Int.natCast_nonneg _
    have h4 : ((u / 2 ^ j : Nat) : Int)
          * sumTo (fun a => blockSum c k j a * blockSum c k j a) (u / 2 ^ j)
        ≤ (2 : Int) ^ (k - j) * blockEnergy c k j :=
      Int.mul_le_mul hqc h3 h3' hQ0
    have h5 : ((shellMax c k : Int) - 2 ^ j) * ((shellMax c k : Int) - 2 ^ j)
        ≤ (2 : Int) ^ (k - j) * blockEnergy c k j :=
      Int.le_trans h1 (Int.le_trans h2 h4)
    have h6 := Int.mul_le_mul_of_nonneg_right h5 hL0
    have e : (2 : Int) ^ (k - j) * blockEnergy c k j * 2 ^ j = 2 ^ k * blockEnergy c k j := by
      rw [← hNcast]
      grind
    rw [e] at h6
    exact h6

/-! ## P2.1: density one-half and the shell maximum -/


theorem ones_le (c : Nat → Bool) (T : Nat) : ones c T ≤ T := by
  induction T with
  | zero => simp [ones]
  | succ T ih =>
    simp only [ones]
    split <;> omega

theorem signedSum_eq (c : Nat → Bool) (T : Nat) :
    S c T = (T : Int) - 2 * (ones c T : Int) := by
  induction T with
  | zero => simp [S, sumTo, ones]
  | succ T ih =>
    unfold S at ih ⊢
    simp only [sumTo, ones]
    rw [ih]
    cases h : c T <;> simp [z, sign, h] <;> omega

theorem shellPrefix_eq (c : Nat → Bool) (k u : Nat) :
    shellPrefix c k u = S c (2 ^ k + u) - S c (2 ^ k) := by
  unfold shellPrefix S
  rw [sumTo_add]
  omega

theorem natAbs_S_le (c : Nat → Bool) (n : Nat) : (S c n).natAbs ≤ n := by
  have h1 := signedSum_eq c n
  have h2 := ones_le c n
  omega

theorem densityHalf_imp_shellMaxLittleO (c : Nat → Bool) (h : DensityHalf c) :
    ShellMaxLittleO c := by
  intro m
  rcases h (3 * m) with ⟨T0, hT0⟩
  refine ⟨T0, ?_⟩
  intro k hk
  have hpow : T0 < 2 ^ k :=
    Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by decide) hk)
  rcases exists_maxTo_attained (fun u => (shellPrefix c k u).natAbs) (2 ^ k) with ⟨u, hu, he⟩
  have hM : shellMax c k = (shellPrefix c k u).natAbs := he
  rw [hM, shellPrefix_eq]
  have h1 := hT0 (2 ^ k + u) (by omega)
  have h2 := hT0 (2 ^ k) (by omega)
  have e1 := signedSum_eq c (2 ^ k + u)
  have e2 := signedSum_eq c (2 ^ k)
  have n1 : (2 * (ones c (2 ^ k + u) : Int) - ((2 ^ k + u : Nat) : Int)).natAbs
      = (S c (2 ^ k + u)).natAbs := by omega
  have n2 : (2 * (ones c (2 ^ k) : Int) - ((2 ^ k : Nat) : Int)).natAbs
      = (S c (2 ^ k)).natAbs := by omega
  rw [n1, Nat.mul_assoc] at h1
  rw [n2, Nat.mul_assoc] at h2
  have hx : (S c (2 ^ k + u) - S c (2 ^ k)).natAbs
      ≤ (S c (2 ^ k + u)).natAbs + (S c (2 ^ k)).natAbs := by omega
  have hmul := Nat.mul_le_mul_left m hx
  rw [Nat.mul_add] at hmul
  omega

theorem S_two_pow_succ (c : Nat → Bool) (k : Nat) :
    S c (2 ^ (k + 1)) = S c (2 ^ k) + shellPrefix c k (2 ^ k) := by
  have h := shellPrefix_eq c k (2 ^ k)
  have e : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by omega
  rw [e]
  omega

theorem dyadic_telescope (c : Nat → Bool) (m K : Nat)
    (hK : ∀ k, K ≤ k → 4 * m * shellMax c k ≤ 2 ^ k) (d : Nat) :
    4 * m * (S c (2 ^ (K + d)) - S c (2 ^ K)).natAbs + 2 ^ K ≤ 2 ^ (K + d) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← Nat.add_assoc, S_two_pow_succ]
    have hs := natAbs_shellPrefix_le_shellMax c (K + d) (2 ^ (K + d)) (Nat.le_refl _)
    have hk := hK (K + d) (by omega)
    have hx : (S c (2 ^ (K + d)) + shellPrefix c (K + d) (2 ^ (K + d)) - S c (2 ^ K)).natAbs
        ≤ (S c (2 ^ (K + d)) - S c (2 ^ K)).natAbs + shellMax c (K + d) := by omega
    have hmul := Nat.mul_le_mul_left (4 * m) hx
    rw [Nat.mul_add] at hmul
    omega

theorem shellMaxLittleO_imp_densityHalf (c : Nat → Bool) (h : ShellMaxLittleO c) :
    DensityHalf c := by
  intro m
  rcases h (4 * m) with ⟨K, hK⟩
  refine ⟨2 ^ K * (2 * m + 1), ?_⟩
  intro T hT
  have hpos : 0 < 2 ^ K := Nat.two_pow_pos K
  have hP : 2 ^ K * (2 * m + 1) = 2 * (m * 2 ^ K) + 2 ^ K := by grind
  have hT1 : T ≠ 0 := by omega
  have lo : 2 ^ T.log2 ≤ T := Nat.log2_self_le hT1
  have hi : T < 2 ^ (T.log2 + 1) := Nat.lt_log2_self
  have hKk : K ≤ T.log2 := by
    have hlt : 2 ^ K < 2 ^ (T.log2 + 1) := by omega
    have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hlt
    omega
  generalize T.log2 = k at lo hi hKk
  have hTk : 2 ^ k + (T - 2 ^ k) = T := by omega
  have hu : T - 2 ^ k ≤ 2 ^ k := by omega
  have hd : K + (k - K) = k := by omega
  have tel := dyadic_telescope c m K hK (k - K)
  rw [hd] at tel
  have sp := shellPrefix_eq c k (T - 2 ^ k)
  rw [hTk] at sp
  have hs := natAbs_shellPrefix_le_shellMax c k (T - 2 ^ k) hu
  have hk := hK k hKk
  have hb := natAbs_S_le c (2 ^ K)
  have hx : (S c T).natAbs
      ≤ (S c (2 ^ K)).natAbs + (S c (2 ^ k) - S c (2 ^ K)).natAbs + shellMax c k := by omega
  have hmul := Nat.mul_le_mul_left (4 * m) hx
  rw [Nat.mul_add, Nat.mul_add] at hmul
  have hb' := Nat.mul_le_mul_left (4 * m) hb
  have e1 : 4 * m * 2 ^ K = 4 * (m * 2 ^ K) := Nat.mul_assoc 4 m (2 ^ K)
  have e2 : 4 * m * (S c T).natAbs = 4 * (m * (S c T).natAbs) := Nat.mul_assoc 4 m _
  have eS := signedSum_eq c T
  have n1 : (2 * (ones c T : Int) - (T : Int)).natAbs = (S c T).natAbs := by omega
  rw [n1]
  omega

theorem densityHalf_iff_shellMaxLittleO (c : Nat → Bool) :
    DensityHalf c ↔ ShellMaxLittleO c :=
  ⟨densityHalf_imp_shellMaxLittleO c, shellMaxLittleO_imp_densityHalf c⟩

/-! ## Flexible energy -/

/-! Proof plan, `N = 2^k`, `L = 2^j`, `M = shellMax c k`, `E = blockEnergy c k j`,
`4^k = N*N`, `8^j = L*L*L`.
(<-) Take the flexible-energy hypothesis at `4*m*m`. Both summands are nonnegative, so
`4mm L^3 ≤ N^2 L` and `4mm E N ≤ N^2 L` hold separately. The first gives `(2mL)^2 ≤ N^2`,
so `2mL ≤ N`. `prefix_estimate` gives `M ≤ L`, or `(M-L)^2 L ≤ N E`, and then
`(2m(M-L))^2 L ≤ 4mm N E ≤ N^2 L`, so `2m(M-L) ≤ N`. Either way `2mM ≤ 2N`.
(->) Take the shell-max hypothesis at `8m` and `k ≥ 2m`, so `8mM ≤ N` and `2m ≤ N^2`.
Pick `j` minimal with `8 m M^2 ≤ L^2`; minimality gives `j = 0` or `L^2 < 32 m M^2`, and in
both cases `2 m L^2 ≤ N^2`, hence `L ≤ N` and `j ≤ k`. Each `|b_a| ≤ 2M`, so
`E L ≤ N 4 M^2`. Multiply the goal by `L > 0`:
`m E N L ≤ 4 m M^2 N^2 ≤ N^2 L^2 / 2` and `m L^4 ≤ N^2 L^2 / 2`. -/

theorem le_of_mul_self_le (a b : Int) (hb : 0 ≤ b) (h : a * a ≤ b * b) : a ≤ b := by
  by_cases hab : a ≤ b
  · exact hab
  · have hlt : b < a := by omega
    have ha : 0 < a := by omega
    have h1 : b * b ≤ b * a := Int.mul_le_mul_of_nonneg_left (Int.le_of_lt hlt) hb
    have h2 : b * a < a * a := Int.mul_lt_mul_of_pos_right hlt ha
    omega

theorem four_pow_eq (k : Nat) : (4 : Int) ^ k = 2 ^ k * 2 ^ k := by
  have e : (4 : Int) = 2 * 2 := by decide
  rw [e, Int.mul_pow]

theorem eight_pow_eq (j : Nat) : (8 : Int) ^ j = 2 ^ j * 2 ^ j * 2 ^ j := by
  have e : (8 : Int) = 2 * 2 * 2 := by decide
  rw [e, Int.mul_pow, Int.mul_pow]

/-- The arithmetic core of (<-). -/
theorem back_core (m N L M E : Int) (hm : 0 ≤ m) (hN : 0 ≤ N) (hL : 0 < L) (hE : 0 ≤ E)
    (h : 4 * m * m * (E * N + L * L * L) ≤ N * N * L)
    (pe : M ≤ L ∨ (M - L) * (M - L) * L ≤ N * E) : m * M ≤ N := by
  have h4 : 0 ≤ 4 * m * m := Int.mul_nonneg (Int.mul_nonneg (by omega) hm) hm
  have hEN : 0 ≤ 4 * m * m * (E * N) := Int.mul_nonneg h4 (Int.mul_nonneg hE hN)
  have hL3 : 0 ≤ 4 * m * m * (L * L * L) :=
    Int.mul_nonneg h4 (Int.mul_nonneg (Int.mul_nonneg (by omega) (by omega)) (by omega))
  have ed : 4 * m * m * (E * N + L * L * L)
      = 4 * m * m * (E * N) + 4 * m * m * (L * L * L) := by grind
  rw [ed] at h
  have e1 : 4 * m * m * (L * L * L) = (2 * m * L) * (2 * m * L) * L := by grind
  have h1 : (2 * m * L) * (2 * m * L) * L ≤ N * N * L := by
    rw [← e1]
    omega
  have h2 : 2 * m * L ≤ N := le_of_mul_self_le _ _ hN (Int.le_of_mul_le_mul_right h1 hL)
  have e2 : 2 * m * L = 2 * (m * L) := by grind
  rw [e2] at h2
  rcases pe with hML | hP
  · have h3 : m * M ≤ m * L := Int.mul_le_mul_of_nonneg_left hML hm
    have h5 : 0 ≤ m * L := Int.mul_nonneg hm (by omega)
    omega
  · have h3 : 4 * m * m * ((M - L) * (M - L) * L) ≤ 4 * m * m * (N * E) :=
      Int.mul_le_mul_of_nonneg_left hP h4
    have e3 : 4 * m * m * ((M - L) * (M - L) * L)
        = (2 * m * (M - L)) * (2 * m * (M - L)) * L := by grind
    have e4 : 4 * m * m * (N * E) = 4 * m * m * (E * N) := by grind
    have h5 : (2 * m * (M - L)) * (2 * m * (M - L)) * L ≤ N * N * L := by
      rw [← e3]
      omega
    have h6 : 2 * m * (M - L) ≤ N :=
      le_of_mul_self_le _ _ hN (Int.le_of_mul_le_mul_right h5 hL)
    have e5 : 2 * m * (M - L) = 2 * (m * M) - 2 * (m * L) := by grind
    rw [e5] at h6
    omega

/-- The arithmetic core of (->). -/
theorem fwd_core (m N L M E : Int) (hm : 0 ≤ m) (hN : 0 ≤ N) (hL : 0 < L)
    (hEL : E * L ≤ N * (4 * (M * M)))
    (hLM : 8 * (m * (M * M)) ≤ L * L)
    (hLN : 2 * (m * (L * L)) ≤ N * N) :
    m * (E * N + L * L * L) ≤ N * N * L := by
  apply Int.le_of_mul_le_mul_right (a := L) _ hL
  have hmN : 0 ≤ m * N := Int.mul_nonneg hm hN
  have hNN : 0 ≤ N * N := Int.mul_nonneg hN hN
  have hLL : 0 ≤ L * L := Int.mul_nonneg (by omega) (by omega)
  have a1 : m * N * (E * L) ≤ m * N * (N * (4 * (M * M))) :=
    Int.mul_le_mul_of_nonneg_left hEL hmN
  have a2 : N * N * (8 * (m * (M * M))) ≤ N * N * (L * L) :=
    Int.mul_le_mul_of_nonneg_left hLM hNN
  have a3 : 2 * (m * (L * L)) * (L * L) ≤ N * N * (L * L) :=
    Int.mul_le_mul_of_nonneg_right hLN hLL
  have e0 : m * (E * N + L * L * L) * L = m * N * (E * L) + m * (L * L) * (L * L) := by grind
  have e1 : m * N * (N * (4 * (M * M))) = 4 * (N * N * (m * (M * M))) := by grind
  have e2 : N * N * (8 * (m * (M * M))) = 8 * (N * N * (m * (M * M))) := by grind
  have e3 : 2 * (m * (L * L)) * (L * L) = 2 * (m * (L * L) * (L * L)) := by grind
  have e4 : N * N * L * L = N * N * (L * L) := by grind
  rw [e0, e4]
  rw [e1] at a1
  rw [e2] at a2
  rw [e3] at a3
  omega

/-- A minimal dyadic scale: `B ≤ L^2` with `L = 2^j`, and `j = 0` or `L^2 < 4B`. -/
theorem exists_min_scale (B : Nat) :
    ∃ j : Nat, B ≤ 2 ^ j * 2 ^ j ∧ (j = 0 ∨ 2 ^ j * 2 ^ j < 4 * B) := by
  have aux : ∀ n : Nat, B ≤ 2 ^ n * 2 ^ n →
      ∃ j : Nat, B ≤ 2 ^ j * 2 ^ j ∧ (j = 0 ∨ 2 ^ j * 2 ^ j < 4 * B) := by
    intro n
    induction n with
    | zero =>
      intro h
      exact ⟨0, h, Or.inl rfl⟩
    | succ n ih =>
      intro h
      by_cases hn : B ≤ 2 ^ n * 2 ^ n
      · exact ih hn
      · refine ⟨n + 1, h, Or.inr ?_⟩
        have e : 2 ^ (n + 1) * 2 ^ (n + 1) = 4 * (2 ^ n * 2 ^ n) := by
          rw [Nat.pow_succ]
          grind
        omega
  apply aux B
  have h1 : B < 2 ^ B := Nat.lt_two_pow_self
  have h2 : 2 ^ B ≤ 2 ^ B * 2 ^ B := Nat.le_mul_self _
  omega

theorem scale_bound (m N L M : Nat) (h8 : 8 * m * M ≤ N) (h2 : 2 * m ≤ N * N)
    (hmin : L = 1 ∨ L * L < 4 * (8 * (m * (M * M)))) : 2 * (m * (L * L)) ≤ N * N := by
  rcases hmin with h | h
  · subst h
    omega
  · have hsq : (8 * m * M) * (8 * m * M) ≤ N * N := Nat.mul_self_le_mul_self h8
    have h3 : m * (L * L) ≤ m * (4 * (8 * (m * (M * M)))) :=
      Nat.mul_le_mul_left m (Nat.le_of_lt h)
    have e : 2 * (m * (4 * (8 * (m * (M * M))))) = (8 * m * M) * (8 * m * M) := by grind
    omega

theorem sumTo_le_mul (f : Nat → Int) (n : Nat) (B : Int) (h : ∀ a, a < n → f a ≤ B) :
    sumTo f n ≤ (n : Int) * B := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih =>
    rw [sumTo_succ]
    have h1 := ih (fun a ha => h a (by omega))
    have h2 := h n (by omega)
    have e : ((n + 1 : Nat) : Int) * B = (n : Int) * B + B := by
      push_cast
      grind
    rw [e]
    omega

theorem blockSum_sq_le (c : Nat → Bool) (k j a : Nat) (hj : j ≤ k) (ha : a < 2 ^ (k - j)) :
    blockSum c k j a * blockSum c k j a
      ≤ 4 * ((shellMax c k : Int) * (shellMax c k : Int)) := by
  have h := natAbs_blockSum_le_two_shellMax c k j a hj ha
  have hc : ((blockSum c k j a).natAbs : Int) ≤ 2 * (shellMax c k : Int) := by
    exact_mod_cast h
  rw [← Int.natAbs_mul_self' (blockSum c k j a)]
  have h2 := Int.mul_le_mul hc hc (Int.natCast_nonneg _)
    (by omega : (0 : Int) ≤ 2 * (shellMax c k : Int))
  have e : 2 * (shellMax c k : Int) * (2 * (shellMax c k : Int))
      = 4 * ((shellMax c k : Int) * (shellMax c k : Int)) := by grind
  omega

/-- `E_(k,j) 2^j ≤ 2^k 4 M_k^2`. -/
theorem blockEnergy_mul_le (c : Nat → Bool) (k j : Nat) (hj : j ≤ k) :
    blockEnergy c k j * 2 ^ j
      ≤ 2 ^ k * (4 * ((shellMax c k : Int) * (shellMax c k : Int))) := by
  have h1 : blockEnergy c k j
      ≤ ((2 ^ (k - j) : Nat) : Int) * (4 * ((shellMax c k : Int) * (shellMax c k : Int))) := by
    unfold blockEnergy
    exact sumTo_le_mul _ _ _ (fun a ha => blockSum_sq_le c k j a hj ha)
  have hQ : ((2 ^ (k - j) : Nat) : Int) = (2 : Int) ^ (k - j) := by
    rw [Int.natCast_pow]
    rfl
  rw [hQ] at h1
  have hL0 : (0 : Int) ≤ 2 ^ j := Int.pow_nonneg (by decide)
  have h2 := Int.mul_le_mul_of_nonneg_right h1 hL0
  have hN : (2 : Int) ^ (k - j) * 2 ^ j = 2 ^ k := by
    rw [← Int.pow_add, Nat.sub_add_cancel hj]
  have e : (2 : Int) ^ (k - j) * (4 * ((shellMax c k : Int) * (shellMax c k : Int))) * 2 ^ j
      = 2 ^ k * (4 * ((shellMax c k : Int) * (shellMax c k : Int))) := by
    rw [← hN]
    grind
  rw [e] at h2
  exact h2

theorem shellMaxLittleO_of_flexibleEnergyToZero (c : Nat → Bool)
    (hF : FlexibleEnergyToZero c) : ShellMaxLittleO c := by
  intro m
  rcases hF (4 * m * m) with ⟨K, hK⟩
  refine ⟨K, fun k hk => ?_⟩
  rcases hK k hk with ⟨j, hj, h⟩
  rw [four_pow_eq, eight_pow_eq] at h
  have hcast : ((4 * m * m : Nat) : Int) = 4 * (m : Int) * (m : Int) := by
    push_cast
    rfl
  rw [hcast] at h
  have hL : (0 : Int) < 2 ^ j := Int.pow_pos (by decide)
  have hN : (0 : Int) ≤ 2 ^ k := Int.pow_nonneg (by decide)
  have key := back_core (m : Int) (2 ^ k) (2 ^ j) (shellMax c k : Int) (blockEnergy c k j)
    (Int.natCast_nonneg _) hN hL (blockEnergy_nonneg c k j) h (prefix_estimate c k j hj)
  exact_mod_cast key

theorem flexibleEnergyToZero_of_shellMaxLittleO (c : Nat → Bool)
    (hS : ShellMaxLittleO c) : FlexibleEnergyToZero c := by
  intro m
  by_cases hm0 : m = 0
  · subst hm0
    refine ⟨0, fun k _ => ⟨0, Nat.zero_le _, ?_⟩⟩
    have h1 : (0 : Int) ≤ 4 ^ k * 2 ^ 0 :=
      Int.mul_nonneg (Int.pow_nonneg (by decide)) (Int.pow_nonneg (by decide))
    have e0 : ((0 : Nat) : Int) = 0 := rfl
    rw [e0, Int.zero_mul]
    exact h1
  · have hm : 1 ≤ m := by omega
    rcases hS (8 * m) with ⟨K0, hK0⟩
    refine ⟨max K0 (2 * m), fun k hk => ?_⟩
    have h8 : 8 * m * shellMax c k ≤ 2 ^ k := hK0 k (by omega)
    have hk2 : 2 * m ≤ 2 ^ k * 2 ^ k := by
      have h1 : k < 2 ^ k := Nat.lt_two_pow_self
      have h2 : 2 ^ k ≤ 2 ^ k * 2 ^ k := Nat.le_mul_self _
      omega
    rcases exists_min_scale (8 * (m * (shellMax c k * shellMax c k))) with ⟨j, hjB, hjmin⟩
    have hmin' : 2 ^ j = 1 ∨ 2 ^ j * 2 ^ j < 4 * (8 * (m * (shellMax c k * shellMax c k))) := by
      rcases hjmin with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr h
    have hLN : 2 * (m * (2 ^ j * 2 ^ j)) ≤ 2 ^ k * 2 ^ k :=
      scale_bound m (2 ^ k) (2 ^ j) (shellMax c k) h8 hk2 hmin'
    have hjk : j ≤ k := by
      have h1 : 2 ^ j * 2 ^ j ≤ m * (2 ^ j * 2 ^ j) := Nat.le_mul_of_pos_left _ hm
      have h2 : 2 ^ j * 2 ^ j ≤ 2 ^ k * 2 ^ k := by omega
      have h3 : 2 ^ j ≤ 2 ^ k := Nat.mul_self_le_mul_self_iff.mp h2
      exact (Nat.pow_le_pow_iff_right (by decide)).mp h3
    refine ⟨j, hjk, ?_⟩
    have hEL := blockEnergy_mul_le c k j hjk
    have hLMi : 8 * ((m : Int) * ((shellMax c k : Int) * (shellMax c k : Int)))
        ≤ (2 : Int) ^ j * 2 ^ j := by
      exact_mod_cast hjB
    have hLNi : 2 * ((m : Int) * ((2 : Int) ^ j * 2 ^ j)) ≤ (2 : Int) ^ k * 2 ^ k := by
      exact_mod_cast hLN
    have hL : (0 : Int) < 2 ^ j := Int.pow_pos (by decide)
    have hN : (0 : Int) ≤ 2 ^ k := Int.pow_nonneg (by decide)
    have key := fwd_core (m : Int) (2 ^ k) (2 ^ j) (shellMax c k : Int) (blockEnergy c k j)
      (Int.natCast_nonneg _) hN hL hEL hLMi hLNi
    rw [four_pow_eq, eight_pow_eq]
    exact key

theorem shellMaxLittleO_iff_flexibleEnergyToZero (c : Nat → Bool) :
    ShellMaxLittleO c ↔ FlexibleEnergyToZero c := by
  exact ⟨flexibleEnergyToZero_of_shellMaxLittleO c, shellMaxLittleO_of_flexibleEnergyToZero c⟩

/-! ## P2.2: ordered energy -/

/-! Proof plan, with `N = 2^k`, `L = 2^j`, `M = shellMax c k`, `E_j = blockEnergy c k j`,
`H = orderedEnergy c k`.
(1) `E_j ≤ H` for `j ≤ k`: every `E_i ≥ 0`, so one term is at most the whole sum.
(2) Given `m ≥ 1`, pick `i` with `2m ≤ 2^i ≤ 4m` and apply the hypothesis at `16 m^3`. For
`k ≥ i` put `j = k - i`, so `2mL ≤ N ≤ 4mL`. `prefix_estimate` gives `M ≤ L`, whence
`mM ≤ mL ≤ N`, or `P = M - L` has `P^2 L ≤ N E_j`. Then
`16 m^3 P^2 L ≤ N (16 m^3 E_j) ≤ N^3 ≤ N^2 4mL`; cancelling `4mL > 0` gives `(2mP)^2 ≤ N^2`, so
`2mP ≤ N`, and `2mM = 2mP + 2mL ≤ 2N`.
(3) `|b_a| ≤ min(L, 2M)` so `E_j ≤ 2^(k-j) g_j` with `g_j = min(4^j, 4M^2)`. For
`F_k = Σ_{j≤k} 2^(k-j) g_j` one has `F_(k+1) = 2 F_k + g_(k+1)`, and by induction on `k`
`F_k ≤ 2 * 4^k` always and `F_k + 4M^2 ≤ 8 M 2^k` once `M ≤ 2^k`. The second starts in the
window `2^k < M ≤ 2^(k+1)` from the first, using `x^2 ≤ Mx` and `M^2 ≤ 2Mx` at `x = 2^k`.
Since `M ≤ N` always, `H ≤ 8MN`, and `ShellMaxLittleO` at `8m` gives `mH ≤ (8mM) N ≤ N^2`. -/

theorem natCast_two_pow (k : Nat) : ((2 ^ k : Nat) : Int) = (2 : Int) ^ k := by
  rw [Int.natCast_pow]
  rfl

theorem term_le_sumTo (f : Nat → Int) (h : ∀ i, 0 ≤ f i) (n j : Nat) (hj : j < n) :
    f j ≤ sumTo f n := by
  have h1 : sumTo f (j + 1) ≤ sumTo f n := sumTo_mono f h (j + 1) n hj
  have h2 : 0 ≤ sumTo f j := sumTo_nonneg f j h
  rw [sumTo_succ] at h1
  omega

theorem blockEnergy_le_orderedEnergy (c : Nat → Bool) (k j : Nat) (hj : j ≤ k) :
    blockEnergy c k j ≤ orderedEnergy c k := by
  unfold orderedEnergy
  exact term_le_sumTo (fun j => blockEnergy c k j) (fun i => blockEnergy_nonneg c k i)
    (k + 1) j (by omega)

theorem orderedEnergyLittleO_imp_maxBlockEnergyLittleO (c : Nat → Bool) :
    OrderedEnergyLittleO c → MaxBlockEnergyLittleO c := by
  intro h m
  rcases h m with ⟨K, hK⟩
  refine ⟨K, fun k hk j hj => ?_⟩
  have h1 := hK k hk
  have h2 := blockEnergy_le_orderedEnergy c k j hj
  have h3 : (m : Int) * blockEnergy c k j ≤ (m : Int) * orderedEnergy c k :=
    Int.mul_le_mul_of_nonneg_left h2 (Int.natCast_nonneg m)
  exact Int.le_trans h3 h1

theorem exists_pow_between (m : Nat) (hm : m ≠ 0) : ∃ i, 2 * m ≤ 2 ^ i ∧ 2 ^ i ≤ 4 * m := by
  refine ⟨(2 * m).log2 + 1, ?_, ?_⟩
  · have h1 := @Nat.lt_log2_self (2 * m)
    omega
  · have h2 := @Nat.log2_self_le (2 * m) (by omega)
    omega

/-- The cancellation step of (2): from `P^2 L ≤ N E`, `16 m^3 E ≤ N^2` and `N ≤ 4mL`. -/
theorem two_mul_le_of_energy (m P L N E : Int) (hm : 0 < m) (hL : 0 < L) (hN : 0 ≤ N)
    (hc : N ≤ 4 * (m * L)) (hyp : 16 * (m * m * m) * E ≤ N * N)
    (h : P * P * L ≤ N * E) : 2 * (m * P) ≤ N := by
  have hm0 : 0 ≤ m := Int.le_of_lt hm
  have hm3 : 0 ≤ 16 * (m * m * m) := by
    have := Int.mul_nonneg (Int.mul_nonneg hm0 hm0) hm0
    omega
  have hA := Int.mul_le_mul_of_nonneg_left h hm3
  have hB := Int.mul_le_mul_of_nonneg_left hyp hN
  have hNN : 0 ≤ N * N := Int.mul_nonneg hN hN
  have hC := Int.mul_le_mul_of_nonneg_left hc hNN
  have e1 : 16 * (m * m * m) * (N * E) = N * (16 * (m * m * m) * E) := by grind
  have e2 : 16 * (m * m * m) * (P * P * L)
      = 4 * (m * L) * ((2 * (m * P)) * (2 * (m * P))) := by grind
  have e3 : N * N * (4 * (m * L)) = 4 * (m * L) * (N * N) := by grind
  have e4 : N * (N * N) = N * N * N := by grind
  have hD : 4 * (m * L) * ((2 * (m * P)) * (2 * (m * P))) ≤ 4 * (m * L) * (N * N) := by
    rw [← e2, ← e3]
    omega
  have hpos : 0 < 4 * (m * L) := by
    have := Int.mul_pos hm hL
    omega
  exact le_of_mul_self_le _ _ hN (Int.le_of_mul_le_mul_left hD hpos)

theorem mul_shellMax_le_of_energy (m M L N E : Int) (hm : 0 < m) (hL : 0 < L) (hN : 0 ≤ N)
    (hd : 2 * (m * L) ≤ N) (hc : N ≤ 4 * (m * L))
    (hyp : 16 * (m * m * m) * E ≤ N * N)
    (pe : M ≤ L ∨ (M - L) * (M - L) * L ≤ N * E) : m * M ≤ N := by
  have hmL : 0 < m * L := Int.mul_pos hm hL
  by_cases hML : M ≤ L
  · have := Int.mul_le_mul_of_nonneg_left hML (Int.le_of_lt hm)
    omega
  · have h : (M - L) * (M - L) * L ≤ N * E := by
      rcases pe with h | h
      · exact absurd h hML
      · exact h
    have h1 := two_mul_le_of_energy m (M - L) L N E hm hL hN hc hyp h
    have e : m * (M - L) = m * M - m * L := by grind
    rw [e] at h1
    omega

theorem maxBlockEnergyLittleO_imp_shellMaxLittleO (c : Nat → Bool) :
    MaxBlockEnergyLittleO c → ShellMaxLittleO c := by
  intro h m
  by_cases hm0 : m = 0
  · subst hm0
    exact ⟨0, fun k _ => by simp⟩
  · rcases h (16 * m * m * m) with ⟨K0, hK0⟩
    rcases exists_pow_between m hm0 with ⟨i, hi1, hi2⟩
    refine ⟨max K0 i, fun k hk => ?_⟩
    have hk0 : K0 ≤ k := by omega
    have hik : i ≤ k := by omega
    have hj : k - i ≤ k := Nat.sub_le _ _
    have hpow : 2 ^ i * 2 ^ (k - i) = 2 ^ k := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hdN : 2 * m * 2 ^ (k - i) ≤ 2 ^ k := by
      rw [← hpow]
      exact Nat.mul_le_mul_right _ hi1
    have hcN : 2 ^ k ≤ 4 * m * 2 ^ (k - i) := by
      rw [← hpow]
      exact Nat.mul_le_mul_right _ hi2
    have hd : 2 * ((m : Int) * (2 : Int) ^ (k - i)) ≤ (2 : Int) ^ k := by
      have := Int.ofNat_le.mpr hdN
      push_cast at this
      rw [Int.mul_assoc] at this
      exact this
    have hc : (2 : Int) ^ k ≤ 4 * ((m : Int) * (2 : Int) ^ (k - i)) := by
      have := Int.ofNat_le.mpr hcN
      push_cast at this
      rw [Int.mul_assoc] at this
      exact this
    have hyp := hK0 k hk0 (k - i) hj
    have e : ((16 * m * m * m : Nat) : Int) = 16 * ((m : Int) * (m : Int) * (m : Int)) := by
      push_cast
      grind
    rw [e, four_pow_eq] at hyp
    have pe := prefix_estimate c k (k - i) hj
    have hmpos : (0 : Int) < (m : Int) := by omega
    have hLpos : (0 : Int) < (2 : Int) ^ (k - i) := Int.pow_pos (by decide)
    have hNnn : (0 : Int) ≤ (2 : Int) ^ k := Int.le_of_lt (Int.pow_pos (by decide))
    have fin := mul_shellMax_le_of_energy (m : Int) (shellMax c k : Int) ((2 : Int) ^ (k - i))
      ((2 : Int) ^ k) (blockEnergy c k (k - i)) hmpos hLpos hNnn hd hc hyp pe
    apply Int.ofNat_le.mp
    push_cast
    exact fin

theorem sumTo_mul_left (a : Int) (f : Nat → Int) (n : Nat) :
    sumTo (fun i => a * f i) n = a * sumTo f n := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih => rw [sumTo_succ, sumTo_succ, ih, Int.mul_add]

theorem sumTo_le_sumTo (f g : Nat → Int) (n : Nat) (h : ∀ i, i < n → f i ≤ g i) :
    sumTo f n ≤ sumTo g n := by
  induction n with
  | zero => exact Int.le_refl _
  | succ n ih =>
    rw [sumTo_succ, sumTo_succ]
    have h1 := ih (fun i hi => h i (by omega))
    have h2 := h n (by omega)
    omega

theorem sumTo_le_const (f : Nat → Int) (n : Nat) (B : Int) (h : ∀ i, i < n → f i ≤ B) :
    sumTo f n ≤ (n : Int) * B := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih =>
    rw [sumTo_succ]
    have h1 := ih (fun i hi => h i (by omega))
    have h2 := h n (by omega)
    have e : ((n + 1 : Nat) : Int) * B = (n : Int) * B + B := by
      push_cast
      grind
    rw [e]
    omega

/-- `F_(k+1) = 2 F_k + g_(k+1)` for `F_k = Σ_{j≤k} 2^(k-j) g_j`. -/
theorem geomSum_succ (g : Nat → Int) (k : Nat) :
    sumTo (fun j => 2 ^ (k + 1 - j) * g j) (k + 1 + 1)
      = 2 * sumTo (fun j => 2 ^ (k - j) * g j) (k + 1) + g (k + 1) := by
  rw [sumTo_succ, ← sumTo_mul_left]
  have e1 : sumTo (fun j => (2 : Int) ^ (k + 1 - j) * g j) (k + 1)
      = sumTo (fun j => 2 * ((2 : Int) ^ (k - j) * g j)) (k + 1) :=
    sumTo_congr _ _ _ (fun j hj => by
      show (2 : Int) ^ (k + 1 - j) * g j = 2 * ((2 : Int) ^ (k - j) * g j)
      have : k + 1 - j = (k - j) + 1 := by omega
      rw [this, Int.pow_succ]
      grind)
  rw [e1]
  show _ + (2 : Int) ^ (k + 1 - (k + 1)) * g (k + 1) = _
  rw [Nat.sub_self, Int.pow_zero, Int.one_mul]

/-- The arithmetic core of (3). -/
theorem geom_bound (g : Nat → Int) (M : Int) (hM : 0 ≤ M)
    (h1 : ∀ j, g j ≤ 2 ^ j * 2 ^ j) (h2 : ∀ j, g j ≤ 4 * (M * M)) (k : Nat) :
    sumTo (fun j => 2 ^ (k - j) * g j) (k + 1) ≤ 2 * (2 ^ k * 2 ^ k) ∧
    (M ≤ 2 ^ k →
      sumTo (fun j => 2 ^ (k - j) * g j) (k + 1) + 4 * (M * M) ≤ 8 * (M * 2 ^ k)) := by
  induction k with
  | zero =>
    have a1 := h1 0
    have a2 := h2 0
    have e : sumTo (fun j => (2 : Int) ^ (0 - j) * g j) (0 + 1) = g 0 := by
      simp [sumTo]
    have p0 : (2 : Int) ^ 0 = 1 := Int.pow_zero 2
    rw [e, p0]
    rw [p0] at a1
    refine ⟨by omega, fun hM1 => ?_⟩
    have hcases : M = 0 ∨ M = 1 := by omega
    rcases hcases with h0 | h0
    · subst h0
      omega
    · subst h0
      omega
  | succ k ih =>
    rcases ih with ⟨ih1, ih2⟩
    rw [geomSum_succ]
    have hx : (0 : Int) < 2 ^ k := Int.pow_pos (by decide)
    have p : (2 : Int) ^ (k + 1) = 2 * 2 ^ k := by omega
    have a1 := h1 (k + 1)
    have a2 := h2 (k + 1)
    rw [p] at a1 ⊢
    have e1 : (2 * (2 : Int) ^ k) * (2 * 2 ^ k) = 4 * (2 ^ k * 2 ^ k) := by grind
    have e2 : M * (2 * (2 : Int) ^ k) = 2 * (M * 2 ^ k) := by grind
    rw [e1] at a1
    rw [e1, e2]
    refine ⟨by omega, fun hMx => ?_⟩
    by_cases hc : M ≤ 2 ^ k
    · have := ih2 hc
      omega
    · have hxM : (2 : Int) ^ k ≤ M := by omega
      have q1 : (2 : Int) ^ k * 2 ^ k ≤ M * 2 ^ k :=
        Int.mul_le_mul_of_nonneg_right hxM (by omega)
      have q2 : M * M ≤ M * (2 * 2 ^ k) := Int.mul_le_mul_of_nonneg_left hMx hM
      rw [e2] at q2
      omega

theorem sq_le_of_natAbs_le (b : Int) (B : Nat) (h : b.natAbs ≤ B) :
    b * b ≤ (B : Int) * (B : Int) := by
  rw [← Int.natAbs_mul_self' b]
  have hc : (b.natAbs : Int) ≤ (B : Int) := Int.ofNat_le.mpr h
  exact Int.mul_le_mul hc hc (Int.natCast_nonneg _) (Int.natCast_nonneg _)

theorem blockSum_sq_le_min (c : Nat → Bool) (k j a : Nat) (hj : j ≤ k) (ha : a < 2 ^ (k - j)) :
    blockSum c k j a * blockSum c k j a
      ≤ min ((2 : Int) ^ j * 2 ^ j) (4 * ((shellMax c k : Int) * (shellMax c k : Int))) := by
  have h1 := sq_le_of_natAbs_le _ _ (natAbs_blockSum_le_pow c k j a)
  have h2 := sq_le_of_natAbs_le _ _ (natAbs_blockSum_le_two_shellMax c k j a hj ha)
  rw [natCast_two_pow] at h1
  have e : ((2 * shellMax c k : Nat) : Int) * ((2 * shellMax c k : Nat) : Int)
      = 4 * ((shellMax c k : Int) * (shellMax c k : Int)) := by
    push_cast
    grind
  rw [e] at h2
  omega

theorem blockEnergy_le_geom (c : Nat → Bool) (k j : Nat) (hj : j ≤ k) :
    blockEnergy c k j
      ≤ 2 ^ (k - j)
        * min ((2 : Int) ^ j * 2 ^ j) (4 * ((shellMax c k : Int) * (shellMax c k : Int))) := by
  unfold blockEnergy
  have h := sumTo_le_const (fun a => blockSum c k j a * blockSum c k j a) (2 ^ (k - j)) _
    (fun a ha => blockSum_sq_le_min c k j a hj ha)
  rw [natCast_two_pow] at h
  exact h

/-- `H_k ≤ 8 M_k 2^k`. -/
theorem orderedEnergy_le (c : Nat → Bool) (k : Nat) :
    orderedEnergy c k ≤ 8 * ((shellMax c k : Int) * 2 ^ k) := by
  have hM : (0 : Int) ≤ (shellMax c k : Int) := Int.natCast_nonneg _
  have hMN : (shellMax c k : Int) ≤ 2 ^ k := by
    rw [← natCast_two_pow]
    exact Int.ofNat_le.mpr (shellMax_le_pow c k)
  have hb := geom_bound
    (fun j => min ((2 : Int) ^ j * 2 ^ j) (4 * ((shellMax c k : Int) * (shellMax c k : Int))))
    (shellMax c k : Int) hM (fun j => Int.min_le_left _ _) (fun j => Int.min_le_right _ _) k
  have h1 : orderedEnergy c k
      ≤ sumTo (fun j => 2 ^ (k - j)
          * min ((2 : Int) ^ j * 2 ^ j) (4 * ((shellMax c k : Int) * (shellMax c k : Int))))
        (k + 1) := by
    unfold orderedEnergy
    exact sumTo_le_sumTo _ _ _ (fun j hj => blockEnergy_le_geom c k j (by omega))
  have h2 := hb.2 hMN
  have h3 := mul_self_nonneg (shellMax c k : Int)
  exact Int.le_trans h1 (by omega)

theorem shellMaxLittleO_imp_orderedEnergyLittleO (c : Nat → Bool) :
    ShellMaxLittleO c → OrderedEnergyLittleO c := by
  intro h m
  rcases h (8 * m) with ⟨K, hK⟩
  refine ⟨K, fun k hk => ?_⟩
  have h1 := hK k hk
  have h1' : 8 * ((m : Int) * (shellMax c k : Int)) ≤ 2 ^ k := by
    have := Int.ofNat_le.mpr h1
    push_cast at this
    rw [Int.mul_assoc] at this
    exact this
  have h2 := orderedEnergy_le c k
  have h3 : (m : Int) * orderedEnergy c k ≤ (m : Int) * (8 * ((shellMax c k : Int) * 2 ^ k)) :=
    Int.mul_le_mul_of_nonneg_left h2 (Int.natCast_nonneg m)
  have hN : (0 : Int) ≤ 2 ^ k := Int.le_of_lt (Int.pow_pos (by decide))
  have h4 : 8 * ((m : Int) * (shellMax c k : Int)) * 2 ^ k ≤ 2 ^ k * 2 ^ k :=
    Int.mul_le_mul_of_nonneg_right h1' hN
  have e : (m : Int) * (8 * ((shellMax c k : Int) * 2 ^ k))
      = 8 * ((m : Int) * (shellMax c k : Int)) * 2 ^ k := by grind
  rw [four_pow_eq]
  omega

/-! ## Control: the weakened hypotheses fail -/


theorem sumTo_halfstep (f : Nat → Int) (h : Nat) :
    ∀ u, (∀ r, r < u → f r = if h ≤ r then -1 else 1) →
      sumTo f u = if u ≤ h then (u : Int) else 2 * (h : Int) - u
  | 0, _ => by simp [sumTo]
  | u + 1, hf => by
      have ih := sumTo_halfstep f h u (fun r hr => hf r (Nat.lt_succ_of_lt hr))
      have hu := hf u (Nat.lt_succ_self u)
      simp only [sumTo]
      rw [ih, hu]
      omega

theorem S_shell (c : Nat → Bool) (k u : Nat) :
    S c (2 ^ k + u) = S c (2 ^ k) + shellPrefix c k u := by
  unfold S shellPrefix
  exact sumTo_add (z c) (2 ^ k) u

/-- False on the first half of every shell `[2^(i+1), 2^(i+2))`, true on the second half. -/
def halfShell (t : Nat) : Bool :=
  decide (∃ i, i < t ∧ (2 ^ (i + 1) + 2 ^ i ≤ t ∧ t < 2 ^ (i + 2)))

theorem halfShell_iff (t : Nat) :
    halfShell t = true ↔ ∃ i, i < t ∧ (2 ^ (i + 1) + 2 ^ i ≤ t ∧ t < 2 ^ (i + 2)) := by
  unfold halfShell
  exact decide_eq_true_iff

theorem two_pow_lt_imp (a b : Nat) (h : 2 ^ a < 2 ^ b) : a < b :=
  (Nat.pow_lt_pow_iff_right (by decide)).mp h

theorem two_pow_add_two (i : Nat) : 2 ^ (i + 2) = 4 * 2 ^ i := by
  have h : 2 ^ (i + 2) = 2 ^ (i + 1) * 2 := Nat.pow_succ 2 (i + 1)
  omega

theorem halfShell_shell (j r : Nat) (hr : r < 2 ^ (j + 1)) :
    halfShell (2 ^ (j + 1) + r) = decide (2 ^ j ≤ r) := by
  have hiff : halfShell (2 ^ (j + 1) + r) = true ↔ 2 ^ j ≤ r := by
    rw [halfShell_iff]
    constructor
    · rintro ⟨i, _, hlo, hhi⟩
      have hi2 := two_pow_add_two i
      have hj2 := two_pow_add_two j
      have hip := Nat.two_pow_pos i
      have hjp := Nat.two_pow_pos j
      have h1 : i + 1 < j + 2 := by
        apply two_pow_lt_imp
        omega
      have h2 : j + 1 < i + 2 := by
        apply two_pow_lt_imp
        omega
      have hij : i = j := by omega
      subst hij
      omega
    · intro h
      have hj2 := two_pow_add_two j
      refine ⟨j, ?_, ?_, ?_⟩
      · have := @Nat.lt_two_pow_self j
        omega
      · omega
      · omega
  cases hc : halfShell (2 ^ (j + 1) + r)
  · have : ¬ 2 ^ j ≤ r := fun h => by rw [hiff.mpr h] at hc; exact Bool.noConfusion hc
    simp [this]
  · have : 2 ^ j ≤ r := hiff.mp hc
    simp [this]

theorem z_halfShell_shell (j r : Nat) (hr : r < 2 ^ (j + 1)) :
    z halfShell (2 ^ (j + 1) + r) = if 2 ^ j ≤ r then -1 else 1 := by
  unfold z sign
  rw [halfShell_shell j r hr]
  by_cases h : 2 ^ j ≤ r <;> simp [h]

theorem shellPrefix_halfShell (j u : Nat) (hu : u ≤ 2 ^ (j + 1)) :
    shellPrefix halfShell (j + 1) u
      = if u ≤ 2 ^ j then (u : Int) else 2 * ((2 ^ j : Nat) : Int) - u := by
  unfold shellPrefix
  exact sumTo_halfstep _ (2 ^ j) u
    (fun r hr => z_halfShell_shell j r (Nat.lt_of_lt_of_le hr hu))

theorem shellPrefix_half (j : Nat) :
    shellPrefix halfShell (j + 1) (2 ^ j) = ((2 ^ j : Nat) : Int) := by
  have hp := Nat.two_pow_pos j
  rw [shellPrefix_halfShell j (2 ^ j) (by omega)]
  simp

theorem shellPrefix_full (j : Nat) :
    shellPrefix halfShell (j + 1) (2 ^ (j + 1)) = 0 := by
  rw [shellPrefix_halfShell j (2 ^ (j + 1)) (Nat.le_refl _)]
  have := Nat.two_pow_pos j
  have h : ¬ 2 ^ (j + 1) ≤ 2 ^ j := by omega
  simp only [h, ↓reduceIte]
  omega

theorem halfShell_zero : halfShell 0 = false := by
  cases hc : halfShell 0
  · rfl
  · obtain ⟨i, hi, _⟩ := (halfShell_iff 0).mp hc
    omega

theorem halfShell_one : halfShell 1 = false := by
  cases hc : halfShell 1
  · rfl
  · obtain ⟨i, _, hlo, _⟩ := (halfShell_iff 1).mp hc
    have := Nat.two_pow_pos i
    omega

theorem S_halfShell_two : S halfShell 2 = 2 := by
  simp [S, sumTo, z, sign, halfShell_zero, halfShell_one]

theorem S_halfShell_dyadic : ∀ j, S halfShell (2 ^ (j + 1)) = 2
  | 0 => S_halfShell_two
  | j + 1 => by
      have ih := S_halfShell_dyadic j
      have hs := S_shell halfShell (j + 1) (2 ^ (j + 1))
      rw [ih, shellPrefix_full] at hs
      have he : 2 ^ (j + 1 + 1) = 2 ^ (j + 1) + 2 ^ (j + 1) := by omega
      rw [he, hs]
      rfl

theorem blockEnergy_halfShell_top (j : Nat) :
    blockEnergy halfShell (j + 1) (j + 1) = 0 := by
  have hb : blockSum halfShell (j + 1) (j + 1) 0 = 0 := by
    have he : blockSum halfShell (j + 1) (j + 1) 0
        = shellPrefix halfShell (j + 1) (2 ^ (j + 1)) := by
      unfold blockSum shellPrefix
      simp only [Nat.zero_mul, Nat.add_zero]
    rw [he, shellPrefix_full]
  unfold blockEnergy
  rw [Nat.sub_self]
  simp [sumTo, hb]

theorem dyadicEndpoints_halfShell : DyadicEndpointsLittleO halfShell := by
  intro m
  refine ⟨2 * m + 1, fun k hk => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [S_halfShell_dyadic j]
  have h0 : (2 : Int).natAbs = 2 := rfl
  rw [h0]
  have h1 := @Nat.lt_two_pow_self (2 * m + 1)
  have h2 : 2 ^ (2 * m + 1) ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by decide) hk
  omega

theorem unpenalizedEnergy_halfShell : UnpenalizedEnergyToZero halfShell := by
  intro m
  refine ⟨1, fun k hk => ⟨k, Nat.le_refl k, ?_⟩⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [blockEnergy_halfShell_top j, Int.mul_zero]
  exact Int.mul_nonneg (Int.pow_nonneg (by decide)) (Int.pow_nonneg (by decide))

theorem not_densityHalf_halfShell : ¬ DensityHalf halfShell := by
  intro h
  obtain ⟨T0, hT0⟩ := h 4
  have hlt := @Nat.lt_two_pow_self T0
  have hpos := Nat.two_pow_pos T0
  have hb := hT0 (2 ^ (T0 + 1) + 2 ^ T0) (by omega)
  have hS := S_shell halfShell (T0 + 1) (2 ^ T0)
  rw [S_halfShell_dyadic T0, shellPrefix_half T0, signedSum_eq] at hS
  omega

theorem weakened_hypotheses_do_not_give_densityHalf :
    ∃ c : Nat → Bool,
      DyadicEndpointsLittleO c ∧ UnpenalizedEnergyToZero c ∧ ¬ DensityHalf c :=
  ⟨halfShell, dyadicEndpoints_halfShell, unpenalizedEnergy_halfShell, not_densityHalf_halfShell⟩

theorem dyadicEndpoints_bridge_fails :
    ¬ ∀ c : Nat → Bool, DyadicEndpointsLittleO c → DensityHalf c := fun h =>
  let ⟨c, hd, _, hn⟩ := weakened_hypotheses_do_not_give_densityHalf
  hn (h c hd)

theorem unpenalizedEnergy_bridge_fails :
    ¬ ∀ c : Nat → Bool, UnpenalizedEnergyToZero c → DensityHalf c := fun h =>
  let ⟨c, _, hu, hn⟩ := weakened_hypotheses_do_not_give_densityHalf
  hn (h c hu)

/-! ## The four forms are one target, for every sequence and for the center column -/

theorem densityHalf_iff_flexibleEnergyToZero (c : Nat → Bool) :
    DensityHalf c ↔ FlexibleEnergyToZero c :=
  (densityHalf_iff_shellMaxLittleO c).trans (shellMaxLittleO_iff_flexibleEnergyToZero c)

theorem shellMaxLittleO_iff_orderedEnergyLittleO (c : Nat → Bool) :
    ShellMaxLittleO c ↔ OrderedEnergyLittleO c :=
  ⟨shellMaxLittleO_imp_orderedEnergyLittleO c, fun h =>
    maxBlockEnergyLittleO_imp_shellMaxLittleO c
      (orderedEnergyLittleO_imp_maxBlockEnergyLittleO c h)⟩

theorem orderedEnergyLittleO_iff_maxBlockEnergyLittleO (c : Nat → Bool) :
    OrderedEnergyLittleO c ↔ MaxBlockEnergyLittleO c :=
  ⟨orderedEnergyLittleO_imp_maxBlockEnergyLittleO c, fun h =>
    shellMaxLittleO_imp_orderedEnergyLittleO c
      (maxBlockEnergyLittleO_imp_shellMaxLittleO c h)⟩

theorem densityHalf_iff_orderedEnergyLittleO (c : Nat → Bool) :
    DensityHalf c ↔ OrderedEnergyLittleO c :=
  (densityHalf_iff_shellMaxLittleO c).trans (shellMaxLittleO_iff_orderedEnergyLittleO c)

/-! ## The official `Problem2` -/

theorem blackCount_eq_ones (n : Nat) : blackCount n = ones center n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [blackCount, ones, List.range_succ, List.filter_append, List.length_append] at ih ⊢
    rw [ih]
    cases h : center n <;> simp [h]

theorem problem2_iff_densityHalf : Problem2 ↔ DensityHalf center := by
  constructor
  · intro h m
    by_cases hm : m = 0
    · exact ⟨0, fun T _ => by simp [hm]⟩
    · obtain ⟨N, hN⟩ := h m (Nat.pos_of_ne_zero hm)
      exact ⟨N, fun T hT => by simpa [blackCount_eq_ones] using hN T hT⟩
  · intro h k hk
    obtain ⟨N, hN⟩ := h k
    exact ⟨N, fun T hT => by simpa [blackCount_eq_ones] using hN T hT⟩

theorem problem2_iff_shellMaxLittleO : Problem2 ↔ ShellMaxLittleO center :=
  problem2_iff_densityHalf.trans (densityHalf_iff_shellMaxLittleO center)

theorem problem2_iff_flexibleEnergyToZero : Problem2 ↔ FlexibleEnergyToZero center :=
  problem2_iff_densityHalf.trans (densityHalf_iff_flexibleEnergyToZero center)

theorem problem2_iff_orderedEnergyLittleO : Problem2 ↔ OrderedEnergyLittleO center :=
  problem2_iff_densityHalf.trans (densityHalf_iff_orderedEnergyLittleO center)

theorem problem2_iff_maxBlockEnergyLittleO : Problem2 ↔ MaxBlockEnergyLittleO center :=
  (problem2_iff_orderedEnergyLittleO).trans (orderedEnergyLittleO_iff_maxBlockEnergyLittleO center)

/-! ## Antiperiodic Spin-Momentum Annihilation, Block-Energy Vanishing, and Diagonal Energy Bridges -/

/-- For every Boolean sequence `c : Nat → Bool` and `n : Nat`, `Rule30Prize.blackCountFor c n`
equals `Rule30P2Bridge.ones c n`. -/
theorem blackCountFor_eq_ones (c : Nat → Bool) : ∀ n : Nat, blackCountFor c n = ones c n
  | 0 => rfl
  | n + 1 => by
    rw [blackCountFor_succ, ones, blackCountFor_eq_ones c n]

/-- **Universal Equivalence of `HalfDensity` and `DensityHalf` (`halfDensity_iff_densityHalf`):**
for every sequence `c : Nat → Bool`, `Rule30Prize.HalfDensity c` holds iff
`Rule30P2Bridge.DensityHalf c` holds. -/
theorem halfDensity_iff_densityHalf (c : Nat → Bool) :
    HalfDensity c ↔ DensityHalf c := by
  constructor
  · intro h m
    by_cases hm : m = 0
    · subst hm; exact ⟨0, fun T _ => by simp⟩
    · obtain ⟨N, hN⟩ := h m (by omega)
      refine ⟨N, fun T hT => ?_⟩
      have h1 := hN T hT
      rwa [blackCountFor_eq_ones] at h1
  · intro h k _
    obtain ⟨T0, hT0⟩ := h k
    refine ⟨T0, fun n hn => ?_⟩
    have h1 := hT0 n hn
    rwa [← blackCountFor_eq_ones] at h1

/-- **All Five Energy Forms from Antiperiodicity (`energy_forms_of_antiperiodic`):** every
eventually `L`-anti-periodic sequence `c` (`0 < L`) satisfies `HalfDensity`, `DensityHalf`,
`ShellMaxLittleO`, `FlexibleEnergyToZero`, `OrderedEnergyLittleO`, and `MaxBlockEnergyLittleO`. -/
theorem energy_forms_of_antiperiodic {c : Nat → Bool} {L : Nat} (hL : 0 < L) (ha : EvAntiPer c L) :
    HalfDensity c ∧ DensityHalf c ∧ ShellMaxLittleO c ∧
      FlexibleEnergyToZero c ∧ OrderedEnergyLittleO c ∧ MaxBlockEnergyLittleO c := by
  have hhd : HalfDensity c := halfDensity_of_antiperiodic hL ha
  have hdh : DensityHalf c := (halfDensity_iff_densityHalf c).mp hhd
  have hsm : ShellMaxLittleO c := (densityHalf_iff_shellMaxLittleO c).mp hdh
  have hfe : FlexibleEnergyToZero c := (shellMaxLittleO_iff_flexibleEnergyToZero c).mp hsm
  have hoe : OrderedEnergyLittleO c := (shellMaxLittleO_iff_orderedEnergyLittleO c).mp hsm
  have hme : MaxBlockEnergyLittleO c := (orderedEnergyLittleO_iff_maxBlockEnergyLittleO c).mp hoe
  exact ⟨hhd, hdh, hsm, hfe, hoe, hme⟩

/-- Negating a bit negates its spin `sign (!b) = - sign b`. -/
theorem sign_not (b : Bool) : sign (!b) = - sign b := by
  cases b <;> rfl

/-- If `c (t + L) = ! c t` for all `t ≥ T`, then `z c (t + L) + z c t = 0`. -/
theorem z_add_antiperiodic {c : Nat → Bool} {L T t : Nat}
    (ha : ∀ s, T ≤ s → c (s + L) = ! c s) (ht : T ≤ t) :
    z c (t + L) + z c t = 0 := by
  simp only [z, ha t ht, sign_not]
  omega

/-- The sum of `f` plus the sum of `-f` over `[0, m)` is `0`. -/
theorem sumTo_add_neg (f : Nat → Int) : ∀ m : Nat, sumTo f m + sumTo (fun r => - f r) m = 0
  | 0 => rfl
  | m + 1 => by
    have ih := sumTo_add_neg f m
    simp only [sumTo]
    omega

/-- Over any full cycle of length `2 * L` starting at `t ≥ T`, the net spin momentum sums to `0`. -/
theorem sumTo_z_two_mul_eq_zero {c : Nat → Bool} {L T t : Nat}
    (ha : ∀ s, T ≤ s → c (s + L) = ! c s) (ht : T ≤ t) :
    sumTo (fun r => z c (t + r)) (2 * L) = 0 := by
  rw [show 2 * L = L + L by omega, sumTo_add]
  have hcongr : sumTo (fun r => z c (t + (L + r))) L = sumTo (fun r => - z c (t + r)) L := by
    apply sumTo_congr
    intro r _
    rw [show t + (L + r) = (t + r) + L by omega]
    have hz := z_add_antiperiodic ha (t := t + r) (by omega)
    omega
  rw [hcongr]
  exact sumTo_add_neg (fun r => z c (t + r)) L

/-- Over any multiple `q * (2 * L)` of the full period `2 * L` starting at `t ≥ T`, the net spin
momentum sums to `0`. -/
theorem sumTo_z_mul_two_mul_eq_zero {c : Nat → Bool} {L T t : Nat}
    (ha : ∀ s, T ≤ s → c (s + L) = ! c s) (ht : T ≤ t) :
    ∀ q : Nat, sumTo (fun r => z c (t + r)) (q * (2 * L)) = 0
  | 0 => by simp [sumTo]
  | q + 1 => by
    rw [Nat.succ_mul, sumTo_add, sumTo_z_mul_two_mul_eq_zero ha ht q, Int.zero_add]
    have hshift : (fun r => z c (t + (q * (2 * L) + r))) =
        (fun r => z c ((t + q * (2 * L)) + r)) := by
      funext r; congr 1; omega
    rw [hshift]
    exact sumTo_z_two_mul_eq_zero ha (by omega)

/-- **Remainder Reduction of `shellPrefix` (`shellPrefix_antiperiodic_mod`):** if `c` is
`L`-anti-periodic from `T ≤ 2 ^ k` onward, then for every `u : Nat`, `shellPrefix c k u` equals the
remainder sum of length `u % (2 * L)` starting at `2 ^ k + (u / (2 * L)) * (2 * L)`. -/
theorem shellPrefix_antiperiodic_mod {c : Nat → Bool} {L T k u : Nat}
    (ha : ∀ s, T ≤ s → c (s + L) = ! c s) (hTk : T ≤ 2 ^ k) :
    shellPrefix c k u =
      sumTo (fun r => z c (2 ^ k + (u / (2 * L)) * (2 * L) + r)) (u % (2 * L)) := by
  unfold shellPrefix
  have hdiv : (u / (2 * L)) * (2 * L) + u % (2 * L) = u := by
    rw [Nat.mul_comm (u / (2 * L)) (2 * L), Nat.div_add_mod]
  conv => lhs; rw [← hdiv]
  rw [sumTo_add, sumTo_z_mul_two_mul_eq_zero ha hTk (u / (2 * L)), Int.zero_add]
  apply sumTo_congr
  intro r _
  congr 1
  omega

/-- **Uniform `O(1)` Shell-Excursion Bound (`shellMax_le_two_mul_of_antiperiodic`):** if `c` is
`L`-anti-periodic (`0 < L`) from `T ≤ 2 ^ k` onward, then `shellMax c k ≤ 2 * L` (a constant bound
independent of the shell index `k`). -/
theorem shellMax_le_two_mul_of_antiperiodic {c : Nat → Bool} {L T k : Nat}
    (hL : 0 < L) (ha : ∀ s, T ≤ s → c (s + L) = ! c s) (hTk : T ≤ 2 ^ k) :
    shellMax c k ≤ 2 * L := by
  unfold shellMax
  apply maxTo_le
  intro u _
  rw [shellPrefix_antiperiodic_mod ha hTk]
  have h1 : (sumTo (fun r => z c (2 ^ k + (u / (2 * L)) * (2 * L) + r)) (u % (2 * L))).natAbs ≤
      u % (2 * L) :=
    natAbs_sumTo_le _ _ (fun r => natAbs_z_le c _)
  have h2 : u % (2 * L) < 2 * L := Nat.mod_lt u (by omega)
  omega

/-- **Exact Block-Momentum Annihilation (`blockSum_eq_zero_of_antiperiodic`):** if `c` is
`2 ^ j₀`-anti-periodic from `T ≤ 2 ^ k` onward, then for every scale `j ≥ j₀ + 1` and block `a`,
`blockSum c k j a = 0`. -/
theorem blockSum_eq_zero_of_antiperiodic {c : Nat → Bool} {j₀ T k j a : Nat}
    (ha : ∀ s, T ≤ s → c (s + 2 ^ j₀) = ! c s) (hTk : T ≤ 2 ^ k) (hj : j₀ + 1 ≤ j) :
    blockSum c k j a = 0 := by
  unfold blockSum
  have hpow : 2 ^ j = 2 ^ (j - (j₀ + 1)) * (2 * 2 ^ j₀) := by
    rw [show 2 * 2 ^ j₀ = 2 ^ (j₀ + 1) by rw [Nat.pow_succ, Nat.mul_comm], ← Nat.pow_add,
      show j - (j₀ + 1) + (j₀ + 1) = j by omega]
  rw [hpow]
  exact sumTo_z_mul_two_mul_eq_zero ha (by omega) (2 ^ (j - (j₀ + 1)))

/-- **Exact Lagrangian Block-Energy Annihilation (`blockEnergy_eq_zero_of_antiperiodic`):** if `c`
is `2 ^ j₀`-anti-periodic from `T ≤ 2 ^ k` onward, then for every scale `j ≥ j₀ + 1`,
`blockEnergy c k j = 0`. -/
theorem blockEnergy_eq_zero_of_antiperiodic {c : Nat → Bool} {j₀ T k j : Nat}
    (ha : ∀ s, T ≤ s → c (s + 2 ^ j₀) = ! c s) (hTk : T ≤ 2 ^ k) (hj : j₀ + 1 ≤ j) :
    blockEnergy c k j = 0 := by
  unfold blockEnergy
  have h0 : sumTo (fun a => blockSum c k j a * blockSum c k j a) (2 ^ (k - j)) =
      sumTo (fun _ => 0) (2 ^ (k - j)) := by
    apply sumTo_congr
    intro a _
    rw [blockSum_eq_zero_of_antiperiodic ha hTk hj, Int.mul_zero]
  rw [h0]
  induction (2 ^ (k - j)) with
  | zero => rfl
  | succ n ih => simp [sumTo, ih]

/-- **Scale Truncation of Ordered Energy (`orderedEnergy_eq_trunc_of_antiperiodic`):** if `c` is
`2 ^ j₀`-anti-periodic from `T ≤ 2 ^ k` onward (`j₀ ≤ k`), then the multi-scale ordered energy
`orderedEnergy c k` equals the partial sum over only the bottom `j₀ + 1` scales `0 ≤ j ≤ j₀`. -/
theorem orderedEnergy_eq_trunc_of_antiperiodic {c : Nat → Bool} {j₀ T k : Nat}
    (ha : ∀ s, T ≤ s → c (s + 2 ^ j₀) = ! c s) (hTk : T ≤ 2 ^ k) (hjk : j₀ ≤ k) :
    orderedEnergy c k = sumTo (fun j => blockEnergy c k j) (j₀ + 1) := by
  unfold orderedEnergy
  have haux : ∀ d : Nat, sumTo (fun j => blockEnergy c k j) ((j₀ + 1) + d) =
      sumTo (fun j => blockEnergy c k j) (j₀ + 1) := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
      rw [Nat.add_succ, sumTo, ih, blockEnergy_eq_zero_of_antiperiodic ha hTk (by omega),
        Int.add_zero]
  rw [show k + 1 = (j₀ + 1) + (k - j₀) by omega]
  exact haux (k - j₀)

/-- **Infinitely Many Left Diagonals Satisfy All Five Energy Forms (`D_infinitely_many_energy_forms`):**
for every `N : Nat`, there exist `j > N` and `k : Nat` such that `D j` is `2 ^ k`-anti-periodic and
satisfies `HalfDensity`, `DensityHalf`, `ShellMaxLittleO`, `FlexibleEnergyToZero`,
`OrderedEnergyLittleO`, and `MaxBlockEnergyLittleO`. -/
theorem D_infinitely_many_energy_forms (N : Nat) :
    ∃ j k : Nat, N < j ∧ EvAntiPer (D j) (2 ^ k) ∧ ¬ EvPer (D j) (2 ^ k) ∧
      HalfDensity (D j) ∧ DensityHalf (D j) ∧ ShellMaxLittleO (D j) ∧
      FlexibleEnergyToZero (D j) ∧ OrderedEnergyLittleO (D j) ∧ MaxBlockEnergyLittleO (D j) := by
  obtain ⟨j, hj, k, ha, hnp, _⟩ := D_infinitely_many_halfDensity N
  exact ⟨j, k, hj, ha, hnp, energy_forms_of_antiperiodic (Nat.two_pow_pos k) ha⟩

/-- **Infinitely Many Right Diagonals have Exact Zero High-Scale Block Energy & Satisfy All Five
Energy Forms (`R_infinitely_many_energy_forms`):** for every `k₀ : Nat`, there exists a right
diagonal `R m` (`k₀ < m ≤ 2 ^ (k₀ + 1) - 1`) that is `2 ^ k₀`-anti-periodic from `t = 0`, has
`blockEnergy (R m) k j = 0` for all `k` and `j ≥ k₀ + 1`, `shellMax (R m) k ≤ 2 * 2 ^ k₀` for all `k`,
and satisfies all five Problem 2 energy forms. -/
theorem R_infinitely_many_energy_forms (k₀ : Nat) :
    ∃ m : Nat, k₀ < m ∧ m ≤ 2 ^ (k₀ + 1) - 1 ∧
      (∀ t : Nat, R m (t + 2 ^ k₀) = ! R m t) ∧
      (∀ k j : Nat, k₀ + 1 ≤ j → blockEnergy (R m) k j = 0) ∧
      (∀ k : Nat, shellMax (R m) k ≤ 2 * 2 ^ k₀) ∧
      HalfDensity (R m) ∧ DensityHalf (R m) ∧ ShellMaxLittleO (R m) ∧
      FlexibleEnergyToZero (R m) ∧ OrderedEnergyLittleO (R m) ∧ MaxBlockEnergyLittleO (R m) := by
  obtain ⟨m, hm1, hm2, ha0, _, _⟩ := R_infinitely_many_halfDensity k₀
  have hea : EvAntiPer (R m) (2 ^ k₀) := ⟨0, fun t _ => ha0 t⟩
  refine ⟨m, hm1, hm2, ha0, fun k j hj => ?_, fun k => ?_,
    energy_forms_of_antiperiodic (Nat.two_pow_pos k₀) hea⟩
  · exact blockEnergy_eq_zero_of_antiperiodic (T := 0) (fun s _ => ha0 s) (Nat.zero_le _) hj
  · exact shellMax_le_two_mul_of_antiperiodic (T := 0) (Nat.two_pow_pos k₀) (fun s _ => ha0 s) (Nat.zero_le _)

open Rule30Jen Rule30Prize Rule30Diagonals Rule30LeftReset Rule30LeftUnbounded Rule30LeftAntiPeriod

/-! ## 1. Multiplicative Spin-Shield Negotiation Identities -/

/-- Local 3-cell Rule 30 collision operator `p ^^ (q || r)`. -/
def rule30 (p q r : Bool) : Bool := p ^^ (q || r)

/-- **Multiplicative Character of XOR (`sign_xor_eq_mul`):** `sign (a ^^ b) = sign a * sign b` for all
`a, b : Bool`. -/
theorem sign_xor_eq_mul (a b : Bool) :
    sign (a ^^ b) = sign a * sign b := by
  cases a <;> cases b <;> rfl

/-- **Multiplicative Spin-Shield Law for Rule 30 (`sign_rule30_eq_mul_shield`):** the output spin
`sign (rule30 p q r)` is the product of the left input spin `sign p` and the right-coalition shield
spin `sign (q || r)`. -/
theorem sign_rule30_eq_mul_shield (p q r : Bool) :
    sign (rule30 p q r) = sign p * sign (q || r) := by
  cases p <;> cases q <;> cases r <;> rfl

/-- **Left-Output Spin Coupling Identity (`sign_left_mul_rule30_eq_shield`):** the product of the left
input spin `sign p` and the output spin `sign (rule30 p q r)` equals the right-coalition shield spin
`sign (q || r)`. -/
theorem sign_left_mul_rule30_eq_shield (p q r : Bool) :
    sign p * sign (rule30 p q r) = sign (q || r) := by
  cases p <;> cases q <;> cases r <;> rfl

/-! ## 2. Universal Cross-Correlation and Shield-Balance Orthogonality -/

/-- Cumulative `T`-step spin cross-correlation `crossCorr f g T = sumTo (fun t => z f t * z g t) T`
measuring the negotiation alignment between two Boolean trajectories `f` and `g`. -/
def crossCorr (f g : Nat → Bool) (T : Nat) : Int :=
  sumTo (fun t => z f t * z g t) T

/-- **Cross-Correlation vs. XOR Signed Sum (`crossCorr_eq_S_xor`):** for any two Boolean sequences
`f, g : Nat → Bool` and horizon `T`, `crossCorr f g T` equals the signed sum `S (fun t => f t ^^ g t) T`,
which equals `T - 2 * ones (fun t => f t ^^ g t) T`. -/
theorem crossCorr_eq_S_xor (f g : Nat → Bool) (T : Nat) :
    crossCorr f g T = S (fun t => f t ^^ g t) T ∧
    crossCorr f g T = (T : Int) - 2 * (ones (fun t => f t ^^ g t) T : Int) := by
  have h1 : crossCorr f g T = S (fun t => f t ^^ g t) T := by
    unfold crossCorr S
    refine sumTo_congr _ _ T (fun t _ => ?_)
    dsimp only [z]
    exact (sign_xor_eq_mul (f t) (g t)).symm
  exact ⟨h1, h1.trans (signedSum_eq (fun t => f t ^^ g t) T)⟩

/-- **Universal Negotiation Conservation Law (`crossCorr_rule30_eq_S_shield`):** for any three
sequences `p, q, r : Nat → Bool` and horizon `T`, the cross-correlation between the left input `p`
and the Rule 30 output `fun t => rule30 (p t) (q t) (r t)` equals the signed sum `S (fun t => q t || r t) T`
of the right coalition shield, which is `T - 2 * ones (fun t => q t || r t) T`. -/
theorem crossCorr_rule30_eq_S_shield (p q r : Nat → Bool) (T : Nat) :
    crossCorr p (fun t => rule30 (p t) (q t) (r t)) T =
      S (fun t => q t || r t) T ∧
    crossCorr p (fun t => rule30 (p t) (q t) (r t)) T =
      (T : Int) - 2 * (ones (fun t => q t || r t) T : Int) := by
  have h1 : crossCorr p (fun t => rule30 (p t) (q t) (r t)) T =
      S (fun t => q t || r t) T := by
    unfold crossCorr S
    refine sumTo_congr _ _ T (fun t _ => ?_)
    dsimp only [z]
    exact sign_left_mul_rule30_eq_shield (p t) (q t) (r t)
  exact ⟨h1, h1.trans (signedSum_eq (fun t => q t || r t) T)⟩

/-- **True-Balance Orthogonality Criterion (`shield_balanced_iff_crossCorr_zero`):** over any finite
horizon `T`, the right coalition shield `fun t => q t || r t` achieves exact `1/2` balance
(`2 * ones (fun t => q t || r t) T = T`, or `S = 0`) if and only if the Rule 30 output is
statistically orthogonal to its left parent `p` (`crossCorr p (fun t => rule30 (p t) (q t) (r t)) T = 0`). -/
theorem shield_balanced_iff_crossCorr_zero (p q r : Nat → Bool) (T : Nat) :
    2 * ones (fun t => q t || r t) T = T ↔
      crossCorr p (fun t => rule30 (p t) (q t) (r t)) T = 0 := by
  have h := (crossCorr_rule30_eq_S_shield p q r T).2
  omega

/-! ## 3. Global Spacetime, Center-Column, Diagonal, and Energy-Form Transfer Laws -/

/-- **Spacetime Column Cross-Correlation Law (`cell_crossCorr_eq_shield_S`):** at every spatial column
`x : Int` and time horizon `T : Nat`, the cross-correlation between the left parent column
`fun t => cell t (x - 1)` and `fun t => cell (t + 1) x` equals `S (fun t => cell t x || cell t (x + 1)) T`
and `T - 2 * ones (fun t => cell t x || cell t (x + 1)) T`. -/
theorem cell_crossCorr_eq_shield_S (x : Int) (T : Nat) :
    crossCorr (fun t => cell t (x - 1)) (fun t => cell (t + 1) x) T =
      S (fun t => cell t x || cell t (x + 1)) T ∧
    crossCorr (fun t => cell t (x - 1)) (fun t => cell (t + 1) x) T =
      (T : Int) - 2 * (ones (fun t => cell t x || cell t (x + 1)) T : Int) := by
  have hcell : (fun t => cell (t + 1) x) =
      (fun t => rule30 (cell t (x - 1)) (cell t x) (cell t (x + 1))) := rfl
  rw [hcell]
  exact crossCorr_rule30_eq_S_shield
    (fun t => cell t (x - 1)) (fun t => cell t x) (fun t => cell t (x + 1)) T

/-- **Center-Column Negotiation Balance Law (`center_crossCorr_eq_right_shield_S`):** for every
horizon `T : Nat`, the cross-correlation between `fun t => cell t (-1)` and the shifted center column
`fun t => center (t + 1)` equals `S (fun t => center t || cell t 1) T` and
`T - 2 * ones (fun t => center t || cell t 1) T`. -/
theorem center_crossCorr_eq_right_shield_S (T : Nat) :
    crossCorr (fun t => cell t (-1)) (fun t => center (t + 1)) T =
      S (fun t => center t || cell t 1) T ∧
    crossCorr (fun t => cell t (-1)) (fun t => center (t + 1)) T =
      (T : Int) - 2 * (ones (fun t => center t || cell t 1) T : Int) := by
  simpa [center] using cell_crossCorr_eq_shield_S 0 T

/-- **Left-Diagonal Cross-Correlation Law (`D_crossCorr_eq_shield_S`):** for every diagonal index
`j : Nat` and horizon `T : Nat`, the cross-correlation between `D j` and `fun t => D (j + 2) (t + 1)`
equals `S (fun t => D (j + 1) t || D (j + 2) t) T` and
`T - 2 * ones (fun t => D (j + 1) t || D (j + 2) t) T`. -/
theorem D_crossCorr_eq_shield_S (j T : Nat) :
    crossCorr (D j) (fun t => D (j + 2) (t + 1)) T =
      S (fun t => D (j + 1) t || D (j + 2) t) T ∧
    crossCorr (D j) (fun t => D (j + 2) (t + 1)) T =
      (T : Int) - 2 * (ones (fun t => D (j + 1) t || D (j + 2) t) T : Int) := by
  have hD : ∀ t, (D j t ^^ D (j + 2) (t + 1)) = (D (j + 1) t || D (j + 2) t) := by
    intro t
    have hstep := D_step j t
    revert hstep
    cases D j t <;> cases D (j + 1) t <;> cases D (j + 2) t <;> cases D (j + 2) (t + 1) <;> decide
  have hfun : (fun t => D j t ^^ D (j + 2) (t + 1)) = (fun t => D (j + 1) t || D (j + 2) t) :=
    funext hD
  have h := crossCorr_eq_S_xor (D j) (fun t => D (j + 2) (t + 1)) T
  rw [hfun] at h
  exact h

/-- **Bidirectional Parity-Balance Transfer (`rule30_antiperiodic_iff_shield_periodic_of_left_antiperiodic`):**
if the left channel `p` is `L`-antiperiodic from `T₀` on (`∀ t ≥ T₀, p (t + L) = !p t`), then the
negotiated output `fun t => rule30 (p t) (q t) (r t)` is `L`-antiperiodic from `T₀` on if and only if
the right coalition shield `fun t => q t || r t` is `L`-periodic from `T₀` on. -/
theorem rule30_antiperiodic_iff_shield_periodic_of_left_antiperiodic
    {p q r : Nat → Bool} {T₀ L : Nat} (hp : ∀ t, T₀ ≤ t → p (t + L) = !p t) :
    (∀ t, T₀ ≤ t → rule30 (p (t + L)) (q (t + L)) (r (t + L)) = !rule30 (p t) (q t) (r t)) ↔
      (∀ t, T₀ ≤ t → (q (t + L) || r (t + L)) = (q t || r t)) := by
  constructor
  · intro hout t ht
    have hpt := hp t ht
    have hot := hout t ht
    unfold rule30 at hot
    rw [hpt] at hot
    revert hot
    cases p t <;> cases (q (t + L) || r (t + L)) <;> cases (q t || r t) <;> decide
  · intro hsh t ht
    have hpt := hp t ht
    have hsht := hsh t ht
    unfold rule30
    rw [hpt, hsht]
    cases p t <;> cases (q t || r t) <;> rfl

/-- **Dual Parity-Balance Transfer (`rule30_antiperiodic_iff_shield_antiperiodic_of_left_periodic`):**
if the left channel `p` is `L`-periodic from `T₀` on (`∀ t ≥ T₀, p (t + L) = p t`), then the
negotiated output `fun t => rule30 (p t) (q t) (r t)` is `L`-antiperiodic from `T₀` on if and only if
the right coalition shield `fun t => q t || r t` is `L`-antiperiodic from `T₀` on. -/
theorem rule30_antiperiodic_iff_shield_antiperiodic_of_left_periodic
    {p q r : Nat → Bool} {T₀ L : Nat} (hp : ∀ t, T₀ ≤ t → p (t + L) = p t) :
    (∀ t, T₀ ≤ t → rule30 (p (t + L)) (q (t + L)) (r (t + L)) = !rule30 (p t) (q t) (r t)) ↔
      (∀ t, T₀ ≤ t → (q (t + L) || r (t + L)) = !(q t || r t)) := by
  constructor
  · intro hout t ht
    have hpt := hp t ht
    have hot := hout t ht
    unfold rule30 at hot
    rw [hpt] at hot
    revert hot
    cases p t <;> cases (q (t + L) || r (t + L)) <;> cases (q t || r t) <;> decide
  · intro hsh t ht
    have hpt := hp t ht
    have hsht := hsh t ht
    unfold rule30
    rw [hpt, hsht]
    cases p t <;> cases (q t || r t) <;> rfl

/-- **All-Energy-Forms Transfer under Shapley Shield Periodicity (`energy_forms_of_left_antiperiodic_of_shield_periodic`):**
for any `L > 0`, if the left channel `p` is `L`-antiperiodic from `T₀` on and the right coalition
shield `fun t => q t || r t` is `L`-periodic from `T₀` on, then the negotiated Rule 30 output
`out := fun t => rule30 (p t) (q t) (r t)` satisfies all six Problem 2 balance and energy conditions:
`HalfDensity`, `DensityHalf`, `ShellMaxLittleO`, `FlexibleEnergyToZero`, `OrderedEnergyLittleO`, and
`MaxBlockEnergyLittleO`. -/
theorem energy_forms_of_left_antiperiodic_of_shield_periodic
    {p q r : Nat → Bool} {T₀ L : Nat} (hL : 0 < L)
    (hp : ∀ t, T₀ ≤ t → p (t + L) = !p t)
    (hsh : ∀ t, T₀ ≤ t → (q (t + L) || r (t + L)) = (q t || r t)) :
    HalfDensity (fun t => rule30 (p t) (q t) (r t)) ∧
      DensityHalf (fun t => rule30 (p t) (q t) (r t)) ∧
      ShellMaxLittleO (fun t => rule30 (p t) (q t) (r t)) ∧
      FlexibleEnergyToZero (fun t => rule30 (p t) (q t) (r t)) ∧
      OrderedEnergyLittleO (fun t => rule30 (p t) (q t) (r t)) ∧
      MaxBlockEnergyLittleO (fun t => rule30 (p t) (q t) (r t)) := by
  have hout := (rule30_antiperiodic_iff_shield_periodic_of_left_antiperiodic hp).mpr hsh
  exact energy_forms_of_antiperiodic hL ⟨T₀, hout⟩

/-! ## 4. Negation Invariance of Energy Forms, Stroboscopic Spin-Shield Negotiation, and Odd-Stride Diagonal Energy Hierarchies -/

/-- **Pointwise Negation Flips the Signed Sum (`S_not_eq_neg`):** for every sequence `c : Nat → Bool`
and horizon `T : Nat`, complementing `c` negates its signed sum:
`S (fun t => !c t) T = - S c T`. -/
theorem S_not_eq_neg (c : Nat → Bool) :
    ∀ T : Nat, S (fun t => !c t) T = - S c T
  | 0 => rfl
  | T + 1 => by
    unfold S
    rw [sumTo_succ, sumTo_succ]
    change S (fun t => !c t) T + z (fun t => !c t) T = - (S c T + z c T)
    rw [S_not_eq_neg c T]
    dsimp only [z]
    rw [sign_not]
    omega

/-- **Pointwise Negation Flips `shellPrefix` (`shellPrefix_not_eq_neg`):** for every sequence
`c : Nat → Bool`, shell index `k : Nat`, and offset `u : Nat`,
`shellPrefix (fun t => !c t) k u = - shellPrefix c k u`. -/
theorem shellPrefix_not_eq_neg (c : Nat → Bool) (k u : Nat) :
    shellPrefix (fun t => !c t) k u = - shellPrefix c k u := by
  rw [shellPrefix_eq, shellPrefix_eq, S_not_eq_neg, S_not_eq_neg]
  omega

/-- **Exact Invariance of `shellMax` Under Pointwise Negation (`shellMax_not_eq`):** for every
sequence `c : Nat → Bool` and shell `k : Nat`,
`shellMax (fun t => !c t) k = shellMax c k`. -/
theorem shellMax_not_eq (c : Nat → Bool) (k : Nat) :
    shellMax (fun t => !c t) k = shellMax c k := by
  unfold shellMax
  have hfun : (fun u => (shellPrefix (fun t => !c t) k u).natAbs) =
      (fun u => (shellPrefix c k u).natAbs) := by
    funext u
    rw [shellPrefix_not_eq_neg, Int.natAbs_neg]
  rw [hfun]

/-- **Pointwise Negation Flips `blockSum` (`blockSum_not_eq_neg`):** for every sequence
`c : Nat → Bool` and indices `k, j, a : Nat`,
`blockSum (fun t => !c t) k j a = - blockSum c k j a`. -/
theorem blockSum_not_eq_neg (c : Nat → Bool) (k j a : Nat) :
    blockSum (fun t => !c t) k j a = - blockSum c k j a := by
  have h1 := shellPrefix_succ_block (fun t => !c t) k j a
  have h2 := shellPrefix_succ_block c k j a
  rw [shellPrefix_not_eq_neg, shellPrefix_not_eq_neg] at h1
  omega

/-- **Exact Invariance of `blockEnergy` Under Pointwise Negation (`blockEnergy_not_eq`):** for every
sequence `c : Nat → Bool` and scales `k, j : Nat`,
`blockEnergy (fun t => !c t) k j = blockEnergy c k j`. -/
theorem blockEnergy_not_eq (c : Nat → Bool) (k j : Nat) :
    blockEnergy (fun t => !c t) k j = blockEnergy c k j := by
  unfold blockEnergy
  refine sumTo_congr _ _ (2 ^ (k - j)) (fun a _ => ?_)
  rw [blockSum_not_eq_neg]
  exact Int.neg_mul_neg (blockSum c k j a) (blockSum c k j a)

/-- **Exact Invariance of `orderedEnergy` Under Pointwise Negation (`orderedEnergy_not_eq`):** for
every sequence `c : Nat → Bool` and scale `k : Nat`,
`orderedEnergy (fun t => !c t) k = orderedEnergy c k`. -/
theorem orderedEnergy_not_eq (c : Nat → Bool) (k : Nat) :
    orderedEnergy (fun t => !c t) k = orderedEnergy c k := by
  unfold orderedEnergy
  refine sumTo_congr _ _ (k + 1) (fun j _ => ?_)
  rw [blockEnergy_not_eq]

/-- **Equivalence of All Problem 2 Energy Forms Under Pointwise Negation (`energy_forms_not_iff`):**
for every sequence `c : Nat → Bool`, complementing `c` preserves `DensityHalf`, `ShellMaxLittleO`,
`FlexibleEnergyToZero`, `OrderedEnergyLittleO`, and `MaxBlockEnergyLittleO`. -/
theorem energy_forms_not_iff (c : Nat → Bool) :
    (DensityHalf (fun t => !c t) ↔ DensityHalf c) ∧
    (ShellMaxLittleO (fun t => !c t) ↔ ShellMaxLittleO c) ∧
    (FlexibleEnergyToZero (fun t => !c t) ↔ FlexibleEnergyToZero c) ∧
    (OrderedEnergyLittleO (fun t => !c t) ↔ OrderedEnergyLittleO c) ∧
    (MaxBlockEnergyLittleO (fun t => !c t) ↔ MaxBlockEnergyLittleO c) := by
  have hd : DensityHalf (fun t => !c t) ↔ DensityHalf c := by
    rw [← halfDensity_iff_densityHalf, ← halfDensity_iff_densityHalf]
    exact halfDensity_not_iff c
  have hs : ShellMaxLittleO (fun t => !c t) ↔ ShellMaxLittleO c := by
    rw [← densityHalf_iff_shellMaxLittleO, ← densityHalf_iff_shellMaxLittleO]
    exact hd
  have hf : FlexibleEnergyToZero (fun t => !c t) ↔ FlexibleEnergyToZero c := by
    rw [← densityHalf_iff_flexibleEnergyToZero, ← densityHalf_iff_flexibleEnergyToZero]
    exact hd
  have ho : OrderedEnergyLittleO (fun t => !c t) ↔ OrderedEnergyLittleO c := by
    rw [← densityHalf_iff_orderedEnergyLittleO, ← densityHalf_iff_orderedEnergyLittleO]
    exact hd
  have hm : MaxBlockEnergyLittleO (fun t => !c t) ↔ MaxBlockEnergyLittleO c := by
    rw [← orderedEnergyLittleO_iff_maxBlockEnergyLittleO, ← orderedEnergyLittleO_iff_maxBlockEnergyLittleO]
    exact ho
  exact ⟨hd, hs, hf, ho, hm⟩

/-- **Arithmetic-Progression Subsampling Commutes with `rule30` (`subseq_rule30`):** for any three
sequences `p, q, r : Nat → Bool`, stride `d : Nat`, and phase `r₀ : Nat`,
`subseq (fun t => rule30 (p t) (q t) (r t)) d r₀ = fun k => rule30 (subseq p d r₀ k) (subseq q d r₀ k) (subseq r d r₀ k)`. -/
theorem subseq_rule30 (p q r : Nat → Bool) (d r₀ : Nat) :
    subseq (fun t => rule30 (p t) (q t) (r t)) d r₀ =
      fun k => rule30 (subseq p d r₀ k) (subseq q d r₀ k) (subseq r d r₀ k) := rfl

/-- **Stroboscopic Negotiation Conservation Law Along Arithmetic Progressions (`crossCorr_subseq_rule30_eq_S_shield`):**
for any sequences `p, q, r : Nat → Bool`, stride `d : Nat`, phase `r₀ : Nat`, and horizon `T : Nat`,
the cross-correlation between `subseq p d r₀` and `subseq (fun t => rule30 (p t) (q t) (r t)) d r₀`
equals the signed sum `S (subseq (fun t => q t || r t) d r₀) T` and
`T - 2 * ones (subseq (fun t => q t || r t) d r₀) T`. -/
theorem crossCorr_subseq_rule30_eq_S_shield (p q r : Nat → Bool) (d r₀ T : Nat) :
    crossCorr (subseq p d r₀) (subseq (fun t => rule30 (p t) (q t) (r t)) d r₀) T =
      S (subseq (fun t => q t || r t) d r₀) T ∧
    crossCorr (subseq p d r₀) (subseq (fun t => rule30 (p t) (q t) (r t)) d r₀) T =
      (T : Int) - 2 * (ones (subseq (fun t => q t || r t) d r₀) T : Int) :=
  crossCorr_rule30_eq_S_shield (subseq p d r₀) (subseq q d r₀) (subseq r d r₀) T

/-- **Stroboscopic Shield-Balance Orthogonality Criterion (`shield_subseq_balanced_iff_crossCorr_zero`):**
over any horizon `T : Nat`, the subsampled right coalition shield `subseq (fun t => q t || r t) d r₀`
achieves exact `1/2` balance (`2 * ones (subseq (fun t => q t || r t) d r₀) T = T`) if and only if
`crossCorr (subseq p d r₀) (subseq (fun t => rule30 (p t) (q t) (r t)) d r₀) T = 0`. -/
theorem shield_subseq_balanced_iff_crossCorr_zero (p q r : Nat → Bool) (d r₀ T : Nat) :
    2 * ones (subseq (fun t => q t || r t) d r₀) T = T ↔
      crossCorr (subseq p d r₀) (subseq (fun t => rule30 (p t) (q t) (r t)) d r₀) T = 0 :=
  shield_balanced_iff_crossCorr_zero (subseq p d r₀) (subseq q d r₀) (subseq r d r₀) T

/-- **Stroboscopic Spacetime Column Cross-Correlation Law (`cell_subseq_crossCorr_eq_shield_S`):**
at every column `x : Int`, stride `d : Nat`, phase `r₀ : Nat`, and horizon `T : Nat`, the
cross-correlation between `subseq (fun t => cell t (x - 1)) d r₀` and `subseq (fun t => cell (t + 1) x) d r₀`
equals `S (subseq (fun t => cell t x || cell t (x + 1)) d r₀) T` and
`T - 2 * ones (subseq (fun t => cell t x || cell t (x + 1)) d r₀) T`. -/
theorem cell_subseq_crossCorr_eq_shield_S (x : Int) (d r₀ T : Nat) :
    crossCorr (subseq (fun t => cell t (x - 1)) d r₀) (subseq (fun t => cell (t + 1) x) d r₀) T =
      S (subseq (fun t => cell t x || cell t (x + 1)) d r₀) T ∧
    crossCorr (subseq (fun t => cell t (x - 1)) d r₀) (subseq (fun t => cell (t + 1) x) d r₀) T =
      (T : Int) - 2 * (ones (subseq (fun t => cell t x || cell t (x + 1)) d r₀) T : Int) :=
  crossCorr_subseq_rule30_eq_S_shield
    (fun t => cell t (x - 1)) (fun t => cell t x) (fun t => cell t (x + 1)) d r₀ T

/-- **Stroboscopic Center-Column Cross-Correlation Law (`center_subseq_crossCorr_eq_right_shield_S`):**
for every stride `d : Nat`, phase `r₀ : Nat`, and horizon `T : Nat`, the cross-correlation between
`subseq (fun t => cell t (-1)) d r₀` and `subseq (fun t => center (t + 1)) d r₀` equals
`S (subseq (fun t => center t || cell t 1) d r₀) T` and
`T - 2 * ones (subseq (fun t => center t || cell t 1) d r₀) T`. -/
theorem center_subseq_crossCorr_eq_right_shield_S (d r₀ T : Nat) :
    crossCorr (subseq (fun t => cell t (-1)) d r₀) (subseq (fun t => center (t + 1)) d r₀) T =
      S (subseq (fun t => center t || cell t 1) d r₀) T ∧
    crossCorr (subseq (fun t => cell t (-1)) d r₀) (subseq (fun t => center (t + 1)) d r₀) T =
      (T : Int) - 2 * (ones (subseq (fun t => center t || cell t 1) d r₀) T : Int) := by
  simpa [center] using cell_subseq_crossCorr_eq_shield_S 0 d r₀ T

/-- **Stroboscopic Left-Diagonal Cross-Correlation Law (`D_subseq_crossCorr_eq_shield_S`):**
for every diagonal index `j : Nat`, stride `d : Nat`, phase `r₀ : Nat`, and horizon `T : Nat`,
the cross-correlation between `subseq (D j) d r₀` and `subseq (fun t => D (j + 2) (t + 1)) d r₀`
equals `S (subseq (fun t => D (j + 1) t || D (j + 2) t) d r₀) T` and
`T - 2 * ones (subseq (fun t => D (j + 1) t || D (j + 2) t) d r₀) T`. -/
theorem D_subseq_crossCorr_eq_shield_S (j d r₀ T : Nat) :
    crossCorr (subseq (D j) d r₀) (subseq (fun t => D (j + 2) (t + 1)) d r₀) T =
      S (subseq (fun t => D (j + 1) t || D (j + 2) t) d r₀) T ∧
    crossCorr (subseq (D j) d r₀) (subseq (fun t => D (j + 2) (t + 1)) d r₀) T =
      (T : Int) - 2 * (ones (subseq (fun t => D (j + 1) t || D (j + 2) t) d r₀) T : Int) := by
  have hD : ∀ k, (subseq (D j) d r₀ k ^^ subseq (fun t => D (j + 2) (t + 1)) d r₀ k) =
      subseq (fun t => D (j + 1) t || D (j + 2) t) d r₀ k := by
    intro k
    dsimp only [subseq]
    have hstep := D_step j (r₀ + k * d)
    revert hstep
    cases D j (r₀ + k * d) <;> cases D (j + 1) (r₀ + k * d) <;>
      cases D (j + 2) (r₀ + k * d) <;> cases D (j + 2) (r₀ + k * d + 1) <;> decide
  have hfun : (fun k => subseq (D j) d r₀ k ^^ subseq (fun t => D (j + 2) (t + 1)) d r₀ k) =
      subseq (fun t => D (j + 1) t || D (j + 2) t) d r₀ := funext hD
  have h := crossCorr_eq_S_xor (subseq (D j) d r₀) (subseq (fun t => D (j + 2) (t + 1)) d r₀) T
  rw [hfun] at h
  exact h

/-- **All Problem 2 Energy Forms Along Odd-Stride Progressions of Antiperiodic Sequences
(`energy_forms_subseq_odd_of_antiperiodic`):** if `EvAntiPer c L` holds (`0 < L`), then for every
odd stride `2 * m + 1` and phase `r₀ : Nat`, the subsequence `subseq c (2 * m + 1) r₀` satisfies
`HalfDensity`, `DensityHalf`, `ShellMaxLittleO`, `FlexibleEnergyToZero`, `OrderedEnergyLittleO`,
and `MaxBlockEnergyLittleO`. -/
theorem energy_forms_subseq_odd_of_antiperiodic {c : Nat → Bool} {L : Nat}
    (hL : 0 < L) (ha : EvAntiPer c L) (m r₀ : Nat) :
    HalfDensity (subseq c (2 * m + 1) r₀) ∧
      DensityHalf (subseq c (2 * m + 1) r₀) ∧
      ShellMaxLittleO (subseq c (2 * m + 1) r₀) ∧
      FlexibleEnergyToZero (subseq c (2 * m + 1) r₀) ∧
      OrderedEnergyLittleO (subseq c (2 * m + 1) r₀) ∧
      MaxBlockEnergyLittleO (subseq c (2 * m + 1) r₀) :=
  energy_forms_of_antiperiodic hL (evAntiPer_subseq_odd ha m r₀)

/-- **Infinitely Many Left Diagonals Satisfy All Problem 2 Energy Forms Along Every Odd-Stride Progression
(`D_subseq_odd_infinitely_many_energy_forms`):** for every odd stride `2 * m + 1`, phase `r₀ : Nat`,
and index bound `N : Nat`, there exists a left diagonal `j > N` such that `subseq (D j) (2 * m + 1) r₀`
satisfies all six Problem 2 balance and energy conditions. -/
theorem D_subseq_odd_infinitely_many_energy_forms (m r₀ N : Nat) :
    ∃ j : Nat, N < j ∧
      HalfDensity (subseq (D j) (2 * m + 1) r₀) ∧
      DensityHalf (subseq (D j) (2 * m + 1) r₀) ∧
      ShellMaxLittleO (subseq (D j) (2 * m + 1) r₀) ∧
      FlexibleEnergyToZero (subseq (D j) (2 * m + 1) r₀) ∧
      OrderedEnergyLittleO (subseq (D j) (2 * m + 1) r₀) ∧
      MaxBlockEnergyLittleO (subseq (D j) (2 * m + 1) r₀) := by
  obtain ⟨j, hj, k, hanti, _, _⟩ := D_infinitely_many_halfDensity N
  have hL : 0 < 2 ^ k := Nat.two_pow_pos k
  exact ⟨j, hj, energy_forms_subseq_odd_of_antiperiodic hL hanti m r₀⟩

/-- **Infinitely Many Right Diagonals Satisfy All Problem 2 Energy Forms Along Every Odd-Stride Progression
(`R_subseq_odd_infinitely_many_energy_forms`):** for every odd stride `2 * m + 1`, phase `r₀ : Nat`,
and exponent `k₀ : Nat`, there exists a right diagonal `R j` (`k₀ < j ≤ 2 ^ (k₀ + 1) - 1`) such that
`subseq (R j) (2 * m + 1) r₀` satisfies all six Problem 2 balance and energy conditions. -/
theorem R_subseq_odd_infinitely_many_energy_forms (m r₀ k₀ : Nat) :
    ∃ j : Nat, k₀ < j ∧ j ≤ 2 ^ (k₀ + 1) - 1 ∧
      HalfDensity (subseq (R j) (2 * m + 1) r₀) ∧
      DensityHalf (subseq (R j) (2 * m + 1) r₀) ∧
      ShellMaxLittleO (subseq (R j) (2 * m + 1) r₀) ∧
      FlexibleEnergyToZero (subseq (R j) (2 * m + 1) r₀) ∧
      OrderedEnergyLittleO (subseq (R j) (2 * m + 1) r₀) ∧
      MaxBlockEnergyLittleO (subseq (R j) (2 * m + 1) r₀) := by
  obtain ⟨j, hj1, hj2, ha0, _, _⟩ := R_infinitely_many_halfDensity k₀
  have hL : 0 < 2 ^ k₀ := Nat.two_pow_pos k₀
  exact ⟨j, hj1, hj2, energy_forms_subseq_odd_of_antiperiodic hL ⟨0, fun t _ => ha0 t⟩ m r₀⟩

/-! ### Direct Energy-Form Bridges to Odd-Period Exclusion and Full Problem 1 Closure -/

/-- **Equivalence of `HalfDensity` and `ShellMaxLittleO` (`halfDensity_iff_shellMaxLittleO`):** for
any sequence `c`, `HalfDensity c ↔ ShellMaxLittleO c`. -/
theorem halfDensity_iff_shellMaxLittleO (c : Nat → Bool) :
    HalfDensity c ↔ ShellMaxLittleO c :=
  (halfDensity_iff_densityHalf c).trans (densityHalf_iff_shellMaxLittleO c)

/-- **Equivalence of `HalfDensity` and `FlexibleEnergyToZero` (`halfDensity_iff_flexibleEnergyToZero`):**
for any sequence `c`, `HalfDensity c ↔ FlexibleEnergyToZero c`. -/
theorem halfDensity_iff_flexibleEnergyToZero (c : Nat → Bool) :
    HalfDensity c ↔ FlexibleEnergyToZero c :=
  (halfDensity_iff_densityHalf c).trans (densityHalf_iff_flexibleEnergyToZero c)

/-- **Equivalence of `HalfDensity` and `OrderedEnergyLittleO` (`halfDensity_iff_orderedEnergyLittleO`):**
for any sequence `c`, `HalfDensity c ↔ OrderedEnergyLittleO c`. -/
theorem halfDensity_iff_orderedEnergyLittleO (c : Nat → Bool) :
    HalfDensity c ↔ OrderedEnergyLittleO c :=
  (halfDensity_iff_densityHalf c).trans (densityHalf_iff_orderedEnergyLittleO c)

/-- **Equivalence of `HalfDensity` and `MaxBlockEnergyLittleO` (`halfDensity_iff_maxBlockEnergyLittleO`):**
for any sequence `c`, `HalfDensity c ↔ MaxBlockEnergyLittleO c`. -/
theorem halfDensity_iff_maxBlockEnergyLittleO (c : Nat → Bool) :
    HalfDensity c ↔ MaxBlockEnergyLittleO c :=
  (halfDensity_iff_orderedEnergyLittleO c).trans (orderedEnergyLittleO_iff_maxBlockEnergyLittleO c)

/-- **Odd-Period Exclusion from `DensityHalf` (`not_evPer_odd_of_densityHalf`):** any sequence `f`
satisfying `DensityHalf f` has no odd eventual period `2 * m + 1`. -/
theorem not_evPer_odd_of_densityHalf {f : Nat → Bool}
    (h : DensityHalf f) (m : Nat) :
    ¬ EvPer f (2 * m + 1) :=
  Rule30LeftAntiPeriod.not_evPer_odd_of_halfDensity ((halfDensity_iff_densityHalf f).mpr h) m

/-- **Odd-Period Exclusion from `ShellMaxLittleO` (`not_evPer_odd_of_shellMaxLittleO`):** any
sequence `f` satisfying `ShellMaxLittleO f` has no odd eventual period `2 * m + 1`. -/
theorem not_evPer_odd_of_shellMaxLittleO {f : Nat → Bool}
    (h : ShellMaxLittleO f) (m : Nat) :
    ¬ EvPer f (2 * m + 1) :=
  Rule30LeftAntiPeriod.not_evPer_odd_of_halfDensity ((halfDensity_iff_shellMaxLittleO f).mpr h) m

/-- **Odd-Period Exclusion from `FlexibleEnergyToZero` (`not_evPer_odd_of_flexibleEnergyToZero`):**
any sequence `f` satisfying `FlexibleEnergyToZero f` has no odd eventual period `2 * m + 1`. -/
theorem not_evPer_odd_of_flexibleEnergyToZero {f : Nat → Bool}
    (h : FlexibleEnergyToZero f) (m : Nat) :
    ¬ EvPer f (2 * m + 1) :=
  Rule30LeftAntiPeriod.not_evPer_odd_of_halfDensity ((halfDensity_iff_flexibleEnergyToZero f).mpr h) m

/-- **Odd-Period Exclusion from `OrderedEnergyLittleO` (`not_evPer_odd_of_orderedEnergyLittleO`):**
any sequence `f` satisfying `OrderedEnergyLittleO f` has no odd eventual period `2 * m + 1`. -/
theorem not_evPer_odd_of_orderedEnergyLittleO {f : Nat → Bool}
    (h : OrderedEnergyLittleO f) (m : Nat) :
    ¬ EvPer f (2 * m + 1) :=
  Rule30LeftAntiPeriod.not_evPer_odd_of_halfDensity ((halfDensity_iff_orderedEnergyLittleO f).mpr h) m

/-- **Odd-Period Exclusion from `MaxBlockEnergyLittleO` (`not_evPer_odd_of_maxBlockEnergyLittleO`):**
any sequence `f` satisfying `MaxBlockEnergyLittleO f` has no odd eventual period `2 * m + 1`. -/
theorem not_evPer_odd_of_maxBlockEnergyLittleO {f : Nat → Bool}
    (h : MaxBlockEnergyLittleO f) (m : Nat) :
    ¬ EvPer f (2 * m + 1) :=
  Rule30LeftAntiPeriod.not_evPer_odd_of_halfDensity ((halfDensity_iff_maxBlockEnergyLittleO f).mpr h) m

/-- **Full `Problem1` Closure from `ShellMaxLittleO` on Progressions (`problem1_of_subseq_shellMaxLittleO`):**
if for every modulus `L > 0` there is a canonical remainder `r < L` with `ShellMaxLittleO (subseq center L r)`,
then `Problem1` holds unconditionally. -/
theorem problem1_of_subseq_shellMaxLittleO
    (h : ∀ L : Nat, 0 < L → ∃ r : Nat, r < L ∧ ShellMaxLittleO (subseq center L r)) :
    Problem1 :=
  Rule30LeftAntiPeriod.problem1_of_subseq_halfDensity_lt (fun L hL => by
    obtain ⟨r, hr, hs⟩ := h L hL
    exact ⟨r, hr, (halfDensity_iff_shellMaxLittleO _).mpr hs⟩)

/-- **Full `Problem1` Closure from `MaxBlockEnergyLittleO` on Progressions
(`problem1_of_subseq_maxBlockEnergyLittleO`):** if for every modulus `L > 0` there is a canonical
remainder `r < L` with `MaxBlockEnergyLittleO (subseq center L r)`, then `Problem1` holds unconditionally. -/
theorem problem1_of_subseq_maxBlockEnergyLittleO
    (h : ∀ L : Nat, 0 < L → ∃ r : Nat, r < L ∧ MaxBlockEnergyLittleO (subseq center L r)) :
    Problem1 :=
  Rule30LeftAntiPeriod.problem1_of_subseq_halfDensity_lt (fun L hL => by
    obtain ⟨r, hr, hs⟩ := h L hL
    exact ⟨r, hr, (halfDensity_iff_maxBlockEnergyLittleO _).mpr hs⟩)

/-- **Reduction of `Problem1` to Center + Even-Stride `ShellMaxLittleO`
(`problem1_of_shellMaxLittleO_and_even_subseq`):** `ShellMaxLittleO center` together with an even-stride
canonical remainder satisfying `ShellMaxLittleO (subseq center (2 * m) r)` for each `m > 0` implies `Problem1`. -/
theorem problem1_of_shellMaxLittleO_and_even_subseq
    (h0 : ShellMaxLittleO center)
    (heven : ∀ m : Nat, 0 < m → ∃ r : Nat, r < 2 * m ∧ ShellMaxLittleO (subseq center (2 * m) r)) :
    Problem1 :=
  Rule30LeftAntiPeriod.problem1_of_problem2_and_even_subseq_halfDensity_lt
    (problem2_iff_shellMaxLittleO.mpr h0)
    (fun m hm => by
      obtain ⟨r, hr, hs⟩ := heven m hm
      exact ⟨r, hr, (halfDensity_iff_shellMaxLittleO _).mpr hs⟩)

/-- **Reduction of `Problem1` to Center + Even-Stride `MaxBlockEnergyLittleO`
(`problem1_of_maxBlockEnergyLittleO_and_even_subseq`):** `MaxBlockEnergyLittleO center` together
with an even-stride canonical remainder satisfying `MaxBlockEnergyLittleO (subseq center (2 * m) r)`
for each `m > 0` implies `Problem1`. -/
theorem problem1_of_maxBlockEnergyLittleO_and_even_subseq
    (h0 : MaxBlockEnergyLittleO center)
    (heven : ∀ m : Nat, 0 < m → ∃ r : Nat, r < 2 * m ∧ MaxBlockEnergyLittleO (subseq center (2 * m) r)) :
    Problem1 :=
  Rule30LeftAntiPeriod.problem1_of_problem2_and_even_subseq_halfDensity_lt
    (problem2_iff_maxBlockEnergyLittleO.mpr h0)
    (fun m hm => by
      obtain ⟨r, hr, hs⟩ := heven m hm
      exact ⟨r, hr, (halfDensity_iff_maxBlockEnergyLittleO _).mpr hs⟩)

/-! ### Unit-Stride Subsequence Identity, Complete Five-Form Progression Closures, and Simultaneous `Problem1 ∧ Problem2` Reductions -/

/-- **Unit-Stride Subsequence Identity (`subseq_one_zero`):** subsampling any sequence `f` with
stride `1` and offset `0` returns `f` identically (`subseq f 1 0 = f`). -/
theorem subseq_one_zero (f : Nat → Bool) : subseq f 1 0 = f := by
  funext k
  unfold subseq
  exact congrArg f (by omega)

/-- **Full `Problem1` Closure from `DensityHalf` on Progressions (`problem1_of_subseq_densityHalf`):**
if for every modulus `L > 0` there is a canonical remainder `r < L` with
`DensityHalf (subseq center L r)`, then `Problem1` holds unconditionally. -/
theorem problem1_of_subseq_densityHalf
    (h : ∀ L : Nat, 0 < L → ∃ r : Nat, r < L ∧ DensityHalf (subseq center L r)) :
    Problem1 :=
  Rule30LeftAntiPeriod.problem1_of_subseq_halfDensity_lt (fun L hL => by
    obtain ⟨r, hr, hd⟩ := h L hL
    exact ⟨r, hr, (halfDensity_iff_densityHalf _).mpr hd⟩)

/-- **Full `Problem1` Closure from `FlexibleEnergyToZero` on Progressions
(`problem1_of_subseq_flexibleEnergyToZero`):** if for every modulus `L > 0` there is a canonical
remainder `r < L` with `FlexibleEnergyToZero (subseq center L r)`, then `Problem1` holds. -/
theorem problem1_of_subseq_flexibleEnergyToZero
    (h : ∀ L : Nat, 0 < L → ∃ r : Nat, r < L ∧ FlexibleEnergyToZero (subseq center L r)) :
    Problem1 :=
  Rule30LeftAntiPeriod.problem1_of_subseq_halfDensity_lt (fun L hL => by
    obtain ⟨r, hr, hf⟩ := h L hL
    exact ⟨r, hr, (halfDensity_iff_flexibleEnergyToZero _).mpr hf⟩)

/-- **Full `Problem1` Closure from `OrderedEnergyLittleO` on Progressions
(`problem1_of_subseq_orderedEnergyLittleO`):** if for every modulus `L > 0` there is a canonical
remainder `r < L` with `OrderedEnergyLittleO (subseq center L r)`, then `Problem1` holds. -/
theorem problem1_of_subseq_orderedEnergyLittleO
    (h : ∀ L : Nat, 0 < L → ∃ r : Nat, r < L ∧ OrderedEnergyLittleO (subseq center L r)) :
    Problem1 :=
  Rule30LeftAntiPeriod.problem1_of_subseq_halfDensity_lt (fun L hL => by
    obtain ⟨r, hr, ho⟩ := h L hL
    exact ⟨r, hr, (halfDensity_iff_orderedEnergyLittleO _).mpr ho⟩)

/-- **Reduction of `Problem1` to Center + Even-Stride `DensityHalf`
(`problem1_of_densityHalf_and_even_subseq`):** `DensityHalf center` together with an even-stride
canonical remainder satisfying `DensityHalf (subseq center (2 * m) r)` for each `m > 0` implies `Problem1`. -/
theorem problem1_of_densityHalf_and_even_subseq
    (h0 : DensityHalf center)
    (heven : ∀ m : Nat, 0 < m → ∃ r : Nat, r < 2 * m ∧ DensityHalf (subseq center (2 * m) r)) :
    Problem1 :=
  Rule30LeftAntiPeriod.problem1_of_problem2_and_even_subseq_halfDensity_lt
    (problem2_iff_densityHalf.mpr h0)
    (fun m hm => by
      obtain ⟨r, hr, hd⟩ := heven m hm
      exact ⟨r, hr, (halfDensity_iff_densityHalf _).mpr hd⟩)

/-- **Reduction of `Problem1` to Center + Even-Stride `FlexibleEnergyToZero`
(`problem1_of_flexibleEnergyToZero_and_even_subseq`):** `FlexibleEnergyToZero center` together with
an even-stride canonical remainder satisfying `FlexibleEnergyToZero (subseq center (2 * m) r)`
for each `m > 0` implies `Problem1`. -/
theorem problem1_of_flexibleEnergyToZero_and_even_subseq
    (h0 : FlexibleEnergyToZero center)
    (heven : ∀ m : Nat, 0 < m → ∃ r : Nat, r < 2 * m ∧ FlexibleEnergyToZero (subseq center (2 * m) r)) :
    Problem1 :=
  Rule30LeftAntiPeriod.problem1_of_problem2_and_even_subseq_halfDensity_lt
    (problem2_iff_flexibleEnergyToZero.mpr h0)
    (fun m hm => by
      obtain ⟨r, hr, hf⟩ := heven m hm
      exact ⟨r, hr, (halfDensity_iff_flexibleEnergyToZero _).mpr hf⟩)

/-- **Reduction of `Problem1` to Center + Even-Stride `OrderedEnergyLittleO`
(`problem1_of_orderedEnergyLittleO_and_even_subseq`):** `OrderedEnergyLittleO center` together with
an even-stride canonical remainder satisfying `OrderedEnergyLittleO (subseq center (2 * m) r)`
for each `m > 0` implies `Problem1`. -/
theorem problem1_of_orderedEnergyLittleO_and_even_subseq
    (h0 : OrderedEnergyLittleO center)
    (heven : ∀ m : Nat, 0 < m → ∃ r : Nat, r < 2 * m ∧ OrderedEnergyLittleO (subseq center (2 * m) r)) :
    Problem1 :=
  Rule30LeftAntiPeriod.problem1_of_problem2_and_even_subseq_halfDensity_lt
    (problem2_iff_orderedEnergyLittleO.mpr h0)
    (fun m hm => by
      obtain ⟨r, hr, ho⟩ := heven m hm
      exact ⟨r, hr, (halfDensity_iff_orderedEnergyLittleO _).mpr ho⟩)

/-- **`Problem2` from `ShellMaxLittleO` on Progressions (`problem2_of_subseq_shellMaxLittleO`):**
specializing the progression hypothesis at modulus `L = 1` forces `r = 0` and recovers
`ShellMaxLittleO center`, hence `Problem2`. -/
theorem problem2_of_subseq_shellMaxLittleO
    (h : ∀ L : Nat, 0 < L → ∃ r : Nat, r < L ∧ ShellMaxLittleO (subseq center L r)) :
    Problem2 := by
  obtain ⟨r, hr, hs⟩ := h 1 (by decide)
  have hr0 : r = 0 := by omega
  subst hr0
  rw [subseq_one_zero] at hs
  exact problem2_iff_shellMaxLittleO.mpr hs

/-- **Single-Hypothesis Simultaneous Closure of `Problem1 ∧ Problem2` via `ShellMaxLittleO`
(`problem1_and_problem2_of_subseq_shellMaxLittleO`):** if for every `L > 0` there is `r < L` with
`ShellMaxLittleO (subseq center L r)`, then both `Problem1` and `Problem2` hold simultaneously. -/
theorem problem1_and_problem2_of_subseq_shellMaxLittleO
    (h : ∀ L : Nat, 0 < L → ∃ r : Nat, r < L ∧ ShellMaxLittleO (subseq center L r)) :
    Problem1 ∧ Problem2 :=
  ⟨problem1_of_subseq_shellMaxLittleO h, problem2_of_subseq_shellMaxLittleO h⟩

/-- **Single-Hypothesis Simultaneous Closure of `Problem1 ∧ Problem2` via `MaxBlockEnergyLittleO`
(`problem1_and_problem2_of_subseq_maxBlockEnergyLittleO`):** if for every `L > 0` there is `r < L`
with `MaxBlockEnergyLittleO (subseq center L r)`, then both `Problem1` and `Problem2` hold. -/
theorem problem1_and_problem2_of_subseq_maxBlockEnergyLittleO
    (h : ∀ L : Nat, 0 < L → ∃ r : Nat, r < L ∧ MaxBlockEnergyLittleO (subseq center L r)) :
    Problem1 ∧ Problem2 := by
  refine ⟨problem1_of_subseq_maxBlockEnergyLittleO h, ?_⟩
  obtain ⟨r, hr, hm⟩ := h 1 (by decide)
  have hr0 : r = 0 := by omega
  subst hr0
  rw [subseq_one_zero] at hm
  exact problem2_iff_maxBlockEnergyLittleO.mpr hm

/-- **Simultaneous Closure of `Problem1 ∧ Problem2` from Center + Even-Stride `ShellMaxLittleO`
(`problem1_and_problem2_of_shellMaxLittleO_and_even_subseq`):** `ShellMaxLittleO center` and
even-stride `ShellMaxLittleO (subseq center (2 * m) r)` imply `Problem1 ∧ Problem2`. -/
theorem problem1_and_problem2_of_shellMaxLittleO_and_even_subseq
    (h0 : ShellMaxLittleO center)
    (heven : ∀ m : Nat, 0 < m → ∃ r : Nat, r < 2 * m ∧ ShellMaxLittleO (subseq center (2 * m) r)) :
    Problem1 ∧ Problem2 :=
  ⟨problem1_of_shellMaxLittleO_and_even_subseq h0 heven, problem2_iff_shellMaxLittleO.mpr h0⟩

/-- **Simultaneous Closure of `Problem1 ∧ Problem2` from Center + Even-Stride `MaxBlockEnergyLittleO`
(`problem1_and_problem2_of_maxBlockEnergyLittleO_and_even_subseq`):** `MaxBlockEnergyLittleO center`
and even-stride `MaxBlockEnergyLittleO (subseq center (2 * m) r)` imply `Problem1 ∧ Problem2`. -/
theorem problem1_and_problem2_of_maxBlockEnergyLittleO_and_even_subseq
    (h0 : MaxBlockEnergyLittleO center)
    (heven : ∀ m : Nat, 0 < m → ∃ r : Nat, r < 2 * m ∧ MaxBlockEnergyLittleO (subseq center (2 * m) r)) :
    Problem1 ∧ Problem2 :=
  ⟨problem1_of_maxBlockEnergyLittleO_and_even_subseq h0 heven, problem2_iff_maxBlockEnergyLittleO.mpr h0⟩

end Rule30P2Bridge
end Ruliology.CellularAutomata
