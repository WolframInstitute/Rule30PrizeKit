module

public import Ruliology.CellularAutomata.Rule30Prize

@[expose] public section

/-!
# Rule 30: Problem 2 from one source-energy estimate

Let `c(t)` be the center column of rule 30 started from a single black cell, and write
`z t = (-1)^{c(t)}` as an integer. For `n ≥ 2` let `N = 2^n` and use the `n` shifts
`S = {0, 1, 2, 4, …, 2^(n-2)}`. The shifted sum over the zero-extended word of length `N` is

  `Z(u) = Σ_{s ∈ S} z(u + s)`   (terms outside `[0, N)` count as `0`),

and the source energy is `Esrc n = Σ_{0 ≤ u < 2^n} Z(u)^2`.
Since `z(u)^2 = 1`, for `0 ≤ u < N` this is `Z(u)^2 = (1 + Σ_j χ_j(u))^2` with the source
signs `χ_j(u) = z(u) z(u + 2^j)` (the terms with `u + 2^j < N`).

Main result (`problem2_of_source_energy`): if `Esrc n = o(2^n n^2)`, in the integer form
`∀ k > 0, eventually 8 k² Esrc n ≤ 2^n n²`, then the center column has density `1/2`
(`Problem2`), along all lengths. This is a sufficient condition, not an equivalence; the kit's
equivalent forms of `Problem2` (shell maxima, block energies) are in `Rule30P2Bridge`. Nothing
here bounds `Esrc` on the center column.

Proof. For `2^(n-1) < M ≤ 2^n`, summing `Z` over `0 ≤ u < M` counts every `z(t)`, `t < M`,
once per shift, up to a boundary error at most `2 Σ_{s∈S} s < 2^n`
(`sum_Z_close`). Cauchy–Schwarz (`cauchy_schwarz`) bounds that sum by `√(M · Esrc n)`, so
`n |D(M)| ≤ √(M · Esrc n) + 2^n` where `D(M) = Σ_{t<M} z t = M - 2·blackCount M`.
Divide by `n M` and use `2^n < 2M`.

Also included, for the record: Cauchy–Schwarz for integer lists
(`cauchy_schwarz_list`), the identity `D(M) = M - 2·blackCount M` (`sum_z`), and the
van der Corput–type bound with the full support (`vdc`):
`n² D(N)² ≤ (N + H) · Ttot N n`, `H = 2^n / 4`, where `Ttot` sums `Z(u)²` over `-H ≤ u < N`.
The part of `Ttot` at `-H ≤ u < 0` is at most `(3/2) · 2^n` (`F_bound`), via the exact
count `Σ_{v=1}^{2^m} #{j ≤ m : v ≤ 2^j}² = 6 · 2^m - 2m - 5` (`cnt_sums`).
-/

namespace Ruliology.CellularAutomata
namespace Rule30SourceEnergy

open Rule30Prize

/-! ## Finite sums -/

/-- `rsum k f = f 0 + f 1 + ⋯ + f (k - 1)`. -/
def rsum : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | k + 1, f => rsum k f + f k

@[simp] theorem rsum_zero (f : Nat → Int) : rsum 0 f = 0 := rfl

theorem rsum_succ (k : Nat) (f : Nat → Int) : rsum (k + 1) f = rsum k f + f k := rfl

/-- Sums are additive. -/
theorem rsum_add (k : Nat) (f g : Nat → Int) :
    rsum k (fun i => f i + g i) = rsum k f + rsum k g := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [rsum_succ, ih]; omega

/-- Sums commute with constant factors. -/
theorem rsum_mul (k : Nat) (c : Int) (f : Nat → Int) :
    rsum k (fun i => c * f i) = c * rsum k f := by
  induction k with
  | zero => simp
  | succ k ih => simp only [rsum_succ, ih, Int.mul_add]

/-- Sums only depend on the summands in range. -/
theorem rsum_congr (k : Nat) {f g : Nat → Int} (h : ∀ i, i < k → f i = g i) :
    rsum k f = rsum k g := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [rsum_succ, rsum_succ, ih (fun i hi => h i (by omega)), h k (by omega)]

/-- Constant sums. -/
theorem rsum_const (k : Nat) (c : Int) : rsum k (fun _ => c) = k * c := by
  induction k with
  | zero => simp
  | succ k ih => rw [rsum_succ, ih]; push_cast; rw [Int.add_mul, Int.one_mul]

/-- Fubini for double sums. -/
theorem rsum_comm (a b : Nat) (g : Nat → Nat → Int) :
    rsum a (fun u => rsum b (fun j => g u j)) = rsum b (fun j => rsum a (fun u => g u j)) := by
  induction a with
  | zero =>
    simp only [rsum_zero]
    exact (rsum_const b 0).trans (by simp) |>.symm
  | succ a ih =>
    rw [rsum_succ, ih, ← rsum_add]
    rfl

/-- Splitting a range `[0, s + M)` at `s`. -/
theorem rsum_split (s M : Nat) (f : Nat → Int) :
    rsum (s + M) f = rsum s f + rsum M (fun u => f (s + u)) := by
  induction M with
  | zero => simp
  | succ M ih => rw [← Nat.add_assoc, rsum_succ, rsum_succ, ih]; omega

/-- Sums of nonnegative terms are nonnegative. -/
theorem rsum_nonneg (k : Nat) {f : Nat → Int} (h : ∀ i, i < k → 0 ≤ f i) : 0 ≤ rsum k f := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [rsum_succ]
    have := ih (fun i hi => h i (by omega))
    have := h k (by omega)
    omega

/-- Sums are monotone in the summands. -/
theorem rsum_le_rsum (k : Nat) {f g : Nat → Int} (h : ∀ i, i < k → f i ≤ g i) :
    rsum k f ≤ rsum k g := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [rsum_succ, rsum_succ]
    have := ih (fun i hi => h i (by omega))
    have := h k (by omega)
    omega

/-- Sums of nonnegative terms are monotone in the length. -/
theorem rsum_mono_len {a b : Nat} (hab : a ≤ b) {f : Nat → Int} (h : ∀ i, 0 ≤ f i) :
    rsum a f ≤ rsum b f := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [rsum_split]
  have := rsum_nonneg d (f := fun u => f (a + u)) (fun i _ => h _)
  omega

/-- Sums of terms in `[-1, 1]` lie in `[-k, k]`. -/
theorem rsum_abs_le (k : Nat) {f : Nat → Int} (h : ∀ i, -1 ≤ f i ∧ f i ≤ 1) :
    -(k : Int) ≤ rsum k f ∧ rsum k f ≤ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [rsum_succ]
    have := h k
    push_cast
    omega

/-- `1 + 2 + ⋯ + 2^(k-1) = 2^k - 1`. -/
theorem rsum_pow_two (k : Nat) : rsum k (fun j => ((2 ^ j : Nat) : Int)) = 2 ^ k - 1 := by
  induction k with
  | zero => simp
  | succ k ih => rw [rsum_succ, ih]; push_cast; rw [Int.pow_succ]; omega

/-! ## Cauchy–Schwarz -/

/-- The expansion `Σ (p x_i - q)² = p² Σ x_i² - 2pq Σ x_i + k q²`. -/
theorem rsum_sq_expand (k : Nat) (f : Nat → Int) (p q : Int) :
    rsum k (fun i => (p * f i - q) ^ 2)
      = p ^ 2 * rsum k (fun i => f i ^ 2) - 2 * p * q * rsum k f + k * q ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [rsum_succ, ih, rsum_succ, rsum_succ]
    push_cast
    grind

/-- **Cauchy–Schwarz**: `(Σ_{i<k} f i)² ≤ k · Σ_{i<k} (f i)²`. -/
theorem cauchy_schwarz (k : Nat) (f : Nat → Int) :
    rsum k f ^ 2 ≤ k * rsum k (fun i => f i ^ 2) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have h0 := rsum_nonneg k (f := fun i => ((k : Int) * f i - rsum k f) ^ 2)
    (fun i _ => Int.sq_nonneg _)
  rw [rsum_sq_expand] at h0
  have hk' : (0 : Int) < k := by omega
  have key : (k : Int) * (rsum k f ^ 2) ≤ k * (k * rsum k (fun i => f i ^ 2)) := by
    have : (k : Int) * (k * rsum k (fun i => f i ^ 2)) - k * rsum k f ^ 2
        = (k : Int) ^ 2 * rsum k (fun i => f i ^ 2) - 2 * k * rsum k f * rsum k f
          + k * rsum k f ^ 2 := by grind
    omega
  exact Int.le_of_mul_le_mul_left key hk'

/-- The expansion `Σ (p x - q)² = p² Σ x² - 2pq Σ x + length · q²` over a list. -/
theorem list_sq_expand (l : List Int) (p q : Int) :
    (l.map (fun x => (p * x - q) ^ 2)).sum
      = p ^ 2 * (l.map (· ^ 2)).sum - 2 * p * q * l.sum + l.length * q ^ 2 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    push_cast
    grind

theorem list_sum_nonneg (l : List Int) (h : ∀ x ∈ l, 0 ≤ x) : 0 ≤ l.sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.sum_cons]
    have := h x (by simp)
    have := ih (fun y hy => h y (by simp [hy]))
    omega

/-- **Cauchy–Schwarz for integer lists**: `(Σ x)² ≤ length · Σ x²`. -/
theorem cauchy_schwarz_list (l : List Int) :
    l.sum ^ 2 ≤ l.length * (l.map (· ^ 2)).sum := by
  rcases Nat.eq_zero_or_pos l.length with h | hk
  · rw [List.length_eq_zero_iff.1 h]; simp
  have h0 := list_sum_nonneg (l.map (fun x => ((l.length : Int) * x - l.sum) ^ 2))
    (fun y hy => by
      obtain ⟨x, _, rfl⟩ := List.mem_map.1 hy
      exact Int.sq_nonneg _)
  rw [list_sq_expand] at h0
  have hk' : (0 : Int) < l.length := by omega
  have key : (l.length : Int) * (l.sum ^ 2) ≤ l.length * (l.length * (l.map (· ^ 2)).sum) := by
    have : (l.length : Int) * (l.length * (l.map (· ^ 2)).sum) - l.length * l.sum ^ 2
        = (l.length : Int) ^ 2 * (l.map (· ^ 2)).sum - 2 * l.length * l.sum * l.sum
          + l.length * l.sum ^ 2 := by grind
    omega
  exact Int.le_of_mul_le_mul_left key hk'

/-! ## The center column as a sign word -/

/-- The sign of the center cell: `-1` for black, `1` for white. -/
def z (t : Nat) : Int := if center t then -1 else 1

/-- `D0 N = Σ_{t<N} z t`. -/
def D0 (N : Nat) : Int := rsum N z

theorem blackCount_succ (n : Nat) :
    blackCount (n + 1) = blackCount n + if center n then 1 else 0 := by
  unfold blackCount
  rw [List.range_succ, List.filter_append]
  cases h : center n <;> simp [h]

/-- `Σ_{t<N} z t = N - 2 · blackCount N`. -/
theorem sum_z (N : Nat) : D0 N = N - 2 * (blackCount N : Int) := by
  induction N with
  | zero => simp [D0, blackCount]
  | succ N ih =>
    unfold D0 at ih ⊢
    rw [rsum_succ, ih, blackCount_succ]
    unfold z
    cases center N <;> simp <;> omega

/-- The zero extension of `z` outside `[0, N)`. -/
def zext (N : Nat) (u : Int) : Int := if 0 ≤ u ∧ u < N then z u.toNat else 0

theorem zext_bound (N : Nat) (u : Int) : -1 ≤ zext N u ∧ zext N u ≤ 1 := by
  unfold zext z
  split
  · split <;> omega
  · omega

/-- `H n = 2^n / 4`, the largest shift. -/
def H (n : Nat) : Nat := 2 ^ n / 4

/-- The shift set `S n = {0, 1, 2, 4, …, 2^(n-2)}` (`n` shifts). -/
def S (n : Nat) : List Nat := 0 :: (List.range (n - 1)).map (2 ^ ·)

/-- The shifted sum `Z N n u = Σ_{s ∈ S n} zext N (u + s)`. -/
def Z (N n : Nat) (u : Int) : Int := ((S n).map (fun s : Nat => zext N (u + s))).sum

theorem list_sum_map_range (k : Nat) (f : Nat → Int) :
    ((List.range k).map f).sum = rsum k f := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.range_succ, List.map_append, List.sum_append, ih]; simp [rsum_succ]

theorem Z_eq (N n : Nat) (u : Int) :
    Z N n u = zext N u + rsum (n - 1) (fun j => zext N (u + ((2 ^ j : Nat) : Int))) := by
  unfold Z S
  rw [List.map_cons, List.sum_cons, List.map_map, ← list_sum_map_range]
  simp only [Int.natCast_zero, Int.add_zero]
  rfl

/-- The total energy `Ttot N n = Σ_{-H ≤ u < N} (Z N n u)²`. -/
def Ttot (N n : Nat) : Int := rsum (N + H n) (fun i => Z N n ((i : Int) - H n) ^ 2)

/-- The source energy `Esrc n = Σ_{0 ≤ u < 2^n} (Z (2^n) n u)²`. -/
def Esrc (n : Nat) : Int := rsum (2 ^ n) (fun u => Z (2 ^ n) n u ^ 2)

/-- For `0 ≤ u < N`, `Z(u)² = (1 + Σ_j χ_j(u))²` with the source signs
`χ_j(u) = z(u) · zext(u + 2^j)`. -/
theorem Z_sq_eq (N n u : Nat) (hu : u < N) :
    Z N n u ^ 2 = (1 + rsum (n - 1) (fun j => z u * zext N (u + ((2 ^ j : Nat) : Int)))) ^ 2 := by
  rw [Z_eq, rsum_mul]
  have hz : zext N u = z u := by unfold zext; simp [hu]
  have h1 : z u * z u = 1 := by unfold z; split <;> rfl
  rw [hz]
  generalize rsum (n - 1) _ = r
  grind

/-! ## Summing the shifted sums -/

/-- The prefix sums of the zero-extended word. -/
theorem rsum_zext_le (N M : Nat) (hM : M ≤ N) : rsum M (fun u => zext N u) = D0 M := by
  unfold D0
  exact rsum_congr _ (fun i hi => by unfold zext; simp; omega)

/-- `Σ_{u<M} zext N (u + s)` differs from `Σ_{u<M} zext N u` by at most `2s`. -/
theorem shift_sum_close (N M s : Nat) :
    -(2 * s : Int) ≤ rsum M (fun u => zext N ((u : Int) + s)) - rsum M (fun u => zext N u) ∧
    rsum M (fun u => zext N ((u : Int) + s)) - rsum M (fun u => zext N u) ≤ 2 * s := by
  -- both sums are pieces of the sum over `[0, s + M)` = `[0, M + s)`
  have e1 := rsum_split s M (fun u => zext N u)
  have e2 := rsum_split M s (fun u => zext N u)
  rw [Nat.add_comm s M] at e1
  have hc : rsum M (fun u => zext N ((s + u : Nat) : Int)) = rsum M (fun u => zext N ((u : Int) + s)) :=
    rsum_congr _ (fun i _ => by push_cast; rw [Int.add_comm])
  rw [hc] at e1
  have b1 := rsum_abs_le s (f := fun u => zext N u) (fun i => zext_bound _ _)
  have b2 := rsum_abs_le s (f := fun u => zext N ((M + u : Nat) : Int)) (fun i => zext_bound _ _)
  omega

/-- **Summing the shifted sums**: `Σ_{u<M} Z(u)` is `n · D0 M` up to an error less than `2^n`. -/
theorem sum_Z_close (n M : Nat) (hn : 1 ≤ n) (hM : M ≤ 2 ^ n) :
    -(2 ^ n : Int) ≤ rsum M (fun u => Z (2 ^ n) n u) - n * D0 M ∧
    rsum M (fun u => Z (2 ^ n) n u) - n * D0 M ≤ 2 ^ n := by
  have hZ : rsum M (fun u => Z (2 ^ n) n u)
      = rsum M (fun u => zext (2 ^ n) u)
        + rsum (n - 1) (fun j => rsum M (fun u => zext (2 ^ n) ((u : Int) + ((2 ^ j : Nat) : Int)))) := by
    rw [← rsum_comm, ← rsum_add]
    exact rsum_congr _ (fun i _ => Z_eq _ _ _)
  -- the error term
  have herr : ∀ k, k ≤ n - 1 →
      -(2 * ((2 ^ k : Nat) - 1) : Int) ≤
        rsum k (fun j => rsum M (fun u => zext (2 ^ n) ((u : Int) + ((2 ^ j : Nat) : Int))))
          - k * rsum M (fun u => zext (2 ^ n) u) ∧
      rsum k (fun j => rsum M (fun u => zext (2 ^ n) ((u : Int) + ((2 ^ j : Nat) : Int))))
          - k * rsum M (fun u => zext (2 ^ n) u) ≤ 2 * ((2 ^ k : Nat) - 1) := by
    intro k _
    induction k with
    | zero => simp
    | succ k ih =>
      have ih := ih (by omega)
      rw [rsum_succ]
      have := shift_sum_close (2 ^ n) M (2 ^ k)
      push_cast at ih this ⊢
      rw [Int.pow_succ]
      constructor <;> grind
  have h := herr (n - 1) (Nat.le_refl _)
  have hp : ((2 ^ (n - 1) : Nat) : Int) * 2 = 2 ^ n := by
    push_cast; rw [← Int.pow_succ, show (n - 1).succ = n by omega]
  rw [hZ, rsum_zext_le _ _ hM]
  rw [rsum_zext_le _ _ hM] at h
  have hn' : (n : Int) = ((n - 1 : Nat) : Int) + 1 := by omega
  rw [hn', Int.add_mul, Int.one_mul]
  omega

/-! ## The van der Corput-type bound with full support -/

/-- **Shift averaging**: `n² · D0(N)² ≤ (N + H) · Ttot N n` for `n ≥ 2`, `N = 2^n`.
The shifted sums `Z(u)`, `-H ≤ u < N`, add up to `n · D0(N)`. -/
theorem vdc (n : Nat) (hn : 2 ≤ n) :
    (n : Int) ^ 2 * D0 (2 ^ n) ^ 2 ≤ ((2 ^ n + H n : Nat) : Int) * Ttot (2 ^ n) n := by
  have hH : 2 ^ n = 4 * 2 ^ (n - 2) := by
    rw [show n = n - 2 + 2 by omega, Nat.pow_add]; simp; omega
  have hH' : H n = 2 ^ (n - 2) := by unfold H; omega
  -- every shift `0 ≤ s ≤ H` contributes `D0 N` to the total sum of the `Z(u)`
  have hshift : ∀ d : Nat, d ≤ H n →
      rsum (2 ^ n + H n) (fun i => zext (2 ^ n) ((i : Int) - d)) = D0 (2 ^ n) := by
    intro d hd
    have e : 2 ^ n + H n = d + (2 ^ n + (H n - d)) := by omega
    rw [e, rsum_split, rsum_split]
    have z1 : rsum d (fun i => zext (2 ^ n) ((i : Int) - d)) = 0 :=
      (rsum_congr _ (fun i hi => by unfold zext; split <;> first | rfl | omega)).trans
        ((rsum_const d 0).trans (by simp))
    have z2 : rsum (H n - d) (fun u => zext (2 ^ n) (((d + (2 ^ n + u) : Nat) : Int) - d)) = 0 :=
      (rsum_congr _ (fun i hi => by unfold zext; split <;> first | rfl | omega)).trans
        ((rsum_const _ 0).trans (by simp))
    have z3 : rsum (2 ^ n) (fun u => zext (2 ^ n) (((d + u : Nat) : Int) - d)) = D0 (2 ^ n) :=
      (rsum_congr _ (fun i _ => by congr 1; omega)).trans (rsum_zext_le _ _ (Nat.le_refl _))
    rw [z1, z3, z2]; omega
  have hsum : rsum (2 ^ n + H n) (fun i => Z (2 ^ n) n ((i : Int) - H n)) = n * D0 (2 ^ n) := by
    have : rsum (2 ^ n + H n) (fun i => Z (2 ^ n) n ((i : Int) - H n))
        = rsum (2 ^ n + H n) (fun i => zext (2 ^ n) ((i : Int) - H n))
          + rsum (n - 1) (fun j => rsum (2 ^ n + H n)
              (fun i => zext (2 ^ n) ((i : Int) - ((H n - 2 ^ j : Nat) : Int)))) := by
      rw [← rsum_comm, ← rsum_add]
      refine rsum_congr _ (fun i _ => ?_)
      rw [Z_eq]
      congr 1
      refine rsum_congr _ (fun j hj => ?_)
      have : 2 ^ j ≤ H n := by
        rw [hH']; exact Nat.pow_le_pow_right (by omega) (by omega)
      congr 1; omega
    rw [this, hshift _ (Nat.le_refl _)]
    rw [rsum_congr (n - 1) (g := fun _ => D0 (2 ^ n)) (fun j _ => hshift (H n - 2 ^ j) (Nat.sub_le _ _)),
      rsum_const]
    have : (n : Int) = ((n - 1 : Nat) : Int) + 1 := by omega
    rw [this, Int.add_mul, Int.one_mul, Int.add_comm]
  have hCS := cauchy_schwarz (2 ^ n + H n) (fun i => Z (2 ^ n) n ((i : Int) - H n))
  rw [hsum] at hCS
  unfold Ttot
  have : ((n : Int) * D0 (2 ^ n)) ^ 2 = (n : Int) ^ 2 * D0 (2 ^ n) ^ 2 := by grind
  rw [← this]
  exact hCS

/-! ## The front energy -/

/-- `cnt m v = #{j ≤ m : v ≤ 2^j}`, the number of shifts reaching from `-v` into `[0, ∞)`. -/
def cnt (m v : Nat) : Int := rsum (m + 1) (fun j => if v ≤ 2 ^ j then 1 else 0)

theorem cnt_nonneg (m v : Nat) : 0 ≤ cnt m v :=
  rsum_nonneg _ (fun _ _ => by split <;> omega)

theorem cnt_succ (m v : Nat) : cnt (m + 1) v = cnt m v + if v ≤ 2 ^ (m + 1) then 1 else 0 :=
  rsum_succ _ _

theorem cnt_big (m v : Nat) (hv : 2 ^ m < v) : cnt m v = 0 := by
  unfold cnt
  rw [rsum_congr _ (g := fun _ => 0) (fun j hj => by
    have : 2 ^ j ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) (by omega)
    simp [show ¬ (v ≤ 2 ^ j) by omega]), rsum_const]
  simp

/-- `Σ_{v=1}^{2^m} cnt m v = 2^(m+1) - 1` and `Σ_{v=1}^{2^m} (cnt m v)² = 6 · 2^m - 2m - 5`. -/
theorem cnt_sums (m : Nat) :
    rsum (2 ^ m) (fun i => cnt m (i + 1)) = 2 ^ (m + 1) - 1 ∧
    rsum (2 ^ m) (fun i => cnt m (i + 1) ^ 2) = 6 * 2 ^ m - 2 * m - 5 := by
  induction m with
  | zero => simp [cnt, rsum_succ]
  | succ m ih =>
    have e : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [Nat.pow_succ]; omega
    have lo : ∀ i, i < 2 ^ m → cnt (m + 1) (i + 1) = cnt m (i + 1) + 1 := by
      intro i hi; rw [cnt_succ]; simp only [show i + 1 ≤ 2 ^ (m + 1) by omega, ite_true]
    have hi : ∀ i, i < 2 ^ m → cnt (m + 1) (2 ^ m + i + 1) = 1 := by
      intro i hi
      rw [cnt_succ, cnt_big _ _ (by omega)]
      simp only [show 2 ^ m + i + 1 ≤ 2 ^ (m + 1) by omega, ite_true]
      rfl
    rw [e, rsum_split, rsum_split]
    have a1 : rsum (2 ^ m) (fun i => cnt (m + 1) (i + 1))
        = rsum (2 ^ m) (fun i => cnt m (i + 1)) + rsum (2 ^ m) (fun _ => 1) := by
      rw [← rsum_add]; exact rsum_congr _ lo
    have a2 : rsum (2 ^ m) (fun i => cnt (m + 1) (2 ^ m + i + 1)) = rsum (2 ^ m) (fun _ => 1) :=
      rsum_congr _ hi
    have b1 : rsum (2 ^ m) (fun i => cnt (m + 1) (i + 1) ^ 2)
        = rsum (2 ^ m) (fun i => cnt m (i + 1) ^ 2)
          + rsum (2 ^ m) (fun i => 2 * cnt m (i + 1)) + rsum (2 ^ m) (fun _ => 1) := by
      rw [← rsum_add, ← rsum_add]
      exact rsum_congr _ (fun i h => by rw [lo i h]; grind)
    have b2 : rsum (2 ^ m) (fun i => cnt (m + 1) (2 ^ m + i + 1) ^ 2)
        = rsum (2 ^ m) (fun _ => 1) :=
      rsum_congr _ (fun i h => by rw [hi i h]; rfl)
    rw [a1, a2, b1, b2, rsum_mul, ih.1, ih.2, rsum_const]
    push_cast
    rw [Int.pow_succ, Int.pow_succ]
    constructor <;> omega

/-- The front shifted sums: `|Z(-v)| ≤ cnt (n-2) v` for `1 ≤ v ≤ H`. -/
theorem Z_front (n i : Nat) (hn : 2 ≤ n) (hi : i < H n) :
    Z (2 ^ n) n ((i : Int) - H n) ^ 2 ≤ cnt (n - 2) (H n - i) ^ 2 := by
  have hb : -cnt (n - 2) (H n - i) ≤ Z (2 ^ n) n ((i : Int) - H n) ∧
      Z (2 ^ n) n ((i : Int) - H n) ≤ cnt (n - 2) (H n - i) := by
    rw [Z_eq]
    have h0 : zext (2 ^ n) ((i : Int) - H n) = 0 := by
      unfold zext; split <;> first | rfl | omega
    rw [h0, Int.zero_add, show n - 1 = n - 2 + 1 by omega]
    unfold cnt
    have term : ∀ j, -(if H n - i ≤ 2 ^ j then (1 : Int) else 0)
          ≤ zext (2 ^ n) ((i : Int) - H n + ((2 ^ j : Nat) : Int)) ∧
        zext (2 ^ n) ((i : Int) - H n + ((2 ^ j : Nat) : Int))
          ≤ (if H n - i ≤ 2 ^ j then (1 : Int) else 0) := by
      intro j
      have := zext_bound (2 ^ n) ((i : Int) - H n + ((2 ^ j : Nat) : Int))
      split
      · omega
      · have : zext (2 ^ n) ((i : Int) - H n + ((2 ^ j : Nat) : Int)) = 0 := by
          unfold zext; split <;> first | rfl | omega
        omega
    constructor
    · have := rsum_le_rsum (n - 2 + 1)
        (f := fun j => -(if H n - i ≤ 2 ^ j then (1 : Int) else 0)) (fun j _ => (term j).1)
      rw [show (fun j => -(if H n - i ≤ 2 ^ j then (1 : Int) else 0))
          = (fun j => (-1) * (if H n - i ≤ 2 ^ j then (1 : Int) else 0)) from
          funext fun j => by omega, rsum_mul] at this
      omega
    · exact rsum_le_rsum _ (fun j _ => (term j).2)
  have hc := cnt_nonneg (n - 2) (H n - i)
  generalize Z (2 ^ n) n ((i : Int) - H n) = x at hb
  generalize cnt (n - 2) (H n - i) = c at hb hc
  have := Int.mul_nonneg (show 0 ≤ c - x by omega) (show 0 ≤ c + x by omega)
  grind

/-- Reversing a range: `Σ_{i<k} f(k - i) = Σ_{i<k} f(i + 1)`. -/
theorem rsum_reflect (k : Nat) (f : Nat → Int) :
    rsum k (fun i => f (k - i)) = rsum k (fun i => f (i + 1)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have e : rsum (k + 1) (fun i => f (k + 1 - i)) = f (k + 1) + rsum k (fun i => f (k - i)) := by
      have := rsum_split 1 k (fun i => f (k + 1 - i))
      rw [Nat.add_comm 1 k] at this
      rw [this]
      simp only [rsum_succ, rsum_zero, Int.zero_add, Nat.sub_zero]
      congr 1
      exact rsum_congr _ (fun i _ => by congr 1; omega)
    rw [e, ih, rsum_succ]
    omega

/-- **Front energy bound**: the shifted sums at `-H ≤ u < 0` carry at most `(3/2) · 2^n`
of the total energy: `0 ≤ Ttot - Esrc` and `2 (Ttot - Esrc) ≤ 3 · 2^n`. -/
theorem F_bound (n : Nat) (hn : 2 ≤ n) :
    0 ≤ Ttot (2 ^ n) n - Esrc n ∧ 2 * (Ttot (2 ^ n) n - Esrc n) ≤ 3 * 2 ^ n := by
  have hH : 2 ^ n = 4 * 2 ^ (n - 2) := by
    rw [show n = n - 2 + 2 by omega, Nat.pow_add]; simp; omega
  have hH' : H n = 2 ^ (n - 2) := by unfold H; omega
  have split : Ttot (2 ^ n) n
      = rsum (H n) (fun i => Z (2 ^ n) n ((i : Int) - H n) ^ 2) + Esrc n := by
    unfold Ttot Esrc
    rw [Nat.add_comm, rsum_split]
    congr 1
    exact rsum_congr _ (fun i _ => by congr 2; omega)
  have hfront : rsum (H n) (fun i => Z (2 ^ n) n ((i : Int) - H n) ^ 2)
      ≤ 6 * 2 ^ (n - 2) - 2 * (n - 2 : Nat) - 5 := by
    have h1 := rsum_le_rsum (H n) (fun i hi => Z_front n i hn hi)
    have h2 := rsum_reflect (H n) (fun v => cnt (n - 2) v ^ 2)
    have h3 := (cnt_sums (n - 2)).2
    rw [← hH'] at h3
    omega
  have h0 := rsum_nonneg (H n) (f := fun i => Z (2 ^ n) n ((i : Int) - H n) ^ 2)
    (fun _ _ => Int.sq_nonneg _)
  have hc : ((2 ^ n : Nat) : Int) = 4 * ((2 ^ (n - 2) : Nat) : Int) := by rw [hH]; push_cast; rfl
  push_cast at hc
  rw [split]
  omega

/-! ## The main theorem -/

/-- The final integer arithmetic. -/
theorem arith (k n M N a Y E : Int) (hk : 1 ≤ k) (hn : 4 * k ≤ n) (hM : 1 ≤ M) (hN : N < 2 * M)
    (ha : M + 1 ≤ k * a) (hY : n * a - N ≤ Y) (hYE : Y ^ 2 ≤ M * E)
    (hE : k ^ 2 * E * 8 ≤ N * n ^ 2) : False := by
  -- `2kY > nM > 0`
  have h1 : n * M < 2 * k * Y := by
    have : n * (M + 1) ≤ n * (k * a) := Int.mul_le_mul_of_nonneg_left ha (by omega)
    have : k * (n * a - N) ≤ k * Y := Int.mul_le_mul_of_nonneg_left hY (by omega)
    have : 2 * k * N < 4 * k * M := by
      have := Int.mul_lt_mul_of_pos_left hN (show 0 < 2 * k by omega); grind
    have : 4 * k * M ≤ n * M := Int.mul_le_mul_of_nonneg_right hn (by omega)
    grind
  have hnM : 0 ≤ n * M := Int.mul_nonneg (by omega) (by omega)
  have h2 := Int.mul_self_lt_mul_self hnM h1
  -- `8 k² Y² ≤ M N n² < 2 M² n²`
  have h3 : 8 * k ^ 2 * Y ^ 2 ≤ M * (N * n ^ 2) := by
    have := Int.mul_le_mul_of_nonneg_left hYE (show 0 ≤ 8 * k ^ 2 by
      have := Int.sq_nonneg k; omega)
    have := Int.mul_le_mul_of_nonneg_left hE (show 0 ≤ M by omega)
    grind
  have h4 : M * (N * n ^ 2) < M * (2 * M * n ^ 2) := by
    apply Int.mul_lt_mul_of_pos_left _ (by omega)
    apply Int.mul_lt_mul_of_pos_right hN
    have : 0 < n := by omega
    exact Int.pow_pos this
  grind

/-- **Problem 2 from the source-energy estimate.** If the source energy satisfies
`Esrc n = o(2^n n²)`, in the integer form: for every `k > 0`, eventually
`8 k² · Esrc n ≤ 2^n · n²`, then the center column of rule 30 has density `1/2`. -/
theorem problem2_of_source_energy
    (hSE : ∀ k : Nat, 0 < k → ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
      (k : Int) ^ 2 * Esrc n * 8 ≤ 2 ^ n * (n : Int) ^ 2) :
    Problem2 := by
  intro k hk
  obtain ⟨n0, hn0⟩ := hSE k hk
  refine ⟨2 ^ (n0 + 4 * k + 2) + 1, fun M hM => ?_⟩
  -- the dyadic scale of `M`
  have hM1 : M - 1 ≠ 0 := by have := Nat.one_le_two_pow (n := n0 + 4 * k + 2); omega
  let n := (M - 1).log2 + 1
  have hlo : 2 ^ (n - 1) ≤ M - 1 := Nat.log2_self_le hM1
  have hhi : M - 1 < 2 ^ n := Nat.lt_log2_self
  have hc : n0 + 4 * k + 2 ≤ n - 1 := (Nat.le_log2 hM1).2 (by omega)
  have hpow : (2 : Int) ^ n = 2 * 2 ^ (n - 1) := by
    rw [← Int.pow_succ', show n - 1 + 1 = n by omega]
  have hlo' : ((2 ^ (n - 1) : Nat) : Int) ≤ M - 1 := by omega
  have hhi' : (M : Int) ≤ ((2 ^ n : Nat) : Int) := by omega
  push_cast at hlo' hhi'
  -- the estimate at scale `n`
  have hE := hn0 n (by omega)
  have hclose := sum_Z_close n M (by omega) (by omega)
  have hCS := cauchy_schwarz M (fun u => Z (2 ^ n) n u)
  have hmono : rsum M (fun u => Z (2 ^ n) n u ^ 2) ≤ Esrc n :=
    rsum_mono_len (by omega) (fun i => Int.sq_nonneg _)
  have hCS' : rsum M (fun u => Z (2 ^ n) n u) ^ 2 ≤ M * Esrc n :=
    Int.le_trans hCS (Int.mul_le_mul_of_nonneg_left hmono (by omega))
  have hD := sum_z M
  -- conclude by contradiction, according to the sign of `D0 M`
  apply Nat.le_of_not_lt
  intro hlt
  rcases Int.natAbs_eq (2 * (blackCount M : Int) - M) with h | h
  · refine arith k n M (2 ^ n) ((2 * (blackCount M : Int) - M).natAbs)
      (-rsum M (fun u => Z (2 ^ n) n u)) (Esrc n) (by omega) (by omega) (by omega) (by omega)
      (by omega) ?_ (by rw [show ∀ x : Int, (-x) ^ 2 = x ^ 2 from fun x => by grind]; exact hCS') hE
    have : (n : Int) * D0 M = n * -((2 * (blackCount M : Int) - M).natAbs : Int) := by
      rw [hD, ← h]; congr 1; omega
    rw [Int.mul_neg] at this
    omega
  · refine arith k n M (2 ^ n) ((2 * (blackCount M : Int) - M).natAbs)
      (rsum M (fun u => Z (2 ^ n) n u)) (Esrc n) (by omega) (by omega) (by omega) (by omega)
      (by omega) ?_ hCS' hE
    have : (n : Int) * D0 M = n * ((2 * (blackCount M : Int) - M).natAbs : Int) := by
      rw [hD]; congr 1; omega
    omega

/-! ## Trivial `2^n n²` energy bound, direct source-energy van der Corput inequality, and equivalence with total-energy `o(2^n n²)` -/

/-- **Pointwise Bound on Shifted Sums (`Z_bounds`):**
for all `N, n : Nat` with `1 ≤ n` and `u : Int`, `-(n : Int) ≤ Z N n u ∧ Z N n u ≤ (n : Int)`. -/
theorem Z_bounds (N n : Nat) (hn : 1 ≤ n) (u : Int) :
    -(n : Int) ≤ Z N n u ∧ Z N n u ≤ (n : Int) := by
  rw [Z_eq]
  have h0 := zext_bound N u
  have hr := rsum_abs_le (n - 1) (f := fun j => zext N (u + ((2 ^ j : Nat) : Int)))
    (fun j => zext_bound N _)
  omega

/-- **Pointwise Square Bound on Shifted Sums (`Z_sq_le_sq`):**
for all `N, n : Nat` with `1 ≤ n` and `u : Int`, `Z N n u ^ 2 ≤ (n : Int) ^ 2`. -/
theorem Z_sq_le_sq (N n : Nat) (hn : 1 ≤ n) (u : Int) :
    Z N n u ^ 2 ≤ (n : Int) ^ 2 := by
  have hb := Z_bounds N n hn u
  generalize Z N n u = x at hb
  have h1 : 0 ≤ (n : Int) - x := by omega
  have h2 : 0 ≤ (n : Int) + x := by omega
  have hprod := Int.mul_nonneg h1 h2
  grind

/-- **Nonnegativity of Source Energy (`Esrc_nonneg`):**
for every `n : Nat`, `0 ≤ Esrc n`. -/
theorem Esrc_nonneg (n : Nat) : 0 ≤ Esrc n :=
  rsum_nonneg (2 ^ n) (fun _ _ => Int.sq_nonneg _)

/-- **Nonnegativity of Total Energy (`Ttot_nonneg`):**
for every `N, n : Nat`, `0 ≤ Ttot N n`. -/
theorem Ttot_nonneg (N n : Nat) : 0 ≤ Ttot N n :=
  rsum_nonneg (N + H n) (fun _ _ => Int.sq_nonneg _)

/-- **Sharp Trivial Upper Bound on Source Energy (`Esrc_le_trivial`):**
for every `n ≥ 1`, `Esrc n ≤ 2 ^ n * (n : Int) ^ 2`. -/
theorem Esrc_le_trivial (n : Nat) (hn : 1 ≤ n) :
    Esrc n ≤ 2 ^ n * (n : Int) ^ 2 := by
  unfold Esrc
  have hle := rsum_le_rsum (2 ^ n) (f := fun u => Z (2 ^ n) n u ^ 2)
    (g := fun _ => (n : Int) ^ 2) (fun u _ => Z_sq_le_sq (2 ^ n) n hn u)
  rw [rsum_const] at hle
  exact hle

/-- **Source Energy Is Bounded Above by Total Energy (`Esrc_le_Ttot`):**
for every `n ≥ 2`, `Esrc n ≤ Ttot (2 ^ n) n`. -/
theorem Esrc_le_Ttot (n : Nat) (hn : 2 ≤ n) : Esrc n ≤ Ttot (2 ^ n) n := by
  have hf := (F_bound n hn).1
  omega

/-- **Exact Dyadic Support Length Identity (`four_mul_add_H`):**
for every `n ≥ 2`, `4 * (2 ^ n + H n) = 5 * 2 ^ n`. -/
theorem four_mul_add_H (n : Nat) (hn : 2 ≤ n) :
    4 * (2 ^ n + H n) = 5 * 2 ^ n := by
  have hH : 2 ^ n = 4 * 2 ^ (n - 2) := by
    rw [show n = n - 2 + 2 by omega, Nat.pow_add]; simp; omega
  unfold H
  omega

/-- **Direct Source-Energy van der Corput Discrepancy Bound (`vdc_source_energy`):**
for every `n ≥ 2`, `8 * (n : Int) ^ 2 * D0 (2 ^ n) ^ 2 ≤ 5 * 2 ^ n * (2 * Esrc n + 3 * 2 ^ n)`. -/
private theorem eight_mul_mul (A B : Int) : 8 * (A * B) = (4 * A) * (2 * B) := by grind

theorem vdc_source_energy (n : Nat) (hn : 2 ≤ n) :
    8 * (n : Int) ^ 2 * D0 (2 ^ n) ^ 2 ≤ 5 * 2 ^ n * (2 * Esrc n + 3 * 2 ^ n) := by
  have hv := vdc n hn
  have hf := (F_bound n hn).2
  have h4 := four_mul_add_H n hn
  have h4_int : (4 : Int) * ((2 ^ n + H n : Nat) : Int) = 5 * (2 : Int) ^ n := by
    have : ((4 * (2 ^ n + H n) : Nat) : Int) = ((5 * 2 ^ n : Nat) : Int) := congrArg Int.ofNat h4
    push_cast at this
    exact this
  have hpow_pos : (0 : Int) < (2 : Int) ^ n := Int.pow_pos (by decide : (0 : Int) < 2)
  have hmul1 := Int.mul_le_mul_of_nonneg_left hv (show (0 : Int) ≤ 8 by decide)
  rw [eight_mul_mul ((2 ^ n + H n : Nat) : Int) (Ttot (2 ^ n) n), h4_int, ← Int.mul_assoc 8 ((n : Int) ^ 2) (D0 (2 ^ n) ^ 2)] at hmul1
  have h2T : 2 * Ttot (2 ^ n) n ≤ 2 * Esrc n + 3 * (2 : Int) ^ n := by omega
  have hmul2 := Int.mul_le_mul_of_nonneg_left h2T (show (0 : Int) ≤ 5 * (2 : Int) ^ n by omega)
  exact Int.le_trans hmul1 hmul2

/-- The integer `o(2^n n²)` hypothesis on the source energy `Esrc n`. -/
def SourceEnergySmallO : Prop :=
  ∀ k : Nat, 0 < k → ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
    (k : Int) ^ 2 * Esrc n * 8 ≤ 2 ^ n * (n : Int) ^ 2

/-- The integer `o(2^n n²)` hypothesis on the total energy `Ttot (2 ^ n) n`. -/
def TotalEnergySmallO : Prop :=
  ∀ k : Nat, 0 < k → ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
    (k : Int) ^ 2 * Ttot (2 ^ n) n * 8 ≤ 2 ^ n * (n : Int) ^ 2

/-- **Equivalence of Source-Energy and Total-Energy Small-O Conditions (`source_energy_o_iff_total_energy_o`):**
`SourceEnergySmallO ↔ TotalEnergySmallO`. -/
theorem source_energy_o_iff_total_energy_o :
    SourceEnergySmallO ↔ TotalEnergySmallO := by
  constructor
  · intro hS k hk
    obtain ⟨n0, hn0⟩ := hS (2 * k) (by omega)
    refine ⟨n0 + 5 * k + 2, fun n hn => ?_⟩
    have hn2 : 2 ≤ n := by omega
    have hE := hn0 n (by omega)
    have hf := (F_bound n hn2).2
    have hkn : (5 * k : Int) ≤ (n : Int) := by omega
    have hk_pos : (0 : Int) ≤ k := by omega
    have hsq : 25 * (k : Int) ^ 2 ≤ (n : Int) ^ 2 := by
      have := Int.mul_le_mul hkn hkn (by omega) (by omega)
      grind
    have hpow_pos : (0 : Int) ≤ 2 ^ n := Int.le_of_lt (Int.pow_pos (by decide : (0 : Int) < 2))
    have h1 : (k : Int) ^ 2 * (2 * Esrc n) * 8 ≤ 2 * (2 ^ n * (n : Int) ^ 2) := by
      have := Int.mul_le_mul_of_nonneg_left hE (show (0 : Int) ≤ 1 by decide)
      grind
    have h2 : (k : Int) ^ 2 * (3 * 2 ^ n) * 8 ≤ 2 ^ n * (n : Int) ^ 2 := by
      have := Int.mul_le_mul_of_nonneg_left hsq hpow_pos
      grind
    have h3 : (k : Int) ^ 2 * (2 * Ttot (2 ^ n) n) * 8 ≤
        (k : Int) ^ 2 * (2 * Esrc n + 3 * 2 ^ n) * 8 := by
      have : (0 : Int) ≤ (k : Int) ^ 2 * 8 := by
        have := Int.sq_nonneg (k : Int); omega
      have := Int.mul_le_mul_of_nonneg_left hf this
      grind
    grind
  · intro hT k hk
    obtain ⟨n0, hn0⟩ := hT k hk
    refine ⟨n0 + 2, fun n hn => ?_⟩
    have hle := Esrc_le_Ttot n (by omega)
    have hTn := hn0 n (by omega)
    have hk2 : (0 : Int) ≤ (k : Int) ^ 2 * 8 := by
      have := Int.sq_nonneg (k : Int); omega
    have := Int.mul_le_mul_of_nonneg_left hle hk2
    grind

/-- **Problem 2 from the Total-Energy Estimate (`problem2_of_total_energy`):**
if `Ttot (2 ^ n) n = o(2^n n²)` (`TotalEnergySmallO`), then `Problem2` holds. -/
theorem problem2_of_total_energy (hTE : TotalEnergySmallO) : Problem2 :=
  problem2_of_source_energy (source_energy_o_iff_total_energy_o.mpr hTE)

end Rule30SourceEnergy
end Ruliology.CellularAutomata
