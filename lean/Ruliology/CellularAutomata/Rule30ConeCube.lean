module

public import Ruliology.CellularAutomata.Rule30RightPeriods

@[expose] public section

/-!
# Rule 30: the binary cube in the single-cell cone

Write `f d u = cell u (u - d)` for the right diagonals of the rule 30 cone (`f d = R d` of
`Rule30Diagonals`). For `j ≥ 0` let `d j` be the depth of the first black cell strictly inside
row `2^j`, read leftward from its right edge:

  `d j = min {d ≥ 1 : cell (2^j) (2^j - d) = true}`.

Equivalently (`per_below_d`, `not_per_d`), `d j` is the first depth at which the diagonals stop
repeating with period `2^j`.

Results.
1. `fresh_digit`: `f (d j) (z + 2^j) = !f (d j) z` for every `z`; and `f (d j)` has period
   `2^(j+1)` (`period_d`).
2. `cube_injective`, `cube_surjective`: for every `m` and `A`, the map
   `u ↦ (cell (u + d j) u)_{j < m}` is a bijection from the `2^m` columns `A ≤ u < A + 2^m`
   onto `Fin m → Bool`. Each binary word of length `m` is read exactly once along the tilted
   transversal `(u + d 0, u), …, (u + d (m-1), u)`.
3. `cube_count`: these `m · 2^m` cells contain exactly `m · 2^(m-1)` black cells.

Proof. The read at level `j` is `Y_j u = f (d j) (u + d j)`. It is complemented by `u ↦ u + 2^j`
and repeats with period `2^(j+1)`. If `u < v` give the same word, write `v - u = 2^j (2q + 1)`
with `j < m`; then `Y_j v = Y_j (u + 2^j) = !Y_j u`. Surjectivity: given a word, choose `u` for
its first `m - 1` letters, then `u` or `u + 2^(m-1)` fixes the last letter without changing the
others.
-/

namespace Ruliology.CellularAutomata
namespace Rule30ConeCube

open Rule30Jen Rule30Diagonals Rule30RightPeriods

/-! ## The doubling depths -/

/-- The right diagonals: `f d u = cell u (u - d)`. -/
def f (d u : Nat) : Bool := cell u ((u : Int) - d)

theorem f_eq_R (d u : Nat) : f d u = R d u := rfl

/-- The first `t ≥ a` with `p t`, searching `k` values. -/
def firstFrom (p : Nat → Bool) (a : Nat) : Nat → Nat
  | 0 => a
  | k + 1 => if p a then a else firstFrom p (a + 1) k

theorem firstFrom_spec (p : Nat → Bool) : ∀ (k a t : Nat), a ≤ t → t < a + k → p t = true →
    a ≤ firstFrom p a k ∧ firstFrom p a k ≤ t ∧ p (firstFrom p a k) = true ∧
      ∀ u, a ≤ u → u < firstFrom p a k → p u = false := by
  intro k
  induction k with
  | zero => intro a t h1 h2; omega
  | succ k ih =>
    intro a t h1 h2 ht
    unfold firstFrom
    split
    · next hp => exact ⟨Nat.le_refl _, h1, hp, fun u h1 h2 => by omega⟩
    · next hp =>
        have hat : a ≠ t := fun e => hp (e ▸ ht)
        obtain ⟨A, B, C, D⟩ := ih (a + 1) t (by omega) (by omega) ht
        refine ⟨by omega, B, C, fun u hu1 hu2 => ?_⟩
        by_cases hu : u = a
        · subst hu; simpa using hp
        · exact D u (by omega) hu2

/-- `d j`: the depth of the first black cell left of the right edge of row `2^j`,
`min {d ≥ 1 : cell (2^j) (2^j - d) = true}`. -/
def d (j : Nat) : Nat := firstFrom (fun i => f (i + 1) (2 ^ j)) 0 (2 ^ (j + 1)) + 1

/-- Row `2^j` has a black cell at some depth `1 ≤ i ≤ 2^(j+1)`. -/
theorem exists_black_depth (j : Nat) : ∃ i, i < 2 ^ (j + 1) ∧ f (i + 1) (2 ^ j) = true := by
  refine Classical.byContradiction fun hcon => ?_
  have hp : Per (2 ^ (j + 1)) (2 ^ j) := by
    refine (per_iff_gap j (2 ^ (j + 1))).2 fun i h1 h2 => ?_
    cases h : R i (2 ^ j)
    · rfl
    · exact absurd ⟨i - 1, by omega, by rw [show i - 1 + 1 = i by omega]; exact h⟩ hcon
  exact not_per_small (Nat.one_le_two_pow) (Nat.le_refl _) hp

theorem d_spec (j : Nat) : 1 ≤ d j ∧ f (d j) (2 ^ j) = true ∧
    ∀ i, 1 ≤ i → i < d j → f i (2 ^ j) = false := by
  obtain ⟨i, hi, hb⟩ := exists_black_depth j
  obtain ⟨_, _, C, D⟩ := firstFrom_spec (fun i => f (i + 1) (2 ^ j)) (2 ^ (j + 1)) 0 i
    (Nat.zero_le _) (by omega) hb
  refine ⟨by unfold d; omega, C, fun i h1 h2 => ?_⟩
  have := D (i - 1) (Nat.zero_le _) (by unfold d at h2; omega)
  rwa [show i - 1 + 1 = i by omega] at this

/-- Below depth `d j` every diagonal repeats with period `2^j`. -/
theorem per_below_d (j : Nat) : Per (d j - 1) (2 ^ j) :=
  (per_iff_gap j (d j - 1)).2 fun i h1 h2 => (d_spec j).2.2 i h1 (by omega)

/-- Diagonal `d j` does not repeat with period `2^j`. -/
theorem not_per_d (j : Nat) : ¬ Per (d j) (2 ^ j) := by
  intro h
  have := ((per_iff_gap j (d j)).1 h) (d j) (d_spec j).1 (Nat.le_refl _)
  rw [← f_eq_R, (d_spec j).2.1] at this
  exact Bool.noConfusion this

/-- **Fresh digit**: shifting by `2^j` complements diagonal `d j`. -/
theorem fresh_digit (j : Nat) : ∀ z, f (d j) (z + 2 ^ j) = !f (d j) z := by
  have e : d j - 1 + 1 = d j := by have := (d_spec j).1; omega
  have h := antiperiod (per_below_d j) (by rw [e]; exact not_per_d j)
  intro z
  have := h z
  rw [e] at this
  exact this

/-- Diagonal `d j` repeats with period `2^(j+1)`. -/
theorem period_d (j : Nat) : ∀ z, f (d j) (z + 2 ^ (j + 1)) = f (d j) z := by
  have e : d j - 1 + 1 = d j := by have := (d_spec j).1; omega
  have h := per_step (per_below_d j)
  rw [e] at h
  exact h

/-! ## The reads along the transversal -/

/-- The read at level `j` in column `u`: the cell at time `u + d j`, position `u`. -/
def Y (j u : Nat) : Bool := cell (u + d j) u

theorem Y_eq (j u : Nat) : Y j u = f (d j) (u + d j) := by
  unfold Y f; exact cell_congr (by omega)

theorem Y_flip (j u : Nat) : Y j (u + 2 ^ j) = !Y j u := by
  rw [Y_eq, Y_eq, show u + 2 ^ j + d j = u + d j + 2 ^ j by omega, fresh_digit]

theorem Y_period (j u q : Nat) : Y j (u + 2 ^ (j + 1) * q) = Y j u := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc, Y_eq, show u + 2 ^ (j + 1) * q + 2 ^ (j + 1) + d j
      = u + 2 ^ (j + 1) * q + d j + 2 ^ (j + 1) by omega, period_d, ← Y_eq, ih]

/-- Every positive integer is `2^j (2q + 1)`. -/
theorem two_adic (n : Nat) : ∀ δ, 0 < δ → δ ≤ n → ∃ j q, δ = 2 ^ j * (2 * q + 1) := by
  induction n with
  | zero => intro δ h1 h2; omega
  | succ n ih =>
    intro δ h1 h2
    rcases Nat.mod_two_eq_zero_or_one δ with h | h
    · obtain ⟨j, q, hq⟩ := ih (δ / 2) (by omega) (by omega)
      exact ⟨j + 1, q, by rw [Nat.pow_succ]; rw [Nat.mul_comm (2 ^ j) 2, Nat.mul_assoc, ← hq]; omega⟩
    · exact ⟨0, δ / 2, by simp; omega⟩

/-- Two columns less than `2^m` apart differ in one of the first `m` reads. -/
theorem reads_differ (m u v : Nat) (huv : u < v) (hv : v < u + 2 ^ m) :
    ∃ j, j < m ∧ Y j v = !Y j u := by
  obtain ⟨j, q, hq⟩ := two_adic (v - u) (v - u) (by omega) (Nat.le_refl _)
  have hj : j < m := by
    refine Nat.lt_of_not_le fun hjm => ?_
    have : 2 ^ m ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) hjm
    have : 2 ^ j ≤ v - u := by rw [hq]; exact Nat.le_mul_of_pos_right _ (by omega)
    omega
  refine ⟨j, hj, ?_⟩
  have : v = u + 2 ^ j + 2 ^ (j + 1) * q := by
    rw [Nat.pow_succ]
    have : v - u = 2 ^ j + 2 ^ j * 2 * q := by rw [hq, Nat.mul_add, Nat.mul_one, Nat.mul_assoc, Nat.add_comm]
    omega
  rw [this, Y_period, Y_flip]

/-! ## The cube -/

/-- **The cube, injectivity**: the `m` reads `cell (u + d j) u`, `j < m`, separate any two
columns `A ≤ u, v < A + 2^m`. -/
theorem cube_injective (m A u v : Nat) (hu : A ≤ u ∧ u < A + 2 ^ m) (hv : A ≤ v ∧ v < A + 2 ^ m)
    (h : (fun j : Fin m => cell (u + d j) u) = (fun j : Fin m => cell (v + d j) v)) : u = v := by
  have key : ∀ a b, a < b → b < a + 2 ^ m →
      (fun j : Fin m => cell (a + d j) a) = (fun j : Fin m => cell (b + d j) b) → False := by
    intro a b hab hb hfun
    obtain ⟨j, hj, hY⟩ := reads_differ m a b hab hb
    have := congrFun hfun ⟨j, hj⟩
    change Y j a = Y j b at this
    rw [hY] at this
    cases hYa : Y j a <;> rw [hYa] at this <;> exact Bool.noConfusion this
  rcases Nat.lt_trichotomy u v with h' | h' | h'
  · exact (key u v h' (by omega) h).elim
  · exact h'
  · exact (key v u h' (by omega) h.symm).elim

/-- **The cube, surjectivity**: every binary word of length `m` is read in some column
`A ≤ u < A + 2^m`. -/
theorem cube_surjective (m A : Nat) (w : Fin m → Bool) :
    ∃ u, A ≤ u ∧ u < A + 2 ^ m ∧ (fun j : Fin m => cell (u + d j) u) = w := by
  have gen : ∀ m (w : Nat → Bool), ∃ u, A ≤ u ∧ u < A + 2 ^ m ∧ ∀ j, j < m → Y j u = w j := by
    intro m w
    induction m with
    | zero => exact ⟨A, Nat.le_refl _, by simp, fun j hj => by omega⟩
    | succ m ih =>
      obtain ⟨u, h1, h2, h3⟩ := ih
      have hp : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [Nat.pow_succ]; omega
      have low : ∀ j, j < m → Y j (u + 2 ^ m) = Y j u := by
        intro j hj
        have : 2 ^ m = 2 ^ (j + 1) * 2 ^ (m - (j + 1)) := by
          rw [← Nat.pow_add]; congr 1; omega
        rw [this, Y_period]
      by_cases hm : Y m u = w m
      · exact ⟨u, h1, by omega, fun j hj => by
          rcases Nat.lt_or_ge j m with hjm | hjm
          · exact h3 j hjm
          · rw [show j = m by omega]; exact hm⟩
      · refine ⟨u + 2 ^ m, by omega, by omega, fun j hj => ?_⟩
        rcases Nat.lt_or_ge j m with hjm | hjm
        · rw [low j hjm]; exact h3 j hjm
        · rw [show j = m by omega, Y_flip]
          cases hY : Y m u <;> cases hw : w m <;> simp_all
  obtain ⟨u, h1, h2, h3⟩ := gen m (fun j => if h : j < m then w ⟨j, h⟩ else false)
  refine ⟨u, h1, h2, funext fun j => ?_⟩
  have := h3 j.val j.isLt
  simp only [j.isLt, dite_true] at this
  exact this

/-! ## Counting black cells -/

/-- A window of length `2^(j+1) q` holds exactly `2^j q` black reads at level `j`. -/
theorem cnt_Y (j A q : Nat) : cnt (Y j) A (2 ^ (j + 1) * q) = 2 ^ j * q := by
  induction q generalizing A with
  | zero => rfl
  | succ q ih =>
    rw [Nat.mul_succ, cnt_add, ih, Nat.pow_succ, show 2 ^ j * 2 = 2 ^ j + 2 ^ j by omega, cnt_add]
    have := cnt_compl (fun s => Y_flip j s) (A + (2 ^ j + 2 ^ j) * q) (2 ^ j)
    rw [show (2 ^ j + 2 ^ j) * q = 2 ^ (j + 1) * q by rw [Nat.pow_succ]; congr 1; omega] at this ⊢
    rw [Nat.mul_succ]
    omega

/-- `nsum k g = g 0 + ⋯ + g (k - 1)`. -/
def nsum : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | k + 1, g => nsum k g + g k

/-- The number of black cells among the reads `cell (u + d j) u`, `A ≤ u < A + 2^m`, `j < m`. -/
def cubeBlack (m A : Nat) : Nat := nsum m (fun j => cnt (Y j) A (2 ^ m))

/-- **Exact count**: the `m · 2^m` cells of the transversal over `2^m` consecutive columns
contain exactly `m · 2^(m-1)` black cells. -/
theorem cube_count (m A : Nat) : cubeBlack m A = m * 2 ^ (m - 1) := by
  have each : ∀ j, j < m → cnt (Y j) A (2 ^ m) = 2 ^ (m - 1) := by
    intro j hj
    have e : 2 ^ m = 2 ^ (j + 1) * 2 ^ (m - (j + 1)) := by rw [← Nat.pow_add]; congr 1; omega
    rw [e, cnt_Y, ← Nat.pow_add]; congr 1; omega
  unfold cubeBlack
  have : ∀ k, k ≤ m → nsum k (fun j => cnt (Y j) A (2 ^ m)) = k * 2 ^ (m - 1) := by
    intro k
    induction k with
    | zero => intro _; simp [nsum]
    | succ k ih =>
      intro hk
      show nsum k _ + _ = _
      rw [ih (by omega)]
      show _ + cnt (Y k) A (2 ^ m) = _
      rw [each k (by omega), Nat.succ_mul]
  exact this m (Nat.le_refl _)

/-! ## Doubling-depth bounds, injectivity of `d`, higher-dyadic invariance, and unique cube coordinates -/

/-- **Doubling-Depth Upper and Lower Bounds (`d_bounds`):**
for every `j : Nat`, `1 ≤ d j ∧ d j ≤ 2 ^ (j + 1)`. -/
theorem d_bounds (j : Nat) : 1 ≤ d j ∧ d j ≤ 2 ^ (j + 1) := by
  obtain ⟨i, hi, hb⟩ := exists_black_depth j
  obtain ⟨_, hle, _, _⟩ := firstFrom_spec (fun i => f (i + 1) (2 ^ j)) (2 ^ (j + 1)) 0 i
    (Nat.zero_le _) (by omega) hb
  unfold d
  omega

/-- **Higher-Dyadic Invariance of Diagonal `d j₁` (`f_d_add_two_pow_of_lt`):**
for `j₁ < j₂` and every `z : Nat`, `f (d j₁) (z + 2 ^ j₂) = f (d j₁) z`. -/
theorem f_d_add_two_pow_of_lt {j₁ j₂ : Nat} (hj : j₁ < j₂) (z : Nat) :
    f (d j₁) (z + 2 ^ j₂) = f (d j₁) z := by
  have hmul : ∀ q u : Nat, f (d j₁) (u + 2 ^ (j₁ + 1) * q) = f (d j₁) u := by
    intro q
    induction q with
    | zero => intro u; rfl
    | succ q ih =>
      intro u
      rw [Nat.mul_succ, ← Nat.add_assoc, period_d j₁, ih]
  have hpow : 2 ^ j₂ = 2 ^ (j₁ + 1) * 2 ^ (j₂ - (j₁ + 1)) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [hpow, hmul]

/-- **Higher-Dyadic Invariance of Transversal Read `Y j₁` (`Y_add_two_pow_of_lt`):**
for `j₁ < j₂` and every `u : Nat`, `Y j₁ (u + 2 ^ j₂) = Y j₁ u`. -/
theorem Y_add_two_pow_of_lt {j₁ j₂ : Nat} (hj : j₁ < j₂) (u : Nat) :
    Y j₁ (u + 2 ^ j₂) = Y j₁ u := by
  have hpow : 2 ^ j₂ = 2 ^ (j₁ + 1) * 2 ^ (j₂ - (j₁ + 1)) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [hpow, Y_period]

/-- **Distinctness of Doubling Depths (`d_ne_of_lt`):**
if `j₁ < j₂`, then `d j₁ ≠ d j₂` (since `f (d j₁)` is invariant under `+ 2 ^ j₂` while
`f (d j₂)` is complemented by `+ 2 ^ j₂`). -/
theorem d_ne_of_lt {j₁ j₂ : Nat} (hj : j₁ < j₂) : d j₁ ≠ d j₂ := by
  intro heq
  have hinv := f_d_add_two_pow_of_lt hj 0
  have hflip := fresh_digit j₂ 0
  rw [heq] at hinv
  rw [hinv] at hflip
  cases f (d j₂) 0 <;> exact Bool.noConfusion hflip

/-- **Injectivity of the Doubling-Depth Sequence `d` (`d_injective`):**
for all `j₁, j₂ : Nat`, `d j₁ = d j₂ ↔ j₁ = j₂`. -/
theorem d_injective (j₁ j₂ : Nat) : d j₁ = d j₂ ↔ j₁ = j₂ := by
  constructor
  · intro heq
    rcases Nat.lt_trichotomy j₁ j₂ with h | h | h
    · exact absurd heq (d_ne_of_lt h)
    · exact h
    · exact absurd heq.symm (d_ne_of_lt h)
  · intro h; subst h; rfl

/-- **Non-Periodicity of Transversal Read `Y j` at All Dyadic Scales `2 ^ k` with `k ≤ j`
(`not_evPer_two_pow_Y`):** for `k ≤ j`, `Y j` is never eventually `2 ^ k`-periodic. -/
theorem not_evPer_two_pow_Y {k j : Nat} (hk : k ≤ j) :
    ¬ ∃ T₀ : Nat, ∀ u : Nat, T₀ ≤ u → Y j (u + 2 ^ k) = Y j u := by
  rintro ⟨T₀, hper⟩
  have hmul : ∀ q u : Nat, T₀ ≤ u → Y j (u + 2 ^ k * q) = Y j u := by
    intro q
    induction q with
    | zero => intro u _; rfl
    | succ q ih =>
      intro u hu
      rw [Nat.mul_succ, ← Nat.add_assoc, hper _ (by omega), ih u hu]
  have hpow : 2 ^ j = 2 ^ k * 2 ^ (j - k) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hev : Y j (T₀ + 2 ^ j) = Y j T₀ := by
    rw [hpow]
    exact hmul (2 ^ (j - k)) T₀ (Nat.le_refl T₀)
  have hfl := Y_flip j T₀
  rw [hev] at hfl
  revert hfl; cases Y j T₀ <;> decide

/-- **Non-Periodicity of Diagonal `f (d j)` at All Dyadic Scales `2 ^ k` with `k ≤ j`
(`not_evPer_two_pow_f_d`):** for `k ≤ j`, `f (d j)` is never eventually `2 ^ k`-periodic. -/
theorem not_evPer_two_pow_f_d {k j : Nat} (hk : k ≤ j) :
    ¬ ∃ T₀ : Nat, ∀ z : Nat, T₀ ≤ z → f (d j) (z + 2 ^ k) = f (d j) z := by
  rintro ⟨T₀, hper⟩
  apply not_evPer_two_pow_Y hk
  refine ⟨T₀, fun u hu => ?_⟩
  rw [Y_eq, Y_eq, show u + 2 ^ k + d j = (u + d j) + 2 ^ k by omega]
  exact hper (u + d j) (by omega)

/-- **Levelwise Half-Density on Every Dyadic Window (`cnt_Y_level`):**
for every `j < m` and every starting column `A : Nat`, `cnt (Y j) A (2 ^ m) = 2 ^ (m - 1)`. -/
theorem cnt_Y_level {m j : Nat} (hj : j < m) (A : Nat) :
    cnt (Y j) A (2 ^ m) = 2 ^ (m - 1) := by
  have e : 2 ^ m = 2 ^ (j + 1) * 2 ^ (m - (j + 1)) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [e, cnt_Y, ← Nat.pow_add]; congr 1; omega

/-- **Unique Cube Coordinates (`cube_unique`):**
for every `m, A : Nat` and word `w : Fin m → Bool`, there exists a unique column `u` in
`[A, A + 2 ^ m)` whose transversal read `(fun j : Fin m => cell (u + d j) u)` equals `w`. -/
theorem cube_unique (m A : Nat) (w : Fin m → Bool) :
    ∃ u : Nat, (A ≤ u ∧ u < A + 2 ^ m ∧ (fun j : Fin m => cell (u + d j) u) = w) ∧
      ∀ v : Nat, A ≤ v ∧ v < A + 2 ^ m → (fun j : Fin m => cell (v + d j) v) = w → v = u := by
  obtain ⟨u, hu1, hu2, huw⟩ := cube_surjective m A w
  refine ⟨u, ⟨hu1, hu2, huw⟩, fun v hv hvw => ?_⟩
  exact cube_injective m A v u hv ⟨hu1, hu2⟩ (by rw [hvw, huw])

end Rule30ConeCube
end Ruliology.CellularAutomata
