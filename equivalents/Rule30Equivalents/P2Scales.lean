module

public import Rule30Equivalents.Basic
public import Rule30Equivalents.ProblemTwo

/-!
# Problem 2: one nearly-geometric sequence of nearly-balanced scales, and the first-passage form

Two exact equivalent forms of `Rule30Prize.Problem2` that the catalog did not have:
`problem2_iff_singleSequence` (one sequence of nearly balanced, nearly geometric scales) and
`problem2_iff_firstPassage` (a hitting-time lower bound), together with the sufficient conditions
`problem2_of_epsGaps` and `problem2_of_exactReturns`. All generic statements hold for every
Boolean sequence. Partial-equivalence only; it does not prove Problem 2.
-/

@[expose] public section

namespace Rule30Equivalents


namespace P2Scales
open Ruliology.CellularAutomata Rule30Prize

/-! ## 0. Self-contained finite sums (the kit is core-only) -/

/-- `isum f n = f 0 + f 1 + … + f (n-1)`. -/
def isum (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => isum f n + f n

@[simp] theorem isum_zero (f : Nat → Int) : isum f 0 = 0 := rfl

theorem isum_succ (f : Nat → Int) (n : Nat) : isum f (n + 1) = isum f n + f n := rfl

/-- The `0/1` value of a Boolean sequence. -/
def bit (b : Nat → Bool) (t : Nat) : Int := if b t then 1 else 0

theorem bit_zero_or_one (b : Nat → Bool) (t : Nat) : bit b t = 0 ∨ bit b t = 1 := by
  unfold bit; split <;> simp

theorem bit_nonneg (b : Nat → Bool) (t : Nat) : 0 ≤ bit b t := by
  rcases bit_zero_or_one b t with h | h <;> omega

theorem bit_le_one (b : Nat → Bool) (t : Nat) : bit b t ≤ 1 := by
  rcases bit_zero_or_one b t with h | h <;> omega

theorem isum_nonneg (b : Nat → Bool) (n : Nat) : 0 ≤ isum (fun t => bit b t) n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [isum_succ]
      have := bit_nonneg b n
      omega

theorem isum_le (b : Nat → Bool) (n : Nat) : isum (fun t => bit b t) n ≤ (n : Int) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [isum_succ]
      push_cast
      have := bit_le_one b n
      omega

/-! ## 1. The discrepancy walk and its telescoping bound -/

/-- The discrepancy walk: `D b n = 2·(black count of b below n) − n`. -/
def D (b : Nat → Bool) (n : Nat) : Int := 2 * isum (fun t => bit b t) n - (n : Int)

/-- One step: `D(n+1) = D n + (2·b n − 1)`. -/
theorem D_succ (b : Nat → Bool) (n : Nat) :
    D b (n + 1) = D b n + (2 * bit b n - 1) := by
  have h : isum (fun t => bit b t) (n + 1)
      = isum (fun t => bit b t) n + bit b n := isum_succ _ n
  unfold D
  rw [h]
  push_cast
  omega

/-- Two-sided bound `k·|x| ≤ K`, kept integral so that `omega` applies. -/
def Bdd (k : Nat) (x : Int) (K : Int) : Prop :=
  -K ≤ ((k : Int)) * x ∧ ((k : Int)) * x ≤ K

theorem D_step_scaled (b : Nat → Bool) (k : Nat) (n : Nat) :
    Bdd k (D b (n + 1) - D b n) (k : Int) := by
  rw [D_succ]
  unfold Bdd
  rcases bit_zero_or_one b n with h | h <;> rw [h] <;> omega

/-- Every segment of the walk moves at most its length, at any scale. -/
theorem D_telescope_scaled (b : Nat → Bool) (k : Nat) :
    ∀ {n m : Nat}, n ≤ m →
      Bdd k (D b m - D b n) (((k * (m - n) : Nat)) : Int) := by
  intro n m h
  induction m with
  | zero =>
      have hn : n = 0 := by omega
      subst hn
      unfold Bdd
      simp
  | succ m ih =>
      rcases Nat.eq_or_lt_of_le h with heq | hlt
      · subst heq
        unfold Bdd
        simp
      · have h1 : n ≤ m := by omega
        have h2 := ih h1
        have h3 := D_step_scaled b k m
        have h4 : D b (m + 1) - D b n
            = (D b m - D b n) + (D b (m + 1) - D b m) := by omega
        rw [h4]
        unfold Bdd at h2 h3 ⊢
        rw [Int.mul_add]
        have hcast : (((k * (m + 1 - n) : Nat)) : Int)
            = (((k * (m - n) : Nat)) : Int) + ((k : Int)) := by
          have hnat : k * (m + 1 - n) = k * (m - n) + k := by
            have h1 : m + 1 - n = (m - n) + 1 := by omega
            rw [h1, Nat.mul_add, Nat.mul_one]
          rw [hnat]
          push_cast
          rfl
        rw [hcast]
        constructor <;> omega

/-- `n` is a `k`-good scale if `k·|D n| ≤ n`. -/
def Good (b : Nat → Bool) (k : Nat) (n : Nat) : Prop := Bdd k (D b n) ((n : Int))

/-- Density `1/2` in the generic (official-kit-style) form. -/
def DensityOf (b : Nat → Bool) : Prop :=
  ∀ k, 0 < k → ∃ N, ∀ n, N ≤ n →
    k * (2 * isum (fun t => bit b t) n - (n : Int)).natAbs ≤ n

/-- First-passage (hitting-time) form: the walk cannot reach height `h` before
time `k·h`.  No first-passage operator is needed: the statement is vacuous at a
height that is never reached, which is exactly right. -/
def FirstPassage (b : Nat → Bool) : Prop :=
  ∀ k, 0 < k → ∃ H, ∀ h t, H ≤ h → (D b t).natAbs = h → k * h ≤ t

/-! ## 2. Elementary toolkit -/

theorem natAbs_le_iff (x : Int) (n : Nat) :
    x.natAbs ≤ n ↔ -((n : Int)) ≤ x ∧ x ≤ (n : Int) := by
  cases x with
  | ofNat m => simp
  | negSucc m => rw [Int.natAbs_negSucc]; simp; omega

theorem natAbs_natCast (k : Nat) : ((k : Int)).natAbs = k := rfl

/-- Multiplication by a nonnegative integer preserves `≤`. -/
theorem mul_mono (c : Nat) {x y : Int} (h : x ≤ y) : (c : Int) * x ≤ (c : Int) * y :=
  Int.mul_le_mul_of_nonneg_left h (by exact_mod_cast Nat.zero_le c)

/-- `Bdd` is monotone in its bound. -/
theorem Bdd_mono {k : Nat} {x : Int} {C D : Nat} (h : Bdd k x (C : Int)) (hCD : C ≤ D) :
    Bdd k x (D : Int) := by
  unfold Bdd at *
  have h1 : ((C : Nat) : Int) ≤ ((D : Nat) : Int) := by exact_mod_cast hCD
  constructor <;> omega

/-- A larger scale is a stronger hypothesis: `Bdd K x C → Bdd k x C` for `k ≤ K`. -/
theorem Bdd_of_scale {k K : Nat} {x : Int} {C : Nat} (h : Bdd K x (C : Int)) (hk : k ≤ K) :
    Bdd k x (C : Int) := by
  have h' : (((K : Int)) * x).natAbs ≤ C := (natAbs_le_iff _ _).mpr h
  have h2 : (((k : Int)) * x).natAbs ≤ C := by
    simp only [Int.natAbs_mul, natAbs_natCast] at h' ⊢
    exact Nat.le_trans (Nat.mul_le_mul_right _ hk) h'
  exact (natAbs_le_iff _ _).mp h2

/-- Scaling up a bound: `|x| ≤ C → |c·x| ≤ c·C`. -/
theorem Bdd_mul (c : Nat) {x : Int} {C : Nat} (h : Bdd 1 x (C : Int)) :
    Bdd c x ((c * C : Nat) : Int) := by
  have h' : x.natAbs ≤ C := by
    have h2 : (((1 : Int)) * x).natAbs ≤ C := (natAbs_le_iff _ _).mpr h
    simpa using h2
  have h3 : (((c : Int)) * x).natAbs ≤ c * C := by
    rw [Int.natAbs_mul, natAbs_natCast]
    exact Nat.mul_le_mul_left c h'
  exact (natAbs_le_iff _ _).mp h3

/-- `Bdd` is subadditive. -/
theorem Bdd_add {k : Nat} {x y : Int} {C D : Nat} (h1 : Bdd k x (C : Int))
    (h2 : Bdd k y (D : Int)) : Bdd k (x + y) ((C + D : Nat) : Int) := by
  unfold Bdd at *
  push_cast
  rw [Int.mul_add]
  constructor <;> omega

/-- Negation preserves `Bdd`. -/
theorem Bdd_neg {k : Nat} {x : Int} {C : Nat} (h : Bdd k x (C : Int)) : Bdd k (-x) (C : Int) := by
  unfold Bdd at *
  rw [Int.mul_neg]
  constructor <;> omega

/-- Halving: `|2k·x| ≤ 2n → |k·x| ≤ n`. -/
theorem Bdd_halve {k : Nat} {x : Int} {n : Nat} (h : Bdd (2 * k) x (2 * (n : Int))) :
    Bdd k x (n : Int) := by
  unfold Bdd at *
  have e : ((2 * k : Nat) : Int) * x = 2 * ((k : Int) * x) := by
    have h1 : ((2 * k : Nat) : Int) = 2 * (k : Int) := by push_cast; rfl
    rw [h1, Int.mul_assoc]
  rw [e] at h
  constructor <;> omega

/-- Quarter-scale reduction: `|4k·x| ≤ 2n → |k·x| ≤ n`. -/
theorem Bdd_quarter {k : Nat} {x : Int} {n : Nat} (h : Bdd (4 * k) x (2 * (n : Int))) :
    Bdd k x (n : Int) := by
  unfold Bdd at *
  have e : ((4 * k : Nat) : Int) * x = 4 * ((k : Int) * x) := by
    have h1 : ((4 * k : Nat) : Int) = 4 * (k : Int) := by push_cast; rfl
    rw [h1, Int.mul_assoc]
  rw [e] at h
  constructor <;> omega

/-- Strictly increasing sequences are monotone. -/
theorem mono_le {g : Nat → Nat} (hmono : ∀ j, g j < g (j + 1)) :
    ∀ {a b : Nat}, a ≤ b → g a ≤ g b := by
  intro a b hab
  induction b with
  | zero => have h : a = 0 := by omega
            subst h; exact Nat.le_refl _
  | succ b ih =>
      rcases Nat.eq_or_lt_of_le hab with heq | hlt
      · subst heq; exact Nat.le_refl _
      · have h1 : a ≤ b := by omega
        exact Nat.le_trans (ih h1) (Nat.le_of_lt (hmono b))

theorem lt_of_mono_lt {g : Nat → Nat} (hmono : ∀ j, g j < g (j + 1)) {a b : Nat}
    (h : g a < g b) : a < b := by
  rcases Nat.lt_or_ge a b with h' | h'
  · exact h'
  · have h2 : g b ≤ g a := mono_le hmono h'
    omega

theorem grow {g : Nat → Nat} (hmono : ∀ j, g j < g (j + 1)) :
    ∀ j, g 0 + j ≤ g j := by
  intro j
  induction j with
  | zero => exact Nat.le_refl _
  | succ j ih =>
      have h1 : g j < g (j + 1) := hmono j
      omega

/-! ## 3. The single-sequence form (the sandwich) -/

/-- For strictly increasing `g` and `n ≥ g J` there is an index `j ≥ J` that
brackets `n`: `g j ≤ n < g (j+1)`.  (`Nat.find` is not in the core-only kit, so
this is proved by induction on `n`.) -/
theorem exists_bracket {g : Nat → Nat} (hmono : ∀ j, g j < g (j + 1)) (J : Nat) :
    ∀ n, g J ≤ n → ∃ j, J ≤ j ∧ g j ≤ n ∧ n < g (j + 1) := by
  intro n
  induction n with
  | zero =>
      intro hn
      exact ⟨J, Nat.le_refl J, hn, by have := hmono J; omega⟩
  | succ n ih =>
      intro hn
      by_cases h0 : g J ≤ n
      · obtain ⟨j, hj1, hj2, hj3⟩ := ih h0
        by_cases h4 : n + 1 < g (j + 1)
        · exact ⟨j, hj1, by omega, h4⟩
        · exact ⟨j + 1, by omega, by omega, by have := hmono (j + 1); omega⟩
      · exact ⟨J, Nat.le_refl J, by omega, by have := hmono J; omega⟩

/-- **The sandwich.**  One sequence of nearly-balanced scales whose successive
ratios tend to `1` forces density `1/2`: at parameter `2k` the two deficits
`k·|D (g j)|` and `k·(n − g j)` are each at most `g j / 2`. -/
theorem densityOf_of_singleSequence {b : Nat → Bool} {g : Nat → Nat}
    (hmono : ∀ j, g j < g (j + 1))
    (hacc : ∀ k, 0 < k → ∃ J, ∀ j, J ≤ j → Bdd k (D b (g j)) (g j : Int))
    (hratio : ∀ k, 0 < k → ∃ J, ∀ j, J ≤ j → k * (g (j + 1) - g j) ≤ g j) :
    DensityOf b := by
  intro k hk
  have h2k : 0 < 2 * k := by omega
  obtain ⟨Ja, hJa⟩ := hacc (2 * k) h2k
  obtain ⟨Jr, hJr⟩ := hratio (2 * k) h2k
  refine ⟨g (max Ja Jr), fun n hn => ?_⟩
  obtain ⟨j, hJ, hgj, hj⟩ := exists_bracket hmono (max Ja Jr) n hn
  -- the two deficits
  have hAcc : Bdd (2 * k) (D b (g j)) (g j : Int) := hJa j (by omega)
  have hRat : 2 * k * (g (j + 1) - g j) ≤ g j := hJr j (by omega)
  have hRatZ : (((2 * k * (g (j + 1) - g j) : Nat)) : Int) ≤ (g j : Int) := by
    exact_mod_cast hRat
  have hTel : Bdd 1 (D b n - D b (g j)) (((n - g j : Nat)) : Int) := by
    simpa using D_telescope_scaled b 1 hgj
  have hTelS : Bdd (2 * k) (D b n - D b (g j))
      (((2 * k) * (n - g j) : Nat) : Int) := Bdd_mul (2 * k) hTel
  have hgapZ : (((2 * k) * (n - g j) : Nat) : Int)
      ≤ (((2 * k * (g (j + 1) - g j) : Nat)) : Int) := by
    have h3 : (n - g j : Nat) ≤ g (j + 1) - g j :=
      Nat.sub_le_sub_right (Nat.le_of_lt hj) (g j)
    have h4 : 2 * k * (n - g j) ≤ 2 * k * (g (j + 1) - g j) :=
      Nat.mul_le_mul_left _ h3
    exact_mod_cast h4
  have hstep : D b n = (D b n - D b (g j)) + D b (g j) := by omega
  have hupper : Bdd (2 * k) (D b n) (2 * (n : Int)) := by
    have hA : Bdd (2 * k) (D b n - D b (g j)) ((n : Int)) :=
      Bdd_mono hTelS (by omega)
    have hB : Bdd (2 * k) (D b (g j)) ((n : Int)) :=
      Bdd_mono hAcc (by omega)
    have hC : Bdd (2 * k) ((D b n - D b (g j)) + D b (g j)) (((n + n : Nat)) : Int) :=
      Bdd_add hA hB
    rw [← hstep] at hC
    have h2 : (((n + n : Nat)) : Int) = 2 * (n : Int) := by push_cast; omega
    rwa [h2] at hC
  have hmain : Bdd k (D b n) ((n : Int)) := Bdd_halve hupper
  have h3 : k * (D b n).natAbs ≤ n := by
    have h4 : (((k : Int)) * D b n).natAbs ≤ n := (natAbs_le_iff _ _).mpr hmain
    rw [Int.natAbs_mul, natAbs_natCast] at h4
    exact h4
  simpa [D] using h3

/-- Converse: from density `1/2` take the identity sequence. -/
theorem singleSequence_of_densityOf {b : Nat → Bool} (h : DensityOf b) :
    ∃ g : Nat → Nat, (∀ j, g j < g (j + 1)) ∧
      (∀ k, 0 < k → ∃ J, ∀ j, J ≤ j → Bdd k (D b (g j)) (g j : Int)) ∧
      (∀ k, 0 < k → ∃ J, ∀ j, J ≤ j → k * (g (j + 1) - g j) ≤ g j) := by
  refine ⟨fun j => j, fun j => Nat.lt_succ_self j, ?_, ?_⟩
  · intro k hk
    obtain ⟨N, hN⟩ := h k hk
    refine ⟨N, fun j hj => ?_⟩
    have h1 : k * (D b j).natAbs ≤ j := by simpa [D] using hN j hj
    have h2 : (((k : Int)) * D b j).natAbs ≤ j := by
      rw [Int.natAbs_mul, natAbs_natCast]
      exact h1
    exact (natAbs_le_iff _ _).mp h2
  · intro k hk
    refine ⟨k, fun j hj => ?_⟩
    have h1 : j + 1 - j = 1 := by omega
    rw [h1, Nat.mul_one]
    omega

/-- **The weakest-shape form of P2.**  Density `1/2` holds iff there is a single
nearly-geometric sequence of nearly-balanced scales.  The double uniformity
`∀k ∀m` of the return-gap form is redundant. -/
theorem densityOf_iff_singleSequence (b : Nat → Bool) :
    DensityOf b ↔ ∃ g : Nat → Nat, (∀ j, g j < g (j + 1)) ∧
      (∀ k, 0 < k → ∃ J, ∀ j, J ≤ j → Bdd k (D b (g j)) (g j : Int)) ∧
      (∀ k, 0 < k → ∃ J, ∀ j, J ≤ j → k * (g (j + 1) - g j) ≤ g j) :=
  ⟨singleSequence_of_densityOf, fun ⟨_, h1, h2, h3⟩ => densityOf_of_singleSequence h1 h2 h3⟩

/-! ## 4. The frontier: gap fraction versus accuracy -/

/-- **Frontier theorem.**  If for every gap tolerance `e` there is SOME accuracy
level `k ≥ e` whose good set has relative gaps `≤ 1/e`, then density `1/2`
holds.  The certified discrepancy is `1/k + 1/e`; the accuracy may be chosen
after the tolerance, and no fixed gap fraction suffices (`P2RG.md` §4). -/
theorem densityOf_of_epsGaps {b : Nat → Bool}
    (h : ∀ e, 0 < e → ∃ k, e ≤ k ∧ ∃ N₀, ∀ N, N₀ ≤ N →
      ∃ g, g ≤ N ∧ (e - 1) * N ≤ e * g ∧ Good b k g) :
    DensityOf b := by
  intro k hk
  have he : 0 < 4 * k := by omega
  obtain ⟨K, hK, N₀, hN₀⟩ := h (4 * k) he
  refine ⟨N₀, fun n hn => ?_⟩
  obtain ⟨g, hgle, hggap, hggood⟩ := hN₀ n hn
  -- the gap is at most `n/(4k)`
  have hnat : 4 * k * (n - g) ≤ n := by
    have h1 : 4 * k * n = 4 * k * g + 4 * k * (n - g) := by
      rw [← Nat.mul_add]; congr 1; omega
    have h2 : (4 * k - 1) * n = 4 * k * n - n := by
      rw [Nat.sub_mul, Nat.one_mul]
    omega
  have hnatZ : ((((4 * k) * (n - g) : Nat)) : Int) ≤ (n : Int) := by exact_mod_cast hnat
  -- scale the telescope at `4k`
  have hTel : Bdd 1 (D b n - D b g) (((n - g : Nat)) : Int) := by
    simpa using D_telescope_scaled b 1 hgle
  have hTelS : Bdd (4 * k) (D b n - D b g) ((((4 * k) * (n - g) : Nat)) : Int) :=
    Bdd_mul (4 * k) hTel
  have hA : Bdd (4 * k) (D b n - D b g) ((n : Int)) := Bdd_mono hTelS (by omega)
  -- the good scale at accuracy `K ≥ 4k`
  have hB : Bdd (4 * k) (D b g) ((g : Int)) := Bdd_of_scale (K := K) hggood hK
  have hB' : Bdd (4 * k) (D b g) ((n : Int)) := Bdd_mono hB (by omega)
  have hC : Bdd (4 * k) ((D b n - D b g) + D b g) (((n + n : Nat)) : Int) := Bdd_add hA hB'
  have hstep : (D b n - D b g) + D b g = D b n := by omega
  rw [hstep] at hC
  have h2 : (((n + n : Nat)) : Int) = 2 * (n : Int) := by push_cast; omega
  rw [h2] at hC
  have hmain : Bdd k (D b n) ((n : Int)) := Bdd_quarter hC
  have h4 : (((k : Int)) * D b n).natAbs ≤ n := (natAbs_le_iff _ _).mpr hmain
  rw [Int.natAbs_mul, natAbs_natCast] at h4
  simpa [D] using h4

/-- Bounded relative gaps suffice: a special case of `densityOf_of_epsGaps`. -/
theorem densityOf_of_boundedGaps {b : Nat → Bool}
    (h : ∀ k, 0 < k → ∃ m, ∃ N₀, ∀ N, N₀ ≤ N →
      ∃ g, N ≤ g ∧ g ≤ N + m ∧ Good b k g) :
    DensityOf b := by
  intro k hk
  have h2k : 0 < 2 * k := by omega
  obtain ⟨m, N₀, hN₀⟩ := h (2 * k) h2k
  refine ⟨max N₀ ((2 * k + 1) * m), fun n hn => ?_⟩
  have hn0 : N₀ ≤ n := by omega
  have hbound : (2 * k + 1) * m ≤ n := by omega
  have hmul : (2 * k + 1) * m = 2 * (k * m) + m := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
  obtain ⟨g, h1, h2, h3⟩ := hN₀ n hn0
  have hTel : Bdd 1 (D b g - D b n) (((g - n : Nat)) : Int) := by
    simpa using D_telescope_scaled b 1 h1
  have hTelS : Bdd (2 * k) (D b g - D b n) ((((2 * k) * (g - n) : Nat)) : Int) :=
    Bdd_mul (2 * k) hTel
  have hgn : g - n ≤ m := by omega
  have hTelM : Bdd (2 * k) (D b g - D b n) (((2 * k) * m : Nat)) :=
    Bdd_mono hTelS (Nat.mul_le_mul_left _ hgn)
  have hA : Bdd (2 * k) (D b g) (((n + m : Nat)) : Int) := Bdd_mono h3 (by omega)
  have hC : Bdd (2 * k) (D b g + (-(D b g - D b n))) ((((n + m) + (2 * k) * m : Nat)) : Int) :=
    Bdd_add hA (Bdd_neg hTelM)
  have hstep : D b g + (-(D b g - D b n)) = D b n := by omega
  rw [hstep] at hC
  have hmul2 : (2 * k) * m = 2 * (k * m) := by rw [Nat.mul_assoc]
  have hfin : ((n + m) + (2 * k) * m) ≤ 2 * n := by omega
  have hC2 : Bdd (2 * k) (D b n) (2 * (n : Int)) := by
    have h4 : Bdd (2 * k) (D b n) (((2 * n : Nat)) : Int) := Bdd_mono hC hfin
    have h5 : (((2 * n : Nat)) : Int) = 2 * (n : Int) := by push_cast; rfl
    rwa [h5] at h4
  have hmain : Bdd k (D b n) ((n : Int)) := Bdd_halve hC2
  have h4 : (((k : Int)) * D b n).natAbs ≤ n := (natAbs_le_iff _ _).mpr hmain
  rw [Int.natAbs_mul, natAbs_natCast] at h4
  simpa [D] using h4

/-- Exact returns whose ratios tend to `1` suffice: no accuracy parameter. -/
theorem densityOf_of_exactReturns {b : Nat → Bool} {g : Nat → Nat}
    (hmono : ∀ j, g j < g (j + 1))
    (hzero : ∀ j, D b (g j) = 0)
    (hratio : ∀ k, 0 < k → ∃ J, ∀ j, J ≤ j → k * (g (j + 1) - g j) ≤ g j) :
    DensityOf b := by
  refine densityOf_of_singleSequence hmono ?_ hratio
  intro k hk
  refine ⟨0, fun j _ => ?_⟩
  rw [hzero j]
  unfold Bdd
  constructor <;> simp

/-! ## 5. The first-passage form -/

/-- The walk never leaves the cone `|D n| ≤ n`. -/
theorem D_natAbs_le (b : Nat → Bool) (n : Nat) : (D b n).natAbs ≤ n := by
  have h0 := isum_nonneg b n
  have h1 := isum_le b n
  rw [natAbs_le_iff]
  unfold D
  constructor <;> omega

/-- **P2 is a hitting-time lower bound.**  Density `1/2` holds iff for every `k`
no height `h ≥ H(k)` is reached before time `k·h`.  Every recorded sufficient
condition for P2 is an upper bound on `|D|`; this form is a lower bound on
first-passage times. -/
theorem densityOf_iff_firstPassage (b : Nat → Bool) : DensityOf b ↔ FirstPassage b := by
  constructor
  · intro h k hk
    obtain ⟨N, hN⟩ := h (2 * k) (by omega)
    refine ⟨N, fun hh t ht hD => ?_⟩
    rcases Nat.lt_or_ge t N with hlt | hge
    · have h1 := D_natAbs_le b t
      omega
    · have h1 : 2 * k * (D b t).natAbs ≤ t := by simpa [D] using hN t hge
      rw [hD] at h1
      have h2 : 2 * (k * hh) ≤ t := by
        rw [Nat.mul_assoc] at h1
        exact h1
      omega
  · intro h k hk
    obtain ⟨H, hH⟩ := h (2 * k) (by omega)
    refine ⟨max H (k * H), fun n hn => ?_⟩
    have hcone := D_natAbs_le b n
    rcases Nat.lt_or_ge (D b n).natAbs H with hlt | hge
    · have h1 : k * (D b n).natAbs ≤ k * (H - 1) := Nat.mul_le_mul_left k (by omega)
      have h2 : k * (H - 1) ≤ k * H := Nat.mul_le_mul_left k (by omega)
      have h3 : k * (H - 1) ≤ n := by omega
      have h4 : k * (D b n).natAbs ≤ n := by omega
      simpa [D] using h4
    · have h1 : 2 * k * (D b n).natAbs ≤ n := hH _ n hge rfl
      have h2 : 2 * (k * (D b n).natAbs) ≤ n := by
        rw [Nat.mul_assoc] at h1
        exact h1
      have h3 : k * (D b n).natAbs ≤ n := by omega
      simpa [D] using h3

/-! ## 6. Instantiation to the official target -/

theorem isum_const (c : Int) (n : Nat) : isum (fun _ => c) n = c * (n : Int) := by
  induction n with
  | zero => simp
  | succ n ih => rw [isum_succ, ih]; push_cast; rw [Int.mul_add, Int.mul_one]

theorem blackCount_succ_int (n : Nat) :
    (blackCount (n + 1) : Int) = (blackCount n : Int) + bit center n := by
  have h : blackCount (n + 1) = blackCount n + (if center n then 1 else 0) := by
    unfold blackCount
    rw [List.range_succ, List.filter_append, List.length_append]
    cases hh : center n <;> simp [hh]
  rw [h]
  unfold bit
  cases hh : center n <;> simp

/-- The official `blackCount` is the sum of the `0/1` sequence. -/
theorem blackCount_eq_isum (n : Nat) :
    (blackCount n : Int) = isum (fun t => bit center t) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [blackCount_succ_int, ih, isum_succ]

/-- The official `Problem2` is the generic density statement at the centre column. -/
theorem problem2_iff_densityOf : Problem2 ↔ DensityOf center := by
  unfold Problem2 DensityOf
  constructor
  · intro h k hk
    obtain ⟨N, hN⟩ := h k hk
    refine ⟨N, fun n hn => ?_⟩
    have h1 := hN n hn
    rwa [blackCount_eq_isum] at h1
  · intro h k hk
    obtain ⟨N, hN⟩ := h k hk
    refine ⟨N, fun n hn => ?_⟩
    have h1 := hN n hn
    rwa [blackCount_eq_isum]

/-- **`Problem2` in the single-sequence form** — the weakest-shape obligation. -/
theorem problem2_iff_singleSequence : Problem2 ↔ ∃ g : Nat → Nat,
    (∀ j, g j < g (j + 1)) ∧
    (∀ k, 0 < k → ∃ J, ∀ j, J ≤ j → Bdd k (D center (g j)) (g j : Int)) ∧
    (∀ k, 0 < k → ∃ J, ∀ j, J ≤ j → k * (g (j + 1) - g j) ≤ g j) :=
  problem2_iff_densityOf.trans (densityOf_iff_singleSequence center)

/-- **`Problem2` in the first-passage form** (a hitting-time lower bound). -/
theorem problem2_iff_firstPassage : Problem2 ↔ FirstPassage center :=
  problem2_iff_densityOf.trans (densityOf_iff_firstPassage center)

/-- **`Problem2` from the frontier hypothesis.** -/
theorem problem2_of_epsGaps
    (h : ∀ e, 0 < e → ∃ k, e ≤ k ∧ ∃ N₀, ∀ N, N₀ ≤ N →
      ∃ g, g ≤ N ∧ (e - 1) * N ≤ e * g ∧ Good center k g) : Problem2 :=
  problem2_iff_densityOf.mpr (densityOf_of_epsGaps h)

/-- **`Problem2` from multiplicatively dense exact returns.** -/
theorem problem2_of_exactReturns {g : Nat → Nat}
    (hmono : ∀ j, g j < g (j + 1))
    (hzero : ∀ j, D center (g j) = 0)
    (hratio : ∀ k, 0 < k → ∃ J, ∀ j, J ≤ j → k * (g (j + 1) - g j) ≤ g j) : Problem2 :=
  problem2_iff_densityOf.mpr (densityOf_of_exactReturns hmono hzero hratio)


end P2Scales

end Rule30Equivalents
