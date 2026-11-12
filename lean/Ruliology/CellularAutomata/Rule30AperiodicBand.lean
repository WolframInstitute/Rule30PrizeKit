module

public import Ruliology.CellularAutomata.Rule30SeedLeftSide
public import Ruliology.CellularAutomata.Rule30TraceEdge

/-!
# Aperiodic bands at the left edge

Rule 30 from one black cell. The left edge of the light cone moves one cell left each tick, so column `c < 0` turns black at tick
`-c`, and at tick `t` it is `t + c` cells in from the edge. An aperiodic band of depth `N` from column `c₀` says that no column
`c ≤ c₀` becomes periodic, with any period `P`, if its first period ends while it is within `N` cells of the edge, that is, if
`c ≤ -(T + P) + N` (`AperiodicBand`). It bounds how late periodicity can start: a column `c ≤ c₀` that is `P`-periodic from `T`
has `T + P > N - c`. `LongPeriodBand` is the same for the periods above a bound. A band from column `0` at every depth is Problem 1
(`problem1_of_band`): the bands measure how far in from the edge the columns are known to be aperiodic.

`Rule30TraceEdge` gives a band of depth 384 from column `-2985` (`band_384`). A band for long periods comes from each left diagonal
that is black from some tick on: a period longer than its depth would carry one of its black cells back to a tick before the
column turns black (`Rule30TraceEdge.not_cell_periodic_gt_of_black_diagonal`). With the single seed on the strip `A0` from tick
77,920 through wheel 58,288 (`Rule30SeedLeftSide`), `D 58288` is black from tick 77,920, which gives a band of depth 58,288 for the
periods above 58,288 from column `-77,920` (`band_58288`). The seed also satisfies the hypotheses of the `+-` branch of
`Rule30LeftAntiPeriod` (`seed_D58287`, `seed_D58288`), so its seventh white diagonal is `D 87866`, the period doubles to 32 at
`D 87867`, and `D 87868` is black (`seed_seventh_white_diagonal`), with a band of depth 87,868 for the periods above 87,868
(`band_87868`).
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30AperiodicBand

set_option autoImplicit false

open Rule30Jen Rule30Diagonals Rule30LeftReset Rule30WhiteSpacing Rule30LeftAntiPeriod Rule30FourLeftSides
  Rule30SeedLeftSide Rule30TraceEdge

/-! ### Bands -/

/-- No column `c ≤ c₀` becomes periodic, with any period, while it is within `N` cells of the left edge of the light cone. -/
def AperiodicBand (N : Nat) (c₀ : Int) : Prop :=
  ∀ c : Int, c ≤ c₀ → ∀ T P : Nat, 0 < P → c ≤ -((T + P : Nat) : Int) + N →
    ¬ ∀ t : Nat, T ≤ t → cell (t + P) c = cell t c

/-- No column `c ≤ c₀` becomes periodic, with a period above `P₀`, while it is within `N` cells of the left edge. -/
def LongPeriodBand (N P₀ : Nat) (c₀ : Int) : Prop :=
  ∀ c : Int, c ≤ c₀ → ∀ T P : Nat, P₀ < P → c ≤ -((T + P : Nat) : Int) + N →
    ¬ ∀ t : Nat, T ≤ t → cell (t + P) c = cell t c

theorem AperiodicBand.mono {N N' : Nat} {c₀ c₀' : Int} (h : AperiodicBand N c₀) (hN : N' ≤ N) (hc : c₀' ≤ c₀) :
    AperiodicBand N' c₀' :=
  fun c hc' T P hP hb => h c (Int.le_trans hc' hc) T P hP (by omega)

theorem AperiodicBand.longPeriod {N : Nat} {c₀ : Int} (h : AperiodicBand N c₀) (P₀ : Nat) : LongPeriodBand N P₀ c₀ :=
  fun c hc T P hP hb => h c hc T P (by omega) hb

/-- **A band from column `0` at every depth is Problem 1.** -/
theorem problem1_of_band (h : ∀ N, AperiodicBand N 0) : Rule30Prize.Problem1 := by
  unfold Rule30Prize.Problem1
  rintro ⟨T, P, hP, hper⟩
  exact h (T + P) 0 (Int.le_refl 0) T P hP (by omega) hper

/-- The band of depth 384 from column `-2985`, every period. -/
theorem band_384 : AperiodicBand 384 (-2985) :=
  fun c hc T P hP hb => not_cell_periodic_at_col_le_neg_add_add_three_hundred_eighty_four c T P hP (by omega) (by omega)

/-! ### From the seed's strip -/

/-- Wheels 58,287 and 58,288 of `A0`: the gate of the `+-` branch, and black. -/
theorem A0_gate : ∀ r, r < 16 →
    Sp A0 58288 r = true ∧ Sp A0 58287 r = gate16_D58287_neg.eval (((Sp A0 8 r, Sp A0 10 r), Sp A0 29 r), Sp A0 400 r) := by
  decide +kernel

/-- `D 58288` of the single seed is black from tick 77,920. -/
theorem seed_D58288 : ∀ t, 77920 ≤ t → D 58288 t = true := by
  intro t ht
  rw [seed_low t ht (j := 58288) (by omega), Sp_mod A0_return]
  exact (A0_gate (t % 16) (Nat.mod_lt _ (by omega))).1

/-- The first hypothesis of the `+-` branch of `Rule30LeftAntiPeriod`, for the single seed. -/
theorem seed_D58287 : ∀ t, 929138 ≤ t → D 58287 t = gate16_D58287_neg.eval (osc4State t) := by
  intro t ht
  have e : ∀ j, j ≤ 58288 → D j t = Sp A0 j (t % 16) := fun j hj => by
    rw [seed_low t (by omega) hj, Sp_mod A0_return]
  unfold osc4State osc3State
  rw [e 58287 (by omega), e 8 (by omega), e 10 (by omega), e 29 (by omega), e 400 (by omega)]
  exact (A0_gate (t % 16) (Nat.mod_lt _ (by omega))).2

/-- The second hypothesis of the `+-` branch, for the single seed. -/
theorem seed_D58288_late : ∀ t, 929156 ≤ t → D 58288 t = true :=
  fun t ht => seed_D58288 t (by omega)

/-- **The single seed's seventh white diagonal is `D 87866`**: the period doubles to 32 at `D 87867`, which has half density,
and `D 87868` is black. -/
theorem seed_seventh_white_diagonal :
    (∀ t : Nat, 1402404 ≤ t → D 87866 t = false) ∧ EvWhite (D 87866) ∧
    (∀ t : Nat, 1402404 ≤ t → D 87867 (t + 16) = !D 87867 t) ∧ EvAntiPer (D 87867) 16 ∧ EvPer (D 87867) 32 ∧
    HalfDensity (D 87867) ∧ (∀ t : Nat, 1402422 ≤ t → D 87868 t = true) ∧ EvBlack (D 87868) :=
  seventh_white_diagonal_and_period32_doubling_of_pos_neg seed_D58287 seed_D58288_late

/-- The band of depth 58,288 from column `-77,920`, for the periods above 58,288. -/
theorem band_58288 : LongPeriodBand 58288 58288 (-77920) :=
  fun c hc T P hP hb => not_cell_periodic_gt_of_black_diagonal 58288 77920 seed_D58288 c T P hP (by omega) (by omega)

/-- The band of depth 87,868 from column `-1,402,422`, for the periods above 87,868. -/
theorem band_87868 : LongPeriodBand 87868 87868 (-1402422) :=
  fun c hc T P hP hb =>
    not_cell_periodic_gt_eighty_seven_thousand_eight_hundred_sixty_eight_of_pos_neg seed_D58287 seed_D58288_late T hP
      (by omega) (by omega)

/-! ### Shifted `+J` black-diagonal bands (`c₀ = min 0 (J - T_J)`), `T + P > N - c` onset bounds, short/long band gluing for `Problem1`, and anti-period laws -/

/-- **Three-Parameter Monotonicity of `LongPeriodBand` (`LongPeriodBand.mono`):**
`LongPeriodBand N P₀ c₀` is antitone in depth `N` and rightmost column `c₀`, and monotone in the
period threshold `P₀`. -/
theorem LongPeriodBand.mono {N N' P₀ P₀' : Nat} {c₀ c₀' : Int}
    (h : LongPeriodBand N P₀ c₀) (hN : N' ≤ N) (hP : P₀ ≤ P₀') (hc : c₀' ≤ c₀) :
    LongPeriodBand N' P₀' c₀' :=
  fun c hc' T P hP' hb => h c (Int.le_trans hc' hc) T P (by omega) (by omega)

/-- **Exact Equivalence Between `AperiodicBand N c₀` and `LongPeriodBand N 0 c₀`
(`aperiodicBand_iff_longPeriodBand_zero`).** -/
theorem aperiodicBand_iff_longPeriodBand_zero (N : Nat) (c₀ : Int) :
    AperiodicBand N c₀ ↔ LongPeriodBand N 0 c₀ :=
  ⟨fun h => h.longPeriod 0, fun h c hc T P hP hb => h c hc T P hP hb⟩

/-- **Quantitative Onset-Plus-Period Lower Bound From `AperiodicBand`
(`onset_add_period_gt_of_aperiodicBand`):** if `AperiodicBand N c₀` holds and column `c ≤ c₀`
is `P`-periodic (`0 < P`) from tick `T`, then `(N : Int) - c < ((T + P : Nat) : Int)`. -/
theorem onset_add_period_gt_of_aperiodicBand {N : Nat} {c₀ c : Int} {T P : Nat}
    (h : AperiodicBand N c₀) (hc : c ≤ c₀) (hP : 0 < P)
    (hper : ∀ t : Nat, T ≤ t → cell (t + P) c = cell t c) :
    (N : Int) - c < ((T + P : Nat) : Int) := by
  apply Classical.byContradiction
  intro hle
  exact h c hc T P hP (by omega) hper

/-- **Quantitative Onset-Plus-Period Lower Bound From `LongPeriodBand`
(`onset_add_period_gt_of_longPeriodBand`):** if `LongPeriodBand N P₀ c₀` holds and column `c ≤ c₀`
is `P`-periodic (`P₀ < P`) from tick `T`, then `(N : Int) - c < ((T + P : Nat) : Int)`. -/
theorem onset_add_period_gt_of_longPeriodBand {N P₀ : Nat} {c₀ c : Int} {T P : Nat}
    (h : LongPeriodBand N P₀ c₀) (hc : c ≤ c₀) (hP : P₀ < P)
    (hper : ∀ t : Nat, T ≤ t → cell (t + P) c = cell t c) :
    (N : Int) - c < ((T + P : Nat) : Int) := by
  apply Classical.byContradiction
  intro hle
  exact h c hc T P hP (by omega) hper

/-- **Gluing Bounded-Period Exclusion and `LongPeriodBand` Into `AperiodicBand`
(`aperiodicBand_of_short_and_longPeriodBand`):** if all periods `0 < P ≤ P₀` are excluded to depth `N`
from column `c₀` and `LongPeriodBand N P₀ c₀` holds for `P > P₀`, then `AperiodicBand N c₀` holds. -/
theorem aperiodicBand_of_short_and_longPeriodBand {N P₀ : Nat} {c₀ : Int}
    (hshort : ∀ c : Int, c ≤ c₀ → ∀ T P : Nat, 0 < P → P ≤ P₀ →
      c ≤ -((T + P : Nat) : Int) + N → ¬ ∀ t : Nat, T ≤ t → cell (t + P) c = cell t c)
    (hlong : LongPeriodBand N P₀ c₀) :
    AperiodicBand N c₀ := by
  intro c hc T P hP hb
  rcases Nat.lt_or_ge P₀ P with hgt | hle
  · exact hlong c hc T P hgt hb
  · exact hshort c hc T P hP hle hb

/-- **Closing `Problem1` by Gluing Short-Period Exclusions and `LongPeriodBand` at Column `0`
(`problem1_of_short_and_longPeriodBand_zero`):** if for every depth `N` there exists a period
threshold `P₀` such that `LongPeriodBand N P₀ 0` holds and all periods `0 < P ≤ P₀` are excluded at
column `0` before `T + P ≤ N`, then `Rule30Prize.Problem1` holds. -/
theorem problem1_of_short_and_longPeriodBand_zero
    (hcover : ∀ N : Nat, ∃ P₀ : Nat,
      (∀ T P : Nat, 0 < P → P ≤ P₀ → T + P ≤ N → ¬ ∀ t : Nat, T ≤ t → cell (t + P) 0 = cell t 0) ∧
      LongPeriodBand N P₀ 0) :
    Rule30Prize.Problem1 := by
  unfold Rule30Prize.Problem1
  rintro ⟨T, P, hP, hper⟩
  obtain ⟨P₀, hshort, hlong⟩ := hcover (T + P)
  rcases Nat.lt_or_ge P₀ P with hgt | hle
  · exact hlong 0 (Int.le_refl 0) T P hgt (by omega) hper
  · exact hshort T P hP hle (Nat.le_refl _) hper

/-- **Right-Shifted Black-Diagonal Non-Periodicity (`not_cell_periodic_gt_of_black_diagonal_shifted`):**
because `D J (s + J) = cell (s + J) (-s)`, if `D J t = true` for all `t ≥ T_J`, then no column
`c ≤ 0` with `c ≤ (J : Int) - (T_J : Int)` and `c ≤ -(T + P) + J` can have period `P > J` from tick `T`
(strengthening `c ≤ -T_J` rightward by `+J` columns to `c ≤ min 0 (J - T_J)`). -/
theorem not_cell_periodic_gt_of_black_diagonal_shifted
    (J T_J : Nat) (hblack : ∀ t : Nat, T_J ≤ t → D J t = true)
    (c : Int) (T P : Nat) (hPJ : J < P)
    (hc_nonpos : c ≤ 0) (hc0 : c ≤ (J : Int) - (T_J : Int))
    (hc : c ≤ -((T + P : Nat) : Int) + (J : Int)) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + P) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have ht0_ge : T ≤ s + J - P := by omega
  have heq := hper (s + J - P) ht0_ge
  have h1 : (s + J - P) + P = s + J := by omega
  rw [h1, hc_eq] at heq
  have htrue : cell (s + J) (-(s : Int)) = true := by
    have hd : D J (s + J) = cell (s + J) (-(s : Int)) := by
      unfold D
      exact congrArg (cell (s + J)) (by omega)
    rw [← hd]
    exact hblack (s + J) (by omega)
  have hfalse : cell (s + J - P) (-(s : Int)) = false :=
    Rule30Jen.cell_eq_false_of_lt (s + J - P) (-(s : Int)) (by omega)
  rw [htrue, hfalse] at heq
  exact Bool.noConfusion heq

/-- **Right-Shifted Long-Period Band From Any Black Diagonal
(`longPeriodBand_of_black_diagonal_shifted`):** if diagonal `D J` is black from tick `T_J` on, then
`LongPeriodBand J J (min 0 ((J : Int) - (T_J : Int)))` holds (reaching `c₀ = 0` whenever `T_J ≤ J`). -/
theorem longPeriodBand_of_black_diagonal_shifted (J T_J : Nat)
    (hblack : ∀ t : Nat, T_J ≤ t → D J t = true) :
    LongPeriodBand J J (min 0 ((J : Int) - (T_J : Int))) :=
  fun c hc T P hP hb =>
    not_cell_periodic_gt_of_black_diagonal_shifted J T_J hblack c T P hP (by omega) (by omega) hb

/-- **Odd-Multiple Anti-Periodicity Propagation (`antiPer_odd_mul`):**
if `f (t + L) = !f t` for all `t ≥ T₀`, then for every `m : Nat` and `t ≥ T₀`,
`f (t + L * (2 * m + 1)) = !f t`. -/
theorem antiPer_odd_mul {f : Nat → Bool} {L T₀ : Nat}
    (hanti : ∀ t : Nat, T₀ ≤ t → f (t + L) = !f t) :
    ∀ (m t : Nat), T₀ ≤ t → f (t + L * (2 * m + 1)) = !f t
  | 0, t, ht => by simpa using hanti t ht
  | m + 1, t, ht => by
    have h1 := antiPer_odd_mul hanti m t ht
    have h2 := hanti (t + L * (2 * m + 1)) (by omega)
    have h3 := hanti (t + L * (2 * m + 1) + L) (by omega)
    have heq : t + L * (2 * (m + 1) + 1) = t + L * (2 * m + 1) + L + L := by
      rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 1 + 1 by omega,
        Nat.mul_add, Nat.mul_add, Nat.mul_one]
      omega
    rw [heq, h3, h2, h1, Bool.not_not]

/-- **Odd-Multiple Period Exclusion for Anti-Periodic Sequences (`not_evPer_mul_odd_of_antiPer`):**
if `f (t + L) = !f t` for all `t ≥ T₀`, then `¬ EvPer f (L * (2 * m + 1))` for every `m : Nat`. -/
theorem not_evPer_mul_odd_of_antiPer {f : Nat → Bool} {L T₀ : Nat}
    (hanti : ∀ t : Nat, T₀ ≤ t → f (t + L) = !f t) (m : Nat) :
    ¬ EvPer f (L * (2 * m + 1)) := by
  rintro ⟨T₁, hper⟩
  have ha := antiPer_odd_mul hanti m (max T₀ T₁) (Nat.le_max_left T₀ T₁)
  have hp := hper (max T₀ T₁) (Nat.le_max_right T₀ T₁)
  rw [hp] at ha
  revert ha
  cases f (max T₀ T₁) <;> decide

/-- **Anti-Periodic Sequences Are Neither Eventually White Nor Eventually Black
(`not_evWhite_and_not_evBlack_of_antiPer`).** -/
theorem not_evWhite_and_not_evBlack_of_antiPer {f : Nat → Bool} {L T₀ : Nat}
    (hanti : ∀ t : Nat, T₀ ≤ t → f (t + L) = !f t) :
    ¬ EvWhite f ∧ ¬ EvBlack f := by
  constructor
  · rintro ⟨T₁, hw⟩
    have ha := hanti (max T₀ T₁) (Nat.le_max_left T₀ T₁)
    rw [hw (max T₀ T₁) (Nat.le_max_right T₀ T₁),
      hw (max T₀ T₁ + L) (by omega)] at ha
    cases ha
  · rintro ⟨T₁, hb⟩
    have ha := hanti (max T₀ T₁) (Nat.le_max_left T₀ T₁)
    rw [hb (max T₀ T₁) (Nat.le_max_right T₀ T₁),
      hb (max T₀ T₁ + L) (by omega)] at ha
    cases ha

/-- **Right-Shifted Band of Depth `58,288` From Column `-19,632` (`band_58288_shifted`):**
improves `band_58288` rightward by `58,288` columns (`58288 - 77920 = -19632`). -/
theorem band_58288_shifted : LongPeriodBand 58288 58288 (-19632) :=
  (longPeriodBand_of_black_diagonal_shifted 58288 77920 seed_D58288).mono
    (Nat.le_refl _) (Nat.le_refl _) (by decide)

/-- **Right-Shifted Band of Depth `87,868` From Column `-1,314,554` (`band_87868_shifted`):**
improves `band_87868` rightward by `87,868` columns (`87868 - 1402422 = -1314554`). -/
theorem band_87868_shifted : LongPeriodBand 87868 87868 (-1314554) :=
  (longPeriodBand_of_black_diagonal_shifted 87868 1402422
    seed_seventh_white_diagonal.2.2.2.2.2.2.1).mono
    (Nat.le_refl _) (Nat.le_refl _) (by decide)

/-- Wheel `87,865` of `A0` has odd 16-tick XOR parity and at least one `true` bit on every 16-tick orbit. -/
theorem A0_87865_odd_and_nonwhite : ∀ r, r < 16 →
    orbitXor (fun x => (x + 1) % 16) (Sp A0 87865) 16 r = true ∧
    orbitHasTrue (fun x => (x + 1) % 16) (Sp A0 87865) 16 r = true := by
  decide +kernel

/-- **`D 53209` of the single seed is black from tick `77,920` (`seed_D53209_early`):**
improves the generic `847,906` onset of `D 53209` down to `77,920` via `seed_low` and `A0_white_black`. -/
theorem seed_D53209_early : ∀ t, 77920 ≤ t → D 53209 t = true := by
  intro t ht
  rw [seed_low t ht (j := 53209) (by omega), Sp_mod A0_return]
  exact (A0_white_black (t % 16) (Nat.mod_lt _ (by omega))).2.2.2.2.2.1

/-- **`D 87867` of the single seed is `16`-anti-periodic already from tick `177,560` (`seed_D87867_early`):**
improves the `1,402,404` onset in `seed_seventh_white_diagonal` down to `177,560` (`7.9x` earlier)
directly from `seed_eq_A0` and `A0_87865_odd_and_nonwhite`. -/
theorem seed_D87867_early : ∀ t, 177560 ≤ t → D 87867 (t + 16) = !D 87867 t :=
  (D_antiperiodic_and_halfDensity_of_white_and_odd_orbitXor
    (fun r => (r + 1) % 16) (fun t => t % 16) 16 87865 177560 (by decide) (Sp A0 87865)
    (fun t _ => by omega)
    (fun t _ => by omega)
    (fun t ht => by rw [seed_eq_A0 (by omega) ht, Sp_mod A0_return])
    (fun t ht => (seed_white_black ht).1.2.2.2.2.2.2)
    (fun t _ => (A0_87865_odd_and_nonwhite (t % 16) (Nat.mod_lt _ (by omega))).1)).1

/-- **`D 87868` of the single seed is black already from tick `177,578` (`seed_D87868_early`),
and `D 87869 (t + 1) = !D 87867 t` from tick `177,578` (`seed_D87869_succ_eq_not_D87867`):**
improves the `1,402,422` onset of `D 87868` down to `177,578` (`7.9x` earlier). -/
theorem seed_D87868_early_and_D87869_complement :
    (∀ t : Nat, 177578 ≤ t → D 87868 t = true) ∧
    EvBlack (D 87868) ∧
    (∀ t : Nat, 177578 ≤ t → D 87869 (t + 1) = !D 87867 t) :=
  D_black_shield_after_white_of_nonwhite_gate
    (fun r => (r + 1) % 16) (fun t => t % 16) 16 87865 177560 (Sp A0 87865)
    (fun t _ => by omega)
    (fun t ht => by rw [seed_eq_A0 (by omega) ht, Sp_mod A0_return])
    (fun t ht => (seed_white_black ht).1.2.2.2.2.2.2)
    (fun t _ => (A0_87865_odd_and_nonwhite (t % 16) (Nat.mod_lt _ (by omega))).2)

theorem seed_D87868_early : ∀ t : Nat, 177578 ≤ t → D 87868 t = true :=
  seed_D87868_early_and_D87869_complement.1

/-- **Right-Shifted Band of Depth `401` From Column `-2,593` (`band_401_shifted`):**
covers all periods `P > 401` from column `401 - 2994 = -2593`. -/
theorem band_401_shifted : LongPeriodBand 401 401 (-2593) :=
  (longPeriodBand_of_black_diagonal_shifted 401 2994 D_four_hundred_one_eq_true).mono
    (Nat.le_refl _) (Nat.le_refl _) (by decide)

/-- **Right-Shifted Band of Depth `53,209` From Column `-24,711` (`band_53209_shifted`):**
covers all periods `P > 53,209` from column `53209 - 77920 = -24711`. -/
theorem band_53209_shifted : LongPeriodBand 53209 53209 (-24711) :=
  (longPeriodBand_of_black_diagonal_shifted 53209 77920 seed_D53209_early).mono
    (Nat.le_refl _) (Nat.le_refl _) (by decide)

/-- **Early-Onset Band of Depth `87,868` From Column `-177,578` (`band_87868_early`):**
improves `band_87868` from `-1,402,422` to `-177,578` via `seed_D87868_early`. -/
theorem band_87868_early : LongPeriodBand 87868 87868 (-177578) :=
  fun c hc T P hP hb =>
    not_cell_periodic_gt_of_black_diagonal 87868 177578 seed_D87868_early c T P hP (by omega) (by omega)

/-- **Early-Onset Right-Shifted Band of Depth `87,868` From Column `-89,710` (`band_87868_early_shifted`):**
combines `seed_D87868_early` (`T_J = 177,578`) with the `+J` shift (`87868 - 177578 = -89710`),
improving `band_87868` rightward by `1,312,712` columns (`15.6x` closer to column `0`). -/
theorem band_87868_early_shifted : LongPeriodBand 87868 87868 (-89710) :=
  (longPeriodBand_of_black_diagonal_shifted 87868 177578 seed_D87868_early).mono
    (Nat.le_refl _) (Nat.le_refl _) (by decide)

end Ruliology.CellularAutomata.Rule30AperiodicBand
