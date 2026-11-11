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

end Ruliology.CellularAutomata.Rule30AperiodicBand
