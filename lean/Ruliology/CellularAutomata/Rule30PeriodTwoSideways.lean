module

public import Ruliology.CellularAutomata.Rule30PeriodTwoCoupled

/-!
# Rule 30, period 2: the coupled question in finite configurations and sideways

`Rule30PeriodTwoCoupled.CQ01` is the open statement that excludes an eventual period `2`. This
module restates it in two ways, locates the one candidate counterexample for each right half, and
proves the barrier that goes with them.

**Finite configurations.**
* `CQ01_iff_no_finite_alternating`: `CQ01` holds exactly when no configuration with finitely many
  black cells has center column `1, 0, 1, 0, …` from time `0`: it is the period-2 case of the
  finite-configuration version of Problem 1.
* `Q01_no_leftfinite_alternating`: `Q01` already covers every configuration whose left half is
  finite, whatever its right half.

**Sideways.** For a right half `R`, `u R s` is column `1` at the white step `2 s + 1` of the right
half driven by the alternating column.
* `Psi R`: the left row that keeps the center alternating forever against `R`. It is the
  constrained start `Theta` whose free bits are the complement of `u R` (`Psi_inX`, `Psi_free`).
  `Psi_unique`: every left row that does so agrees with `Psi R` at every depth `≥ 1`.
* `CQ01_iff_Psi`: `CQ01` says that `Psi R` has infinitely many black cells for every finitely
  supported `R`.
* `not_finSupp_Psi_of_eventuallyPeriodic` (the absorption route): this holds whenever `u R` is
  eventually periodic.
* `not_finSupp_Psi_of_R2`: it holds for `R` whenever it holds for `R2 R`, the right half two steps
  later.

**Exact death.** A left row `L` keeps the center alternating exactly until the first depth `d ≥ 1`
where it differs from `Psi R`.
* `exact_death`: column `-1` of the run from `L` meets the coupled constraint (`Meets`) at every
  time `t < d - 1` and violates it at time `d - 1`. This is left-permutivity
  (`Rule30ZeroBoundary.pivot`).
* `alternates_iff_meets`: in the configuration `glue L R` (left row `L`, black center, right half
  `R`), the center alternates through time `n` exactly when `L` meets the constraint at every time
  `t < n`. `exact_death_center`: the center alternates through time `d - 1` and not at time `d`.
* `truncation_death`: the truncation of `Psi R` at width `W` keeps the center alternating exactly
  until the first black depth of `Psi R` beyond `W`.
So for each `R` the row `Psi R` is the only candidate counterexample to `CQ01`.

**The `R = ∅` milestone.** `CQ01Empty` (**open**): `Psi empty` has infinitely many black cells.
`CQ01Empty_of_CQ01`. `CQ01Empty_iff`: no finite configuration whose right half (positions `≥ 1`) is
white keeps the center alternating from time `0`.

**Barrier.** `alternates_long`: from finite configurations the center can alternate for any number
of steps (the cut ether `Rule30ZeroBoundaryBarriers.c7cut`). So
`no_finite_abstract_ranking_coupled`: no ranking through a finite abstraction of configurations
decreases at every double step over which the center flips twice. This is the two-sided form of
barrier B1 (`Rule30ZeroBoundaryBarriers.no_finite_abstract_ranking`).

The exact-death identity was first observed numerically, for `R = ∅` and widths up to `300`.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30PeriodTwoSideways

open Rule30Jen Rule30Realization Rule30ZeroBoundary Rule30PeriodTwoCoupled
open Rule30Ether (drv drv_col0 drv_init)

/-- A configuration with finitely many black cells. -/
def FinConfig (x : Int → Bool) : Prop := ∃ W : Nat, ∀ p : Int, W < p.natAbs → x p = false

theorem altCol_even (s : Nat) : altCol (2 * s) = true := by
  unfold altCol; rw [show 2 * s % 2 = 0 by omega]; rfl

theorem altCol_odd (s : Nat) : altCol (2 * s + 1) = false := by
  unfold altCol; rw [show (2 * s + 1) % 2 = 1 by omega]; rfl

theorem alt_even (f : Nat → Bool) (s : Nat) : alt f (2 * s) = true := by
  unfold alt; rw [ite_eq_left (by omega)]

theorem alt_odd (f : Nat → Bool) (s : Nat) : alt f (2 * s + 1) = f s := by
  unfold alt; rw [ite_eq_right (by omega), show (2 * s + 1) / 2 = s by omega]

theorem evol_congr {x : Int → Bool} {t : Nat} {p q : Int} (h : p = q) : evol x t p = evol x t q :=
  h ▸ rfl

/-- The driven right half only reads `x` at the positions `≥ 1`. -/
theorem drv_congr {c x y : Nat → Bool} (h : ∀ p, 1 ≤ p → x p = y p) :
    ∀ t p, drv c x t p = drv c y t p
  | 0, 0 => by simp [drv]
  | 0, p + 1 => by rw [drv_init _ _ _ (by omega), drv_init _ _ _ (by omega)]; exact h _ (by omega)
  | t + 1, 0 => by rw [drv_col0, drv_col0]
  | t + 1, p + 1 => by
    show rule (drv c x t p) (drv c x t (p + 1)) (drv c x t (p + 2)) =
      rule (drv c y t p) (drv c y t (p + 1)) (drv c y t (p + 2))
    rw [drv_congr h t p, drv_congr h t (p + 1), drv_congr h t (p + 2)]

/-! ### From a finite configuration with alternating center to a violation of `CQ01` -/

section Forward
variable (x : Int → Bool) (hx : ∀ t, evol x t 0 = altCol t)
include hx

theorem alt_center_step (t : Nat) :
    altCol (t + 1) = xor (evol x t (-1)) (altCol t || evol x t 1) := by
  rw [← hx (t + 1), ← hx t]
  show rule (evol x t (0 - 1)) (evol x t 0) (evol x t (0 + 1)) = _
  rfl

theorem col_m1_even (s : Nat) : evol x (2 * s) (-1) = true := by
  have h := alt_center_step x hx (2 * s)
  rw [altCol_even, altCol_odd] at h
  revert h; cases evol x (2 * s) (-1) <;> simp

theorem col_m1_odd (s : Nat) : evol x (2 * s + 1) (-1) = !evol x (2 * s + 1) 1 := by
  have h := alt_center_step x hx (2 * s + 1)
  rw [show 2 * s + 1 + 1 = 2 * (s + 1) by omega, altCol_even, altCol_odd] at h
  revert h; cases evol x (2 * s + 1) (-1) <;> cases evol x (2 * s + 1) 1 <;> simp

theorem right_is_drv : ∀ (t p : Nat), drv altCol (fun p => x (p : Int)) t p = evol x t (p : Int)
  | 0, 0 => by rw [drv_col0]; exact (hx 0).symm
  | 0, p + 1 => drv_init _ _ (p + 1) (by omega)
  | t + 1, 0 => by rw [drv_col0]; exact (hx (t + 1)).symm
  | t + 1, p + 1 => by
    show rule (drv altCol _ t p) (drv altCol _ t (p + 1)) (drv altCol _ t (p + 2)) =
      rule (evol x t (((p + 1 : Nat) : Int) - 1)) (evol x t ((p + 1 : Nat) : Int))
        (evol x t (((p + 1 : Nat) : Int) + 1))
    rw [right_is_drv t p, right_is_drv t (p + 1), right_is_drv t (p + 2),
      evol_congr (show ((p + 1 : Nat) : Int) - 1 = (p : Int) by omega),
      evol_congr (show ((p + 1 : Nat) : Int) + 1 = ((p + 2 : Nat) : Int) by omega)]

theorem left_is_zrow :
    ∀ (t k : Nat), 1 ≤ k → zrow (fun k => x (-(k : Int))) t k = evol x t (-(k : Int))
  | 0, k, hk => zrow_zero_of_pos _ hk
  | t + 1, k, hk => by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [zrow_succ]
    show _ = rule (evol x t (-((j + 1 : Nat) : Int) - 1)) (evol x t (-((j + 1 : Nat) : Int)))
      (evol x t (-((j + 1 : Nat) : Int) + 1))
    rw [left_is_zrow t (j + 2) (by omega), left_is_zrow t (j + 1) (by omega),
      evol_congr (show -((j + 1 : Nat) : Int) - 1 = -((j + 2 : Nat) : Int) by omega)]
    cases j with
    | zero =>
      rw [zrow_wall, evol_congr (show -((0 + 1 : Nat) : Int) + 1 = 0 by omega), hx t]
      obtain ⟨s, rfl | rfl⟩ : ∃ s, t = 2 * s ∨ t = 2 * s + 1 := ⟨t / 2, by omega⟩
      · rw [evol_congr (show -((0 + 1 : Nat) : Int) = -1 by omega), col_m1_even x hx s]; rfl
      · rw [altCol_odd]; rfl
    | succ j =>
      rw [left_is_zrow t (j + 1) (by omega),
        evol_congr (show -((j + 1 + 1 : Nat) : Int) + 1 = -((j + 1 : Nat) : Int) by omega)]
      rfl

theorem left_inX : InX (fun k => x (-(k : Int))) := fun s => by
  rw [left_is_zrow x hx (2 * s) 1 (by omega)]
  exact (evol_congr (by omega)).trans (col_m1_even x hx s)

theorem left_coupled (s : Nat) :
    zrow (fun k => x (-(k : Int))) (2 * s + 1) 1 = !drv altCol (fun p => x (p : Int)) (2 * s + 1) 1 := by
  rw [left_is_zrow x hx (2 * s + 1) 1 (by omega), right_is_drv x hx (2 * s + 1) 1,
    evol_congr (show -((1 : Nat) : Int) = -1 by omega)]
  exact col_m1_odd x hx s

end Forward

/-! ### Gluing a left row, a black center and a right half -/

/-- Glue a left row `L` (depth `k` at position `-k`), a black center and a right half `R`. -/
def glue (L R : Nat → Bool) (p : Int) : Bool :=
  if p < 0 then L (-p).toNat else if p = 0 then true else R p.toNat

/-- The claimed evolution: the zero-boundary left half and the right half driven by `altCol`. -/
def gluedRun (L R : Nat → Bool) (t : Nat) (p : Int) : Bool :=
  if p < 0 then zrow L t (-p).toNat else drv altCol R t p.toNat

theorem gluedRun_m1 (L R : Nat → Bool) (t : Nat) : gluedRun L R t (-1) = zrow L t 1 := by
  unfold gluedRun; rw [ite_eq_left (by omega)]; rfl

theorem gluedRun_zero (L R : Nat → Bool) (t : Nat) : gluedRun L R t 0 = altCol t := by
  unfold gluedRun; rw [ite_eq_right (by omega)]; exact drv_col0 _ _ t

theorem gluedRun_one (L R : Nat → Bool) (t : Nat) : gluedRun L R t 1 = drv altCol R t 1 := by
  unfold gluedRun; rw [ite_eq_right (by omega)]; rfl

/-- The gluing is the true evolution as long as the coupled constraint holds. -/
theorem evol_glue_upto (L R : Nat → Bool) (n : Nat)
    (hX : ∀ s, 2 * s < n → zrow L (2 * s) 1 = true)
    (hC : ∀ s, 2 * s + 1 < n → zrow L (2 * s + 1) 1 = !drv altCol R (2 * s + 1) 1) :
    ∀ t p, t ≤ n → evol (glue L R) t p = gluedRun L R t p
  | 0, p, _ => by
    show glue L R p = gluedRun L R 0 p
    unfold glue gluedRun
    by_cases h : p < 0
    · rw [ite_eq_left h, ite_eq_left h]
      obtain ⟨k, hk⟩ : ∃ k : Nat, (-p).toNat = k + 1 := ⟨(-p).toNat - 1, by omega⟩
      rw [hk]; rfl
    · rw [ite_eq_right h, ite_eq_right h]
      by_cases h0 : p = 0
      · rw [ite_eq_left h0, show p.toNat = 0 by omega, drv_col0]; rfl
      · rw [ite_eq_right h0, drv_init _ _ _ (by omega)]
  | t + 1, p, ht => by
    show rule (evol (glue L R) t (p - 1)) (evol (glue L R) t p) (evol (glue L R) t (p + 1)) =
      gluedRun L R (t + 1) p
    rw [evol_glue_upto L R n hX hC t (p - 1) (by omega), evol_glue_upto L R n hX hC t p (by omega),
      evol_glue_upto L R n hX hC t (p + 1) (by omega)]
    rcases (show p ≤ -2 ∨ p = -1 ∨ p = 0 ∨ p = 1 ∨ 2 ≤ p by omega) with h | h | h | h | h
    · -- deep in the left half
      unfold gluedRun
      rw [ite_eq_left (show p - 1 < 0 by omega), ite_eq_left (show p < 0 by omega),
        ite_eq_left (show p + 1 < 0 by omega), ite_eq_left (show p < 0 by omega)]
      obtain ⟨k, hk⟩ : ∃ k : Nat, (-p).toNat = k + 2 := ⟨(-p).toNat - 2, by omega⟩
      rw [show (-(p - 1)).toNat = k + 3 by omega, hk, show (-(p + 1)).toNat = k + 1 by omega]
      rfl
    · -- column -1: the wall is white, and the center is black only where column -1 is
      unfold gluedRun
      rw [ite_eq_left (show p - 1 < 0 by omega), ite_eq_left (show p < 0 by omega),
        ite_eq_right (show ¬ p + 1 < 0 by omega), ite_eq_left (show p < 0 by omega),
        show (-(p - 1)).toNat = 2 by omega, show (-p).toNat = 1 by omega,
        show (p + 1).toNat = 0 by omega, drv_col0, zrow_succ L t 0, zrow_wall]
      show xor (zrow L t 2) (zrow L t 1 || altCol t) = xor (zrow L t 2) (zrow L t 1 || false)
      obtain ⟨s, rfl | rfl⟩ : ∃ s, t = 2 * s ∨ t = 2 * s + 1 := ⟨t / 2, by omega⟩
      · rw [hX s (by omega)]; rfl
      · rw [altCol_odd]
    · -- the center
      unfold gluedRun
      rw [ite_eq_left (show p - 1 < 0 by omega), ite_eq_right (show ¬ p < 0 by omega),
        ite_eq_right (show ¬ p + 1 < 0 by omega), ite_eq_right (show ¬ p < 0 by omega),
        show (-(p - 1)).toNat = 1 by omega, show p.toNat = 0 by omega,
        show (p + 1).toNat = 1 by omega, drv_col0, drv_col0]
      show xor (zrow L t 1) (altCol t || drv altCol R t 1) = altCol (t + 1)
      obtain ⟨s, rfl | rfl⟩ : ∃ s, t = 2 * s ∨ t = 2 * s + 1 := ⟨t / 2, by omega⟩
      · rw [hX s (by omega), altCol_even, altCol_odd]; rfl
      · rw [hC s (by omega), altCol_odd, show 2 * s + 1 + 1 = 2 * (s + 1) by omega, altCol_even]
        cases drv altCol R (2 * s + 1) 1 <;> rfl
    · -- column 1
      unfold gluedRun
      rw [ite_eq_right (show ¬ p - 1 < 0 by omega), ite_eq_right (show ¬ p < 0 by omega),
        ite_eq_right (show ¬ p + 1 < 0 by omega), ite_eq_right (show ¬ p < 0 by omega),
        show (p - 1).toNat = 0 by omega, show p.toNat = 0 + 1 by omega,
        show (p + 1).toNat = 2 by omega]
      rfl
    · -- deep in the right half
      unfold gluedRun
      rw [ite_eq_right (show ¬ p - 1 < 0 by omega), ite_eq_right (show ¬ p < 0 by omega),
        ite_eq_right (show ¬ p + 1 < 0 by omega), ite_eq_right (show ¬ p < 0 by omega)]
      obtain ⟨k, hk⟩ : ∃ k : Nat, p.toNat = k + 1 := ⟨p.toNat - 1, by omega⟩
      rw [show (p - 1).toNat = k by omega, hk, show (p + 1).toNat = k + 2 by omega]
      rfl

theorem evol_glue (L R : Nat → Bool) (hX : ∀ s, zrow L (2 * s) 1 = true)
    (hC : ∀ s, zrow L (2 * s + 1) 1 = !drv altCol R (2 * s + 1) 1) (t : Nat) (p : Int) :
    evol (glue L R) t p = gluedRun L R t p :=
  evol_glue_upto L R t (fun s _ => hX s) (fun s _ => hC s) t p (Nat.le_refl t)

theorem glue_fin {L R : Nat → Bool} (hL : FinSupp L) (hR : FinSupp R) : FinConfig (glue L R) := by
  obtain ⟨WL, hWL⟩ := hL
  obtain ⟨WR, hWR⟩ := hR
  refine ⟨max WL WR, fun p hp => ?_⟩
  unfold glue
  by_cases hn : p < 0
  · rw [ite_eq_left hn]; exact hWL _ (by omega)
  · rw [ite_eq_right hn, ite_eq_right (by omega)]; exact hWR _ (by omega)

/-! ### Finite configurations -/

/-- **`CQ01` is the period-2 case of the finite-configuration problem**: it holds exactly when no
configuration with finitely many black cells has center column `1, 0, 1, 0, …` from time `0`. -/
theorem CQ01_iff_no_finite_alternating :
    CQ01 ↔ ¬ ∃ x : Int → Bool, FinConfig x ∧ ∀ t, evol x t 0 = altCol t := by
  constructor
  · rintro hC ⟨x, ⟨W, hW⟩, hx⟩
    exact hC ⟨fun k => x (-(k : Int)), fun p => x (p : Int), ⟨W, fun k hk => hW _ (by omega)⟩,
      ⟨W, fun p hp => hW _ (by omega)⟩, left_inX x hx, left_coupled x hx⟩
  · rintro h ⟨L, R, hL, hR, hX, hC⟩
    refine h ⟨glue L R, glue_fin hL hR, fun t => ?_⟩
    rw [evol_glue L R hX hC t 0, gluedRun_zero]

/-- **`Q01` already covers every configuration whose left half is finite** (number-like in Kopra's
sense; the right half is arbitrary): none has center column `1, 0, 1, 0, …` from time `0`. -/
theorem Q01_no_leftfinite_alternating (hQ : Q01) :
    ¬ ∃ x : Int → Bool, (∃ W : Nat, ∀ p : Int, p < -(W : Int) → x p = false) ∧
      ∀ t, evol x t 0 = altCol t := by
  rintro ⟨x, ⟨W, hW⟩, hx⟩
  exact hQ (fun k => x (-(k : Int))) ⟨W, fun k hk => hW _ (by omega)⟩ (left_inX x hx)

/-! ### The sideways row `Psi R` -/

/-- Column `1` at the white step `2 s + 1` of the right half `R` driven by the alternating
column. -/
def u (R : Nat → Bool) (s : Nat) : Bool := drv altCol R (2 * s + 1) 1

/-- **The sideways row**: the constrained start whose free bits are the complement of `u R`. -/
def Psi (R : Nat → Bool) : Nat → Bool := Theta fun s => !u R s

theorem Psi_inX (R : Nat → Bool) : InX (Psi R) := Theta_inX _

theorem Psi_free (R : Nat → Bool) (s : Nat) :
    zrow (Psi R) (2 * s + 1) 1 = !drv altCol R (2 * s + 1) 1 :=
  Theta_free _ s

theorem Psi_col (R : Nat → Bool) (t : Nat) : zrow (Psi R) t 1 = alt (fun s => !u R s) t :=
  Theta_col _ t

/-- **Every left row that keeps the center alternating against `R` is `Psi R`** at every depth
`≥ 1`. -/
theorem Psi_unique {L R : Nat → Bool} (hX : InX L)
    (hC : ∀ s, zrow L (2 * s + 1) 1 = !drv altCol R (2 * s + 1) 1) : zrow L 0 = Psi R :=
  Theta_unique hX hC

/-- **`CQ01` sideways**: for every finitely supported right half `R`, the row `Psi R` has
infinitely many black cells. -/
theorem CQ01_iff_Psi : CQ01 ↔ ∀ R, FinSupp R → ¬ FinSupp (Psi R) := by
  constructor
  · intro hC R hR hP
    exact hC ⟨Psi R, R, hP, hR, Psi_inX R, Psi_free R⟩
  · rintro h ⟨L, R, ⟨W, hW⟩, hR, hX, hC⟩
    refine h R hR ⟨W, fun k hk => ?_⟩
    rw [← Psi_unique hX hC, zrow_zero_of_pos _ (by omega)]
    exact hW k hk

/-- **The absorption route**: if `u R` is eventually periodic, `Psi R` has infinitely many black
cells, because the free bits of a finitely supported constrained start are never eventually periodic
(`Rule30ZeroBoundary.free_not_eventuallyPeriodic`). -/
theorem not_finSupp_Psi_of_eventuallyPeriodic (R : Nat → Bool) (h : EventuallyPeriodic (u R)) :
    ¬ FinSupp (Psi R) := by
  intro hfin
  apply free_not_eventuallyPeriodic hfin (Psi_inX R)
  obtain ⟨T, P, hP, hper⟩ := h
  refine ⟨T, P, hP, fun t ht => ?_⟩
  show zrow (Psi R) (2 * (t + P) + 1) 1 = zrow (Psi R) (2 * t + 1) 1
  rw [Psi_free, Psi_free]
  exact congrArg (!·) (hper t ht)

/-- Restarting the driven right half at time `a`. -/
theorem drv_shift (c x : Nat → Bool) (a : Nat) :
    ∀ t p, drv c x (a + t) p = drv (fun t => c (a + t)) (fun p => drv c x a p) t p
  | 0, 0 => by rw [drv_col0, drv_col0]
  | 0, p + 1 => by rw [drv_init _ _ _ (by omega)]; rfl
  | t + 1, 0 => by rw [drv_col0, drv_col0]
  | t + 1, p + 1 => by
    show rule (drv c x (a + t) p) (drv c x (a + t) (p + 1)) (drv c x (a + t) (p + 2)) =
      rule (drv _ _ t p) (drv _ _ t (p + 1)) (drv _ _ t (p + 2))
    rw [drv_shift c x a t p, drv_shift c x a t (p + 1), drv_shift c x a t (p + 2)]

/-- The right half two steps later. -/
def R2 (R : Nat → Bool) : Nat → Bool := fun p => drv altCol R 2 p

theorem u_R2 (R : Nat → Bool) (s : Nat) : u (R2 R) s = u R (s + 1) := by
  unfold u R2
  rw [show 2 * (s + 1) + 1 = 2 + (2 * s + 1) by omega, drv_shift altCol R 2 (2 * s + 1) 1]
  have : (fun t => altCol (2 + t)) = altCol := funext fun t => by
    unfold altCol; rw [show (2 + t) % 2 = t % 2 by omega]
  rw [this]

/-- **The statements propagate backwards in time**: if the row for the right half two steps later
has infinitely many black cells, so has `Psi R`. For example `CQ01Empty` follows from the case of
the right half `11`, which the white right half becomes two steps later. -/
theorem not_finSupp_Psi_of_R2 (R : Nat → Bool) (h : ¬ FinSupp (Psi (R2 R))) :
    ¬ FinSupp (Psi R) := by
  rintro ⟨W, hW⟩
  have hX : InX (zrow (Psi R) 2) := fun s => by
    rw [← zrow_shift, show 2 + 2 * s = 2 * (s + 1) by omega]
    exact Psi_inX R (s + 1)
  have hC : ∀ s, zrow (zrow (Psi R) 2) (2 * s + 1) 1 = !drv altCol (R2 R) (2 * s + 1) 1 := by
    intro s
    rw [← zrow_shift, show 2 + (2 * s + 1) = 2 * (s + 1) + 1 by omega, Psi_free]
    exact congrArg (!·) (u_R2 R s).symm
  refine h ⟨W + 2, fun k hk => ?_⟩
  rw [← Psi_unique hX hC, zrow_zero_of_pos _ (by omega)]
  exact zrow_fin hW 2 k (by omega)

/-! ### Exact death -/

/-- Column `-1` of the run from `L` meets the coupled constraint against `R` at time `t`: black at
the even times, the complement of column `1` of the driven right half at the odd times. -/
def Meets (R L : Nat → Bool) (t : Nat) : Prop := zrow L t 1 = alt (fun s => !u R s) t

/-- **Exact death.** If the left row `L` first differs from `Psi R` at depth `d ≥ 1`, its run meets
the coupled constraint at every time `t < d - 1` and violates it at time `d - 1`. -/
theorem exact_death {L R : Nat → Bool} {d : Nat} (hd : 1 ≤ d)
    (hag : ∀ i, 1 ≤ i → i < d → L i = Psi R i) (hne : L d ≠ Psi R d) :
    (∀ t, t + 1 < d → Meets R L t) ∧ ¬ Meets R L (d - 1) := by
  refine ⟨fun t ht => ?_, fun hm => ?_⟩
  · show zrow L t 1 = _
    rw [← Psi_col R t]
    exact zrow_light_cone t 1 fun i h1 h2 => hag i h1 (by omega)
  · refine pivot (L := L) (L' := Psi R) (t := d - 1) (fun i h1 h2 => hag i h1 (by omega))
      (by rw [show d - 1 + 1 = d by omega]; exact hne) ?_
    rw [hm, Psi_col]

/-- In `glue L R`, the center alternates through time `n` exactly when `L` meets the coupled
constraint at every time `t < n`. -/
theorem alternates_iff_meets (L R : Nat → Bool) : ∀ n,
    (∀ t, t ≤ n → evol (glue L R) t 0 = altCol t) ↔ ∀ t, t < n → Meets R L t
  | 0 => by
    refine ⟨fun _ t ht => absurd ht (by omega), fun _ t ht => ?_⟩
    obtain rfl : t = 0 := by omega
    show glue L R 0 = altCol 0
    unfold glue altCol; simp
  | n + 1 => by
    have key : (∀ t, t < n → Meets R L t) →
        (evol (glue L R) (n + 1) 0 = altCol (n + 1) ↔ Meets R L n) := by
      intro hm
      have hg := evol_glue_upto L R n
        (fun s hs => by have := hm (2 * s) hs; rwa [Meets, alt_even] at this)
        (fun s hs => by have := hm (2 * s + 1) hs; rwa [Meets, alt_odd] at this)
      show rule (evol (glue L R) n (0 - 1)) (evol (glue L R) n 0) (evol (glue L R) n (0 + 1)) =
        altCol (n + 1) ↔ _
      rw [hg n _ (Nat.le_refl n), hg n _ (Nat.le_refl n), hg n _ (Nat.le_refl n),
        show (0 : Int) - 1 = -1 by rfl, show (0 : Int) + 1 = 1 by rfl, gluedRun_m1, gluedRun_zero,
        gluedRun_one]
      unfold Meets rule
      obtain ⟨s, rfl | rfl⟩ : ∃ s, n = 2 * s ∨ n = 2 * s + 1 := ⟨n / 2, by omega⟩
      · rw [altCol_even, altCol_odd, alt_even]
        cases zrow L (2 * s) 1 <;> simp
      · rw [altCol_odd, show 2 * s + 1 + 1 = 2 * (s + 1) by omega, altCol_even, alt_odd]
        unfold u
        cases zrow L (2 * s + 1) 1 <;> cases drv altCol R (2 * s + 1) 1 <;> simp
    constructor
    · intro h
      have hn := (alternates_iff_meets L R n).1 fun t ht => h t (by omega)
      intro t ht
      by_cases htn : t < n
      · exact hn t htn
      · obtain rfl : t = n := by omega
        exact (key hn).1 (h (t + 1) (Nat.le_refl _))
    · intro h
      have hn : ∀ t, t < n → Meets R L t := fun t ht => h t (by omega)
      have hl := (alternates_iff_meets L R n).2 hn
      intro t ht
      by_cases htn : t ≤ n
      · exact hl t htn
      · obtain rfl : t = n + 1 := by omega
        exact (key hn).2 (h n (by omega))

/-- **Exact death for configurations.** If `L` first differs from `Psi R` at depth `d ≥ 1`, the
center of `glue L R` alternates through time `d - 1` and not at time `d`. -/
theorem exact_death_center {L R : Nat → Bool} {d : Nat} (hd : 1 ≤ d)
    (hag : ∀ i, 1 ≤ i → i < d → L i = Psi R i) (hne : L d ≠ Psi R d) :
    (∀ t, t < d → evol (glue L R) t 0 = altCol t) ∧ evol (glue L R) d 0 ≠ altCol d := by
  obtain ⟨h1, h2⟩ := exact_death hd hag hne
  have hA := (alternates_iff_meets L R (d - 1)).2 fun t ht => h1 t (by omega)
  refine ⟨fun t ht => hA t (by omega), fun he => h2 ?_⟩
  refine (alternates_iff_meets L R d).1 (fun t ht => ?_) (d - 1) (by omega)
  by_cases htd : t < d
  · exact hA t (by omega)
  · obtain rfl : t = d := by omega
    exact he

/-- **The truncations of `Psi R`**: cut at width `W`, the row keeps the center alternating exactly
until the first black depth `d` of `Psi R` beyond `W`. -/
theorem truncation_death (R : Nat → Bool) {W d : Nat} (hWd : W < d) (hd : Psi R d = true)
    (hz : ∀ k, W < k → k < d → Psi R k = false) :
    (∀ t, t < d → evol (glue (truncate (Psi R) W) R) t 0 = altCol t) ∧
      evol (glue (truncate (Psi R) W) R) d 0 ≠ altCol d := by
  refine exact_death_center (by omega) (fun i _ h2 => ?_) ?_
  · unfold truncate
    by_cases hi : i ≤ W
    · simp [hi]
    · rw [hz i (by omega) h2]; simp
  · unfold truncate
    rw [hd]
    simp
    omega

/-! ### The `R = ∅` milestone -/

/-- The white right half. -/
def empty : Nat → Bool := fun _ => false

/-- **The `R = ∅` milestone** (open): the row that keeps the center alternating against the white
right half has infinitely many black cells. -/
def CQ01Empty : Prop := ¬ FinSupp (Psi empty)

theorem CQ01Empty_of_CQ01 (h : CQ01) : CQ01Empty :=
  CQ01_iff_Psi.1 h empty ⟨0, fun _ _ => rfl⟩

/-- **`CQ01Empty` for configurations**: no finite configuration whose right half is white keeps
the center alternating from time `0`. -/
theorem CQ01Empty_iff : CQ01Empty ↔
    ¬ ∃ x : Int → Bool, FinConfig x ∧ (∀ p : Int, 0 < p → x p = false) ∧
      ∀ t, evol x t 0 = altCol t := by
  constructor
  · rintro hE ⟨x, ⟨W, hW⟩, hR, hx⟩
    have hC : ∀ s, zrow (fun k => x (-(k : Int))) (2 * s + 1) 1 = !drv altCol empty (2 * s + 1) 1 :=
      fun s => by
        rw [left_coupled x hx s, drv_congr (fun p hp => hR p (by omega)) (2 * s + 1) 1]
        rfl
    refine hE ⟨W, fun k hk => ?_⟩
    rw [← Psi_unique (left_inX x hx) hC, zrow_zero_of_pos _ (by omega)]
    exact hW _ (by omega)
  · rintro h hP
    refine h ⟨glue (Psi empty) empty, glue_fin hP ⟨0, fun _ _ => rfl⟩, fun p hp => ?_, fun t => ?_⟩
    · unfold glue; rw [ite_eq_right (by omega), ite_eq_right (by omega)]; rfl
    · rw [evol_glue _ _ (Psi_inX empty) (Psi_free empty) t 0, gluedRun_zero]

/-! ### Barrier: alternation from finite configurations is unbounded -/

/-- **From finite configurations the center can alternate for any number of steps.** -/
theorem alternates_long (n : Nat) : ∃ x : Int → Bool, FinConfig x ∧
    ∀ t, t ≤ n → evol x (t + 1) 0 = !evol x t 0 := by
  refine ⟨Rule30ZeroBoundaryBarriers.c7cut n, ⟨7 * n + 6, fun p hp => ?_⟩, fun t ht => ?_⟩
  · rcases (show p < -(7 * (n : Int) + 1) ∨ 7 * (n : Int) + 6 < p by omega) with h | h
    · exact Rule30ZeroBoundaryBarriers.c7cut_below n p h
    · exact Rule30ZeroBoundaryBarriers.c7cut_above n p h
  · rw [Rule30ZeroBoundaryBarriers.c7cut_agree n (t + 1) 0 (by omega) (by omega),
      Rule30ZeroBoundaryBarriers.c7cut_agree n t 0 (by omega) (by omega)]
    exact Rule30ZeroBoundaryBarriers.c7_center t

/-- The center flips at both of the next two steps. -/
def FlipsTwice (x : Int → Bool) : Prop := evol x 1 0 = !evol x 0 0 ∧ evol x 2 0 = !evol x 1 0

/-- **No ranking through a finite abstraction** of configurations decreases at every double step
over which the center of a finite configuration flips twice. -/
theorem no_finite_abstract_ranking_coupled {A : Type} (Ls : List A) (α : (Int → Bool) → A)
    (hα : ∀ x, α x ∈ Ls) (rank : A → Nat) :
    ¬ ∀ x, FinConfig x → FlipsTwice x → rank (α (evol x 2)) < rank (α x) := by
  intro h
  let M := Ls.length + 1
  let y : Nat → Int → Bool := fun j => evol (Rule30ZeroBoundaryBarriers.c7cut M) (2 * j)
  have hres : ∀ j b p, evol (y j) b p = evol (Rule30ZeroBoundaryBarriers.c7cut M) (2 * j + b) p :=
    fun j b p => Rule30ZeroBoundaryBarriers.evol_restart _ (2 * j) b p
  have hfin : ∀ j, FinConfig (y j) := by
    intro j
    have hl := (Rule30ZeroBoundaryBarriers.left_edge (Rule30ZeroBoundaryBarriers.c7cut_lo M)
      (fun p hp => Rule30ZeroBoundaryBarriers.c7cut_below M p hp) (2 * j)).2
    have hr := (Rule30ZeroBoundaryBarriers.right_edge (Rule30ZeroBoundaryBarriers.c7cut_hi M)
      (fun p hp => Rule30ZeroBoundaryBarriers.c7cut_above M p hp) (2 * j)).2
    refine ⟨7 * M + 6 + 2 * j, fun p hp => ?_⟩
    rcases (show p < -(7 * (M : Int) + 1) - ((2 * j : Nat) : Int) ∨
        7 * (M : Int) + 6 + ((2 * j : Nat) : Int) < p by omega) with h' | h'
    · exact hl p h'
    · exact hr p h'
  have hc : ∀ t, t ≤ 7 * M + 1 →
      evol (Rule30ZeroBoundaryBarriers.c7cut M) t 0 = evol Rule30ZeroBoundaryBarriers.c7 t 0 :=
    fun t ht => Rule30ZeroBoundaryBarriers.c7cut_agree M t 0 (by omega) (by omega)
  have hdec : ∀ j, j ≤ Ls.length → rank (α (y (j + 1))) < rank (α (y j)) := by
    intro j hj
    have hstep : (fun p => evol (y j) 2 p) = y (j + 1) := by
      funext p; rw [hres]; show _ = evol _ (2 * (j + 1)) p; rw [show 2 * j + 2 = 2 * (j + 1) by omega]
    have hflip : FlipsTwice (y j) := by
      refine ⟨?_, ?_⟩
      · rw [hres, hres, hc _ (by omega), hc _ (by omega)]
        exact Rule30ZeroBoundaryBarriers.c7_center _
      · rw [hres, hres, hc _ (by omega), hc _ (by omega), show 2 * j + 2 = (2 * j + 1) + 1 by omega]
        exact Rule30ZeroBoundaryBarriers.c7_center _
    have := h (y j) (hfin j) hflip
    rwa [show (evol (y j) 2) = y (j + 1) from hstep] at this
  obtain ⟨m, m', hlt, hle, heq⟩ :=
    Rule30ZeroBoundaryBarriers.pigeonhole_gen Ls (fun j => α (y j)) fun j => hα _
  have chain : ∀ k, m + k + 1 ≤ m' → rank (α (y (m + k + 1))) < rank (α (y m)) := by
    intro k
    induction k with
    | zero => intro hk; exact hdec m (by omega)
    | succ k ih =>
      intro hk
      exact Nat.lt_trans (hdec (m + k + 1) (by omega)) (ih (by omega))
  have := chain (m' - m - 1) (by omega)
  rw [show m + (m' - m - 1) + 1 = m' by omega] at this
  exact Nat.lt_irrefl _ (heq ▸ this)

/-! ### Iterated `2k`-step backward propagation for `R2` and `Psi` -/

/-- The right half `2 * k` steps later under `R2`. -/
def R2n : Nat → (Nat → Bool) → (Nat → Bool)
  | 0, R => R
  | k + 1, R => R2 (R2n k R)

/-- **Iterated `2k`-Step Shift of `u R` and Backward Propagation of `¬ FinSupp (Psi R)` (`u_R2n_and_not_finSupp_Psi_of_R2n`).** -/
theorem u_R2n_and_not_finSupp_Psi_of_R2n (k : Nat) (R : Nat → Bool) :
    (∀ s : Nat, u (R2n k R) s = u R (s + k)) ∧
    (¬ FinSupp (Psi (R2n k R)) → ¬ FinSupp (Psi R)) := by
  induction k generalizing R with
  | zero => exact ⟨fun _ => rfl, fun h => h⟩
  | succ k ih =>
    refine ⟨fun s => ?_, fun h => ?_⟩
    · unfold R2n
      rw [u_R2, (ih R).1 (s + 1), show s + 1 + k = s + (k + 1) by omega]
    · unfold R2n at h
      exact (ih R).2 (not_finSupp_Psi_of_R2 (R2n k R) h)

end Rule30PeriodTwoSideways
end Ruliology.CellularAutomata
