module

public import Ruliology.CellularAutomata.Rule30LeftAntiPeriod
public import Ruliology.CellularAutomata.Rule30FiniteConfigs

/-!
# Every period, coupled: FinConf for one column as a family of coupled questions

A configuration splits into its left half, its center column and its right half. Each half
evolves as the half driven by the center column: the left half as `Rule30DrivenLeft.L`, the right
half as `Rule30Ether.drv` (`left_eq_L`, `right_eq_drv`). The center column is then updated from its
two driven neighbours (`coupled_of_evol`). Conversely, gluing two driven halves to a center column
`ω` that satisfies this update gives a configuration with center column `ω` (`evol_glue`).

* `Coupled ω s x`: the column `ω`, the left half `s` and the right half `x` satisfy the update
  `ω (t + 1) = rule (L ω s t (-1)) (ω t) (drv ω x t 1)` at every time.
* `CQ ω` (**open** for every nonconstant periodic `ω`): no finite left half and finite right half
  are coupled to `ω`. `CQ_altCol_iff_CQ01`: for the alternating column this is
  `Rule30PeriodTwoCoupled.CQ01`.
* `CQ_iff_no_finite_config`: `CQ ω` holds iff no finite configuration has center column `ω`.
* `finConf_center_iff`: **FinConf for one column is the family of coupled questions**. No nonzero
  finite configuration has an eventually periodic center column iff `CQ ω` holds for every
  periodic `ω` with a black cell.
* `problem1_of_CQ`: the family implies Problem 1.

The period-specific reductions drop one half of this system: `Q01` and the period-3
statements `Q001`, `C3`, `C3w` and `C3s001` keep the left half; Absorption and `AbsorptionT` keep the
right half.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30Coupled

open Rule30Jen Rule30Realization Rule30PeriodTwoSideways Rule30FiniteConfigs
open Rule30DrivenLeft (L L_col0 L_succ L_zero)
open Rule30Ether (drv drv_col0 drv_init)

/-! ### The two halves of any configuration are driven by its center column -/

/-- The left half of any evolution is the left half driven by its center column. -/
theorem left_eq_L (y : Int → Bool) :
    ∀ t (p : Int), p ≤ 0 → evol y t p = L (fun t => evol y t 0) y t p
  | 0, p, hp => by
    show y p = (if p < 0 then y p else evol y 0 0)
    by_cases h : p < 0
    · rw [ite_eq_left h]
    · rw [ite_eq_right h, show p = 0 by omega]; rfl
  | t + 1, p, hp => by
    by_cases h : p < 0
    · rw [L_succ h, ← left_eq_L y t (p - 1) (by omega), ← left_eq_L y t p (by omega),
        ← left_eq_L y t (p + 1) (by omega)]
      rfl
    · rw [show p = 0 by omega, L_col0]

/-- The right half of any evolution is the right half driven by its center column. -/
theorem right_eq_drv (y : Int → Bool) :
    ∀ t (p : Nat), evol y t (p : Int) = drv (fun t => evol y t 0) (fun p => y (p : Int)) t p
  | 0, 0 => by rw [drv_col0]; rfl
  | 0, p + 1 => by rw [drv_init _ _ _ (by omega)]; rfl
  | t + 1, 0 => by rw [drv_col0]; rfl
  | t + 1, p + 1 => by
    show rule (evol y t (((p + 1 : Nat) : Int) - 1)) (evol y t ((p + 1 : Nat) : Int))
        (evol y t (((p + 1 : Nat) : Int) + 1)) =
      rule (drv _ _ t p) (drv _ _ t (p + 1)) (drv _ _ t (p + 2))
    rw [← right_eq_drv y t p, ← right_eq_drv y t (p + 1), ← right_eq_drv y t (p + 2),
      show ((p + 1 : Nat) : Int) - 1 = (p : Int) by omega,
      show ((p + 1 : Nat) : Int) + 1 = ((p + 2 : Nat) : Int) by omega]

/-! ### The coupled update -/

/-- The column `ω` is coupled to the left half `s` and the right half `x`. -/
def Coupled (ω : Nat → Bool) (s : Int → Bool) (x : Nat → Bool) : Prop :=
  ∀ t, ω (t + 1) = rule (L ω s t (-1)) (ω t) (drv ω x t 1)

/-- The center column of any configuration is coupled to the two halves of the configuration. -/
theorem coupled_of_evol (y : Int → Bool) :
    Coupled (fun t => evol y t 0) y (fun p => y (p : Int)) := by
  intro t
  show rule (evol y t (0 - 1)) (evol y t 0) (evol y t (0 + 1)) = _
  rw [left_eq_L y t (0 - 1) (by omega), show ((0 : Int) + 1) = ((1 : Nat) : Int) from rfl,
    right_eq_drv y t 1]
  rfl

/-- Glue a left half `s` (positions `< 0`), a center cell `b₀` and a right half `x`
(positions `≥ 1`). -/
def glue (s : Int → Bool) (b₀ : Bool) (x : Nat → Bool) (p : Int) : Bool :=
  if p < 0 then s p else if p = 0 then b₀ else x p.toNat

/-- **Gluing.** If `ω` is coupled to `s` and `x`, the glued configuration evolves as the two
driven halves around the center column `ω`. -/
theorem evol_glue {ω : Nat → Bool} {s : Int → Bool} {x : Nat → Bool} (h : Coupled ω s x) :
    ∀ t (p : Int), evol (glue s (ω 0) x) t p = if p < 0 then L ω s t p else drv ω x t p.toNat
  | 0, p => by
    show glue s (ω 0) x p = _
    unfold glue
    by_cases hp : p < 0
    · rw [ite_eq_left hp, ite_eq_left hp, L_zero hp]
    · rw [ite_eq_right hp, ite_eq_right hp]
      by_cases h0 : p = 0
      · rw [ite_eq_left h0, show p.toNat = 0 by omega, drv_col0]
      · rw [ite_eq_right h0, drv_init _ _ _ (by omega)]
  | t + 1, p => by
    show rule (evol (glue s (ω 0) x) t (p - 1)) (evol (glue s (ω 0) x) t p)
        (evol (glue s (ω 0) x) t (p + 1)) = _
    rw [evol_glue h t (p - 1), evol_glue h t p, evol_glue h t (p + 1)]
    rcases (show p ≤ -2 ∨ p = -1 ∨ p = 0 ∨ 1 ≤ p by omega) with hp | hp | hp | hp
    · rw [ite_eq_left (show p - 1 < 0 by omega), ite_eq_left (show p < 0 by omega),
        ite_eq_left (show p + 1 < 0 by omega), ite_eq_left (show p < 0 by omega), L_succ (by omega)]
    · subst hp
      rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
        L_succ (by omega), show ((-1 : Int) + 1).toNat = 0 by rfl, drv_col0,
        show (-1 : Int) + 1 = 0 by rfl, L_col0]
    · subst hp
      rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        show ((0 : Int)).toNat = 0 by rfl, show ((0 : Int) + 1).toNat = 1 by rfl, drv_col0,
        drv_col0, show (0 : Int) - 1 = -1 by rfl, ← h t]
    · rw [ite_eq_right (show ¬ p - 1 < 0 by omega), ite_eq_right (show ¬ p < 0 by omega),
        ite_eq_right (show ¬ p + 1 < 0 by omega), ite_eq_right (show ¬ p < 0 by omega)]
      obtain ⟨k, hk⟩ : ∃ k : Nat, p.toNat = k + 1 := ⟨p.toNat - 1, by omega⟩
      rw [show (p - 1).toNat = k by omega, hk, show (p + 1).toNat = k + 2 by omega]
      rfl

theorem center_glue {ω : Nat → Bool} {s : Int → Bool} {x : Nat → Bool} (h : Coupled ω s x)
    (t : Nat) : evol (glue s (ω 0) x) t 0 = ω t := by
  rw [evol_glue h t 0, ite_eq_right (by omega), show (0 : Int).toNat = 0 from rfl, drv_col0]

/-! ### The coupled questions -/

/-- **The coupled question for the column `ω`** (open for every nonconstant periodic `ω`): no
finite left half and finite right half are coupled to `ω`. -/
def CQ (ω : Nat → Bool) : Prop :=
  ¬ ∃ (s : Int → Bool) (x : Nat → Bool), (∃ W : Nat, ∀ p : Int, p < -(W : Int) → s p = false) ∧
    (∃ W : Nat, ∀ p, W < p → x p = false) ∧ Coupled ω s x

/-- **`CQ ω` holds iff no finite configuration has center column `ω`.** -/
theorem CQ_iff_no_finite_config (ω : Nat → Bool) :
    CQ ω ↔ ¬ ∃ y : Int → Bool, FinConfig y ∧ ∀ t, evol y t 0 = ω t := by
  constructor
  · rintro hC ⟨y, ⟨W, hW⟩, hy⟩
    have hω : (fun t => evol y t 0) = ω := funext hy
    refine hC ⟨y, fun p => y (p : Int), ⟨W, fun p hp => hW p (by omega)⟩,
      ⟨W, fun p hp => hW p (by omega)⟩, ?_⟩
    rw [← hω]
    exact coupled_of_evol y
  · rintro h ⟨s, x, ⟨W₁, hW₁⟩, ⟨W₂, hW₂⟩, hc⟩
    refine h ⟨glue s (ω 0) x, ⟨W₁ + W₂, fun p hp => ?_⟩, center_glue hc⟩
    unfold glue
    by_cases hn : p < 0
    · rw [ite_eq_left hn]; exact hW₁ p (by omega)
    · rw [ite_eq_right hn, ite_eq_right (by omega)]; exact hW₂ _ (by omega)

/-- For the alternating column the coupled question is `CQ01`. -/
theorem CQ_altCol_iff_CQ01 : CQ Rule30PeriodTwoCoupled.altCol ↔ Rule30PeriodTwoCoupled.CQ01 :=
  (CQ_iff_no_finite_config _).trans CQ01_iff_no_finite_alternating.symm

/-- The zero configuration stays zero. -/
theorem evol_zero {y : Int → Bool} (hz : ∀ p, y p = false) : ∀ t p, evol y t p = false
  | 0, p => hz p
  | t + 1, p => by
    show rule (evol y t (p - 1)) (evol y t p) (evol y t (p + 1)) = false
    rw [evol_zero hz t (p - 1), evol_zero hz t p, evol_zero hz t (p + 1)]
    rfl

/-- **FinConf for one column is the family of coupled questions**: no nonzero finite configuration
has an eventually periodic center column iff `CQ ω` holds for every periodic `ω` with a black
cell. -/
theorem finConf_center_iff :
    (∀ y : Int → Bool, FinConfig y → (∃ p, y p = true) →
      ¬ EventuallyPeriodic (fun t => evol y t 0)) ↔
    ∀ ω : Nat → Bool, (∃ P, 0 < P ∧ ∀ t, ω (t + P) = ω t) → (∃ t, ω t = true) → CQ ω := by
  constructor
  · rintro h ω ⟨P, hP, hper⟩ ⟨t₀, ht₀⟩
    rw [CQ_iff_no_finite_config]
    rintro ⟨y, hfin, hy⟩
    have hne : ∃ p, y p = true := by
      refine Classical.byContradiction fun hz => ?_
      have hzero : ∀ p, y p = false := fun p => by
        cases hyp : y p
        · rfl
        · exact absurd ⟨p, hyp⟩ hz
      rw [← hy t₀, evol_zero hzero] at ht₀
      exact absurd ht₀ (by decide)
    exact h y hfin hne ⟨0, P, hP, fun t _ => by
      show evol y (t + P) 0 = evol y t 0
      rw [hy, hy, hper]⟩
  · rintro h y hfin hne ⟨T, P, hP, hper⟩
    have hblack : ∃ t, evol y (T + t) 0 = true := by
      refine Classical.byContradiction fun hw => ?_
      refine no_column_eventually_constant_finite hfin hne 0 ⟨T, false, fun t ht => ?_⟩
      cases hc : evol y t 0
      · rfl
      · exact absurd ⟨t - T, by rw [show T + (t - T) = t by omega]; exact hc⟩ hw
    have hC := h (fun t => evol y (T + t) 0)
      ⟨P, hP, fun t => by
        show evol y (T + (t + P)) 0 = evol y (T + t) 0
        rw [show T + (t + P) = (T + t) + P by omega]
        exact hper _ (by omega)⟩
      hblack
    rw [CQ_iff_no_finite_config] at hC
    exact hC ⟨fun p => evol y T p, evol_finConfig hfin T,
      fun t => Rule30ZeroBoundaryBarriers.evol_restart y T t 0⟩

/-- **The coupled questions imply Problem 1**: the single black cell is a nonzero finite
configuration. -/
theorem problem1_of_CQ
    (h : ∀ ω : Nat → Bool, (∃ P, 0 < P ∧ ∀ t, ω (t + P) = ω t) → (∃ t, ω t = true) → CQ ω) :
    Rule30Prize.Problem1 := by
  have hF := finConf_center_iff.2 h seed ⟨0, fun p hp => by
    show decide (p = 0) = false
    simp; omega⟩ ⟨0, rfl⟩
  intro hep
  apply hF
  have : (fun t => evol seed t 0) = Rule30Prize.center := funext fun t => evol_seed t 0
  rw [this]
  exact hep

/-! ### Shift Invariance of `CQ`, Unconditional Constant-Column Exclusion, and Nonconstant Reduction of `Problem1` -/

/-- **Backward Time-Shift Transfer for `CQ` (`CQ_of_CQ_shift`):** if `CQ (fun t => ω (t + k))`
holds for some shift `k : Nat`, then `CQ ω` holds. -/
theorem CQ_of_CQ_shift {ω : Nat → Bool} (k : Nat)
    (hk : CQ (fun t => ω (t + k))) : CQ ω := by
  rw [CQ_iff_no_finite_config] at hk ⊢
  rintro ⟨y, hfin, hy⟩
  refine hk ⟨fun p => evol y k p, evol_finConfig hfin k, fun t => ?_⟩
  rw [Rule30ZeroBoundaryBarriers.evol_restart y k t 0, hy (k + t), Nat.add_comm k t]

/-- **One-Step Phase-Shift Invariance of `CQ` for Periodic Columns (`CQ_periodic_succ_iff`):**
if `ω` is `P`-periodic (`0 < P`), then `CQ (fun t => ω (t + 1)) ↔ CQ ω`. -/
theorem CQ_periodic_succ_iff {ω : Nat → Bool} {P : Nat} (hP : 0 < P)
    (hper : ∀ t, ω (t + P) = ω t) :
    CQ (fun t => ω (t + 1)) ↔ CQ ω := by
  constructor
  · exact CQ_of_CQ_shift 1
  · intro hC
    apply CQ_of_CQ_shift (P - 1) (ω := fun t => ω (t + 1))
    have hback : (fun t => ω (t + (P - 1) + 1)) = ω := by
      funext t
      rw [show t + (P - 1) + 1 = t + P by omega]
      exact hper t
    rwa [hback]

/-- **Exact Phase-Shift Invariance of `CQ` for Periodic Columns (`CQ_periodic_shift_iff`):**
if `ω` is `P`-periodic (`0 < P`), then `CQ (fun t => ω (t + k)) ↔ CQ ω` for every phase shift `k : Nat`. -/
theorem CQ_periodic_shift_iff {P : Nat} (hP : 0 < P) :
    ∀ (k : Nat) {ω : Nat → Bool}, (∀ t, ω (t + P) = ω t) → (CQ (fun t => ω (t + k)) ↔ CQ ω)
  | 0, ω, _ => by simp
  | k + 1, ω, hper => by
    have hper1 : ∀ t, (fun s => ω (s + 1)) (t + P) = (fun s => ω (s + 1)) t := fun t => by
      show ω (t + P + 1) = ω (t + 1)
      rw [show t + P + 1 = (t + 1) + P by omega, hper (t + 1)]
    have ih := CQ_periodic_shift_iff hP k (ω := fun s => ω (s + 1)) hper1
    have heq : (fun t => ω (t + k + 1)) = (fun t => ω (t + (k + 1))) := by
      funext t; rw [Nat.add_assoc]
    change CQ (fun t => ω (t + k + 1)) ↔ CQ (fun s => ω (s + 1)) at ih
    rw [heq] at ih
    exact ih.trans (CQ_periodic_succ_iff hP hper)

/-- **Unconditional `CQ` for Eventually Constant Columns with a Black Cell
(`CQ_of_eventually_constant`):** if `ω` is eventually constant (`∀ t, T ≤ t → ω t = b`) and has at
least one black cell (`∃ t₀, ω t₀ = true`), then `CQ ω` holds unconditionally. -/
theorem CQ_of_eventually_constant {ω : Nat → Bool} {T : Nat} {b : Bool}
    (hconst : ∀ t, T ≤ t → ω t = b) (hblack : ∃ t₀, ω t₀ = true) : CQ ω := by
  rw [CQ_iff_no_finite_config]
  rintro ⟨y, hfin, hy⟩
  obtain ⟨t₀, ht₀⟩ := hblack
  have hne : ∃ p, y p = true := by
    refine Classical.byContradiction fun hz => ?_
    have hzero : ∀ p, y p = false := fun p => by
      cases hyp : y p
      · rfl
      · exact absurd ⟨p, hyp⟩ hz
    rw [← hy t₀, evol_zero hzero] at ht₀
    exact absurd ht₀ (by decide)
  exact no_column_eventually_constant_finite hfin hne 0 ⟨T, b, fun t ht => by
    rw [hy t]
    exact hconst t ht⟩

/-- **Unconditional `CQ` for the Constant All-Black Column (`CQ_const_true`):**
`CQ (fun _ => true)` holds unconditionally. -/
theorem CQ_const_true : CQ (fun _ => true) :=
  CQ_of_eventually_constant (T := 0) (b := true) (fun _ _ => rfl) ⟨0, rfl⟩

/-- **Reduction of `Problem1` to Nonconstant Periodic Coupled Questions
(`problem1_of_nonconstant_CQ`):** if `CQ ω` holds for every periodic `ω` that contains both a black
cell and a white cell, then `Rule30Prize.Problem1` holds. -/
theorem problem1_of_nonconstant_CQ
    (h : ∀ ω : Nat → Bool, (∃ P, 0 < P ∧ ∀ t, ω (t + P) = ω t) →
      (∃ t, ω t = true) → (∃ t, ω t = false) → CQ ω) :
    Rule30Prize.Problem1 := by
  refine problem1_of_CQ (fun ω hper hblack => ?_)
  by_cases hwhite : ∃ t, ω t = false
  · exact h ω hper hblack hwhite
  · refine CQ_of_eventually_constant (T := 0) (b := true) (fun t _ => ?_) hblack
    cases hω : ω t
    · exact False.elim (hwhite ⟨t, hω⟩)
    · rfl

/-- Inductive phase-reduction helper (`CQ_of_canonical_CQ`): if `CQ` holds for every periodic
sequence with `ω 0 = true` and a white cell, then it holds for every periodic sequence with
`ω t₀ = true` and a white cell for any `t₀ : Nat`. -/
theorem CQ_of_canonical_CQ
    (h : ∀ ω : Nat → Bool, (∃ P, 0 < P ∧ ∀ t, ω (t + P) = ω t) →
      ω 0 = true → (∃ t, ω t = false) → CQ ω)
    {P : Nat} (hP : 0 < P) :
    ∀ (t₀ : Nat) {ω : Nat → Bool}, (∀ t, ω (t + P) = ω t) →
      ω t₀ = true → (∃ t, ω t = false) → CQ ω
  | 0, ω, hper, ht0, hw => h ω ⟨P, hP, hper⟩ ht0 hw
  | t₀ + 1, ω, hper, ht0, ⟨t₁, ht₁⟩ => by
    have hper1 : ∀ t, (fun s => ω (s + 1)) (t + P) = (fun s => ω (s + 1)) t := fun t => by
      show ω (t + P + 1) = ω (t + 1)
      rw [show t + P + 1 = (t + 1) + P by omega, hper (t + 1)]
    have hw1 : ∃ t, (fun s => ω (s + 1)) t = false := by
      refine ⟨t₁ + (P - 1), ?_⟩
      show ω (t₁ + (P - 1) + 1) = false
      rw [show t₁ + (P - 1) + 1 = t₁ + P by omega, hper t₁, ht₁]
    have ht01 : (fun s => ω (s + 1)) t₀ = true := ht0
    exact CQ_of_CQ_shift 1 (CQ_of_canonical_CQ h hP t₀ (ω := fun s => ω (s + 1)) hper1 ht01 hw1)

/-- **Canonical Phase-Anchored Reduction of `Problem1` (`problem1_of_canonical_CQ`):**
since `CQ` is invariant under phase shifts of periodic columns (`CQ_periodic_shift_iff`), to prove
`Rule30Prize.Problem1` it suffices to establish `CQ ω` for periodic sequences `ω` anchored with a
black cell at `t = 0` (`ω 0 = true`) that also take the value `false`. -/
theorem problem1_of_canonical_CQ
    (h : ∀ ω : Nat → Bool, (∃ P, 0 < P ∧ ∀ t, ω (t + P) = ω t) →
      ω 0 = true → (∃ t, ω t = false) → CQ ω) :
    Rule30Prize.Problem1 :=
  problem1_of_nonconstant_CQ (fun _ ⟨_, hP, hper⟩ ⟨t₀, ht₀⟩ hw =>
    CQ_of_canonical_CQ h hP t₀ hper ht₀ hw)

/-! ### Reduction of `Problem1` under `Problem2` to Balanced Even-Period Coupled Questions -/

/-- Window-count invariance under time shift for purely `L`-periodic sequences
(`winCount_shift_of_periodic`): if `∀ t, ω (t + L) = ω t`, then
`Rule30LeftAntiPeriod.winCount (fun t => ω (t + k)) 0 L = Rule30LeftAntiPeriod.winCount ω 0 L`. -/
theorem winCount_shift_of_periodic {ω : Nat → Bool} {L : Nat}
    (hper : ∀ t, ω (t + L) = ω t) (k : Nat) :
    Rule30LeftAntiPeriod.winCount (fun t => ω (t + k)) 0 L =
      Rule30LeftAntiPeriod.winCount ω 0 L := by
  have heq : ∀ d, Rule30LeftAntiPeriod.winCount (fun t => ω (t + k)) 0 d =
      Rule30LeftAntiPeriod.winCount ω k d := by
    intro d
    induction d with
    | zero => rfl
    | succ d ih =>
      simp only [Rule30LeftAntiPeriod.winCount, ih, Nat.zero_add]
      rw [Nat.add_comm d k]
  rw [heq L]
  exact Rule30LeftAntiPeriod.winCount_const_of_periodic (T := 0) (fun t _ => hper t) (by omega)

/-- **Balanced Even-Period Coupled Reduction of `Problem1` under `Problem2`
(`problem1_of_problem2_and_balanced_even_CQ`):** under `Rule30Prize.Problem2` (**open**), to prove
`Rule30Prize.Problem1` it suffices to establish `CQ ω` for every `(2 * m)`-periodic sequence `ω`
(`0 < m`) that is exactly half-balanced on its period window
(`Rule30LeftAntiPeriod.winCount ω 0 (2 * m) = m`). -/
theorem problem1_of_problem2_and_balanced_even_CQ
    (hP2 : Rule30Prize.Problem2)
    (hCQ : ∀ (m : Nat) (ω : Nat → Bool), 0 < m →
      (∀ t, ω (t + 2 * m) = ω t) →
      Rule30LeftAntiPeriod.winCount ω 0 (2 * m) = m → CQ ω) :
    Rule30Prize.Problem1 := by
  rintro ⟨T, P, hP, hper⟩
  let ω : Nat → Bool := fun t => Rule30Prize.center (T + t)
  have hper_ω : ∀ t, ω (t + P) = ω t := fun t => by
    show Rule30Prize.center (T + (t + P)) = Rule30Prize.center (T + t)
    rw [show T + (t + P) = (T + t) + P by omega]
    exact hper (T + t) (by omega)
  have hhd_ω : Rule30LeftAntiPeriod.HalfDensity ω :=
    (Rule30LeftAntiPeriod.halfDensity_shift_iff Rule30Prize.center T).mpr hP2
  have hbal : 2 * Rule30LeftAntiPeriod.winCount ω 0 P = P :=
    (Rule30LeftAntiPeriod.periodic_halfDensity_iff_two_mul_winCount_eq
      (f := ω) (T := 0) (L := P) hP (fun t _ => hper_ω t)).mp hhd_ω
  let m := Rule30LeftAntiPeriod.winCount ω 0 P
  have hm_pos : 0 < m := by omega
  have hP_eq : P = 2 * m := by omega
  have hper_2m : ∀ t, ω (t + 2 * m) = ω t := by
    intro t; rw [← hP_eq]; exact hper_ω t
  have hwin_2m : Rule30LeftAntiPeriod.winCount ω 0 (2 * m) = m := by
    rw [← hP_eq]
  have hC : CQ ω := hCQ m ω hm_pos hper_2m hwin_2m
  rw [CQ_iff_no_finite_config] at hC
  have hs : FinConfig seed := ⟨0, fun p hp => by
    show decide (p = 0) = false
    simp; omega⟩
  refine hC ⟨fun p => evol seed T p, evol_finConfig hs T, fun t => ?_⟩
  rw [Rule30ZeroBoundaryBarriers.evol_restart seed T t 0]
  exact evol_seed (T + t) 0

/-- **Canonical Phase-Anchored Balanced Even-Period Reduction under `Problem2`
(`problem1_of_problem2_and_canonical_balanced_even_CQ`):** under `Rule30Prize.Problem2` (**open**),
to prove `Rule30Prize.Problem1` it suffices to establish `CQ ω` for every `(2 * m)`-periodic
sequence `ω` (`0 < m`) anchored with a black cell at `t = 0` (`ω 0 = true`) that satisfies
`Rule30LeftAntiPeriod.winCount ω 0 (2 * m) = m`. -/
theorem problem1_of_problem2_and_canonical_balanced_even_CQ
    (hP2 : Rule30Prize.Problem2)
    (hCQ : ∀ (m : Nat) (ω : Nat → Bool), 0 < m →
      (∀ t, ω (t + 2 * m) = ω t) →
      ω 0 = true →
      Rule30LeftAntiPeriod.winCount ω 0 (2 * m) = m → CQ ω) :
    Rule30Prize.Problem1 := by
  refine problem1_of_problem2_and_balanced_even_CQ hP2 (fun m ω hm hper hwin => ?_)
  have hblack : ∃ k, ω k = true := by
    refine Classical.byContradiction fun hno => ?_
    have hall : ∀ t, ω t = false := fun t => by
      cases hω : ω t
      · rfl
      · exact False.elim (hno ⟨t, hω⟩)
    have hzero : ∀ d, Rule30LeftAntiPeriod.winCount ω 0 d = 0 := by
      intro d
      induction d with
      | zero => rfl
      | succ d ih => simp [Rule30LeftAntiPeriod.winCount, ih, hall d]
    have hm0 : m = 0 := by rw [← hwin, hzero (2 * m)]
    omega
  obtain ⟨k, hk⟩ := hblack
  have hper_k : ∀ t, (fun s => ω (s + k)) (t + 2 * m) = (fun s => ω (s + k)) t := fun t => by
    show ω (t + 2 * m + k) = ω (t + k)
    rw [show t + 2 * m + k = (t + k) + 2 * m by omega, hper (t + k)]
  have hwin_k : Rule30LeftAntiPeriod.winCount (fun s => ω (s + k)) 0 (2 * m) = m := by
    rw [winCount_shift_of_periodic hper k, hwin]
  have h0_k : (fun s => ω (s + k)) 0 = true := by
    show ω (0 + k) = true
    rwa [Nat.zero_add]
  exact CQ_of_CQ_shift k (hCQ m (fun s => ω (s + k)) hm hper_k h0_k hwin_k)

/-! ### Algebraic Inversion of `Coupled`, Universal Aperiodicity of Driven Neighbors, and `m >= 2` Balanced Even-Period Reduction Under `Problem2` and `CQ01` -/

/-- **Left-Permutive Inversion of `Coupled` (`L_neg1_of_coupled`):** if `Coupled ω s x` holds,
then at every step `t`, `L ω s t (-1) = xor (ω (t + 1)) (ω t || drv ω x t 1)`. -/
theorem L_neg1_of_coupled {ω : Nat → Bool} {s : Int → Bool} {x : Nat → Bool}
    (h : Coupled ω s x) (t : Nat) :
    L ω s t (-1) = xor (ω (t + 1)) (ω t || drv ω x t 1) := by
  have ht := h t
  revert ht
  cases ω (t + 1) <;> cases L ω s t (-1) <;> cases ω t <;> cases drv ω x t 1 <;> decide

/-- **Black-Step Right-Shield Absorption in `Coupled` (`L_neg1_of_coupled_true`):** if
`Coupled ω s x` holds and `ω t = true`, then `L ω s t (-1) = !ω (t + 1)` independently of `x`. -/
theorem L_neg1_of_coupled_true {ω : Nat → Bool} {s : Int → Bool} {x : Nat → Bool}
    (h : Coupled ω s x) {t : Nat} (ht : ω t = true) :
    L ω s t (-1) = !ω (t + 1) := by
  rw [L_neg1_of_coupled h t, ht]
  cases ω (t + 1) <;> rfl

/-- **White-Step Neighbor Relation in `Coupled` (`L_neg1_of_coupled_false`):** if `Coupled ω s x`
holds and `ω t = false`, then `L ω s t (-1) = xor (ω (t + 1)) (drv ω x t 1)`. -/
theorem L_neg1_of_coupled_false {ω : Nat → Bool} {s : Int → Bool} {x : Nat → Bool}
    (h : Coupled ω s x) {t : Nat} (ht : ω t = false) :
    L ω s t (-1) = xor (ω (t + 1)) (drv ω x t 1) := by
  rw [L_neg1_of_coupled h t, ht]
  cases ω (t + 1) <;> cases drv ω x t 1 <;> rfl

/-- **Universal Aperiodicity of the Left Neighbor `L ω s · (-1)` for Periodic `ω`
(`not_eventuallyPeriodic_L_neg1_of_coupled_periodic`):** for any `P`-periodic `ω` (`0 < P`)
with a black cell and any left-bounded `s`, `fun t => L ω s t (-1)` is not eventually periodic. -/
theorem not_eventuallyPeriodic_L_neg1_of_coupled_periodic
    {ω : Nat → Bool} {s : Int → Bool} {P W : Nat}
    (hP : 0 < P) (hper : ∀ t, ω (t + P) = ω t)
    (hblack : ∃ t₀, ω t₀ = true)
    (hs : ∀ p : Int, p < -(W : Int) → s p = false) :
    ¬ EventuallyPeriodic (fun t => L ω s t (-1)) := by
  have h := Rule30DrivenLeft.not_eventuallyPeriodic_free_phase_of_bounded
    (P := 1) (φ₀ := 0) (K := 0) (by decide) (by decide) hs (Or.inr hblack)
    ⟨0, P, hP, fun t _ => hper t⟩ (fun k _ hne => False.elim (hne (Nat.mod_one k)))
  simpa using h

/-- **Multi-Period Step Invariance for Purely Periodic Sequences (`periodic_add_mul`):** if
`∀ t, f (t + P) = f t`, then `f (t + k * P) = f t` for all `k, t : Nat`. -/
theorem periodic_add_mul {f : Nat → Bool} {P : Nat} (hper : ∀ t, f (t + P) = f t) :
    ∀ (k t : Nat), f (t + k * P) = f t
  | 0, t => by simp
  | k + 1, t => by
    rw [Nat.succ_mul, ← Nat.add_assoc, hper (t + k * P), periodic_add_mul hper k t]

/-- **Universal Aperiodicity of the Right Neighbor `drv ω x · 1` in Any Coupled Pair
(`not_eventuallyPeriodic_drv_one_of_coupled_periodic`):** if `ω` is `P`-periodic (`0 < P`) with
a black cell, `s` is left-bounded (`∀ p < -W, s p = false`), and `Coupled ω s x` holds, then the
right-half neighbor `fun t => drv ω x t 1` is never eventually periodic. -/
theorem not_eventuallyPeriodic_drv_one_of_coupled_periodic
    {ω : Nat → Bool} {s : Int → Bool} {x : Nat → Bool} {P W : Nat}
    (hP : 0 < P) (hper : ∀ t, ω (t + P) = ω t)
    (hblack : ∃ t₀, ω t₀ = true)
    (hs : ∀ p : Int, p < -(W : Int) → s p = false)
    (hc : Coupled ω s x) :
    ¬ EventuallyPeriodic (fun t => drv ω x t 1) := by
  rintro ⟨T, Q, hQ, hdrv⟩
  dsimp only at hdrv
  have hdrv_mul : ∀ k t, T ≤ t → drv ω x (t + k * Q) 1 = drv ω x t 1 := by
    intro k
    induction k with
    | zero => intro t _; simp
    | succ k ih =>
      intro t ht
      rw [Nat.succ_mul, ← Nat.add_assoc, hdrv (t + k * Q) (by omega), ih t ht]
  apply not_eventuallyPeriodic_L_neg1_of_coupled_periodic hP hper hblack hs
  refine ⟨T, P * Q, Nat.mul_pos hP hQ, fun t ht => ?_⟩
  dsimp only
  rw [L_neg1_of_coupled hc (t + P * Q), L_neg1_of_coupled hc t]
  have hω0 : ω (t + P * Q) = ω t := by
    rw [Nat.mul_comm P Q]
    exact periodic_add_mul hper Q t
  have hω1 : ω (t + P * Q + 1) = ω (t + 1) := by
    rw [show t + P * Q + 1 = (t + 1) + Q * P by rw [Nat.mul_comm P Q]; omega]
    exact periodic_add_mul hper Q (t + 1)
  have hd1 : drv ω x (t + P * Q) 1 = drv ω x t 1 :=
    hdrv_mul P t ht
  rw [hω0, hω1, hd1]

/-- **Canonical Balanced 2-Periodic Characterization (`two_periodic_canonical_balanced_eq_altCol_succ`):**
any 2-periodic sequence `ω` (`∀ t, ω (t + 2) = ω t`) with `ω 0 = true` and
`Rule30LeftAntiPeriod.winCount ω 0 2 = 1` equals `Rule30PeriodTwoCoupled.altCol`. -/
theorem two_periodic_canonical_balanced_eq_altCol_succ {ω : Nat → Bool}
    (hper : ∀ t, ω (t + 2) = ω t) (h0 : ω 0 = true)
    (hwin : Rule30LeftAntiPeriod.winCount ω 0 2 = 1) :
    ∀ t, ω t = Rule30PeriodTwoCoupled.altCol t := by
  have h1 : ω 1 = false := by
    simp only [Rule30LeftAntiPeriod.winCount, Nat.zero_add, h0] at hwin
    cases hω1 : ω 1 <;> simp_all
  have halt2 : ∀ k, Rule30PeriodTwoCoupled.altCol (k + 2) = Rule30PeriodTwoCoupled.altCol k := by
    intro k; simp [Rule30PeriodTwoCoupled.altCol, Nat.add_mod_right]
  have hstep : ∀ t, ω t = Rule30PeriodTwoCoupled.altCol t ∧
      ω (t + 1) = Rule30PeriodTwoCoupled.altCol (t + 1) := by
    intro t
    induction t with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [h0]; decide
      · rw [Nat.zero_add, h1]; decide
    | succ t ih =>
      refine ⟨ih.2, ?_⟩
      rw [hper t, ih.1, halt2 t]
  exact fun t => (hstep t).1

/-- **`CQ01` Discharges All Canonical Balanced 2-Periodic Coupled Questions
(`CQ_of_CQ01_and_two_periodic_balanced`):** under `Rule30PeriodTwoCoupled.CQ01` (**open**),
`CQ ω` holds for every 2-periodic sequence `ω` with `ω 0 = true` and `winCount ω 0 2 = 1`. -/
theorem CQ_of_CQ01_and_two_periodic_balanced
    (hCQ01 : Rule30PeriodTwoCoupled.CQ01) {ω : Nat → Bool}
    (hper : ∀ t, ω (t + 2) = ω t) (h0 : ω 0 = true)
    (hwin : Rule30LeftAntiPeriod.winCount ω 0 2 = 1) : CQ ω := by
  have heq : ω = Rule30PeriodTwoCoupled.altCol :=
    funext (two_periodic_canonical_balanced_eq_altCol_succ hper h0 hwin)
  rw [heq]
  exact CQ_altCol_iff_CQ01.mpr hCQ01

/-- **Reduction of `Problem1` Under `Problem2` and `CQ01` to Half-Balanced Even Periods `2 * m >= 4`
(`problem1_of_problem2_and_CQ01_and_canonical_balanced_even_ge_two_CQ`):** under
`Rule30Prize.Problem2` (**open**) and `Rule30PeriodTwoCoupled.CQ01` (**open**), to prove
`Rule30Prize.Problem1` it suffices to establish `CQ ω` for canonical `(2 * m)`-periodic
sequences `ω` (`ω 0 = true`) with `2 ≤ m` (`2 * m ≥ 4`) and `winCount ω 0 (2 * m) = m`. -/
theorem problem1_of_problem2_and_CQ01_and_canonical_balanced_even_ge_two_CQ
    (hP2 : Rule30Prize.Problem2) (hCQ01 : Rule30PeriodTwoCoupled.CQ01)
    (hCQ : ∀ (m : Nat) (ω : Nat → Bool), 2 ≤ m →
      (∀ t, ω (t + 2 * m) = ω t) →
      ω 0 = true →
      Rule30LeftAntiPeriod.winCount ω 0 (2 * m) = m → CQ ω) :
    Rule30Prize.Problem1 := by
  refine problem1_of_problem2_and_canonical_balanced_even_CQ hP2 (fun m ω hm hper h0 hwin => ?_)
  by_cases hm2 : 2 ≤ m
  · exact hCQ m ω hm2 hper h0 hwin
  · obtain rfl : m = 1 := by omega
    exact CQ_of_CQ01_and_two_periodic_balanced hCQ01 hper h0 hwin

/-! ### Complete Classification of Balanced 4-Periodic Columns (`m = 2`) and Reduction of `Problem1` Under `Problem2`, `CQ01`, and `CQ w0011Col` to `2 * m >= 6` -/

/-- **The Canonical Balanced 4-Periodic Column (`w0011Col`):** the 4-periodic sequence
`[false, false, true, true]` repeated (`fun t => Rule30Ether.wordAt Rule30Ether.w0011 t`). -/
def w0011Col (t : Nat) : Bool := Rule30Ether.wordAt Rule30Ether.w0011 t

/-- **Period-4 Law for `w0011Col` (`w0011Col_periodic`):** `w0011Col (t + 4) = w0011Col t` for all `t`. -/
theorem w0011Col_periodic (t : Nat) : w0011Col (t + 4) = w0011Col t := by
  unfold w0011Col Rule30Ether.wordAt Rule30Ether.w0011
  simp [Nat.add_mod_right]

/-- **4-Periodic Agreement Criterion (`periodic_four_eq_of_first_four`):** if `ω` and `ω'` are
both 4-periodic and agree at `0, 1, 2, 3`, then `ω t = ω' t` for all `t : Nat`. -/
theorem periodic_four_eq_of_first_four {ω ω' : Nat → Bool}
    (hω : ∀ t, ω (t + 4) = ω t) (hω' : ∀ t, ω' (t + 4) = ω' t)
    (h0 : ω 0 = ω' 0) (h1 : ω 1 = ω' 1) (h2 : ω 2 = ω' 2) (h3 : ω 3 = ω' 3) :
    ∀ t, ω t = ω' t := by
  have hstep : ∀ t, ω t = ω' t ∧ ω (t + 1) = ω' (t + 1) ∧
      ω (t + 2) = ω' (t + 2) ∧ ω (t + 3) = ω' (t + 3) := by
    intro t
    induction t with
    | zero => exact ⟨h0, h1, h2, h3⟩
    | succ t ih =>
      refine ⟨ih.2.1, ih.2.2.1, ih.2.2.2, ?_⟩
      rw [show t + 1 + 3 = t + 4 by omega, hω t, hω' t, ih.1]
  exact fun t => (hstep t).1

/-- **Complete Classification of Canonical Balanced 4-Periodic Columns
(`four_periodic_canonical_balanced_classify`):** every 4-periodic sequence `ω`
(`∀ t, ω (t + 4) = ω t`) with `ω 0 = true` and `winCount ω 0 4 = 2` is either
`Rule30PeriodTwoCoupled.altCol`, `fun t => w0011Col (t + 2)`, or `fun t => w0011Col (t + 3)`. -/
theorem four_periodic_canonical_balanced_classify {ω : Nat → Bool}
    (hper : ∀ t, ω (t + 4) = ω t) (h0 : ω 0 = true)
    (hwin : Rule30LeftAntiPeriod.winCount ω 0 4 = 2) :
    (ω = Rule30PeriodTwoCoupled.altCol) ∨
    (ω = fun t => w0011Col (t + 2)) ∨
    (ω = fun t => w0011Col (t + 3)) := by
  have hsum : (if ω 0 = true then 1 else 0) + (if ω 1 = true then 1 else 0) +
      (if ω 2 = true then 1 else 0) + (if ω 3 = true then 1 else 0) = 2 := by
    simpa [Rule30LeftAntiPeriod.winCount, Nat.zero_add] using hwin
  rw [h0] at hsum
  have hcases : (ω 1 = false ∧ ω 2 = true ∧ ω 3 = false) ∨
      (ω 1 = true ∧ ω 2 = false ∧ ω 3 = false) ∨
      (ω 1 = false ∧ ω 2 = false ∧ ω 3 = true) := by
    revert hsum
    cases ω 1 <;> cases ω 2 <;> cases ω 3 <;> decide
  rcases hcases with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · left
    funext t
    apply periodic_four_eq_of_first_four hper
      (fun k => by simp [Rule30PeriodTwoCoupled.altCol, show (k + 4) % 2 = k % 2 by omega])
    · rw [h0]; decide
    · rw [h1]; decide
    · rw [h2]; decide
    · rw [h3]; decide
  · right; left
    funext t
    apply periodic_four_eq_of_first_four hper
      (fun k => by show w0011Col (k + 4 + 2) = w0011Col (k + 2); rw [show k + 4 + 2 = (k + 2) + 4 by omega, w0011Col_periodic])
    · rw [h0]; decide
    · rw [h1]; decide
    · rw [h2]; decide
    · rw [h3]; decide
  · right; right
    funext t
    apply periodic_four_eq_of_first_four hper
      (fun k => by show w0011Col (k + 4 + 3) = w0011Col (k + 3); rw [show k + 4 + 3 = (k + 3) + 4 by omega, w0011Col_periodic])
    · rw [h0]; decide
    · rw [h1]; decide
    · rw [h2]; decide
    · rw [h3]; decide

/-- **`CQ01` and `CQ w0011Col` Discharge All Canonical Balanced 4-Periodic Coupled Questions
(`CQ_of_CQ01_and_CQ_w0011_and_four_periodic_balanced`):** under `Rule30PeriodTwoCoupled.CQ01`
(**open**) and `CQ w0011Col` (**open**), `CQ ω` holds for every 4-periodic sequence `ω` with
`ω 0 = true` and `winCount ω 0 4 = 2`. -/
theorem CQ_of_CQ01_and_CQ_w0011_and_four_periodic_balanced
    (hCQ01 : Rule30PeriodTwoCoupled.CQ01) (hCQ0011 : CQ w0011Col)
    {ω : Nat → Bool} (hper : ∀ t, ω (t + 4) = ω t) (h0 : ω 0 = true)
    (hwin : Rule30LeftAntiPeriod.winCount ω 0 4 = 2) : CQ ω := by
  rcases four_periodic_canonical_balanced_classify hper h0 hwin with rfl | rfl | rfl
  · exact CQ_altCol_iff_CQ01.mpr hCQ01
  · exact (CQ_periodic_shift_iff (by decide : 0 < 4) 2 w0011Col_periodic).mpr hCQ0011
  · exact (CQ_periodic_shift_iff (by decide : 0 < 4) 3 w0011Col_periodic).mpr hCQ0011

/-- **Reduction of `Problem1` Under `Problem2`, `CQ01`, and `CQ w0011Col` to Half-Balanced Even
Periods `2 * m >= 6` (`problem1_of_problem2_and_CQ01_and_CQ_w0011_and_canonical_balanced_even_ge_three_CQ`):**
under `Rule30Prize.Problem2` (**open**), `Rule30PeriodTwoCoupled.CQ01` (**open**), and
`CQ w0011Col` (**open**), to prove `Rule30Prize.Problem1` it suffices to establish `CQ ω` for
canonical `(2 * m)`-periodic sequences `ω` (`ω 0 = true`) with `3 ≤ m` (`2 * m ≥ 6`) and
`winCount ω 0 (2 * m) = m`. -/
theorem problem1_of_problem2_and_CQ01_and_CQ_w0011_and_canonical_balanced_even_ge_three_CQ
    (hP2 : Rule30Prize.Problem2) (hCQ01 : Rule30PeriodTwoCoupled.CQ01)
    (hCQ0011 : CQ w0011Col)
    (hCQ : ∀ (m : Nat) (ω : Nat → Bool), 3 ≤ m →
      (∀ t, ω (t + 2 * m) = ω t) →
      ω 0 = true →
      Rule30LeftAntiPeriod.winCount ω 0 (2 * m) = m → CQ ω) :
    Rule30Prize.Problem1 := by
  refine problem1_of_problem2_and_CQ01_and_canonical_balanced_even_ge_two_CQ hP2 hCQ01
    (fun m ω hm2 hper h0 hwin => ?_)
  by_cases hm3 : 3 ≤ m
  · exact hCQ m ω hm3 hper h0 hwin
  · obtain rfl : m = 2 := by omega
    exact CQ_of_CQ01_and_CQ_w0011_and_four_periodic_balanced hCQ01 hCQ0011 hper h0 hwin

/-! ### Eliminating `CQ01` and Odd Multiples of 2 via Stride-2 `HalfDensity`: Reduction of `Problem1` to Multiples of 4 (`4 * k >= 8`) -/

/-- **Modulo-4 Period Divisibility Under Stride-2 `HalfDensity`
(`four_dvd_period_of_subseq_two_halfDensity`):** if
`Rule30LeftAntiPeriod.HalfDensity (Rule30LeftAntiPeriod.subseq Rule30Prize.center 2 r)` holds and
`Rule30Prize.center` is eventually `P`-periodic (`0 < P`) from `T` on, then `P = 4 * k` for some
`0 < k`. -/
theorem four_dvd_period_of_subseq_two_halfDensity {r T P : Nat}
    (hd2 : Rule30LeftAntiPeriod.HalfDensity (Rule30LeftAntiPeriod.subseq Rule30Prize.center 2 r))
    (hP : 0 < P) (hper : ∀ t, T ≤ t → Rule30Prize.center (t + P) = Rule30Prize.center t) :
    ∃ k : Nat, 0 < k ∧ P = 4 * k := by
  obtain ⟨a, m, hfac⟩ := Rule30LeftAntiPeriod.exists_eq_two_pow_mul_odd P hP
  have hev_fac : ∃ T', ∀ t, T' ≤ t → Rule30Prize.center (t + 2 ^ a * (2 * m + 1)) = Rule30Prize.center t := by
    rw [← hfac]; exact ⟨T, hper⟩
  rcases Nat.eq_zero_or_pos a with rfl | ha_pos
  · rw [Nat.pow_zero, Nat.one_mul] at hev_fac
    exact False.elim (Rule30LeftAntiPeriod.not_evPer_odd_of_subseq_halfDensity hd2 m hev_fac)
  · by_cases ha1 : a = 1
    · subst ha1
      exact False.elim (Rule30LeftAntiPeriod.not_evPer_two_pow_mul_odd_of_subseq_halfDensity (a := 1) hd2 m hev_fac)
    · have ha2 : 2 ≤ a := by omega
      refine ⟨2 ^ (a - 2) * (2 * m + 1), Nat.mul_pos (Nat.two_pow_pos _) (by omega), ?_⟩
      have hpow : 2 ^ a = 4 * 2 ^ (a - 2) := by
        change 2 ^ a = 2 ^ 2 * 2 ^ (a - 2)
        rw [← Nat.pow_add, show 2 + (a - 2) = a by omega]
      rw [hfac, hpow, Nat.mul_assoc]

/-- **Stride-2 `HalfDensity` Excludes Any `altCol` Tail of `center`
(`not_center_shift_eq_altCol_of_subseq_two_halfDensity`):** if
`Rule30LeftAntiPeriod.HalfDensity (Rule30LeftAntiPeriod.subseq Rule30Prize.center 2 r)` holds,
then for every shift `T : Nat`, `(fun t => Rule30Prize.center (T + t)) ≠ Rule30PeriodTwoCoupled.altCol`. -/
theorem not_center_shift_eq_altCol_of_subseq_two_halfDensity {r : Nat}
    (hd2 : Rule30LeftAntiPeriod.HalfDensity (Rule30LeftAntiPeriod.subseq Rule30Prize.center 2 r))
    (T : Nat) :
    (fun t => Rule30Prize.center (T + t)) ≠ Rule30PeriodTwoCoupled.altCol := by
  intro heq
  have hfun : ∀ t, Rule30Prize.center (T + t) = Rule30PeriodTwoCoupled.altCol t :=
    fun t => congrFun heq t
  have halt2 : ∀ k, Rule30PeriodTwoCoupled.altCol (k + 2) = Rule30PeriodTwoCoupled.altCol k := by
    intro k; simp [Rule30PeriodTwoCoupled.altCol, Nat.add_mod_right]
  have hev2 : ∃ T', ∀ t, T' ≤ t → Rule30Prize.center (t + 2 * (2 * 0 + 1)) = Rule30Prize.center t := by
    refine ⟨T, fun t ht => ?_⟩
    change Rule30Prize.center (t + 2) = Rule30Prize.center t
    have h1 := hfun (t - T + 2)
    have h2 := hfun (t - T)
    rw [show T + (t - T + 2) = t + 2 by omega, halt2 (t - T)] at h1
    rw [show T + (t - T) = t by omega] at h2
    exact h1.trans h2.symm
  exact Rule30LeftAntiPeriod.not_evPer_mul_odd_of_subseq_halfDensity (by decide : 0 < 2) hd2 0 hev2

/-- **Exclusion of All Canonical Balanced 4-Periodic Tails of `center` Under Stride-2 `HalfDensity`
and `CQ w0011Col` (`not_center_shift_four_periodic_balanced_of_subseq_two_halfDensity_and_CQ_w0011`):**
under `Rule30LeftAntiPeriod.HalfDensity (Rule30LeftAntiPeriod.subseq Rule30Prize.center 2 r)`
(**open**) and `CQ w0011Col` (**open**), no shifted tail `ω t = Rule30Prize.center (T + t)` can
satisfy `∀ t, ω (t + 4) = ω t`, `ω 0 = true`, and `winCount ω 0 4 = 2`. -/
theorem not_center_shift_four_periodic_balanced_of_subseq_two_halfDensity_and_CQ_w0011
    {r T : Nat}
    (hd2 : Rule30LeftAntiPeriod.HalfDensity (Rule30LeftAntiPeriod.subseq Rule30Prize.center 2 r))
    (hCQ0011 : CQ w0011Col)
    (hper : ∀ t, Rule30Prize.center (T + (t + 4)) = Rule30Prize.center (T + t))
    (h0 : Rule30Prize.center (T + 0) = true)
    (hwin : Rule30LeftAntiPeriod.winCount (fun t => Rule30Prize.center (T + t)) 0 4 = 2) :
    False := by
  let ω : Nat → Bool := fun t => Rule30Prize.center (T + t)
  rcases four_periodic_canonical_balanced_classify (ω := ω) hper h0 hwin with halt | hw2 | hw3
  · exact not_center_shift_eq_altCol_of_subseq_two_halfDensity hd2 T halt
  · have hC : CQ ω := by
      rw [hw2]
      exact (CQ_periodic_shift_iff (by decide : 0 < 4) 2 w0011Col_periodic).mpr hCQ0011
    rw [CQ_iff_no_finite_config] at hC
    have hs : FinConfig seed := ⟨0, fun p hp => by show decide (p = 0) = false; simp; omega⟩
    refine hC ⟨fun p => evol seed T p, evol_finConfig hs T, fun t => ?_⟩
    rw [Rule30ZeroBoundaryBarriers.evol_restart seed T t 0]
    exact evol_seed (T + t) 0
  · have hC : CQ ω := by
      rw [hw3]
      exact (CQ_periodic_shift_iff (by decide : 0 < 4) 3 w0011Col_periodic).mpr hCQ0011
    rw [CQ_iff_no_finite_config] at hC
    have hs : FinConfig seed := ⟨0, fun p hp => by show decide (p = 0) = false; simp; omega⟩
    refine hC ⟨fun p => evol seed T p, evol_finConfig hs T, fun t => ?_⟩
    rw [Rule30ZeroBoundaryBarriers.evol_restart seed T t 0]
    exact evol_seed (T + t) 0

/-- **Reduction of `Problem1` Under Stride-2 `HalfDensity`, `Problem2`, and `CQ w0011Col` to
Multiples of 4 with `4 * k >= 8`
(`problem1_of_subseq_two_halfDensity_and_problem2_and_CQ_w0011_and_canonical_balanced_four_mul_ge_two_CQ`):**
under `Rule30LeftAntiPeriod.HalfDensity (Rule30LeftAntiPeriod.subseq Rule30Prize.center 2 r)`
(**open**), `Rule30Prize.Problem2` (**open**), and `CQ w0011Col` (**open**) (without assuming
`CQ01`), to prove `Rule30Prize.Problem1` it suffices to establish `CQ ω` solely for canonical
`(4 * k)`-periodic sequences `ω` (`ω 0 = true`) with `2 ≤ k` (`4 * k ≥ 8`) and
`winCount ω 0 (4 * k) = 2 * k`. -/
theorem problem1_of_subseq_two_halfDensity_and_problem2_and_CQ_w0011_and_canonical_balanced_four_mul_ge_two_CQ
    {r : Nat}
    (hd2 : Rule30LeftAntiPeriod.HalfDensity (Rule30LeftAntiPeriod.subseq Rule30Prize.center 2 r))
    (hP2 : Rule30Prize.Problem2) (hCQ0011 : CQ w0011Col)
    (hCQ : ∀ (k : Nat) (ω : Nat → Bool), 2 ≤ k →
      (∀ t, ω (t + 4 * k) = ω t) →
      ω 0 = true →
      Rule30LeftAntiPeriod.winCount ω 0 (4 * k) = 2 * k → CQ ω) :
    Rule30Prize.Problem1 := by
  rintro ⟨T, P, hP, hper⟩
  obtain ⟨k, hk_pos, hP_eq⟩ := four_dvd_period_of_subseq_two_halfDensity hd2 hP hper
  have hper_4k : ∀ t, T ≤ t → Rule30Prize.center (t + 4 * k) = Rule30Prize.center t := by
    intro t ht; rw [← hP_eq]; exact hper t ht
  let ω₀ : Nat → Bool := fun t => Rule30Prize.center (T + t)
  have hper_ω₀ : ∀ t, ω₀ (t + 4 * k) = ω₀ t := fun t => by
    show Rule30Prize.center (T + (t + 4 * k)) = Rule30Prize.center (T + t)
    rw [show T + (t + 4 * k) = (T + t) + 4 * k by omega]
    exact hper_4k (T + t) (by omega)
  have hhd_ω₀ : Rule30LeftAntiPeriod.HalfDensity ω₀ :=
    (Rule30LeftAntiPeriod.halfDensity_shift_iff Rule30Prize.center T).mpr hP2
  have hbal₀ : 2 * Rule30LeftAntiPeriod.winCount ω₀ 0 (4 * k) = 4 * k :=
    (Rule30LeftAntiPeriod.periodic_halfDensity_iff_two_mul_winCount_eq
      (f := ω₀) (T := 0) (L := 4 * k) (by omega) (fun t _ => hper_ω₀ t)).mp hhd_ω₀
  have hwin₀ : Rule30LeftAntiPeriod.winCount ω₀ 0 (4 * k) = 2 * k := by omega
  have hblack : ∃ s, ω₀ s = true := by
    refine Classical.byContradiction fun hno => ?_
    have hall : ∀ t, ω₀ t = false := fun t => by
      cases hω : ω₀ t
      · rfl
      · exact False.elim (hno ⟨t, hω⟩)
    have hzero : ∀ d, Rule30LeftAntiPeriod.winCount ω₀ 0 d = 0 := by
      intro d; induction d with
      | zero => rfl
      | succ d ih => simp [Rule30LeftAntiPeriod.winCount, ih, hall d]
    rw [hzero (4 * k)] at hwin₀
    omega
  obtain ⟨s, hs_true⟩ := hblack
  let ω : Nat → Bool := fun t => Rule30Prize.center (T + s + t)
  have hω_eq : ω = fun t => ω₀ (t + s) := by
    funext t; show Rule30Prize.center (T + s + t) = Rule30Prize.center (T + (t + s))
    rw [show T + s + t = T + (t + s) by omega]
  have hper_ω : ∀ t, ω (t + 4 * k) = ω t := fun t => by
    show Rule30Prize.center (T + s + (t + 4 * k)) = Rule30Prize.center (T + s + t)
    rw [show T + s + (t + 4 * k) = (T + s + t) + 4 * k by omega]
    exact hper_4k (T + s + t) (by omega)
  have hwin_ω : Rule30LeftAntiPeriod.winCount ω 0 (4 * k) = 2 * k := by
    rw [hω_eq, winCount_shift_of_periodic hper_ω₀ s, hwin₀]
  have h0_ω : ω 0 = true := by
    show Rule30Prize.center (T + s + 0) = true
    simpa [Nat.add_zero] using hs_true
  by_cases hk2 : 2 ≤ k
  · have hC : CQ ω := hCQ k ω hk2 hper_ω h0_ω hwin_ω
    rw [CQ_iff_no_finite_config] at hC
    have hseed : FinConfig seed := ⟨0, fun p hp => by show decide (p = 0) = false; simp; omega⟩
    refine hC ⟨fun p => evol seed (T + s) p, evol_finConfig hseed (T + s), fun t => ?_⟩
    rw [Rule30ZeroBoundaryBarriers.evol_restart seed (T + s) t 0]
    exact evol_seed (T + s + t) 0
  · obtain rfl : k = 1 := by omega
    exact not_center_shift_four_periodic_balanced_of_subseq_two_halfDensity_and_CQ_w0011
      (T := T + s) hd2 hCQ0011 hper_ω h0_ω hwin_ω

/-! ### Arbitrary-Horizon Dyadic Coupled Reduction (`2^(K+1) * q`) and Elimination of Both `CQ01` and `CQ w0011Col` at `K = 2` (`8 * q >= 8`) -/

/-- **Arbitrary-Horizon Dyadic Coupled Reduction of `Problem1`
(`problem1_of_dyadic_subseq_halfDensity_and_problem2_and_canonical_balanced_two_pow_mul_CQ`):**
if `1 ≤ K`, `Rule30LeftAntiPeriod.HalfDensity (Rule30LeftAntiPeriod.subseq Rule30Prize.center (2 ^ a) r)`
holds for some `r` at each level `1 ≤ a ≤ K` (**open**), and `Rule30Prize.Problem2` (**open**)
holds, then to prove `Rule30Prize.Problem1` it suffices to establish `CQ ω` solely for canonical
`(2 ^ (K + 1) * q)`-periodic sequences `ω` (`ω 0 = true`, `1 ≤ q`) with
`winCount ω 0 (2 ^ (K + 1) * q) = 2 ^ K * q`. -/
theorem problem1_of_dyadic_subseq_halfDensity_and_problem2_and_canonical_balanced_two_pow_mul_CQ
    {K : Nat} (hK : 1 ≤ K)
    (hdyadic : ∀ a : Nat, 1 ≤ a → a ≤ K →
      ∃ r : Nat, Rule30LeftAntiPeriod.HalfDensity (Rule30LeftAntiPeriod.subseq Rule30Prize.center (2 ^ a) r))
    (hP2 : Rule30Prize.Problem2)
    (hCQ : ∀ (q : Nat) (ω : Nat → Bool), 1 ≤ q →
      (∀ t, ω (t + 2 ^ (K + 1) * q) = ω t) →
      ω 0 = true →
      Rule30LeftAntiPeriod.winCount ω 0 (2 ^ (K + 1) * q) = 2 ^ K * q → CQ ω) :
    Rule30Prize.Problem1 := by
  rintro ⟨T, P, hP, hper⟩
  obtain ⟨q, hq_pos, hP_eq⟩ :=
    Rule30LeftAntiPeriod.two_pow_succ_dvd_of_evPer_and_dyadic_subseq_halfDensity hK hP hdyadic ⟨T, hper⟩
  let L := 2 ^ (K + 1) * q
  have hL_eq : 2 * (2 ^ K * q) = L := by
    show 2 * (2 ^ K * q) = 2 ^ (K + 1) * q
    rw [← Nat.mul_assoc, ← Nat.pow_succ']
  have hL_pos : 0 < L := Nat.mul_pos (Nat.two_pow_pos _) hq_pos
  have hper_L : ∀ t, T ≤ t → Rule30Prize.center (t + L) = Rule30Prize.center t := by
    intro t ht; change Rule30Prize.center (t + 2 ^ (K + 1) * q) = Rule30Prize.center t; rw [← hP_eq]; exact hper t ht
  let ω₀ : Nat → Bool := fun t => Rule30Prize.center (T + t)
  have hper_ω₀ : ∀ t, ω₀ (t + L) = ω₀ t := fun t => by
    show Rule30Prize.center (T + (t + L)) = Rule30Prize.center (T + t)
    rw [show T + (t + L) = (T + t) + L by omega]
    exact hper_L (T + t) (by omega)
  have hhd_ω₀ : Rule30LeftAntiPeriod.HalfDensity ω₀ :=
    (Rule30LeftAntiPeriod.halfDensity_shift_iff Rule30Prize.center T).mpr hP2
  have hbal₀ : 2 * Rule30LeftAntiPeriod.winCount ω₀ 0 L = L :=
    (Rule30LeftAntiPeriod.periodic_halfDensity_iff_two_mul_winCount_eq
      (f := ω₀) (T := 0) (L := L) hL_pos (fun t _ => hper_ω₀ t)).mp hhd_ω₀
  have hwin₀ : Rule30LeftAntiPeriod.winCount ω₀ 0 L = 2 ^ K * q := by omega
  have hblack : ∃ s, ω₀ s = true := by
    refine Classical.byContradiction fun hno => ?_
    have hall : ∀ t, ω₀ t = false := fun t => by
      cases hω : ω₀ t
      · rfl
      · exact False.elim (hno ⟨t, hω⟩)
    have hzero : ∀ d, Rule30LeftAntiPeriod.winCount ω₀ 0 d = 0 := by
      intro d; induction d with
      | zero => rfl
      | succ d ih => simp [Rule30LeftAntiPeriod.winCount, ih, hall d]
    rw [hzero L] at hbal₀
    omega
  obtain ⟨s, hs_true⟩ := hblack
  let ω : Nat → Bool := fun t => Rule30Prize.center (T + s + t)
  have hω_eq : ω = fun t => ω₀ (t + s) := by
    funext t; show Rule30Prize.center (T + s + t) = Rule30Prize.center (T + (t + s))
    rw [show T + s + t = T + (t + s) by omega]
  have hper_ω : ∀ t, ω (t + L) = ω t := fun t => by
    show Rule30Prize.center (T + s + (t + L)) = Rule30Prize.center (T + s + t)
    rw [show T + s + (t + L) = (T + s + t) + L by omega]
    exact hper_L (T + s + t) (by omega)
  have hwin_ω : Rule30LeftAntiPeriod.winCount ω 0 L = 2 ^ K * q := by
    rw [hω_eq, winCount_shift_of_periodic hper_ω₀ s, hwin₀]
  have h0_ω : ω 0 = true := by
    show Rule30Prize.center (T + s + 0) = true
    simpa [Nat.add_zero] using hs_true
  have hC : CQ ω := hCQ q ω hq_pos hper_ω h0_ω hwin_ω
  rw [CQ_iff_no_finite_config] at hC
  have hseed : FinConfig seed := ⟨0, fun p hp => by show decide (p = 0) = false; simp; omega⟩
  refine hC ⟨fun p => evol seed (T + s) p, evol_finConfig hseed (T + s), fun t => ?_⟩
  rw [Rule30ZeroBoundaryBarriers.evol_restart seed (T + s) t 0]
  exact evol_seed (T + s + t) 0

/-- **Modulo-8 Coupled Reduction of `Problem1` Without `CQ01` or `CQ w0011Col`
(`problem1_of_subseq_two_four_halfDensity_and_problem2_and_canonical_balanced_eight_mul_CQ`):**
under `HalfDensity (subseq Rule30Prize.center 2 r₁)` (**open**),
`HalfDensity (subseq Rule30Prize.center 4 r₂)` (**open**), and `Rule30Prize.Problem2` (**open**)
(without assuming `CQ01` or `CQ w0011Col`), to prove `Rule30Prize.Problem1` it suffices to
establish `CQ ω` solely for canonical `(8 * q)`-periodic sequences `ω` (`ω 0 = true`, `1 ≤ q`)
with `winCount ω 0 (8 * q) = 4 * q`. -/
theorem problem1_of_subseq_two_four_halfDensity_and_problem2_and_canonical_balanced_eight_mul_CQ
    {r₁ r₂ : Nat}
    (hd2 : Rule30LeftAntiPeriod.HalfDensity (Rule30LeftAntiPeriod.subseq Rule30Prize.center 2 r₁))
    (hd4 : Rule30LeftAntiPeriod.HalfDensity (Rule30LeftAntiPeriod.subseq Rule30Prize.center 4 r₂))
    (hP2 : Rule30Prize.Problem2)
    (hCQ : ∀ (q : Nat) (ω : Nat → Bool), 1 ≤ q →
      (∀ t, ω (t + 8 * q) = ω t) →
      ω 0 = true →
      Rule30LeftAntiPeriod.winCount ω 0 (8 * q) = 4 * q → CQ ω) :
    Rule30Prize.Problem1 :=
  problem1_of_dyadic_subseq_halfDensity_and_problem2_and_canonical_balanced_two_pow_mul_CQ
    (K := 2) (by decide)
    (fun a ha1 ha2 => by
      have : a = 1 ∨ a = 2 := by omega
      rcases this with rfl | rfl
      · exact ⟨r₁, hd2⟩
      · exact ⟨r₂, hd4⟩)
    hP2 hCQ

/-! ### Exhaustive Classification of 4-Anti-Periodic Columns into Two Necklaces (`w00001111Col`, `w00101101Col`) and Period-8 Coupled Discharge -/

/-- **The Canonical 8-Periodic 4-Contiguous-Black Column (`w00001111Col`):**
`w00001111Col t = decide (4 ≤ t % 8)`, repeating `[false, false, false, false, true, true, true, true]`. -/
def w00001111Col (t : Nat) : Bool := decide (4 ≤ t % 8)

/-- **The Canonical 8-Periodic `00101101` Necklace Column (`w00101101Col`):** repeating
`[false, false, true, false, true, true, false, true]`. -/
def w00101101Col (t : Nat) : Bool :=
  let r := t % 8
  decide (r = 2 ∨ r = 4 ∨ r = 5 ∨ r = 7)

/-- **Exhaustive 8-Bit Shift Classification of 4-Anti-Periodic Columns
(`antiPeriodic_four_shift_eq_w00001111Col_or_w00101101Col`):** every sequence `ω : Nat → Bool`
satisfying `∀ t, ω (t + 4) = !ω t` is a cyclic shift of either `w00001111Col` or `w00101101Col`. -/
theorem antiPeriodic_four_shift_eq_w00001111Col_or_w00101101Col {ω : Nat → Bool}
    (hanti : ∀ t : Nat, ω (t + 4) = !ω t) :
    (∃ s : Nat, ∀ t : Nat, ω (t + s) = w00001111Col t) ∨
    (∃ s : Nat, ∀ t : Nat, ω (t + s) = w00101101Col t) := by
  have hper8 : ∀ t : Nat, ω (t + 8) = ω t := fun t => by
    rw [show t + 8 = (t + 4) + 4 by omega, hanti (t + 4), hanti t, Bool.not_not]
  have hmod8 : ∀ t : Nat, ω t = ω (t % 8) := fun t => by
    have hdiv : ∀ q r : Nat, ω (r + 8 * q) = ω r := by
      intro q r; induction q with
      | zero => simp
      | succ q ih => rw [Nat.mul_succ, ← Nat.add_assoc, hper8, ih]
    conv => lhs; rw [← Nat.mod_add_div t 8]
    exact hdiv (t / 8) (t % 8)
  have h4 : ω 4 = !ω 0 := hanti 0
  have h5 : ω 5 = !ω 1 := hanti 1
  have h6 : ω 6 = !ω 2 := hanti 2
  have h7 : ω 7 = !ω 3 := hanti 3
  have hdec : ∀ b₀ b₁ b₂ b₃ : Bool,
      (∃ s < 8, ∀ r < 8,
        (let idx := (r + s) % 8
         if idx = 0 then b₀ else if idx = 1 then b₁ else if idx = 2 then b₂ else if idx = 3 then b₃
         else if idx = 4 then !b₀ else if idx = 5 then !b₁ else if idx = 6 then !b₂ else !b₃) =
        w00001111Col r) ∨
      (∃ s < 8, ∀ r < 8,
        (let idx := (r + s) % 8
         if idx = 0 then b₀ else if idx = 1 then b₁ else if idx = 2 then b₂ else if idx = 3 then b₃
         else if idx = 4 then !b₀ else if idx = 5 then !b₁ else if idx = 6 then !b₂ else !b₃) =
        w00101101Col r) := by decide
  have hlookup : ∀ n : Nat, ω n =
      (let idx := n % 8
       if idx = 0 then ω 0 else if idx = 1 then ω 1 else if idx = 2 then ω 2 else if idx = 3 then ω 3
       else if idx = 4 then !ω 0 else if idx = 5 then !ω 1 else if idx = 6 then !ω 2 else !ω 3) := by
    intro n
    rw [hmod8 n]
    have hlt : n % 8 < 8 := Nat.mod_lt n (by decide)
    rcases (by omega : n % 8 = 0 ∨ n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 3 ∨
                       n % 8 = 4 ∨ n % 8 = 5 ∨ n % 8 = 6 ∨ n % 8 = 7) with
      h | h | h | h | h | h | h | h <;> simp [h, h4, h5, h6, h7]
  rcases hdec (ω 0) (ω 1) (ω 2) (ω 3) with ⟨s, _, hs⟩ | ⟨s, _, hs⟩
  · left; refine ⟨s, fun t => ?_⟩
    rw [hlookup (t + s)]
    have hmod_add : (t + s) % 8 = (t % 8 + s) % 8 := by omega
    have hw : w00001111Col t = w00001111Col (t % 8) := by
      unfold w00001111Col; rw [Nat.mod_mod]
    rw [hmod_add, hw]
    exact hs (t % 8) (Nat.mod_lt t (by decide))
  · right; refine ⟨s, fun t => ?_⟩
    rw [hlookup (t + s)]
    have hmod_add : (t + s) % 8 = (t % 8 + s) % 8 := by omega
    have hw : w00101101Col t = w00101101Col (t % 8) := by
      unfold w00101101Col; rw [Nat.mod_mod]
    rw [hmod_add, hw]
    exact hs (t % 8) (Nat.mod_lt t (by decide))

/-- **Discharging All 4-Anti-Periodic Columns from `CQ w00001111Col` and `CQ w00101101Col`
(`CQ_of_antiPeriodic_four`):** if `CQ w00001111Col` (**open**) and `CQ w00101101Col` (**open**)
hold, then `CQ ω` holds for every 4-anti-periodic sequence `ω` (`∀ t, ω (t + 4) = !ω t`). -/
theorem CQ_of_antiPeriodic_four {ω : Nat → Bool}
    (h1 : CQ w00001111Col) (h2 : CQ w00101101Col)
    (hanti : ∀ t : Nat, ω (t + 4) = !ω t) : CQ ω := by
  rcases antiPeriodic_four_shift_eq_w00001111Col_or_w00101101Col hanti with ⟨s, hs⟩ | ⟨s, hs⟩
  · rw [CQ_iff_no_finite_config] at h1 ⊢
    rintro ⟨c, hfin, hcol⟩
    refine h1 ⟨fun p => evol c s p, evol_finConfig hfin s, fun t => ?_⟩
    rw [Rule30ZeroBoundaryBarriers.evol_restart c s t 0, hcol (s + t), Nat.add_comm s t, hs t]
  · rw [CQ_iff_no_finite_config] at h2 ⊢
    rintro ⟨c, hfin, hcol⟩
    refine h2 ⟨fun p => evol c s p, evol_finConfig hfin s, fun t => ?_⟩
    rw [Rule30ZeroBoundaryBarriers.evol_restart c s t 0, hcol (s + t), Nat.add_comm s t, hs t]

/-- **Discharging Period 8 (`q = 1`) Under All-Residue Stride-4 `HalfDensity` and `CQ` on the Two
Anti-Periodic Necklaces (`CQ_of_periodic_eight_and_all_subseq_four_halfDensity`):** if
`∀ t, ω (t + 8) = ω t`, `∀ r < 4, HalfDensity (subseq ω 4 r)`, `CQ w00001111Col` (**open**),
and `CQ w00101101Col` (**open**), then `CQ ω` holds. -/
theorem CQ_of_periodic_eight_and_all_subseq_four_halfDensity {ω : Nat → Bool}
    (h1 : CQ w00001111Col) (h2 : CQ w00101101Col)
    (hper8 : ∀ t : Nat, ω (t + 8) = ω t)
    (hhd4 : ∀ r : Nat, r < 4 → Rule30LeftAntiPeriod.HalfDensity (Rule30LeftAntiPeriod.subseq ω 4 r)) :
    CQ ω :=
  CQ_of_antiPeriodic_four h1 h2
    (fun t => Rule30LeftAntiPeriod.antiPeriodic_of_periodic_two_mul_and_all_subseq_halfDensity
      (M := 4) (T₀ := 0) (by decide) (fun j _ => hper8 j) hhd4 t (Nat.zero_le t))

/-- **Exclusion of Eventual 4-Anti-Periodicity of `center` Under `CQ w00001111Col` and
`CQ w00101101Col` (`not_eventually_antiPeriodic_four_of_CQ`):** under `CQ w00001111Col`
(**open**) and `CQ w00101101Col` (**open**), `Rule30Prize.center` is never eventually
4-anti-periodic. -/
theorem not_eventually_antiPeriodic_four_of_CQ
    (h1 : CQ w00001111Col) (h2 : CQ w00101101Col) :
    ¬ ∃ T : Nat, ∀ t : Nat, T ≤ t → Rule30Prize.center (t + 4) = !Rule30Prize.center t := by
  rintro ⟨T, hanti⟩
  let ω : Nat → Bool := fun t => Rule30Prize.center (T + t)
  have hanti_ω : ∀ t : Nat, ω (t + 4) = !ω t := fun t => by
    show Rule30Prize.center (T + (t + 4)) = !Rule30Prize.center (T + t)
    rw [show T + (t + 4) = (T + t) + 4 by omega]
    exact hanti (T + t) (by omega)
  have hC : CQ ω := CQ_of_antiPeriodic_four h1 h2 hanti_ω
  rw [CQ_iff_no_finite_config] at hC
  have hseed : FinConfig seed := ⟨0, fun p hp => by show decide (p = 0) = false; simp; omega⟩
  refine hC ⟨fun p => evol seed T p, evol_finConfig hseed T, fun t => ?_⟩
  rw [Rule30ZeroBoundaryBarriers.evol_restart seed T t 0]
  exact evol_seed (T + t) 0

end Rule30Coupled
end Ruliology.CellularAutomata
