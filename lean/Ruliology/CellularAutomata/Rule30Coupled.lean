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

end Rule30Coupled
end Ruliology.CellularAutomata
