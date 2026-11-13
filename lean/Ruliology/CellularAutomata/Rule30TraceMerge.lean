module

public import Ruliology.CellularAutomata.Rule30TraceEdge

/-!
# A limitation of reconstructing the left half from one center trace

Two explicit configurations with left edge -3 have the same entire center
trace but different initial cells at -1. Their right halves are periodic and
infinite. Their complete rows merge after one step and become finite after
two steps. Thus eventual finiteness cannot replace finiteness at time zero
in a proposed stronger left-reconstruction argument.

This is NOT a counterexample to EdgeObservable: the left edges agree. It is
also NOT a counterexample involving two finite initial configurations.
No full prize problem is claimed solved.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30TraceMerge

open Rule30Jen Rule30Realization Rule30PeriodTwoSideways Rule30TraceEdge

/-- Initial word 1010 at positions -3..0, followed by (010)^infinity. -/
def leftExample (p : Int) : Bool :=
  if p ≤ 0 then decide (p = -3 ∨ p = -1) else decide (p % 3 = 2)

/-- Initial word 1100 at positions -3..0, followed by (100)^infinity. -/
def rightExample (p : Int) : Bool :=
  if p ≤ 0 then decide (p = -3 ∨ p = -2) else decide (p % 3 = 1)

def commonImage (p : Int) : Bool := decide (-4 ≤ p ∧ p ≠ -2)

def finiteImage (p : Int) : Bool := decide (p = -5 ∨ p = -4 ∨ p = -1)

theorem left_white {p : Int} (hp : p < -3) : leftExample p = false := by
  simp only [leftExample, ite_eq_left (show p ≤ 0 by omega), decide_eq_false_iff_not]
  omega

theorem right_white {p : Int} (hp : p < -3) : rightExample p = false := by
  simp only [rightExample, ite_eq_left (show p ≤ 0 by omega), decide_eq_false_iff_not]
  omega

theorem left_edge : HasLeftEdge leftExample (-3) := ⟨by decide, fun _ h => left_white h⟩

theorem right_edge : HasLeftEdge rightExample (-3) := ⟨by decide, fun _ h => right_white h⟩

theorem one_step_images (p : Int) :
    evol leftExample 1 p = commonImage p ∧ evol rightExample 1 p = commonImage p := by
  by_cases hlow : p < -4
  · have hl : ∀ q, q < -3 → leftExample q = false := fun _ h => left_white h
    have hr : ∀ q, q < -3 → rightExample q = false := fun _ h => right_white h
    change rule (leftExample (p-1)) (leftExample p) (leftExample (p+1)) = _ ∧
      rule (rightExample (p-1)) (rightExample p) (rightExample (p+1)) = _
    rw [hl _ (by omega), hl _ (by omega), hl _ (by omega),
        hr _ (by omega), hr _ (by omega), hr _ (by omega)]
    simp [rule, commonImage, show ¬ -4 ≤ p by omega]
  · by_cases hhigh : 2 ≤ p
    · have hmod : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
      change rule (leftExample (p-1)) (leftExample p) (leftExample (p+1)) = _ ∧
        rule (rightExample (p-1)) (rightExample p) (rightExample (p+1)) = _
      rcases hmod with hm | hm | hm <;>
        simp [leftExample, rightExample, rule, commonImage,
          show ¬ p-1 ≤ 0 by omega, show ¬ p ≤ 0 by omega,
          show ¬ p+1 ≤ 0 by omega, show -4 ≤ p by omega, show p ≠ -2 by omega,
          show (p-1)%3 = (p%3+2)%3 by omega,
          show (p+1)%3 = (p%3+1)%3 by omega, hm]
    · have hp : p = -4 ∨ p = -3 ∨ p = -2 ∨ p = -1 ∨ p = 0 ∨ p = 1 := by omega
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem common_second_image (p : Int) : evol commonImage 1 p = finiteImage p := by
  by_cases hlow : p < -5
  · change rule (commonImage (p-1)) (commonImage p) (commonImage (p+1)) = _
    simp [commonImage, finiteImage, rule,
      show ¬ -4 ≤ p-1 by omega, show ¬ -4 ≤ p by omega,
      show ¬ -4 ≤ p+1 by omega, show p ≠ -5 by omega,
      show p ≠ -4 by omega, show p ≠ -1 by omega]
  · by_cases hhigh : 1 ≤ p
    · change rule (commonImage (p-1)) (commonImage p) (commonImage (p+1)) = _
      simp [commonImage, finiteImage, rule,
        show -4 ≤ p-1 by omega, show -4 ≤ p by omega,
        show -4 ≤ p+1 by omega, show p-1 ≠ -2 by omega,
        show p ≠ -2 by omega, show p+1 ≠ -2 by omega,
        show p ≠ -5 by omega, show p ≠ -4 by omega, show p ≠ -1 by omega]
    · have hp : p = -5 ∨ p = -4 ∨ p = -3 ∨ p = -2 ∨ p = -1 ∨ p = 0 := by omega
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem same_images : evol leftExample 1 = evol rightExample 1 :=
  funext fun p => (one_step_images p).1.trans (one_step_images p).2.symm

/-- Exact infinite trace equality, not a finite numerical agreement. -/
theorem same_center_trace : ∀ t, evol leftExample t 0 = evol rightExample t 0
  | 0 => by decide
  | t+1 => by
    rw [show t+1 = 1+t by omega,
        ← Rule30ZeroBoundaryBarriers.evol_restart leftExample 1 t 0,
        ← Rule30ZeroBoundaryBarriers.evol_restart rightExample 1 t 0]
    rw [show (fun p => evol leftExample 1 p) = (fun p => evol rightExample 1 p) from same_images]

theorem different_left_neighbor : leftExample (-1) ≠ rightExample (-1) := by decide

theorem finite_after_two : FinConfig (evol leftExample 2) ∧ FinConfig (evol rightExample 2) := by
  have hfin : FinConfig finiteImage := ⟨5, fun p hp => by
    simp only [finiteImage, decide_eq_false_iff_not]
    omega⟩
  have hl : evol leftExample 1 = commonImage := funext fun p => (one_step_images p).1
  have hr : evol rightExample 1 = commonImage := funext fun p => (one_step_images p).2
  have hc : evol commonImage 1 = finiteImage := funext common_second_image
  have l2 : evol leftExample 2 = finiteImage := by
    funext p
    rw [show 2 = 1+1 from rfl, ← Rule30ZeroBoundaryBarriers.evol_restart leftExample 1 1 p]
    change evol (evol leftExample 1) 1 p = _
    rw [hl, hc]
  have r2 : evol rightExample 2 = finiteImage := by
    funext p
    rw [show 2 = 1+1 from rfl, ← Rule30ZeroBoundaryBarriers.evol_restart rightExample 1 1 p]
    change evol (evol rightExample 1) 1 p = _
    rw [hr, hc]
  rw [l2, r2]
  exact ⟨hfin,hfin⟩

theorem initial_rows_not_finite : ¬ FinConfig leftExample ∧ ¬ FinConfig rightExample := by
  constructor
  · rintro ⟨W,hW⟩
    have hf := hW (3*(W:Int)+5) (by omega)
    have ht : leftExample (3*(W:Int)+5) = true := by
      simp only [leftExample, ite_eq_right (by omega : ¬ 3*(W:Int)+5 ≤ 0), decide_eq_true_eq]
      omega
    rw [ht] at hf
    cases hf
  · rintro ⟨W,hW⟩
    have hf := hW (3*(W:Int)+4) (by omega)
    have ht : rightExample (3*(W:Int)+4) = true := by
      simp only [rightExample, ite_eq_right (by omega : ¬ 3*(W:Int)+4 ≤ 0), decide_eq_true_eq]
      omega
    rw [ht] at hf
    cases hf

/-- Initial right finiteness cannot be replaced by eventual finiteness in a
stronger claim that the center trace determines the entire initial left half. -/
theorem no_left_recovery_from_eventual_finiteness :
    ∃ x y : Int → Bool, HasLeftEdge x (-3) ∧ HasLeftEdge y (-3) ∧
      (∀ t, evol x t 0 = evol y t 0) ∧ x (-1) ≠ y (-1) ∧
      FinConfig (evol x 2) ∧ FinConfig (evol y 2) ∧ ¬ FinConfig x ∧ ¬ FinConfig y :=
  ⟨leftExample,rightExample,left_edge,right_edge,same_center_trace,
    different_left_neighbor,finite_after_two.1,finite_after_two.2,
    initial_rows_not_finite.1,initial_rows_not_finite.2⟩

/-- Unlike full left recovery, edge recovery extends to initially infinite
rows that become finite, because their left edge keeps moving at speed one. -/
def EventualFiniteEdgeObservable : Prop :=
  ∀ (x y : Int → Bool), (∃ t, FinConfig (evol x t)) → (∃ t, FinConfig (evol y t)) →
    ∀ a b, HasLeftEdge x a → HasLeftEdge y b →
      (∀ t, evol x t 0 = evol y t 0) → a = b

theorem restart_row (x : Int → Bool) (a b : Nat) :
    evol (evol x a) b = evol x (a+b) :=
  funext fun p => Rule30ZeroBoundaryBarriers.evol_restart x a b p

/-- This equivalence does not establish either open edge-recovery property. -/
theorem eventual_finite_edge_iff : EventualFiniteEdgeObservable ↔ EdgeObservable := by
  constructor
  · intro h x y hx hy a b ha hb he
    exact h x y ⟨0,hx⟩ ⟨0,hy⟩ a b ha hb he
  · rintro h x y ⟨tx,hx⟩ ⟨ty,hy⟩ a b ha hb he
    have hxf : FinConfig (evol x (tx+ty)) := by
      rw [← restart_row x tx ty]
      exact Rule30FiniteConfigs.evol_finConfig hx ty
    have hyf : FinConfig (evol y (tx+ty)) := by
      rw [show tx+ty = ty+tx by omega, ← restart_row y ty tx]
      exact Rule30FiniteConfigs.evol_finConfig hy tx
    have hedge := h (evol x (tx+ty)) (evol y (tx+ty)) hxf hyf
      (a-(tx+ty)) (b-(tx+ty))
      (hasLeftEdge_evol ha (tx+ty)) (hasLeftEdge_evol hb (tx+ty))
      (fun t => by
        rw [Rule30ZeroBoundaryBarriers.evol_restart,Rule30ZeroBoundaryBarriers.evol_restart]
        exact he ((tx+ty)+t))
    omega

/-! ## All-column agreement from step `1` onward and exact support at step `2` -/

/-- **All-Column Agreement from Step `1` Onward and Exact Support at Step `2` (`same_all_columns_from_one_and_step_two_support`).** -/
theorem same_all_columns_from_one_and_step_two_support (t : Nat) (p : Int) :
    evol leftExample (t + 1) p = evol rightExample (t + 1) p ∧
    (evol leftExample 2 p = true ↔ p = -5 ∨ p = -4 ∨ p = -1) ∧
    (evol rightExample 2 p = true ↔ p = -5 ∨ p = -4 ∨ p = -1) := by
  have hall : ∀ s : Nat, evol leftExample (s + 1) p = evol rightExample (s + 1) p := by
    intro s
    rw [show s + 1 = 1 + s by omega,
        ← Rule30ZeroBoundaryBarriers.evol_restart leftExample 1 s p,
        ← Rule30ZeroBoundaryBarriers.evol_restart rightExample 1 s p,
        same_images]
  have hl2 : evol leftExample 2 p = finiteImage p := by
    rw [show (2 : Nat) = 1 + 1 from rfl,
        ← Rule30ZeroBoundaryBarriers.evol_restart leftExample 1 1 p]
    have hl1 : evol leftExample 1 = commonImage := funext fun q => (one_step_images q).1
    rw [hl1]
    exact common_second_image p
  have hr2 : evol rightExample 2 p = finiteImage p := by
    rw [← hall 1, hl2]
  refine ⟨hall t, ?_, ?_⟩
  · rw [hl2]; unfold finiteImage; exact decide_eq_true_iff
  · rw [hr2]; unfold finiteImage; exact decide_eq_true_iff

end Ruliology.CellularAutomata.Rule30TraceMerge
