module
public import Ruliology.CellularAutomata.Rule30ResetFreeStrip
public import Ruliology.CellularAutomata.Rule30ZeroBoundary

/-! Actual zero-wall evolution and the five-phase reset alternative. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30ResetFreeBoundary
open Rule30ResetFreeCore Rule30ResetFreeRuns Rule30ResetFreeStrip Rule30ZeroBoundary
set_option maxRecDepth 30000
set_option maxHeartbeats 10000000

theorem zrow_recurrence (L : Nat → Bool) (T : Nat) :
    RowRecurrence (fun t k => zrow L (T+t.val) k) := by
  intro t p hp
  obtain ⟨k,hk⟩ : ∃ k,p=k+1 := ⟨p-1,by omega⟩
  subst p
  have h := zrow_succ L (T+t.val) k
  simpa only [show T+(t.val+1)=(T+t.val)+1 by omega,
    show k+1+1=k+2 by omega,show k+1-1=k by omega] using h

theorem zrow_five_reset_free_rows (L : Nat → Bool) (T : Nat)
    (avoid : ∀ t : Fin 5,AvoidReset (zrow L (T+t.val))) :
    ∃ M,∀ p,M≤p → zrow L T (p+5)=zrow L T p := by
  have h := five_reset_free_rows (fun t k => zrow L (T+t.val) k) (zrow_recurrence L T) avoid
  simpa only [fin0,Nat.add_zero] using h

theorem zrow_five_reset_free_tails (L : Nat → Bool) (T : Nat)
    (avoid : ∀ t : Fin 5,EventuallyAvoidReset (zrow L (T+t.val))) :
    ∃ M,∀ p,M≤p → zrow L T (p+5)=zrow L T p := by
  have h := five_reset_free_tails (fun t k => zrow L (T+t.val) k) (zrow_recurrence L T) avoid
  simpa only [fin0,Nat.add_zero] using h

theorem one_phase_has_unbounded_resets (L : Nat → Bool) (T : Nat)
    (notFive : ¬∃ M,∀ p,M≤p → zrow L T (p+5)=zrow L T p) :
    ∃ t : Fin 5,¬EventuallyAvoidReset (zrow L (T+t.val)) := by
  classical
  by_cases ex : ∃ t : Fin 5,¬EventuallyAvoidReset (zrow L (T+t.val))
  · exact ex
  · have every : ∀ t : Fin 5,EventuallyAvoidReset (zrow L (T+t.val)) := by
      intro t
      by_cases h : EventuallyAvoidReset (zrow L (T+t.val))
      · exact h
      · exact False.elim (ex ⟨t,h⟩)
    exact False.elim (notFive (zrow_five_reset_free_tails L T every))

theorem not_eventual_avoid (f : Nat → Bool) (bad : ¬EventuallyAvoidReset f) :
    ∀ K,∃ i n,K≤i ∧ n%3=1 ∧ f i=false ∧ f (i+n+1)=false ∧
      ∀ j,j<n → f (i+j+1)=true := by
  classical
  intro K
  by_cases ex : ∃ i n,K≤i ∧ n%3=1 ∧ f i=false ∧ f (i+n+1)=false ∧
      ∀ j,j<n → f (i+j+1)=true
  · exact ex
  · apply False.elim
    apply bad
    refine ⟨K,?_⟩
    intro i n left right ones modone
    apply ex
    refine ⟨K+i,n,by omega,modone,left,?_,?_⟩
    · simpa only [Nat.add_assoc] using right
    · intro j hj
      simpa only [Nat.add_assoc] using ones j hj

/-- Unless the spatial tail is already5-periodic, one of the next five rows
contains inverse-reset words arbitrarily far from the wall. -/
theorem arbitrarily_far_resets_in_five (L : Nat → Bool) (T : Nat)
    (notFive : ¬∃ M,∀ p,M≤p → zrow L T (p+5)=zrow L T p) :
    ∃ t : Fin 5,∀ K,∃ i n,K≤i ∧ n%3=1 ∧ zrow L (T+t.val) i=false ∧
      zrow L (T+t.val) (i+n+1)=false ∧ ∀ j,j<n → zrow L (T+t.val) (i+j+1)=true := by
  obtain ⟨t,ht⟩ := one_phase_has_unbounded_resets L T notFive
  exact ⟨t,not_eventual_avoid _ ht⟩

/-! ## Multi-period spatial tail invariance (`p + 5 * k`) under five reset-free tails -/

/-- **Multi-Period Spatial Tail Invariance Under Five Reset-Free Tails (`zrow_five_reset_free_tails_mul`).** -/
theorem zrow_five_reset_free_tails_mul (L : Nat → Bool) (T : Nat)
    (avoid : ∀ t : Fin 5, EventuallyAvoidReset (zrow L (T + t.val))) :
    ∃ M, ∀ p k, M ≤ p → zrow L T (p + 5 * k) = zrow L T p := by
  obtain ⟨M, hM⟩ := zrow_five_reset_free_tails L T avoid
  refine ⟨M, fun p k hp => ?_⟩
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show p + 5 * (k + 1) = (p + 5 * k) + 5 by omega,
        hM (p + 5 * k) (by omega), ih]

end Ruliology.CellularAutomata.Rule30ResetFreeBoundary
