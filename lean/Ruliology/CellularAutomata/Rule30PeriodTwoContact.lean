module
public import Ruliology.CellularAutomata.Rule30RightPrefixClock

/-! An exact reformulation of no return to temporal period two. The
unbounded assertion is NOT proved here: it is equivalent to a common-zero
assertion about adjacent actual right profiles. Single-profile no00 is
insufficient. This supplies a small interface for the next proof attempt. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30PeriodTwoContact
open Rule30RightProfiles Rule30RightPrefixClock
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

theorem forcing_constant (c f : Nat → Bool)
    (step : ∀t,c (t+1)=xor (c t) (f t)) (hc : Period c 2) :
    ∀t,f t=f 0 := by
  have same : ∀t,f (t+1)=f t := by
    intro t
    have back := step (t+1)
    rw [show t+1+1=t+2 by omega,hc t,step t] at back
    cases ef : f t <;> cases en : f (t+1) <;> cases ec : c t <;>
      simp only [ef,en,ec] at back ⊢ <;> first | rfl | contradiction
  intro t
  induction t with
  | zero => rfl
  | succ t ih => exact (same t).trans ih

theorem contact_forces_zero (a b c : Nat → Bool)
    (step : ∀t,c (t+1)=xor (c t) (a t || b t)) (hc : Period c 2)
    (u : Nat) (ha : a u=false) (hb : b u=false) : ∀t,b t=false := by
  have constant := forcing_constant c (fun t => a t || b t) step hc
  have initial : (a 0 || b 0)=false := by
    rw [←constant u,ha,hb]
    rfl
  intro t
  have zero : (a t || b t)=false := (constant t).trans initial
  cases eb : b t
  · rfl
  · cases a t <;> simp_all

theorem cover_forces_period_two (a b c : Nat → Bool)
    (step : ∀t,c (t+1)=xor (c t) (a t || b t))
    (cover : ∀t,(a t || b t)=true) : Period c 2 := by
  intro t
  rw [show t+2=(t+1)+1 by omega,step (t+1),step t,cover t,cover (t+1)]
  cases c t <;> rfl

def No00 (b : Nat → Bool) : Prop := ∀t,(b t || b (t+1))=true

theorem antiperiod_no00_toggle (f : Nat → Bool) (p : Nat)
    (anti : ∀t,f (t+p)=!f t) (hn : No00 f) : ∀t,f (t+1)=!f t := by
  intro t
  have near := hn t
  have far := hn (t+p)
  rw [anti t,show t+p+1=(t+1)+p by omega,anti (t+1)] at far
  cases ef : f t <;> cases en : f (t+1) <;>
    simp only [ef,en] at near far ⊢ <;> first | rfl | contradiction

theorem antiperiod_no00_period_two (f : Nat → Bool) (p : Nat)
    (anti : ∀t,f (t+p)=!f t) (hn : No00 f) : Period f 2 := by
  have toggle := antiperiod_no00_toggle f p anti hn
  intro t
  rw [show t+2=(t+1)+1 by omega,toggle (t+1),toggle t]
  cases f t <;> rfl

/-- A nonalternating isolated-zero profile cannot introduce a new prefix
period. This is uniform in the prior period, not a bounded-clock check. -/
theorem no00_nonperiod_two_no_growth (D : Int → Nat → Bool) (j : Int) (p : Nat)
    (step : Recurrence D) (old : PrefixPer D j p)
    (hn : No00 (D (j+1))) (bad : ¬Period (D (j+1)) 2) :
    PrefixPer D (j+1) p := by
  classical
  by_cases already : PrefixPer D (j+1) p
  · exact already
  · exact False.elim (bad (antiperiod_no00_period_two _ p
      (growth_antiperiod step old already) hn))

theorem actual_no00_nonperiod_two_no_growth (x : Int → Bool) (j : Int) (p : Nat)
    (old : PrefixPer (rightDiag x) j p)
    (hn : No00 (rightDiag x (j+1))) (bad : ¬Period (rightDiag x (j+1)) 2) :
    PrefixPer (rightDiag x) (j+1) p :=
  no00_nonperiod_two_no_growth _ j p (actual_recurrence x) old hn bad

theorem period_two_successor_forces_cover (a b c : Nat → Bool)
    (step : ∀t,c (t+1)=xor (c t) (a t || b t))
    (hc : Period c 2) (hb : ¬Period b 2) : ∀t,(a t || b t)=true := by
  intro t
  cases ea : a t <;> cases eb : b t
  · have zero := contact_forces_zero a b c step hc t ea eb
    exact False.elim (hb (by intro u;rw [zero,zero]))
  · rfl
  · rfl
  · rfl

theorem cover_running_forces_no00 (d a b : Nat → Bool)
    (step : ∀t,b (t+1)=xor (b t) (a t || d t))
    (cover : ∀t,(a t || b t)=true) : No00 b := by
  intro t
  cases eb : b t
  · have h := cover t
    have ha : a t=true := by cases ea : a t <;> simp_all
    rw [step t,eb,ha]
    cases d t <;> rfl
  · rfl

def NoReturnTwo (P : Nat → Nat → Bool) : Prop :=
  ∀n,Period (P (n+2)) 2 → Period (P (n+1)) 2

def ContactProgress (P : Nat → Nat → Bool) : Prop :=
  ∀n,¬Period (P (n+1)) 2 → ∃t,P n t=false ∧ P (n+1) t=false

/-- This is an equivalence of the missing claims, not a proof of either. -/
theorem contact_iff_no_return (P : Nat → Nat → Bool)
    (step : ∀n t,P (n+2) (t+1)=xor (P (n+2) t) (P n t || P (n+1) t)) :
    ContactProgress P ↔ NoReturnTwo P := by
  classical
  constructor
  · intro contacts n hc
    by_cases good : Period (P (n+1)) 2
    · exact good
    · obtain ⟨u,ha,hb⟩ := contacts n good
      have zero := contact_forces_zero (P n) (P (n+1)) (P (n+2)) (step n) hc u ha hb
      exact False.elim (good (by intro t;rw [zero,zero]))
  · intro noReturn n bad
    by_cases found : ∃t,P n t=false ∧ P (n+1) t=false
    · exact found
    · have cover : ∀t,(P n t || P (n+1) t)=true := by
        intro t
        cases ea : P n t <;> cases eb : P (n+1) t
        · exact False.elim (found ⟨t,ea,eb⟩)
        · rfl
        · rfl
        · rfl
      exact False.elim (bad (noReturn n (cover_forces_period_two _ _ _ (step n) cover)))

/-- A return-to-two counterexample must have an isolated-zero predecessor.
This restriction is necessary, not a proof that no counterexample exists. -/
theorem counter_predecessor_no00 (P : Nat → Nat → Bool)
    (step : ∀n t,P (n+2) (t+1)=xor (P (n+2) t) (P n t || P (n+1) t))
    (n : Nat) (hc : Period (P (n+3)) 2) (hb : ¬Period (P (n+2)) 2) :
    No00 (P (n+2)) := by
  have cover := period_two_successor_forces_cover (P (n+1)) (P (n+2)) (P (n+3))
    (step (n+1)) hc hb
  apply cover_running_forces_no00 (P n) (P (n+1)) (P (n+2)) _ cover
  intro t
  simpa only [Bool.or_comm] using step n t

def actualProfiles (x : Int → Bool) (n : Nat) : Nat → Bool := rightDiag x (n:Int)

theorem actual_step (x : Int → Bool) (n t : Nat) :
    actualProfiles x (n+2) (t+1)=xor (actualProfiles x (n+2) t)
      (actualProfiles x n t || actualProfiles x (n+1) t) := by
  have h := rightDiag_step x ((n+2:Nat):Int) t
  rw [show ((n+2:Nat):Int)-1=((n+1:Nat):Int) by omega,
    show ((n+2:Nat):Int)-2=(n:Int) by omega] at h
  simpa only [actualProfiles,Bool.or_comm] using h

theorem actual_contact_iff_no_return (x : Int → Bool) :
    ContactProgress (actualProfiles x) ↔ NoReturnTwo (actualProfiles x) :=
  contact_iff_no_return _ (actual_step x)

theorem actual_counter_predecessor_no00 (x : Int → Bool) (n : Nat)
    (hc : Period (actualProfiles x (n+3)) 2)
    (hb : ¬Period (actualProfiles x (n+2)) 2) : No00 (actualProfiles x (n+2)) :=
  counter_predecessor_no00 _ (actual_step x) n hc hb

end Ruliology.CellularAutomata.Rule30PeriodTwoContact
