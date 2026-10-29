module
public import Ruliology.CellularAutomata.Rule30ProfileClockSharpness

/-! Explicit wave classification within the checked clock range. A rightmost
black cell and global prefix period32 force an alternating initial left tail.
Conversely those two tails have global right-diagonal period2. Nothing here
classifies arbitrary larger clocks or a vertical center-column trace. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30LowClockWaves
open Rule30RightProfiles Rule30RightPrefixClock Rule30RightPrefixBound
open Rule30ProfileClockEscape
set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

def AntiOne (f : Nat → Bool) : Prop := ∀t,f (t+1)=!f t

theorem two_alternating_force_opposite (a b c : Nat → Bool)
    (ha : AntiOne a) (hb : AntiOne b) (hc : Period c 2)
    (step : ∀t,c (t+1)=xor (c t) (b t || a t)) : ∀t,b t=!a t := by
  intro t
  have ret := hc t
  rw [show t+2=(t+1)+1 by omega,step (t+1),step t,ha t,hb t] at ret
  cases ea : a t <;> cases eb : b t <;> cases ec : c t <;>
    simp only [ea,eb,ec] at ret ⊢ <;> first | rfl | contradiction

theorem opposite_forces_alternating (a b c : Nat → Bool)
    (opposite : ∀t,b t=!a t)
    (step : ∀t,c (t+1)=xor (c t) (b t || a t)) : AntiOne c := by
  intro t
  rw [step,opposite]
  cases a t <;> cases c t <;> rfl

theorem alternating_initial_opposite (a b : Nat → Bool)
    (ha : AntiOne a) (hb : AntiOne b) (initial : b 0=!a 0) : ∀t,b t=!a t := by
  intro t
  induction t with
  | zero => exact initial
  | succ t ih =>
    rw [hb t,ha t,ih]

theorem anti_period_two {f : Nat → Bool} (h : AntiOne f) : Period f 2 := by
  intro t
  rw [show t+2=(t+1)+1 by omega,h (t+1),h t]
  cases f t <;> rfl

theorem array_opposite (P : Nat → Nat → Bool)
    (p0 : ∀t,P 0 t=true) (p1 : AntiOne (P 1))
    (step : ∀n t,P (n+2) (t+1)=xor (P (n+2) t) (P (n+1) t || P n t))
    (per : ∀n,Period (P n) 2) : ∀n t,P (n+2) t=!P (n+1) t := by
  have p2 : AntiOne (P 2) := by
    intro t
    rw [step 0 t,p0 t]
    cases P 1 t <;> cases P 2 t <;> rfl
  have pairs : ∀n,AntiOne (P (n+1)) ∧ AntiOne (P (n+2)) := by
    intro n
    induction n with
    | zero => exact ⟨p1,p2⟩
    | succ n ih =>
      have opp := two_alternating_force_opposite (P (n+1)) (P (n+2)) (P (n+3)) ih.1 ih.2 (per (n+3)) (step (n+1))
      exact ⟨ih.2,opposite_forces_alternating _ _ _ opp (step (n+1))⟩
  intro n
  exact two_alternating_force_opposite _ _ _ (pairs n).1 (pairs n).2 (per (n+3)) (step (n+1))

theorem array_period_two (P : Nat → Nat → Bool)
    (p0 : ∀t,P 0 t=true) (p1 : AntiOne (P 1))
    (step : ∀n t,P (n+2) (t+1)=xor (P (n+2) t) (P (n+1) t || P n t))
    (initial : ∀n,P (n+2) 0=!P (n+1) 0) : ∀n,Period (P n) 2 := by
  have p2 : AntiOne (P 2) := by
    intro t
    rw [step 0 t,p0 t]
    cases P 1 t <;> cases P 2 t <;> rfl
  have pairs : ∀n,AntiOne (P (n+1)) ∧ AntiOne (P (n+2)) := by
    intro n
    induction n with
    | zero => exact ⟨p1,p2⟩
    | succ n ih =>
      have opp := alternating_initial_opposite _ _ ih.1 ih.2 (initial n)
      exact ⟨ih.2,opposite_forces_alternating _ _ _ opp (step (n+1))⟩
  intro n
  by_cases hn : n=0
  · subst n;intro t;rw [p0,p0]
  · have h := anti_period_two (pairs (n-1)).1
    simpa only [show n-1+1=n by omega] using h

def P (x : Int → Bool) (R : Int) (n : Nat) : Nat → Bool := rightDiag x (-R+(n:Int))

theorem P_initial (x : Int → Bool) (R : Int) (n : Nat) : P x R n 0=x (R-(n:Int)) := by
  change x ((0:Int)-(-R+(n:Int)))=x (R-(n:Int))
  congr 1
  omega

theorem boundary_black (x : Int → Bool) (R : Int)
    (hx : ∀p,R<p → x p=false) (hR : x R=true) : ∀t,rightDiag x (-R) t=true := by
  have hp := right_boundary_prefix_one x R hx (-R) (by omega)
  intro t
  induction t with
  | zero => simpa [rightDiag,Rule30Realization.evol] using hR
  | succ t ih => exact (hp t).trans ih

theorem first_alternates (x : Int → Bool) (R : Int)
    (hx : ∀p,R<p → x p=false) (hR : x R=true) : AntiOne (P x R 1) := by
  intro t
  have h := rightDiag_step x (-R+1) t
  rw [show -R+1-1= -R by omega,show -R+1-2= -R-1 by omega,
    boundary_black x R hx hR t,right_white x R hx t (-R-1) (by omega)] at h
  change rightDiag x (-R+1) (t+1)=!rightDiag x (-R+1) t
  rw [h]
  cases rightDiag x (-R+1) t <;> rfl

theorem P_step (x : Int → Bool) (R : Int) (hx : ∀p,R<p → x p=false) :
    ∀n t,P x R (n+2) (t+1)=xor (P x R (n+2) t) (P x R (n+1) t || P x R n t) :=
  (actualClock x R hx).recurrence

/-- All globally period32 arrays with a genuine right edge have an alternating
initial left tail, starting one cell left of the rightmost black cell. -/
theorem global32_tail_alternates (x : Int → Bool) (R : Int)
    (hx : ∀p,R<p → x p=false) (hR : x R=true)
    (global : ∀n:Nat,PrefixPer (rightDiag x) (-R+(n:Int)) 32) :
    ∀n:Nat,x (R-((n+2:Nat):Int))=!x (R-((n+1:Nat):Int)) := by
  have p0 : ∀t,P x R 0 t=true := by
    simpa only [P,Int.ofNat_zero,Int.add_zero] using boundary_black x R hx hR
  have per := global_period32_forces_period2 x R hx global
  have opp := array_opposite (P x R) p0 (first_alternates x R hx hR) (P_step x R hx) per
  intro n
  have h := opp n 0
  rw [P_initial,P_initial] at h
  exact h

theorem alternating_tail_period_two (x : Int → Bool) (R : Int)
    (hx : ∀p,R<p → x p=false) (hR : x R=true)
    (tail : ∀n:Nat,x (R-((n+2:Nat):Int))=!x (R-((n+1:Nat):Int))) :
    ∀n:Nat,Period (P x R n) 2 := by
  have p0 : ∀t,P x R 0 t=true := by
    simpa only [P,Int.ofNat_zero,Int.add_zero] using boundary_black x R hx hR
  apply array_period_two (P x R) p0 (first_alternates x R hx hR) (P_step x R hx)
  intro n
  rw [P_initial,P_initial]
  exact tail n

theorem alternating_tail_prefix_two (x : Int → Bool) (R : Int)
    (hx : ∀p,R<p → x p=false) (hR : x R=true)
    (tail : ∀n:Nat,x (R-((n+2:Nat):Int))=!x (R-((n+1:Nat):Int))) :
    ∀n:Nat,PrefixPer (rightDiag x) (-R+(n:Int)) 2 := by
  have per := alternating_tail_period_two x R hx hR tail
  intro n i hi t
  by_cases white : i< -R
  · rw [right_white x R hx _ i white,right_white x R hx _ i white]
  · have cast : ((i+R).toNat:Int)=i+R := Int.toNat_of_nonneg (by omega)
    have index : -R+((i+R).toNat:Int)=i := by omega
    have h := per (i+R).toNat t
    simpa only [P,index] using h

/-- Within global period32, the two alternating-tail waves are the only
nonzero right-edge configurations. The converse has the stronger period2. -/
theorem global32_iff_alternating_tail (x : Int → Bool) (R : Int)
    (hx : ∀p,R<p → x p=false) (hR : x R=true) :
    (∀n:Nat,PrefixPer (rightDiag x) (-R+(n:Int)) 32) ↔
    (∀n:Nat,x (R-((n+2:Nat):Int))=!x (R-((n+1:Nat):Int))) := by
  constructor
  · exact global32_tail_alternates x R hx hR
  · intro tail n
    have hp := alternating_tail_prefix_two x R hx hR tail n
    exact prefix_pow_mono (a:=1) (b:=5) hp (by omega)

end Ruliology.CellularAutomata.Rule30LowClockWaves
