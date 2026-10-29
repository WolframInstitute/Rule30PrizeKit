module
public import Ruliology.CellularAutomata.Rule30PeriodTwoContact
public import Ruliology.CellularAutomata.Rule30ProfileGraphCases

/-! A period-two return requires a large clock two columns earlier.
This strengthens the previous one-column condition, but leaves arbitrary
large hidden clocks and the general common-zero claim open. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30TwoBackClock
open Rule30RightProfiles Rule30RightPrefixClock Rule30RightPrefixBound
open Rule30ProfileGraph Rule30PeriodTwoContact
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 20000000

theorem two_back_period_two (x : Int → Bool) (R : Int)
    (hx : ∀p,R<p → x p=false) (n : Nat)
    (old : PrefixPer (rightDiag x) (-R+(n:Int)) 32)
    (current : Period (rightDiag x (-R+((n+2:Nat):Int))) 2) :
    Period (rightDiag x (-R+((n+1:Nat):Int))) 2 := by
  classical
  let j : Int := -R+(n:Int)
  have i1 : -R+((n+1:Nat):Int)=j+1 := by dsimp [j];omega
  have i2 : -R+((n+2:Nat):Int)=j+2 := by dsimp [j];omega
  rw [i1]
  by_cases good : Period (rightDiag x (j+1)) 2
  · exact good
  · have hc : Period (rightDiag x (j+2)) 2 := by rw [←i2];exact current
    have stepC : ∀t,rightDiag x (j+2) (t+1)=xor (rightDiag x (j+2) t)
        (rightDiag x j t || rightDiag x (j+1) t) := by
      intro t
      have h := rightDiag_step x (j+2) t
      rw [show j+2-1=j+1 by omega,show j+2-2=j by omega] at h
      simpa only [Bool.or_comm] using h
    have cover := period_two_successor_forces_cover _ _ _ stepC hc good
    have stepB : ∀t,rightDiag x (j+1) (t+1)=xor (rightDiag x (j+1) t)
        (rightDiag x j t || rightDiag x (j-1) t) := by
      intro t
      have h := rightDiag_step x (j+1) t
      simpa only [show j+1-1=j by omega,show j+1-2=j-1 by omega] using h
    have hn := cover_running_forces_no00 _ _ _ stepB cover
    have prior : PrefixPer (rightDiag x) (j+1) 32 :=
      actual_no00_nonperiod_two_no_growth x j 32 old hn good
    have pc : Period (rightDiag x (j+2)) 32 :=
      period_pow_mono (a:=1) (b:=5) hc (by omega)
    have pc' : Period (rightDiag x ((j+1)+1)) 32 := by
      rw [show j+1+1=j+2 by omega]
      exact pc
    have full : PrefixPer (rightDiag x) (-R+((n+2:Nat):Int)) 32 := by
      rw [i2]
      have h := prefix_extend prior pc'
      rw [show j+1+1=j+2 by omega] at h
      exact h
    have inherited := actual_period_inherits Rule30ProfileGraphCases.graph
      (by decide +kernel) (by decide +kernel) Rule30ProfileGraphCases.root_a
      Rule30ProfileGraphCases.root_b Rule30ProfileGraphCases.graph_valid
      x R hx (n+2) 1 (by decide +kernel) full current
    have index : -R+((n+2:Nat):Int)-1=j+1 := by dsimp [j];omega
    rw [index] at inherited
    exact inherited

theorem counter_two_back_clock64 (x : Int → Bool) (R : Int)
    (hx : ∀p,R<p → x p=false) (n : Nat)
    (current : Period (rightDiag x (-R+((n+2:Nat):Int))) 2)
    (previous : ¬Period (rightDiag x (-R+((n+1:Nat):Int))) 2) :
    6≤prefixExponent x R hx n := by
  by_cases high : 6≤prefixExponent x R hx n
  · exact high
  · have hp := prefix_pow_mono (prefixExponent_spec x R hx n).1
      (show prefixExponent x R hx n≤5 by omega)
    exact False.elim (previous (two_back_period_two x R hx n hp current))

end Ruliology.CellularAutomata.Rule30TwoBackClock
