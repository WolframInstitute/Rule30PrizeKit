module
public import Ruliology.CellularAutomata.Rule30Certificates.ProfileGraph32

/-! Every actual right-bounded seed has no individual period drop while its
whole-prefix clock is at most32, uniformly in spatial depth. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30ProfileGraphCases
open Rule30ProfileGraph
theorem actual_small_clock_minimal (x : Int → Bool) (R : Int)
    (hx : ∀p,R<p → x p=false) (n E : Nat) (hE : E≤5)
    (clock : Rule30RightPrefixClock.PrefixIsE (Rule30RightProfiles.rightDiag x) (-R+(n:Int)) E) :
    ∀e,e<E → ¬Rule30RightPrefixClock.Period (Rule30RightProfiles.rightDiag x (-R+(n:Int))) (2^e) :=
  actual_last_minimal graph (by decide +kernel) (by decide +kernel) root_a root_b graph_valid x R hx n E hE clock
theorem actual_no_drop_below_sixty_four (x : Int → Bool) (R : Int)
    (hx : ∀p,R<p → x p=false) (n E : Nat) (hE : E≤5)
    (clock : Rule30RightPrefixClock.PrefixIsE (Rule30RightProfiles.rightDiag x) (-R+(n:Int)) E) :
    ∀e,e<E → ¬Rule30RightPrefixClock.Period (Rule30RightProfiles.rightDiag x (-R+((n+1:Nat):Int))) (2^e) :=
  actual_no_small_clock_drop graph (by decide +kernel) (by decide +kernel) root_a root_b graph_valid x R hx n E hE clock
end Ruliology.CellularAutomata.Rule30ProfileGraphCases
