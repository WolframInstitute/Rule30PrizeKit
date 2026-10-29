module
public import Ruliology.CellularAutomata.Rule30Certificates.ProfileClockRank32

/-! A genuinely non-period-two right diagonal forces the whole-prefix clock
to at least64 within14 further diagonals. Global period32 therefore collapses
to period2. Applies at every depth to any right-bounded initial configuration. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30ProfileClockEscape
open Rule30RightProfiles Rule30RightPrefixClock Rule30RightPrefixBound Rule30ProfileGraph
theorem no_period32_extension (x : Int → Bool) (R : Int)
    (hx : ∀p,R<p → x p=false) (n : Nat)
    (bad : ¬Period (rightDiag x (-R+(n:Int))) 2) :
    ¬PrefixPer (rightDiag x) (-R+((n+14:Nat):Int)) 32 :=
  actual_escape Rule30ProfileGraphCases.graph (by decide +kernel) (by decide +kernel)
    Rule30ProfileGraphCases.root_a Rule30ProfileGraphCases.root_b
    Rule30ProfileGraphCases.graph_valid nodeRank 13 rank_valid x R hx n bad

/-- A genuinely non-period-two profile forces the whole-prefix clock to64
within fourteen more spatial diagonals, uniformly over all right-bounded seeds. -/
theorem nonperiod_two_forces_clock64 (x : Int → Bool) (R : Int)
    (hx : ∀p,R<p → x p=false) (n : Nat)
    (bad : ¬Period (rightDiag x (-R+(n:Int))) 2) :
    6≤prefixExponent x R hx (n+14) := by
  by_cases high : 6≤prefixExponent x R hx (n+14)
  · exact high
  · have low : prefixExponent x R hx (n+14)≤5 := by omega
    have hp := prefix_pow_mono (prefixExponent_spec x R hx (n+14)).1 low
    exact False.elim (no_period32_extension x R hx n bad hp)

theorem small_clock_escape (x : Int → Bool) (R : Int)
    (hx : ∀p,R<p → x p=false) (n E : Nat) (hlo : 2≤E) (hhi : E≤5)
    (clock : PrefixIsE (rightDiag x) (-R+(n:Int)) E) :
    6≤prefixExponent x R hx (n+14) := by
  have bad := Rule30ProfileGraphCases.actual_small_clock_minimal x R hx n E hhi clock 1 (by omega)
  exact nonperiod_two_forces_clock64 x R hx n bad

/-- A whole right-diagonal array with global period32 already has period2.
This is a bounded-clock classification, not an assertion for every dyadic clock. -/
theorem global_period32_forces_period2 (x : Int → Bool) (R : Int)
    (hx : ∀p,R<p → x p=false)
    (global : ∀n:Nat,PrefixPer (rightDiag x) (-R+(n:Int)) 32) :
    ∀n:Nat,Period (rightDiag x (-R+(n:Int))) 2 := by
  intro n
  by_cases hp : Period (rightDiag x (-R+(n:Int))) 2
  · exact hp
  · exact False.elim (no_period32_extension x R hx n hp (global (n+14)))

end Ruliology.CellularAutomata.Rule30ProfileClockEscape
