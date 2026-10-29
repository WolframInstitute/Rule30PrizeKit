module
public import Ruliology.CellularAutomata.Rule30RightPrefixBound
public import Ruliology.CellularAutomata.Rule30FiniteConfigs

/-! A finite left edge forces prefix periods to grow. This uses the official
moving-edge theorem, and does not assume nonloss of individual diagonal periods.
It complements the generic prefix upper bound; it is not a Prize solution. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30PrefixClockGrowth
open Rule30RightProfiles Rule30RightPrefixClock Rule30RightPrefixBound
open Rule30Realization Rule30RecordCharge
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

/-- At time p, diagonal -L+2p meets the leftmost black cell. At time zero
the same diagonal is strictly left of the seed. It cannot have period p. -/
theorem edge_witness (x : Int → Bool) (L : Int)
    (hL : x L=true) (hleft : ∀i,i<L → x i=false)
    (p : Nat) (hp : 0<p) : ¬Period (rightDiag x (-L+2*(p:Int))) p := by
  intro per
  have h := per 0
  have black := Rule30FiniteConfigs.evol_left_edge hL hleft p
  have white := hleft (L-2*(p:Int)) (by omega)
  have index : (p:Int)-(-L+2*(p:Int))=L-(p:Int) := by omega
  have index0 : (0:Int)-(-L+2*(p:Int))=L-2*(p:Int) := by omega
  simp only [rightDiag,Nat.zero_add,Int.ofNat_zero,index,index0] at h
  rw [black,show evol x 0 (L-2*(p:Int))=x (L-2*(p:Int)) from rfl,white] at h
  exact Bool.noConfusion h

theorem prefix_period_edge_bound (x : Int → Bool) (R L : Int)
    (hL : x L=true) (hleft : ∀i,i<L → x i=false)
    (n p : Nat) (hp : 0<p)
    (per : PrefixPer (rightDiag x) (-R+(n:Int)) p) :
    (n:Int)<R-L+2*(p:Int) := by
  by_cases hn : (n:Int)<R-L+2*(p:Int)
  · exact hn
  · exact False.elim (edge_witness x L hL hleft p hp
      (per (-L+2*(p:Int)) (by omega)))

/-- Explicit lower bound for the least whole-prefix exponent of any seed with
both a white right side and a genuine finite left edge. -/
theorem prefix_exponent_lower (x : Int → Bool) (R L : Int)
    (hright : ∀i,R<i → x i=false) (hL : x L=true)
    (hleft : ∀i,i<L → x i=false) (n e : Nat)
    (hn : (R-L).toNat+2*2^e ≤ n) :
    e < prefixExponent x R hright n := by
  have hLR : L≤R := by
    by_cases h : L≤R
    · exact h
    · have white := hright L (by omega)
      rw [hL] at white
      exact False.elim (Bool.noConfusion white)
  by_cases he : e < prefixExponent x R hright n
  · exact he
  · have per := prefix_pow_mono (prefixExponent_spec x R hright n).1 (by omega : prefixExponent x R hright n≤e)
    have bound := prefix_period_edge_bound x R L hL hleft n (2^e) (Nat.two_pow_pos e) per
    have castWidth : ((R-L).toNat:Int)=R-L := Int.toNat_of_nonneg (by omega)
    have castP : ((2*2^e:Nat):Int)=2*((2^e:Nat):Int) := by omega
    omega

theorem prefix_exponents_unbounded (x : Int → Bool) (R L : Int)
    (hright : ∀i,R<i → x i=false) (hL : x L=true)
    (hleft : ∀i,i<L → x i=false) (e : Nat) :
    ∃N,∀n,N≤n → e < prefixExponent x R hright n := by
  exact ⟨(R-L).toNat+2*2^e,fun n hn => prefix_exponent_lower x R L hright hL hleft n e hn⟩

/-- A two-sided bound on actual finite-seed prefix clocks. -/
theorem two_sided_prefix_clock (x : Int → Bool) (R L : Int)
    (hright : ∀i,R<i → x i=false) (hL : x L=true)
    (hleft : ∀i,i<L → x i=false) (n : Nat) :
    prefixExponent x R hright n ≤ B n ∧
    (n:Int)<R-L+2*((2^prefixExponent x R hright n:Nat):Int) := by
  exact ⟨right_bounded_exponent_half x R hright n,
    prefix_period_edge_bound x R L hL hleft n _ (Nat.two_pow_pos _) (prefixExponent_spec x R hright n).1⟩

end Ruliology.CellularAutomata.Rule30PrefixClockGrowth
