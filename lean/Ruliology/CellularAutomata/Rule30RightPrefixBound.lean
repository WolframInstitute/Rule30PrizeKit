module
public import Ruliology.CellularAutomata.Rule30RightPrefixClock
public import Ruliology.CellularAutomata.Rule30DifferenceOrder

/-! Generalizing the official single-cell half-rate proof to prefix clocks.
The difference-order and record-charge arguments are reused from the official
Rule30RightPeriods module, with prefix periods supplying the hypotheses. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30RightPrefixBound
open Rule30RightPrefixClock Rule30RightProfiles Rule30DifferenceOrder Rule30RecordCharge
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

structure Clock where
  profile : Nat → Nat → Bool
  exponent : Nat → Nat
  exponent_zero : exponent 0=0
  exponent_succ_cases : ∀ j,exponent (j+1)=exponent j ∨ exponent (j+1)=exponent j+1
  period : ∀ j t,profile j (t+2^exponent j)=profile j t
  antiperiod : ∀ {j},exponent (j+1)=exponent j+1 →
    ∀ t,profile (j+1) (t+2^exponent j)=!profile (j+1) t
  recurrence : ∀ j t,profile (j+2) (t+1)=xor (profile (j+2) t) (profile (j+1) t || profile j t)

section Bound
variable (C : Clock)


/-- The resource at pair `i`: the difference order of `C.profile (2 i)` over one period. -/
noncomputable def pairResource (i : Nat) : Nat := order (C.profile (2 * i)) (2 ^ C.exponent (2 * i))

theorem pair_step (i t : Nat) :
    C.profile (2 * i + 1 + 1) (t + 1) = xor (C.profile (2 * i + 1 + 1) t) (C.profile (2 * i + 1) t || C.profile (2 * i) t) :=
  C.recurrence (2 * i) t

/-- The pairs of diagonals form a record-charge path with `nu = 0`. -/
noncomputable def pairPath : Path 0 where
  weight i := C.exponent (2 * i + 1 + 1) - C.exponent (2 * i)
  exponent i := C.exponent (2 * i)
  resource := pairResource C
  exponent_zero := C.exponent_zero
  exponent_step i := by
    have h0 := C.exponent_succ_cases (2 * i)
    have h1 := C.exponent_succ_cases (2 * i + 1)
    show C.exponent (2 * (i + 1)) = _
    rw [show 2 * (i + 1) = 2 * i + 1 + 1 by omega]
    omega
  weight_le_two i := by
    have h0 := C.exponent_succ_cases (2 * i)
    have h1 := C.exponent_succ_cases (2 * i + 1)
    show C.exponent (2 * i + 1 + 1) - C.exponent (2 * i) ≤ 2
    omega
  reset_before i hw := by
    have h0 := C.exponent_succ_cases (2 * i)
    have h1 := C.exponent_succ_cases (2 * i + 1)
    change C.exponent (2 * i + 1 + 1) - C.exponent (2 * i) = 2 at hw
    have e0 : C.exponent (2 * i + 1) = C.exponent (2 * i) + 1 := by omega
    have e1 : C.exponent (2 * i + 1 + 1) = C.exponent (2 * i + 1) + 1 := by omega
    have hanti : ∀ t, C.profile (2 * i + 1 + 1) (t + 2 * 2 ^ C.exponent (2 * i)) = !C.profile (2 * i + 1 + 1) t := by
      intro t
      have := C.antiperiod e1 t
      rwa [e0, two_pow_succ'] at this
    exact order_reset_before (C.period (2 * i)) (C.antiperiod e0) (pair_step C i) hanti
  reset_after i hw := by
    have h0 := C.exponent_succ_cases (2 * i)
    have h1 := C.exponent_succ_cases (2 * i + 1)
    change C.exponent (2 * i + 1 + 1) - C.exponent (2 * i) = 2 at hw
    have e0 : C.exponent (2 * i + 1) = C.exponent (2 * i) + 1 := by omega
    have e1 : C.exponent (2 * i + 1 + 1) = C.exponent (2 * i + 1) + 1 := by omega
    have hanti : ∀ t, C.profile (2 * i + 1 + 1) (t + 2 ^ (C.exponent (2 * i) + 1)) =
        !C.profile (2 * i + 1 + 1) t := by
      intro t
      have := C.antiperiod e1 t
      rwa [e0] at this
    have hord := order_of_antiperiod hanti
    show order (C.profile (2 * (i + 1))) (2 ^ C.exponent (2 * (i + 1))) + 1 =
      2 ^ (0 + C.exponent (2 * (i + 1)) - 1)
    rw [show 2 * (i + 1) = 2 * i + 1 + 1 by omega, e1, e0, two_pow_succ' (C.exponent (2 * i) + 1),
      hord, show 0 + (C.exponent (2 * i) + 1 + 1) - 1 = C.exponent (2 * i) + 1 by omega]
    have := Nat.one_le_two_pow (n := C.exponent (2 * i) + 1)
    omega
  countdown i hw := by
    have h0 := C.exponent_succ_cases (2 * i)
    have h1 := C.exponent_succ_cases (2 * i + 1)
    change C.exponent (2 * i + 1 + 1) - C.exponent (2 * i) = 1 at hw
    show pairResource C i ≤ order (C.profile (2 * (i + 1))) (2 ^ C.exponent (2 * (i + 1))) + 1
    rw [show 2 * (i + 1) = 2 * i + 1 + 1 by omega]
    unfold pairResource
    rcases h0 with e0 | e0
    · -- the low diagonal keeps its period: the high diagonal is complemented by `M`
      have e1 : C.exponent (2 * i + 1 + 1) = C.exponent (2 * i) + 1 := by omega
      have hanti : ∀ t, C.profile (2 * i + 1 + 1) (t + 2 ^ C.exponent (2 * i)) = !C.profile (2 * i + 1 + 1) t := by
        intro t
        have := C.antiperiod (j := 2 * i + 1) (by omega) t
        rwa [e0] at this
      rw [e1, two_pow_succ', order_of_antiperiod hanti]
      have := order_le (C.profile (2 * i)) (2 ^ C.exponent (2 * i))
      omega
    · -- the low diagonal is complemented by `M`: countdown
      have e1 : C.exponent (2 * i + 1 + 1) = C.exponent (2 * i) + 1 := by omega
      rw [e1, two_pow_succ']
      exact order_countdown (C.period (2 * i)) (C.antiperiod e0) (pair_step C i)

/-- `e_{2d} ≤ d + Q 0 d`. -/
theorem exponent_two_mul_le (d : Nat) : C.exponent (2 * d) ≤ d + Q 0 d :=
  exponent_le_Q (pairPath C) d

theorem exponent_le_B (j : Nat) : C.exponent j ≤ B j := by
  unfold B
  obtain ⟨d, rfl | rfl⟩ : ∃ d, j = 2 * d ∨ j = 2 * d + 1 := ⟨j / 2, by omega⟩
  · rw [show (2 * d + 1) / 2 = d by omega, show 2 * d / 2 = d by omega]
    exact exponent_two_mul_le C d
  · rw [show (2 * d + 1 + 1) / 2 = d + 1 by omega, show (2 * d + 1) / 2 = d by omega]
    have := exponent_two_mul_le C d
    rcases C.exponent_succ_cases (2 * d) with h | h <;> omega


end Bound

theorem right_boundary_prefix_one (x : Int → Bool) (R : Int)
    (hx : ∀ p,R<p → x p=false) : PrefixPer (rightDiag x) (-R) 1 := by
  intro i hi t
  by_cases outer : i < -R
  · rw [right_white x R hx _ i outer,right_white x R hx _ i outer]
  · have eqi : i= -R := by omega
    subst i
    rw [rightDiag_step,right_white x R hx _ (-R-1) (by omega),
      right_white x R hx _ (-R-2) (by omega)]
    cases rightDiag x (-R) t <;> rfl

noncomputable def prefixExponent (x : Int → Bool) (R : Int)
    (hx : ∀ p,R<p → x p=false) (n : Nat) : Nat :=
  Classical.choose (exists_prefix_exponent x R hx (-R+(n:Int)))

theorem prefixExponent_spec (x : Int → Bool) (R : Int)
    (hx : ∀ p,R<p → x p=false) (n : Nat) :
    PrefixIsE (rightDiag x) (-R+(n:Int)) (prefixExponent x R hx n) :=
  Classical.choose_spec (exists_prefix_exponent x R hx (-R+(n:Int)))

noncomputable def actualClock (x : Int → Bool) (R : Int)
    (hx : ∀ p,R<p → x p=false) : Clock where
  profile n := rightDiag x (-R+(n:Int))
  exponent := prefixExponent x R hx
  exponent_zero := by
    have spec := prefixExponent_spec x R hx 0
    have hp := right_boundary_prefix_one x R hx
    by_cases hz : prefixExponent x R hx 0=0
    · exact hz
    · exact False.elim (spec.2 0 (by omega) (by simpa only [Int.ofNat_zero,Int.add_zero,Nat.pow_zero] using hp))
  exponent_succ_cases n := by
    have old := prefixExponent_spec x R hx n
    have next := prefixExponent_spec x R hx (n+1)
    have index : -R+((n+1:Nat):Int)=(-R+(n:Int))+1 := by omega
    rw [index] at next
    exact exponent_step (actual_recurrence x) old next
  period n := (prefixExponent_spec x R hx n).1 _ (by omega)
  antiperiod := by
    intro n growth
    have old := prefixExponent_spec x R hx n
    have next := prefixExponent_spec x R hx (n+1)
    have index : -R+((n+1:Nat):Int)=(-R+(n:Int))+1 := by omega
    rw [index] at next
    have anti := growth_antiperiod (actual_recurrence x) old.1
      (next.2 (prefixExponent x R hx n) (by omega))
    simpa only [index] using anti
  recurrence n t := by
    have h := rightDiag_step x (-R+((n+2:Nat):Int)) t
    simpa only [show -R+((n+2:Nat):Int)-1=-R+((n+1:Nat):Int) by omega,
      show -R+((n+2:Nat):Int)-2=-R+(n:Int) by omega] using h

theorem right_bounded_exponent_half (x : Int → Bool) (R : Int)
    (hx : ∀ p,R<p → x p=false) (n : Nat) : prefixExponent x R hx n ≤ B n :=
  exponent_le_B (actualClock x R hx) n

/-- Raising a dyadic prefix period preserves periodicity. -/
theorem prefix_pow_mono {D j a b} (h : PrefixPer D j (2^a)) (hab : a≤b) :
    PrefixPer D j (2^b) := by
  have lift : ∀ r,PrefixPer D j (2^(a+r)) := by
    intro r
    induction r with
    | zero => simpa only [Nat.add_zero] using h
    | succ r ih =>
      have hp := prefix_double ih
      have power : 2*2^(a+r)=2^((a+r)+1) := (Nat.mul_comm _ _).trans (Nat.pow_succ 2 (a+r)).symm
      rw [power] at hp
      simpa only [Nat.add_succ] using hp
  have hsum : a+(b-a)=b := by omega
  simpa only [hsum] using lift (b-a)

/-- For every right-bounded initial configuration, the entire prefix through
diagonal n from the right boundary has period 2^B(n). -/
theorem right_bounded_prefix_half (x : Int → Bool) (R : Int)
    (hx : ∀ p,R<p → x p=false) (n : Nat) :
    PrefixPer (rightDiag x) (-R+(n:Int)) (2^B n) :=
  prefix_pow_mono (prefixExponent_spec x R hx n).1 (right_bounded_exponent_half x R hx n)

/-- Literal Rule30 evolution: every diagonal n left of the right boundary
repeats from time zero with the universal half-rate period. -/
theorem evol_right_diagonal_half (x : Int → Bool) (R : Int)
    (hx : ∀ p,R<p → x p=false) (n t : Nat) :
    Rule30Realization.evol x (t+2^B n) (R+((t+2^B n:Nat):Int)-(n:Int)) =
      Rule30Realization.evol x t (R+(t:Int)-(n:Int)) := by
  have h := right_bounded_prefix_half x R hx n (-R+(n:Int)) (by omega) t
  simpa only [rightDiag,
    show ((t+2^B n:Nat):Int)-(-R+(n:Int))=R+((t+2^B n:Nat):Int)-(n:Int) by omega,
    show (t:Int)-(-R+(n:Int))=R+(t:Int)-(n:Int) by omega] using h

end Ruliology.CellularAutomata.Rule30RightPrefixBound
