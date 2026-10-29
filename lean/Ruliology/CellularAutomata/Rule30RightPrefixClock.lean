module
public import Ruliology.CellularAutomata.Rule30RightProfiles

/-! Prefix clocks for arbitrary right-bounded seeds. Individual diagonal periods
may drop. Only the period of the whole prefix is used here. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30RightPrefixClock
open Rule30RightProfiles
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

def Period (f : Nat → Bool) (p : Nat) : Prop := ∀ t, f (t+p)=f t
def PrefixPer (D : Int → Nat → Bool) (j : Int) (p : Nat) : Prop :=
  ∀ i, i≤j → Period (D i) p
def Recurrence (D : Int → Nat → Bool) : Prop :=
  ∀ j t, D j (t+1)=xor (D j t) (D (j-1) t || D (j-2) t)
def PrefixIsE (D : Int → Nat → Bool) (j : Int) (e : Nat) : Prop :=
  PrefixPer D j (2^e) ∧ ∀ k, k<e → ¬PrefixPer D j (2^k)

theorem prefix_mono {D j k p} (h : PrefixPer D j p) (hk : k≤j) : PrefixPer D k p :=
  fun i hi => h i (by omega)

theorem prefix_extend {D j p} (h : PrefixPer D j p) (next : Period (D (j+1)) p) :
    PrefixPer D (j+1) p := by
  intro i hi
  by_cases old : i≤j
  · exact h i old
  · have : i=j+1 := by omega
    subst i
    exact next

theorem prefix_double {D j p} (h : PrefixPer D j p) : PrefixPer D j (2*p) := by
  intro i hi t
  rw [show t+2*p=(t+p)+p by omega,h i hi,h i hi]

theorem forcing_period {D j p} (h : PrefixPer D j p) :
    ∀ t, (D j (t+p) || D (j-1) (t+p))=(D j t || D (j-1) t) := by
  intro t
  rw [h j (by omega),h (j-1) (by omega)]

theorem next_shift {D j p} (step : Recurrence D) (h : PrefixPer D j p) (t : Nat) :
    D (j+1) (t+p)=xor (D (j+1) t) (xr (fun s => D j s || D (j-1) s) p) := by
  apply running_shift (D:=D (j+1)) (g:=fun s => D j s || D (j-1) s)
  · intro s
    simpa only [show j+1-1=j by omega,show j+1-2=j-1 by omega] using step (j+1) s
  · exact forcing_period h

theorem prefix_step {D j p} (step : Recurrence D) (h : PrefixPer D j p) :
    PrefixPer D (j+1) (2*p) := by
  apply prefix_extend (prefix_double h)
  intro t
  rw [show t+2*p=(t+p)+p by omega,next_shift step h,next_shift step h]
  cases D (j+1) t <;> cases xr (fun s => D j s || D (j-1) s) p <;> rfl

theorem growth_antiperiod {D j p} (step : Recurrence D) (h : PrefixPer D j p)
    (growth : ¬PrefixPer D (j+1) p) : ∀ t, D (j+1) (t+p)=!D (j+1) t := by
  have parity : xr (fun s => D j s || D (j-1) s) p=true := by
    cases eq : xr (fun s => D j s || D (j-1) s) p
    · exfalso
      apply growth
      apply prefix_extend h
      intro t
      rw [next_shift step h,eq,Bool.xor_false]
    · rfl
  intro t
  rw [next_shift step h,parity]
  cases D (j+1) t <;> rfl

theorem exponent_step {D j e f} (step : Recurrence D)
    (a : PrefixIsE D j e) (b : PrefixIsE D (j+1) f) : f=e ∨ f=e+1 := by
  have low : e≤f := by
    by_cases hh : e≤f
    · exact hh
    · exact False.elim (a.2 f (by omega) (prefix_mono b.1 (by omega)))
  have high : f≤e+1 := by
    by_cases hh : f≤e+1
    · exact hh
    · have hp := prefix_step step a.1
      have power : 2*2^e=2^(e+1) := (Nat.mul_comm _ _).trans (Nat.pow_succ 2 e).symm
      rw [power] at hp
      exact False.elim (b.2 (e+1) (by omega) hp)
  omega

/-- No `11011` prefix-clock word once the base exponent is at least2.
The middle plateau is explicit; no individual-period nonloss is assumed. -/
theorem no_11011 {D : Int → Nat → Bool} (step : Recurrence D)
    (j : Int) (E : Nat) (hE : 2≤E)
    (h0 : PrefixIsE D j E) (h1 : PrefixIsE D (j+1) (E+1))
    (h2 : PrefixIsE D (j+2) (E+2)) (h3 : PrefixIsE D (j+3) (E+2))
    (h4 : PrefixIsE D (j+4) (E+3)) : ¬PrefixIsE D (j+5) (E+4) := by
  let q := 2^(E+1)
  have double : 2*q=2^(E+2) := by
    calc
      2*q=2^(E+1)*2 := Nat.mul_comm _ _
      _ = 2^((E+1)+1) := (Nat.pow_succ 2 (E+1)).symm
      _ = 2^(E+2) := rfl
  have four : 4*q=2^(E+3) := by
    have power : 2^(E+3)=2^(E+1)*4 := by
      calc
        2^(E+3)=2^((E+1)+2) := rfl
        _ = 2^(E+1)*2^2 := Nat.pow_add 2 (E+1) 2
        _ = 2^(E+1)*4 := rfl
    dsimp [q]
    rw [power,Nat.mul_comm]
  have half : q/2=2^E := by simp [q,Nat.pow_succ]
  have q8 : q%8=0 := by
    obtain ⟨k,hk⟩ : ∃ k,E=k+2 := ⟨E-2,by omega⟩
    dsimp [q]
    rw [hk,show k+2+1=k+3 by omega,Nat.pow_add]
    simp
  have da : ∀ t,D (j+1) (t+q/2)=!D (j+1) t := by
    rw [half]
    exact growth_antiperiod step h0.1 (h1.2 E (by omega))
  have aa : ∀ t,D (j+2) (t+q)=!D (j+2) t := by
    have h := growth_antiperiod step h1.1 (by
      simpa only [show j+1+1=j+2 by omega] using h2.2 (E+1) (by omega))
    simpa only [show j+1+1=j+2 by omega] using h
  have ca : ∀ t,D (j+4) (t+2*q)=!D (j+4) t := by
    rw [double]
    have h := growth_antiperiod step h3.1 (by
      simpa only [show j+3+1=j+4 by omega] using h4.2 (E+2) (by omega))
    simpa only [show j+3+1=j+4 by omega] using h
  have eta := eta_false_of_antiperiod q q8 (D (j+1)) da
  have law := shift_law q (by omega) (D (j+1)) (D (j+2)) (D (j+3))
    (D (j+4)) (D (j+5)) (h1.1 (j+1) (by omega)) aa
    (by rw [double];exact h3.1 (j+3) (by omega)) ca
    (fun t => by simpa only [show j+3-1=j+2 by omega,show j+3-2=j+1 by omega] using step (j+3) t)
    (fun t => by simpa only [show j+5-1=j+4 by omega,show j+5-2=j+3 by omega] using step (j+5) t)
  have per : PrefixPer D (j+5) (2^(E+3)) := by
    have last : Period (D (j+5)) (2^(E+3)) := by
      intro t
      have h := law t
      rw [eta,Bool.xor_false,four] at h
      exact h
    have extended := prefix_extend h4.1 (by
      simpa only [show j+4+1=j+5 by omega] using last)
    simpa only [show j+4+1=j+5 by omega] using extended
  intro h5
  exact h5.2 (E+3) (by omega) per

theorem actual_recurrence (x : Int → Bool) : Recurrence (rightDiag x) := rightDiag_step x

/-- The initial configuration may be arbitrary to the left of its right bound. -/
theorem right_white (x : Int → Bool) (R : Int)
    (hx : ∀ p,R<p → x p=false) :
    ∀ t j,j < -R → rightDiag x j t=false := by
  intro t
  induction t with
  | zero =>
    intro j hj
    change x ((0:Int)-j)=false
    exact hx _ (by omega)
  | succ t ih =>
    intro j hj
    rw [rightDiag_step,ih j hj,ih (j-1) (by omega),ih (j-2) (by omega)]
    rfl

/-- Every finite right-diagonal prefix of a right-bounded seed has a dyadic
period, from time zero. No transient or left-support hypothesis is needed. -/
theorem right_bounded_prefix_power (x : Int → Bool) (R : Int)
    (hx : ∀ p,R<p → x p=false) :
    ∀ n : Nat,PrefixPer (rightDiag x) (-R-1+(n:Int)) (2^n) := by
  intro n
  induction n with
  | zero =>
    intro i hi t
    rw [right_white x R hx _ i (by omega),right_white x R hx _ i (by omega)]
  | succ n ih =>
    have h := prefix_step (actual_recurrence x) ih
    have power : 2*2^n=2^(n+1) := (Nat.mul_comm _ _).trans (Nat.pow_succ 2 n).symm
    rw [power] at h
    simpa only [show -R-1+((n+1:Nat):Int)=(-R-1+(n:Int))+1 by omega] using h

theorem exists_prefix_exponent (x : Int → Bool) (R : Int)
    (hx : ∀ p,R<p → x p=false) (j : Int) :
    ∃ e,PrefixIsE (rightDiag x) j e := by
  classical
  have ex : ∃ e,PrefixPer (rightDiag x) j (2^e) := by
    let n := (j+R+1).toNat
    exact ⟨n,prefix_mono (right_bounded_prefix_power x R hx n) (by omega)⟩
  have key : ∀ n : Nat,(∃ k,k≤n ∧ PrefixPer (rightDiag x) j (2^k)) →
      ∃ e,PrefixIsE (rightDiag x) j e := by
    intro n
    induction n with
    | zero =>
      rintro ⟨k,hk,hp⟩
      have hzero : k=0 := by omega
      subst k
      exact ⟨0,hp,fun l hl => False.elim (by omega)⟩
    | succ n ih =>
      intro bounded
      by_cases smaller : ∃ k,k≤n ∧ PrefixPer (rightDiag x) j (2^k)
      · exact ih smaller
      · obtain ⟨k,hk,hp⟩ := bounded
        have eqk : k=n+1 := by
          by_cases old : k≤n
          · exact False.elim (smaller ⟨k,old,hp⟩)
          · omega
        subst k
        exact ⟨n+1,hp,fun l hl pl => smaller ⟨l,by omega,pl⟩⟩
  obtain ⟨n,hp⟩ := ex
  exact key n ⟨n,by omega,hp⟩

theorem actual_no_11011 (x : Int → Bool) (j : Int) (E : Nat) (hE : 2≤E)
    (h0 : PrefixIsE (rightDiag x) j E) (h1 : PrefixIsE (rightDiag x) (j+1) (E+1))
    (h2 : PrefixIsE (rightDiag x) (j+2) (E+2)) (h3 : PrefixIsE (rightDiag x) (j+3) (E+2))
    (h4 : PrefixIsE (rightDiag x) (j+4) (E+3)) :
    ¬PrefixIsE (rightDiag x) (j+5) (E+4) :=
  no_11011 (actual_recurrence x) j E hE h0 h1 h2 h3 h4

end Ruliology.CellularAutomata.Rule30RightPrefixClock
