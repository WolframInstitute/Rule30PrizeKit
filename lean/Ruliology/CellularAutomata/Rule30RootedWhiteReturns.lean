module

public import Ruliology.CellularAutomata.Rule30AgedLeftDiagonals
public import Ruliology.CellularAutomata.Rule30LeftUnbounded

/-! Backward spatial determinism pins a periodic pair to its depth. The white
interface bound counts one temporal word per white, and applies to every
pointed recurrent strip with a black edge. -/
@[expose] public section

namespace Ruliology.CellularAutomata.Rule30RootedWhiteReturns
open Ruliology.CellularAutomata.Rule30AgedLeftDiagonals
open Ruliology.CellularAutomata.Rule30LeftUnbounded (code code_lt code_inj pigeonhole)

abbrev Column := Nat → Bool
abbrev ProfilePair := Column × Column
private def z : Column := fun _ => false
private def sig (d : Nat → Column) : Nat → ProfilePair
  | 0 => (z,z)
  | 1 => (z,d 0)
  | n+2 => (d n,d (n+1))

private def back (v : ProfilePair) : ProfilePair :=
  (fun t => xor (v.2 (t+1)) (v.1 t || v.2 t), v.1)

private theorem back_zero : back (z,z) = (z,z) := rfl

private theorem back_sig {d : Nat → Column} (hd : Recurrence d) (i : Nat) :
    back (sig d (i+1)) = sig d i := by
  apply Prod.ext
  · funext t
    match i with
    | 0 => change xor (d 0 (t+1)) (false || d 0 t) = false
           rw [hd.1]; cases d 0 t <;> rfl
    | 1 => change xor (d 1 (t+1)) (d 0 t || d 1 t) = false
           rw [hd.2.1]; cases d 0 t <;> cases d 1 t <;> rfl
    | n+2 =>
      change xor (d (n+2) (t+1)) (d (n+1) t || d (n+2) t) = d n t
      rw [hd.2.2]; cases d n t <;> cases d (n+1) t <;> cases d (n+2) t <;> rfl
  · cases i with
    | zero => rfl
    | succ i => cases i <;> rfl

private theorem sig_pos {d : Nat → Column} (hd : Recurrence d) (h0 : d 0 0 = true) :
    ∀ n, sig d (n+1) ≠ (z,z) := by
  intro n
  induction n with
  | zero =>
    intro e
    have h := congrArg (fun v : ProfilePair => v.2 0) e
    change d 0 0 = false at h
    rw [h0] at h; contradiction
  | succ n ih =>
    intro h
    apply ih
    rw [← back_sig hd (n+1),h,back_zero]

private theorem distinct {d : Nat → Column} (hd : Recurrence d) (h0 : d 0 0 = true) :
    ∀ i j, i<j → sig d i ≠ sig d j := by
  intro i
  induction i with
  | zero =>
    intro j hj h
    cases j with
    | zero => omega
    | succ j => exact sig_pos hd h0 j h.symm
  | succ i ih =>
    intro j hj h
    cases j with
    | zero => omega
    | succ j => exact ih j (by omega) (by rw [← back_sig hd i, ← back_sig hd j,h])

private theorem period_code {a b : Column} {p : Nat} (hp : 0<p)
    (ha : PeriodFrom a 0 p) (hb : PeriodFrom b 0 p) (hc : code a p = code b p) : a=b := by
  funext t
  have decomp : t%p + (t/p)*p = t := by simpa [Nat.mul_comm] using Nat.mod_add_div t p
  calc a t = a (t%p) := by
         simpa [decomp] using period_mul ha (t/p) (t%p) (Nat.zero_le _)
       _ = b (t%p) := code_inj _ _ _ hc _ (Nat.mod_lt _ hp)
       _ = b t := by simpa [decomp] using (period_mul hb (t/p) (t%p) (Nat.zero_le _)).symm

/-- Distinct white interfaces with a common clock have distinct preceding
words. No physical path can visit infinitely many white interfaces at this clock. -/
theorem rooted_white_count {d : Nat → Column} (hd : Recurrence d) (h0 : d 0 0=true)
    {p : Nat} (hp : 0<p) (n : Nat) (atWheel : Nat → Nat)
    (ordered : ∀ i j, i<j → j<n → atWheel i < atWheel j)
    (white : ∀ i, i<n → ∀ t, d (atWheel i+1) t=false)
    (clock : ∀ i, i<n → PeriodFrom (d (atWheel i)) 0 p) : n ≤ 2^p := by
  apply pigeonhole (2^p) n (fun i => code (d (atWheel i)) p)
  · exact fun i _ => code_lt _ _
  · intro i j hi hj eqcode
    have hpair : sig d (atWheel i+2) = sig d (atWheel j+2) := by
      apply Prod.ext
      · exact period_code hp (clock i hi) (clock j hj) eqcode
      · exact funext (fun t => (white i hi t).trans (white j hj t).symm)
    by_cases lt : i<j
    · have lt' := ordered i j lt hj
      exact False.elim (distinct hd h0 _ _ (by omega) hpair)
    by_cases gt : j<i
    · have gt' := ordered j i gt hi
      exact False.elim (distinct hd h0 _ _ (by omega) hpair.symm)
    omega

private theorem two_code {d : Nat → Column} (hd : Recurrence d) (h0 : d 0 0=true)
    {p : Nat} (hp : 0<p) (m : Nat) (periods : ∀ i, i≤m+1 → PeriodFrom (d i) 0 p) :
    m+1 ≤ 2^p * 2^p := by
  let num := fun i => code (d (i+1)) p + 2^p * code (d i) p
  have base : 0 < 2^p := Nat.two_pow_pos _
  apply pigeonhole (2^p*2^p) (m+1) num
  · intro i _
    have h := code_lt (d i) p
    have h' := code_lt (d (i+1)) p
    have h'' := Nat.mul_le_mul_right (2^p) (show code (d i) p + 1 ≤ 2^p by omega)
    dsimp [num]; rw [Nat.mul_comm (2^p) (code (d i) p)]; rw [Nat.add_mul,Nat.one_mul] at h''; omega
  · intro i j hi hj h
    have high := congrArg (fun v => v / 2^p) h
    have low := congrArg (fun v => v % 2^p) h
    simp [num, Nat.add_mul_div_left _ _ base, Nat.div_eq_of_lt (code_lt _ _),
          Nat.mod_eq_of_lt (code_lt _ _)] at high low
    have e : sig d (i+2) = sig d (j+2) :=
      Prod.ext (period_code hp (periods _ (by omega)) (periods _ (by omega)) high)
               (period_code hp (periods _ (by omega)) (periods _ (by omega)) low)
    by_cases lt : i<j
    · exact False.elim (distinct hd h0 _ _ (by omega) e)
    by_cases gt : j<i
    · exact False.elim (distinct hd h0 _ _ (by omega) e.symm)
    omega

/-- Every black-edged strip eventually leaves any prescribed common clock. -/
theorem escapes_clock {d : Nat → Column} (hd : Recurrence d) (h0 : d 0 0=true)
    {p : Nat} (hp : 0<p) : ∃ j, j ≤ 2^p*2^p+1 ∧ ¬PeriodFrom (d j) 0 p := by
  classical
  apply Classical.byContradiction
  intro h
  have hall : ∀ i, i ≤ 2^p*2^p+1 → PeriodFrom (d i) 0 p := by
    intro i hi
    apply Classical.byContradiction
    intro bad
    exact h ⟨i,hi,bad⟩
  have hbad := two_code hd h0 hp _ hall
  omega

private theorem first_at (pred : Nat → Prop) (n : Nat) (hn : pred n) :
    ∃ m, m ≤ n ∧ pred m ∧ ∀ i, i<m → ¬pred i := by
  classical
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases e : ∃ i, i<n ∧ pred i
    · obtain ⟨i, hin, hi⟩ := e
      obtain ⟨m, hm, hp, hfirst⟩ := ih i hin hi
      exact ⟨m, by omega, hp, hfirst⟩
    · exact ⟨n, by omega, hn, fun i hi h => e ⟨i,hi,h⟩⟩

private theorem white_flip {a x : Column} {p : Nat} (ha : PeriodFrom a 0 p)
    (step : ∀ t, x (t+1) = xor (a t) (x t)) (loss : ¬PeriodFrom x 0 p) :
    ∀ t, x (t+p) = !(x t) := by
  have same : x p ≠ x 0 := by
    intro e
    apply loss
    intro t _
    induction t with
    | zero => simpa using e
    | succ t ih =>
      rw [show t+1+p=(t+p)+1 by omega, step (t+p), step t,ha t (by omega),ih (by omega)]
  intro t
  induction t with
  | zero => cases hp : x p <;> cases h : x 0 <;> simp_all
  | succ t ih =>
    rw [show t+1+p=(t+p)+1 by omega,step (t+p),step t,ha t (by omega),ih]
    cases a t <;> cases x t <;> rfl

/-- Beyond any already settled pointed prefix, the first loss of its common
clock occurs immediately after a permanently white wheel. The next column
is antiperiodic at that clock, at every tick including the marked phase. -/
theorem first_clock_loss {d : Nat → Column} (hd : Recurrence d) (h0 : d 0 0=true)
    (recurrent : ∀ j, ∃ q, 0<q ∧ PeriodFrom (d j) 0 q)
    {p m : Nat} (hp : 0<p) (hm : 1≤m)
    (hprefix : ∀ i, i≤m → PeriodFrom (d i) 0 p) :
    ∃ j, m≤j ∧ j+1 ≤ 2^p*2^p+1 ∧
      (∀ i, i≤j → PeriodFrom (d i) 0 p) ∧
      (∀ t, d j t=false) ∧ (∀ t, d (j+1) (t+p) = !(d (j+1) t)) := by
  classical
  obtain ⟨n, hn, bad⟩ := escapes_clock hd h0 hp
  obtain ⟨k, hkn, hk, first⟩ := first_at (fun i => ¬PeriodFrom (d i) 0 p) n bad
  have good : ∀ i, i<k → PeriodFrom (d i) 0 p := fun i hi => Classical.not_not.mp (first i hi)
  have hmk : m<k := by
    by_cases h : k≤m
    · exact False.elim (hk (hprefix k h))
    · omega
  obtain ⟨i, rfl⟩ : ∃ i, k=i+2 := ⟨k-2, by omega⟩
  have white : ∀ t, d (i+1) t=false := by
    intro t
    cases h : d (i+1) t with
    | false => rfl
    | true =>
      obtain ⟨q,hq,hperiod⟩ := recurrent (i+2)
      exact False.elim (hk (reset_inherits (hd.2.2 i) (good i (by omega))
        (good (i+1) (by omega)) hperiod hq (Nat.zero_le t) h))
  refine ⟨i+1,by omega,by omega,fun j hj => good j (by omega),white,?_⟩
  apply white_flip (good i (by omega)) _ hk
  intro t
  simpa only [white,Bool.false_or] using hd.2.2 i t

/-- A white wheel and a black wheel two places deeper occur beyond any cutoff.
The common-prefix clock hypothesis is satisfied by the pointed cycle systems. -/
theorem unbounded_anchors {d : Nat → Column} (hd : Recurrence d) (h0 : d 0 0=true)
    (clocks : ∀ m, ∃ p, 0<p ∧ ∀ i, i≤m → PeriodFrom (d i) 0 p) (lo : Nat) :
    ∃ j, lo≤j ∧ (∀ t, d j t=false) ∧ (∀ t, d (j+2) t=true) := by
  have recurrent : ∀ j, ∃ p, 0<p ∧ PeriodFrom (d j) 0 p := by
    intro j
    obtain ⟨p,hp,h⟩ := clocks j
    exact ⟨p,hp,h j (by omega)⟩
  obtain ⟨p,hp,hprefix⟩ := clocks (lo+1)
  obtain ⟨j,hj,_,_,hw,anti⟩ := first_clock_loss hd h0 recurrent hp (by omega : 1≤lo+1) hprefix
  have blackTick : ∃ t, d (j+1) t=true := by
    cases h : d (j+1) 0 with
    | true => exact ⟨0,h⟩
    | false => exact ⟨0+p,by rw [anti 0,h]; rfl⟩
  obtain ⟨t,ht⟩ := blackTick
  have latch : ∀ k, d (j+2) (t+1+k)=true := by
    intro k
    induction k with
    | zero => simp [hd.2.2,hw,ht]
    | succ k ih =>
      rw [show t+1+(k+1)=(t+1+k)+1 by omega,hd.2.2,hw,ih]; simp
  obtain ⟨q,hq,hper⟩ := recurrent (j+2)
  refine ⟨j,by omega,hw,?_⟩
  intro u
  have le : t+1 ≤ (t+1)*q := by
    simpa using Nat.mul_le_mul_left (t+1) (show 1≤q by omega)
  have e := latch (u+(t+1)*q-(t+1))
  rw [show t+1+(u+(t+1)*q-(t+1))=u+(t+1)*q by omega, period_mul hper _ u (by omega)] at e
  exact e

end Ruliology.CellularAutomata.Rule30RootedWhiteReturns
