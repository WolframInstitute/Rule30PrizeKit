module

public import Ruliology.CellularAutomata.Rule30MarkedGaps
public import Ruliology.CellularAutomata.Rule30LightCone
public import Ruliology.CellularAutomata.Rule30FrontLaw
public import Ruliology.CellularAutomata.Rule30LeftAntiPeriod

/-!
# Arrival colors of white gaps born from solid black intervals

At the birth row, a pulse at position k has a white interval to its
left and l white sites to its right. After k ticks the pulse reaches
the center beside a white gap of length l. The center l ticks later
reads the singleton's left diagonal D l at time k+l. Only the indicated
finite interval at birth is required, and every such geometry occurs
one tick after a single solid interval. Settled white, black and
anti-periodic diagonals give three distinct behaviors at unbounded widths.
-/

@[expose] public section
namespace Ruliology.CellularAutomata.Rule30GapBirthArrival
open Rule30Jen Rule30Realization Rule30Diagonals Rule30LightCone
open Rule30ZeroBoundaryBarriers (evol_shift_all evol_restart)

def pulse (j p : Int) : Bool := decide (p = j)

theorem pulse_evol (j : Int) (t : Nat) (p : Int) :
    evol (pulse j) t p = cell t (p-j) := by
  have h := evol_shift_all (x:=seed) (x':=pulse j) (d:=j)
    (fun q => by simp [pulse, seed, show q+j=j ↔ q=0 by omega]) t (p-j)
  simpa [evol_seed] using h

/-- The positions outside this finite interval are free. -/
def BirthWindow (x : Int → Bool) (l k : Nat) : Prop :=
  x (-(l:Int)-k-1)=true ∧ ∀ p : Int, -(l:Int)-k ≤ p → p ≤ (l:Int)+k →
    x p = pulse k p

/-- Prescribing the entire past center for H ticks and the initial right
half leaves the terminal strictly negative half arbitrary. Its positive
half must, and does, coincide with the driven right half. -/
theorem prescribe_terminal_left (H : Nat) (R Y : Int → Bool) (w : Nat → Bool) :
    ∃ x : Int → Bool, (∀ p : Int, 1≤p → x p=R p) ∧
      (∀ t, t≤H → evol x t 0=w t) ∧
      (∀ p : Int, p<0 → evol x H p=Y p) ∧
      (∀ p : Int, 1≤p → evol x H p=rh R w H p) := by
  let y : Int → Bool := fun p => if 1≤p then rh R w H p else if p=0 then w H else Y p
  let c := fun t => if t<H then w t else evol y (t-H) 0
  let x := conf R c
  have obs := (realize R c).2
  have past (t : Nat) (ht : t≤H) : evol x t 0=w t := by
    rw [obs]
    by_cases lt : t<H
    · simp [c,lt]
    · have e : t=H := by omega
      simp [e,c,evol,y]
  have right (p : Int) (hp : 1≤p) : evol x H p=rh R w H p := by
    rw [show evol x H p=rh R c H p by simp [x,evol_conf,hp]]
    exact rh_congr R H (fun t ht => by simp [c,ht]) p
  have all : evol x H = y := by
    apply unique
    · intro p hp
      simpa [y,hp] using right p hp
    · intro t
      rw [evol_restart,obs]
      simp [c,show ¬ H+t<H by omega]
  exact ⟨x,(realize R c).1,past,fun p hp => by simp [all,y,show ¬1≤p by omega,show p≠0 by omega],right⟩

/-- The finite-window version preserves every cell from -W rightwards
at time H and requires no initial black to the left of -(W+H). -/
theorem finite_prescribed_past (H W : Nat) (R Y : Int → Bool) (w : Nat → Bool) :
    ∃ x : Int → Bool, (∀ p : Int, p < -((W+H:Nat):Int) → x p=false) ∧
      (∀ p : Int, 1≤p → x p=R p) ∧ (∀ t, t≤H → evol x t 0=w t) ∧
      (∀ p : Int, -(W:Int)≤p → p<0 → evol x H p=Y p) ∧
      (∀ p : Int, 1≤p → evol x H p=rh R w H p) := by
  obtain ⟨z,initial,past,left,right⟩ := prescribe_terminal_left H R Y w
  let x := fun p : Int => if p < -((W+H:Nat):Int) then false else z p
  have copy (t : Nat) (p : Int) (h : -((W+H:Nat):Int) ≤ p-t) : evol x t p=evol z t p :=
    evol_window (fun q lo _ => ite_eq_right (by omega))
  exact ⟨x,fun p hp => ite_eq_left hp,
    fun p hp => (ite_eq_right (show ¬p < -((W+H:Nat):Int) by omega)).trans (initial p hp),
    fun t ht => (copy t 0 (by omega)).trans (past t ht),
    fun p lo hi => (copy H p (by omega)).trans (left p hi),
    fun p hp => (copy H p (by omega)).trans (right p hp)⟩

theorem gap_at_launch {x l k} (w : BirthWindow x l k) :
    evol x k (-(l:Int)-1)=true ∧
    (∀ p : Int, -(l:Int)≤p → p<0 → evol x k p=false) ∧ evol x k 0=true := by
  have cap : evol x k (-(l:Int)-1) = evol (pulse (-(l:Int)-k-1)) k (-(l:Int)-1) := by
    apply evol_window
    intro q lo hi
    by_cases h : q = -(l:Int)-k-1
    · simpa [h,pulse] using w.1
    · rw [w.2 q (by omega) (by omega)]
      simp [pulse,h,show q ≠ (k:Int) by omega]
  rw [pulse_evol] at cap
  have ed := R_zero k
  simp only [R, Int.ofNat_zero, Int.sub_zero] at ed
  have inside (p : Int) (lo : -(l:Int) ≤ p) (hi : p ≤ 0) :
      evol x k p = cell k (p-k) := by
    rw [← pulse_evol]
    exact evol_window (fun q h h' => w.2 q (by omega) (by omega))
  refine ⟨cap.trans ?_, fun p lo hi => (inside p lo (by omega)).trans (cell_eq_false_of_lt _ _ (by omega)), ?_⟩
  · simpa only [show -(l:Int)-1-(-(l:Int)-k-1) = (k:Int) by omega] using ed
  · rw [inside 0 (by omega) (by omega), Int.zero_sub, cell_left_edge]

theorem arrival_eq_diagonal {x l k} (w : BirthWindow x l k) :
    evol x (k+l) 0 = D l (k+l) := by
  have h : evol x (k+l) 0 = evol (pulse k) (k+l) 0 :=
    evol_window (fun q lo hi => w.2 q (by omega) (by omega))
  rw [h,pulse_evol]
  unfold D
  congr 1
  omega

def bar (l k : Nat) (p : Int) : Bool := decide (-(l:Int)-k-1 ≤ p ∧ p < (k:Int))

theorem bar_birth (l k : Nat) : BirthWindow (evol (bar l k) 1) l k := by
  constructor
  · simp [evol,rule,bar,show ¬ (-(l:Int)-k-1 ≤ -(l:Int)-k-1-1) by omega,
      show -(l:Int)-k-1 < (k:Int) by omega]
  · intro p lo hi
    change rule (bar l k (p-1)) (bar l k p) (bar l k (p+1)) = pulse k p
    by_cases h : p=(k:Int)
    · subst p
      simp [bar,pulse,rule,show -(l:Int)-k-1 ≤ (k:Int)-1 by omega,
        show (k:Int)-1 < k by omega,show ¬ ((k:Int)+1 < k) by omega]
    · by_cases h' : p<(k:Int)
      · simp [bar,pulse,rule,h,h',show -(l:Int)-k-1≤p-1 by omega,
          show p-1 < (k:Int) by omega,show -(l:Int)-k-1 ≤ p by omega]
      · simp [bar,pulse,rule,h,h',show ¬ (p-1 < (k:Int)) by omega,
          show ¬ (p+1 < (k:Int)) by omega]

def readBar (l k : Nat) : Bool := evol (bar l k) (1+(k+l)) 0

theorem readBar_eq (l k : Nat) : readBar l k = D l (k+l) := by
  unfold readBar
  rw [← evol_restart]
  exact arrival_eq_diagonal (bar_birth l k)

/-- Every falling center edge supplies a gap width within two of its age
at which both colors already occur with a delay of at most two from birth. -/
theorem short_launch_contrast (t : Nat) (on : cell t 0=true) (off : cell (t+1) 0=false) :
    ∃ l, t≤l ∧ l≤t+2 ∧ ∃ k, 1≤k ∧ k≤2 ∧ readBar l k ≠ readBar l 0 := by
  apply Classical.byContradiction
  intro nope
  have eq (l k : Nat) (lo : t≤l) (hi : l≤t+2) (kl : 1≤k) (kh : k≤2) :
      cell (k+l) (-(k:Int)) = cell l 0 := by
    have h : readBar l k = readBar l 0 := Classical.byContradiction
      (fun hn => nope ⟨l,lo,hi,k,kl,kh,hn⟩)
    rw [readBar_eq,readBar_eq] at h
    simpa [D,show (l:Int)-((k:Int)+(l:Int)) = -(k:Int) by omega] using h
  have a := eq t 2 (by omega) (by omega) (by decide) (by decide)
  have b := eq (t+1) 1 (by omega) (by omega) (by decide) (by decide)
  have c := eq (t+2) 1 (by omega) (by omega) (by decide) (by decide)
  rw [show 2+t=t+2 by omega,on] at a
  rw [show 1+(t+1)=t+2 by omega,off] at b
  rw [show 1+(t+2)=(t+2)+1 by omega] at c
  change rule (cell (t+2) (-2)) (cell (t+2) (-1)) (cell (t+2) 0) = cell (t+2) 0 at c
  change cell (t+2) (-2) = true at a
  change cell (t+2) (-1) = false at b
  rw [a,b] at c
  cases h : cell (t+2) 0 <;> simp [rule,h] at c

theorem short_launch_unbounded (N : Nat) :
    ∃ l, N≤l ∧ ∃ k, 1≤k ∧ k≤2 ∧ readBar l k ≠ readBar l 0 := by
  have falls : ∃ t, N≤t ∧ cell t 0=true ∧ cell (t+1) 0=false := by
    apply Classical.byContradiction
    intro no
    apply Rule30Prize.center_not_eventually_constant
    by_cases ex : ∃ s, N≤s ∧ cell s 0=true
    · obtain ⟨s,hs,black⟩ := ex
      refine ⟨s,true,fun t ht => ?_⟩
      obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le ht
      induction d with
      | zero => exact black
      | succ d ih =>
        cases hh : cell (s+d+1) 0 with
        | true => exact hh
        | false => exact (no ⟨s+d,by omega,ih (by omega),hh⟩).elim
    · refine ⟨N,false,fun t ht => ?_⟩
      cases h : cell t 0 with
      | false => exact h
      | true => exact (ex ⟨t,ht,h⟩).elim
  obtain ⟨t,late,on,off⟩ := falls
  obtain ⟨l,lo,_,h⟩ := short_launch_contrast t on off
  exact ⟨l,Nat.le_trans late lo,h⟩

theorem unbounded_white (N : Nat) : ∃ l>N, ∃ K, ∀ k≥K, readBar l k=false := by
  obtain ⟨l,hl,T,h⟩ := Rule30LeftUnbounded.D_infinitely_many_white N
  exact ⟨l,hl,T,fun k hk => (readBar_eq l k).trans (h _ (by omega))⟩

theorem unbounded_black (N : Nat) : ∃ l>N, ∃ K, ∀ k≥K, readBar l k=true := by
  obtain ⟨l,hl,T,h⟩ := Rule30LeftUnbounded.D_infinitely_many_black N
  exact ⟨l,hl,T,fun k hk => (readBar_eq l k).trans (h _ (by omega))⟩

private theorem band_period {d m : Nat} (le : d≤m) (q : Nat) :
    Rule30LeftReset.EvPer (D d) (q*2^m) := by
  apply Rule30LeftUnbounded.EvPer.of_dvd
    (show Rule30LeftReset.EvPer (D d) (2^d) from
      ⟨Rule30FrontLaw.frontBound d,Rule30FrontLaw.D_periodic_from_frontBound d⟩)
  exact Nat.dvd_trans (Nat.pow_dvd_pow 2 le) (Nat.dvd_mul_left _ _)

private theorem late_failure (N H : Nat) (hp : 0<H) :
    ∃ l>N, ¬Rule30LeftReset.EvPer (D l) H := by
  obtain ⟨l,_,bad⟩ := Rule30LeftUnbounded.D_period_unbounded (H*2^N)
    (Nat.mul_pos hp (Nat.two_pow_pos _))
  refine ⟨l,?_,fun per => bad (Rule30LeftUnbounded.EvPer.of_dvd per (Nat.dvd_mul_right _ _))⟩
  exact Nat.lt_of_not_ge (fun le => bad (band_period le H))

private theorem view {l k m a : Nat} {p : Int} (big : 2*m≤l) (age : m≤k)
    (later : a≤2*m) (lo : -(m:Int)≤p) (hi : p≤m) :
    evol (bar l k) (1+(k-m+a)) p = cell (k-m+a) (p-k) := by
  rw [← evol_restart, ← pulse_evol]
  exact evol_window (fun q low high => (bar_birth l k).2 q (by omega) (by omega))

/-- Even the whole radius-m, time-radius-m observation around launch,
the gap length and an arbitrary clock phase can agree while the arrivals
differ. The shift H is fixed before the required width and age are given. -/
theorem indistinguishable_launches (m Q : Nat) (qpos : 0<Q) :
    ∃ H, 0<H ∧ Q∣H ∧ ∀ N, ∃ l>N, ∃ k>N, m≤k ∧
      (∀ a : Nat, a≤2*m → ∀ p : Int, -(m:Int)≤p → p≤m →
        evol (bar l k) (1+(k-m+a)) p =
          evol (bar l (k+H)) (1+(k+H-m+a)) p) ∧
      readBar l k ≠ readBar l (k+H) := by
  let H := Q*2^(2*m)
  have hH : 0<H := Nat.mul_pos qpos (Nat.two_pow_pos _)
  obtain ⟨S,_,common⟩ := Rule30LeftUnbounded.common_threshold (2*m)
    (Q:=H) (fun j hj => band_period hj Q)
  refine ⟨H,hH,Nat.dvd_mul_right _ _,fun N => ?_⟩
  obtain ⟨l,hl,bad⟩ := late_failure (N+2*m) H hH
  have ex : ∃ t, S+l+m+N<t ∧ D l (t+H)≠D l t := by
    apply Classical.byContradiction
    intro no
    apply bad
    exact ⟨S+l+m+N+1,fun t ht => Classical.byContradiction
      (fun h => no ⟨t,by omega,h⟩)⟩
  obtain ⟨t,ht,diff⟩ := ex
  let k := t-l
  have kt : k+l=t := by dsimp [k]; omega
  have old : S+m+N<k := by dsimp [k]; omega
  refine ⟨l,by omega,k,by omega,by omega,?_,?_⟩
  · intro a ha p lo hi
    rw [view (by omega) (by omega) ha lo hi,view (by omega) (by omega) ha lo hi]
    by_cases left : p+(a:Int)-(m:Int)<0
    · rw [cell_eq_false_of_lt _ _ (by omega),cell_eq_false_of_lt (k+H-m+a) _ (by omega)]
    · let j := (p+(a:Int)-(m:Int)).toNat
      have jval : (j:Int)=p+(a:Int)-(m:Int) := by dsimp [j]; omega
      have h := common j (by omega) (k-m+a) (by omega)
      unfold D at h
      rw [show k-m+a+H=k+H-m+a by omega,
        show (j:Int)-((k+H-m+a:Nat):Int)=p-(k+H:Nat) by omega,
        show (j:Int)-((k-m+a:Nat):Int)=p-k by omega] at h
      exact h.symm
  · rw [readBar_eq,readBar_eq,kt,show k+H+l=t+H by omega]
    exact Ne.symm diff

theorem unbounded_both (N : Nat) : ∃ l>N, ∃ h : Nat, 0<h ∧
    ∃ K, ∀ k≥K, readBar l (k+h) = !(readBar l k) := by
  obtain ⟨l,hl,b,⟨T,ht⟩,_,_⟩ := Rule30LeftAntiPeriod.D_infinitely_many_halfDensity N
  refine ⟨l,hl,2^b,Nat.two_pow_pos _,T,fun k hk => ?_⟩
  rw [readBar_eq,readBar_eq,show k+2^b+l = k+l+2^b by omega]
  exact ht _ (by omega)

end Ruliology.CellularAutomata.Rule30GapBirthArrival
