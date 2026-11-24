module

public import Ruliology.CellularAutomata.Rule30MarkedGaps
public import Ruliology.CellularAutomata.Rule30LightCone
public import Ruliology.CellularAutomata.Rule30Window
public import Ruliology.CellularAutomata.Rule30PeriodTwoLadder
public import Ruliology.CellularAutomata.Rule30DrivenLeftWindows

/-!
# Physical and externally driven tests for delayed restart failures

The five center readings 11000 already exclude a completely white initial
left half. On the singleton the black-only observer can nevertheless take
35 ticks to fail. A different sample really has a finite white-left
realization through offset 18. Initial edits beyond a failed cone can
prolong the black-only delay on other finite seeds.

A separate sufficient condition for Problem 1 keeps a black at the
virtual center and supplies a right input from other actual center
excerpts. Under an eventual center period the driven-left window theorem
bounds the match, uniformly in those excerpts and their Boolean readout.
-/

@[expose] public section
namespace Ruliology.CellularAutomata.Rule30RestartVisibility
open Ruliology.CellularAutomata
open Rule30Jen Rule30Realization Rule30LightCone Rule30DrivenLeft Rule30MarkedGaps

abbrev trace (x : Int → Bool) (t : Nat) := evol x t 0
private abbrev read (c : Nat → Bool) (t : Nat) := L c (fun _ => false) t (-1)

private theorem driven_prefix {c v : Nat → Bool} {initial : Int → Bool} (t : Nat) (h : ∀ u, u≤t → c u=v u) (p : Int) :
    L c initial t p = L v initial t p := by
  induction t generalizing p with
  | zero => simp [L,h 0 (by omega)]
  | succ t ih =>
    simp only [L]
    split
    · rw [ih (fun k hk => h k (by omega)),ih (fun k hk => h k (by omega)),ih (fun k hk => h k (by omega))]
    · exact h _ (by omega)

private theorem failed_prefix {c v : Nat → Bool} {t : Nat} (h : ∀ u, u≤t+1 → c u=v u) :
    Failed c t ↔ Failed v t := by
  unfold Failed
  rw [driven_prefix t (fun k hk => h k (by omega)),h t (by omega),h (t+1) (by omega)]

/-- Only the leftmost site of the light cone has to be changed to prescribe
one new center bit. The entire plane to its right is kept at launch. -/
private theorem edit (x : Int → Bool) (t : Nat) (b : Bool) : ∃ y : Int → Bool,
    (∀ p : Int, p≠-(t:Int) → y p=x p) ∧
    (∀ j, j<t → trace y j=trace x j) ∧ trace y t=b := by
  by_cases eq : trace x t=b
  · exact ⟨x,fun _ _ => rfl,fun _ _ => rfl,eq⟩
  let y := fun p : Int => if p=-(t:Int) then !x p else x p
  have same (p : Int) (ne : p≠-(t:Int)) : y p=x p := by simp [y,ne]
  refine ⟨y,same,fun j hj => evol_window (fun q lo _ => same q (by omega)),?_⟩
  have flip := center_flip_leftmost (x:=x) (x':=y) t (fun q lo _ => same q (by omega)) (by simp [y])
  change evol y t 0=b
  rw [flip]
  change (!(trace x t))=b
  cases h : trace x t <;> cases b <;> simp_all

/-- From a black tick with no earlier failure, set the next bit to
force the first failure there, keeping every other initial bit. -/
private theorem force_exit (x : Int → Bool) (k : Nat) (on : trace x k=true)
    (clean : ∀ i, i<k → ¬ Failed (trace x) i) : ∃ y : Int → Bool,
    (∀ p : Int, p≠-((k+1:Nat):Int) → y p=x p) ∧ FirstFailure (trace y) k := by
  obtain ⟨y,same,old,last⟩ := edit x (k+1) (read (trace x) k)
  refine ⟨y,same,⟨⟨(old k (by omega)).trans on,?_⟩,fun i hi =>
    fun bad => clean i hi ((failed_prefix (fun u hu => old u (by omega))).mp bad)⟩⟩
  rw [driven_prefix k (fun u hu => old u (by omega)),last]
  cases h : read (trace x) k <;> simp_all [read]

/-- One earlier failed prediction becomes a successful black check.
The next failure can be placed within two ticks, using only three new
initial sites strictly beyond the previously protected prefix. -/
theorem extend_failure (x : Int → Bool) (k : Nat) (fst : FirstFailure (trace x) k) :
    ∃ y l, k<l ∧ l≤k+2 ∧ FirstFailure (trace y) l ∧
      (∀ p : Int, p < -(l:Int)-1 ∨ -(k:Int)≤p → y p=x p) ∧
      (∀ i, i≤k → trace y i=trace x i) := by
  obtain ⟨a,sa,ha,last⟩ := edit x (k+1) (!(read (trace x) k))
  have clean (i : Nat) (hi : i≤k) : ¬ Failed (trace a) i := by
    by_cases lt : i<k
    · exact fun bad => fst.2 i lt ((failed_prefix (fun u hu => ha u (by omega))).mp bad)
    · have eq : i=k := by omega
      subst i
      rintro ⟨_,bad⟩
      rw [driven_prefix k (fun u hu => ha u (by omega)),last] at bad
      exact bad (by simp [read])
  by_cases on : trace a (k+1)=true
  · obtain ⟨y,sy,ff⟩ := force_exit a (k+1) on (fun i hi => clean i (by omega))
    refine ⟨y,k+1,by omega,by omega,ff,fun p hp => (sy p (by omega)).trans (sa p (by omega)),?_⟩
    intro i hi
    exact (evol_window (x:=a) (x':=y) (t:=i) (p:=0) (fun q lo _ => sy q (by omega))).trans (ha i (by omega))
  · obtain ⟨b,sb,hb,nextOn⟩ := edit a (k+2) true
    have before (i : Nat) (hi : i<k+2) : ¬ Failed (trace b) i := by
      by_cases le : i≤k
      · exact fun bad => clean i le ((failed_prefix (fun u hu => hb u (by omega))).mp bad)
      · have e : i=k+1 := by omega
        subst i
        exact fun bad => on ((hb (k+1) (by omega)).symm.trans bad.1)
    obtain ⟨y,sy,ff⟩ := force_exit b (k+2) nextOn before
    refine ⟨y,k+2,by omega,by omega,ff,fun p hp =>
      (sy p (by omega)).trans ((sb p (by omega)).trans (sa p (by omega))),?_⟩
    intro i hi
    exact (evol_window (x:=b) (x':=y) (t:=i) (p:=0) (fun q lo _ => sy q (by omega))).trans
      ((hb i (by omega)).trans (ha i (by omega)))

/-- Unbounded finite delays are obtainable while fixing every site
from -k rightwards, including the whole right half. Each extension
adds at least one tick, and at most two, to the previous delay. -/
theorem extend_many (x : Int → Bool) (k : Nat) (fst : FirstFailure (trace x) k) (n : Nat) :
    ∃ y l, k+n≤l ∧ l≤k+2*n ∧ FirstFailure (trace y) l ∧
      ∀ p : Int, p < -(l:Int)-1 ∨ -(k:Int)≤p → y p=x p := by
  induction n with
  | zero => exact ⟨x,k,by omega,by omega,fst,fun _ _ => rfl⟩
  | succ n ih =>
    obtain ⟨a,j,lo,hi,ff,same⟩ := ih
    obtain ⟨y,l,lo',hi',next,sy,_⟩ := extend_failure a j ff
    exact ⟨y,l,by omega,by omega,next,fun p hp => (sy p (by omega)).trans (same p (by omega))⟩

/-- The word 11000 beginning at a black cannot be read with four white
sites immediately to its left, for any choice of the full right half. -/
theorem no_11000 (x : Int → Bool) (white : ∀ p : Int, -4≤p → p<0 → x p=false)
    (black : trace x 0=true) (h3 : trace x 3=false) : trace x 4=true := by
  change x 0=true at black
  have h1 := white (-1) (by decide) (by decide)
  have h2 := white (-2) (by decide) (by decide)
  have h3' := white (-3) (by decide) (by decide)
  have h4 := white (-4) (by decide) (by decide)
  cases a : x 1 <;> cases b : x 2 <;> cases d : x 3 <;> cases e : x 4 <;>
    simp_all (config := { decide := true }) [trace,evol,rule]

open Rule30Window
open _root_.Ruliology.CellularAutomata.Rule30PeriodTwoLadder (orb orb_succ testBit_L tr rn)

/-- The packed half used in the period-two ladder works for any clock. -/
private theorem packed_general (c : Nat → Bool) (X : Nat) (t : Nat) (p : Int) (hp : p<0) :
    L c (Rule30PeriodTwoLadder.startOf X) t p = (orb c X t).testBit (-1-p).toNat := by
  induction t generalizing p with
  | zero => simp [L_zero hp,orb,Rule30PeriodTwoLadder.startOf,hp]
  | succ t ih =>
    rw [L_succ hp,ih (p-1) (by omega),orb_succ,testBit_L,ih p hp,
      show (-1-(p-1)).toNat=(-1-p).toNat+1 by omega]
    unfold rule
    by_cases eq : p = -1
    · subst p
      rw [show (-1:Int)+1=0 by decide,L_col0]
      simp [rn]
    · rw [ih (p+1) (by omega)]
      obtain ⟨k,hk⟩ : ∃ k, (-1-p).toNat=k+1 := ⟨(-1-p).toNat-1,by omega⟩
      rw [hk,show (-1-(p+1)).toNat=k by omega]
      rfl

private theorem packed_read (c : Nat → Bool) (t : Nat) (p : Int) (hp : p<0) :
    L c (fun _ => false) t p = (orb c 0 t).testBit (-1-p).toNat := by
  have z : Rule30PeriodTwoLadder.startOf 0 = fun _ => false := by funext q; simp [Rule30PeriodTwoLadder.startOf]
  rw [← z]; exact packed_general c 0 t p hp

private def mismatch (w t : Nat) : Bool :=
  w.testBit t && (tr w.testBit 0 t == w.testBit (t+1))

private theorem mismatch_iff (w t : Nat) : mismatch w t = true ↔ Failed w.testBit t := by
  unfold mismatch Failed tr
  rw [packed_read _ t (-1) (by decide)]
  change (_ && (_ == _)) = true ↔ _ ∧ (orb w.testBit 0 t).testBit 0 ≠ !w.testBit (t+1)
  cases w.testBit t <;> cases (orb w.testBit 0 t).testBit 0 <;> cases w.testBit (t+1) <;> decide

private def bits := centerLoop 61513 61513 0 (2^61513) 0

set_option maxRecDepth 200000 in
set_option maxHeartbeats 10000000 in
private theorem samples : (bits >>> 59732)%2^20=353363 ∧
    (bits >>> 61476)%2^37=37179128387 := by decide +kernel

set_option exponentiation.threshold 62000 in
private theorem sample_bit {s n w : Nat} (le : s+n≤61513)
    (sample : (bits >>> s)%2^n=w) (i : Nat) (small : i<n) :
    cell (s+i) 0 = w.testBit i := by
  have h := centerLoop_spec 61513 61513 0 0 (by simp) (s+i)
  rw [show row 61513 0=2^61513 from rfl] at h
  rw [← sample,Nat.testBit_mod_two_pow,decide_eq_true small,Bool.true_and,Nat.testBit_shiftRight]
  unfold bits
  rw [h,ite_eq_right (by omega),ite_eq_left (by omega),row_testBit _ _ (by omega)]
  rfl

private theorem first_of_sample {s l w : Nat}
    (bitsAgree : ∀ i, i≤l+1 → cell (s+i) 0 = w.testBit i)
    (last : mismatch w l=true) (early : ∀ i : Fin l, mismatch w i.val=false) :
    FirstFailure (fun t => cell (s+t) 0) l := by
  refine ⟨(failed_prefix bitsAgree).mpr ((mismatch_iff w l).mp last),?_⟩
  intro i hi bad
  have eq := (mismatch_iff w i).mpr ((failed_prefix (fun t ht => bitsAgree t (by omega))).mp bad)
  rw [early ⟨i,hi⟩] at eq
  contradiction

/-- The black-only observer passes through time 34. Already the fifth
center reading is impossible from a white left half with any right half. -/
theorem singleton_delayed_but_impossible :
    FirstFailure (fun t => cell (61476+t) 0) 35 ∧
    ¬∃ x : Int → Bool, (∀ p : Int, -4≤p → p<0 → x p=false) ∧
      ∀ t, t≤4 → trace x t=cell (61476+t) 0 := by
  have h := sample_bit (s:=61476) (n:=37) (by decide) samples.2
  refine ⟨first_of_sample (fun i hi => h i (by omega)) (by decide +kernel) (by decide +kernel),?_⟩
  rintro ⟨x,white,copy⟩
  have h0 := (copy 0 (by decide)).trans (h 0 (by decide))
  have h3 := (copy 3 (by decide)).trans (h 3 (by decide))
  have h4 := (copy 4 (by decide)).trans (h 4 (by decide))
  exact Bool.noConfusion ((no_11000 x white (h0.trans (by decide)) (h3.trans (by decide))).symm.trans (h4.trans (by decide : (37179128387:Nat).testBit 4=false)))

def smallSeed (p : Int) : Bool := decide (0≤p) && (239:Nat).testBit p.toNat

/-- Here the full center trace does come from a finite seed with a white
left half for 19 readings. The twentieth reading fails the black check. -/
theorem singleton_physical_eighteen :
    (∀ p : Int, p<0 → smallSeed p=false) ∧ (∀ p : Int, 7<p → smallSeed p=false) ∧
    (∀ t, t≤18 → trace smallSeed t=cell (59732+t) 0) ∧
    FirstFailure (fun t => cell (59732+t) 0) 18 := by
  have h := sample_bit (s:=59732) (n:=20) (by decide) samples.1
  have finite : ∀ j : Fin 19, trace smallSeed j.val=(353363:Nat).testBit j.val := by decide +kernel
  refine ⟨fun p hp => by simp [smallSeed,show ¬0≤p by omega],?_,
    fun t ht => (finite ⟨t,by omega⟩).trans (h t (by omega)).symm,
    first_of_sample (fun i hi => h i (by omega)) (by decide +kernel) (by decide +kernel)⟩
  intro p hp
  have small : (239:Nat)<2^p.toNat := Nat.lt_of_lt_of_le (by decide : 239<2^8)
    (Nat.pow_le_pow_right (by decide) (by omega))
  simp [smallSeed,Nat.testBit_lt_two_pow small]

/-- Agreement through offset n, with an initially white negative half
and an arbitrary right half. -/
def Feasible (c : Nat → Bool) (n : Nat) : Prop :=
  ∃ x : Int → Bool, (∀ p : Int, p<0 → x p=false) ∧ ∀ t, t≤n → trace x t=c t

def PhysicalExit (c : Nat → Bool) (n : Nat) : Prop := Feasible c n ∧ ¬Feasible c (n+1)

private theorem wall_correct {x : Int → Bool} (white : ∀ p : Int, p<0 → x p=false)
    (t : Nat) (p : Int) (neg : p≤0) : L (trace x) (fun _ => false) t p=evol x t p := by
  induction t generalizing p with
  | zero =>
    by_cases z : p=0
    · simp [z,L_col0,trace]
    · simp [L,evol,show p<0 by omega,white p (by omega)]
  | succ t ih =>
    by_cases z : p=0
    · simp [z,L_col0,trace]
    · rw [L_succ (by omega),ih (p-1) (by omega),ih p neg,ih (p+1) (by omega)]
      rfl

private theorem failure_rules_out {c : Nat → Bool} {n : Nat} (bad : Failed c n) :
    ¬Feasible c (n+1) := by
  rintro ⟨x,white,eq⟩
  obtain ⟨on,bad'⟩ := (failed_prefix eq).mpr bad
  rw [wall_correct white n (-1) (by decide)] at bad'
  apply bad'
  change evol x n (-1) = !(rule (evol x n (-1)) (evol x n 0) (evol x n 1))
  change evol x n 0=true at on
  cases h : evol x n (-1) <;> simp [rule,on]

/-- The two certified physical exit times. At the later launch the
black-only test continues to pass for a further 32 ticks. -/
theorem singleton_physical_exits :
    PhysicalExit (fun t => cell (59732+t) 0) 18 ∧
    PhysicalExit (fun t => cell (61476+t) 0) 3 := by
  obtain ⟨white,_,copy,ff⟩ := singleton_physical_eighteen
  refine ⟨⟨⟨smallSeed,white,copy⟩,failure_rules_out ff.1⟩,?_,?_⟩
  · let x : Int → Bool := fun p => decide (0≤p ∧ p≤2)
    have known : ∀ i : Fin 4, trace x i.val=(37179128387:Nat).testBit i.val := by decide +kernel
    exact ⟨x,fun p hp => by simp [x,show ¬0≤p by omega],fun t ht =>
      (known ⟨t,by omega⟩).trans ((sample_bit (s:=61476) (n:=37) (by decide) samples.2 t (by omega)).symm)⟩
  · rintro ⟨x,white,copy⟩
    exact singleton_delayed_but_impossible.2 ⟨x,fun p _ hp => white p hp,copy⟩

/-- The full right half and sites down to −35 can be kept exactly as
in the actual row at age 61476, while initial edits farther left cause
arbitrarily late first failures on other finite Rule 30 seeds. -/
theorem controls_for_record (n : Nat) :
    ∃ y l, 35+n≤l ∧ l≤35+2*n ∧ FirstFailure (trace y) l ∧
      ∀ p : Int, p < -(l:Int)-1 ∨ -35≤p → y p=cell 61476 p := by
  have clock : trace (cell 61476) = fun k => cell (61476+k) 0 := by
    funext k
    have h := Rule30ZeroBoundaryBarriers.evol_restart seed 61476 k 0
    simpa only [evol_seed] using h
  exact extend_many (cell 61476) 35 (clock ▸ singleton_delayed_but_impossible.1) n

/-- The virtual center is represented by site -1, with its right input
at site 0. The initial black is at -1 and all other negative sites are white. -/
def Matches (s : Nat) (input : Nat → Bool) (n : Nat) : Prop :=
  ∀ t, t≤n → L input (Rule30PeriodTwoLadder.startOf 1) t (-1)=cell (s+t) 0

/-- Both real-center excerpts may start at arbitrary ages. Even a Boolean
function of arbitrarily many shifted, positive-stride samples may drive it:
under a proposed period it inherits the same period and onset. -/
theorem match_bound {T P : Nat} (pos : 0<P)
    (per : ∀ t, T≤t → cell (t+P) 0=cell t 0)
    (s m : Nat) (offset stridePred : Fin m → Nat) (f : (Fin m → Bool) → Bool) :
    ¬ Matches s (fun t => f (fun i => cell (offset i+(stridePred i+1)*t) 0)) (2*(T+P)) := by
  let b := fun t => f (fun i => cell (offset i+(stridePred i+1)*t) 0)
  have period (t : Nat) (ht : T≤t) : b (t+P)=b t := by
    apply congrArg f
    funext i
    have large : T≤offset i+(stridePred i+1)*t := by rw [Nat.succ_mul]; omega
    rw [Nat.mul_add,← Nat.add_assoc]
    exact periodic_mul (f:=fun k => cell k 0) per (stridePred i+1) _ large
  obtain ⟨t,lo,hi,bad⟩ := Rule30DrivenLeftWindows.exists_period_disagreement_before_local
    b (Rule30PeriodTwoLadder.startOf 1) (m:=1) (T:=T) pos (by decide)
    (fun t ht _ => period t ht)
    (fun p hp => by simpa [Rule30PeriodTwoLadder.startOf,show p<0 by omega] using
      (Nat.testBit_lt_two_pow (x:=1) (i:=(-1-p).toNat) (by
        exact Nat.lt_of_lt_of_le (by decide : 1<2^1) (Nat.pow_le_pow_right (by decide) (by omega)))))
    (by decide)
  intro copy
  apply bad
  rw [copy (t+P) (by omega),copy t (by omega),← Nat.add_assoc,per _ (by omega)]

theorem problem1_of_matches
    (many : ∀ n, ∃ s m, ∃ offset stridePred : Fin m → Nat, ∃ f : (Fin m → Bool) → Bool,
      Matches s (fun t => f (fun i => cell (offset i+(stridePred i+1)*t) 0)) n) : Rule30Prize.Problem1 := by
  rintro ⟨T,P,pos,per⟩
  obtain ⟨s,m,offset,stridePred,f,copy⟩ := many (2*(T+P))
  exact match_bound pos per s m offset stridePred f copy

private def pairInput (t : Nat) : Bool :=
  xor ((231424319805287749480199:Nat).testBit t) ((197859586904456642810396:Nat).testBit t)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 15000000 in
private theorem paired_samples :
    (bits >>> 0)%2^78=71127594389035322811195 ∧
    (bits >>> 10769)%2^78=231424319805287749480199 ∧
    (bits >>> 33309)%2^78=197859586904456642810396 := by decide +kernel

/-- The XOR of two actual center excerpts drives all 76 consecutive
updates starting at the seed and fails on update 77. -/
theorem two_shifts_76 :
    Matches 0 (fun t => xor (cell (10769+t) 0) (cell (33309+t) 0)) 76 ∧
    ¬Matches 0 (fun t => xor (cell (10769+t) 0) (cell (33309+t) 0)) 77 := by
  let v := fun t => xor (cell (10769+t) 0) (cell (33309+t) 0)
  have b (t : Nat) (ht : t≤77) : v t=pairInput t := by
    unfold v pairInput
    rw [sample_bit (s:=10769) (n:=78) (by decide) paired_samples.2.1 t (by omega),
      sample_bit (s:=33309) (n:=78) (by decide) paired_samples.2.2 t (by omega)]
  have bit (t : Nat) (ht : t≤77) : L v (Rule30PeriodTwoLadder.startOf 1) t (-1) =
      (orb pairInput 1 t).testBit 0 := by
    rw [driven_prefix t (fun u hu => b u (by omega)),packed_general pairInput 1 t (-1) (by decide)]
    rfl
  have ok : ∀ t : Fin 77, (orb pairInput 1 t.val).testBit 0 =
      (71127594389035322811195:Nat).testBit t.val := by decide +kernel
  constructor
  · intro t ht
    exact (bit t (by omega)).trans ((ok ⟨t,by omega⟩).trans
      ((sample_bit (s:=0) (n:=78) (by decide) paired_samples.1 t (by omega)).symm))
  · intro copy
    have no : (orb pairInput 1 77).testBit 0 ≠ (71127594389035322811195:Nat).testBit 77 := by decide +kernel
    exact no ((bit 77 (by decide)).symm.trans ((copy 77 (by decide)).trans
      (sample_bit (s:=0) (n:=78) (by decide) paired_samples.1 77 (by decide))))

end Ruliology.CellularAutomata.Rule30RestartVisibility
