module

public import Ruliology.CellularAutomata.Rule30Certificates.MassCounterexamples

@[expose] public section

/-!
# Arbitrarily large counterexamples to the sharp period-two mass conjectures

For a fixed white wall, write `H` for a valid G-prefix length and `A` for the
weight of its finite initial row below `H`, as in `Rule30PeriodTwoMass`.
There are unbounded horizons with `H = 7*A + 9`, and unbounded even horizons
with `H = 7*A + 8`. Both named sharp conjectures fail. Every `MassFloor q d`
requires `q ≥ 7`, and at `q = 7` it requires `d ≥ 9`.

The initial row consists of sites 2 and 4, an initial segment of the spikes at
`1 + 7*i`, and a chosen finite suffix. In moving coordinates the two inputs
from the periodic background have period 28. Each additional lane at most
doubles the period. Increasing the spike count by `8 * 2^w` preserves all
`w` tests after the cut and preserves the excess of length over seven times
weight. The existence of some linear floor and the period-two question for
the single seed remain open.
-/

namespace Ruliology.CellularAutomata.Rule30MassCounterexamples

open Ruliology.CellularAutomata.Rule30ZeroBoundary.IntegerForm (F iter testBit_F_zero testBit_F_succ)
open Rule30PeriodTwoMass (tr cnt wt gstep GWord ConjS ConjSEven MassFloor)

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- Time zero, followed by an eight-tick cycle. -/
def phase (t : Nat) := if t = 0 then 0 else 1 + (t-1)%8
/-- An eight-cell boundary layer followed by a seven-cell spatial period. -/
def slot (d : Nat) := if d < 8 then d else 8 + (d-8)%7

def masks : Array Nat := #[278,17333,9765,32125,321,17251,9814,32213,277]
def ether (t d : Nat) := masks[phase t]!.testBit (slot d)

private theorem phase_lt (t : Nat) : phase t < 9 := by unfold phase; split <;> omega
private theorem slot_lt (d : Nat) : slot d < 15 := by unfold slot; split <;> omega
private theorem phase_mod (t : Nat) : phase t % 4 = t % 4 := by unfold phase; split <;> omega
private theorem slot_mod (d : Nat) : slot d % 7 = d % 7 := by unfold slot; split <;> omega
private theorem phase_add (t n : Nat) : phase (phase t+n) = phase (t+n) := by
  unfold phase; split <;> split <;> split <;> omega
private theorem slot_add (d n : Nat) : slot (slot d+n) = slot (d+n) := by
  unfold slot
  split <;> split <;> (first | rfl | split <;> omega)

private theorem norm (t d a b : Nat) : ether (phase t+a) (slot d+b) = ether (t+a) (d+b) := by
  simp only [ether, phase_add, slot_add]

private theorem ether_zero (t : Nat) : ether (t+1) 0 = xor (ether t 1) (ether t 0) := by
  have h : ∀ t, t < 9 → ether (t+1) 0 = xor (ether t 1) (ether t 0) := by decide +kernel
  have hh := h (phase t) (phase_lt t)
  change ether (phase t+1) (slot 0+0) = xor (ether (phase t+0) (slot 0+1)) (ether (phase t+0) (slot 0+0)) at hh
  rw [norm, norm, norm] at hh
  exact hh


private theorem ether_step (t d : Nat) :
    ether (t+1) (d+1) = xor (ether t (d+2)) (ether t (d+1) || ether t d) := by
  have h : ∀ t, t < 9 → ∀ d, d < 15 →
      ether (t+1) (d+1) = xor (ether t (d+2)) (ether t (d+1) || ether t d) := by decide +kernel
  have hh := h (phase t) (phase_lt _) (slot d) (slot_lt _)
  change ether (phase t+1) (slot d+1) = xor (ether (phase t+0) (slot d+2))
    (ether (phase t+0) (slot d+1) || ether (phase t+0) (slot d+0)) at hh
  rw [norm, norm, norm, norm] at hh
  exact hh

/-- Leftmost bit of each of these four seven-periodic bulk rows is bit 0. -/
def bulk : Array Nat := #[2,7,76,123]
private theorem ether_bulk (t d : Nat) (hd : 8 ≤ d) :
    ether t d = bulk[t%4]!.testBit (d%7) := by
  have h : ∀ p, p < 9 → ∀ j, j < 15 → 8 ≤ j →
      masks[p]!.testBit j = bulk[p%4]!.testBit (j%7) := by decide +kernel
  have bound : 8 ≤ slot d := by unfold slot; split <;> omega
  simpa only [ether,phase_mod,slot_mod] using h (phase t) (phase_lt _) (slot d) (slot_lt _) bound

def initialBit (d : Nat) : Bool := decide (d=2 ∨ d=4 ∨ d%7=1)
private theorem ether_initial (d : Nat) : ether 0 d = initialBit d := by
  by_cases h : d < 8
  · exact (by decide +kernel : ∀ j, j < 8 → ether 0 j = initialBit j) _ h
  · rw [ether_bulk _ _ (by omega)]
    have z : ∀ j, j<7 → bulk[0%4]!.testBit j = decide (j=1) := by decide +kernel
    rw [z _ (by omega)]
    unfold initialBit
    apply decide_eq_decide.mpr; omega

private theorem ether_white (t : Nat) :
    ether t 0 = decide (t ≠ 0 ∧ t%8≠6) := by
  have h : ∀ p, p<9 → masks[p]!.testBit 0 = decide (p ≠ 0 ∧ p%8≠6) := by decide +kernel
  change masks[phase t]!.testBit 0 = _
  rw [h _ (phase_lt _)]
  apply decide_eq_decide.mpr
  unfold phase; split <;> omega

private theorem ether_g (t : Nat) : gstep (fun s=>ether s 0) t = true := by
  unfold gstep; split <;> simp only [ether_white]
  · decide
  · split <;> simp <;> omega

/-- A row with supplementary bits 2 and 4 and n bits spaced seven apart. -/
def spikes : Nat → Nat
  | 0 => 0
  | n+1 => spikes n ||| (2^(1+7*n))

def seed (n : Nat) := spikes n ||| 20
def cut (n : Nat) := 1+7*n

private theorem spikes_bit (n d : Nat) :
    (spikes n).testBit d = decide (d%7=1 ∧ d<cut n) := by
  induction n with
  | zero => simp [spikes, cut]; omega
  | succ n ih =>
    simp only [spikes,Nat.testBit_or,Nat.testBit_two_pow,ih,Bool.or_eq_decide]
    apply decide_eq_decide.mpr
    simp only [decide_eq_true_eq]; unfold cut; omega

private theorem twenty_bit (d : Nat) : (20:Nat).testBit d = decide (d=2 ∨ d=4) := by
  by_cases h : d<5
  · exact (by decide +kernel : ∀ j, j<5 → (20:Nat).testBit j = decide (j=2 ∨ j=4)) d h
  · have hz : (20:Nat).testBit d = false := by
      apply Nat.testBit_lt_two_pow
      exact Nat.lt_of_lt_of_le (by decide : 20 < 2^5) (Nat.pow_le_pow_right (by decide) (by omega))
    rw [hz]
    simp; omega

private theorem seed_bit (n d : Nat) (hn : 0 < n) :
    (seed n).testBit d = (decide (d < cut n) && initialBit d) := by
  simp only [seed,Nat.testBit_or,spikes_bit,twenty_bit,initialBit]
  simp only [Bool.or_eq_decide,Bool.and_eq_decide]
  apply decide_eq_decide.mpr; simp only [decide_eq_true_eq]; unfold cut; omega

def bitAt (n t d : Nat) := (iter F t (seed n)).testBit d

private theorem beforeFront (n : Nat) (hn : 0<n) : ∀ t d, t+d < cut n → bitAt n t d = ether t d
  | 0,d,hd => by
    change (seed n).testBit d = ether 0 d
    rw [seed_bit _ _ hn,ether_initial]; simp [show d<cut n by omega]
  | t+1,0,hd => by
    rw [ether_zero]
    change (F (iter F t (seed n))).testBit 0 = _
    rw [testBit_F_zero]
    change xor (bitAt n t 1) (bitAt n t 0) = _
    rw [beforeFront n hn t 1 (by omega), beforeFront n hn t 0 (by omega)]
  | t+1,d+1,hd => by
    rw [ether_step]
    change (F (iter F t (seed n))).testBit (d+1) = _
    rw [testBit_F_succ]
    change xor (bitAt n t (d+2)) (bitAt n t (d+1) || bitAt n t d) = _
    rw [beforeFront n hn t (d+2) (by omega), beforeFront n hn t (d+1) (by omega), beforeFront n hn t d (by omega)]

/-- Bits immediately in front of the disturbance, packed from the periodic bulk. -/
def feedTable : Array Nat := #[0,0,0,3,0,3,0,3,0,0,1,2,1,3,1,3,0,0,3,1,2,2,2,3,0,1,2,3]
def feed (t : Nat) := feedTable[t%28]!

/-- At time t the two external inputs sit at cut−t−2 and cut−t−1. -/
private theorem feed_correct (n t j : Nat) (ht : t+16 ≤ cut n) (hj : j<2) :
    ether t (cut n-t-2+j) = (feed t).testBit j := by
  rw [ether_bulk _ _ (by omega)]
  have h : ∀ p, p<28 → ∀ i, i<2 →
      bulk[p%4]!.testBit ((34-p+i)%7) = feedTable[p]!.testBit i := by decide +kernel
  have hp : (t%28)%4 = t%4 := by omega
  have hq : (34-t%28+j)%7 = (cut n-t-2+j)%7 := by unfold cut at *; omega
  simpa only [feed,hp,hq] using h (t%28) (by omega) j hj

private theorem cnt_seed (n : Nat) (hn : 0<n) : ∀ h,
    cnt (seed n).testBit h = cnt initialBit (min h (cut n))
  | 0 => rfl
  | h+1 => by
    rw [cnt,cnt_seed n hn h,seed_bit n h hn]
    by_cases hlt : h<cut n
    · rw [Nat.min_eq_left (by omega),Nat.min_eq_left (by omega),cnt]
      simp [hlt]
    · rw [Nat.min_eq_right (by omega),Nat.min_eq_right (by omega)]
      simp [hlt]

private theorem block_bit (n j : Nat) (hn : 0<n) (hj : j<7) :
    initialBit (cut n+j)=decide (j=0) := by
  apply decide_eq_decide.mpr; unfold cut; omega

private theorem block_count (n : Nat) (hn : 0<n) :
    cnt initialBit (cut (n+1)) = cnt initialBit (cut n)+1 := by
  rw [show cut (n+1)=cut n+7 by unfold cut; omega]
  simp only [cnt]
  have first := block_bit n 0 hn (by decide)
  simp only [Nat.add_zero,decide_true] at first
  simp only [block_bit n 6 hn (by decide),block_bit n 5 hn (by decide),block_bit n 4 hn (by decide),
    block_bit n 3 hn (by decide),block_bit n 2 hn (by decide),block_bit n 1 hn (by decide),first]
  rfl

private theorem count_init (m : Nat) : cnt initialBit (cut (m+1))=m+3 := by
  induction m with
  | zero => decide
  | succ m ih => rw [block_count (m+1) (by omega),ih]

/-! ## Any finite suffix and any finite lookahead -/

namespace Suffix

/-- Attach the low bit of q at the first omitted spike. -/
def row (n q : Nat) := seed n ||| (q <<< cut n)

private def read (x t d : Nat) := (iter F t x).testBit d

private theorem row_before (n q d : Nat) (hd : d<cut n) :
    (row n q).testBit d = (seed n).testBit d := by
  simp [row,Nat.testBit_or,Nat.testBit_shiftLeft,show ¬cut n≤d by omega]

private theorem row_after (n q j : Nat) (hn : 0<n) :
    (row n q).testBit (cut n+j) = q.testBit j := by
  rw [row,Nat.testBit_or,seed_bit _ _ hn,Nat.testBit_shiftLeft]
  simp [show ¬cut n+j<cut n by omega]

/-- An agreement of complete wall-side row prefixes propagates inside its
forward triangle, independently of the two ages when it is sampled. -/
private theorem propagate (x y a b W : Nat)
    (h : ∀ d, d<W → read x a d=read y b d) :
    ∀ u d, u+d<W → read x (a+u) d=read y (b+u) d
  | 0,d,hd => h d (by omega)
  | u+1,0,hd => by
    change (F (iter F (a+u) x)).testBit 0 = (F (iter F (b+u) y)).testBit 0
    rw [testBit_F_zero,testBit_F_zero]
    change xor (read x (a+u) 1) (read x (a+u) 0)=xor (read y (b+u) 1) (read y (b+u) 0)
    rw [propagate x y a b W h u 1 (by omega),propagate x y a b W h u 0 (by omega)]
  | u+1,d+1,hd => by
    change (F (iter F (a+u) x)).testBit (d+1) = (F (iter F (b+u) y)).testBit (d+1)
    rw [testBit_F_succ,testBit_F_succ]
    change xor (read x (a+u) (d+2)) (read x (a+u) (d+1) || read x (a+u) d)=
      xor (read y (b+u) (d+2)) (read y (b+u) (d+1) || read y (b+u) d)
    rw [propagate x y a b W h u (d+2) (by omega),propagate x y a b W h u (d+1) (by omega),
      propagate x y a b W h u d (by omega)]

private theorem untouched (n q t d : Nat) (hn : 0<n) (h : t+d<cut n) :
    read (row n q) t d=ether t d := by
  have a := propagate (row n q) (seed n) 0 0 (cut n) (row_before n q) t d h
  rw [Nat.zero_add] at a
  exact a.trans (beforeFront n hn t d h)

/-- Lanes zero and one supply the two periodic background bits. Later lanes
start from q and evolve by the left-permutive update in moving coordinates. -/
def lanes (q : Nat) : Nat → Nat → Bool
  | 0,j => if j<2 then (feed 0).testBit j else q.testBit (j-2)
  | t+1,j => match j with
    | 0 => (feed (t+1)).testBit 0
    | 1 => (feed (t+1)).testBit 1
    | i+2 => xor (lanes q t (i+2)) (lanes q t (i+1) || lanes q t i)

private theorem low_lanes (q t j : Nat) (hj : j<2) :
    lanes q t j=(feed t).testBit j := by
  rcases (show j=0 ∨ j=1 by omega) with rfl | rfl <;> cases t <;> rfl

private theorem lanes_match (n q : Nat) (hn : 0<n) :
    ∀ t, t+16≤cut n → ∀ j,
    read (row n q) t (cut n-t-2+j)=lanes q t j := by
  intro t
  induction t with
  | zero =>
    intro ht j
    by_cases hj : j<2
    · rw [low_lanes _ _ _ hj,untouched _ _ _ _ hn (by omega),feed_correct _ _ _ ht hj]
    · have loc : cut n-0-2+j=cut n+(j-2) := by omega
      change (row n q).testBit _ = _
      rw [loc,row_after _ _ _ hn]
      simp [lanes,hj]
  | succ t ih =>
    intro ht j
    by_cases hj : j<2
    · rw [low_lanes _ _ _ hj,untouched _ _ _ _ hn (by omega),feed_correct _ _ _ ht hj]
    · obtain ⟨i,rfl⟩ : ∃ i, j=i+2 := ⟨j-2,by omega⟩
      let d:=cut n-t-2+i
      have loc : cut n-(t+1)-2+(i+2)=d+1 := by dsimp [d];omega
      rw [loc]
      change (F (iter F t (row n q))).testBit (d+1)=_
      rw [testBit_F_succ]
      change xor (read (row n q) t (d+2)) (read (row n q) t (d+1) || read (row n q) t d)=_
      have a:=ih (by omega) (i+2)
      have b:=ih (by omega) (i+1)
      have c:=ih (by omega) i
      change read (row n q) t d=lanes q t i at c
      rw [show d+2=cut n-t-2+(i+2) by dsimp [d];omega,a,
        show d+1=cut n-t-2+(i+1) by dsimp [d];omega,b,c]
      rfl

/-- Bound on the clock period of a strip containing w internal lanes. -/
def period (w : Nat) := 28 * 2^w

private theorem period_succ (w : Nat) : period (w+1)=2*period w := by
  simp only [period,Nat.pow_succ];omega

/-- Every finite strip repeats from its first tick. This is uniform in q. -/
theorem lanes_periodic (q w : Nat) :
    ∀ j, j<w+2 → ∀ t, lanes q (t+period w) j=lanes q t j := by
  induction w with
  | zero =>
    intro j hj t
    rw [low_lanes _ _ _ hj,low_lanes _ _ _ hj]
    have h : (t+period 0)%28=t%28 := by simp [period]
    simp [feed,h]
  | succ w ih =>
    intro j hj
    rw [period_succ]
    by_cases h : j<w+2
    · exact Ruliology.CellularAutomata.Rule30Diagonals.periodic_double (f:=fun t=>lanes q t j) (L:=period w) (ih j h)
    · obtain rfl : j=w+2 := by omega
      apply Ruliology.CellularAutomata.Rule30Diagonals.xor_accum_periodic
        (x:=fun t=>lanes q t (w+2)) (L:=period w) (g:=fun t=>lanes q t (w+1) || lanes q t w)
      · intro t; rfl
      · intro t;rw [ih (w+1) (by omega), ih w (by omega)]

/-- Shift in spike count. Its sevenfold time shift is a multiple of eight and
twice the moving-strip period. -/
def jump (w : Nat) := 8 * 2^w
private def delay (w : Nat) := 56 * 2^w
private def sample (n : Nat) := cut n-16

private theorem cut_shift (n w : Nat) : cut (n+jump w)=cut n+delay w := by
  simp only [cut,jump,delay];omega

private theorem sample_shift (n w : Nat) (hn : 3≤n) :
    sample (n+jump w)=sample n+delay w := by
  unfold sample;rw [cut_shift];unfold cut;omega

private theorem match_sample (n q w d : Nat) (hn : 3≤n) (hd : d<16+w) :
    read (row (n+jump w) q) (sample (n+jump w)) d =
      read (row n q) (sample n) d := by
  have h1 : 0<n := by omega
  have h2 : 0<n+jump w := by omega
  have s : sample n+16=cut n := by unfold sample cut;omega
  have s' : sample (n+jump w)+16=cut (n+jump w) := by unfold sample cut;omega
  by_cases hl : d<16
  · rw [untouched _ _ _ _ h2 (by omega),untouched _ _ _ _ h1 (by omega)]
    have p : phase (sample (n+jump w))=phase (sample n) := by
      rw [sample_shift n w hn];unfold phase delay sample cut;split <;> split <;> omega
    simp only [ether,p]
  · let j:=d-14
    have hj : j<w+2 := by dsimp [j];omega
    have a:=lanes_match (n+jump w) q h2 (sample (n+jump w)) (by omega) j
    have b:=lanes_match n q h1 (sample n) (by omega) j
    rw [show cut (n+jump w)-sample (n+jump w)-2+j=d by dsimp [j];omega] at a
    rw [show cut n-sample n-2+j=d by dsimp [j];omega] at b
    have p:=Ruliology.CellularAutomata.Rule30Diagonals.periodic_double (f:=fun t=>lanes q t j) (L:=period w) (lanes_periodic q w j hj) (sample n)
    have dd : delay w=2*period w := by unfold delay period;omega
    rw [a,b,sample_shift n w hn,dd];exact p

private theorem terminal_read (n q w u : Nat) (hn : 3≤n) (hu : u<16+w) :
    tr (row (n+jump w) q) (sample (n+jump w)+u)=tr (row n q) (sample n+u) :=
  propagate _ _ _ _ _ (fun d h=>match_sample n q w d hn h) u 0 (by omega)

private theorem initial_checks (n q t : Nat) (hn : 0<n) (ht : t<cut n) :
    gstep (tr (row n q)) t=true := by
  have same (i : Nat) (hi : i≤t) : tr (row n q) i=ether i 0 := untouched n q i 0 hn (by omega)
  have good:=ether_g t
  unfold gstep at *
  rw [same 0 (by omega),same t (by omega),same (t-2) (by omega)]
  exact good

/-- All individual tests in the lookahead have the same outcomes. -/
theorem suffix_checks_recur (n q w i : Nat) (hn : 3≤n) (hi : i<w) :
    gstep (tr (row (n+jump w) q)) (cut (n+jump w)+i) =
    gstep (tr (row n q)) (cut n+i) := by
  let u:=16+i
  have hu : u<16+w := by dsimp [u];omega
  have c : cut n+i=sample n+u := by dsimp [sample,cut,u];omega
  have c' : cut (n+jump w)+i=sample (n+jump w)+u := by dsimp [sample,cut,u];omega
  have hp : (cut (n+jump w)+i)%2=(cut n+i)%2 := by rw [cut_shift];unfold delay;omega
  have z : cut n+i≠0 := by unfold cut;omega
  have z' : cut (n+jump w)+i≠0 := by unfold cut;omega
  have c2 : cut n+i-2=sample n+(u-2) := by dsimp [sample,cut,u];omega
  have c2' : cut (n+jump w)+i-2=sample (n+jump w)+(u-2) := by dsimp [sample,cut,u];omega
  have cur : tr (row (n+jump w) q) (cut (n+jump w)+i)=tr (row n q) (cut n+i) := by
    rw [c,c']; exact terminal_read n q w u hn hu
  have old : tr (row (n+jump w) q) (cut (n+jump w)+i-2)=tr (row n q) (cut n+i-2) := by
    rw [c2,c2']; exact terminal_read n q w (u-2) hn (by omega)
  simp only [gstep,ite_eq_right z,ite_eq_right z',hp,cur,old]

private theorem word_iff_tail (n q w : Nat) (hn : 0<n) :
    GWord (tr (row n q)) (cut n+w) ↔
    ∀ i, i<w → gstep (tr (row n q)) (cut n+i)=true := by
  constructor
  · intro h i hi;exact h (cut n+i) (by omega)
  · intro h t ht
    by_cases b : t<cut n
    · exact initial_checks n q t hn b
    · exact (show cut n+(t-cut n)=t by omega) ▸ h (t-cut n) (by omega)

/-- Finite-horizon validity repeats for every suffix and lookahead width. -/
theorem suffix_word_recurrence (n q w : Nat) (hn : 3≤n) :
    GWord (tr (row (n+jump w) q)) (cut (n+jump w)+w) ↔ GWord (tr (row n q)) (cut n+w) := by
  rw [word_iff_tail _ _ _ (by omega),word_iff_tail _ _ _ (by omega)]
  constructor
  · intro h i hi
    rw [← suffix_checks_recur n q w i hn hi]; exact h i hi
  · intro h i hi
    rw [suffix_checks_recur n q w i hn hi]; exact h i hi


/-- Iteration at every nonnegative multiple of the spike-count shift. -/
theorem suffix_word_multiples (n q w k : Nat) (hn : 3≤n) :
    GWord (tr (row (n+k*jump w) q)) (cut (n+k*jump w)+w) ↔
    GWord (tr (row n q)) (cut n+w) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : n+(k+1)*jump w=(n+k*jump w)+jump w := by rw [Nat.succ_mul];omega
    rw [e,suffix_word_recurrence (n+k*jump w) q w (by omega)]
    exact ih

private theorem count_split (f : Nat → Bool) (a b : Nat) :
    cnt f (a+b)=cnt f a+cnt (fun j=>f (a+j)) b := by
  induction b with
  | zero => simp [cnt]
  | succ b ih =>
    rw [show a+(b+1)=(a+b)+1 by omega,cnt,ih,cnt]
    omega

private theorem count_prefix (n q : Nat) : ∀ h, h≤cut n →
    cnt (row n q).testBit h=cnt (seed n).testBit h
  | 0,_ => rfl
  | h+1,hh => by
    rw [cnt,cnt,count_prefix n q h (by omega),row_before n q h (by omega)]

/-- The excess of horizon over seven times weight is independent of n. -/
theorem suffix_weight (n q w : Nat) (hn : 0<n) :
    wt (cut n+w) (row n q) = n+2+cnt q.testBit w := by
  unfold wt
  rw [count_split _ (cut n) w,count_prefix n q (cut n) (by omega),cnt_seed n hn,Nat.min_self]
  rw [show (fun j=>(row n q).testBit (cut n+j))=q.testBit by
    funext j;exact row_after n q j hn]
  obtain ⟨m,rfl⟩ : ∃ m, n=m+1 := ⟨n-1,by omega⟩
  rw [count_init]

/-- The seed fits in the advertised horizon exactly when its suffix fits in w bits. -/
theorem suffix_fits (n q w : Nat) (hn : 0<n) :
    row n q<2^(cut n+w) ↔ q<2^w := by
  constructor
  · intro h
    apply Nat.lt_pow_two_of_testBit
    intro j hj
    rw [← row_after n q j hn]
    apply Nat.testBit_lt_two_pow
    exact Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by omega))
  · intro h
    apply Nat.lt_pow_two_of_testBit
    intro j hj
    have e : j=cut n+(j-cut n) := by omega
    rw [e,row_after n q (j-cut n) hn]
    apply Nat.testBit_lt_two_pow
    exact Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by omega))

end Suffix


namespace Suffix

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 20000

private theorem concrete_row : row 2635 (2^17) = Certificates.seed2635 := by decide +kernel

/-- Every M gives a valid finite prefix of length H at least M with H=7A+9. -/
theorem arbitrarily_late_excess_nine (M : Nat) :
    ∃ H Y, M≤H ∧ Y<2^H ∧ GWord (tr Y) H ∧ H=7*wt H Y+9 := by
  let n:=2635+M*jump 29
  have hn : 0<n := by dsimp [n];omega
  have hj : jump 29=4294967296 := by decide
  have hg : GWord (tr (row 2635 (2^17))) (cut 2635+29) := by
    rw [concrete_row]
    exact Certificates.counterexample2635.1
  have hnew:= (suffix_word_multiples 2635 (2^17) 29 M (by decide)).2 hg
  have wc : cnt (2^17:Nat).testBit 29=1 := by decide +kernel
  refine ⟨cut n+29,row n (2^17),?_,(suffix_fits n _ _ hn).2 (by decide),hnew,?_⟩
  · dsimp [cut,n]; rw [hj]; omega
  · rw [suffix_weight n _ _ hn,wc]
    unfold cut;omega


/-- Even horizons can also be arbitrarily large, with excess eight. -/
theorem arbitrarily_late_even_excess_eight (M : Nat) :
    ∃ m Y, M ≤ 2 * m ∧ Y < 2 ^ (2 * m) ∧ GWord (tr Y) (2 * m) ∧
      2 * m = 7 * wt (2 * m) Y + 8 := by
  let n := 2635 + M * jump 28
  have hn : 0 < n := by dsimp [n]; omega
  have hj : jump 28 = 2147483648 := by decide
  have hbase : GWord (tr (row 2635 (2^17))) (cut 2635 + 28) := by
    rw [concrete_row]
    exact fun t ht => Certificates.counterexample2635.1 t (by change t < 18474 at ht; omega)
  have hword := (suffix_word_multiples 2635 (2^17) 28 M (by decide)).2 hbase
  have hbits := (suffix_fits n (2^17) 28 hn).2 (by decide)
  have hweight := suffix_weight n (2^17) 28 hn
  have hcount : cnt (2^17 : Nat).testBit 28 = 1 := by decide +kernel
  rw [hcount] at hweight
  have heven : 2 * ((cut n + 28) / 2) = cut n + 28 := by
    dsimp [cut, n]; rw [hj]; omega
  refine ⟨(cut n + 28) / 2, row n (2^17), ?_⟩
  rw [heven]
  refine ⟨?_, hbits, hword, ?_⟩
  · dsimp [cut, n]; rw [hj]; omega
  · rw [hweight]; unfold cut; omega

/-- Every linear mass floor has slope at least seven. At slope seven its
additive constant is at least nine. -/
theorem necessary_mass_floor_parameters (q d : Nat) (h : MassFloor q d) :
    7 ≤ q ∧ (q = 7 → 9 ≤ d) := by
  obtain ⟨H, Y, hH, hY, hG, heq⟩ := arbitrarily_late_excess_nine (7 * d + 10)
  have hb := h H Y hY hG
  constructor
  · by_cases hq : 7 ≤ q
    · exact hq
    · have hsmall : q ≤ 6 := by omega
      have hw := Nat.mul_le_mul_right (wt H Y) hsmall
      omega
  · intro hq
    subst q
    omega

end Suffix

/-- The concrete even prefix also directly refutes the two catalog conjectures. -/
theorem sharp_mass_conjectures_false : ¬ ConjS ∧ ¬ ConjSEven :=
  ⟨Certificates.sharp_mass_conjectures_false.1, Certificates.sharp_mass_conjectures_false.2.1⟩

end Ruliology.CellularAutomata.Rule30MassCounterexamples
