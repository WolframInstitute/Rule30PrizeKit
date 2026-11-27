module

public import Ruliology.CellularAutomata.Rule30SidewaysLocks

/-!
# Two exact forcing thresholds beside an alternating Rule 30 column
Author display name: onebluecloud. AI collaborator: OpenAI Codex (GPT-6).
The sharp thresholds supplement Herbert et al.'s two ether families and reuse
Quint and Gemini's 19-cell period-two lock. The proof establishes finite-depth
transfer for arbitrary available windows and two exact thresholds for all completions.
-/

@[expose] public section

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Ruliology.CellularAutomata.Rule30SharpPrefixes

open Rule30StripCertificates (lin3 seg seg_succ)
open Rule30Ether (drv drv_col0 drv_init rowOf rowOf_head)
open Rule30PeriodTwoCoupled (altCol)
open Rule30PeriodTwoSideways (u)

/-- Cell `1` is the low bit. Nothing is assumed about cells above the prefix. -/
def Prefix (seed k : Nat) (R : Nat → Bool) : Prop :=
  ∀ i, i < k → R (i + 1) = seed.testBit i

def tone (q : Nat) : Bool := decide (q % 2 = 1)

/-- For every completion, read the right neighbour at all white ticks. -/
def Forces (seed k : Nat) : Prop :=
  ∀ R, Prefix seed k R → ∀ q, u R q = tone q

def win (R : Nat → Bool) (t w : Nat) := rowOf (drv altCol R) t 0 w
private def decode (w n : Nat) := seg (fun i => n.testBit i) w
abbrev advance := Rule30SidewaysLocks.dstep

private theorem extendWin (R : Nat → Bool) (t w : Nat) :
    win R t (w + 1) = win R t w ++ [drv altCol R t (w + 1)] := by
  unfold win rowOf
  simp only [seg_succ, Nat.zero_add]

private theorem nextWin (R : Nat → Bool) (q w : Nat) :
    win R (2*(q+1)+1) w =
      advance (win R (2*q+1) w) (drv altCol R (2*q+1) (w+1))
        (drv altCol R (2*q+1) (w+2)) := by
  rw [show 2*(q+1)+1=2*q+1+2 by omega]
  exact Rule30SidewaysLocks.winW_dstep w R (2*q+1) (by omega)

private theorem headWin (R : Nat → Bool) (q v : Nat) :
    (win R (2*q+1) (v+1)).headD false = u R q :=
  rowOf_head _ _ 0 v

def succs (s : List Bool) : List (List Bool) :=
  [advance s false false, advance s false true,
   advance s true false, advance s true true].eraseDups

private theorem advanceMem (s : List Bool) (a b : Bool) : advance s a b ∈ succs s := by
  cases a <;> cases b <;> simp [succs]

private theorem nextMem (R : Nat → Bool) (q w : Nat) :
    win R (2*(q+1)+1) w ∈ succs (win R (2*q+1) w) := by
  rw [nextWin]
  apply advanceMem

def terminal (b : Bool) :=
  Rule30SidewaysLocks.cls 19 Rule30SidewaysLocks.lock2Codes (if b then 0 else 1)

def Good (R : Nat → Bool) (q : Nat) : Prop :=
  ∀ n, u R (q+n) = tone (q+n)

private theorem terminalGood (R : Nat → Bool) (q : Nat)
    (h : win R (2*q+1) 19 ∈ terminal (tone q)) : Good R q := by
  intro n
  rcases Nat.mod_two_eq_zero_or_one q with hq | hq
  · have hh : Rule30SidewaysLocks.winW 19 R (2*q+1) ∈
        Rule30SidewaysLocks.cls 19 Rule30SidewaysLocks.lock2Codes 1 := by
      simpa [terminal, tone, hq, win, Rule30SidewaysLocks.winW] using h
    have hn := Rule30SidewaysLocks.u_of_lock (V := 18) Rule30SidewaysLocks.lock2_ok
      (by decide) R (s0 := q) (k := 1) (by decide) hh n
    rw [Rule30SidewaysLocks.word2_mod_two] at hn
    have e : (1+n)%2=0 ↔ (q+n)%2=1 := by omega
    simpa only [tone, e] using hn
  · have hh : Rule30SidewaysLocks.winW 19 R (2*q+1) ∈
        Rule30SidewaysLocks.cls 19 Rule30SidewaysLocks.lock2Codes 0 := by
      simpa [terminal, tone, hq, win, Rule30SidewaysLocks.winW] using h
    have hn := Rule30SidewaysLocks.u_of_lock (V := 18) Rule30SidewaysLocks.lock2_ok
      (by decide) R (s0 := q) (k := 0) (by decide) hh n
    rw [Rule30SidewaysLocks.word2_mod_two] at hn
    have e : (0+n)%2=0 ↔ (q+n)%2=1 := by omega
    simpa only [tone, e] using hn

private theorem takeSeg : ∀ (w k : Nat) (f : Nat → Bool), k ≤ w →
    (seg f w).take k = seg f k
  | _, 0, _, _ => rfl
  | 0, _+1, _, h => by omega
  | w+1, k+1, f, h => by
    change f 0 :: (seg (fun i => f (i+1)) w).take k = f 0 :: seg (fun i => f (i+1)) k
    rw [takeSeg w k _ (by omega)]

def hit (q : Nat) (s : List Bool) : Bool :=
  (terminal (tone q)).contains (s.take 19)

private theorem hitGood (R : Nat → Bool) (q v : Nat) (hw : 19 ≤ v+1)
    (h : hit q (win R (2*q+1) (v+1)) = true) : Good R q := by
  have hh := List.contains_iff_mem.1 h
  have e : (win R (2*q+1) (v+1)).take 19 = win R (2*q+1) 19 := by
    unfold win rowOf
    exact takeSeg _ _ _ hw
  exact terminalGood R q (e ▸ hh)

/-- Finite-depth transfer to the known permanent lock, with all exterior bits free. -/
def cert : Nat → Nat → List Bool → Bool
  | 0, q, s => hit q s
  | f+1, q, s => hit q s ||
      ((s.headD false == tone q) && (succs s).all (cert f (q+1)))

theorem certified (R : Nat → Bool) (v : Nat) (hw : 19 ≤ v+1) (fuel q : Nat)
    (h : cert fuel q (win R (2*q+1) (v+1)) = true) : Good R q := by
  induction fuel generalizing q with
  | zero => exact hitGood R q v hw h
  | succ f ih =>
    simp only [cert, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with entry | ⟨out,step⟩
    · exact hitGood R q v hw entry
    · have hn := ih (q+1) (List.all_eq_true.1 step _ (nextMem R q (v+1)))
      intro n
      cases n with
      | zero => simpa using (headWin R q v).symm.trans out
      | succ n =>
        have hh := hn n
        rw [show q+n.succ=q+1+n by omega]
        exact hh

private theorem initPrefix {seed k : Nat} {R : Nat → Bool} (h : Prefix seed k R) :
    win R 0 k = decode k seed := by
  exact Rule30SidewaysLocks.rowOf_zero_prefix h

private theorem extendZero (R : Nat → Bool) (w : Nat) :
    win R 0 (w+1) = win R 0 w ++ [R (w+1)] := by
  rw [extendWin, drv_init _ _ _ (by omega)]

private theorem tickOne (R : Nat → Bool) (w : Nat) :
    win R 1 w = lin3 (true :: win R 0 (w+1)) :=
  Rule30GateTrap.rowOf_evolve R 1 0 w

private theorem checked31 (a b c : Bool) :
    cert 12 0 (lin3 (true :: (decode 23 31 ++ [a,b,c]))) = true := by
  cases a <;> cases b <;> cases c <;> decide +kernel

private theorem checked495 (a : Bool) :
    cert 6 0 (lin3 (true :: (decode 20 495 ++ [a]))) = true := by
  cases a <;> decide +kernel

theorem prefix31_sufficient : Forces 31 23 := by
  intro R h q
  have e := tickOne R 25
  rw [extendZero R 25, extendZero R 24, extendZero R 23, initPrefix h] at e
  simp only [List.append_assoc, List.singleton_append] at e
  have k : cert 12 0 (win R 1 25) = true := by rw [e]; exact checked31 _ _ _
  simpa using certified R 24 (by decide) 12 0 k q

theorem prefix495_sufficient : Forces 495 20 := by
  intro R h q
  have e := tickOne R 20
  rw [extendZero R 20, initPrefix h] at e
  have k : cert 6 0 (win R 1 20) = true := by rw [e]; exact checked495 _
  simpa using certified R 19 (by decide) 6 0 k q

private def seedRow (z : Nat) (j : Nat) : Bool := z.testBit (j-1)

private theorem finiteTrace (z q : Nat) :
    u (seedRow z) q =
      (Rule30GateTrap.evolve 0 (2*q+1) (decode (1+(2*q+1)) z)).headD false := by
  have hp : Prefix z (1+(2*q+1)) (seedRow z) := by intro i _; simp [seedRow]
  have e := Rule30GateTrap.rowOf_evolve (seedRow z) (2*q+1) 0 1
  change win (seedRow z) (0+(2*q+1)) 1 =
      Rule30GateTrap.evolve 0 (2*q+1) (win (seedRow z) 0 (1+(2*q+1))) at e
  rw [Nat.zero_add, initPrefix hp] at e
  exact (headWin (seedRow z) q 0).symm.trans (congrArg (fun s : List Bool => s.headD false) e)

private theorem witness31 : Prefix 31 22 (seedRow 4194335) ∧
    u (seedRow 4194335) 31 ≠ tone 31 := by
  constructor
  · have e : ∀ i : Fin 22, (4194335 : Nat).testBit i.val = (31 : Nat).testBit i.val := by decide +kernel
    intro i hi
    simpa [seedRow] using e ⟨i,hi⟩
  · rw [finiteTrace]; decide +kernel

private theorem witness495 : Prefix 495 19 (seedRow 35127791) ∧
    u (seedRow 35127791) 37 ≠ tone 37 := by
  constructor
  · have e : ∀ i : Fin 19, (35127791 : Nat).testBit i.val = (495 : Nat).testBit i.val := by decide +kernel
    intro i hi
    simpa [seedRow] using e ⟨i,hi⟩
  · rw [finiteTrace]; decide +kernel

/-- The 31 family forces the visible alternating word exactly at lengths at least 23. -/
theorem sharp31 (k : Nat) : Forces 31 k ↔ 23 ≤ k := by
  constructor
  · intro h
    by_cases hk : 23 ≤ k
    · exact hk
    · exact False.elim (witness31.2 (h _ (fun i hi => witness31.1 i (by omega)) 31))
  · intro h R hp
    exact prefix31_sufficient R (fun i hi => hp i (by omega))

/-- The 495 family forces the visible alternating word exactly at lengths at least 20. -/
theorem sharp495 (k : Nat) : Forces 495 k ↔ 20 ≤ k := by
  constructor
  · intro h
    by_cases hk : 20 ≤ k
    · exact hk
    · exact False.elim (witness495.2 (h _ (fun i hi => witness495.1 i (by omega)) 37))
  · intro h R hp
    exact prefix495_sufficient R (fun i hi => hp i (by omega))

/-- An exterior pair at an odd sample encodes the two cells immediately beyond the window. -/
def freeRun (s : List Bool) (pairs : List Nat) : List Bool :=
  pairs.foldl (fun w p => advance w (p.testBit 0) (p.testBit 1)) s

/-- Thirty-nine legal two-tick moves of the 24-cell finite-window relaxation. -/
def boundaryPairs : List Nat :=
  [0,0,1,0,2,0,0,1,0,0,0,1,1,1,1,1] ++ List.replicate 23 0

/-- The width-24 relaxation admits a false white reading at tick 79, even
from the genuine tick-1 window of a right half in the sharp 23-cell family. -/
theorem width24_separation :
    ∃ R : Nat → Bool, Prefix 31 23 R ∧ u R 39 = true ∧
      boundaryPairs.length = 39 ∧
      (freeRun (win R 1 24) boundaryPairs).headD false = false := by
  refine ⟨seedRow 8388639, ?_⟩
  have hp : Prefix 31 23 (seedRow 8388639) := by
    have e : ∀ i : Fin 23, (8388639 : Nat).testBit i.val = (31 : Nat).testBit i.val := by
      decide +kernel
    intro i hi
    simpa [seedRow] using e ⟨i,hi⟩
  refine ⟨hp, (prefix31_sufficient _ hp 39).trans (by decide), by decide, ?_⟩
  decide +kernel

end Ruliology.CellularAutomata.Rule30SharpPrefixes
