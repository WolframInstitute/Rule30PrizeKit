module

public import Ruliology.CellularAutomata.Rule30ZeroBoundary

/-!
# Uniform spatial period lifting in sideways Rule 30 reconstruction

Write a pair of consecutive cells as a state in `Fin 4`. The next spatial
state, driven by the cell on the next temporal row, is
`(a,b) ↦ (b, u XOR (b OR a))` (`step_encode`).

The two transfer maps generate 41 transformations. Of these, 37 occur
for words containing a white driver cell. Their closure and the identity
`F^5=F^3` are kernel checked. Induction on arbitrary words makes this a
statement for every block length, rather than a fixed-width certificate.

`stateAt_period` proves that a periodic driver with period p and a white
cell yields spatial period 2p after at most 3p steps, for any initial pair.
`recon_period_lift` connects this directly to the official `recon`: if row
t+1 has period p after depth D+1, and its period contains a white cell,
row t has period 2p after depth D+3p. Both p and D are unbounded.

The result permits successive period doublings. The white-cell hypothesis
is necessary: the all-black driver transfer has a three-cycle.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30SpatialPeriodLifting

abbrev State := Fin 4
abbrev Code := State × State × State × State

def step (u : Bool) (s : State) : State :=
  match s.val with
  | 0 => if u then 1 else 0
  | 1 => if u then 2 else 3
  | 2 => if u then 0 else 1
  | _ => if u then 2 else 3

def encode (a b : Bool) : State :=
  if a then (if b then 3 else 2) else (if b then 1 else 0)

theorem step_encode (u a b : Bool) :
    step u (encode a b) = encode b (xor u (b || a)) := by
  cases u <;> cases a <;> cases b <;> rfl

def eval (c : Code) (s : State) : State :=
  match s.val with
  | 0 => c.1
  | 1 => c.2.1
  | 2 => c.2.2.1
  | _ => c.2.2.2

def post (u : Bool) (c : Code) : Code :=
  (step u c.1, step u c.2.1, step u c.2.2.1, step u c.2.2.2)

theorem eval_post (u : Bool) (c : Code) (s : State) :
    eval (post u c) s = step u (eval c s) := by
  obtain ⟨s, hs⟩ := s
  have h : s=0 ∨ s=1 ∨ s=2 ∨ s=3 := by omega
  rcases h with rfl | rfl | rfl | rfl <;> rfl

def oneCodes : List Code := [
  (0, 1, 2, 1),
  (0, 1, 2, 3),
  (1, 2, 0, 2),
  (2, 0, 1, 0)
]

def zeroCodes : List Code := [
  (0, 0, 0, 0),
  (0, 0, 1, 0),
  (0, 0, 2, 0),
  (0, 0, 3, 0),
  (0, 1, 0, 1),
  (0, 1, 1, 1),
  (0, 2, 0, 2),
  (0, 2, 2, 2),
  (0, 3, 0, 3),
  (0, 3, 1, 3),
  (0, 3, 3, 3),
  (1, 0, 0, 0),
  (1, 0, 1, 0),
  (1, 0, 3, 0),
  (1, 1, 0, 1),
  (1, 1, 1, 1),
  (1, 1, 2, 1),
  (1, 1, 3, 1),
  (1, 2, 1, 2),
  (1, 2, 2, 2),
  (1, 3, 1, 3),
  (1, 3, 3, 3),
  (2, 0, 0, 0),
  (2, 0, 2, 0),
  (2, 1, 1, 1),
  (2, 1, 2, 1),
  (2, 2, 0, 2),
  (2, 2, 1, 2),
  (2, 2, 2, 2),
  (3, 0, 0, 0),
  (3, 0, 3, 0),
  (3, 1, 0, 1),
  (3, 1, 1, 1),
  (3, 1, 3, 1),
  (3, 3, 0, 3),
  (3, 3, 1, 3),
  (3, 3, 3, 3)
]

theorem zero_checked : zeroCodes.all (fun c => [false,true].all
    (fun b => zeroCodes.contains (post b c))) = true := by decide

theorem one_true_checked : oneCodes.all
    (fun c => oneCodes.contains (post true c)) = true := by decide

theorem one_false_checked : oneCodes.all
    (fun c => zeroCodes.contains (post false c)) = true := by decide

theorem zero_closed (c : Code) (hc : c ∈ zeroCodes) (b : Bool) :
    post b c ∈ zeroCodes := by
  have h := List.all_eq_true.mp zero_checked c hc
  have hb : b ∈ [false,true] := by cases b <;> simp
  exact List.contains_iff_mem.mp (List.all_eq_true.mp h b hb)

theorem one_true (c : Code) (hc : c ∈ oneCodes) : post true c ∈ oneCodes :=
  List.contains_iff_mem.mp (List.all_eq_true.mp one_true_checked c hc)

theorem one_false (c : Code) (hc : c ∈ oneCodes) : post false c ∈ zeroCodes :=
  List.contains_iff_mem.mp (List.all_eq_true.mp one_false_checked c hc)

def wordCode : List Bool → Code
  | [] => (0,1,2,3)
  | b::w => post b (wordCode w)

def runWord : List Bool → State → State
  | [], s => s
  | b::w, s => step b (runWord w s)

theorem eval_word (w : List Bool) (s : State) : eval (wordCode w) s = runWord w s := by
  induction w with
  | nil =>
    obtain ⟨s,hs⟩ := s
    have h : s=0 ∨ s=1 ∨ s=2 ∨ s=3 := by omega
    rcases h with rfl | rfl | rfl | rfl <;> rfl
  | cons b w ih => simpa [wordCode,runWord,eval_post] using congrArg (step b) ih

theorem word_class (w : List Bool) :
    (wordCode w ∈ oneCodes ∧ false ∉ w) ∨
    (wordCode w ∈ zeroCodes ∧ false ∈ w) := by
  induction w with
  | nil => exact Or.inl ⟨by decide, by simp⟩
  | cons b w ih =>
    rcases ih with ⟨hc,hz⟩ | ⟨hc,hz⟩
    · cases b with
      | false => exact Or.inr ⟨one_false _ hc, by simp⟩
      | true => exact Or.inl ⟨one_true _ hc, by simp [hz]⟩
    · exact Or.inr ⟨zero_closed _ hc b, by simp [hz]⟩

def power (f : State → State) : Nat → State → State
  | 0, s => s
  | n+1, s => f (power f n s)

theorem power_checked : zeroCodes.all (fun c => ([0,1,2,3] : List State).all
    (fun s => power (eval c) 5 s == power (eval c) 3 s)) = true := by decide

theorem zero_power (c : Code) (hc : c ∈ zeroCodes) (s : State) :
    power (eval c) 5 s = power (eval c) 3 s := by
  have h := List.all_eq_true.mp power_checked c hc
  have hs : s ∈ ([0,1,2,3] : List State) := by
    obtain ⟨s,hs⟩ := s
    have h : s=0 ∨ s=1 ∨ s=2 ∨ s=3 := by omega
    rcases h with rfl | rfl | rfl | rfl <;> simp
  exact beq_iff_eq.mp (List.all_eq_true.mp h s hs)

/-- Every finite driver block containing a zero settles after three block
applications to a cycle of period dividing two. No bound on block length. -/
theorem word_power (w : List Bool) (hz : false ∈ w) (s : State) :
    power (runWord w) 5 s = power (runWord w) 3 s := by
  have hc : wordCode w ∈ zeroCodes := by
    rcases word_class w with ⟨_,h⟩ | ⟨h,_⟩
    · exact False.elim (h hz)
    · exact h
  have hf : eval (wordCode w) = runWord w := funext (eval_word w)
  simpa [hf] using zero_power _ hc s

theorem word_power_period (w : List Bool) (hz : false ∈ w)
    (k : Nat) (hk : 3 ≤ k) (s : State) :
    power (runWord w) (k+2) s = power (runWord w) k s := by
  obtain ⟨n,rfl⟩ : ∃ n, k=3+n := ⟨k-3,by omega⟩
  clear hk
  induction n with
  | zero => exact word_power w hz s
  | succ n ih => simpa [Nat.add_assoc,power] using congrArg (runWord w) ih

open Ruliology.CellularAutomata.Rule30ZeroBoundary

def stateAt (u : Nat → Bool) (s : State) : Nat → State
  | 0 => s
  | n+1 => step (u n) (stateAt u s n)

def inputWord (u : Nat → Bool) : Nat → List Bool
  | 0 => []
  | n+1 => u n :: inputWord u n

theorem run_input (u : Nat → Bool) (n : Nat) (s : State) :
    runWord (inputWord u n) s = stateAt u s n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [inputWord,runWord,stateAt] using congrArg (step (u n)) ih

theorem input_zero (u : Nat → Bool) (n i : Nat) (hi : i<n) (hu : u i=false) :
    false ∈ inputWord u n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : i=n
    · simp [inputWord,←h,hu]
    · have h' : i<n := by omega
      exact List.mem_cons_of_mem _ (ih h')

theorem stateAt_shift (u : Nat → Bool) (s : State) (n k : Nat) :
    stateAt u s (n+k) = stateAt (fun j => u (n+j)) (stateAt u s n) k := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [Nat.add_assoc,stateAt] using congrArg (step (u (n+k))) ih

theorem period_mul (u : Nat → Bool) (p : Nat) (hp : ∀ n, u (n+p)=u n)
    (k j : Nat) : u (k*p+j)=u j := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show (k+1)*p+j=(k*p+j)+p by rw [Nat.add_mul]; simp only [Nat.one_mul]; omega,hp,ih]

theorem stateAt_blocks (u : Nat → Bool) (p : Nat) (hp : ∀ n, u (n+p)=u n)
    (s : State) (k : Nat) :
    stateAt u s (k*p) = power (fun q => stateAt u q p) k s := by
  induction k with
  | zero => simp [stateAt,power]
  | succ k ih =>
    rw [show (k+1)*p=k*p+p by simp [Nat.add_mul],stateAt_shift]
    have hu : (fun j => u (k*p+j))=u := funext (period_mul u p hp k)
    rw [hu,ih]
    rfl

/-- A periodic binary driver with a zero gives an eventual period dividing
twice its own period, with transient at most three driver blocks. -/
theorem stateAt_period (u : Nat → Bool) (p : Nat)
    (hp : ∀ n, u (n+p)=u n) (hz : ∃ i, i<p ∧ u i=false)
    (s : State) (n : Nat) (hn : 3*p≤n) :
    stateAt u s (n+2*p)=stateAt u s n := by
  obtain ⟨i,hi,hui⟩ := hz
  have hword := input_zero u p i hi hui
  have hf : runWord (inputWord u p) = fun q => stateAt u q p := funext (run_input u p)
  have hb : stateAt u s (5*p)=stateAt u s (3*p) := by
    rw [stateAt_blocks u p hp,stateAt_blocks u p hp]
    simpa [hf] using word_power (inputWord u p) hword s
  obtain ⟨j,rfl⟩ : ∃ j, n=3*p+j := ⟨n-3*p,by omega⟩
  rw [show 3*p+j+2*p=5*p+j by omega,stateAt_shift,stateAt_shift]
  have hu5 : (fun j => u (5*p+j))=u := funext (period_mul u p hp 5)
  have hu3 : (fun j => u (3*p+j))=u := funext (period_mul u p hp 3)
  rw [hu5,hu3,hb]

theorem encode_injective (a b c d : Bool) :
    encode a b = encode c d ↔ a=c ∧ b=d := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

def rowDriver (a : Nat → Bool) (D t : Nat) (n : Nat) : Bool :=
  recon a (D+n+1) (t+1)

theorem recon_stateAt (a : Nat → Bool) (D t n : Nat) :
    stateAt (rowDriver a D t) (encode (recon a D t) (recon a (D+1) t)) n =
    encode (recon a (D+n) t) (recon a (D+n+1) t) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [stateAt,ih,step_encode]
    simp only [rowDriver]
    simpa [Nat.add_assoc] using congrArg (encode (recon a (D+n+1) t))
      (recon_two a (D+n) t).symm

/-- Uniform spatial period lifting for the official sideways reconstruction:
if row t+1 has period p after depth D+1 and has a white cell in that block,
row t has period 2p after depth D+3p. -/
theorem recon_period_lift (a : Nat → Bool) (D t p : Nat)
    (hp : ∀ n, recon a (D+n+p+1) (t+1)=recon a (D+n+1) (t+1))
    (hz : ∃ i, i<p ∧ recon a (D+i+1) (t+1)=false)
    (n : Nat) (hn : 3*p≤n) :
    recon a (D+n+2*p) t = recon a (D+n) t := by
  have hup : ∀ n, rowDriver a D t (n+p)=rowDriver a D t n := by
    intro n
    simpa [rowDriver,Nat.add_assoc] using hp n
  have huz : ∃ i, i<p ∧ rowDriver a D t i=false := hz
  have h := stateAt_period (rowDriver a D t) p hup huz
    (encode (recon a D t) (recon a (D+1) t)) n hn
  rw [recon_stateAt,recon_stateAt] at h
  have h' := (encode_injective _ _ _ _).mp h
  simpa [Nat.add_assoc] using h'.1


end Ruliology.CellularAutomata.Rule30SpatialPeriodLifting
