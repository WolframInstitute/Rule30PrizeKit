module

public import Ruliology.CellularAutomata.Rule30Prize
public import Ruliology.CellularAutomata.Rule30Jen
public import Ruliology.CellularAutomata.Rule30Realization
public import Ruliology.CellularAutomata.Rule30Diagonals

/-!
# A sharp left-edge width for six earlier Rule 30 generations

At age at least 110, the first 81 cells of the singleton force the twelve
vacuum bits in a six-step inverse, for every choice of the twelve bits at
the other end of the window. This gives a finite ancestor for every finite
suffix attached to that prefix. At ages 189 + 8k an 80-cell prefix has a
finite continuation for which this fails, obtained by changing only offsets 80 and 83.

The cone on thirteen input cells is permutive in the first cell. Reading one
output bit from right to left therefore recovers that input from the other
twelve. The finite certificate evaluates this operation simultaneously on
all 4096 Boolean assignments, with one bit per assignment in a natural
number. The singleton's 88-cell moving prefix repeats after eight steps
from age 127. The intervening ages starting at 110 are checked separately.
-/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30SixStepEdge

open Rule30Jen

def layer (f : α → α → α → α) (a b : α) : List α → List α
  | [] => []
  | c :: cs => f a b c :: layer f b c cs

def triangle (f : α → α → α → α) : Nat → List α → List α
  | 0, xs => xs
  | n+1, a :: b :: cs => triangle f n (layer f a b cs)
  | _+1, _ => []

private theorem layer_map (g : α → β) (f : α → α → α → α) (f' : β → β → β → β)
    (ok : ∀ a b c, g (f a b c) = f' (g a) (g b) (g c)) (a b : α) (cs : List α) :
    (layer f a b cs).map g = layer f' (g a) (g b) (cs.map g) := by
  induction cs generalizing a b with
  | nil => rfl
  | cons c cs ih => simp [layer, ok, ih]

private theorem triangle_map (g : α → β) (f : α → α → α → α) (f' : β → β → β → β)
    (ok : ∀ a b c, g (f a b c) = f' (g a) (g b) (g c)) (n : Nat) (xs : List α) :
    (triangle f n xs).map g = triangle f' n (xs.map g) := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    cases xs with
    | nil => rfl
    | cons a rest =>
      cases rest with
      | nil => rfl
      | cons b cs => simp [triangle, ih, layer_map g f f' ok]

-- Guess a white leftmost input, evaluate the six-step cone, and XOR
-- with the observed bit to recover the required leftmost input.
def recover (f : α → α → α → α) (add : α → α → α) (zero : α)
    (obs : α) (reg : List α) : List α :=
  add obs ((triangle f 6 (zero :: reg)).headD zero) :: reg.take 11

def scan (pull : Bool → List α → List α) (word : Nat) : Nat → List α → List α
  | 0, s => s
  | k+1, s => scan pull word k (pull (word.testBit k) s)

def rewind (word width : Nat) (reg : List Bool) : List Bool :=
  scan (recover rule xor false) word width reg

private def laneRule (a b c : Nat) := a ^^^ (b ||| c)
set_option exponentiation.threshold 5000
private def ones : Nat := 2^4096-1
private def lanePull (b : Bool) := recover laneRule (· ^^^ ·) 0 (if b then ones else 0)

private theorem lane_pull (i : Nat) (hi : i < 4096) (b : Bool) (s : List Nat) :
    (lanePull b s).map (fun x => x.testBit i) =
      recover rule xor false b (s.map (fun x => x.testBit i)) := by
  let g := fun (x : Nat) => x.testBit i
  have gate (a b c : Nat) : g (laneRule a b c) = rule (g a) (g b) (g c) := by
    simp [g,laneRule,rule,Nat.testBit_xor,Nat.testBit_or]
  have ht := triangle_map g laneRule rule gate 6 (0::s)
  have hd := congrArg (fun xs => xs.headD false) ht
  simp [g] at hd
  have hb : (if b then ones else 0).testBit i = b := by
    cases b
    · simp
    · change (2^4096-1).testBit i = true
      rw [Nat.testBit_two_pow_sub_one]
      exact decide_eq_true hi
  simp [lanePull,recover,Nat.testBit_xor,hb]
  rw [← hd]
  cases (triangle laneRule 6 (0 :: s)).head? <;> simp

private theorem scan_map (word i : Nat) (hi : i < 4096) (n : Nat) (s : List Nat) :
    (scan lanePull word n s).map (fun x => x.testBit i) =
      rewind word n (s.map (fun x => x.testBit i)) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simpa only [scan,rewind,lane_pull i hi] using ih (lanePull (word.testBit n) s)

private def duplicate (n p : Nat) :=
  p % 2^n ||| ((p % 2^n) <<< n)

private def variables : Nat → List Nat
  | 0 => []
  | k+1 =>
    let n := 2^k
    ((2^n-1) <<< n) :: (variables k).map (duplicate n)

private theorem lanes_cover (xs : List Bool) :
    ∃ i < 2^xs.length, (variables xs.length).map (fun x => x.testBit i) = xs := by
  induction xs with
  | nil => exact ⟨0,by decide,rfl⟩
  | cons b xs ih =>
    obtain ⟨i,hi,eq⟩ := ih
    let n := 2^xs.length
    have lt : i < n := hi
    cases b
    · refine ⟨i,by simp [Nat.pow_succ]; omega,?_⟩
      simp [variables,List.map_map,duplicate,Nat.testBit_shiftLeft,Nat.testBit_or,
        Nat.not_le_of_lt hi,hi,Function.comp_def,eq]
    · refine ⟨n+i,by simp [Nat.pow_succ]; dsimp [n] at *; omega,?_⟩
      have ge : 2^xs.length ≤ n+i := by dsimp [n]; omega
      have ng : ¬ n+i < 2^xs.length := by omega
      have sub : n+i-2^xs.length=i := by dsimp [n]; omega
      simp [variables,List.map_map,duplicate,Nat.testBit_shiftLeft,Nat.testBit_or,
        ge,ng,sub,hi,Function.comp_def,eq]

-- Packed singleton in coordinates measured inward from the moving left edge.
def leftWord : Nat → Nat
  | 0 => 1
  | t+1 =>
    let w := leftWord t
    ((w <<< 2) ^^^ ((w <<< 1) ||| w)) % 2^88

private theorem cycle (t : Nat) : leftWord (127+t) = leftWord (135+t) := by
  induction t with
  | zero => decide +kernel
  | succ t ih => exact congrArg (fun w : Nat => ((w <<< 2) ^^^ ((w <<< 1) ||| w)) % 2^88) ih

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem finite_certificate : ∀ k : Fin 25,
    scan lanePull (leftWord (110+k.val)) 81 (variables 12) = List.replicate 12 0 := by
  decide +kernel

/-- At every age from 110, all 4096 terminal six-step registers rewind to
the twelve vacuum cells on the left when the genuine 81 edge bits are read. -/
theorem six_step_reset (t : Nat) (ht : 110 ≤ t) (reg : List Bool) (len : reg.length=12) :
    rewind (leftWord t) 81 reg = List.replicate 12 false := by
  have values (a : Nat) (ha : 110 ≤ a) :
      scan lanePull (leftWord a) 81 (variables 12) = List.replicate 12 0 := by
    induction a using Nat.strongRecOn with
    | ind a ih =>
      by_cases low : a < 135
      · let k : Fin 25 := ⟨a-110,by omega⟩
        simpa only [show 110+k.val=a by dsimp [k]; omega] using finite_certificate k
      · have eq := cycle (a-135)
        rw [show 135+(a-135)=a by omega,show 127+(a-135)=a-8 by omega] at eq
        rw [← eq]
        exact ih (a-8) (by omega) (by omega)
  obtain ⟨i,hi,hreg⟩ := lanes_cover reg
  rw [len] at hi hreg
  have result := scan_map (leftWord t) i hi 81 (variables 12)
  rw [values t ht,hreg] at result
  simpa using result.symm

private theorem real_edge (t : Nat) (j : Int) (hi : j < 88) :
    cell t (j-t) = if 0 ≤ j then (leftWord t).testBit j.toNat else false := by
  induction t generalizing j with
  | zero =>
    by_cases h : j=0
    · subst j; decide
    · by_cases neg : j<0
      · rw [cell_eq_false_of_lt _ _ (by omega),ite_eq_right (by omega)]
      · simp [cell,leftWord,h,show 0 ≤ j by omega]
        rw [show (1 : Nat)=2^0 by decide,Nat.testBit_two_pow]
        simp [show 0 ≠ j.toNat by omega]
  | succ t ih =>
    by_cases neg : j<0
    · rw [cell_eq_false_of_lt _ _ (by omega),ite_eq_right (by omega)]
    · rw [cell,show j-((t+1 : Nat) : Int)-1=(j-2)-t by omega,
        show j-((t+1 : Nat) : Int)=(j-1)-t by omega,
        show j-1-(t : Int)+1=j-t by omega, ih (j-2) (by omega),
        ih (j-1) (by omega),ih j hi]
      have hk : j.toNat < 88 := by omega
      simp only [leftWord,Nat.testBit_mod_two_pow,hk,decide_true,Bool.true_and,
        Nat.testBit_xor,Nat.testBit_or,Nat.testBit_shiftLeft,rule]
      by_cases low : j<2
      · obtain rfl | rfl : j=0 ∨ j=1 := by omega
        all_goals simp
      · simp [show 0 ≤ j by omega,show 1 ≤ j by omega,show 2 ≤ j by omega,
          show 2 ≤ j.toNat by omega,show 1 ≤ j.toNat by omega,
          show (j-1).toNat=j.toNat-1 by omega,show (j-2).toNat=j.toNat-2 by omega]

/-- The bits read in the certificate are exactly the singleton's physical cells. -/
theorem leftWord_correct (t i : Nat) (hi : i<88) :
    (leftWord t).testBit i = cell t ((i : Int)-t) := by
  simpa using (real_edge t i (by omega)).symm

open Rule30Realization

private def window (x : Int → Bool) : Nat → Int → List Bool
  | 0, _ => []
  | n+1, j => x j :: window x n (j+1)

private theorem win_len (x : Int → Bool) (k : Nat) (j : Int) :
    (window x k j).length = k := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih => simp [window,ih]

private theorem take_win (x : Int → Bool) (k : Nat) (j : Int) :
    (window x (k+1) j).take k = window x k j := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih => exact congrArg (List.cons (x j)) (ih (j+1))

private theorem win_layer (x : Int → Bool) (k : Nat) (j : Int) :
    layer rule (x j) (x (j+1)) (window x k (j+2)) = window (evol x 1) k (j+1) := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih =>
    simp only [window,layer]
    have tail := ih (j+1)
    rw [show j+1+1=j+2 by omega,show j+1+2=j+2+1 by omega] at tail
    rw [tail]
    simp [evol,show j+1+1=j+2 by omega]

private theorem evol_first (x : Int → Bool) (n : Nat) (j : Int) :
    evol (evol x 1) n j = evol x (n+1) j := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    change rule _ _ _ = rule _ _ _
    rw [ih,ih,ih]

private theorem triangle_evol (n : Nat) (x : Int → Bool) (j : Int) :
    triangle rule n (window x (2*n+1) j) = [evol x n (j+n)] := by
  induction n generalizing x j with
  | zero => simp [triangle,window,evol]
  | succ n ih =>
    rw [show 2*(n+1)+1 = (2*n+1)+2 by omega]
    change triangle rule n (layer rule (x j) (x (j+1)) (window x (2*n+1) (j+1+1))) = _
    rw [show j+1+1=j+2 by omega,win_layer,ih,evol_first,show j+1+(n : Int)=j+(n+1 : Nat) by omega]

private theorem layer_len (a b : Bool) (xs : List Bool) :
    (layer rule a b xs).length = xs.length := by
  induction xs generalizing a b with
  | nil => rfl
  | cons c xs ih => simp [layer,ih]

private theorem perm_head (n : Nat) (a b : Bool) (xs : List Bool) (h : xs.length=2*n) :
    (triangle rule n (a::xs)).headD false =
      xor (xor a b) ((triangle rule n (b::xs)).headD false) := by
  induction n generalizing a b xs with
  | zero => simp [triangle]
  | succ n ih =>
    cases xs with
    | nil => simp at h
    | cons c xs =>
      cases xs with
      | nil => simp at h; omega
      | cons d xs =>
        change (triangle rule n (rule a c d :: layer rule c d xs)).headD false = _
        have hc := ih (rule a c d) (rule b c d) (layer rule c d xs)
          (by simp only [layer_len]; simp at h; omega)
        have cancel : xor (rule a c d) (rule b c d) = xor a b := by
          cases a <;> cases b <;> cases c <;> cases d <;> rfl
        rw [cancel] at hc
        exact hc

private theorem recover_win (x : Int → Bool) (j : Int) :
    recover rule xor false (evol x 6 (j+6)) (window x 12 (j+1)) = window x 12 j := by
  have p := perm_head 6 (x j) false (window x 12 (j+1)) (win_len x 12 (j+1))
  have cone := triangle_evol 6 x j
  change triangle rule 6 (x j :: window x 12 (j+1)) = [evol x 6 (j+6)] at cone
  rw [cone] at p
  simp only [Bool.xor_false,List.headD_cons] at p
  unfold recover
  rw [p,take_win x 11 (j+1)]
  exact congrArg (fun b => b :: window x 11 (j+1)) (xor_xor_cancel _ _)

private theorem rewind_win (x : Int → Bool) (e : Int) (k word : Nat)
    (obs : ∀ i : Nat, i<k → word.testBit i = evol x 6 (e+i)) :
    rewind word k (window x 12 (e-6+k)) = window x 12 (e-6) := by
  induction k with
  | zero => simp [rewind,scan]
  | succ k ih =>
    change rewind word k (recover rule xor false (word.testBit k) _) = _
    rw [obs k (by omega),show e+(k : Int)=(e-6+k)+6 by omega,
      show e-6+((k+1 : Nat) : Int)=(e-6+k)+1 by omega,recover_win]
    exact ih (fun i hi => obs i (by omega))

/-- Every six-step preimage of these 81 genuine edge cells has the twelve
vacuum bits immediately before its nominal left edge, even if the rest of
the observed row and the two infinite tails of the preimage are unrestricted. -/
theorem physical_reset (t : Nat) (ht : 110 ≤ t) (x : Int → Bool) (e : Int)
    (obs : ∀ i : Nat, i<81 → evol x 6 (e+i) = cell t ((i : Int)-t)) :
    ∀ i : Nat, i<12 → x (e-6+i) = false := by
  have wr := rewind_win x e 81 (leftWord t) (fun i hi => (leftWord_correct t i (by omega)).trans (obs i hi).symm)
  have empty := wr.symm.trans (six_step_reset t ht _ (win_len _ _ _))
  have at_index (k : Nat) (j : Int) (i : Nat) (hi : i<k) :
      (window x k j)[i]? = some (x (j+i)) := by
    induction k generalizing j i with
    | zero => omega
    | succ k ih =>
      cases i with
      | zero => simp [window]
      | succ i =>
        simpa only [window,List.getElem?_cons_succ,show j+((i+1 : Nat):Int)=j+1+i by omega]
          using ih (j+1) i (by omega)
  intro i hi
  have val := at_index 12 (e-6) i hi
  rw [empty] at val
  rw [List.getElem?_replicate_of_lt hi] at val
  exact Option.some.inj val.symm

private def backwards (y : Int → Bool) (b : Int) : Nat → Bool × Bool
  | 0 => (false,false)
  | n+1 =>
    let s := backwards y b n
    (rule (y (b-n)) s.1 s.2,s.1)

private theorem one_parent (y : Int → Bool) (b : Int) (far : ∀ j, b<j → y j=false) :
    ∃ x : Int → Bool, (∀ j, b-1<j → x j=false) ∧ evol x 1=y := by
  let x := fun (j : Int) => (backwards y b (b-j).toNat).1
  have right_vacuum (j : Int) (h : b≤j) : x j=false := by
    simp [x,show (b-j).toNat=0 by omega,backwards]
  have at_k (k : Nat) : x (b-k) = (backwards y b k).1 := by
    simp [x,show (b-(b-(k : Int))).toNat=k by omega]
  have next_k (k : Nat) : x (b-k+1) = (backwards y b k).2 := by
    cases k with
    | zero => exact right_vacuum _ (by omega)
    | succ k =>
      rw [show b-((k+1 : Nat):Int)+1=b-k by omega]
      exact at_k k
  refine ⟨x,fun j hj => right_vacuum j (by omega),?_⟩
  funext j
  change rule (x (j-1)) (x j) (x (j+1)) = y j
  by_cases outside : b<j
  · rw [right_vacuum _ (by omega),right_vacuum _ (by omega),right_vacuum _ (by omega),far _ outside]
    rfl
  · let k := (b-j).toNat
    have pos : j=b-k := by dsimp [k]; omega
    rw [pos,next_k,at_k,show b-(k : Int)-1=b-((k+1 : Nat):Int) by omega,at_k]
    change xor (xor _ _) _ = _
    exact xor_xor_cancel _ _

private theorem right_parent (n : Nat) (y : Int → Bool) (b : Int)
    (far : ∀ j, b<j → y j=false) :
    ∃ x : Int → Bool, (∀ j, b-n<j → x j=false) ∧ evol x n=y := by
  induction n generalizing b y with
  | zero => exact ⟨y,fun j h => far j (by omega),rfl⟩
  | succ n ih =>
    obtain ⟨z,hz,ez⟩ := one_parent y b far
    obtain ⟨x,hx,ex⟩ := ih z (b-1) hz
    refine ⟨x,fun j h => hx j (by omega),?_⟩
    funext j
    change rule _ _ _ = _
    simp only [ex]
    exact congrFun ez j

/-- Any finite continuation of the genuine 81-cell prefix, with vacuum to
its left, has a six-step ancestor in the contracted support interval. -/
theorem finite_ancestor (t : Nat) (ht : 110 ≤ t) (y : Int → Bool) (e b : Int)
    (left : ∀ j, j<e → y j=false) (right : ∀ j, b<j → y j=false)
    (obs : ∀ i : Nat, i<81 → y (e+i) = cell t ((i : Int)-t)) :
    ∃ x : Int → Bool, (∀ j, j<e+6 ∨ b-6<j → x j=false) ∧ evol x 6=y := by
  obtain ⟨x,far,eq⟩ := right_parent 6 y b right
  have init := rewind_win x e 81 (leftWord t)
    (fun i hi => (leftWord_correct t i (by omega)).trans (by rw [eq]; exact (obs i hi).symm))
  have base := init.symm.trans (six_step_reset t ht _ (win_len _ _ _))
  have zero (n : Nat) : window x 12 (e-6-n) = List.replicate 12 false := by
    induction n with
    | zero => simpa using base
    | succ n ih =>
      let j : Int := e-6-((n+1 : Nat) : Int)
      have back := (recover_win x j).symm
      rw [eq,left (j+6) (by dsimp [j]; omega),
        show j+1=e-6-n by dsimp [j]; omega,ih] at back
      exact back.trans (by decide)
  refine ⟨x,?_,eq⟩
  intro j hj
  rcases hj with lo | hi
  · by_cases earlier : j < e-6
    · have h := zero (e-6-j).toNat
      rw [show e-6-((e-6-j).toNat : Int)=j by omega] at h
      exact congrArg (fun l => l.headD false) h
    · have inside := physical_reset t ht x e (by rw [eq]; exact obs)
      have h := inside (j-(e-6)).toNat (by omega)
      simpa only [show e-6+((j-(e-6)).toNat : Int)=j by omega] using h
  · exact far j hi

/-- A failed six-step ancestry check certifies a discrepancy inside the
first 81 cells for a candidate with finite support in the stated interval. -/
theorem mismatch_of_no_ancestor (t : Nat) (ht : 110 ≤ t) (y : Int → Bool) (e b : Int)
    (left : ∀ j, j<e → y j=false) (right : ∀ j, b<j → y j=false)
    (failure : ¬ ∃ x : Int → Bool,
      (∀ j, j<e+6 ∨ b-6<j → x j=false) ∧ evol x 6=y) :
    ∃ i : Nat, i<81 ∧ y (e+i) ≠ cell t ((i : Int)-t) := by
  apply Classical.byContradiction
  intro no
  apply failure
  apply finite_ancestor t ht y e b left right
  intro i hi
  exact Classical.byContradiction (fun ne => no ⟨i,hi,ne⟩)

private theorem vacuum_window (x : Int → Bool) (j : Int) (n : Nat)
    (vac : ∀ i : Nat, i<n → x (j+i)=false) :
    window x n j = List.replicate n false := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    have first := vac 0 (by omega)
    have first' : x j = false := by simpa using first
    simp only [window,List.replicate_succ,first',List.cons.injEq,true_and]
    apply ih
    intro i hi
    rw [show j+1+(i : Int)=j+(i+1 : Nat) by omega]
    exact vac _ (by omega)

private def twoFlips (w : Nat) := w ^^^ (2^80 ||| 2^83)

private theorem two_flip_certificate :
    (scan lanePull (twoFlips (leftWord 189)) 84 (variables 12)).headD 0 = ones := by
  decide +kernel

/-- At ages 189 + 8k, toggling exactly cells 80 and 83 (offsets from the
left edge) destroys every six-step past with the required left vacuum,
while retaining every other cell of the actual singleton. -/
theorem two_flips_no_past (k : Nat) (x : Int → Bool)
    (vac : ∀ j : Int, j<6 → x j=false) :
    let t := 189+8*k
    evol x 6 ≠ fun j : Int => xor (cell t (j-t)) (decide (j=80 ∨ j=83)) := by
  let t := 189+8*k
  have repeatWord : leftWord t = leftWord 189 := by
    induction k with
    | zero => rfl
    | succ k ih =>
      have h := cycle (62+8*k)
      rw [show 127+(62+8*k)=189+8*k by omega,
        show 135+(62+8*k)=189+8*(k+1) by omega] at h
      exact h.symm.trans ih
  change evol x 6 ≠ fun j : Int => xor (cell t (j-t)) (decide (j=80 ∨ j=83))
  intro eq
  let w := twoFlips (leftWord t)
  have obs (i : Nat) (hi : i<84) : w.testBit i = evol x 6 (0+i) := by
    rw [eq,Int.zero_add]
    simp only [w,twoFlips,Nat.testBit_xor,Nat.testBit_or,Nat.testBit_two_pow,
      leftWord_correct t i (by omega)]
    congr 1
    have a : (80 : Nat)=i ↔ (i : Int)=80 := by omega
    have b : (83 : Nat)=i ↔ (i : Int)=83 := by omega
    simp only [a,b]
    by_cases l : (i : Int)=80 <;> by_cases r : (i : Int)=83 <;> simp [l,r]
  let s := window x 12 (0-6+(84 : Nat))
  have len : s.length=12 := win_len _ _ _
  obtain ⟨i,hi,reg⟩ := lanes_cover s
  rw [len] at hi reg
  have link := scan_map w i hi 84 (variables 12)
  rw [reg] at link
  have output : rewind w 84 s = List.replicate 12 false :=
    (rewind_win x 0 84 w obs).trans (vacuum_window x _ _ (fun j hj => vac _ (by omega)))
  rw [output] at link
  have first := congrArg (fun l => l.headD false) link
  have packed : (scan lanePull w 84 (variables 12)).headD 0=ones := by
    simpa only [w,repeatWord] using two_flip_certificate
  cases he : (scan lanePull w 84 (variables 12)) with
  | nil => simp [he,ones] at packed
  | cons v vs =>
    simp only [he,List.headD_cons] at packed
    rw [he] at first
    change v.testBit i = false at first
    rw [packed] at first
    change (2^4096-1).testBit i=false at first
    rw [Nat.testBit_two_pow_sub_one,decide_eq_true hi] at first
    contradiction

end Ruliology.CellularAutomata.Rule30SixStepEdge
