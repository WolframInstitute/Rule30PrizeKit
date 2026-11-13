module

public import Ruliology.CellularAutomata.Rule30Ether
public import Ruliology.CellularAutomata.Rule30Realization

/-!
# Controlled responses and the triangular right-edge update

The response tree for every possible left driver is equivalent to alternating
head/OR observations of a triangular update. This is an exact controlled-system
equivalence. A single prescribed driver is a different question; no prize
problem is solved here.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30ControlledResponse

open Rule30Jen Rule30Ether

abbrev State := Nat → Bool

def prepend (a : Bool) (x : State) : State
  | 0 => a
  | k+1 => x k

def diagonal (x : State) (k : Nat) : Bool :=
  xor (x k) (x (k+1) || x (k+2))

def step (b : Bool) (x : State) : State :=
  prepend (xor b (x 0 || x 1)) (diagonal x)

def run (c : Nat → Bool) (x : State) : Nat → State
  | 0 => x
  | t+1 => step (c t) (run c x t)

def asRight (x : State) (p : Nat) : Bool :=
  if p=0 then false else x (p-1)

/-- The controlled state uses zero-based indexing of the kit's positions 1,2,... . -/
theorem run_sound (c : Nat → Bool) (x : State) : ∀ t k,
    run c x t k=drv c (asRight x) t (k+1) := by
  intro t
  induction t with
  | zero => intro k; simp [run,drv,asRight]
  | succ t ih =>
      intro k
      cases k with
      | zero => simp [run,step,prepend,drv,rule,ih,drv_col0]
      | succ k => simp [run,step,prepend,diagonal,drv,rule,ih,Nat.add_assoc]

theorem run_shift (c : Nat → Bool) (x : State) : ∀ n,
    run c x (n+1)=run (fun j => c (j+1)) (step (c 0) x) n
  | 0 => rfl
  | n+1 => by
      rw [run,run_shift c x n]
      rfl

def ResponseEq : Nat → State → State → Prop
  | 0,_,_ => True
  | n+1,x,y => x 0=y 0 ∧ ∀ b, ResponseEq n (step b x) (step b y)

theorem responseEq_iff_runs (n : Nat) (x y : State) :
    ResponseEq n x y ↔ ∀ c t, t<n → run c x t 0=run c y t 0 := by
  induction n generalizing x y with
  | zero => simp [ResponseEq]
  | succ n ih =>
      constructor
      · intro h c t ht
        cases t with
        | zero => exact h.1
        | succ t =>
            rw [run_shift,run_shift]
            exact (ih (step (c 0) x) (step (c 0) y)).mp (h.2 (c 0)) _ t (by omega)
      · intro h
        refine ⟨h (fun _ => false) 0 (by omega),fun b => ?_⟩
        apply (ih _ _).mpr
        intro c t ht
        have he := h (prepend b c) (t+1) (by omega)
        rw [run_shift,run_shift] at he
        simpa only [prepend] using he

theorem diagonal_prepend (a : Bool) (x : State) : diagonal (prepend a x)=step a x := by
  funext k
  cases k <;> rfl

theorem step_prepend (b a : Bool) (x : State) :
    step b (prepend a x)=prepend (xor b (a || x 0)) (step a x) := by
  unfold step
  rw [diagonal_prepend]
  rfl

private theorem xor_cancel (a b : Bool) : xor (xor a b) b=a := by
  cases a <;> cases b <;> rfl

/-- One arbitrary shared prefix cell costs one observation of the tail system. -/
theorem responseEq_all_prepend (n : Nat) (x y : State) :
    (∀ a, ResponseEq (n+1) (prepend a x) (prepend a y)) ↔ ResponseEq n x y := by
  induction n generalizing x y with
  | zero => simp [ResponseEq,prepend]
  | succ n ih =>
      constructor
      · intro h
        have hhead : x 0=y 0 := by
          have he := ((h false).2 false).1
          simpa [step,prepend] using he
        refine ⟨hhead,fun b => ?_⟩
        apply (ih _ _).mp
        intro a
        have he := (h b).2 (xor a (b || x 0))
        rw [step_prepend,step_prepend,← hhead,xor_cancel] at he
        exact he
      · intro h a
        refine ⟨rfl,fun b => ?_⟩
        rw [step_prepend,step_prepend,h.1]
        exact (ih _ _).mpr (h.2 a) (xor b (a || y 0))

/-- Two observations remove one triangular diagonal layer exactly. -/
theorem responseEq_two (n : Nat) (x y : State) :
    ResponseEq (n+2) x y ↔ x 0=y 0 ∧ (x 0 || x 1)=(y 0 || y 1) ∧
      ResponseEq n (diagonal x) (diagonal y) := by
  constructor
  · intro h
    have hor : (x 0 || x 1)=(y 0 || y 1) := by
      have he := (h.2 false).1
      simpa [step,prepend] using he
    refine ⟨h.1,hor,(responseEq_all_prepend n _ _).mp (fun a => ?_)⟩
    have he := h.2 (xor a (x 0 || x 1))
    change ResponseEq (n+1)
      (prepend (xor (xor a (x 0 || x 1)) (x 0 || x 1)) (diagonal x))
      (prepend (xor (xor a (x 0 || x 1)) (y 0 || y 1)) (diagonal y)) at he
    rw [← hor,xor_cancel] at he
    exact he
  · rintro ⟨hhead,hor,hdiag⟩
    refine ⟨hhead,fun b => ?_⟩
    change ResponseEq (n+1) (prepend (xor b (x 0 || x 1)) (diagonal x))
      (prepend (xor b (y 0 || y 1)) (diagonal y))
    rw [hor]
    exact (responseEq_all_prepend n _ _).mpr hdiag _

def iterate (x : State) : Nat → State
  | 0 => x
  | n+1 => diagonal (iterate x n)

theorem iterate_from (x : State) : ∀ n, iterate (diagonal x) n=iterate x (n+1)
  | 0 => rfl
  | n+1 => by rw [iterate,iterate_from x n]; rfl

def ObserveEq (x y : State) : Prop :=
  x 0=y 0 ∧ (x 0 || x 1)=(y 0 || y 1)

def SameResponse (x y : State) : Prop := ∀ n, ResponseEq n x y

theorem sameResponse_shift {x y : State} (h : SameResponse x y) :
    SameResponse (diagonal x) (diagonal y) :=
  fun n => ((responseEq_two n x y).mp (h (n+2))).2.2

theorem sameResponse_observe {x y : State} (h : SameResponse x y) : ObserveEq x y :=
  ⟨((responseEq_two 0 x y).mp (h 2)).1,((responseEq_two 0 x y).mp (h 2)).2.1⟩

private theorem response_of_diagonal : ∀ n (x y : State),
    (∀ k, ObserveEq (iterate x k) (iterate y k)) → ResponseEq n x y
  | 0,_,_,_ => True.intro
  | 1,x,y,h => ⟨(h 0).1,fun _ => True.intro⟩
  | n+2,x,y,h => (responseEq_two n x y).mpr ⟨(h 0).1,(h 0).2,
      response_of_diagonal n (diagonal x) (diagonal y) (fun k => by
        rw [iterate_from,iterate_from]
        exact h (k+1))⟩

/-- Exact equivalence for every boundary word and observation horizon. -/
theorem sameResponse_iff_diagonal (x y : State) :
    SameResponse x y ↔ ∀ k, ObserveEq (iterate x k) (iterate y k) := by
  constructor
  · intro h
    have hi : ∀ k, SameResponse (iterate x k) (iterate y k) := by
      intro k
      induction k with
      | zero => exact h
      | succ k ih => exact sameResponse_shift ih
    exact fun k => sameResponse_observe (hi k)
  · intro h n
    exact response_of_diagonal n x y h

theorem sameResponse_iff_drv (x y : State) :
    SameResponse x y ↔ ∀ c t, drv c (asRight x) t 1=drv c (asRight y) t 1 := by
  constructor
  · intro h c t
    rw [← run_sound c x t 0,← run_sound c y t 0]
    exact (responseEq_iff_runs (t+1) x y).mp (h _) c t (by omega)
  · intro h n
    apply (responseEq_iff_runs n x y).mpr
    intro c t _
    rw [run_sound,run_sound]
    exact h c t

theorem sameResponse_refl (x : State) : SameResponse x x :=
  (sameResponse_iff_drv x x).mpr (fun _ _ => rfl)

theorem sameResponse_symm {x y : State} (h : SameResponse x y) : SameResponse y x :=
  (sameResponse_iff_drv y x).mpr (fun c t => ((sameResponse_iff_drv x y).mp h c t).symm)

theorem sameResponse_trans {x y z : State} (h : SameResponse x y) (g : SameResponse y z) :
    SameResponse x z :=
  (sameResponse_iff_drv x z).mpr (fun c t =>
    ((sameResponse_iff_drv x y).mp h c t).trans ((sameResponse_iff_drv y z).mp g c t))

theorem sameResponse_prepend {x y : State} (h : SameResponse x y) (a : Bool) :
    SameResponse (prepend a x) (prepend a y) := by
  intro n
  cases n with
  | zero => exact True.intro
  | succ n => exact (responseEq_all_prepend n x y).mpr (h n) a

def withPrefix : List Bool → State → State
  | [],x => x
  | a::bs,x => prepend a (withPrefix bs x)

theorem sameResponse_withPrefix {x y : State} (h : SameResponse x y) (bs : List Bool) :
    SameResponse (withPrefix bs x) (withPrefix bs y) := by
  induction bs with
  | nil => exact h
  | cons a bs ih => exact sameResponse_prepend ih a

def word (bs : List Bool) (k : Nat) : Bool := bs.getD k false

theorem word_cons (a : Bool) (bs : List Bool) : word (a::bs)=prepend a (word bs) := by
  funext k
  cases k <;> rfl

theorem word_append (bs cs : List Bool) : word (bs++cs)=withPrefix bs (word cs) := by
  induction bs with
  | nil => rfl
  | cons a bs ih =>
      rw [List.cons_append,word_cons,withPrefix,ih]

theorem diagonal_011 : diagonal (word [false,true,true])=word [true,false,true] := by
  funext k
  cases k with
  | zero => rfl
  | succ k =>
      cases k with
      | zero => rfl
      | succ k => cases k <;> rfl

theorem diagonal_01 : diagonal (word [false,true])=word [true,true] := by
  funext k
  cases k with
  | zero => rfl
  | succ k => cases k <;> rfl

theorem diagonal_101 : diagonal (word [true,false,true])=word [false,true,true] := by
  funext k
  cases k with
  | zero => rfl
  | succ k =>
      cases k with
      | zero => rfl
      | succ k => cases k <;> rfl

theorem diagonal_11 : diagonal (word [true,true])=word [false,true] := by
  funext k
  cases k with
  | zero => rfl
  | succ k => cases k <;> rfl

private theorem primitive_responses : ∀ n,
    ResponseEq n (word [false,true,true]) (word [false,true]) ∧
    ResponseEq n (word [true,false,true]) (word [true,true])
  | 0 => ⟨True.intro,True.intro⟩
  | 1 => ⟨⟨rfl,fun _ => True.intro⟩,⟨rfl,fun _ => True.intro⟩⟩
  | n+2 => by
      constructor
      · apply (responseEq_two n _ _).mpr
        refine ⟨rfl,rfl,?_⟩
        rw [diagonal_011,diagonal_01]
        exact (primitive_responses n).2
      · apply (responseEq_two n _ _).mpr
        refine ⟨rfl,rfl,?_⟩
        rw [diagonal_101,diagonal_11]
        exact (primitive_responses n).1

/-- A terminal 011 may be replaced by 01, behind any finite shared prefix. -/
theorem tail_011_response (bs : List Bool) :
    SameResponse (word (bs++[false,true,true])) (word (bs++[false,true])) := by
  rw [word_append,word_append]
  exact sameResponse_withPrefix (fun n => (primitive_responses n).1) bs

/-- A terminal 101 may be replaced by 11, behind any finite shared prefix. -/
theorem tail_101_response (bs : List Bool) :
    SameResponse (word (bs++[true,false,true])) (word (bs++[true,true])) := by
  rw [word_append,word_append]
  exact sameResponse_withPrefix (fun n => (primitive_responses n).2) bs

theorem tail_011_drv (bs : List Bool) (c : Nat → Bool) (t : Nat) :
    drv c (asRight (word (bs++[false,true,true]))) t 1=
      drv c (asRight (word (bs++[false,true]))) t 1 :=
  (sameResponse_iff_drv _ _).mp (tail_011_response bs) c t

theorem tail_101_drv (bs : List Bool) (c : Nat → Bool) (t : Nat) :
    drv c (asRight (word (bs++[true,false,true]))) t 1=
      drv c (asRight (word (bs++[true,true]))) t 1 :=
  (sameResponse_iff_drv _ _).mp (tail_101_response bs) c t

/-- An equivalent finite test without branching over all boundary words. -/
def ObservationPrefix : Nat → State → State → Prop
  | 0,_,_ => True
  | 1,x,y => x 0=y 0
  | n+2,x,y => ObserveEq x y ∧ ObservationPrefix n (diagonal x) (diagonal y)

theorem responseEq_iff_observationPrefix : ∀ n (x y : State),
    ResponseEq n x y ↔ ObservationPrefix n x y
  | 0,_,_ => Iff.rfl
  | 1,_,_ => by simp [ResponseEq,ObservationPrefix]
  | n+2,x,y => by
      rw [responseEq_two,ObservationPrefix,← responseEq_iff_observationPrefix n]
      exact and_assoc.symm

instance observeEqDecidable (x y : State) : Decidable (ObserveEq x y) :=
  inferInstanceAs (Decidable (x 0=y 0 ∧ (x 0 || x 1)=(y 0 || y 1)))

instance observationPrefixDecidable : ∀ n (x y : State), Decidable (ObservationPrefix n x y)
  | 0,_,_ => isTrue True.intro
  | 1,x,y => inferInstanceAs (Decidable (x 0=y 0))
  | n+2,x,y => @instDecidableAnd (ObserveEq x y)
      (ObservationPrefix n (diagonal x) (diagonal y)) (observeEqDecidable x y)
      (observationPrefixDecidable n (diagonal x) (diagonal y))

def shortWindowA : State := word [false,true,false,true,false,true]
def shortWindowB : State := word [false,true,true,false,false,false,true]

/-- Width seven does not make thirteen observations a complete test. -/
theorem short_window_agreement : ResponseEq 13 shortWindowA shortWindowB := by
  rw [responseEq_iff_observationPrefix]
  decide

theorem short_window_not_sameResponse : ¬ SameResponse shortWindowA shortWindowB := by
  intro h
  have he := (sameResponse_iff_diagonal _ _).mp h 8
  have hn : ¬ ObserveEq (iterate shortWindowA 8) (iterate shortWindowB 8) := by decide
  exact hn he

theorem zero_driver_head (x : State) (hx : x 0=true) :
    ∀ t, run (fun _ => false) x t 0=true := by
  intro t
  induction t with
  | zero => exact hx
  | succ t ih => simp [run,step,prepend,ih]

/-- Agreement for one periodic driver does not imply universal response equality.
This externally imposed driver is not asserted to extend to a finite full row. -/
theorem fixed_driver_counterexample :
    (∀ t, drv (fun _ => false) (asRight (word [true])) t 1=
      drv (fun _ => false) (asRight (word [true,true])) t 1) ∧
    ¬ SameResponse (word [true]) (word [true,true]) := by
  constructor
  · intro t
    rw [← run_sound _ _ t 0,← run_sound _ _ t 0]
    rw [zero_driver_head _ rfl,zero_driver_head _ rfl]
  · intro h
    have he := (sameResponse_iff_diagonal _ _).mp h 1
    have hn : ¬ ObserveEq (iterate (word [true]) 1) (iterate (word [true,true]) 1) := by decide
    exact hn he

theorem sameResponse_step {x y : State} (h : SameResponse x y) (b : Bool) :
    SameResponse (step b x) (step b y) := fun n => (h (n+1)).2 b

open Rule30Realization

def rightPart (x : Int → Bool) (k : Nat) : Bool := x ((k:Int)+1)

theorem rightPart_next (x : Int → Bool) (t : Nat) :
    rightPart (evol x (t+1))=step (evol x t 0) (rightPart (evol x t)) := by
  funext k
  cases k with
  | zero => simp [rightPart,evol,step,prepend,rule]
  | succ k =>
      simp [rightPart,evol,step,prepend,diagonal,rule,Int.natCast_add,Int.add_assoc]
      congr 1 <;> omega

/-- Universal right-response equivalence remains sound under actual left feedback. -/
theorem feedback_left_equal {x y : Int → Bool}
    (hleft : ∀ p, p≤0 → x p=y p) (hright : SameResponse (rightPart x) (rightPart y)) :
    ∀ t, (∀ p, p≤0 → evol x t p=evol y t p) ∧
      SameResponse (rightPart (evol x t)) (rightPart (evol y t)) := by
  intro t
  induction t with
  | zero => exact ⟨hleft,hright⟩
  | succ t ih =>
      constructor
      · intro p hp
        have hhead : evol x t 1=evol y t 1 := (sameResponse_observe ih.2).1
        change rule (evol x t (p-1)) (evol x t p) (evol x t (p+1)) =
          rule (evol y t (p-1)) (evol y t p) (evol y t (p+1))
        rw [ih.1 (p-1) (by omega),ih.1 p hp]
        by_cases hz : p=0
        · subst p; rw [show (0:Int)+1=1 by omega,hhead]
        · rw [ih.1 (p+1) (by omega)]
      · rw [rightPart_next,rightPart_next,ih.1 0 (by omega)]
        exact sameResponse_step ih.2 _

def splice (left : Int → Bool) (right : State) (p : Int) : Bool :=
  if p≤0 then left p else right (p.toNat-1)

theorem rightPart_splice (left : Int → Bool) (right : State) :
    rightPart (splice left right)=right := by
  funext k
  simp [rightPart,splice,show ¬ (k:Int)+1≤0 by omega]

theorem splice_same_center (left : Int → Bool) {x y : State} (h : SameResponse x y) (t : Nat) :
    evol (splice left x) t 0=evol (splice left y) t 0 := by
  apply (feedback_left_equal (x:=splice left x) (y:=splice left y) ?_ ?_ t).1 0 (by omega)
  · intro p hp
    simp [splice,hp]
  · rwa [rightPart_splice,rightPart_splice]

theorem tail_011_center (left : Int → Bool) (bs : List Bool) (t : Nat) :
    evol (splice left (word (bs++[false,true,true]))) t 0=
      evol (splice left (word (bs++[false,true]))) t 0 :=
  splice_same_center left (tail_011_response bs) t

theorem tail_101_center (left : Int → Bool) (bs : List Bool) (t : Nat) :
    evol (splice left (word (bs++[true,false,true]))) t 0=
      evol (splice left (word (bs++[true,true]))) t 0 :=
  splice_same_center left (tail_101_response bs) t

/-! ## Additivity of `iterate` and 4-bit terminal response reductions (`0101 → 01` and `1011 → 11`) -/

/-- **Additivity of `iterate` and 4-Bit Terminal Response Reductions (`iterate_add_and_tail_four_bit_reductions`).** -/
theorem iterate_add_and_tail_four_bit_reductions (x : State) (a b : Nat) (bs : List Bool) :
    iterate x (a + b) = iterate (iterate x a) b ∧
    SameResponse (word (bs ++ [false, true, false, true])) (word (bs ++ [false, true])) ∧
    SameResponse (word (bs ++ [true, false, true, true])) (word (bs ++ [true, true])) := by
  refine ⟨?_, ?_, ?_⟩
  · induction b with
    | zero => rfl
    | succ b ih => rw [Nat.add_succ, iterate, iterate, ih]
  · have h1 : bs ++ [false, true, false, true] = (bs ++ [false]) ++ [true, false, true] := by simp
    have h2 : (bs ++ [false]) ++ [true, true] = bs ++ [false, true, true] := by simp
    rw [h1]
    apply sameResponse_trans (tail_101_response (bs ++ [false]))
    rw [h2]
    exact tail_011_response bs
  · have h1 : bs ++ [true, false, true, true] = (bs ++ [true]) ++ [false, true, true] := by simp
    have h2 : (bs ++ [true]) ++ [false, true] = bs ++ [true, false, true] := by simp
    rw [h1]
    apply sameResponse_trans (tail_011_response (bs ++ [true]))
    rw [h2]
    exact tail_101_response bs

end Ruliology.CellularAutomata.Rule30ControlledResponse
