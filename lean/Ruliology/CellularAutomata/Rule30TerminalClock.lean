module

public import Ruliology.CellularAutomata.Rule30ControlledResponse

/-!
# Terminal response rewrites preserve the entire triangular clock

The known terminal rewrites 011 -> 01 and 101 -> 11 do more than preserve
the observed response: behind every shared finite prefix they intertwine
the full triangular update by mutually inverse maps on the linked states.
Consequently all state-return times and equal-time relations are preserved,
with no bound on the prefix length, time or temporal clock.

This does not prove completeness of these response rewrites. In particular
it does not prove that an arbitrary head period is a full-state period,
and it does not prove a statement about the vertical center column.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30TerminalClock

open Rule30ControlledResponse

/-- The long and short tails are indexed by the length of their shared prefix. -/
inductive Linked : Nat → State → State → Prop
  | base (a : Bool) : Linked 0 (word [a,!a,true]) (word [a,true])
  | cons {n : Nat} {x y : State} (a : Bool) (h : Linked n x y) :
      Linked (n+1) (prepend a x) (prepend a y)

def inflate (n : Nat) (y : State) (k : Nat) : Bool :=
  if k<n then y k else word [y n,!(y n),true] (k-n)

def deflate (n : Nat) (x : State) (k : Nat) : Bool :=
  if k<n then x k else word [x n,true] (k-n)

theorem inflate_prepend (n : Nat) (a : Bool) (y : State) :
    inflate (n+1) (prepend a y)=prepend a (inflate n y) := by
  funext k
  cases k with
  | zero => simp [inflate,prepend]
  | succ k => simp [inflate,prepend,Nat.succ_sub_succ_eq_sub]

theorem deflate_prepend (n : Nat) (a : Bool) (x : State) :
    deflate (n+1) (prepend a x)=prepend a (deflate n x) := by
  funext k
  cases k with
  | zero => simp [deflate,prepend]
  | succ k => simp [deflate,prepend,Nat.succ_sub_succ_eq_sub]

theorem linked_inflate {n : Nat} {x y : State} (h : Linked n x y) : x=inflate n y := by
  induction h with
  | base a => funext k; simp [inflate,word]
  | cons a h ih => rw [inflate_prepend,← ih]

theorem linked_deflate {n : Nat} {x y : State} (h : Linked n x y) : y=deflate n x := by
  induction h with
  | base a => funext k; simp [deflate,word]
  | cons a h ih => rw [deflate_prepend,← ih]

theorem linked_response {n : Nat} {x y : State} (h : Linked n x y) : SameResponse x y := by
  induction h with
  | base a =>
      cases a with
      | false => exact tail_011_response []
      | true => exact tail_101_response []
  | cons a h ih => exact sameResponse_prepend ih a

/-- One full triangular step preserves the same indexed correspondence. -/
theorem linked_diagonal {n : Nat} {x y : State} (h : Linked n x y) :
    Linked n (diagonal x) (diagonal y) := by
  induction h with
  | base a =>
      cases a with
      | false =>
          change Linked 0 (diagonal (word [false,true,true])) (diagonal (word [false,true]))
          rw [diagonal_011,diagonal_01]
          exact Linked.base true
      | true =>
          change Linked 0 (diagonal (word [true,false,true])) (diagonal (word [true,true]))
          rw [diagonal_101,diagonal_11]
          exact Linked.base false
  | cons a h ih =>
      have hor := (sameResponse_observe (linked_response h)).2
      rw [diagonal_prepend,diagonal_prepend]
      unfold step
      rw [hor]
      exact Linked.cons _ ih

theorem linked_iterate {n : Nat} {x y : State} (h : Linked n x y) :
    ∀ t, Linked n (iterate x t) (iterate y t)
  | 0 => h
  | t+1 => linked_diagonal (linked_iterate h t)

/-- The two full-state orbits have exactly the same equality relations at all times. -/
theorem iterate_equal_iff {n : Nat} {x y : State} (h : Linked n x y) (s t : Nat) :
    iterate x s=iterate x t ↔ iterate y s=iterate y t := by
  constructor
  · intro he
    calc
      iterate y s=deflate n (iterate x s) := linked_deflate (linked_iterate h s)
      _=deflate n (iterate x t) := congrArg (deflate n) he
      _=iterate y t := (linked_deflate (linked_iterate h t)).symm
  · intro he
    calc
      iterate x s=inflate n (iterate y s) := linked_inflate (linked_iterate h s)
      _=inflate n (iterate y t) := congrArg (inflate n) he
      _=iterate x t := (linked_inflate (linked_iterate h t)).symm

theorem return_iff {n : Nat} {x y : State} (h : Linked n x y) (H : Nat) :
    iterate x H=x ↔ iterate y H=y := by
  simpa only [iterate] using iterate_equal_iff h H 0

theorem linked_prefix (bs : List Bool) (a : Bool) :
    Linked bs.length (word (bs++[a,!a,true])) (word (bs++[a,true])) := by
  induction bs with
  | nil => exact Linked.base a
  | cons b bs ih =>
      simpa only [List.cons_append,word_cons,List.length_cons] using Linked.cons b ih

/-- A terminal 011 -> 01 rewrite preserves every full-state return time. -/
theorem tail_011_return_iff (bs : List Bool) (H : Nat) :
    iterate (word (bs++[false,true,true])) H=word (bs++[false,true,true]) ↔
      iterate (word (bs++[false,true])) H=word (bs++[false,true]) :=
  return_iff (linked_prefix bs false) H

/-- A terminal 101 -> 11 rewrite preserves every full-state return time. -/
theorem tail_101_return_iff (bs : List Bool) (H : Nat) :
    iterate (word (bs++[true,false,true])) H=word (bs++[true,false,true]) ↔
      iterate (word (bs++[true,true])) H=word (bs++[true,true]) :=
  return_iff (linked_prefix bs true) H

/-- Repeated sound terminal rewrites also preserve every full-state return time. -/
inductive RewriteEq : State → State → Prop
  | refl (x : State) : RewriteEq x x
  | linked {n : Nat} {x y : State} (h : Linked n x y) : RewriteEq x y
  | symm {x y : State} (h : RewriteEq x y) : RewriteEq y x
  | trans {x y z : State} (h : RewriteEq x y) (g : RewriteEq y z) : RewriteEq x z

theorem rewrite_response {x y : State} (h : RewriteEq x y) : SameResponse x y := by
  induction h with
  | refl x => exact sameResponse_refl x
  | linked h => exact linked_response h
  | symm h ih => exact sameResponse_symm ih
  | trans h g ih ig => exact sameResponse_trans ih ig

theorem rewrite_equal_iff {x y : State} (h : RewriteEq x y) (s t : Nat) :
    iterate x s=iterate x t ↔ iterate y s=iterate y t := by
  induction h with
  | refl x => rfl
  | linked h => exact iterate_equal_iff h s t
  | symm h ih => exact ih.symm
  | trans h g ih ig => exact ih.trans ig

theorem rewrite_return_iff {x y : State} (h : RewriteEq x y) (H : Nat) :
    iterate x H=x ↔ iterate y H=y := by
  simpa only [iterate] using rewrite_equal_iff h H 0

/-! ## Closure of `RewriteEq` under `iterate` and 4-bit terminal return preservation (`0101 ↔ 01` and `1011 ↔ 11`) -/

/-- **Closure of `RewriteEq` Under `iterate` and 4-Bit Terminal Return Equivalence (`rewriteEq_iterate_and_four_bit_return_iff`).** -/
theorem rewriteEq_iterate_and_four_bit_return_iff
    {x y : State} (bs : List Bool) (t H : Nat) :
    (RewriteEq x y → RewriteEq (iterate x t) (iterate y t)) ∧
    (iterate (word (bs ++ [false, true, false, true])) H = word (bs ++ [false, true, false, true]) ↔
      iterate (word (bs ++ [false, true])) H = word (bs ++ [false, true])) ∧
    (iterate (word (bs ++ [true, false, true, true])) H = word (bs ++ [true, false, true, true]) ↔
      iterate (word (bs ++ [true, true])) H = word (bs ++ [true, true])) := by
  refine ⟨fun h => ?_, ?_, ?_⟩
  · induction h with
    | refl z => exact RewriteEq.refl (iterate z t)
    | linked hL => exact RewriteEq.linked (linked_iterate hL t)
    | symm _ ih => exact RewriteEq.symm ih
    | trans _ _ ih1 ih2 => exact RewriteEq.trans ih1 ih2
  · have h1 : bs ++ [false, true, false, true] = (bs ++ [false]) ++ [true, false, true] := by simp
    have h2 : (bs ++ [false]) ++ [true, true] = bs ++ [false, true, true] := by simp
    have hrw1 : RewriteEq (word ((bs ++ [false]) ++ [true, false, true]))
        (word ((bs ++ [false]) ++ [true, true])) :=
      RewriteEq.linked (linked_prefix (bs ++ [false]) true)
    have hrw2 : RewriteEq (word (bs ++ [false, true, true])) (word (bs ++ [false, true])) :=
      RewriteEq.linked (linked_prefix bs false)
    rw [h1]
    rw [h2] at hrw1
    exact rewrite_return_iff (RewriteEq.trans hrw1 hrw2) H
  · have h1 : bs ++ [true, false, true, true] = (bs ++ [true]) ++ [false, true, true] := by simp
    have h2 : (bs ++ [true]) ++ [false, true] = bs ++ [true, false, true] := by simp
    have hrw1 : RewriteEq (word ((bs ++ [true]) ++ [false, true, true]))
        (word ((bs ++ [true]) ++ [false, true])) :=
      RewriteEq.linked (linked_prefix (bs ++ [true]) false)
    have hrw2 : RewriteEq (word (bs ++ [true, false, true])) (word (bs ++ [true, true])) :=
      RewriteEq.linked (linked_prefix bs true)
    rw [h1]
    rw [h2] at hrw1
    exact rewrite_return_iff (RewriteEq.trans hrw1 hrw2) H

end Ruliology.CellularAutomata.Rule30TerminalClock
