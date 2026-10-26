module

public import Ruliology.CellularAutomata.Rule30ControlledResponse

/-!
# Exact eight-step return of finite triangular states

For every catalog `State` that is white from some finite index onward,
return after eight triangular updates is equivalent to return after two
updates of the shifted state `fun k => x (k+3)`
(`iterate_finite_return_eight_iff`). For newest-first finite words the shift
is `drop 3` (`iterate_word_return_eight_iff`).

The proof scans words in older-first order, where deleting the three newest
cells means taking the prefix of length `length - 3`. A kernel-checked
certificate on 36 pairs of nine-time profiles tracks the first two-step
discrepancy and its delayed eight-step discrepancy. Induction on the word
then proves the criterion at every width, including empty and short words.
`evolution_state` connects this representation to the catalog's exact map.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30FiniteReturnEight

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private structure Profile where
  t0 : Bool
  t1 : Bool
  t2 : Bool
  t3 : Bool
  t4 : Bool
  t5 : Bool
  t6 : Bool
  t7 : Bool
  t8 : Bool
deriving DecidableEq, Repr

private def ofNat (n : Nat) : Profile :=
  ⟨n.testBit 0, n.testBit 1, n.testBit 2, n.testBit 3, n.testBit 4,
   n.testBit 5, n.testBit 6, n.testBit 7, n.testBit 8⟩

private def zero : Profile := ofNat 0

/-- p is the previous (nearest older) cell, r the older cell before p. -/
private def nextProfile (p r : Profile) (v : Bool) : Profile :=
  let c1 := xor v (p.t0 || r.t0)
  let c2 := xor c1 (p.t1 || r.t1)
  let c3 := xor c2 (p.t2 || r.t2)
  let c4 := xor c3 (p.t3 || r.t3)
  let c5 := xor c4 (p.t4 || r.t4)
  let c6 := xor c5 (p.t5 || r.t5)
  let c7 := xor c6 (p.t6 || r.t6)
  let c8 := xor c7 (p.t7 || r.t7)
  ⟨v,c1,c2,c3,c4,c5,c6,c7,c8⟩

/-- A parallel triangular update with the two supplied older boundary bits. -/
def change (p r : Bool) : List Bool → List Bool
  | [] => []
  | v :: vs => xor v (p || r) :: change v p vs

/-- One simultaneous update of an older-first finite word, with both older
boundary bits white. -/
def F (xs : List Bool) : List Bool := change false false xs

def evolution : Nat → List Bool → List Bool
  | 0, xs => xs
  | t+1, xs => F (evolution t xs)

theorem local_rule_bridge (current previous older : Bool) :
    xor current (previous || older) =
      Ruliology.CellularAutomata.Rule30Jen.rule current previous older := rfl

/-- Eight parallel updates with time-varying supplied boundary profiles. -/
private def run8 (p r : Profile) (xs : List Bool) : List Bool :=
  change p.t7 r.t7 (change p.t6 r.t6 (change p.t5 r.t5 (change p.t4 r.t4
    (change p.t3 r.t3 (change p.t2 r.t2 (change p.t1 r.t1 (change p.t0 r.t0 xs)))))))

private theorem run8_nil (p r : Profile) : run8 p r [] = [] := rfl

/-- The semantic spatial bridge is definitional, not an assumed clock rule. -/
private theorem run8_cons (p r : Profile) (v : Bool) (vs : List Bool) :
    run8 p r (v :: vs) = (nextProfile p r v).t8 :: run8 (nextProfile p r v) p vs := rfl

private theorem run8_white (xs : List Bool) : run8 zero zero xs = evolution 8 xs := rfl

private def state (i : Fin 36) : Profile × Profile :=
  match i.val with
  | 0 => ⟨ofNat 0,ofNat 0⟩
  | 1 => ⟨ofNat 511,ofNat 0⟩
  | 2 => ⟨ofNat 170,ofNat 511⟩
  | 3 => ⟨ofNat 341,ofNat 511⟩
  | 4 => ⟨ofNat 170,ofNat 170⟩
  | 5 => ⟨ofNat 341,ofNat 170⟩
  | 6 => ⟨ofNat 170,ofNat 341⟩
  | 7 => ⟨ofNat 341,ofNat 341⟩
  | 8 => ⟨ofNat 204,ofNat 170⟩
  | 9 => ⟨ofNat 307,ofNat 170⟩
  | 10 => ⟨ofNat 102,ofNat 341⟩
  | 11 => ⟨ofNat 409,ofNat 341⟩
  | 12 => ⟨ofNat 180,ofNat 204⟩
  | 13 => ⟨ofNat 331,ofNat 204⟩
  | 14 => ⟨ofNat 210,ofNat 307⟩
  | 15 => ⟨ofNat 301,ofNat 307⟩
  | 16 => ⟨ofNat 90,ofNat 102⟩
  | 17 => ⟨ofNat 421,ofNat 102⟩
  | 18 => ⟨ofNat 150,ofNat 409⟩
  | 19 => ⟨ofNat 361,ofNat 409⟩
  | 20 => ⟨ofNat 168,ofNat 180⟩
  | 21 => ⟨ofNat 343,ofNat 180⟩
  | 22 => ⟨ofNat 138,ofNat 331⟩
  | 23 => ⟨ofNat 373,ofNat 331⟩
  | 24 => ⟨ofNat 162,ofNat 210⟩
  | 25 => ⟨ofNat 349,ofNat 210⟩
  | 26 => ⟨ofNat 42,ofNat 301⟩
  | 27 => ⟨ofNat 469,ofNat 301⟩
  | 28 => ⟨ofNat 84,ofNat 90⟩
  | 29 => ⟨ofNat 427,ofNat 90⟩
  | 30 => ⟨ofNat 186,ofNat 421⟩
  | 31 => ⟨ofNat 325,ofNat 421⟩
  | 32 => ⟨ofNat 234,ofNat 150⟩
  | 33 => ⟨ofNat 277,ofNat 150⟩
  | 34 => ⟨ofNat 174,ofNat 361⟩
  | 35 => ⟨ofNat 337,ofNat 361⟩
  | _ => ⟨zero,zero⟩

private def category (i : Fin 36) : Nat :=
  if i.val < 8 then 0 else if i.val < 12 then 1 else if i.val < 20 then 2 else 3

private theorem category_le (i : Fin 36) : category i ≤ 3 := by
  unfold category
  split <;> first | omega | (split <;> first | omega | (split <;> omega))

private theorem category_certificate : ∀ (i : Fin 36) (v : Bool),
    let p := (state i).1
    let r := (state i).2
    let q := nextProfile p r v
    if category i = 3 then q.t8 ≠ v
    else q.t8 = v ∧ ∃ j : Fin 36,
      (state j).1 = q ∧
      (state j).2 = p ∧
      (if category i = 0 then category j = (if q.t2 = v then 0 else 1)
       else category j = category i + 1) := by
  decide +kernel

private def run2 (p r : Profile) (xs : List Bool) : List Bool :=
  change p.t1 r.t1 (change p.t0 r.t0 xs)

private theorem run2_cons (p r : Profile) (v : Bool) (vs : List Bool) :
    run2 p r (v :: vs) = (nextProfile p r v).t2 :: run2 (nextProfile p r v) p vs := rfl

private theorem run2_white (xs : List Bool) : run2 zero zero xs = evolution 2 xs := rfl

private def ShortTwo (p r : Profile) (xs : List Bool) : Prop :=
  run2 p r (xs.take (xs.length-3)) = xs.take (xs.length-3)

private theorem short_two_small (p r : Profile) (xs : List Bool) (h : xs.length ≤ 3) :
    ShortTwo p r xs := by
  have hz : xs.length-3 = 0 := by omega
  simp [ShortTwo,hz,run2,change]

private theorem short_two_cons (p r : Profile) (v : Bool) (vs : List Bool) :
    ShortTwo p r (v :: vs) ↔ vs.length ≤ 2 ∨
      ((nextProfile p r v).t2 = v ∧ ShortTwo (nextProfile p r v) p vs) := by
  by_cases h : vs.length ≤ 2
  · constructor
    · intro _; exact Or.inl h
    · intro _; exact short_two_small p r (v::vs) (by simp only [List.length_cons]; omega)
  · unfold ShortTwo
    rw [show (v :: vs).length-3 = (vs.length-3)+1 by simp only [List.length_cons]; omega]
    simp only [List.take_succ_cons,run2_cons,List.cons.injEq,h,false_or]

private theorem dispatch (xs : List Bool) : ∀ i : Fin 36,
    run8 (state i).1 (state i).2 xs = xs ↔
      if category i = 0 then
        ShortTwo (state i).1 (state i).2 xs
      else xs.length + category i ≤ 3 := by
  induction xs with
  | nil =>
    intro i
    simp only [run8_nil,List.length_nil,Nat.zero_add,true_iff]
    by_cases h : category i = 0
    · rw [if_pos h]
      exact short_two_small _ _ [] (by simp)
    · rw [if_neg h]
      exact category_le i
  | cons v vs ih =>
    intro i
    let p := (state i).1
    let r := (state i).2
    have cert := category_certificate i v
    change (if category i = 3 then (nextProfile p r v).t8 ≠ v else
      (nextProfile p r v).t8 = v ∧ ∃ j : Fin 36,
        (state j).1 = nextProfile p r v ∧
        (state j).2 = p ∧
        (if category i = 0 then category j = (if (nextProfile p r v).t2 = v then 0 else 1)
         else category j = category i+1)) at cert
    change run8 p r (v::vs) = v::vs ↔
      if category i = 0 then ShortTwo p r (v::vs) else (v::vs).length+category i ≤ 3
    by_cases h3 : category i = 3
    · simp only [h3,if_true] at cert
      simp [run8_cons,List.cons.injEq,cert,h3]
    · simp only [h3,if_false] at cert
      obtain ⟨h8,j,hp,hr,hcat⟩ := cert
      have sub := ih j
      rw [hp,hr] at sub
      rw [run8_cons,h8,List.cons.injEq]
      simp only [true_and]
      rw [sub]
      by_cases h0 : category i = 0
      · simp only [h0,if_true] at hcat ⊢
        by_cases h2 : (nextProfile p r v).t2 = v
        · have hj : category j = 0 := by simpa only [h2,if_true] using hcat
          rw [hj]
          simp only [if_true]
          rw [short_two_cons]
          simp only [h2,true_and]
          constructor
          · intro h; exact Or.inr h
          · intro h
            rcases h with hs | hs
            · exact short_two_small _ _ vs (by omega)
            · exact hs
        · have hj : category j = 1 := by simpa only [h2,if_false] using hcat
          rw [hj]
          simp only [show ¬ (1:Nat)=0 by decide,if_false,short_two_cons,h2,false_and,or_false]
          omega
      · simp only [h0,if_false] at hcat ⊢
        have hj : category j ≠ 0 := by omega
        simp only [hj,if_false,List.length_cons]
        omega

/-- Exact all-width finite-white reduction. Empty and short prefixes are
handled by Nat subtraction and the literal empty-word evolution. -/
theorem return_eight_iff_prefix_two (xs : List Bool) :
    evolution 8 xs = xs ↔
      evolution 2 (xs.take (xs.length-3)) = xs.take (xs.length-3) := by
  have h := dispatch xs ⟨0,by decide⟩
  change run8 zero zero xs = xs ↔ ShortTwo zero zero xs at h
  simpa only [run8_white,ShortTwo,run2_white] using h


/-! ## The catalog's newest-first, zero-tailed state representation -/

private theorem change_length (xs : List Bool) (p r : Bool) :
    (change p r xs).length = xs.length := by
  induction xs generalizing p r with
  | nil => rfl
  | cons v vs ih => simp only [change,List.length_cons,ih]

theorem F_length (xs : List Bool) : (F xs).length = xs.length :=
  change_length xs false false

theorem evolution_length (xs : List Bool) (t : Nat) :
    (evolution t xs).length = xs.length := by
  induction t with
  | zero => rfl
  | succ t ih => rw [evolution,F_length,ih]

private theorem change_getD (xs : List Bool) (p r : Bool) (i : Nat) (hi : i < xs.length) :
    (change p r xs).getD i false =
      xor (xs.getD i false) ((p :: xs).getD i false || (r :: p :: xs).getD i false) := by
  induction xs generalizing p r i with
  | nil => simp at hi
  | cons v vs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simp only [change,List.getD_cons_succ]
      exact ih v p i (by simpa using hi)

private theorem getD_out (xs : List Bool) (i : Nat) (hi : xs.length ≤ i) :
    xs.getD i false = false := by
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_none hi]
  rfl

private theorem getD_reverse (xs : List Bool) (i : Nat) (hi : i < xs.length) :
    xs.reverse.getD i false = xs.getD (xs.length - 1 - i) false := by
  rw [List.getD_eq_getElem?_getD,List.getElem?_reverse hi,List.getD_eq_getElem?_getD]

/-- Older-first finite words are reversed into the catalog's newest-first
state, with all cells beyond the represented word permanently white. -/
def asState (xs : List Bool) : Rule30ControlledResponse.State :=
  Rule30ControlledResponse.word xs.reverse

/-- Exact one-step semantic bridge, including all zero-default boundary cases. -/
theorem F_state (xs : List Bool) :
    asState (F xs) = Rule30ControlledResponse.diagonal (asState xs) := by
  funext k
  change (F xs).reverse.getD k false =
    xor (xs.reverse.getD k false) (xs.reverse.getD (k+1) false || xs.reverse.getD (k+2) false)
  by_cases hk : k < xs.length
  · let i := xs.length - 1 - k
    have hindex : i + k + 1 = xs.length := by dsimp [i]; omega
    have hi : i < xs.length := by omega
    have hp : (false :: xs).getD i false = xs.reverse.getD (k+1) false := by
      cases he : i with
      | zero =>
        rw [getD_out xs.reverse (k+1) (by simp only [List.length_reverse]; omega)]
        rfl
      | succ j =>
        rw [List.getD_cons_succ,getD_reverse xs (k+1) (by omega)]
        congr 1
        omega
    have hr : (false :: false :: xs).getD i false = xs.reverse.getD (k+2) false := by
      cases he : i with
      | zero =>
        rw [getD_out xs.reverse (k+2) (by simp only [List.length_reverse]; omega)]
        rfl
      | succ j =>
        cases j with
        | zero =>
          rw [getD_out xs.reverse (k+2) (by simp only [List.length_reverse]; omega)]
          rfl
        | succ j =>
          rw [List.getD_cons_succ,List.getD_cons_succ,getD_reverse xs (k+2) (by omega)]
          congr 1
          omega
    rw [getD_reverse (F xs) k (by simpa only [F_length] using hk),F_length]
    change (change false false xs).getD i false = _
    rw [change_getD xs false false i hi,getD_reverse xs k hk,hp,hr]
  · rw [getD_out (F xs).reverse k (by simp only [List.length_reverse,F_length]; omega),
        getD_out xs.reverse k (by simp only [List.length_reverse]; omega),
        getD_out xs.reverse (k+1) (by simp only [List.length_reverse]; omega),
        getD_out xs.reverse (k+2) (by simp only [List.length_reverse]; omega)]
    rfl

/-- Every finite-word update agrees with the existing catalog's literal map. -/
theorem evolution_state (xs : List Bool) (t : Nat) :
    asState (evolution t xs) = Rule30ControlledResponse.iterate (asState xs) t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [evolution,F_state,ih,Rule30ControlledResponse.iterate]

private theorem word_injective_length (xs ys : List Bool) (hl : xs.length = ys.length)
    (h : Rule30ControlledResponse.word xs = Rule30ControlledResponse.word ys) : xs = ys := by
  apply List.ext_getElem hl
  intro i hx hy
  have he := congrFun h i
  simpa only [Rule30ControlledResponse.word,List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hx,List.getElem?_eq_getElem hy,Option.getD_some] using he

theorem state_return_iff (xs : List Bool) (t : Nat) :
    Rule30ControlledResponse.iterate (asState xs) t = asState xs ↔ evolution t xs = xs := by
  rw [← evolution_state]
  constructor
  · intro h
    have hr := word_injective_length (evolution t xs).reverse xs.reverse
      (by simp only [List.length_reverse,evolution_length]) h
    have := congrArg List.reverse hr
    simpa only [List.reverse_reverse] using this
  · intro h
    rw [h]

/-- For every newest-first finite word, full-state eight-step return is
equivalent to two-step return after deleting the three newest cells. -/
theorem iterate_word_return_eight_iff (xs : List Bool) :
    Rule30ControlledResponse.iterate (Rule30ControlledResponse.word xs) 8 =
        Rule30ControlledResponse.word xs ↔
      Rule30ControlledResponse.iterate (Rule30ControlledResponse.word (xs.drop 3)) 2 =
        Rule30ControlledResponse.word (xs.drop 3) := by
  have h := return_eight_iff_prefix_two xs.reverse
  simp only [List.length_reverse,← List.reverse_drop] at h
  have e8 := state_return_iff xs.reverse 8
  have e2 := state_return_iff (xs.drop 3).reverse 2
  simpa only [asState,List.reverse_reverse] using (e8.trans h).trans e2.symm

private theorem word_drop (xs : List Bool) (n : Nat) :
    Rule30ControlledResponse.word (xs.drop n) =
      fun k => Rule30ControlledResponse.word xs (k+n) := by
  funext k
  simp [Rule30ControlledResponse.word,List.getD_eq_getElem?_getD,Nat.add_comm]

/-- The same criterion for every finitely supported catalog state. Shifting
by three removes its newest three cells and preserves its zero tail. -/
theorem iterate_finite_return_eight_iff (x : Rule30ControlledResponse.State)
    (W : Nat) (hx : ∀ k, W ≤ k → x k = false) :
    Rule30ControlledResponse.iterate x 8 = x ↔
      Rule30ControlledResponse.iterate (fun k => x (k+3)) 2 = (fun k => x (k+3)) := by
  let xs := (List.range W).map x
  have hxs : Rule30ControlledResponse.word xs = x := by
    funext k
    by_cases hk : k < W
    · simp [Rule30ControlledResponse.word,xs,List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem, hk]
    · have hw : W ≤ k := by omega
      rw [hx k hw]
      exact getD_out xs k (by simp [xs]; omega)
  have h := iterate_word_return_eight_iff xs
  rw [word_drop,hxs] at h
  exact h

end Ruliology.CellularAutomata.Rule30FiniteReturnEight
