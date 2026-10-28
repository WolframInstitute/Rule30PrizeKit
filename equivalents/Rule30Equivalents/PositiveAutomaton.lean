module

public import Ruliology.CellularAutomata.Rule30Prize
public import Mathlib.Data.List.Basic
public import Lean.Elab.Tactic.Omega

/-!
# Positive words in Rule 30's three automaton states

The finite-word states are `A=(A,C)`, `B=(A,C) swap`, and `C=(B,C) swap`.
Bits are read older-first, products act right to left, and sections are
indexed by the input. These are the states already described in
`AutomatonGroup` for automaton group 2369: its labels `c,b,a` correspond
to `A,B,C` here. That identification is existing background, not a new
classification result.

* `act_memory` identifies all raw two-bit memories with a literal scan of
  the official `Rule30Jen.rule`; `act_A_eq_ruleScan` gives the white boundary.
* `positive_word_freeness` proves that positive state words define equal
  actions on every finite Boolean input if and only if the state words agree.
* `Bounds.faithful_at_twice_length` proves that, for words of n state factors,
  all inputs of exactly 2n bits suffice. `Bounds.distinguishing_input` gives
  such an input whenever two words of the same length are distinct.

The method is the reset-automaton freeness argument of P. V. Silva and
B. Steinberg, "On a Class of Automata Groups Generalizing Lamplighter Groups",
Int. J. Algebra Comput. 15 (2005), 1213-1234 (Theorem 2.2 in the author
preprint, https://cmup.fc.up.pt/cmup/pvsilva/pubs/reset.pdf), specialized to
the explicit two-bit reset table. The kernel proof establishes that table,
finite-word inverses, and the reset/cancellation induction directly.

The action domain is `List Bool`, including the empty word. No surjectivity
on natural numbers or eventually-white infinite inputs is assumed. The 2n
bound concerns distinguishing two transformations, not the time until two
observed Rule 30 traces separate. No reader-completeness or P1 claim is made.
-/

@[expose] public section

namespace Rule30Equivalents.PositiveAutomaton

inductive State where
  | A | B | C
  deriving DecidableEq

open State

def flip : State → Bool
  | A => false
  | B | C => true

def next : State → Bool → State
  | A, false => A
  | B, false => A
  | C, false => B
  | _, true => C

def act (q : State) : List Bool → List Bool
  | [] => []
  | b :: bs => Bool.xor b (flip q) :: act (next q b) bs

def memory (previous older : Bool) : State :=
  if previous then C else if older then B else A

def ruleScan (previous older : Bool) : List Bool → List Bool
  | [] => []
  | b :: bs => Ruliology.CellularAutomata.Rule30Jen.rule b previous older ::
      ruleScan b previous bs

/-- The automaton is literally the Rule30 xor/or scan with raw older memory. -/
theorem act_memory (previous older : Bool) (xs : List Bool) :
    act (memory previous older) xs = ruleScan previous older xs := by
  induction xs generalizing previous older with
  | nil => rfl
  | cons b bs ih =>
    have hf : flip (memory previous older) = (previous || older) := by
      cases previous <;> cases older <;> rfl
    have hn : next (memory previous older) b = memory b previous := by
      cases previous <;> cases older <;> cases b <;> rfl
    simp only [act, ruleScan, hn, ih, hf, Ruliology.CellularAutomata.Rule30Jen.rule]

theorem act_A_eq_ruleScan (xs : List Bool) :
    act A xs = ruleScan false false xs := by
  exact act_memory false false xs

def undo (q : State) : List Bool → List Bool
  | [] => []
  | b :: bs =>
    let x := Bool.xor b (flip q)
    x :: undo (next q x) bs

theorem act_undo (q : State) (xs : List Bool) : act q (undo q xs) = xs := by
  induction xs generalizing q with
  | nil => rfl
  | cons b bs ih =>
    cases q <;> cases b <;> simp [act, undo, flip, next, ih]

theorem undo_act (q : State) (xs : List Bool) : undo q (act q xs) = xs := by
  induction xs generalizing q with
  | nil => rfl
  | cons b bs ih =>
    cases q <;> cases b <;> simp [act, undo, flip, next, ih]

theorem act_bijective (q : State) : Function.Bijective (act q) := by
  constructor
  · intro x y h
    have h' := congrArg (undo q) h
    simpa only [undo_act] using h'
  · intro x
    exact ⟨undo q x, act_undo q x⟩

def run : List State → List Bool → List Bool
  | [], xs => xs
  | q :: qs, xs => act q (run qs xs)

def Equivalent (u v : List State) : Prop := ∀ xs, run u xs = run v xs

theorem run_append (u v : List State) (xs : List Bool) :
    run (u ++ v) xs = run u (run v xs) := by
  induction u with
  | nil => rfl
  | cons q qs ih => simp only [List.cons_append, run, ih]

theorem cancel_right (u v : List State) (q : State)
    (h : Equivalent (u ++ [q]) (v ++ [q])) : Equivalent u v := by
  intro xs
  have hx := h (undo q xs)
  simpa only [run_append, run, act_undo] using hx

def sectionState (q : State) : List Bool → State
  | [] => q
  | b :: bs => sectionState (next q b) bs

def sections : List State → List Bool → List State
  | [], _ => []
  | q :: qs, xs => sectionState q (run qs xs) :: sections qs xs

theorem sections_length (w : List State) (xs : List Bool) :
    (sections w xs).length = w.length := by
  induction w with
  | nil => rfl
  | cons q qs ih => simp only [sections, List.length_cons, ih]

theorem act_append (q : State) (xs ys : List Bool) :
    act q (xs ++ ys) = act q xs ++ act (sectionState q xs) ys := by
  induction xs generalizing q with
  | nil => rfl
  | cons b bs ih => simp only [List.cons_append, act, sectionState, ih]

theorem run_append_input (w : List State) (xs ys : List Bool) :
    run w (xs ++ ys) = run w xs ++ run (sections w xs) ys := by
  induction w generalizing xs ys with
  | nil => rfl
  | cons q qs ih =>
    simp only [run, sections]
    rw [ih, act_append]

theorem sections_append (u v : List State) (xs : List Bool) :
    sections (u ++ v) xs = sections u (run v xs) ++ sections v xs := by
  induction u generalizing xs with
  | nil => rfl
  | cons q qs ih =>
    simp only [List.cons_append, sections, run_append, ih]

theorem cancel_prefix {α : Type} (xs ys zs : List α) :
    xs ++ ys = xs ++ zs → ys = zs := by
  induction xs with
  | nil => intro h; exact h
  | cons q qs ih =>
    intro h
    apply ih
    exact congrArg List.tail h

theorem sections_equivalent (u v : List State) (h : Equivalent u v)
    (xs : List Bool) : Equivalent (sections u xs) (sections v xs) := by
  intro ys
  have he := h (xs ++ ys)
  rw [run_append_input, run_append_input, h xs] at he
  exact cancel_prefix _ _ _ he

def reset (x y : Bool) : State := if y then C else if x then B else A

/-- Every two-bit input resets the memory, independently of its initial state. -/
theorem two_bit_reset (q : State) (x y : Bool) :
    sectionState q [x,y] = reset x y := by
  cases q <;> cases x <;> cases y <;> rfl

theorem reset_zero (q : State) : sectionState q [false,false] = A := by
  cases q <;> rfl

/-- The modified reset functions distinguish the three states already at 00. -/
theorem reset_after_output (p q : State) :
    sectionState p (act q [false,false]) = q := by
  cases p <;> cases q <;> rfl

theorem sections_snoc_zero (u : List State) (q : State) :
    sections (u ++ [q]) [false,false] =
      sections u (act q [false,false]) ++ [A] := by
  rw [sections_append]
  simp only [run, sections, reset_zero]

theorem snoc_exists : ∀ (xs : List State), xs ≠ [] →
    ∃ u q, xs = u ++ [q] := by
  intro xs
  induction xs with
  | nil => intro h; exact False.elim (h rfl)
  | cons q qs ih =>
    intro _
    cases qs with
    | nil => exact ⟨[], q, rfl⟩
    | cons r rs =>
      obtain ⟨u, s, hu⟩ := ih (by simp)
      exact ⟨q :: u, s, by simp only [List.cons_append, hu]⟩

def lastFrom (d : State) : List State → State
  | [] => d
  | q :: qs => lastFrom q qs

def lastState (xs : List State) : State := lastFrom A xs

theorem lastFrom_append_single (d : State) (xs : List State) (q : State) :
    lastFrom d (xs ++ [q]) = q := by
  induction xs generalizing d with
  | nil => rfl
  | cons r rs ih => simp only [List.cons_append, lastFrom, ih]

theorem section_last (u : List State) (hu : u ≠ []) (q : State) :
    lastState (sections u (act q [false,false])) = q := by
  obtain ⟨v, p, rfl⟩ := snoc_exists u hu
  rw [sections_append]
  simp only [sections, run, reset_after_output, lastState, lastFrom_append_single]

theorem nil_of_length_zero (xs : List State) (h : xs.length = 0) : xs = [] := by
  cases xs with
  | nil => rfl
  | cons q qs => simp at h

/-- Reset/cancellation induction, including the empty and one-state cases. -/
theorem same_length_faithful : ∀ n (u v : List State),
    u.length = n → v.length = n → Equivalent u v → u = v := by
  intro n
  induction n with
  | zero =>
    intro u v hu hv _
    have hu0 : u = [] := nil_of_length_zero u hu
    have hv0 : v = [] := nil_of_length_zero v hv
    rw [hu0, hv0]
  | succ n ih =>
    intro u v hu hv h
    obtain ⟨U, q, rfl⟩ := snoc_exists u (by intro hz; rw [hz] at hu; simp at hu)
    obtain ⟨V, r, rfl⟩ := snoc_exists v (by intro hz; rw [hz] at hv; simp at hv)
    have hU : U.length = n := by simpa using hu
    have hV : V.length = n := by simpa using hv
    cases n with
    | zero =>
      have hU0 : U = [] := nil_of_length_zero U hU
      have hV0 : V = [] := nil_of_length_zero V hV
      subst U
      subst V
      have hz := h [false,false]
      cases q <;> cases r <;> simp_all [run, act, flip, next]
    | succ k =>
      have hUn : U ≠ [] := by intro hz; rw [hz] at hU; simp at hU
      have hVn : V ≠ [] := by intro hz; rw [hz] at hV; simp at hV
      have hs : Equivalent
          (sections U (act q [false,false]) ++ [A])
          (sections V (act r [false,false]) ++ [A]) := by
        simpa only [sections_snoc_zero] using
          sections_equivalent (U ++ [q]) (V ++ [r]) h [false,false]
      have hsec := cancel_right _ _ A hs
      have hw := ih _ _ ((sections_length _ _).trans hU)
        ((sections_length _ _).trans hV) hsec
      have hqr : q = r := by
        have he := congrArg lastState hw
        simpa only [section_last U hUn q, section_last V hVn r] using he
      subst r
      exact congrArg (fun w => w ++ [q]) (ih U V hU hV (cancel_right U V q h))

def pick : List State → Nat → State
  | [], _ => A
  | q :: _, 0 => q
  | _ :: qs, i+1 => pick qs i

theorem pick_middle (u v : List State) (q : State) :
    pick (u ++ q :: v) u.length = q := by
  induction u with
  | nil => rfl
  | cons p ps ih => simp only [List.cons_append, List.length_cons, pick, ih]

theorem pick_append_lt (u v : List State) (i : Nat) (hi : i < u.length) :
    pick (u ++ v) i = pick u i := by
  induction u generalizing i with
  | nil => simp at hi
  | cons q qs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simp only [List.cons_append, pick]
      exact ih i (by simpa using hi)

theorem separator_not_lt (u v : List State)
    (h : ∀ q : State, u ++ [q] ++ v = v ++ [q] ++ u) :
    ¬ u.length < v.length := by
  intro hlt
  have ha := congrArg (fun xs => pick xs u.length) (h A)
  have hb := congrArg (fun xs => pick xs u.length) (h B)
  simp only [List.append_assoc, List.singleton_append, pick_middle,
    pick_append_lt v _ _ hlt] at ha hb
  have bad : A = B := ha.trans hb.symm
  cases bad

/-- Equality on all finite inputs determines the complete positive state word. -/
theorem positive_word_faithful (u v : List State) (h : Equivalent u v) : u = v := by
  have hsep : ∀ q : State, u ++ [q] ++ v = v ++ [q] ++ u := by
    intro q
    apply same_length_faithful ((u ++ [q] ++ v).length)
    · rfl
    · simp only [List.length_append, List.length_singleton]
      omega
    · intro xs
      simp only [run_append, run]
      rw [h xs, h (act q (run v xs))]
  have hnot := separator_not_lt u v hsep
  have hnot' := separator_not_lt v u (fun q => (hsep q).symm)
  have hlen : v.length = u.length := by omega
  exact same_length_faithful u.length u v rfl hlen h

theorem positive_word_freeness (u v : List State) : Equivalent u v ↔ u = v := by
  constructor
  · exact positive_word_faithful u v
  · intro h
    subst v
    intro xs
    rfl


namespace Bounds

open Rule30Equivalents.PositiveAutomaton
open Rule30Equivalents.PositiveAutomaton.State

def AgreeUpTo (u v : List State) (n : Nat) : Prop :=
  ∀ xs : List Bool, xs.length ≤ n → run u xs = run v xs

theorem act_length (q : State) (xs : List Bool) : (act q xs).length = xs.length := by
  induction xs generalizing q with
  | nil => rfl
  | cons b bs ih => simp only [act, List.length_cons, ih]

theorem undo_length (q : State) (xs : List Bool) : (undo q xs).length = xs.length := by
  induction xs generalizing q with
  | nil => rfl
  | cons b bs ih => simp only [undo, List.length_cons, ih]

theorem run_length (w : List State) (xs : List Bool) : (run w xs).length = xs.length := by
  induction w with
  | nil => rfl
  | cons q qs ih => simp only [run, act_length, ih]

theorem cancel_right_upto (u v : List State) (q : State) (n : Nat)
    (h : AgreeUpTo (u ++ [q]) (v ++ [q]) n) : AgreeUpTo u v n := by
  intro xs hx
  have he := h (undo q xs) (by simpa only [undo_length] using hx)
  simpa only [run_append, run, act_undo] using he

theorem sections_upto (u v : List State) (xs : List Bool) (n : Nat)
    (h : AgreeUpTo u v (xs.length+n)) : AgreeUpTo (sections u xs) (sections v xs) n := by
  intro ys hy
  have he := h (xs ++ ys) (by simp only [List.length_append]; omega)
  have hx := h xs (by omega)
  rw [run_append_input, run_append_input, hx] at he
  exact cancel_prefix _ _ _ he

/-- Equality through twice the number of factors determines a positive word. -/
theorem faithful_upto : ∀ n (u v : List State),
    u.length=n → v.length=n → AgreeUpTo u v (2*n) → u=v := by
  intro n
  induction n with
  | zero =>
    intro u v hu hv _
    rw [nil_of_length_zero u hu, nil_of_length_zero v hv]
  | succ n ih =>
    intro u v hu hv h
    obtain ⟨U,q,rfl⟩ := snoc_exists u (by intro hz; rw [hz] at hu; simp at hu)
    obtain ⟨V,r,rfl⟩ := snoc_exists v (by intro hz; rw [hz] at hv; simp at hv)
    have hU : U.length=n := by simpa using hu
    have hV : V.length=n := by simpa using hv
    cases n with
    | zero =>
      have hU0 := nil_of_length_zero U hU
      have hV0 := nil_of_length_zero V hV
      subst U
      subst V
      have hz := h [false,false] (by decide)
      cases q <;> cases r <;> simp_all [run, act, Rule30Equivalents.PositiveAutomaton.flip, next]
    | succ k =>
      have hUn : U≠[] := by intro hz; rw [hz] at hU; simp at hU
      have hVn : V≠[] := by intro hz; rw [hz] at hV; simp at hV
      have hbudget : AgreeUpTo (U++[q]) (V++[r])
          ([false,false].length + 2*(k+1)) := by
        intro xs hx
        apply h xs
        simp only [List.length_cons, List.length_nil] at hx
        omega
      have hs : AgreeUpTo
          (sections U (act q [false,false]) ++ [A])
          (sections V (act r [false,false]) ++ [A]) (2*(k+1)) := by
        simpa only [sections_snoc_zero] using
          sections_upto (U++[q]) (V++[r]) [false,false] (2*(k+1)) hbudget
      have hsec := cancel_right_upto _ _ A _ hs
      have hw := ih _ _ ((sections_length _ _).trans hU)
        ((sections_length _ _).trans hV) hsec
      have hqr : q=r := by
        have he := congrArg lastState hw
        simpa only [section_last U hUn q, section_last V hVn r] using he
      subst r
      have hsmall : AgreeUpTo (U++[q]) (V++[q]) (2*(k+1)) := by
        intro xs hx
        exact h xs (by omega)
      exact congrArg (fun w => w++[q])
        (ih U V hU hV (cancel_right_upto U V q _ hsmall))

theorem take_append_length (xs ys : List Bool) :
    (xs ++ ys).take xs.length = xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    change b :: (bs ++ ys).take bs.length = b :: bs
    rw [ih]

theorem upto_of_exact (u v : List State) (n : Nat)
    (h : ∀ xs : List Bool, xs.length=n → run u xs=run v xs) : AgreeUpTo u v n := by
  intro xs hx
  let tail := List.replicate (n-xs.length) false
  have ht : (xs ++ tail).length=n := by
    simp only [List.length_append, List.length_replicate, tail]
    omega
  have he := h (xs ++ tail) ht
  rw [run_append_input, run_append_input] at he
  have hp := congrArg (fun ys : List Bool => ys.take xs.length) he
  have hpu : (run u xs ++ run (sections u xs) tail).take xs.length = run u xs := by
    rw [← run_length u xs]
    exact take_append_length _ _
  have hpv : (run v xs ++ run (sections v xs) tail).take xs.length = run v xs := by
    rw [← run_length v xs]
    exact take_append_length _ _
  rw [hpu,hpv] at hp
  exact hp

/-- All 2n-bit inputs suffice, uniformly in the positive composition length n. -/
theorem faithful_at_twice_length (n : Nat) (u v : List State)
    (hu : u.length=n) (hv : v.length=n)
    (h : ∀ xs : List Bool, xs.length=2*n → run u xs=run v xs) : u=v :=
  faithful_upto n u v hu hv (upto_of_exact u v (2*n) h)

theorem distinguishing_input (n : Nat) (u v : List State)
    (hu : u.length=n) (hv : v.length=n) (hne : u≠v) :
    ∃ xs : List Bool, xs.length=2*n ∧ run u xs≠run v xs := by
  apply Classical.byContradiction
  intro hn
  apply hne
  apply faithful_at_twice_length n u v hu hv
  intro xs hx
  apply Classical.byContradiction
  intro he
  exact hn ⟨xs,hx,he⟩


end Bounds

end Rule30Equivalents.PositiveAutomaton
