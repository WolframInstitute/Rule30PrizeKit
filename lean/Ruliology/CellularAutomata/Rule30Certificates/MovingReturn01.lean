module

public import Ruliology.CellularAutomata.Rule30MovingStrip

/-!
Certificate data and kernel-checked RUP refutation for moving return period 1.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Certificates.MovingReturn01

open Ruliology.CellularAutomata.Rule30RingOrbits
open Ruliology.CellularAutomata.Rule30MovingStrip

set_option linter.all false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev p : Nat := 1
abbrev q : Nat := 5
abbrev cols : Nat := 3
abbrev offset : Nat := 1
abbrev w : Nat := 1
def states : List Nat := [0]
def base : List Nat := [1]
def slope : List Nat := [0]
def formula : List (List Nat) := stripFormula p q cols offset w states

-- Bit-mask clause database
noncomputable def M0 : Nat → Nat := (fun _ => nat_lit 0x10400000880104020200410080801040242a08290411081204050806010a820a41044204810142018042a08290411081204050806)
noncomputable def get_M : Nat → Nat := M0

-- Packed proof steps
noncomputable def P0 : Nat → Nat := (branch (nat_lit 0) (fun _ => nat_lit 0x802400c018008001) (branch (nat_lit 1) (fun _ => nat_lit 0x28019004013) (fun _ => nat_lit 0x3006005003200001a00c000)))
noncomputable def get_P : Nat → Nat := P0
noncomputable def getWord_P (idx : Nat) : Nat := get_P idx

noncomputable def getClause (i : Nat) : Nat :=
  strictNat i fun i => Nat.land
    (Nat.shiftRight (get_M (Nat.div i (nat_lit 32))) (Nat.mul (Nat.mod i (nat_lit 32)) (nat_lit 16))) (nat_lit 0xffff)


def transitionRow (t : Nat) : List (List Nat) := (List.range (q-2)).flatMap fun i => sixClauses (vid q t i) (vid q t (i+1)) (vid q t (i+2)) (vid q (t+1) i)
theorem formula_part0 : checkFormula getClause (transitionRow 0) 0 = true := by decide +kernel
theorem formula_part1 : checkFormula getClause (periodFormula p q cols) 18 = true := by decide +kernel
theorem formula_part2 : checkFormula getClause (states.map (forbid q offset w)) 24 = true := by decide +kernel
theorem formula_shape : formula = (transitionRow 0) ++ (periodFormula p q cols) ++ (states.map (forbid q offset w)) := by
  simp only [formula, stripFormula, transitionFormula, show List.range p = [0] from rfl, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc, transitionRow]
theorem formula_ok : checkFormula getClause formula 0 = true := by
  rw [formula_shape]
  apply checkFormula_append_ok formula_part0
  apply checkFormula_append_ok formula_part1
  exact formula_part2
theorem rup_ok0 : replayPackedN getClause getWord_P 3 25 0 = true := by decide +kernel
theorem nil_ok : Nat.beq (getClause 27) 0 = true := by decide +kernel

theorem unsat : ∀ assign : Nat → Bool, ¬ (∀ c ∈ formula, Models assign c) := by
  intro a hm
  have hk0 : Known getClause a 25 := initial_known formula_ok hm
  have hk1 : Known getClause a 28 := replayPackedN_sound 3 25 0 hk0 rup_ok0
  exact unsat_of_known_nil nil_ok hk1

theorem strip_window_in_states (x : Int → Bool) (hx : orbit x p = x) (origin : Int) :
    ∃ s ∈ states, Matches x origin w s :=
  finite_strip_forces (by decide) (by decide) (by decide) unsat x hx origin

theorem potential_exact_ok : checkPotential w states base slope 1 0 = true := by decide +kernel
theorem potential_ok : checkPotential w states base slope 81 14 = true := by decide +kernel

theorem linear_words (m : Nat) :
    ∃ L : List (List Bool),
      L.length ≤ 81 + m * 14 ∧
      ∀ (x : Int → Bool), orbit x 1 = x → ∀ origin : Int, rowWord x origin m ∈ L :=
  linear_words_of_strip potential_ok strip_window_in_states m

end Ruliology.CellularAutomata.Rule30Certificates.MovingReturn01
