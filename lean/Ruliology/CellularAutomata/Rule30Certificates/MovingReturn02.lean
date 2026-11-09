module

public import Ruliology.CellularAutomata.Rule30MovingStrip

/-!
Certificate data and kernel-checked RUP refutation for moving return period 2.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Certificates.MovingReturn02

open Ruliology.CellularAutomata.Rule30RingOrbits
open Ruliology.CellularAutomata.Rule30MovingStrip

set_option linter.all false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev p : Nat := 2
abbrev q : Nat := 7
abbrev cols : Nat := 3
abbrev offset : Nat := 1
abbrev w : Nat := 4
def states : List Nat := [0, 1, 2, 3, 5, 6, 10, 13]
def base : List Nat := [1, 1, 1, 1, 1, 1, 1, 1]
def slope : List Nat := [0, 0, 0, 0, 1, 0, 1, 0]
def formula : List (List Nat) := stripFormula p q cols offset w states

-- Bit-mask clause database
noncomputable def M0 : Nat → Nat := (branch (nat_lit 0) (fun _ => nat_lit 0x40050000020018000000100a800000802900000100440000080120000010014000008006000000402a00000200a40000040110000020048000004005000002001800000100a800000802900000100440000080120000010014000008006000000402a00000200a40000040110000020048000004005000002001800000100a800000802900000100440000080120000010014000008006) (branch (nat_lit 1) (fun _ => nat_lit 0x2000000100400000080080000004010000002402a00000200a40000040110000020048000004005000002001800000100a800000802900000100440000080120000010014000008006000000402a00000200a40000040110000020048000004005000002001800000100a800000802900000100440000080120000010014000008006000000402a00000200a40000040110000020048000) (fun _ => nat_lit 0x80000000400000000040000010000000002000400000001100000400080000040020020010008000000004000008001000002008400000000140040000050000040014000000059000000019800000009600000002640000000a500000002980000000a900000002a80800000040100000020)))
noncomputable def get_M : Nat → Nat := M0

-- Packed proof steps
noncomputable def P0 : Nat → Nat := (branch (nat_lit 7) (branch (nat_lit 3) (branch (nat_lit 1) (branch (nat_lit 0) (fun _ => nat_lit 0x4001e01800d008045) (fun _ => nat_lit 0x1e01180100f008000e04804a010003)) (branch (nat_lit 2) (fun _ => nat_lit 0x3802200001e81c012c090094040007014000) (fun _ => nat_lit 0x3802000804c008047))) (branch (nat_lit 5) (branch (nat_lit 4) (fun _ => nat_lit 0x3002602404d02a01401e00f808800c00804c018048) (fun _ => nat_lit 0x10007806003409809c00804c010044)) (branch (nat_lit 6) (fun _ => nat_lit 0xf007800007a01004f00c005) (fun _ => nat_lit 0x1c00f80100f00e80a001004f010004)))) (branch (nat_lit 11) (branch (nat_lit 9) (branch (nat_lit 8) (fun _ => nat_lit 0x8804807803e008051) (fun _ => nat_lit 0x4808c01004f008049)) (branch (nat_lit 10) (fun _ => nat_lit 0x3801401004f008053) (fun _ => nat_lit 0x1000940f807e00c05200c054))) (branch (nat_lit 13) (branch (nat_lit 12) (fun _ => nat_lit 0x2009e04805500800c) (fun _ => nat_lit 0x2009e04805500800e)) (branch (nat_lit 14) (fun _ => nat_lit 0x4013c0300ac02005700c042) (fun _ => nat_lit 0xc02b004013c0180b0020057010043)))))
noncomputable def get_P : Nat → Nat := P0
noncomputable def getWord_P (idx : Nat) : Nat := get_P idx

noncomputable def getClause (i : Nat) : Nat :=
  strictNat i fun i => Nat.land
    (Nat.shiftRight (get_M (Nat.div i (nat_lit 32))) (Nat.mul (Nat.mod i (nat_lit 32)) (nat_lit 38))) (nat_lit 0x3fffffffff)


def transitionRow (t : Nat) : List (List Nat) := (List.range (q-2)).flatMap fun i => sixClauses (vid q t i) (vid q t (i+1)) (vid q t (i+2)) (vid q (t+1) i)
theorem formula_part0 : checkFormula getClause (transitionRow 0) 0 = true := by decide +kernel
theorem formula_part1 : checkFormula getClause (transitionRow 1) 30 = true := by decide +kernel
theorem formula_part2 : checkFormula getClause (periodFormula p q cols) 60 = true := by decide +kernel
theorem formula_part3 : checkFormula getClause (states.map (forbid q offset w)) 66 = true := by decide +kernel
theorem formula_shape : formula = (transitionRow 0) ++ (transitionRow 1) ++ (periodFormula p q cols) ++ (states.map (forbid q offset w)) := by
  simp only [formula, stripFormula, transitionFormula, show List.range p = [0, 1] from rfl, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc, transitionRow]
theorem formula_ok : checkFormula getClause formula 0 = true := by
  rw [formula_shape]
  apply checkFormula_append_ok formula_part0
  apply checkFormula_append_ok formula_part1
  apply checkFormula_append_ok formula_part2
  exact formula_part3
theorem rup_ok0 : replayPackedN getClause getWord_P 16 74 0 = true := by decide +kernel
theorem nil_ok : Nat.beq (getClause 89) 0 = true := by decide +kernel

theorem unsat : ∀ assign : Nat → Bool, ¬ (∀ c ∈ formula, Models assign c) := by
  intro a hm
  have hk0 : Known getClause a 74 := initial_known formula_ok hm
  have hk1 : Known getClause a 90 := replayPackedN_sound 16 74 0 hk0 rup_ok0
  exact unsat_of_known_nil nil_ok hk1

theorem strip_window_in_states (x : Int → Bool) (hx : orbit x p = x) (origin : Int) :
    ∃ s ∈ states, Matches x origin w s :=
  finite_strip_forces (by decide) (by decide) (by decide) unsat x hx origin

theorem potential_exact_ok : checkPotential w states base slope 8 2 = true := by decide +kernel
theorem potential_ok : checkPotential w states base slope 81 14 = true := by decide +kernel

theorem linear_words (m : Nat) :
    ∃ L : List (List Bool),
      L.length ≤ 81 + m * 14 ∧
      ∀ (x : Int → Bool), orbit x 2 = x → ∀ origin : Int, rowWord x origin m ∈ L :=
  linear_words_of_strip potential_ok strip_window_in_states m

end Ruliology.CellularAutomata.Rule30Certificates.MovingReturn02
