module

public import Ruliology.CellularAutomata.Rule30ZeroBoundarySmall

/-!
# Death times of the zero-boundary left half: exact at width 52, lower bounds at 56 and 60

`Rule30ZeroBoundaryWidth52.q01_width_le_52` proves that every zero-boundary start supported at depths at most 52 has
a white depth-1 cell at some even time at most 96. This module gives a start that attains that bound, so the bound 96
is exact, and lower bounds at two larger widths.

* `width52_lower`: the start `w52 = 0x7dc2ff6fcc4fd` (bits are depths 1 to 52) is black at depth 1 at every even time
  below 96. With `Rule30ZeroBoundaryWidth52.q01_width_le_52`, the least uniform even death bound at width 52 is
  exactly 96. This module does not import that one, so that importing it does not build the four width-52
  certificate chunks.
* `width56_lower`, `width60_lower`: the starts `w56` and `w60` are black at depth 1 at every even time below 100 and
  below 114. So no uniform even death bound at width 56 is below 100, and none at width 60 is below 114.

Upper bounds at widths 56 and 60 are not proved here. The values 96, 100 and 114 sit 8, 12 and 6 below 2W, so the
death time is not of the form 2W − c with c fixed.

**Method.** A kernel computation through the kit's own packed evaluator. `w < 2 ^ W` by `decide`; `toFun w` is white
beyond depth W by `testBit_ge_of_lt`; bit 0 of `prun w (2 s)` is checked for every s below D / 2 by
`decide +kernel` (48, 50 and 57 packed orbits); and `run_toFun` turns that bit into the physical depth-1 cell
`zrow (toFun w) t 1`.
-/

set_option Elab.async false

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30ZeroBoundaryDeathTimes

open Rule30ZeroBoundary Rule30ZeroBoundarySmall

/-! ## The witnesses (bits are depths `1 .. W`; the wall at depth `0` is white) -/

/-- The width-52 witness: 51 bits, so supported at depths at most 52. -/
def w52 : Nat := 0x7dc2ff6fcc4fd

/-- The width-56 witness: 56 bits. -/
def w56 : Nat := 0x93d4b223f5b9b5

/-- The width-60 witness: 60 bits. -/
def w60 : Nat := 0xe77a4e77b8f99b5

theorem w52_lt : w52 < 2 ^ 52 := by decide
theorem w56_lt : w56 < 2 ^ 56 := by decide
theorem w60_lt : w60 < 2 ^ 60 := by decide

/-- `toFun r` is false beyond the width of `r`. -/
theorem toFun_width {r W : Nat} (h : r < 2 ^ W) (k : Nat) (hk : W < k) : toFun r k = false := by
  unfold toFun
  have h1 : k ≠ 0 := by omega
  simp only [h1, ite_false]
  exact testBit_ge_of_lt h (by omega)

/-- The physical depth-1 cell of the start `toFun r` at time `t` is bit `0` of the packed orbit (`run_toFun`). -/
theorem zrow_packed (r t : Nat) : zrow (toFun r) t 1 = (prun r t).testBit 0 := by
  rw [run_toFun]; rfl

/-! ## The packed orbits, kernel-evaluated -/

/-- Black at depth 1 at every even time below 96: 48 packed orbits. -/
theorem w52_black : ∀ s, s < 48 → (prun w52 (2 * s)).testBit 0 = true := by decide +kernel

/-- White at 96. -/
theorem w52_white : (prun w52 96).testBit 0 = false := by decide +kernel

/-- Black at depth 1 at every even time below 100: 50 packed orbits. -/
theorem w56_black : ∀ s, s < 50 → (prun w56 (2 * s)).testBit 0 = true := by decide +kernel

theorem w56_white : (prun w56 100).testBit 0 = false := by decide +kernel

/-- Black at depth 1 at every even time below 114: 57 packed orbits. -/
theorem w60_black : ∀ s, s < 57 → (prun w60 (2 * s)).testBit 0 = true := by decide +kernel

theorem w60_white : (prun w60 114).testBit 0 = false := by decide +kernel

/-! ## Survival below the bound, in the physical vocabulary -/

theorem survives_of_black {r D : Nat} (hb : ∀ s, s < D / 2 → (prun r (2 * s)).testBit 0 = true) (hD : D % 2 = 0) :
    ∀ t, t < D → t % 2 = 0 → zrow (toFun r) t 1 = true := by
  intro t ht he
  rw [zrow_packed]
  obtain ⟨s, rfl⟩ : ∃ s, t = 2 * s := ⟨t / 2, by omega⟩
  exact hb s (by omega)

theorem w52_survives : ∀ t, t < 96 → t % 2 = 0 → zrow (toFun w52) t 1 = true :=
  survives_of_black w52_black rfl

theorem w52_dies : zrow (toFun w52) 96 1 = false := by
  rw [zrow_packed]; exact w52_white

theorem w56_survives : ∀ t, t < 100 → t % 2 = 0 → zrow (toFun w56) t 1 = true :=
  survives_of_black w56_black rfl

theorem w56_dies : zrow (toFun w56) 100 1 = false := by
  rw [zrow_packed]; exact w56_white

theorem w60_survives : ∀ t, t < 114 → t % 2 = 0 → zrow (toFun w60) t 1 = true :=
  survives_of_black w60_black rfl

theorem w60_dies : zrow (toFun w60) 114 1 = false := by
  rw [zrow_packed]; exact w60_white

/-! ## The headline statements -/

/-- **A lower bound at width 52, attaining `Rule30ZeroBoundaryWidth52.q01_width_le_52`:** a start supported at depths
at most 52 with no even white time below 96. With that theorem, the least uniform even death bound at width 52 is
exactly 96. -/
theorem width52_lower :
    ∃ x : Nat → Bool, (∀ k, 52 < k → x k = false) ∧ (∀ t, t < 96 → t % 2 = 0 → zrow x t 1 = true) :=
  ⟨toFun w52, toFun_width w52_lt, w52_survives⟩

/-- **A lower bound at width 56:** a start supported at depths at most 56 with no even white time below 100. -/
theorem width56_lower :
    ∃ x : Nat → Bool, (∀ k, 56 < k → x k = false) ∧ (∀ t, t < 100 → t % 2 = 0 → zrow x t 1 = true) :=
  ⟨toFun w56, toFun_width w56_lt, w56_survives⟩

/-- **A lower bound at width 60:** a start supported at depths at most 60 with no even white time below 114. -/
theorem width60_lower :
    ∃ x : Nat → Bool, (∀ k, 60 < k → x k = false) ∧ (∀ t, t < 114 → t % 2 = 0 → zrow x t 1 = true) :=
  ⟨toFun w60, toFun_width w60_lt, w60_survives⟩

end Ruliology.CellularAutomata.Rule30ZeroBoundaryDeathTimes
