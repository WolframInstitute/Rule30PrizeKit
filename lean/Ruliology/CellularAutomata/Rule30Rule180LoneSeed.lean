module

public import Ruliology.CellularAutomata.Rule30WedgeParity

/-!
# The lone-seed orbit of Rule 180

Rule 180 is `a ⊕ b ⊕ bc` (`Rule30WedgeParity.rule180Coef`), the left-permutive rule `a ⊕ b(1 ⊕ c)`. Its
orbit of the lone seed has a closed form: at an even time `t` the only black cell is at position `t`, and
at an odd time `t` the black cells are at `t - 1` and `t` (`orbit`, `evolve_seed`). Each step is a local
check on that support (`step_even`, `step_odd`), so the orbit is proved by induction on the support and
not by case analysis on the history.

Hence the center column is `1, 1, 0, 0, 0, …` (`center_eq`): black at times `0` and `1` and white from
time `2` on (`center_white`), and every cell left of position `t - 1` is white from time `2` on
(`white_left`). Rule 180 shares the odd wedge counts of Rule 30 (`Rule30WedgeParity.rule180_wedge_odd`), so
those counts say nothing about the center column.

This is a statement about one rule and one seed; it does not bear on Rule 30.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30Rule180LoneSeed

open Rule30WedgeParity

/-- The lone seed: one black cell at position `0`. -/
def seed : Int → Bool := fun j => decide (j = 0)

/-- The support of the Rule 180 orbit of the lone seed: position `t` at an even time `t`, positions
`t - 1` and `t` at an odd time `t`. -/
def orbit (t : Nat) (i : Int) : Bool :=
  if t % 2 = 0 then decide (i = (t : Int)) else decide (i = (t : Int) - 1 ∨ i = (t : Int))

theorem g180 (b c : Bool) : rule180Coef.g b c = xor b (b && c) := by
  cases b <;> cases c <;> rfl

/-- From a single black cell at `t` the next row has black cells at `t` and `t + 1`. -/
theorem step_even {t : Nat} (ht : t % 2 = 0) (i : Int) :
    stepC rule180Coef (orbit t) i = orbit (t + 1) i := by
  have ht' : (t + 1) % 2 ≠ 0 := by omega
  simp only [stepC, orbit, ht, ht', ite_true, ite_false, g180]
  push_cast
  by_cases h1 : i = (t : Int) <;> by_cases h2 : i = (t : Int) + 1 <;>
    by_cases h3 : i - 1 = (t : Int) <;> by_cases h4 : i + 1 = (t : Int) <;> simp_all <;> omega

/-- From black cells at `t - 1` and `t` the next row has the single black cell `t + 1`. -/
theorem step_odd {t : Nat} (ht : t % 2 ≠ 0) (i : Int) :
    stepC rule180Coef (orbit t) i = orbit (t + 1) i := by
  have ht' : (t + 1) % 2 = 0 := by omega
  simp only [stepC, orbit, ht, ht', ite_true, ite_false, g180]
  push_cast
  rcases (by omega : i ≤ (t : Int) - 3 ∨ i = (t : Int) - 2 ∨ i = (t : Int) - 1 ∨ i = (t : Int) ∨
      i = (t : Int) + 1 ∨ (t : Int) + 2 ≤ i) with h | h | h | h | h | h
  · have b : ¬ (i = (t : Int) - 1 ∨ i = (t : Int)) := by omega
    have c : ¬ (i = (t : Int) + 1) := by omega
    simp [b, c] <;> omega
  · have b : ¬ (i = (t : Int) - 1 ∨ i = (t : Int)) := by omega
    have c : ¬ (i = (t : Int) + 1) := by omega
    simp [b, c] <;> omega
  · have b : (i = (t : Int) - 1 ∨ i = (t : Int)) := by omega
    have d : (i + 1 = (t : Int) - 1 ∨ i + 1 = (t : Int)) := by omega
    have c : ¬ (i = (t : Int) + 1) := by omega
    simp [b, c, d] <;> omega
  · have b : (i = (t : Int) - 1 ∨ i = (t : Int)) := by omega
    have d : ¬ (i + 1 = (t : Int) - 1 ∨ i + 1 = (t : Int)) := by omega
    have c : ¬ (i = (t : Int) + 1) := by omega
    simp [b, c, d] <;> omega
  · simp [h] <;> omega
  · have b : ¬ (i = (t : Int) - 1 ∨ i = (t : Int)) := by omega
    have c : ¬ (i = (t : Int) + 1) := by omega
    simp [b, c] <;> omega

theorem evolve_seed (t : Nat) : evolveC rule180Coef t seed = orbit t := by
  induction t with
  | zero => funext i; simp [evolveC, seed, orbit]
  | succ t ih =>
    funext i
    show stepC rule180Coef (evolveC rule180Coef t seed) i = orbit (t + 1) i
    rw [ih]
    by_cases h : t % 2 = 0
    · exact step_even h i
    · exact step_odd h i

/-- **The center column of Rule 180 from the lone seed is `1, 1, 0, 0, 0, …`.** -/
theorem center_eq (t : Nat) : evolveC rule180Coef t seed 0 = decide (t ≤ 1) := by
  rw [evolve_seed]
  unfold orbit
  by_cases h : t % 2 = 0
  · simp only [h, ite_true]
    by_cases h0 : t = 0
    · subst h0; simp
    · have : ¬ ((0 : Int) = (t : Int)) := by omega
      simp [this]; omega
  · simp only [h, ite_false]
    by_cases h1 : t = 1
    · subst h1; simp
    · have : ¬ ((0 : Int) = (t : Int) - 1 ∨ (0 : Int) = (t : Int)) := by omega
      simp [this]; omega

theorem center_black (t : Nat) (ht : t ≤ 1) : evolveC rule180Coef t seed 0 = true := by
  rw [center_eq]; simp [ht]

/-- From time `2` on the center column is white: it is eventually constant. -/
theorem center_white (t : Nat) (_ht : 2 ≤ t) : evolveC rule180Coef t seed 0 = false := by
  rw [center_eq]; simp; omega

/-- From time `2` on every cell at a position `≤ t - 2` is white. -/
theorem white_left (t : Nat) (_ht : 2 ≤ t) (i : Int) (hi : i ≤ (t : Int) - 2) :
    evolveC rule180Coef t seed i = false := by
  rw [evolve_seed]
  unfold orbit
  by_cases h : t % 2 = 0
  · simp only [h, ite_true]; simp; omega
  · simp only [h, ite_false]; simp; omega

/-! ## Right-edge light-cone law `evolveC rule180Coef t seed t = true` and white right of `t` -/

/-- **Right-Edge Light-Cone Law for Rule 180 From the Lone Seed (`right_edge_and_white_right_of_light_cone`).** -/
theorem right_edge_and_white_right_of_light_cone (t : Nat) (i : Int) :
    evolveC rule180Coef t seed (t : Int) = true ∧
    ((t : Int) < i → evolveC rule180Coef t seed i = false) := by
  rw [evolve_seed]
  unfold orbit
  refine ⟨?_, fun hi => ?_⟩
  · by_cases h : t % 2 = 0 <;> simp [h]
  · by_cases h : t % 2 = 0 <;> simp [h] <;> omega

end Rule30Rule180LoneSeed
end Ruliology.CellularAutomata
