module

public import Ruliology.CellularAutomata.Rule30Jen

/-!
# Rule 30 from a single white cell, and rule 135

Two single-seed patterns are column `-1` of the usual rule-30 pattern in disguise.

* `cellW_succ`: rule 30 started from a single white cell on an all-black background is, after
  one step, a single black cell at position `1`: `cellW (t + 1) p = cell t (p - 1)`. So its
  center column at time `t + 1` is column `-1` of the usual pattern at time `t`.
* `cell135_succ`: rule 135 (`!left xor (center && right)`, the black-white conjugate of rule 30)
  from a single black cell is, from step `1` on, the usual rule-30 pattern shifted one step and
  one cell and complemented: `cell135 (t + 1) p = !cell t (p - 1)`. So its center column at time
  `t + 1` is `!cell t (-1)`.
* `problem1_black_or_white`, `problem1_30_or_135`: by Jen's theorem (`Rule30Jen.jen`, columns `0`
  and `-1` are not both eventually periodic), **the center column of rule 30 from a single black
  cell or the center column from a single white cell is not eventually periodic**, and likewise
  for rule 30 and rule 135 from a single black cell. Which one is not is left open.

By mirror symmetry, rule 86 (the mirror image of rule 30) and rule 149 (that of rule 135) have
the same single-seed center columns as rules 30 and 135; this is not formalized here.

Source: E. Jen, *Global properties of cellular automata*, J. Stat. Phys. 43 (1986) 219–242, for the
reduction to columns `0` and `-1`.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30WhiteSeed

open Rule30Jen

/-! ### Rule 30 from a single white cell -/

/-- Rule 30 from a single white cell at `0` on an all-black background. -/
def cellW : Nat → Int → Bool
  | 0, p => !decide (p = 0)
  | t + 1, p => rule (cellW t (p - 1)) (cellW t p) (cellW t (p + 1))

/-- After one step the white seed has become a single black cell at position `1`. -/
theorem cellW_succ : ∀ (t : Nat) (p : Int), cellW (t + 1) p = cell t (p - 1)
  | 0, p => by
    show rule (!decide (p - 1 = 0)) (!decide (p = 0)) (!decide (p + 1 = 0)) = decide (p - 1 = 0)
    rcases (show p = 1 ∨ p = 0 ∨ p = -1 ∨ (p ≠ 1 ∧ p ≠ 0 ∧ p ≠ -1) by omega) with
      h | h | h | ⟨h1, h2, h3⟩
    · subst h; decide
    · subst h; decide
    · subst h; decide
    · have e1 : decide (p - 1 = 0) = false := decide_eq_false (by omega)
      have e2 : decide (p = 0) = false := decide_eq_false (by omega)
      have e3 : decide (p + 1 = 0) = false := decide_eq_false (by omega)
      rw [e1, e2, e3]; rfl
  | t + 1, p => by
    show rule (cellW (t + 1) (p - 1)) (cellW (t + 1) p) (cellW (t + 1) (p + 1)) =
      rule (cell t (p - 1 - 1)) (cell t (p - 1)) (cell t (p - 1 + 1))
    rw [cellW_succ t (p - 1), cellW_succ t p, cellW_succ t (p + 1),
      show p + 1 - 1 = p by omega, show p - 1 + 1 = p by omega]

/-- **Black seed or white seed.** The center column of rule 30 from a single black cell and the
center column from a single white cell on a black background are not both eventually
periodic. -/
theorem problem1_black_or_white :
    ¬ (EventuallyPeriodic (fun t => cell t 0) ∧ EventuallyPeriodic (fun t => cellW t 0)) := by
  rintro ⟨h30, ⟨T, P, hP, hW⟩⟩
  have hm1 : EventuallyPeriodic (fun t => cell t (-1)) := by
    refine ⟨T, P, hP, fun t ht => ?_⟩
    have h := hW (t + 1) (by omega)
    simp only [] at h
    rw [show t + 1 + P = (t + P) + 1 by omega, cellW_succ, cellW_succ] at h
    exact h
  exact jen 0 (-1) (by omega) ⟨h30, hm1⟩

/-! ### Rule 135 -/

/-- Rule 135: `!left xor (center && right)`. -/
def rule135 (a b c : Bool) : Bool := xor (!a) (b && c)

/-- Rule 135 from a single black cell at position `0`. -/
def cell135 : Nat → Int → Bool
  | 0, p => decide (p = 0)
  | t + 1, p => rule135 (cell135 t (p - 1)) (cell135 t p) (cell135 t (p + 1))

theorem cell135_succ : ∀ (t : Nat) (p : Int), cell135 (t + 1) p = !cell t (p - 1)
  | 0, p => by
    show rule135 (decide (p - 1 = 0)) (decide (p = 0)) (decide (p + 1 = 0)) = !decide (p - 1 = 0)
    rcases (show p = 1 ∨ p = 0 ∨ p = -1 ∨ (p ≠ 1 ∧ p ≠ 0 ∧ p ≠ -1) by omega) with
      h | h | h | ⟨h1, h2, h3⟩
    · subst h; decide
    · subst h; decide
    · subst h; decide
    · have e1 : decide (p - 1 = 0) = false := decide_eq_false (by omega)
      have e2 : decide (p = 0) = false := decide_eq_false (by omega)
      have e3 : decide (p + 1 = 0) = false := decide_eq_false (by omega)
      rw [e1, e2, e3]; rfl
  | t + 1, p => by
    show rule135 (cell135 (t + 1) (p - 1)) (cell135 (t + 1) p) (cell135 (t + 1) (p + 1)) =
      !rule (cell t (p - 1 - 1)) (cell t (p - 1)) (cell t (p - 1 + 1))
    rw [cell135_succ t (p - 1), cell135_succ t p, cell135_succ t (p + 1),
      show p + 1 - 1 = p by omega, show p - 1 + 1 = p by omega]
    cases cell t (p - 1 - 1) <;> cases cell t (p - 1) <;> cases cell t p <;> rfl

theorem center135_succ (t : Nat) : cell135 (t + 1) 0 = !cell t (-1) := by
  rw [cell135_succ]; rfl

/-- **Rule 30 or rule 135.** The single-seed center columns of rule 30 and rule 135 are not both
eventually periodic. -/
theorem problem1_30_or_135 :
    ¬ (EventuallyPeriodic (fun t => cell t 0) ∧ EventuallyPeriodic (fun t => cell135 t 0)) := by
  rintro ⟨h30, ⟨T, P, hP, h135⟩⟩
  have hm1 : EventuallyPeriodic (fun t => cell t (-1)) := by
    refine ⟨T, P, hP, fun t ht => ?_⟩
    have e : cell135 ((t + P) + 1) 0 = cell135 (t + 1) 0 := by
      have h := h135 (t + 1) (by omega)
      simp only [] at h
      rw [show t + 1 + P = (t + P) + 1 by omega] at h
      exact h
    rw [center135_succ, center135_succ] at e
    show cell (t + P) (-1) = cell t (-1)
    revert e
    cases cell (t + P) (-1) <;> cases cell t (-1) <;> simp
  exact jen 0 (-1) (by omega) ⟨h30, hm1⟩

/-! ### Global Complement Conjugacy, Column Periodicity Equivalences, and Period-1 Exclusion for `cellW` and `cell135` -/

/-- **Exact Global Complement Conjugacy (`cell135_eq_not_cellW`):** for every time `t : Nat`
(including `t = 0`) and every spatial position `p : Int`, `cell135 t p = !cellW t p`. -/
theorem cell135_eq_not_cellW : ∀ (t : Nat) (p : Int), cell135 t p = !cellW t p
  | 0, p => by simp [cell135, cellW]
  | t + 1, p => by rw [cell135_succ, cellW_succ]

/-- **Inverse Global Complement Conjugacy (`cellW_eq_not_cell135`):** for every time `t : Nat` and
every spatial position `p : Int`, `cellW t p = !cell135 t p`. -/
theorem cellW_eq_not_cell135 (t : Nat) (p : Int) : cellW t p = !cell135 t p := by
  rw [cell135_eq_not_cellW, Bool.not_not]

/-- **Column Periodicity Equivalence for `cellW` (`eventuallyPeriodic_cellW_iff`):** for every
column `p : Int`, `fun t => cellW t p` is eventually periodic if and only if `fun t => cell t (p - 1)`
is eventually periodic. -/
theorem eventuallyPeriodic_cellW_iff (p : Int) :
    EventuallyPeriodic (fun t => cellW t p) ↔ EventuallyPeriodic (fun t => cell t (p - 1)) := by
  constructor
  · rintro ⟨T, P, hP, hW⟩
    refine ⟨T, P, hP, fun t ht => ?_⟩
    have h := hW (t + 1) (by omega)
    simp only [] at h
    rw [show t + 1 + P = (t + P) + 1 by omega, cellW_succ, cellW_succ] at h
    exact h
  · rintro ⟨T, P, hP, hc⟩
    refine ⟨T + 1, P, hP, fun t ht => ?_⟩
    rcases t with _ | t
    · omega
    · simp only []
      rw [show t + 1 + P = (t + P) + 1 by omega, cellW_succ, cellW_succ]
      exact hc t (by omega)

/-- **Direct Column Periodicity Equivalence Between `cell135` and `cellW`
(`eventuallyPeriodic_cell135_iff_cellW`):** for every column `p : Int`, `fun t => cell135 t p` is
eventually periodic if and only if `fun t => cellW t p` is eventually periodic. -/
theorem eventuallyPeriodic_cell135_iff_cellW (p : Int) :
    EventuallyPeriodic (fun t => cell135 t p) ↔ EventuallyPeriodic (fun t => cellW t p) := by
  constructor
  · rintro ⟨T, P, hP, h135⟩
    refine ⟨T, P, hP, fun t ht => ?_⟩
    have h := h135 t ht
    show cellW (t + P) p = cellW t p
    rw [cellW_eq_not_cell135 (t + P) p, cellW_eq_not_cell135 t p]
    exact congrArg Bool.not h
  · rintro ⟨T, P, hP, hW⟩
    refine ⟨T, P, hP, fun t ht => ?_⟩
    have h := hW t ht
    show cell135 (t + P) p = cell135 t p
    rw [cell135_eq_not_cellW (t + P) p, cell135_eq_not_cellW t p]
    exact congrArg Bool.not h

/-- **Column Periodicity Equivalence for `cell135` (`eventuallyPeriodic_cell135_iff`):** for every
column `p : Int`, `fun t => cell135 t p` is eventually periodic if and only if `fun t => cell t (p - 1)`
is eventually periodic. -/
theorem eventuallyPeriodic_cell135_iff (p : Int) :
    EventuallyPeriodic (fun t => cell135 t p) ↔ EventuallyPeriodic (fun t => cell t (p - 1)) :=
  (eventuallyPeriodic_cell135_iff_cellW p).trans (eventuallyPeriodic_cellW_iff p)

/-- **Jen's Adjacent-Column Theorem for `cellW` (`not_adjacent_cellW`):** for every `p : Int`,
columns `p` and `p + 1` of `cellW` are never both eventually periodic. -/
theorem not_adjacent_cellW (p : Int)
    (h0 : EventuallyPeriodic (fun t => cellW t p))
    (h1 : EventuallyPeriodic (fun t => cellW t (p + 1))) : False := by
  have hc0 := (eventuallyPeriodic_cellW_iff p).mp h0
  have hc1 := (eventuallyPeriodic_cellW_iff (p + 1)).mp h1
  rw [show p + 1 - 1 = p - 1 + 1 by omega] at hc1
  exact not_adjacent (p - 1) hc0 hc1

/-- **Jen's Adjacent-Column Theorem for `cell135` (`not_adjacent_cell135`):** for every `p : Int`,
columns `p` and `p + 1` of `cell135` are never both eventually periodic. -/
theorem not_adjacent_cell135 (p : Int)
    (h0 : EventuallyPeriodic (fun t => cell135 t p))
    (h1 : EventuallyPeriodic (fun t => cell135 t (p + 1))) : False := by
  exact not_adjacent_cellW p
    ((eventuallyPeriodic_cell135_iff_cellW p).mp h0)
    ((eventuallyPeriodic_cell135_iff_cellW (p + 1)).mp h1)

/-- **No Column of `cellW` Is Eventually Constant (`no_column_eventually_constant_cellW`):**
for every column `p : Int`, `fun t => cellW t p` is not eventually constant. -/
theorem no_column_eventually_constant_cellW (p : Int) :
    ¬ ∃ T b, ∀ t, T ≤ t → cellW t p = b := by
  rintro ⟨T, b, h⟩
  have hconst : ∀ t, T ≤ t → cell t (p - 1) = b := by
    intro t ht
    have e := h (t + 1) (by omega)
    rw [cellW_succ] at e
    exact e
  have hep0 : EventuallyPeriodic (fun t => cell t (p - 1)) :=
    ⟨T, 1, Nat.one_pos, fun t ht => (hconst (t + 1) (by omega)).trans (hconst t ht).symm⟩
  cases b
  · have hmono : ∀ t, T ≤ t → cell t (p - 1 + 1) = true → cell (t + 1) (p - 1 + 1) = true := by
      intro t ht h1
      show rule (cell t (p - 1 + 1 - 1)) (cell t (p - 1 + 1)) (cell t (p - 1 + 1 + 1)) = true
      rw [show p - 1 + 1 - 1 = p - 1 by omega, hconst t ht, h1]
      rfl
    by_cases hx : ∃ t, T ≤ t ∧ cell t (p - 1 + 1) = true
    · obtain ⟨t₀, ht₀, hf⟩ := hx
      have hk : ∀ k, cell (t₀ + k) (p - 1 + 1) = true := by
        intro k
        induction k with
        | zero => exact hf
        | succ k ih => exact hmono (t₀ + k) (by omega) ih
      have hconst1 : ∀ t, t₀ ≤ t → cell t (p - 1 + 1) = true := by
        intro t ht
        have := hk (t - t₀)
        rwa [show t₀ + (t - t₀) = t by omega] at this
      exact not_adjacent (p - 1) hep0
        ⟨t₀, 1, Nat.one_pos, fun t ht => (hconst1 (t + 1) (by omega)).trans (hconst1 t ht).symm⟩
    · have hconst1 : ∀ t, T ≤ t → cell t (p - 1 + 1) = false := by
        intro t ht
        cases hft : cell t (p - 1 + 1)
        · rfl
        · exact absurd ⟨t, ht, hft⟩ hx
      exact not_adjacent (p - 1) hep0
        ⟨T, 1, Nat.one_pos, fun t ht => (hconst1 (t + 1) (by omega)).trans (hconst1 t ht).symm⟩
  · have hleft : ∀ t, T ≤ t → cell t (p - 1 - 1) = false := by
      intro t ht
      have e := hconst (t + 1) (by omega)
      have hc : cell (t + 1) (p - 1) = rule (cell t (p - 1 - 1)) (cell t (p - 1)) (cell t (p - 1 + 1)) := rfl
      rw [hc, hconst t ht] at e
      revert e
      cases cell t (p - 1 - 1) <;> simp [rule]
    have hep_left : EventuallyPeriodic (fun t => cell t (p - 1 - 1)) :=
      ⟨T, 1, Nat.one_pos, fun t ht => (hleft (t + 1) (by omega)).trans (hleft t ht).symm⟩
    rw [show p - 1 = p - 1 - 1 + 1 by omega] at hep0
    exact not_adjacent (p - 1 - 1) hep_left hep0

/-- **No Column of `cell135` Is Eventually Constant (`no_column_eventually_constant_cell135`):**
for every column `p : Int`, `fun t => cell135 t p` is not eventually constant. -/
theorem no_column_eventually_constant_cell135 (p : Int) :
    ¬ ∃ T b, ∀ t, T ≤ t → cell135 t p = b := by
  rintro ⟨T, b, h⟩
  refine no_column_eventually_constant_cellW p ⟨T, !b, fun t ht => ?_⟩
  rw [cellW_eq_not_cell135, h t ht]

end Rule30WhiteSeed
end Ruliology.CellularAutomata
