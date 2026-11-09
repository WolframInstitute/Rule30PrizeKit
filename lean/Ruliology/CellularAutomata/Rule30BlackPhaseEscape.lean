module

public import Ruliology.CellularAutomata.Rule30Coupled
public import Ruliology.CellularAutomata.Rule30PeriodTwo

@[expose] public section

/-!
# Rule 30: universal black-phase escape

Rule 30 updates a cell by `x' = x₋ xor (x or x₊)`. When the center cell is black at time `t`,
the `or` is `1` whatever the right neighbour is, so the next center value is the negation of the
left neighbour: `center (t+1) = ! cell t (-1)`. If the center column were eventually periodic
with period word `w`, this would force the left neighbour at every black phase of `w`,
independently of the right half: `cell t (-1) = ! w (t+1)` whenever `w t = true`.

The left half under a prescribed boundary column is `Rule30DrivenLeft.L w s`, and the real
pattern satisfies `cell (T+k) p = L w (cell T) k p` for `p ≤ 0` (`Rule30DrivenLeft.cell_eq_L`).
So an eventually periodic center would give a finite nonzero left start whose driven evolution
passes every black-phase check for ever.

* `UBE` (universal black-phase escape, **open**): every finite nonzero left start, driven by
  every periodic word with a black phase, eventually fails a black-phase check.
  `BlackEscapeOnCone` (**open**) is the same for the actual rows of the single-seed pattern only.
* `problem1_of_UBE`: `UBE → BlackEscapeOnCone → Problem1` (`blackEscape_of_UBE`,
  `problem1_of_blackEscape`).
* `allBlack_escape`: the all-black word escapes by time `m + 1`, from
  `Rule30DrivenLeft.ones_fails`.

**How `UBE` sits against the kit's coupled question and `Q01`.**
* `CQ_of_UBE`: `UBE` implies `Rule30Coupled.CQ ω` for every periodic `ω` with a black phase, the
  hypothesis of `Rule30Coupled.problem1_of_CQ`. A finite configuration with center column `ω`
  gives a coupled pair whose left half passes every black-phase check of `ω`; if that left half
  is white, it is replaced by the driven left half one step after the first black phase of `ω`
  (`Rule30DrivenLeft.L_first_black_driver_edge`, `Rule30DrivenLeft.L_add`).
* `Q01_of_UBE`: `UBE` implies `Rule30PeriodTwo.Q01`. `Q01` is the instance of `UBE` for the
  word `w t = (t even)`: while the black-phase checks of that word hold, the left half it drives
  equals the zero-driven left half (`driven_eq_zeroDriven`), and the checks are then exactly the
  condition of `Q01`, column `-1` black at every even step.
* Neither converse is known. `UBE` constrains the left half alone, for every periodic word at
  once; `CQ ω` also asks for a finite right half coupled to `ω`, and `Q01` is a single word.

Nothing here proves `UBE`, `BlackEscapeOnCone`, `CQ` or `Q01`.
-/

namespace Ruliology.CellularAutomata
namespace Rule30BlackPhaseEscape

open Rule30Jen Rule30Prize Rule30DrivenLeft


/-- **Universal black-phase escape** (open). For every finite nonzero left start `s`
(leftmost black at `-m`), every period `p > 0` and every `p`-periodic word `w` with a black phase,
the driven left half-line `L w s` violates, at some black phase `t`, the forced value
`cell t (-1) = ! w (t+1)`. Values of `s` at nonnegative sites are irrelevant to `L`. -/
def UBE : Prop :=
  ∀ (m : Nat) (s : Int → Bool) (p : Nat) (w : Nat → Bool),
    0 < m →
    (∀ i : Int, i < -(m : Int) → s i = false) →
    s (-(m : Int)) = true →
    0 < p → (∀ t, w (t + p) = w t) → (∃ j, w j = true) →
    ∃ t, w t = true ∧ L w s t (-1) ≠ !(w (t + 1))

/-- **Black-phase escape on the cone** (open). The same escape, from the actual rows `cell T`
of the single-cell pattern with `T ≥ 1`, for every periodic word with a black phase that starts
with the actual center value. -/
def BlackEscapeOnCone : Prop :=
  ∀ (T p : Nat) (w : Nat → Bool), 0 < T → 0 < p →
    (∀ t, w (t + p) = w t) → w 0 = center T →
    (∃ j, w j = true) →
    ∃ s, w s = true ∧ L w (fun i => cell T i) s (-1) ≠ !(w (s + 1))

/-- The Boolean identity behind the forced update at a black phase: if the left neighbour `l` is
forced to `!d` whenever the center `c` is black, then `l || c = l xor (c && d)`. With `d` the next
center value, this turns the driven update into the zero-boundary update plus an additive
forcing term `c && d` (the integer form of Bosdure, `Rule30ZeroBoundary.Q01_iff_integer`). -/
theorem or_eq_xor_of_black_phase (l c d : Bool)
    (hadmit : c = true → l = !d) :
    (l || c) = xor l (c && d) := by
  cases l <;> cases c <;> cases d <;> simp_all

/-- The all-black word escapes by time `m + 1`: the case `w = fun _ => true` of `UBE`,
from the kit's `ones_fails`. -/
theorem allBlack_escape {s : Int → Bool} {m : Nat} (hm : 0 < m)
    (hs0 : ∀ i : Int, i < -(m : Int) → s i = false)
    (hs1 : s (-(m : Int)) = true) :
    ∃ t, t ≤ m + 1 ∧
      L (fun _ => true) s t (-1) ≠ !(true : Bool) := by
  obtain ⟨t, ht, hb⟩ := ones_fails hm hs0 hs1
  exact ⟨t, ht, by simp [hb]⟩

/-- `UBE` contains the cone statement: the cone row `cell T` with `T ≥ 1` is a finite nonzero
left start (`real_edge`). -/
theorem blackEscape_of_UBE (hUBE : UBE) : BlackEscapeOnCone := by
  intro T p w hT hp hper _hw0 hsome
  obtain ⟨hedge0, hedge1⟩ := real_edge T
  exact hUBE T (fun i => cell T i) p w hT hedge0 hedge1 hp hper hsome

/-- `BlackEscapeOnCone` implies the official Problem 1, uniformly in transient and period.
If the center were periodic from `T`, take the period word from `S = T + 1` (so that the left
half-line at `S` is nonzero); it has a black phase by `center_not_eventually_constant`; the real
pattern's black phases force `cell (S+t) (-1) = ! w (t+1)` (`cell_left`), and the real left
half-line is the driven one (`cell_eq_L`), contradicting the escape. -/
theorem problem1_of_blackEscape (hE : BlackEscapeOnCone) : Problem1 := by
  intro hperiod
  obtain ⟨T, p, hp, hper⟩ := hperiod
  let S : Nat := T + 1
  let w : Nat → Bool := fun t => cell (S + t) 0
  have hS : 0 < S := by dsimp [S]; omega
  have hwper : ∀ t, w (t + p) = w t := by
    intro t
    have he := hper (S + t) (by dsimp [S]; omega)
    simpa [w, center, Nat.add_assoc] using he
  have hw0 : w 0 = center S := by simp [w, center]
  have hsome : ∃ j, w j = true := by
    apply Classical.byContradiction
    intro hn
    apply center_not_eventually_constant
    refine ⟨S, false, ?_⟩
    intro t ht
    have hf : w (t - S) = false := by
      cases he : w (t - S) with
      | false => rfl
      | true => exact False.elim (hn ⟨t - S, he⟩)
    have heq : S + (t - S) = t := by omega
    simpa [w, center, heq] using hf
  obtain ⟨t, ht, hbad⟩ := hE S p w hS hp hwper hw0 hsome
  apply hbad
  have hb : cell (S + t) 0 = true := ht
  have hl := cell_left (S + t) 0
  change cell (S + t) (-1) =
    xor (cell (S + t + 1) 0) (cell (S + t) 0 || cell (S + t) 1) at hl
  rw [hb] at hl
  have hforce : cell (S + t) (-1) = !(cell (S + t + 1) 0) := by
    cases he : cell (S + t + 1) 0 <;> simpa [he] using hl
  calc
    L w (fun i => cell S i) t (-1) = cell (S + t) (-1) := by
      simpa [w] using cell_eq_L S t (-1) (by decide)
    _ = !(w (t + 1)) := by simpa [w, Nat.add_assoc] using hforce

/-- `UBE` implies the official Problem 1. -/
theorem problem1_of_UBE (hUBE : UBE) : Problem1 :=
  problem1_of_blackEscape (blackEscape_of_UBE hUBE)

/-- At a black phase of a coupled column, the left neighbour is forced: `L ω s t (-1)` is the
negation of the next center value. -/
theorem coupled_black_phase {ω : Nat → Bool} {s : Int → Bool} {x : Nat → Bool}
    (hc : Rule30Coupled.Coupled ω s x) {t : Nat} (ht : ω t = true) :
    L ω s t (-1) = !(ω (t + 1)) := by
  have h := hc t
  rw [ht] at h
  revert h
  cases L ω s t (-1) <;> cases ω (t + 1) <;> simp [rule]

/-- **`UBE` gives the coupled question for every periodic column with a black phase.** So `UBE`
gives `Problem1` also through `Rule30Coupled.problem1_of_CQ`. -/
theorem CQ_of_UBE (hUBE : UBE) (ω : Nat → Bool)
    (hper : ∃ P, 0 < P ∧ ∀ t, ω (t + P) = ω t) (hblack : ∃ t, ω t = true) :
    Rule30Coupled.CQ ω := by
  rintro ⟨s, x, ⟨W, hW⟩, _, hc⟩
  obtain ⟨P, hP, hωP⟩ := hper
  rcases bounded_all_white_or_has_edge s W hW with hwhite | ⟨m, hm, _, hs0, hs1⟩
  · -- white left half: restart one step after the first black phase
    obtain ⟨t₀, ht₀, hfirst⟩ := exists_least_nat hblack
    have hwh : ∀ k < t₀, ω k = false := by
      intro k hk
      cases h : ω k with
      | false => rfl
      | true => exact False.elim (hfirst k hk h)
    obtain ⟨hedge0, hedge1⟩ := L_first_black_driver_edge hwhite hwh ht₀
    let ω' : Nat → Bool := fun k => ω (t₀ + 1 + k)
    have hper' : ∀ t, ω' (t + P) = ω' t := by
      intro t
      show ω (t₀ + 1 + (t + P)) = ω (t₀ + 1 + t)
      rw [show t₀ + 1 + (t + P) = (t₀ + 1 + t) + P by omega, hωP]
    have hblack' : ∃ j, ω' j = true := by
      refine ⟨P - 1, ?_⟩
      show ω (t₀ + 1 + (P - 1)) = true
      rw [show t₀ + 1 + (P - 1) = t₀ + P by omega, hωP]
      exact ht₀
    obtain ⟨t, ht, hbad⟩ := hUBE 1 (L ω s (t₀ + 1)) P ω' (by decide)
      (fun p hp => hedge0 p (by simpa using hp)) (by simpa using hedge1) hP hper' hblack'
    apply hbad
    have hL := L_add ω s (t₀ + 1) t (-1) (by decide)
    have hcheck := coupled_black_phase hc (t := t₀ + 1 + t) ht
    rw [← hL]
    rw [hcheck]
    rfl
  · obtain ⟨t, ht, hbad⟩ := hUBE m s P ω hm hs0 hs1 hP hωP hblack
    exact hbad (coupled_black_phase hc ht)

/-- The word black at even times and white at odd times. -/
def evenWord (t : Nat) : Bool := decide (t % 2 = 0)

/-- While column `-1` of the zero-driven left half is black at every even step, the left half
driven by `evenWord` equals the zero-driven one. -/
theorem driven_eq_zeroDriven {s : Int → Bool}
    (hall : ∀ k, L (fun _ => false) s (2 * k) (-1) = true) :
    ∀ t : Nat, ∀ p : Int, p < 0 → L evenWord s t p = L (fun _ => false) s t p := by
  intro t
  induction t with
  | zero => intro p hp; rw [L_zero hp, L_zero hp]
  | succ t ih =>
    intro p hp
    rw [L_succ hp, L_succ hp, ih (p - 1) (by omega), ih p hp]
    by_cases hq : p + 1 < 0
    · rw [ih (p + 1) hq]
    · have hp1 : p = -1 := by omega
      subst hp1
      rw [show (-1 : Int) + 1 = 0 by rfl, L_col0, L_col0]
      by_cases he : t % 2 = 0
      · have hb := hall (t / 2)
        rw [show 2 * (t / 2) = t by omega] at hb
        rw [hb]
        cases L (fun _ => false) s t (-1 - 1) <;> cases evenWord t <;> rfl
      · have hw : evenWord t = false := by simp [evenWord, he]
        rw [hw]

/-- **`UBE` implies `Q01`.** `Q01` is the instance of `UBE` for `evenWord`. -/
theorem Q01_of_UBE (hUBE : UBE) : Rule30PeriodTwo.Q01 := by
  intro m s hm hs0 hs1 hall
  obtain ⟨t, ht, hbad⟩ := hUBE m s 2 evenWord hm hs0 hs1 (by decide)
    (fun t => by simp [evenWord, Nat.add_mod_right]) ⟨0, rfl⟩
  have he : t % 2 = 0 := by simpa [evenWord] using ht
  have hn : evenWord (t + 1) = false := by simp [evenWord]; omega
  apply hbad
  rw [driven_eq_zeroDriven hall t (-1) (by decide), hn]
  have hb := hall (t / 2)
  rw [show 2 * (t / 2) = t by omega] at hb
  rw [hb]; rfl

end Rule30BlackPhaseEscape
end Ruliology.CellularAutomata
