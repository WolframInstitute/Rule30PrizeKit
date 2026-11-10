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

/-! ## Period-indexed black-phase escape `UBEAt p`, unconditional `UBEAt 1`, and the equivalence `UBEAt 2 ↔ Q01` -/

/-- **Black-phase escape at a fixed period `p` (`UBEAt p`):**
for every finite nonzero left start `s` (leftmost black at `-m`) and every `p`-periodic word `w`
with a black phase, `L w s` violates `L w s t (-1) = !(w (t + 1))` at some black phase `t`. -/
def UBEAt (p : Nat) : Prop :=
  ∀ (m : Nat) (s : Int → Bool) (w : Nat → Bool),
    0 < m →
    (∀ i : Int, i < -(m : Int) → s i = false) →
    s (-(m : Int)) = true →
    (∀ t, w (t + p) = w t) → (∃ j, w j = true) →
    ∃ t, w t = true ∧ L w s t (-1) ≠ !(w (t + 1))

/-- **`UBE` is equivalent to `UBEAt p` for all `p > 0` (`UBE_iff_forall_UBEAt`).** -/
theorem UBE_iff_forall_UBEAt : UBE ↔ ∀ p : Nat, 0 < p → UBEAt p := by
  constructor
  · intro h p hp m s w hm hs0 hs1 hper hblack
    exact h m s p w hm hs0 hs1 hp hper hblack
  · intro h m s p w hm hs0 hs1 hp hper hblack
    exact h p hp m s w hm hs0 hs1 hper hblack

/-- Every `1`-periodic word `w` is constant (`periodic_one_const`). -/
theorem periodic_one_const {w : Nat → Bool} (hper : ∀ t, w (t + 1) = w t) :
    ∀ t : Nat, w t = w 0
  | 0 => rfl
  | t + 1 => by rw [← periodic_one_const hper t, ← hper t]

/-- **Unconditional Period-1 Black-Phase Escape (`UBEAt_one`):**
every `1`-periodic word with a black phase is identically `true`, so `UBEAt 1` holds unconditionally
by `allBlack_escape`. -/
theorem UBEAt_one : UBEAt 1 := by
  intro m s w hm hs0 hs1 hper ⟨j, hj⟩
  have hw0 : w 0 = true := by rw [← periodic_one_const hper j]; exact hj
  have hwall : w = (fun _ => true) := funext (fun t => by rw [periodic_one_const hper t, hw0])
  subst hwall
  obtain ⟨t, _, hbad⟩ := allBlack_escape hm hs0 hs1
  exact ⟨t, rfl, hbad⟩

/-- **Converse of `driven_eq_zeroDriven` (`zeroDriven_of_evenWord_admissible`):**
if `L evenWord s` satisfies `L evenWord s (2 * k) (-1) = true` at every even step `2 * k`, then
`L evenWord s` coincides with the zero-driven left half `L (fun _ => false) s` at all times `t`
and negative positions `p < 0`. -/
theorem zeroDriven_of_evenWord_admissible {s : Int → Bool}
    (hadm : ∀ k, L evenWord s (2 * k) (-1) = true) :
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
      · have hb : L (fun _ => false) s t (-1) = true := by
          rw [← ih (-1) (by decide), show t = 2 * (t / 2) by omega]
          exact hadm (t / 2)
        rw [hb]
        cases L (fun _ => false) s t (-1 - 1) <;> cases evenWord t <;> rfl
      · have hw : evenWord t = false := by simp [evenWord, he]
        rw [hw]

/-- **One-Step Left-Edge Shift (`L_one_step_edge`):**
if `s` has its leftmost black cell at `-m` (`0 < m`), then after one step under any boundary word `w`,
`L w s 1` has its leftmost black cell at `-(m + 1)`. -/
theorem L_one_step_edge (w : Nat → Bool) {s : Int → Bool} {m : Nat} (hm : 0 < m)
    (hs0 : ∀ i : Int, i < -(m : Int) → s i = false)
    (hs1 : s (-(m : Int)) = true) :
    (∀ i : Int, i < -((m + 1 : Nat) : Int) → L w s 1 i = false) ∧
      L w s 1 (-((m + 1 : Nat) : Int)) = true := by
  refine ⟨fun i hi => ?_, ?_⟩
  · have hi0 : i < 0 := by omega
    rw [L_succ hi0, L_zero (by omega), L_zero hi0, L_zero (by omega),
        hs0 (i - 1) (by omega), hs0 i (by omega), hs0 (i + 1) (by omega)]
    rfl
  · have hm0 : -((m + 1 : Nat) : Int) < 0 := by omega
    rw [L_succ hm0, L_zero (by omega), L_zero hm0, L_zero (by omega),
        hs0 (-((m + 1 : Nat) : Int) - 1) (by omega),
        hs0 (-((m + 1 : Nat) : Int)) (by omega),
        show -((m + 1 : Nat) : Int) + 1 = -(m : Int) by omega, hs1]
    rfl

/-- The word white at even times and black at odd times (`oddWord t = decide (t % 2 = 1)`). -/
def oddWord (t : Nat) : Bool := decide (t % 2 = 1)

theorem oddWord_succ_eq_evenWord (t : Nat) : oddWord (1 + t) = evenWord t := by
  rcases Nat.mod_two_eq_zero_or_one t with h | h <;> simp [oddWord, evenWord, h] <;> omega

/-- Every `2`-periodic word `w` is determined by `w 0` and `w 1` (`periodic_two_eq`). -/
theorem periodic_two_eq {w : Nat → Bool} (hper : ∀ t, w (t + 2) = w t) :
    ∀ t : Nat, w t = if t % 2 = 0 then w 0 else w 1 := by
  intro t
  have hdiv : ∀ k : Nat, w (2 * k) = w 0 ∧ w (2 * k + 1) = w 1 := by
    intro k
    induction k with
    | zero => exact ⟨rfl, rfl⟩
    | succ k ih =>
      refine ⟨?_, ?_⟩
      · rw [show 2 * (k + 1) = 2 * k + 2 by omega, hper]; exact ih.1
      · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega, hper]; exact ih.2
  rcases Nat.mod_two_eq_zero_or_one t with he | ho
  · rw [ite_eq_left he, show t = 2 * (t / 2) by omega, (hdiv (t / 2)).1]
  · rw [ite_eq_right (by omega), show t = 2 * (t / 2) + 1 by omega, (hdiv (t / 2)).2]

/-- **`Q01` implies `evenWord` escape (`evenWord_escape_of_Q01`).** -/
theorem evenWord_escape_of_Q01 (hQ : Rule30PeriodTwo.Q01) {m : Nat} {s : Int → Bool}
    (hm : 0 < m) (hs0 : ∀ i : Int, i < -(m : Int) → s i = false) (hs1 : s (-(m : Int)) = true) :
    ∃ t, evenWord t = true ∧ L evenWord s t (-1) ≠ !(evenWord (t + 1)) := by
  apply Classical.byContradiction
  intro hno
  have hadm : ∀ k, L evenWord s (2 * k) (-1) = true := by
    intro k
    have hev : evenWord (2 * k) = true := by simp [evenWord]
    have hnx : evenWord (2 * k + 1) = false := by simp [evenWord]
    cases hb : L evenWord s (2 * k) (-1)
    · exfalso
      apply hno
      refine ⟨2 * k, hev, ?_⟩
      rw [hb, hnx]; decide
    · rfl
  have hzero : ∀ k, L (fun _ => false) s (2 * k) (-1) = true := by
    intro k
    rw [← zeroDriven_of_evenWord_admissible hadm (2 * k) (-1) (by decide)]
    exact hadm k
  exact hQ m s hm hs0 hs1 hzero

/-- **`Q01` implies `oddWord` escape (`oddWord_escape_of_Q01`).** -/
theorem oddWord_escape_of_Q01 (hQ : Rule30PeriodTwo.Q01) {m : Nat} {s : Int → Bool}
    (hm : 0 < m) (hs0 : ∀ i : Int, i < -(m : Int) → s i = false) (hs1 : s (-(m : Int)) = true) :
    ∃ t, oddWord t = true ∧ L oddWord s t (-1) ≠ !(oddWord (t + 1)) := by
  rcases L_one_step_edge oddWord hm hs0 hs1 with ⟨hs0', hs1'⟩
  obtain ⟨t, ht, hbad⟩ := evenWord_escape_of_Q01 hQ (m := m + 1) (s := L oddWord s 1)
    (by omega) hs0' hs1'
  refine ⟨1 + t, ?_, ?_⟩
  · rw [oddWord_succ_eq_evenWord]; exact ht
  · have hshift : (fun k => oddWord (1 + k)) = evenWord := funext oddWord_succ_eq_evenWord
    have hL := L_add oddWord s 1 t (-1) (by decide)
    rw [hshift] at hL
    rw [hL, show 1 + t + 1 = 1 + (t + 1) by omega, oddWord_succ_eq_evenWord]
    exact hbad

/-- **Exact Equivalence of Period-2 Black-Phase Escape and `Q01` (`UBEAt_two_iff_Q01`):**
`UBEAt 2` holds if and only if `Rule30PeriodTwo.Q01` holds. -/
theorem UBEAt_two_iff_Q01 : UBEAt 2 ↔ Rule30PeriodTwo.Q01 := by
  constructor
  · intro h2 m s hm hs0 hs1 hall
    obtain ⟨t, ht, hbad⟩ := h2 m s evenWord hm hs0 hs1
      (fun t => by simp [evenWord, Nat.add_mod_right]) ⟨0, rfl⟩
    have he : t % 2 = 0 := by simpa [evenWord] using ht
    have hn : evenWord (t + 1) = false := by simp [evenWord]; omega
    apply hbad
    rw [driven_eq_zeroDriven hall t (-1) (by decide), hn]
    have hb := hall (t / 2)
    rw [show 2 * (t / 2) = t by omega] at hb
    rw [hb]; rfl
  · intro hQ m s w hm hs0 hs1 hper ⟨j, hj⟩
    have hw_eq := periodic_two_eq hper
    cases hw0 : w 0 <;> cases hw1 : w 1
    · have hfalse := hw_eq j
      rw [hw0, hw1] at hfalse
      split at hfalse <;> (rw [hfalse] at hj; exact Bool.noConfusion hj)
    · have hodd : w = oddWord := funext (fun t => by
        rw [hw_eq t, hw0, hw1]; unfold oddWord; rcases Nat.mod_two_eq_zero_or_one t with h | h <;> simp [h])
      subst hodd
      exact oddWord_escape_of_Q01 hQ hm hs0 hs1
    · have heven : w = evenWord := funext (fun t => by
        rw [hw_eq t, hw0, hw1]; unfold evenWord; rcases Nat.mod_two_eq_zero_or_one t with h | h <;> simp [h])
      subst heven
      exact evenWord_escape_of_Q01 hQ hm hs0 hs1
    · have hall1 : w = (fun _ => true) := funext (fun t => by
        rw [hw_eq t, hw0, hw1]; split <;> rfl)
      subst hall1
      obtain ⟨t, _, hbad⟩ := allBlack_escape hm hs0 hs1
      exact ⟨t, rfl, hbad⟩

end Rule30BlackPhaseEscape
end Ruliology.CellularAutomata
