module

public import Ruliology.CellularAutomata.Rule30ResetCompactness

/-! Windows that catch every tick, and the relaxed doubling lemma, on pointed recurrent
strips. The open reset hypothesis is confined to a first clock loss and exactly the two
white intervals starting there. -/
@[expose] public section

namespace Ruliology.CellularAutomata.Rule30RelaxedWindows

open Ruliology.CellularAutomata
open Rule30AgedLeftDiagonals Rule30EveryKStatement
open Ruliology.CellularAutomata.Rule30RecurrentStrip (Clock Reset dyadic_prefix_clock)
open Ruliology.CellularAutomata.Rule30RootedWhiteReturns (Column first_clock_loss unbounded_anchors)
open Ruliology.CellularAutomata.Rule30ResetCompactness (LInfinity cap_of_unbounded_resets)

abbrev PrefixClocks (d : Nat → Column) := ∀ m, ∃ p, 0 < p ∧ Clock d m p
def White (d : Nat → Column) (a : Nat) := ∀ t, d a t = false

/-- The least prefix clock is p = 2^e through a. The next column flips at p,
so a + 1 is the first wheel at which that clock fails. -/
structure FirstLoss (d : Nat → Column) (a e : Nat) : Prop where
  clock : Clock d a (2^e)
  least : ∀ q, 0 < q → Clock d a q → 2^e ≤ q
  white : White d a
  flip : ∀ t, d (a+1) (t+2^e) = !(d (a+1) t)

def NextWhite (d : Nat → Column) (a b : Nat) :=
  a < b ∧ White d b ∧ ∀ i, a < i → i < b → ¬ White d i

/-- Both ends of the closed run belong to the window at the same tick s. -/
def Catch (d : Nat → Column) (a c s : Nat) :=
  ∃ j n, a ≤ j ∧ j+1+n ≤ c ∧ Reset (fun i => d i s) j n

/-- A white middle wheel cannot be strictly inside the black run. Thus a
catch in the combined window occurs wholly in one of its two stretches. -/
theorem catch_split {d : Nat → Column} {a b c s : Nat} (hab : a ≤ b) (hbc : b ≤ c)
    (white : d b s = false) : Catch d a c s ↔ Catch d a b s ∨ Catch d b c s := by
  constructor
  · rintro ⟨j, n, ha, hc, reset⟩
    by_cases left : j+1+n ≤ b
    · exact Or.inl ⟨j, n, ha, left, reset⟩
    by_cases right : b ≤ j
    · exact Or.inr ⟨j, n, right, hc, reset⟩
    have black := reset.2.2.1 (b-(j+1)) (by omega)
    rw [show j+1+(b-(j+1)) = b by omega] at black
    exact absurd (white.symm.trans black) (by decide)
  · rintro (⟨j, n, ha, hb, reset⟩ | ⟨j, n, hb, hc, reset⟩)
    · exact ⟨j, n, ha, Nat.le_trans hb hbc, reset⟩
    · exact ⟨j, n, Nat.le_trans hab hb, hc, reset⟩

/-- The first relaxation of the doubling lemma, in its rooted strip form. -/
def DLMinusOne : Prop := ∀ (d : Nat → Column), Recurrence d → d 0 0 = true →
  PrefixClocks d → ∀ a e b c, FirstLoss d a e → NextWhite d a b →
    NextWhite d b c → ∀ s, Catch d a c s

theorem unbounded_first_losses {d : Nat → Column} (hd : Recurrence d)
    (h0 : d 0 0 = true) (clocks : PrefixClocks d) (lo : Nat) :
    ∃ a e, lo ≤ a ∧ FirstLoss d a e := by
  have recurrent : ∀ i, ∃ p, 0 < p ∧ PeriodFrom (d i) 0 p := by
    intro i
    obtain ⟨p, hp, hclock⟩ := clocks i
    exact ⟨p, hp, hclock i (by omega)⟩
  obtain ⟨e, clock, least⟩ := dyadic_prefix_clock hd h0 recurrent (lo+1)
  obtain ⟨a, ha, _, clockA, white, flip⟩ :=
    first_clock_loss hd h0 recurrent (Nat.two_pow_pos e) (by omega : 1 ≤ lo+1) clock
  exact ⟨a, e, by omega, clockA,
    fun q hq hclock => least q hq (fun i hi => hclock i (by omega)), white, flip⟩

theorem exists_next_white {d : Nat → Column} (hd : Recurrence d)
    (h0 : d 0 0 = true) (clocks : PrefixClocks d) (a : Nat) :
    ∃ b, NextWhite d a b := by
  obtain ⟨b, hab, white, black⟩ := unbounded_anchors hd h0 clocks (a+1)
  clear black
  change White d b at white
  classical
  induction b using Nat.strongRecOn with
  | ind b ih =>
    by_cases earlier : ∃ i, a < i ∧ i < b ∧ White d i
    · obtain ⟨i, hai, hib, hi⟩ := earlier
      exact ih i hib hai hi
    · exact ⟨b, hab, white, fun i hai hib hi => earlier ⟨i, hai, hib, hi⟩⟩

/-- The window argument only uses unbounded starts and a catch in the
prescribed phase. Window choices can depend on the strip and the cutoff. -/
theorem lInfinity_of_windows
    (windows : ∀ (d : Nat → Column), Recurrence d → d 0 0 = true → PrefixClocks d →
      ∀ lo, ∃ a c, lo ≤ a ∧ ∀ s, Catch d a c s) : LInfinity := by
  intro d hd h0 clocks s lo
  obtain ⟨a, c, ha, catches⟩ := windows d hd h0 clocks lo
  obtain ⟨j, n, hj, _, reset⟩ := catches s
  exact ⟨j, n, Nat.le_trans ha hj, reset⟩

theorem lInfinity_of_dlMinusOne (h : DLMinusOne) : LInfinity := by
  apply lInfinity_of_windows
  intro d hd h0 clocks lo
  obtain ⟨a, e, ha, loss⟩ := unbounded_first_losses hd h0 clocks lo
  obtain ⟨b, hab⟩ := exists_next_white hd h0 clocks a
  obtain ⟨c, hbc⟩ := exists_next_white hd h0 clocks b
  exact ⟨a, c, ha, h d hd h0 clocks a e b c loss hab hbc⟩

/-- The kit's explicit settling-age witness for the physical every-k target. -/
theorem everyK_of_dlMinusOne (h : DLMinusOne) :
    EveryK (fun k => settlingBound (widthFor (cap_of_unbounded_resets
      (lInfinity_of_dlMinusOne h)) k)) :=
  Rule30EveryKInverse.conditional_every_k _

end Ruliology.CellularAutomata.Rule30RelaxedWindows
