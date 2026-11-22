module

public import Ruliology.CellularAutomata.Rule30GateTrapLadder

/-!
# The core mass form of the gate-trap ladder

`Rule30GateTrapLadder` reduces `CQ01Empty` to `MassDivergesLift W` (lift paths of width `W` with
no further condition) and to `Q01GapLiftCore W` (lift paths together with
`Rule30GateTrapLift.TwoCoreOK`). Counts of light seeds are made inside the lift language and the
three core words together, so the mass statement they bear on is the core one. This module adds it.

* `twoCoreOK_congr`: `Rule30GateTrapLift.TwoCoreOK g s` reads only the cells `g (s + i)`, `i < 28`.
* `AcceptLiftCore W y H`: `y` is accepted by one lift path of width `W` for `H` steps in the sense
  of `AcceptLift`, and the first cells of its windows satisfy `TwoCoreOK` at every step `s` with
  `2 s + 56 ≤ H`, that is at every step whose 28 cells lie inside the horizon.
* `MassDivergesLiftCore W` (**open**): for every `M` there is `H` such that no natural number of
  popcount at most `M` is accepted in this sense for `H` steps. It follows from
  `MassDivergesLift W` (`massDivergesLiftCore_of_massDivergesLift`), weakens as `W` grows
  (`MassDivergesLiftCore_mono`) and gives `Q01GapLiftCore W`
  (`Q01GapLiftCore_of_massDivergesLiftCore`), hence `CQ01Empty` for `W ≥ 16`
  (`CQ01Empty_of_massDivergesLiftCore`).

So `MassDivergesLift W → MassDivergesLiftCore W → Q01GapLiftCore W → CQ01Empty` for `16 ≤ W`.
Nothing here decides `MassDivergesLiftCore`, `CQ01Empty` or Problem 1.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30GateTrapLadderCore

open Rule30StripCertificates Rule30Ether Rule30PeriodTwoCoupled Rule30GateTrap Rule30ZeroBoundary
open Rule30ZeroBoundary.IntegerForm Rule30GateTrapLadder

/-- **`TwoCoreOK` reads 28 cells.** If `g` and `g'` agree on the 28 cells from `s` and from `s'`,
`TwoCoreOK g s` gives `TwoCoreOK g' s'`. -/
theorem twoCoreOK_congr {g g' : Nat → Bool} {s s' : Nat}
    (h : ∀ i, i < 28 → g (s + i) = g' (s' + i))
    (hc : Rule30GateTrapLift.TwoCoreOK g s) : Rule30GateTrapLift.TwoCoreOK g' s' := by
  have reads : ∀ w : List Bool, w.length ≤ 28 →
      Rule30GateTrapWords.Reads g' s' w → Rule30GateTrapWords.Reads g s w := by
    intro w hw hr i hi
    rw [h i (by omega)]
    exact hr i hi
  obtain ⟨⟨hgap, h33, h3553⟩, h3535353⟩ := hc
  refine ⟨⟨?_, fun hr => h33 (reads _ (by decide) hr), fun hr => h3553 (reads _ (by decide) hr)⟩,
    fun hr => h3535353 (reads _ (by decide) hr)⟩
  intro hs
  have e0 := h 0 (by omega)
  have e1 := h 1 (by omega)
  have e2 := h 2 (by omega)
  have e3 := h 3 (by omega)
  have e4 := h 4 (by omega)
  have e5 := h 5 (by omega)
  simp only [Nat.add_zero] at e0
  rw [← e0] at hs
  rcases hgap hs with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3, a4, a5⟩
  · left
    exact ⟨by rw [← e1]; exact a1, by rw [← e2]; exact a2, by rw [← e3]; exact a3⟩
  · right
    exact ⟨by rw [← e1]; exact a1, by rw [← e2]; exact a2, by rw [← e3]; exact a3,
      by rw [← e4]; exact a4, by rw [← e5]; exact a5⟩

/-- `y` is accepted by a lift path of width `W` for `H` steps (`AcceptLift`), and the first cells
of the windows of that path satisfy `TwoCoreOK` at every step whose 28 cells lie inside the
horizon. -/
def AcceptLiftCore (W y H : Nat) : Prop :=
  ∃ ws, LiftPath W ws ∧
    (∀ t, t < H →
      (iter F t y).testBit 0 = if t % 2 = 1 then true else !(ws (t / 2)).headD false) ∧
    ∀ s, 2 * s + 56 ≤ H → Rule30GateTrapLift.TwoCoreOK (fun k => (ws k).headD false) s

/-- **`MassDivergesLiftCore W`** (**open**): for every `M` there is `H` such that no natural
number of popcount at most `M` is accepted in the sense of `AcceptLiftCore W` for `H` steps. -/
def MassDivergesLiftCore (W : Nat) : Prop :=
  ∀ M : Nat, ∃ H : Nat, ∀ y : Nat,
    Rule30ZeroCoastBridge.popcount y ≤ M → ¬ AcceptLiftCore W y H

theorem AcceptLiftCore.acceptLift {W y H : Nat} (h : AcceptLiftCore W y H) : AcceptLift W y H := by
  obtain ⟨ws, hp, ht, _⟩ := h
  exact ⟨ws, hp, ht⟩

/-- **The core form is the weaker statement**: `MassDivergesLift W` gives `MassDivergesLiftCore W`. -/
theorem massDivergesLiftCore_of_massDivergesLift {W : Nat} (h : MassDivergesLift W) :
    MassDivergesLiftCore W := fun M => by
  obtain ⟨H, hH⟩ := h M
  exact ⟨H, fun y hy ha => hH y hy ha.acceptLift⟩

theorem AcceptLiftCore.take {W W' : Nat} (hW : 16 ≤ W) (hWW : W ≤ W') {y H : Nat}
    (h : AcceptLiftCore W' y H) : AcceptLiftCore W y H := by
  obtain ⟨ws, hp, ht, hc⟩ := h
  refine ⟨_, liftPath_take hW hWW hp, fun t htH => ?_, fun s hs => ?_⟩
  · rw [ht t htH]
    show _ = if t % 2 = 1 then true else !((ws (t / 2)).take W).headD false
    rw [headD_take _ _ (by omega)]
  · exact twoCoreOK_congr (fun i _ => (headD_take (ws (s + i)) W (by omega)).symm) (hc s hs)

/-- **The core mass ladder.** For `16 ≤ W ≤ W'`, `MassDivergesLiftCore W` gives
`MassDivergesLiftCore W'`. -/
theorem MassDivergesLiftCore_mono {W W' : Nat} (hW : 16 ≤ W) (hWW : W ≤ W')
    (h : MassDivergesLiftCore W) : MassDivergesLiftCore W' := fun M => by
  obtain ⟨H, hH⟩ := h M
  exact ⟨H, fun y hy ha => hH y hy (ha.take hW hWW)⟩

/-- **`MassDivergesLiftCore W` gives `Q01GapLiftCore W`.** A finite start read by a lift path
from step `s0` on and satisfying the core words there, run to the time `2 s0 + 1` and read as a
natural number, is accepted in the core sense for every `H`. -/
theorem Q01GapLiftCore_of_massDivergesLiftCore {W : Nat} (hM : MassDivergesLiftCore W) :
    Q01GapLiftCore W := by
  rintro L hf hX ⟨s0, ⟨ws, hp, hh⟩, hcore⟩
  obtain ⟨W0, hW0⟩ := Rule30GateTrapLift.finSupp_zrow hf (2 * s0 + 1)
  obtain ⟨H, hH⟩ := hM (Rule30ZeroCoastBridge.popcount (natOfRow (zrow L (2 * s0 + 1)) W0))
  apply hH _ (Nat.le_refl _)
  refine ⟨ws, hp, fun t _ => ?_, fun s _ => ?_⟩
  · have hrow : ∀ k, 1 ≤ k →
        rowOfNat (natOfRow (zrow L (2 * s0 + 1)) W0) k = zrow L (2 * s0 + 1) k :=
      rowOfNat_natOfRow hW0
    have hcol : (iter F t (natOfRow (zrow L (2 * s0 + 1)) W0)).testBit 0 =
        zrow L (2 * s0 + 1 + t) 1 := by
      rw [← zrow_rowOfNat_col1, zrow_congr hrow t 1, ← zrow_shift]
    rw [hcol]
    rcases Nat.mod_two_eq_zero_or_one t with h2 | h2
    · obtain ⟨k, rfl⟩ : ∃ k, t = 2 * k := ⟨t / 2, by omega⟩
      rw [ite_eq_right (by omega), show 2 * k / 2 = k by omega, hh k,
        show 2 * s0 + 1 + 2 * k = 2 * (s0 + k) + 1 by omega]
      simp
    · obtain ⟨k, rfl⟩ : ∃ k, t = 2 * k + 1 := ⟨t / 2, by omega⟩
      rw [ite_eq_left h2, show 2 * s0 + 1 + (2 * k + 1) = 2 * (s0 + k + 1) by omega]
      exact hX (s0 + k + 1)
  · exact twoCoreOK_congr (fun i _ => by simp only [hh (s + i), Nat.add_assoc])
      (hcore (s0 + s) (by omega))

/-- **`CQ01Empty` follows from `MassDivergesLiftCore W`** for every `W ≥ 16`. -/
theorem CQ01Empty_of_massDivergesLiftCore {W : Nat} (hW : 16 ≤ W) (hM : MassDivergesLiftCore W) :
    Rule30PeriodTwoSideways.CQ01Empty :=
  CQ01Empty_of_Q01GapLiftCore hW (Q01GapLiftCore_of_massDivergesLiftCore hM)

/-- **The core mass ladder in one statement.** For `16 ≤ W ≤ W'`: `MassDivergesLift W` gives
`MassDivergesLiftCore W`, which gives `MassDivergesLiftCore W'` and `Q01GapLiftCore W`, and
`MassDivergesLiftCore W'` gives `CQ01Empty`. -/
theorem coreLadder {W W' : Nat} (hW : 16 ≤ W) (hWW : W ≤ W') :
    (MassDivergesLift W → MassDivergesLiftCore W) ∧
      (MassDivergesLiftCore W → MassDivergesLiftCore W') ∧
      (MassDivergesLiftCore W → Q01GapLiftCore W) ∧
      (MassDivergesLiftCore W' → Rule30PeriodTwoSideways.CQ01Empty) :=
  ⟨massDivergesLiftCore_of_massDivergesLift, MassDivergesLiftCore_mono hW hWW,
    Q01GapLiftCore_of_massDivergesLiftCore, CQ01Empty_of_massDivergesLiftCore (Nat.le_trans hW hWW)⟩

end Ruliology.CellularAutomata.Rule30GateTrapLadderCore
