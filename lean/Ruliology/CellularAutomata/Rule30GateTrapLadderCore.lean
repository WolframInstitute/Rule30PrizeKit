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

/-! ## Horizon monotonicity, shift invariance, mod-`2^H` locality, and bounded-seed equivalence for `MassDivergesLiftCore` -/

/-- **Zero-horizon core acceptance (`AcceptLiftCore_zero`):** every seed `y` satisfies `AcceptLiftCore W y 0` for `W ≥ 16`. -/
theorem AcceptLiftCore_zero {W y : Nat} (hW : 16 ≤ W) : AcceptLiftCore W y 0 := by
  refine ⟨fun k => winW Rule30PeriodTwoSideways.empty W (293 + 2 * k),
    winW_liftPath Rule30PeriodTwoSideways.empty hW (by decide) entry_empty,
    fun t ht => by omega, fun s hs => by omega⟩

/-- **Core horizon monotonicity (`AcceptLiftCore_mono_horizon`):** `AcceptLiftCore W y H2` implies
`AcceptLiftCore W y H1` whenever `H1 ≤ H2`. -/
theorem AcceptLiftCore_mono_horizon {W y H1 H2 : Nat} (hle : H1 ≤ H2)
    (h : AcceptLiftCore W y H2) : AcceptLiftCore W y H1 := by
  obtain ⟨ws, hp, ht, hc⟩ := h
  exact ⟨ws, hp, fun t ht1 => ht t (by omega), fun s hs1 => hc s (by omega)⟩

/-- **Even-step shift invariance (`AcceptLiftCore_shift_even`):** advancing `y` by `2 * d` steps
maps `AcceptLiftCore W y H` to `AcceptLiftCore W (iter F (2 * d) y) (H - 2 * d)`. -/
theorem AcceptLiftCore_shift_even {W y H d : Nat} (hW : 16 ≤ W)
    (h : AcceptLiftCore W y H) : AcceptLiftCore W (iter F (2 * d) y) (H - 2 * d) := by
  obtain ⟨ws, hp, ht, hc⟩ := h
  refine ⟨fun k => ws (d + k), LiftPath_shift hW hp d, fun t htH => ?_, fun s hs => ?_⟩
  · have hlt : 2 * d + t < H := by omega
    have hrow := ht (2 * d + t) hlt
    rw [← Rule30ZeroCoastBridge.iter_F_add, hrow]
    by_cases hodd : (2 * d + t) % 2 = 1
    · have htodd : t % 2 = 1 := by omega
      simp [hodd, htodd]
    · have hteven : t % 2 = 0 := by omega
      simp only [hodd, ↓reduceIte, hteven]
      have hdiv : (2 * d + t) / 2 = d + t / 2 := by omega
      rw [hdiv]
      rfl
  · exact twoCoreOK_congr (fun i _ => by simp only [Nat.add_assoc]) (hc (d + s) (by omega))

/-- **Finite-horizon mod-`2^H` locality (`AcceptLiftCore_mod_pow2`):** `AcceptLiftCore W y H`
depends only on the low `H` bits `y % 2 ^ H`. -/
theorem AcceptLiftCore_mod_pow2 {W y H : Nat} :
    AcceptLiftCore W (y % 2 ^ H) H ↔ AcceptLiftCore W y H := by
  have hbit (x : Nat) : x.testBit 0 = decide (x % 2 ^ 1 = 1) := by
    rw [Nat.testBit_zero, Nat.pow_one]
  constructor
  · rintro ⟨ws, hp, ht, hc⟩
    refine ⟨ws, hp, fun t htH => ?_, hc⟩
    have hm := ht t htH
    have hmod := Rule30ZeroCoastBridge.iter_F_mod_pow2 t y 1
    have hmod2 := Rule30ZeroCoastBridge.iter_F_mod_pow2 t (y % 2 ^ H) 1
    have hsub : (y % 2 ^ H) % 2 ^ (1 + t) = y % 2 ^ (1 + t) :=
      Nat.mod_mod_of_dvd y (Nat.pow_dvd_pow 2 (by omega))
    rw [hbit, hmod, ← hsub, ← hmod2, ← hbit, hm]
  · rintro ⟨ws, hp, ht, hc⟩
    refine ⟨ws, hp, fun t htH => ?_, hc⟩
    have hm := ht t htH
    have hmod := Rule30ZeroCoastBridge.iter_F_mod_pow2 t y 1
    have hmod2 := Rule30ZeroCoastBridge.iter_F_mod_pow2 t (y % 2 ^ H) 1
    have hsub : (y % 2 ^ H) % 2 ^ (1 + t) = y % 2 ^ (1 + t) :=
      Nat.mod_mod_of_dvd y (Nat.pow_dvd_pow 2 (by omega))
    rw [hbit, hmod2, hsub, ← hmod, ← hbit, hm]

/-- **Bounded-seed reduction for open `MassDivergesLiftCore W` (`MassDivergesLiftCore_iff_bounded_seed`):**
quantifying over all `y : Nat` in `MassDivergesLiftCore W` is equivalent to quantifying over the
finite box `y < 2 ^ H`. -/
theorem MassDivergesLiftCore_iff_bounded_seed {W : Nat} :
    MassDivergesLiftCore W ↔
      ∀ M : Nat, ∃ H : Nat, ∀ y : Nat, y < 2 ^ H →
        Rule30ZeroCoastBridge.popcount y ≤ M → ¬ AcceptLiftCore W y H := by
  constructor
  · intro hM M
    obtain ⟨H, hH⟩ := hM M
    exact ⟨H, fun y _ hy ha => hH y hy ha⟩
  · intro hb M
    obtain ⟨H, hH⟩ := hb M
    refine ⟨H, fun y hy ha => ?_⟩
    have hlt : y % 2 ^ H < 2 ^ H := Nat.mod_lt y (Nat.pow_pos (by decide : 0 < 2))
    have hpc : Rule30ZeroCoastBridge.popcount (y % 2 ^ H) ≤ M :=
      Nat.le_trans (Rule30ZeroCoastBridge.popcount_mod_pow2_le y H) hy
    exact hH (y % 2 ^ H) hlt hpc (AcceptLiftCore_mod_pow2.mpr ha)

end Ruliology.CellularAutomata.Rule30GateTrapLadderCore
