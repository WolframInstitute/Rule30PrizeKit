module

public import Ruliology.CellularAutomata.Rule30EtherSingleCellAux
public import Ruliology.CellularAutomata.Rule30EtherSingleCellCases0
public import Ruliology.CellularAutomata.Rule30EtherSingleCellCases1
public import Ruliology.CellularAutomata.Rule30EtherSingleCellCases2
public import Ruliology.CellularAutomata.Rule30EtherSingleCellCases3
public import Ruliology.CellularAutomata.Rule30EtherSingleCellCases4
public import Ruliology.CellularAutomata.Rule30EtherSingleCellCases5
public import Ruliology.CellularAutomata.Rule30EtherSingleCellCases6
public import Ruliology.CellularAutomata.Rule30EtherSingleCellCases7

@[expose] public section

/-!
# Rule 30: the single-cell case of period-4 absorption for the word `0001`

For every position `p` and phase `φ`, the right half with one black cell at `p` and all other
cells white, driven by `0001^∞` at phase `φ`, eventually enters the ether-and-wall family for the
alignment `(5, 0)` or `(6, 0)`.  This is the single-cell restriction of
`Rule30Ether.Absorption w0001 A0001`; it does not prove the full absorption conjecture.

The proof has two parts.  For `p ≥ 31` the cell lies outside the backward light cone of the
13-cell wall window at the all-white entry time `14 - φ`, so the orbit agrees there with the
all-white orbit, which is checked directly.  For the finitely many `p ≤ 30` the entry is checked
by a kernel computation of the row recurrence (`famBAt_sound` and the `case_*` lemmas).
-/

namespace Ruliology.CellularAutomata
namespace Rule30Ether

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The finite check: for `1 ≤ p ≤ 30` and `φ < 4`, the single-cell right half reaches the
family.  Each branch is one of the kernel-checked `case_p_phi` lemmas. -/
theorem small_case {p φ : Nat} (hp1 : 1 ≤ p) (hp30 : p ≤ 30) (hφ : φ < 4) :
    ∃ a ∈ A0001, ∃ t1,
      InFamily (drv (fun n => wordAt w0001 (n + φ)) (delta p)) a.1 (a.2 + φ) t1 := by
  have hp : p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 ∨ p = 8 ∨ p = 9 ∨ p = 10 ∨ p = 11 ∨ p = 12 ∨ p = 13 ∨ p = 14 ∨ p = 15 ∨ p = 16 ∨ p = 17 ∨ p = 18 ∨ p = 19 ∨ p = 20 ∨ p = 21 ∨ p = 22 ∨ p = 23 ∨ p = 24 ∨ p = 25 ∨ p = 26 ∨ p = 27 ∨ p = 28 ∨ p = 29 ∨ p = 30 := by omega
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hφc : φ = 0 ∨ φ = 1 ∨ φ = 2 ∨ φ = 3 := by omega
    rcases hφc with rfl | rfl | rfl | rfl
    · exact ⟨(6, 0), by decide, 10, case_1_0⟩
    · exact ⟨(6, 0), by decide, 10, case_1_1⟩
    · exact ⟨(6, 0), by decide, 10, case_1_2⟩
    · exact ⟨(6, 0), by decide, 79, case_1_3⟩
  · have hφc : φ = 0 ∨ φ = 1 ∨ φ = 2 ∨ φ = 3 := by omega
    rcases hφc with rfl | rfl | rfl | rfl
    · exact ⟨(6, 0), by decide, 78, case_2_0⟩
    · exact ⟨(6, 0), by decide, 48, case_2_1⟩
    · exact ⟨(5, 0), by decide, 10, case_2_2⟩
    · exact ⟨(6, 0), by decide, 79, case_2_3⟩
  · have hφc : φ = 0 ∨ φ = 1 ∨ φ = 2 ∨ φ = 3 := by omega
    rcases hφc with rfl | rfl | rfl | rfl
    · exact ⟨(6, 0), by decide, 8, case_3_0⟩
    · exact ⟨(6, 0), by decide, 142, case_3_1⟩
    · exact ⟨(6, 0), by decide, 108, case_3_2⟩
    · exact ⟨(6, 0), by decide, 95, case_3_3⟩
  · have hφc : φ = 0 ∨ φ = 1 ∨ φ = 2 ∨ φ = 3 := by omega
    rcases hφc with rfl | rfl | rfl | rfl
    · exact ⟨(5, 0), by decide, 8, case_4_0⟩
    · exact ⟨(6, 0), by decide, 113, case_4_1⟩
    · exact ⟨(6, 0), by decide, 65, case_4_2⟩
    · exact ⟨(6, 0), by decide, 25, case_4_3⟩
  · have hφc : φ = 0 ∨ φ = 1 ∨ φ = 2 ∨ φ = 3 := by omega
    rcases hφc with rfl | rfl | rfl | rfl
    · exact ⟨(6, 0), by decide, 152, case_5_0⟩
    · exact ⟨(6, 0), by decide, 117, case_5_1⟩
    · exact ⟨(6, 0), by decide, 193, case_5_2⟩
    · exact ⟨(6, 0), by decide, 63, case_5_3⟩
  · have hφc : φ = 0 ∨ φ = 1 ∨ φ = 2 ∨ φ = 3 := by omega
    rcases hφc with rfl | rfl | rfl | rfl
    · exact ⟨(6, 0), by decide, 74, case_6_0⟩
    · exact ⟨(6, 0), by decide, 97, case_6_1⟩
    · exact ⟨(6, 0), by decide, 40, case_6_2⟩
    · exact ⟨(6, 0), by decide, 43, case_6_3⟩
  · have hφc : φ = 0 ∨ φ = 1 ∨ φ = 2 ∨ φ = 3 := by omega
    rcases hφc with rfl | rfl | rfl | rfl
    · exact ⟨(6, 0), by decide, 13, case_7_0⟩
    · exact ⟨(6, 0), by decide, 88, case_7_1⟩
    · exact ⟨(6, 0), by decide, 138, case_7_2⟩
    · exact ⟨(6, 0), by decide, 120, case_7_3⟩
  · have hφc : φ = 0 ∨ φ = 1 ∨ φ = 2 ∨ φ = 3 := by omega
    rcases hφc with rfl | rfl | rfl | rfl
    · exact ⟨(6, 0), by decide, 135, case_8_0⟩
    · exact ⟨(6, 0), by decide, 42, case_8_1⟩
    · exact ⟨(6, 0), by decide, 92, case_8_2⟩
    · exact ⟨(6, 0), by decide, 9, case_8_3⟩
  · have hφc : φ = 0 ∨ φ = 1 ∨ φ = 2 ∨ φ = 3 := by omega
    rcases hφc with rfl | rfl | rfl | rfl
    · exact ⟨(6, 0), by decide, 213, case_9_0⟩
    · exact ⟨(6, 0), by decide, 181, case_9_1⟩
    · exact ⟨(6, 0), by decide, 13, case_9_2⟩
    · exact ⟨(6, 0), by decide, 15, case_9_3⟩
  · have hφc : φ = 0 ∨ φ = 1 ∨ φ = 2 ∨ φ = 3 := by omega
    rcases hφc with rfl | rfl | rfl | rfl
    · exact ⟨(6, 0), by decide, 94, case_10_0⟩
    · exact ⟨(6, 0), by decide, 241, case_10_1⟩
    · exact ⟨(6, 0), by decide, 112, case_10_2⟩
    · exact ⟨(6, 0), by decide, 183, case_10_3⟩
  · have hφc : φ = 0 ∨ φ = 1 ∨ φ = 2 ∨ φ = 3 := by omega
    rcases hφc with rfl | rfl | rfl | rfl
    · exact ⟨(6, 0), by decide, 114, case_11_0⟩
    · exact ⟨(6, 0), by decide, 50, case_11_1⟩
    · exact ⟨(6, 0), by decide, 89, case_11_2⟩
    · exact ⟨(6, 0), by decide, 77, case_11_3⟩
  · have hφc : φ = 0 ∨ φ = 1 ∨ φ = 2 ∨ φ = 3 := by omega
    rcases hφc with rfl | rfl | rfl | rfl
    · exact ⟨(6, 0), by decide, 72, case_12_0⟩
    · exact ⟨(6, 0), by decide, 209, case_12_1⟩
    · exact ⟨(6, 0), by decide, 47, case_12_2⟩
    · exact ⟨(6, 0), by decide, 338, case_12_3⟩
  · have hφc : φ = 0 ∨ φ = 1 ∨ φ = 2 ∨ φ = 3 := by omega
    rcases hφc with rfl | rfl | rfl | rfl
    · exact ⟨(6, 0), by decide, 325, case_13_0⟩
    · exact ⟨(6, 0), by decide, 96, case_13_1⟩
    · exact ⟨(6, 0), by decide, 21, case_13_2⟩
    · exact ⟨(6, 0), by decide, 39, case_13_3⟩
  · have hφc : φ = 0 ∨ φ = 1 ∨ φ = 2 ∨ φ = 3 := by omega
    rcases hφc with rfl | rfl | rfl | rfl
    · exact ⟨(6, 0), by decide, 78, case_14_0⟩
    · exact ⟨(6, 0), by decide, 12, case_14_1⟩
    · exact ⟨(6, 0), by decide, 47, case_14_2⟩
    · exact ⟨(6, 0), by decide, 160, case_14_3⟩
  · have hφc : φ = 0 ∨ φ = 1 ∨ φ = 2 ∨ φ = 3 := by omega
    rcases hφc with rfl | rfl | rfl | rfl
    · exact ⟨(6, 0), by decide, 24, case_15_0⟩
    · exact ⟨(6, 0), by decide, 91, case_15_1⟩
    · exact ⟨(6, 0), by decide, 134, case_15_2⟩
    · exact ⟨(6, 0), by decide, 54, case_15_3⟩
  · have hφc : φ = 0 ∨ φ = 1 ∨ φ = 2 ∨ φ = 3 := by omega
    rcases hφc with rfl | rfl | rfl | rfl
    · exact ⟨(6, 0), by decide, 107, case_16_0⟩
    · exact ⟨(6, 0), by decide, 28, case_16_1⟩
    · exact ⟨(6, 0), by decide, 117, case_16_2⟩
    · exact ⟨(6, 0), by decide, 12, case_16_3⟩
  · have hφc : φ = 0 ∨ φ = 1 ∨ φ = 2 ∨ φ = 3 := by omega
    rcases hφc with rfl | rfl | rfl | rfl
    · exact ⟨(6, 0), by decide, 130, case_17_0⟩
    · exact ⟨(6, 0), by decide, 107, case_17_1⟩
    · exact ⟨(6, 0), by decide, 7, case_17_2⟩
    · exact ⟨(6, 0), by decide, 196, case_17_3⟩
  · have hφc : φ = 0 ∨ φ = 1 ∨ φ = 2 ∨ φ = 3 := by omega
    rcases hφc with rfl | rfl | rfl | rfl
    · exact ⟨(6, 0), by decide, 140, case_18_0⟩
    · exact ⟨(6, 0), by decide, 21, case_18_1⟩
    · exact ⟨(6, 0), by decide, 53, case_18_2⟩
    · exact ⟨(6, 0), by decide, 127, case_18_3⟩
  · have hφc : φ = 0 ∨ φ = 1 ∨ φ = 2 ∨ φ = 3 := by omega
    rcases hφc with rfl | rfl | rfl | rfl
    · exact ⟨(6, 0), by decide, 9, case_19_0⟩
    · exact ⟨(6, 0), by decide, 76, case_19_1⟩
    · exact ⟨(6, 0), by decide, 62, case_19_2⟩
    · exact ⟨(6, 0), by decide, 52, case_19_3⟩
  · have hφc : φ = 0 ∨ φ = 1 ∨ φ = 2 ∨ φ = 3 := by omega
    rcases hφc with rfl | rfl | rfl | rfl
    · exact ⟨(6, 0), by decide, 126, case_20_0⟩
    · exact ⟨(6, 0), by decide, 259, case_20_1⟩
    · exact ⟨(6, 0), by decide, 114, case_20_2⟩
    · exact ⟨(6, 0), by decide, 10, case_20_3⟩
  · have hφc : φ = 0 ∨ φ = 1 ∨ φ = 2 ∨ φ = 3 := by omega
    rcases hφc with rfl | rfl | rfl | rfl
    · exact ⟨(6, 0), by decide, 58, case_21_0⟩
    · exact ⟨(6, 0), by decide, 57, case_21_1⟩
    · exact ⟨(6, 0), by decide, 12, case_21_2⟩
    · exact ⟨(6, 0), by decide, 123, case_21_3⟩
  · have hφc : φ = 0 ∨ φ = 1 ∨ φ = 2 ∨ φ = 3 := by omega
    rcases hφc with rfl | rfl | rfl | rfl
    · exact ⟨(6, 0), by decide, 124, case_22_0⟩
    · exact ⟨(6, 0), by decide, 12, case_22_1⟩
    · exact ⟨(6, 0), by decide, 21, case_22_2⟩
    · exact ⟨(6, 0), by decide, 63, case_22_3⟩
  · have hφc : φ = 0 ∨ φ = 1 ∨ φ = 2 ∨ φ = 3 := by omega
    rcases hφc with rfl | rfl | rfl | rfl
    · exact ⟨(6, 0), by decide, 14, case_23_0⟩
    · exact ⟨(6, 0), by decide, 62, case_23_1⟩
    · exact ⟨(6, 0), by decide, 30, case_23_2⟩
    · exact ⟨(6, 0), by decide, 27, case_23_3⟩
  · have hφc : φ = 0 ∨ φ = 1 ∨ φ = 2 ∨ φ = 3 := by omega
    rcases hφc with rfl | rfl | rfl | rfl
    · exact ⟨(6, 0), by decide, 155, case_24_0⟩
    · exact ⟨(6, 0), by decide, 124, case_24_1⟩
    · exact ⟨(6, 0), by decide, 30, case_24_2⟩
    · exact ⟨(6, 0), by decide, 11, case_24_3⟩
  · have hφc : φ = 0 ∨ φ = 1 ∨ φ = 2 ∨ φ = 3 := by omega
    rcases hφc with rfl | rfl | rfl | rfl
    · exact ⟨(6, 0), by decide, 74, case_25_0⟩
    · exact ⟨(6, 0), by decide, 31, case_25_1⟩
    · exact ⟨(6, 0), by decide, 12, case_25_2⟩
    · exact ⟨(6, 0), by decide, 19, case_25_3⟩
  · have hφc : φ = 0 ∨ φ = 1 ∨ φ = 2 ∨ φ = 3 := by omega
    rcases hφc with rfl | rfl | rfl | rfl
    · exact ⟨(6, 0), by decide, 32, case_26_0⟩
    · exact ⟨(6, 0), by decide, 13, case_26_1⟩
    · exact ⟨(6, 0), by decide, 13, case_26_2⟩
    · exact ⟨(6, 0), by decide, 11, case_26_3⟩
  · have hφc : φ = 0 ∨ φ = 1 ∨ φ = 2 ∨ φ = 3 := by omega
    rcases hφc with rfl | rfl | rfl | rfl
    · exact ⟨(6, 0), by decide, 14, case_27_0⟩
    · exact ⟨(6, 0), by decide, 21, case_27_1⟩
    · exact ⟨(6, 0), by decide, 12, case_27_2⟩
    · exact ⟨(6, 0), by decide, 11, case_27_3⟩
  · have hφc : φ = 0 ∨ φ = 1 ∨ φ = 2 ∨ φ = 3 := by omega
    rcases hφc with rfl | rfl | rfl | rfl
    · exact ⟨(6, 0), by decide, 15, case_28_0⟩
    · exact ⟨(6, 0), by decide, 13, case_28_1⟩
    · exact ⟨(6, 0), by decide, 12, case_28_2⟩
    · exact ⟨(6, 0), by decide, 11, case_28_3⟩
  · have hφc : φ = 0 ∨ φ = 1 ∨ φ = 2 ∨ φ = 3 := by omega
    rcases hφc with rfl | rfl | rfl | rfl
    · exact ⟨(6, 0), by decide, 14, case_29_0⟩
    · exact ⟨(6, 0), by decide, 13, case_29_1⟩
    · exact ⟨(6, 0), by decide, 12, case_29_2⟩
    · exact ⟨(6, 0), by decide, 11, case_29_3⟩
  · have hφc : φ = 0 ∨ φ = 1 ∨ φ = 2 ∨ φ = 3 := by omega
    rcases hφc with rfl | rfl | rfl | rfl
    · exact ⟨(6, 0), by decide, 14, case_30_0⟩
    · exact ⟨(6, 0), by decide, 13, case_30_1⟩
    · exact ⟨(6, 0), by decide, 12, case_30_2⟩
    · exact ⟨(6, 0), by decide, 11, case_30_3⟩

/-- The theorem for `φ < 4`.  `p = 0` is the all-white orbit (column `0` is overwritten by the
driver), `1 ≤ p ≤ 30` is the finite check, and `p ≥ 31` is the light-cone reduction. -/
theorem singleCell_mod (x : Nat → Bool) (p φ : Nat) (hx : x p = true)
    (hx' : ∀ q, q ≠ p → x q = false) (hφ : φ < 4) :
    ∃ a ∈ A0001, ∃ t1,
      InFamily (drv (fun n => wordAt w0001 (n + φ)) x) a.1 (a.2 + φ) t1 := by
  rcases Nat.eq_zero_or_pos p with hp0 | hp
  · subst p
    have hxeq : x = delta 0 := delta_eq hx hx'
    rw [hxeq]
    obtain ⟨hEw, hWw⟩ := allWhite_data φ hφ
    refine ⟨(6, 0), by decide, 14 - φ, 3, by decide, ?_, ?_⟩
    · intro q hq1 hq3
      simp only [Prod.fst, Prod.snd]
      rw [show 14 - φ + (0 + φ) = 14 by omega]
      exact hEw q hq1 hq3
    · simp only [Prod.fst, Prod.snd, Nat.zero_add]
      rw [show 14 - φ + φ = 14 by omega]
      simpa using hWw
  · rcases Nat.lt_or_ge p 31 with hp31 | hp31
    · have hp30 : p ≤ 30 := by omega
      have hxeq : x = delta p := delta_eq hx hx'
      rw [hxeq]
      exact small_case hp hp30 hφ
    · have hIF := large_case (x := x) (p := p) (φ := φ) hp31 hx' hφ
      refine ⟨(6, 0), by decide, 14 - φ, ?_⟩
      simpa using hIF

/-- **Single-cell absorption for `w = 0001`.**  The right half with a single black cell at `p` and
all other cells white, driven by `0001^∞` at phase `φ`, eventually enters the ether-and-wall
family for the alignment `(5, 0)` or `(6, 0)`.  This is the single-cell restriction of
`Rule30Ether.Absorption w0001 A0001`, not the full conjecture. -/
theorem singleCell_absorption (x : Nat → Bool) (p φ : Nat) (hx : x p = true)
    (hx' : ∀ q, q ≠ p → x q = false) :
    ∃ a ∈ A0001, ∃ t1,
      InFamily (drv (fun t => wordAt w0001 (t + φ)) x) a.1 (a.2 + φ) t1 := by
  have hφ0 : φ % 4 < 4 := Nat.mod_lt _ (by decide)
  obtain ⟨a, ha, t1, hIF⟩ := singleCell_mod x p (φ % 4) hx hx' hφ0
  have hdrv : drv (fun t => wordAt w0001 (t + φ)) x =
      drv (fun t => wordAt w0001 (t + φ % 4)) x := by
    apply drv_phase_congr
    intro t
    unfold wordAt
    congr 1
    simp only [Nat.add_mod, Nat.mod_mod]
  have ha0 : a.2 = 0 := by
    have hmem := ha
    simp [A0001] at hmem
    rcases hmem with rfl | rfl <;> rfl
  have hss : (a.2 + φ % 4) % 4 = (a.2 + φ) % 4 := by
    rw [ha0]
    simp
  refine ⟨a, ha, t1, ?_⟩
  rw [hdrv]
  exact (InFamily_phase_congr (F := drv (fun t => wordAt w0001 (t + φ % 4)) x)
    (j0 := a.1) (s := a.2 + φ % 4) (s' := a.2 + φ) hss).1 hIF

end Rule30Ether
end Ruliology.CellularAutomata
