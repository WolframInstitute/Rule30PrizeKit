module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

/-!
# Stripe prefixes with four and five tail cells: front-window cycles

Data for `Rule30ZeroBoundaryStripeFour`:
- Four-cell tail cycles (window `32`, post-arrival horizon `31`): `cyc4_8`, `cyc4_9`, `cyc4_10`,
  `cyc4_11`, `cyc4_12`, `cyc4_14`, `cyc4_15`.
- Five-cell tail cycles (window `32`, post-arrival horizon `31`): `cyc5_17`, `cyc5_19`, `cyc5_21`,
  `cyc5_23`, `cyc5_25`, `cyc5_27`, `cyc5_29`, `cyc5_31`.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront.StripeCycles3

open Rule30ZeroBoundaryStripeFront
open Rule30ZeroBoundary Rule30ZeroBoundarySmall

theorem seg4_8_0 : seg 32 31 0 1073741832 1 16384 0 8 1 = true := by decide +kernel
theorem seg4_8_1 : seg 32 31 0 8 1 16384 16384 1073741832 1 = true := by decide +kernel
theorem cyc4_8 : Cycle 32 31 8 1 32768 :=
  ⟨by decide, by decide, (path_append (seg_sound 32 31 0 1073741832 1 16384 0 8 1 seg4_8_0) (seg_sound 32 31 0 8 1 16384 16384 1073741832 1 seg4_8_1))⟩

theorem seg4_9_0 : seg 32 31 1 9 0 4096 0 9 0 = true := by decide +kernel
theorem cyc4_9 : Cycle 32 31 9 0 4096 :=
  ⟨by decide, by decide, (seg_sound 32 31 1 9 0 4096 0 9 0 seg4_9_0)⟩

theorem seg4_10_0 : seg 32 31 0 10 1 8192 0 10 1 = true := by decide +kernel
theorem cyc4_10 : Cycle 32 31 10 1 8192 :=
  ⟨by decide, by decide, (seg_sound 32 31 0 10 1 8192 0 10 1 seg4_10_0)⟩

theorem seg4_11_0 : seg 32 31 1 1073741835 0 16384 0 11 0 = true := by decide +kernel
theorem seg4_11_1 : seg 32 31 1 2147483659 0 16384 16384 1073741835 0 = true := by decide +kernel
theorem seg4_11_2 : seg 32 31 1 3221225483 0 16384 32768 2147483659 0 = true := by decide +kernel
theorem seg4_11_3 : seg 32 31 1 11 0 16384 49152 3221225483 0 = true := by decide +kernel
theorem cyc4_11 : Cycle 32 31 11 0 65536 :=
  ⟨by decide, by decide, (path_append (path_append (path_append (seg_sound 32 31 1 1073741835 0 16384 0 11 0 seg4_11_0) (seg_sound 32 31 1 2147483659 0 16384 16384 1073741835 0 seg4_11_1)) (seg_sound 32 31 1 3221225483 0 16384 32768 2147483659 0 seg4_11_2)) (seg_sound 32 31 1 11 0 16384 49152 3221225483 0 seg4_11_3))⟩

theorem seg4_12_0 : seg 32 31 0 12 1 16384 0 12 1 = true := by decide +kernel
theorem cyc4_12 : Cycle 32 31 12 1 16384 :=
  ⟨by decide, by decide, (seg_sound 32 31 0 12 1 16384 0 12 1 seg4_12_0)⟩

theorem seg4_14_0 : seg 32 31 0 3758096398 1 16384 0 14 1 = true := by decide +kernel
theorem seg4_14_1 : seg 32 31 0 3221225486 1 16384 16384 3758096398 1 = true := by decide +kernel
theorem seg4_14_2 : seg 32 31 0 2684354574 1 16384 32768 3221225486 1 = true := by decide +kernel
theorem seg4_14_3 : seg 32 31 0 14 1 16384 49152 2684354574 1 = true := by decide +kernel
theorem cyc4_14 : Cycle 32 31 14 1 65536 :=
  ⟨by decide, by decide, (path_append (path_append (path_append (seg_sound 32 31 0 3758096398 1 16384 0 14 1 seg4_14_0) (seg_sound 32 31 0 3221225486 1 16384 16384 3758096398 1 seg4_14_1)) (seg_sound 32 31 0 2684354574 1 16384 32768 3221225486 1 seg4_14_2)) (seg_sound 32 31 0 14 1 16384 49152 2684354574 1 seg4_14_3))⟩

theorem seg4_15_0 : seg 32 31 1 15 0 16384 0 15 0 = true := by decide +kernel
theorem cyc4_15 : Cycle 32 31 15 0 16384 :=
  ⟨by decide, by decide, (seg_sound 32 31 1 15 0 16384 0 15 0 seg4_15_0)⟩

theorem seg5_17_0 : seg 32 31 1 17 0 16384 0 17 0 = true := by decide +kernel
theorem cyc5_17 : Cycle 32 31 17 0 16384 :=
  ⟨by decide, by decide, (seg_sound 32 31 1 17 0 16384 0 17 0 seg5_17_0)⟩

theorem seg5_19_0 : seg 32 31 1 3825205267 0 16384 0 19 0 = true := by decide +kernel
theorem seg5_19_1 : seg 32 31 1 2415919123 0 16384 16384 3825205267 0 = true := by decide +kernel
theorem seg5_19_2 : seg 32 31 1 1946157075 0 16384 32768 2415919123 0 = true := by decide +kernel
theorem seg5_19_3 : seg 32 31 1 19 0 16384 49152 1946157075 0 = true := by decide +kernel
theorem cyc5_19 : Cycle 32 31 19 0 65536 :=
  ⟨by decide, by decide, (path_append (path_append (path_append (seg_sound 32 31 1 3825205267 0 16384 0 19 0 seg5_19_0) (seg_sound 32 31 1 2415919123 0 16384 16384 3825205267 0 seg5_19_1)) (seg_sound 32 31 1 1946157075 0 16384 32768 2415919123 0 seg5_19_2)) (seg_sound 32 31 1 19 0 16384 49152 1946157075 0 seg5_19_3))⟩

theorem seg5_21_0 : seg 32 31 1 2147483669 0 16384 0 21 0 = true := by decide +kernel
theorem seg5_21_1 : seg 32 31 1 21 0 16384 16384 2147483669 0 = true := by decide +kernel
theorem cyc5_21 : Cycle 32 31 21 0 32768 :=
  ⟨by decide, by decide, (path_append (seg_sound 32 31 1 2147483669 0 16384 0 21 0 seg5_21_0) (seg_sound 32 31 1 21 0 16384 16384 2147483669 0 seg5_21_1))⟩

theorem seg5_23_0 : seg 32 31 1 23 0 16384 0 23 0 = true := by decide +kernel
theorem cyc5_23 : Cycle 32 31 23 0 16384 :=
  ⟨by decide, by decide, (seg_sound 32 31 1 23 0 16384 0 23 0 seg5_23_0)⟩

theorem seg5_25_0 : seg 32 31 1 25 0 16384 0 25 0 = true := by decide +kernel
theorem cyc5_25 : Cycle 32 31 25 0 16384 :=
  ⟨by decide, by decide, (seg_sound 32 31 1 25 0 16384 0 25 0 seg5_25_0)⟩

theorem seg5_27_0 : seg 32 31 1 27 0 4096 0 27 0 = true := by decide +kernel
theorem cyc5_27 : Cycle 32 31 27 0 4096 :=
  ⟨by decide, by decide, (seg_sound 32 31 1 27 0 4096 0 27 0 seg5_27_0)⟩

theorem seg5_29_0 : seg 32 31 1 3758096413 0 16384 0 29 0 = true := by decide +kernel
theorem seg5_29_1 : seg 32 31 1 3221225501 0 16384 16384 3758096413 0 = true := by decide +kernel
theorem seg5_29_2 : seg 32 31 1 2684354589 0 16384 32768 3221225501 0 = true := by decide +kernel
theorem seg5_29_3 : seg 32 31 1 29 0 16384 49152 2684354589 0 = true := by decide +kernel
theorem cyc5_29 : Cycle 32 31 29 0 65536 :=
  ⟨by decide, by decide, (path_append (path_append (path_append (seg_sound 32 31 1 3758096413 0 16384 0 29 0 seg5_29_0) (seg_sound 32 31 1 3221225501 0 16384 16384 3758096413 0 seg5_29_1)) (seg_sound 32 31 1 2684354589 0 16384 32768 3221225501 0 seg5_29_2)) (seg_sound 32 31 1 29 0 16384 49152 2684354589 0 seg5_29_3))⟩

theorem seg5_31_0 : seg 32 31 1 1207959583 0 16384 0 31 0 = true := by decide +kernel
theorem seg5_31_1 : seg 32 31 1 1073741855 0 16384 16384 1207959583 0 = true := by decide +kernel
theorem seg5_31_2 : seg 32 31 1 134217759 0 16384 32768 1073741855 0 = true := by decide +kernel
theorem seg5_31_3 : seg 32 31 1 31 0 16384 49152 134217759 0 = true := by decide +kernel
theorem cyc5_31 : Cycle 32 31 31 0 65536 :=
  ⟨by decide, by decide, (path_append (path_append (path_append (seg_sound 32 31 1 1207959583 0 16384 0 31 0 seg5_31_0) (seg_sound 32 31 1 1073741855 0 16384 16384 1207959583 0 seg5_31_1)) (seg_sound 32 31 1 134217759 0 16384 32768 1073741855 0 seg5_31_2)) (seg_sound 32 31 1 31 0 16384 49152 134217759 0 seg5_31_3))⟩

end Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront.StripeCycles3
