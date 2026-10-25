module

public import Ruliology.CellularAutomata.Rule30EtherSingleCellAux

@[expose] public section

/-!
# Case data for single-cell period-4 absorption for `0001`

The 120 kernel-checked cases `(p, φ)` for positions `p = 1..30`, phases `φ < 4`.
-/

namespace Ruliology.CellularAutomata
namespace Rule30EtherSingleCell

open Rule30Ether Rule30Jen Rule30StripCertificates

set_option maxRecDepth 100000
set_option maxHeartbeats 0






set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem case_1_3 :
    InFamily (drv (fun n => wordAt w0001 (n + 3)) (delta 1)) 6 3 79 :=
  famBAt_sound (k := 3) (by decide)

theorem case_3_0 :
    InFamily (drv (fun n => wordAt w0001 (n + 0)) (delta 3)) 6 0 8 :=
  famBAt_sound (k := 3) (by decide)

theorem case_4_1 :
    InFamily (drv (fun n => wordAt w0001 (n + 1)) (delta 4)) 6 1 113 :=
  famBAt_sound (k := 10) (by decide)

theorem case_4_2 :
    InFamily (drv (fun n => wordAt w0001 (n + 2)) (delta 4)) 6 2 65 :=
  famBAt_sound (k := 3) (by decide)

theorem case_8_2 :
    InFamily (drv (fun n => wordAt w0001 (n + 2)) (delta 8)) 6 2 92 :=
  famBAt_sound (k := 3) (by decide)

theorem case_12_2 :
    InFamily (drv (fun n => wordAt w0001 (n + 2)) (delta 12)) 6 2 47 :=
  famBAt_sound (k := 3) (by decide)

theorem case_12_3 :
    InFamily (drv (fun n => wordAt w0001 (n + 3)) (delta 12)) 6 3 338 :=
  famBAt_sound (k := 10) (by decide)

theorem case_18_1 :
    InFamily (drv (fun n => wordAt w0001 (n + 1)) (delta 18)) 6 1 21 :=
  famBAt_sound (k := 3) (by decide)

theorem case_19_0 :
    InFamily (drv (fun n => wordAt w0001 (n + 0)) (delta 19)) 6 0 9 :=
  famBAt_sound (k := 3) (by decide)

theorem case_21_2 :
    InFamily (drv (fun n => wordAt w0001 (n + 2)) (delta 21)) 6 2 12 :=
  famBAt_sound (k := 3) (by decide)

theorem case_24_2 :
    InFamily (drv (fun n => wordAt w0001 (n + 2)) (delta 24)) 6 2 30 :=
  famBAt_sound (k := 3) (by decide)

theorem case_27_2 :
    InFamily (drv (fun n => wordAt w0001 (n + 2)) (delta 27)) 6 2 12 :=
  famBAt_sound (k := 3) (by decide)

theorem case_29_1 :
    InFamily (drv (fun n => wordAt w0001 (n + 1)) (delta 29)) 6 1 13 :=
  famBAt_sound (k := 3) (by decide)







set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem case_1_1 :
    InFamily (drv (fun n => wordAt w0001 (n + 1)) (delta 1)) 6 1 10 :=
  famBAt_sound (k := 3) (by decide)

theorem case_3_2 :
    InFamily (drv (fun n => wordAt w0001 (n + 2)) (delta 3)) 6 2 108 :=
  famBAt_sound (k := 3) (by decide)

theorem case_6_2 :
    InFamily (drv (fun n => wordAt w0001 (n + 2)) (delta 6)) 6 2 40 :=
  famBAt_sound (k := 3) (by decide)

theorem case_13_0 :
    InFamily (drv (fun n => wordAt w0001 (n + 0)) (delta 13)) 6 0 325 :=
  famBAt_sound (k := 3) (by decide)

theorem case_13_2 :
    InFamily (drv (fun n => wordAt w0001 (n + 2)) (delta 13)) 6 2 21 :=
  famBAt_sound (k := 3) (by decide)

theorem case_16_3 :
    InFamily (drv (fun n => wordAt w0001 (n + 3)) (delta 16)) 6 3 12 :=
  famBAt_sound (k := 3) (by decide)

theorem case_18_2 :
    InFamily (drv (fun n => wordAt w0001 (n + 2)) (delta 18)) 6 2 53 :=
  famBAt_sound (k := 3) (by decide)

theorem case_20_2 :
    InFamily (drv (fun n => wordAt w0001 (n + 2)) (delta 20)) 6 2 114 :=
  famBAt_sound (k := 3) (by decide)

theorem case_23_1 :
    InFamily (drv (fun n => wordAt w0001 (n + 1)) (delta 23)) 6 1 62 :=
  famBAt_sound (k := 3) (by decide)

theorem case_25_0 :
    InFamily (drv (fun n => wordAt w0001 (n + 0)) (delta 25)) 6 0 74 :=
  famBAt_sound (k := 3) (by decide)

theorem case_27_1 :
    InFamily (drv (fun n => wordAt w0001 (n + 1)) (delta 27)) 6 1 21 :=
  famBAt_sound (k := 3) (by decide)

theorem case_27_3 :
    InFamily (drv (fun n => wordAt w0001 (n + 3)) (delta 27)) 6 3 11 :=
  famBAt_sound (k := 3) (by decide)

theorem case_30_2 :
    InFamily (drv (fun n => wordAt w0001 (n + 2)) (delta 30)) 6 2 12 :=
  famBAt_sound (k := 3) (by decide)







set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem case_4_0 :
    InFamily (drv (fun n => wordAt w0001 (n + 0)) (delta 4)) 5 0 8 :=
  famBAt_sound (k := 4) (by decide)

theorem case_5_1 :
    InFamily (drv (fun n => wordAt w0001 (n + 1)) (delta 5)) 6 1 117 :=
  famBAt_sound (k := 3) (by decide)

theorem case_7_1 :
    InFamily (drv (fun n => wordAt w0001 (n + 1)) (delta 7)) 6 1 88 :=
  famBAt_sound (k := 3) (by decide)

theorem case_15_1 :
    InFamily (drv (fun n => wordAt w0001 (n + 1)) (delta 15)) 6 1 91 :=
  famBAt_sound (k := 3) (by decide)

theorem case_18_0 :
    InFamily (drv (fun n => wordAt w0001 (n + 0)) (delta 18)) 6 0 140 :=
  famBAt_sound (k := 3) (by decide)

theorem case_19_3 :
    InFamily (drv (fun n => wordAt w0001 (n + 3)) (delta 19)) 6 3 52 :=
  famBAt_sound (k := 3) (by decide)

theorem case_20_1 :
    InFamily (drv (fun n => wordAt w0001 (n + 1)) (delta 20)) 6 1 259 :=
  famBAt_sound (k := 3) (by decide)

theorem case_21_0 :
    InFamily (drv (fun n => wordAt w0001 (n + 0)) (delta 21)) 6 0 58 :=
  famBAt_sound (k := 3) (by decide)

theorem case_22_1 :
    InFamily (drv (fun n => wordAt w0001 (n + 1)) (delta 22)) 6 1 12 :=
  famBAt_sound (k := 3) (by decide)

theorem case_22_2 :
    InFamily (drv (fun n => wordAt w0001 (n + 2)) (delta 22)) 6 2 21 :=
  famBAt_sound (k := 3) (by decide)

theorem case_23_0 :
    InFamily (drv (fun n => wordAt w0001 (n + 0)) (delta 23)) 6 0 14 :=
  famBAt_sound (k := 3) (by decide)

theorem case_24_1 :
    InFamily (drv (fun n => wordAt w0001 (n + 1)) (delta 24)) 6 1 124 :=
  famBAt_sound (k := 3) (by decide)

theorem case_24_3 :
    InFamily (drv (fun n => wordAt w0001 (n + 3)) (delta 24)) 6 3 11 :=
  famBAt_sound (k := 3) (by decide)

theorem case_26_0 :
    InFamily (drv (fun n => wordAt w0001 (n + 0)) (delta 26)) 6 0 32 :=
  famBAt_sound (k := 3) (by decide)

theorem case_30_0 :
    InFamily (drv (fun n => wordAt w0001 (n + 0)) (delta 30)) 6 0 14 :=
  famBAt_sound (k := 3) (by decide)







set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem case_1_0 :
    InFamily (drv (fun n => wordAt w0001 (n + 0)) (delta 1)) 6 0 10 :=
  famBAt_sound (k := 3) (by decide)

theorem case_2_0 :
    InFamily (drv (fun n => wordAt w0001 (n + 0)) (delta 2)) 6 0 78 :=
  famBAt_sound (k := 3) (by decide)

theorem case_2_1 :
    InFamily (drv (fun n => wordAt w0001 (n + 1)) (delta 2)) 6 1 48 :=
  famBAt_sound (k := 3) (by decide)

theorem case_4_3 :
    InFamily (drv (fun n => wordAt w0001 (n + 3)) (delta 4)) 6 3 25 :=
  famBAt_sound (k := 3) (by decide)

theorem case_5_0 :
    InFamily (drv (fun n => wordAt w0001 (n + 0)) (delta 5)) 6 0 152 :=
  famBAt_sound (k := 3) (by decide)

theorem case_10_1 :
    InFamily (drv (fun n => wordAt w0001 (n + 1)) (delta 10)) 6 1 241 :=
  famBAt_sound (k := 3) (by decide)

theorem case_11_2 :
    InFamily (drv (fun n => wordAt w0001 (n + 2)) (delta 11)) 6 2 89 :=
  famBAt_sound (k := 3) (by decide)

theorem case_14_1 :
    InFamily (drv (fun n => wordAt w0001 (n + 1)) (delta 14)) 6 1 12 :=
  famBAt_sound (k := 3) (by decide)

theorem case_16_0 :
    InFamily (drv (fun n => wordAt w0001 (n + 0)) (delta 16)) 6 0 107 :=
  famBAt_sound (k := 3) (by decide)

theorem case_16_2 :
    InFamily (drv (fun n => wordAt w0001 (n + 2)) (delta 16)) 6 2 117 :=
  famBAt_sound (k := 3) (by decide)

theorem case_17_0 :
    InFamily (drv (fun n => wordAt w0001 (n + 0)) (delta 17)) 6 0 130 :=
  famBAt_sound (k := 3) (by decide)

theorem case_21_1 :
    InFamily (drv (fun n => wordAt w0001 (n + 1)) (delta 21)) 6 1 57 :=
  famBAt_sound (k := 3) (by decide)

theorem case_23_2 :
    InFamily (drv (fun n => wordAt w0001 (n + 2)) (delta 23)) 6 2 30 :=
  famBAt_sound (k := 3) (by decide)

theorem case_28_1 :
    InFamily (drv (fun n => wordAt w0001 (n + 1)) (delta 28)) 6 1 13 :=
  famBAt_sound (k := 3) (by decide)

theorem case_28_3 :
    InFamily (drv (fun n => wordAt w0001 (n + 3)) (delta 28)) 6 3 11 :=
  famBAt_sound (k := 3) (by decide)







set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem case_2_2 :
    InFamily (drv (fun n => wordAt w0001 (n + 2)) (delta 2)) 5 2 10 :=
  famBAt_sound (k := 4) (by decide)

theorem case_5_3 :
    InFamily (drv (fun n => wordAt w0001 (n + 3)) (delta 5)) 6 3 63 :=
  famBAt_sound (k := 3) (by decide)

theorem case_6_1 :
    InFamily (drv (fun n => wordAt w0001 (n + 1)) (delta 6)) 6 1 97 :=
  famBAt_sound (k := 3) (by decide)

theorem case_9_0 :
    InFamily (drv (fun n => wordAt w0001 (n + 0)) (delta 9)) 6 0 213 :=
  famBAt_sound (k := 3) (by decide)

theorem case_10_2 :
    InFamily (drv (fun n => wordAt w0001 (n + 2)) (delta 10)) 6 2 112 :=
  famBAt_sound (k := 3) (by decide)

theorem case_14_0 :
    InFamily (drv (fun n => wordAt w0001 (n + 0)) (delta 14)) 6 0 78 :=
  famBAt_sound (k := 3) (by decide)

theorem case_15_2 :
    InFamily (drv (fun n => wordAt w0001 (n + 2)) (delta 15)) 6 2 134 :=
  famBAt_sound (k := 3) (by decide)

theorem case_19_2 :
    InFamily (drv (fun n => wordAt w0001 (n + 2)) (delta 19)) 6 2 62 :=
  famBAt_sound (k := 3) (by decide)

theorem case_20_3 :
    InFamily (drv (fun n => wordAt w0001 (n + 3)) (delta 20)) 6 3 10 :=
  famBAt_sound (k := 3) (by decide)

theorem case_22_0 :
    InFamily (drv (fun n => wordAt w0001 (n + 0)) (delta 22)) 6 0 124 :=
  famBAt_sound (k := 3) (by decide)

theorem case_24_0 :
    InFamily (drv (fun n => wordAt w0001 (n + 0)) (delta 24)) 6 0 155 :=
  famBAt_sound (k := 3) (by decide)

theorem case_25_1 :
    InFamily (drv (fun n => wordAt w0001 (n + 1)) (delta 25)) 6 1 31 :=
  famBAt_sound (k := 3) (by decide)

theorem case_25_3 :
    InFamily (drv (fun n => wordAt w0001 (n + 3)) (delta 25)) 6 3 19 :=
  famBAt_sound (k := 3) (by decide)

theorem case_26_2 :
    InFamily (drv (fun n => wordAt w0001 (n + 2)) (delta 26)) 6 2 13 :=
  famBAt_sound (k := 3) (by decide)

theorem case_28_0 :
    InFamily (drv (fun n => wordAt w0001 (n + 0)) (delta 28)) 6 0 15 :=
  famBAt_sound (k := 3) (by decide)

theorem case_29_3 :
    InFamily (drv (fun n => wordAt w0001 (n + 3)) (delta 29)) 6 3 11 :=
  famBAt_sound (k := 3) (by decide)







set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem case_2_3 :
    InFamily (drv (fun n => wordAt w0001 (n + 3)) (delta 2)) 6 3 79 :=
  famBAt_sound (k := 3) (by decide)

theorem case_3_3 :
    InFamily (drv (fun n => wordAt w0001 (n + 3)) (delta 3)) 6 3 95 :=
  famBAt_sound (k := 3) (by decide)

theorem case_7_2 :
    InFamily (drv (fun n => wordAt w0001 (n + 2)) (delta 7)) 6 2 138 :=
  famBAt_sound (k := 3) (by decide)

theorem case_7_3 :
    InFamily (drv (fun n => wordAt w0001 (n + 3)) (delta 7)) 6 3 120 :=
  famBAt_sound (k := 3) (by decide)

theorem case_8_1 :
    InFamily (drv (fun n => wordAt w0001 (n + 1)) (delta 8)) 6 1 42 :=
  famBAt_sound (k := 3) (by decide)

theorem case_8_3 :
    InFamily (drv (fun n => wordAt w0001 (n + 3)) (delta 8)) 6 3 9 :=
  famBAt_sound (k := 3) (by decide)

theorem case_9_2 :
    InFamily (drv (fun n => wordAt w0001 (n + 2)) (delta 9)) 6 2 13 :=
  famBAt_sound (k := 3) (by decide)

theorem case_11_1 :
    InFamily (drv (fun n => wordAt w0001 (n + 1)) (delta 11)) 6 1 50 :=
  famBAt_sound (k := 3) (by decide)

theorem case_12_0 :
    InFamily (drv (fun n => wordAt w0001 (n + 0)) (delta 12)) 6 0 72 :=
  famBAt_sound (k := 10) (by decide)

theorem case_12_1 :
    InFamily (drv (fun n => wordAt w0001 (n + 1)) (delta 12)) 6 1 209 :=
  famBAt_sound (k := 3) (by decide)

theorem case_14_3 :
    InFamily (drv (fun n => wordAt w0001 (n + 3)) (delta 14)) 6 3 160 :=
  famBAt_sound (k := 3) (by decide)

theorem case_16_1 :
    InFamily (drv (fun n => wordAt w0001 (n + 1)) (delta 16)) 6 1 28 :=
  famBAt_sound (k := 10) (by decide)

theorem case_18_3 :
    InFamily (drv (fun n => wordAt w0001 (n + 3)) (delta 18)) 6 3 127 :=
  famBAt_sound (k := 3) (by decide)

theorem case_25_2 :
    InFamily (drv (fun n => wordAt w0001 (n + 2)) (delta 25)) 6 2 12 :=
  famBAt_sound (k := 3) (by decide)

theorem case_27_0 :
    InFamily (drv (fun n => wordAt w0001 (n + 0)) (delta 27)) 6 0 14 :=
  famBAt_sound (k := 3) (by decide)

theorem case_29_2 :
    InFamily (drv (fun n => wordAt w0001 (n + 2)) (delta 29)) 6 2 12 :=
  famBAt_sound (k := 3) (by decide)







set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem case_1_2 :
    InFamily (drv (fun n => wordAt w0001 (n + 2)) (delta 1)) 6 2 10 :=
  famBAt_sound (k := 3) (by decide)

theorem case_6_0 :
    InFamily (drv (fun n => wordAt w0001 (n + 0)) (delta 6)) 6 0 74 :=
  famBAt_sound (k := 3) (by decide)

theorem case_6_3 :
    InFamily (drv (fun n => wordAt w0001 (n + 3)) (delta 6)) 6 3 43 :=
  famBAt_sound (k := 3) (by decide)

theorem case_8_0 :
    InFamily (drv (fun n => wordAt w0001 (n + 0)) (delta 8)) 6 0 135 :=
  famBAt_sound (k := 3) (by decide)

theorem case_9_1 :
    InFamily (drv (fun n => wordAt w0001 (n + 1)) (delta 9)) 6 1 181 :=
  famBAt_sound (k := 3) (by decide)

theorem case_9_3 :
    InFamily (drv (fun n => wordAt w0001 (n + 3)) (delta 9)) 6 3 15 :=
  famBAt_sound (k := 3) (by decide)

theorem case_11_3 :
    InFamily (drv (fun n => wordAt w0001 (n + 3)) (delta 11)) 6 3 77 :=
  famBAt_sound (k := 3) (by decide)

theorem case_13_1 :
    InFamily (drv (fun n => wordAt w0001 (n + 1)) (delta 13)) 6 1 96 :=
  famBAt_sound (k := 3) (by decide)

theorem case_14_2 :
    InFamily (drv (fun n => wordAt w0001 (n + 2)) (delta 14)) 6 2 47 :=
  famBAt_sound (k := 3) (by decide)

theorem case_17_1 :
    InFamily (drv (fun n => wordAt w0001 (n + 1)) (delta 17)) 6 1 107 :=
  famBAt_sound (k := 3) (by decide)

theorem case_17_3 :
    InFamily (drv (fun n => wordAt w0001 (n + 3)) (delta 17)) 6 3 196 :=
  famBAt_sound (k := 3) (by decide)

theorem case_21_3 :
    InFamily (drv (fun n => wordAt w0001 (n + 3)) (delta 21)) 6 3 123 :=
  famBAt_sound (k := 3) (by decide)

theorem case_23_3 :
    InFamily (drv (fun n => wordAt w0001 (n + 3)) (delta 23)) 6 3 27 :=
  famBAt_sound (k := 3) (by decide)

theorem case_26_3 :
    InFamily (drv (fun n => wordAt w0001 (n + 3)) (delta 26)) 6 3 11 :=
  famBAt_sound (k := 3) (by decide)

theorem case_28_2 :
    InFamily (drv (fun n => wordAt w0001 (n + 2)) (delta 28)) 6 2 12 :=
  famBAt_sound (k := 3) (by decide)

theorem case_30_1 :
    InFamily (drv (fun n => wordAt w0001 (n + 1)) (delta 30)) 6 1 13 :=
  famBAt_sound (k := 3) (by decide)







set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem case_3_1 :
    InFamily (drv (fun n => wordAt w0001 (n + 1)) (delta 3)) 6 1 142 :=
  famBAt_sound (k := 3) (by decide)

theorem case_5_2 :
    InFamily (drv (fun n => wordAt w0001 (n + 2)) (delta 5)) 6 2 193 :=
  famBAt_sound (k := 3) (by decide)

theorem case_7_0 :
    InFamily (drv (fun n => wordAt w0001 (n + 0)) (delta 7)) 6 0 13 :=
  famBAt_sound (k := 3) (by decide)

theorem case_10_0 :
    InFamily (drv (fun n => wordAt w0001 (n + 0)) (delta 10)) 6 0 94 :=
  famBAt_sound (k := 3) (by decide)

theorem case_10_3 :
    InFamily (drv (fun n => wordAt w0001 (n + 3)) (delta 10)) 6 3 183 :=
  famBAt_sound (k := 3) (by decide)

theorem case_11_0 :
    InFamily (drv (fun n => wordAt w0001 (n + 0)) (delta 11)) 6 0 114 :=
  famBAt_sound (k := 3) (by decide)

theorem case_13_3 :
    InFamily (drv (fun n => wordAt w0001 (n + 3)) (delta 13)) 6 3 39 :=
  famBAt_sound (k := 3) (by decide)

theorem case_15_0 :
    InFamily (drv (fun n => wordAt w0001 (n + 0)) (delta 15)) 6 0 24 :=
  famBAt_sound (k := 3) (by decide)

theorem case_15_3 :
    InFamily (drv (fun n => wordAt w0001 (n + 3)) (delta 15)) 6 3 54 :=
  famBAt_sound (k := 3) (by decide)

theorem case_17_2 :
    InFamily (drv (fun n => wordAt w0001 (n + 2)) (delta 17)) 6 2 7 :=
  famBAt_sound (k := 3) (by decide)

theorem case_19_1 :
    InFamily (drv (fun n => wordAt w0001 (n + 1)) (delta 19)) 6 1 76 :=
  famBAt_sound (k := 3) (by decide)

theorem case_20_0 :
    InFamily (drv (fun n => wordAt w0001 (n + 0)) (delta 20)) 6 0 126 :=
  famBAt_sound (k := 3) (by decide)

theorem case_22_3 :
    InFamily (drv (fun n => wordAt w0001 (n + 3)) (delta 22)) 6 3 63 :=
  famBAt_sound (k := 3) (by decide)

theorem case_26_1 :
    InFamily (drv (fun n => wordAt w0001 (n + 1)) (delta 26)) 6 1 13 :=
  famBAt_sound (k := 3) (by decide)

theorem case_29_0 :
    InFamily (drv (fun n => wordAt w0001 (n + 0)) (delta 29)) 6 0 14 :=
  famBAt_sound (k := 3) (by decide)

theorem case_30_3 :
    InFamily (drv (fun n => wordAt w0001 (n + 3)) (delta 30)) 6 3 11 :=
  famBAt_sound (k := 3) (by decide)


end Rule30EtherSingleCell
end Ruliology.CellularAutomata
