module

public import Ruliology.CellularAutomata.Rule30EtherSingleCellAux

@[expose] public section


namespace Ruliology.CellularAutomata
namespace Rule30Ether

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

end Rule30Ether
end Ruliology.CellularAutomata
