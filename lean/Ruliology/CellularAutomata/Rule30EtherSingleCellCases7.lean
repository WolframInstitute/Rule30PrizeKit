module

public import Ruliology.CellularAutomata.Rule30EtherSingleCellAux

@[expose] public section


namespace Ruliology.CellularAutomata
namespace Rule30Ether

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

end Rule30Ether
end Ruliology.CellularAutomata
