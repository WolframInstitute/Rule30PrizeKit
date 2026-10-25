module

public import Ruliology.CellularAutomata.Rule30EtherSingleCellAux

@[expose] public section


namespace Ruliology.CellularAutomata
namespace Rule30Ether

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

end Rule30Ether
end Ruliology.CellularAutomata
