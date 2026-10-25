module

public import Ruliology.CellularAutomata.Rule30EtherSingleCellAux

@[expose] public section


namespace Ruliology.CellularAutomata
namespace Rule30Ether

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

end Rule30Ether
end Ruliology.CellularAutomata
