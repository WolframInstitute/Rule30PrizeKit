module

public import Ruliology.CellularAutomata.Rule30EtherSingleCellAux

@[expose] public section


namespace Ruliology.CellularAutomata
namespace Rule30Ether

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

end Rule30Ether
end Ruliology.CellularAutomata
