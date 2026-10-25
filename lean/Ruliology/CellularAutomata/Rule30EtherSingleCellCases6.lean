module

public import Ruliology.CellularAutomata.Rule30EtherSingleCellAux

@[expose] public section


namespace Ruliology.CellularAutomata
namespace Rule30Ether

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

end Rule30Ether
end Ruliology.CellularAutomata
