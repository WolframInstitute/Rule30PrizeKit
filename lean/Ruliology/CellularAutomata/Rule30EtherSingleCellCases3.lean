module

public import Ruliology.CellularAutomata.Rule30EtherSingleCellAux

@[expose] public section


namespace Ruliology.CellularAutomata
namespace Rule30Ether

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

end Rule30Ether
end Ruliology.CellularAutomata
