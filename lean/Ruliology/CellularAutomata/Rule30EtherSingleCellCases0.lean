module

public import Ruliology.CellularAutomata.Rule30EtherSingleCellAux

@[expose] public section


namespace Ruliology.CellularAutomata
namespace Rule30Ether

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

end Rule30Ether
end Ruliology.CellularAutomata
