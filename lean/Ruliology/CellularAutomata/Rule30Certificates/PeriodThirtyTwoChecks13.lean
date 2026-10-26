module

public import Ruliology.CellularAutomata.Rule30Certificates.PeriodThirtyTwoPool

/-!
# Period-32 pool checks, blocks 26 through 27

Ordinary-kernel checks of closure and the shielding gate property for this
slice of the 2,116-node pool.  The data itself is defined once in
`PeriodThirtyTwoPool`.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate

open Ruliology.CellularAutomata.Rule30FiniteClockCertificate

set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem block26_gate :
    (block26.all rowGateOK) = true := by
  decide +kernel

theorem block_26_closed :
    (block26.all (nodeCheck 32 pool32)) = true := by
  decide +kernel

theorem block27_gate :
    (block27.all rowGateOK) = true := by
  decide +kernel

theorem block_27_closed :
    (block27.all (nodeCheck 32 pool32)) = true := by
  decide +kernel

end Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate
