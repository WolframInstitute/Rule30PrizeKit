module

public import Ruliology.CellularAutomata.Rule30Certificates.PeriodThirtyTwoPool

/-!
# Period-32 pool detection check

An ordinary-kernel check that a period-two head clock propagates through every
temporal pair in the 2,116-node pool.  Full coverage is assembled in
Rule30PeriodThirtyTwoShielding.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate

open Ruliology.CellularAutomata.Rule30FiniteClockCertificate

set_option maxRecDepth 32768
set_option maxHeartbeats 0

theorem detection32_checked :
    detectionCheck 32 2 pool32 = true := by
  decide +kernel

end Ruliology.CellularAutomata.Rule30PeriodThirtyTwoShielding.Certificate
