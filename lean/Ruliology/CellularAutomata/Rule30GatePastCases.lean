module
public import Ruliology.CellularAutomata.Rule30Certificates.GatePastCases

/-! Checked closing bounds for legal five-, six-, and seven-bit gate pasts.
The future is arbitrary and infinite. Arbitrary past length remains open. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30GatePastCases
open Rule30ZeroBoundary Rule30PastStrip Rule30GatePastCover

namespace Five
theorem legal_pasts_agree (G : Nat → Bool) (p q : Fin 32)
    (hg : GateLegal G) (hp : GateLegal (prependN 5 p G)) (hq : GateLegal (prependN 5 q G)) :
    ∀ k, 49≤k → lam (oddTrace (prependN 5 p G)) k = lam (oddTrace (prependN 5 q G)) k := by
  exact Rule30Certificates.GatePastCases.Five.legal_pasts_agree G p q hg hp hq
end Five

namespace Six
theorem legal_pasts_agree (G : Nat → Bool) (p q : Fin 64)
    (hg : GateLegal G) (hp : GateLegal (prependN 6 p G)) (hq : GateLegal (prependN 6 q G)) :
    ∀ k, 99≤k → lam (oddTrace (prependN 6 p G)) k = lam (oddTrace (prependN 6 q G)) k := by
  exact Rule30Certificates.GatePastCases.Six.legal_pasts_agree G p q hg hp hq
end Six

namespace Seven
theorem legal_pasts_agree (G : Nat → Bool) (p q : Fin 128)
    (hg : GateLegal G) (hp : GateLegal (prependN 7 p G)) (hq : GateLegal (prependN 7 q G)) :
    ∀ k, 107≤k → lam (oddTrace (prependN 7 p G)) k = lam (oddTrace (prependN 7 q G)) k := by
  exact Rule30Certificates.GatePastCases.Seven.legal_pasts_agree G p q hg hp hq
end Seven

end Ruliology.CellularAutomata.Rule30GatePastCases
