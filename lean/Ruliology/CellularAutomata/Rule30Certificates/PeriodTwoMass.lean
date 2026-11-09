module

public import Ruliology.CellularAutomata.Rule30ZeroBoundary

/-!
# Conjecture S to length `90`: the kernel check

Data for `Rule30PeriodTwoMass`: the kernel evaluates `fdfs 90 91 0 0 0 = true` (`fcert90`,
`decide +kernel`), an exhaustive search over the seeds `Y < 2 ^ H`, `H ≤ 90`, of the zero-wall map
`Rule30ZeroBoundary.IntegerForm.F`. A node `(k, Y, w)` is a seed `Y < 2 ^ k` whose wall trace is a
G word of length `k`, with `w` its number of ones. Its children are `Y` and `Y + 2 ^ k`; one
iteration `iter F (k - 2) Y` gives the trace bits at times `k - 2` and `k` (`trPair`), and the
child `Y + 2 ^ k` has the same bit at time `k - 2` and the opposite bit at time `k`. A node with
`N + 5 ≤ 7 w` is not expanded. `Rule30PeriodTwoMass.fdfs_dfs` proves that this search implies the
plain search `Rule30PeriodTwoMass.dfs`, whose soundness `dfs_sound` gives `S_upto_90`.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30PeriodTwoMass

open Rule30ZeroBoundary.IntegerForm (F iter)

/-- The bound of Conjecture S at a node of length `k` and weight `w` (even form at even `k`). -/
def okW (k w : Nat) : Bool :=
  if k < 2 then true else if k % 2 = 0 then decide (k + 5 ≤ 7 * w)
  else decide (k + 4 ≤ 7 * w)

/-- The G rule at time `k`, from the trace bits `a` at time `k - 2` and `b` at time `k`. -/
def gs (k : Nat) (a b : Bool) : Bool :=
  if k = 0 then !b else if k % 2 = 1 then b else (a || b)

/-- The trace bits at times `k - 2` and `k`, from the row `B` at time `k - 2` (at `k < 2` the
first is unused and `B` is the seed). -/
def pairOf (k B : Nat) : Bool × Bool :=
  if k < 2 then (false, (iter F k B).testBit 0) else (B.testBit 0, (F (F B)).testBit 0)

/-- The trace bits of the seed `Y` at times `k - 2` and `k`. -/
def trPair (k Y : Nat) : Bool × Bool := pairOf k (iter F (k - 2) Y)

/-- The search with the weight `w` carried along and one trace iteration per node. -/
def fdfs (N : Nat) : Nat → Nat → Nat → Nat → Bool
  | 0, _, _, _ => true
  | f + 1, k, Y, w =>
    decide (N + 5 ≤ 7 * w) ||
    (okW k w && (!(gs k (trPair k Y).1 (trPair k Y).2) || fdfs N f (k + 1) Y w) &&
      (!(gs k (trPair k Y).1 (!(trPair k Y).2)) || fdfs N f (k + 1) (Y + 2 ^ k) (w + 1)))

set_option maxHeartbeats 0 in
/-- The search to length `90` succeeds (kernel evaluation, no native code). -/
theorem fcert90 : fdfs 90 91 0 0 0 = true := by decide +kernel

end Ruliology.CellularAutomata.Rule30PeriodTwoMass
