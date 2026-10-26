#!/bin/bash
# Build everything in the kit: prebuilt Mathlib, the statements, the equivalences, the template, and
# every module of the catalog. setup.sh builds only what the template imports; run this before you
# import another catalog module, or build that module alone with `lake build Ruliology.<Module>`.
#
#   bash build_all.sh        stop at the first module that fails
#   bash build_all.sh -k     go on, and list the modules that failed at the end
#
# The catalog builds one module at a time, in the order of lean/README.md: a cold parallel build of
# its certificate modules needs about 12.5 GB. Each module's output is in .lake/build-logs/.
set -u
cd "$(dirname "$0")"
keep=0
[ "${1:-}" = "-k" ] && keep=1
mkdir -p .lake/build-logs
failed=""

build() {
  local name=$1
  shift
  if lake build "$@" > ".lake/build-logs/$name.log" 2>&1; then
    echo "ok    $name"
  else
    echo "FAIL  $name"
    failed="$failed $name"
    if [ "$keep" = 0 ]; then tail -40 ".lake/build-logs/$name.log"; exit 1; fi
  fi
}

lake exe cache get || exit 1
build kit Rule30PrizeKit Rule30Challenge Rule30Submission
for m in Rule30Predecessors Rule30PredecessorCounts BusyBeaverLifetimes Rule30Blocks Rule30Jen \
    Rule30Prize Rule30Window Rule30MaskedJen Rule30Diagonals Rule30BlackRuns Rule30BlackRunBlocks \
    Rule30StripCertificates Rule30StripCertificateTable Rule30DrivenLeft Rule30RightPeriods \
    Rule30WhiteSeed Rule30Realization Rule30FactorWindow Rule30PeriodTwo Rule30ZeroBoundary \
    Rule30ZeroBoundaryStripe Rule30ZeroBoundarySmall Rule30ZeroBoundaryBarriers Rule30Ether \
    Rule30PeriodTwoCoupled Rule30PeriodFourSkeleton Rule30ZeroBoundaryLanes \
    Rule30Certificates.ZeroBoundaryWidth52Chunks0 Rule30Certificates.ZeroBoundaryWidth52Chunks1 \
    Rule30Certificates.ZeroBoundaryWidth52Chunks2 Rule30Certificates.ZeroBoundaryWidth52Chunks3 \
    Rule30ZeroBoundaryWidth52 Rule30ZeroBoundaryStripeFront \
    Rule30Certificates.ZeroBoundaryStripeCycles0 Rule30Certificates.ZeroBoundaryStripeCycles1 \
    Rule30Certificates.ZeroBoundaryStripeCycles2 Rule30Certificates.ZeroBoundaryStripeCycles3 \
    Rule30ZeroBoundaryStripeFamily Rule30ZeroBoundaryStripeFour \
    Rule30ZeroBoundaryStripeFrontLift Rule30Certificates.StripeTail13Completion \
    Rule30ZeroBoundaryStripeFourComplete Rule30EtherTrap \
    Rule30Certificates.EtherTrap0 Rule30Certificates.EtherTrap1 Rule30Certificates.EtherTrap2 \
    Rule30Certificates.EtherTrap3 Rule30Certificates.EtherTrap4 Rule30Certificates.EtherTrap5 \
    Rule30EtherTrapWidth20 Rule30PeriodTwoLanguage Rule30PeriodTwoWidth5 Rule30PeriodTwoWidth6 \
    Rule30EtherThree Rule30EtherThreeNoWall Rule30EtherThreeTrap Rule30EtherThreeReach \
    Rule30EtherThreeLeft Rule30EtherThreeSkeleton Rule30Certificates.WhiteEndChecks Rule30WhiteEnd \
    Rule30WhitePadding \
    Rule30FiniteStrips \
    Rule30WhitePulse \
    Rule30ZeroPredecessor \
    Rule30BackwardTube \
    Rule30WhitePaddingVacuumCriterion \
    Rule30BackwardVacuum \
    Rule30SparsePreimage \
    Rule30Certificates.FiveTailTube \
    Rule30Certificates.SixTailBackward \
    Rule30RestrictedBackwardTube \
    Rule30Certificates.SixTailEndpoints \
    Rule30Certificates.WhitePaddingFamilies \
    Rule30UniformWhitePadding \
    Rule30WordRotation \
    Rule30ShortTail \
    Rule30FiveTailReduction \
    Rule30VacuumExample \
    Rule30WhitePadding10101 \
    Rule30FiveTail \
    Rule30ForbiddenSuffix \
    Rule30SixTailReduction \
    Rule30SixTail \
    Rule30SixTailSharpened \
    Rule30SuffixFamilies \
    Rule30Certificates.StripeMeeting \
    Rule30StripeMeeting \
    Rule30Certificates.PeriodThirtyTwoPool \
    Rule30Certificates.PeriodThirtyTwoChecks{0..33} \
    Rule30Certificates.PeriodThirtyTwoDetection \
    Rule30PeriodThirtyTwoShielding; do
  build "$m" "Ruliology.CellularAutomata.$m"
done
build Ruliology Ruliology

if [ -z "$failed" ]; then echo "all built"; else echo "failed:$failed"; exit 1; fi
