# Rule 30: the statements and the catalog of partial results

This Lake project (package `rule30prize`, library `Ruliology`) holds the official Lean statements of the Rule 30 Prize problems and a catalog of proved partial results about rule 30, all in the namespace `Ruliology.CellularAutomata`. It is plain Lean 4.35.0, without Mathlib.

**Problem 1 is open.** Everything here is a partial result.

- **The statements:** `Ruliology/CellularAutomata/Rule30Jen.lean` defines `rule`, `cell` and `EventuallyPeriodic`. `Ruliology/CellularAutomata/Rule30Prize.lean` defines `center`, `Problem1` and `Problem2`. The kit's [README](../README.md) quotes them.
- **The catalog:** 54 modules. `Ruliology.lean` imports the 40 `Rule30*` modules; their import closure adds the 13 data modules in `Rule30Certificates/` and `BusyBeaverLifetimes`. Each module's docstring records its claim, method and sources.
- **Axioms:** every theorem uses only `propext`, `Classical.choice` and `Quot.sound`. None uses `sorry` or `native_decide`.
- **Provenance:** the 54 catalog modules come from the Ruliology catalog of 2026-10-15, byte for byte except one docstring sentence in `Rule30ZeroBoundaryWidth52`. `SHA256SUMS` lists their hashes as copied, which the kit's first commit, `c2dab06`, matches (`shasum -a 256 -c SHA256SUMS` in a checkout of it). Since then their comments have dropped catalog numbering and provenance, eight modules changed for Lean 4.35.0, and every file became a module of Lean's module system (`module`, `public import`, `@[expose] public section`, so all definitions stay unfoldable for importers) with deprecated names replaced; `git log lean/` shows each change.
- **Added in the kit:** modules proved after the snapshot, proved during the attempt but left out of the catalog, or contributed by participants in the prize. [Added in the kit](#added-in-the-kit) lists them, with credits.

## Status by period

| Case | Status | Lean (`lean/`, namespace `Ruliology.CellularAutomata.*`) |
|---|---|---|
| Period 1 | **Proved** for every column, and for every nonzero configuration with a leftmost black cell | `Rule30Prize.no_column_eventually_constant`, `center_not_eventually_period_one`, `Rule30FiniteConfigs.no_column_eventually_constant` |
| Small periods | **Proved:** no eventual period P ≤ 4096 with transient ≤ 8192 | `Rule30Window` |
| Any period | **Proved:** T + P ≥ 16359 | `Rule30FactorWindow` |
| Period 2 | Reduced to Q01, a statement about the zero-boundary left half. Q01 is **open** in general. It is proved in Lean for every start of width ≤ 52. | `Rule30PeriodTwo`, `Rule30PeriodTwoCoupled`, `Rule30PeriodTwoSideways`, `Rule30ZeroBoundary*`, `Rule30ZeroBoundaryWidth52`, `Rule30PeriodTwoWidth5/6` |
| Least period 3 | Reduced. 001 needs one of AbsorptionT t001, Q001 or C3s001. 011 needs C3w(011). All four are **open**. The ether-and-wall route is closed: the 12 × 3 ether has no wall of any width. | `Rule30EtherThree*` |
| Least period 4 | Reduced to Absorption, the ether-and-wall trap, which is **open**. The pure ether lies in no trap of width ≤ 20. Partial: single-cell and high-support absorption are proved (`Rule30EtherSingleCell`). | `Rule30Ether`, `Rule30PeriodFourSkeleton`, `Rule30EtherTrapWidth20`, `Rule30EtherSingleCell` |
| Longer periods | **Open.** Some words are excluded, for example by long black runs, 30 certified words and every `1 0^q` with `q ≥ 9`. | `Rule30BlackRuns`, `Rule30BlackRunBlocks`, `Rule30StripCertificateTable`, `Rule30WhiteRunEight`, `Rule30WhiteEnd`, `Rule30WhiteEndNine` |

Barriers are also proved:
- Rules 90, 150 and 210 share every structural fact the argument uses, yet their center columns are eventually constant (`Rule30Realization`).
- Local, strip, finite-state, additive and edge-DFA invariants cannot prove Q01 (`Rule30ZeroBoundaryBarriers`).

## Building

You need [elan](https://github.com/leanprover/elan); it installs Lean 4.35.0 from `lean-toolchain`.

`lake build` builds everything, but a cold build runs modules in parallel. The four `Rule30Certificates/ZeroBoundaryWidth52Chunks*` modules take about 20 s and 3 GB each, so a cold parallel build can need about 12.5 GB before the contributed tail modules below. Build these heavy data modules sequentially too.

Building one module at a time is safest; each `lake build` below compiles exactly one module, and peak memory stays under 4 GB.

```sh
cd lean
for m in Rule30Predecessors Rule30PredecessorCounts BusyBeaverLifetimes Rule30Blocks Rule30Jen \
    Rule30Prize Rule30Window Rule30MaskedJen Rule30Diagonals Rule30BlackRuns Rule30BlackRunBlocks \
    Rule30StripCertificates Rule30StripCertificateTable Rule30DrivenLeft Rule30RightPeriods \
    Rule30WhiteSeed Rule30Realization Rule30FactorWindow Rule30PeriodTwo Rule30ZeroBoundary \
    Rule30ZeroBoundaryStripe Rule30ZeroBoundarySmall Rule30ZeroBoundaryBarriers Rule30Ether \
    Rule30PeriodTwoCoupled Rule30PeriodFourSkeleton Rule30ZeroBoundaryLanes \
    Rule30Certificates.ZeroBoundaryWidth52Chunks{0,1,2,3} Rule30ZeroBoundaryWidth52 \
    Rule30ZeroBoundaryStripeFront Rule30Certificates.ZeroBoundaryStripeCycles{0,1,2,3} \
    Rule30ZeroBoundaryStripeFamily Rule30ZeroBoundaryStripeFour \
    Rule30ZeroBoundaryStripeFrontLift Rule30Certificates.StripeTail13Completion \
    Rule30ZeroBoundaryStripeFourComplete Rule30EtherTrap \
    Rule30Certificates.EtherTrap{0,1,2,3,4,5} \
    Rule30EtherSingleCellAux Rule30EtherSingleCellCases Rule30EtherSingleCell \
    Rule30EtherTrapWidth20 Rule30PeriodTwoLanguage Rule30PeriodTwoWidth5 Rule30PeriodTwoWidth6 \
    Rule30EtherThree Rule30EtherThreeNoWall Rule30EtherThreeTrap Rule30EtherThreeReach \
    Rule30EtherThreeLeft Rule30EtherThreeSkeleton Rule30WhiteRunEight Rule30PeriodTwoSideways \
    Rule30LightCone Rule30FiniteConfigs Rule30FiniteMaskedJen Rule30Coupled Rule30FiniteBlackRuns Rule30FiniteBlackRunBlocks Rule30FiniteDiagonals Rule30FiniteWhiteRuns \
    Rule30Certificates.WhiteEndChecks Rule30WhiteEnd Rule30WhiteEndNine \
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
    Rule30StripeMeeting; do
  lake build Ruliology.CellularAutomata.$m || break
done
lake build
```

On 2026-10-15 this took 285 s in total on an Apple M3 Max with 48 GB; the four upstream modules added on 2026-10-23 take about 45 s more. The contributed white-padding modules are measured separately below. Every module not listed below built in under 7 s and 1.2 GB.

| Module | Time | Peak memory |
|---|---|---|
| `Rule30Certificates/ZeroBoundaryWidth52Chunks0`–`3` | 22–24 s each | 2.7–2.8 GB each |
| `Rule30StripCertificateTable` | 21 s | 3.9 GB |
| `Rule30BlackRunBlocks` | 20 s | 2.3 GB |
| `Rule30ZeroBoundarySmall` | 19 s | 3.2 GB |
| `Rule30ZeroBoundaryStripe` | 18 s | 1.8 GB |
| `Rule30Certificates/WhiteEndChecks` | 34 s | 0.8 GB |
| `Rule30Certificates/StripeMeeting` | 47 s | 5.5 GB |
| `Rule30EtherSingleCellCases` | 76 s | 2.2 GB |
| `Rule30EtherThreeNoWall` | 9 s | 1.1 GB |
| `Rule30BlackRuns` | 9 s | 2.2 GB |

### Contributed stripe-front modules

Measured on Windows x64 with Lean 4.35.0 on 2026-10-25. Each module was built
alone with its imports already compiled. Peak memory is the sum of process
RSS, sampled every 50 ms and rounded up below.

| Module | Time | Peak memory |
|---|---|---|
| `Rule30Certificates/ZeroBoundaryStripeCycles3` | 41.8 s | 0.37 GB |
| `Rule30ZeroBoundaryStripeFrontLift` | 7.2 s | 0.73 GB |
| `Rule30Certificates/StripeTail13Completion` | 68.9 s | 2.00 GB |
| `Rule30ZeroBoundaryStripeFourComplete` | 6.0 s | 0.67 GB |

The original monolithic 256-segment tail-13 data compiled in 146.8 s and 0.99 GB on the same machine.
The return-map certificate packs only its 32 visited upper states into parallel lanes.

### Contributed white-padding modules

Measured on Windows x64 with Lean 4.35.0 on 2026-10-24, each module built alone with its imports already compiled. Peak memory is the sum of the processes' RSS, sampled every 50 ms. The other 20 modules of this family build in under 3 s and 0.5 GB each.

| Module | Time | Peak memory |
|---|---|---|
| `Rule30Certificates/WhitePaddingFamilies` | 285.22 s | 2372 MiB |
| `Rule30Certificates/FiveTailTube` | 147.70 s | 3061 MiB |
| `Rule30Certificates/SixTailBackward` | 84.51 s | 1376 MiB |
| `Rule30Certificates/SixTailEndpoints` | 20.16 s | 656 MiB |
| `Rule30SixTailReduction` | 7.12 s | 1222 MiB |

To check axioms, compile a file outside this folder from here:

```sh
cat > /tmp/Axioms.lean <<'EOF'
import Ruliology
#print axioms Ruliology.CellularAutomata.Rule30Prize.center_not_eventually_period_one
EOF
lake env lean /tmp/Axioms.lean
```

## Added in the kit

These modules are not in the 2026-10-15 snapshot of the catalog, and `SHA256SUMS` does not list them. All use only `propext`, `Classical.choice` and `Quot.sound`. To add one, see [Contributing a partial result](../README.md#contributing-a-partial-result).

| Module | Added | What it proves | Headline theorems |
|---|---|---|---|
| `Rule30PhysicalDefects` | 2026-10-27 | Under a hypothetical center period `P` from `T`, every `2P+1` consecutive physical column-one readings after `T+2P` contain a zero `2P`-shift mismatch. Distinct births satisfy `2m <= birthCount(2P,n0,4^m*n0)+1` for fixed `n0 >= T+2P, 4P`, counting sources in `[n0,X-1)`. Exact physical identities and conditional fixed upper-budget implications to Problem 1; the upper budgets remain unproved. Contributed by Troy Lowry with OpenAI Codex. | `bounded_mismatch_episode`, `birth_window`, `base_four_birth_lower`, `problem1_of_fixed_birth_budget` |
| `Rule30CommonGauge` | 2026-10-26 | Auxiliary divided-difference fields: zero-background common-mode classification, distance-dependent exterior phase coherence for every canonical age pair, and unbounded right-depth escape for every nonzero canonical field. Exact adapters identify the canonical mode and CommonField of `Rule30DividedDifference.ObserverCriterion`, and apply exterior coherence directly to that route. Includes ordinary-coordinate and finite-reset-window forms using XOR-rigidity gaps and dyadic returns. Contributed by Troy Lowry with OpenAI Codex. | `HalfLine.common_mode_classification`, `RightWedge.right_wedge_phase_subset`, `BandEscape.escapes_near_reset`, `BandEscape.arbitrarily_deep_after_any_time`, `BandEscape.Ordinary.arbitrarily_far_behind_front`, `ObserverConnection.canonical_common_iff`, `ObserverConnection.observer_mode_right_wedge` |
| `Rule30DividedDifference` | 2026-10-26 | Exact quadratic recombination error and gauged actual-pair evolution. The open auxiliary `ObserverCriterion`, for finite initially supported common modes at a shared lower boundary, implies `Rule30TraceEdge.EdgeObservable` and hence Problem 1. A finite all-gauge invisible mode over periodic backgrounds with no left bound fails `ModeObservable`; the bounded-background frontier keeps its left edge lo-t. Contributed by Troy Lowry with OpenAI Codex. | `curvature`, `Front.actual_difference`, `edgeObservable_of_observerCriterion`, `problem1_of_observerCriterion`, `barrier_mode_not_observable`, `Front.mode_left_edge` |
| `Rule30BackwardTube` | 2026-10-24 | Endpoint-conditioned backward strip certificates combine a finite predecessor chain with a stable zero-driven reachable set to exclude every sufficiently long white-padding word. Contributed by Troy Lowry with OpenAI Codex. | `preCheck_sound`, `tail_tube_forces`, `no_padding_of_endpoint_tube` |
| `Rule30FiniteStrips` | 2026-10-24 | Strip certificate soundness for every column of every configuration with a leftmost black cell, using the uniform masked Jen theorem; no initial strip-state assumption. Contributed by Troy Lowry with OpenAI Codex. | `not_eventually_word_strip`, `not_eventually_word_strip_finite` |
| `Rule30FiveTailReduction` | 2026-10-24 | Trimming white ends and rotating periods reduces every tail of at most five bits to the shorter family or eight new black-ended cores. Contributed by Troy Lowry with OpenAI Codex. | `decomposition`, `no_five_tail_of_cores` |
| `Rule30ForbiddenSuffix` | 2026-10-24 | A vacuum-free full-set image of a fixed suffix excludes white-padding families with arbitrary preceding tail words. Width and suffix are parameters. Contributed by Troy Lowry with OpenAI Codex. | `no_padding_of_forbidden_suffix`, `no_padding_of_forbidden_suffix_finite` |
| `Rule30RestrictedBackwardTube` | 2026-10-24 | Backward tube soundness with white-step predecessor checks restricted to the stable forward reachable set. Contributed by Troy Lowry with OpenAI Codex. | `restrictedPreCheck_sound`, `no_padding_of_endpoint_tube` |
| `Rule30ShortTail` | 2026-10-24 | Exclude every tail of at most four bits after at least 49 white phases, using finite strip certificates, trimming, and period rotation; uniform over all leftmost-black starts. Contributed by Troy Lowry with OpenAI Codex. | `no_short_tail_leftFinite`, `no_short_tail_finite` |
| `Rule30SixTail` | 2026-10-24 | Exclude every tail of at most six bits after at least 77 white phases. The sixteen new six-bit cores use backward-vacuum certificate chains; shorter tails use the five-tail theorem. Contributed by Troy Lowry with OpenAI Codex. | `no_six_tail_leftFinite`, `no_six_tail_finite` |
| `Rule30SixTailReduction` | 2026-10-24 | Trimming and rotation reduce every tail of at most six bits to the five-tail family or sixteen new black-ended cores. Contributed by Troy Lowry with OpenAI Codex. | `decomposition`, `no_six_tail_of_cores` |
| `Rule30SparsePreimage` | 2026-10-24 | Sparse predecessor checks with a proved bitmask completeness condition recover full strip predecessor implications. Contributed by Troy Lowry with OpenAI Codex. | `restricted_of_sparse`, `colConst_inter_of_sparse` |
| `Rule30UniformWhitePadding` | 2026-10-24 | The five pumping certificate families hold for every column of every leftmost-black start, using the generic finite-strip soundness theorem. Contributed by Troy Lowry with OpenAI Codex. | `no_paddingA_leftFinite`, `no_paddingE_leftFinite` |
| `Rule30VacuumExample` | 2026-10-24 | Two five-bit tail applications of the generic vacuum-avoidance criterion use width-five strips; the analytic white-pulse bound handles arbitrary padding. Contributed by Troy Lowry with OpenAI Codex. | `no_paddingA`, `no_paddingB` |
| `Rule30WhitePadding` | 2026-10-24 | A stable zero-driven reachable set and finite tail checks give a strip certificate for every sufficiently long white prefix, by pumping rather than enumerating padding lengths. Contributed by Troy Lowry with OpenAI Codex. | `zeros_stable`, `padding_strip`, `no_padding_word` |
| `Rule30EtherSingleCell` | 2026-10-25 | Single-cell and high-support period-4 absorption for `0001`: one black cell at every position/phase enters the ether-and-wall family (`singleCell_absorption`), and every finitely supported right half white on positions 1..30, of arbitrary support size, enters at time 14−φ (`absorption_high`). Case data is the single module `Rule30EtherSingleCellCases`. Not full absorption. Contributed by Eric Elbaz (Tensorbend.ai). | `singleCell_absorption`, `absorption_high` |
| `Rule30WhitePadding10101` | 2026-10-24 | The endpoint-conditioned backward tube excludes the five-bit tail 10101 after sufficiently many white phases, uniformly over all leftmost-black starts. Contributed by Troy Lowry with OpenAI Codex. | `no_padding_10101_leftFinite`, `no_padding_10101_finite` |
| `Rule30WhitePaddingVacuumCriterion` | 2026-10-24 | A stable zero-driven reachable set and a finite vacuum-free pulse image exclude arbitrary-tail white-padding families. The pulse and its length are unrestricted parameters. Contributed by Troy Lowry with OpenAI Codex. | `no_padding_of_vacuum_avoidance`, `no_padding_seed_of_vacuum_avoidance` |
| `Rule30WhitePulse` | 2026-10-24 | A striped block created by a long black run survives an arbitrary short boundary pulse by locality; the resulting analytic estimate supplies the padding thresholds. Contributed by Troy Lowry with OpenAI Codex. | `white_pulse_return`, `white_padding_forces_early_white` |
| `Rule30WordRotation` | 2026-10-24 | Eventual finite-word repetition is invariant under period rotation; trimming white ends gives the core-tail decomposition. Contributed by Troy Lowry with OpenAI Codex. | `eventuallyWord_swap`, `short_decomposition` |
| `Rule30ZeroPredecessor` | 2026-10-24 | The vacuum has a unique predecessor under a white boundary, uniformly in strip width, by induction through the strip. Contributed by Troy Lowry with OpenAI Codex. | `stripStep_zero_predecessor`, `stripStep_zero_iff` |
| `Rule30Certificates/FiveTailTube` | 2026-10-24 | Consolidated ordinary-kernel certificate data for the five-bit 10101 endpoint tube and the remaining five-bit vacuum-avoidance cores. Contributed by Troy Lowry with OpenAI Codex. | `Tube10101.Zmask` |
| `Rule30Certificates/SixTailBackward` | 2026-10-24 | Consolidated backward-vacuum certificate chains for the sixteen new six-bit black-ended cores. Definitions, predecessor checks, and assembly are in one module. Contributed by Troy Lowry with OpenAI Codex. | `C100001.no_padding` |
| `Rule30Certificates/SixTailEndpoints` | 2026-10-24 | Consolidated endpoint-conditioned predecessor certificates for 110001 and 111101, used to sharpen the common six-tail bound. Contributed by Troy Lowry with OpenAI Codex. | `C110001.no_padding` |
| `Rule30Certificates/WhitePaddingFamilies` | 2026-10-24 | Consolidated reachable-set pumping and vacuum-free suffix certificates for the general white-padding families. Contributed by Troy Lowry with OpenAI Codex. | `ForbiddenSuffix.safe011` |
| `Rule30SixTailSharpened` | 2026-10-24 | No column of a configuration with a leftmost black cell eventually repeats `0^r u` when `r >= 74` and `u` has at most six bits. Covers all nonzero finite starts and the single seed. Backward vacuum certificates give bound 77; two endpoint refinements reduce it to 74. Earlier bounds 69 for five bits and 49 for four bits remain. Proof and formalization by OpenAI Codex through `Troyusrex2`. | `no_six_tail_leftFinite`, `no_six_tail_finite`, `no_six_tail_seed` |
| `Rule30BackwardVacuum` | 2026-10-24 | A finite chain of backward predecessor implications, from the empty set to the vacuum along `0^N u`, excludes every eventual `0^r u` with `r >= max(N, 10*length(u)+11, K+9*(length(u)+1))`. It covers every column of every leftmost-black start without requiring a stabilized forward set. Proof and formalization by OpenAI Codex through `Troyusrex2`, using the existing white-pulse reduction. | `no_vacuum_of_backward_certificate`, `no_padding_of_backward_certificate` |
| `Rule30SuffixFamilies` | 2026-10-24 | For every Boolean word `v` of unrestricted length, no column of a configuration with a leftmost black cell eventually repeats `0^r v 011` when `r >= 10*length(v)+41`. Suffixes `001001` and `111001` give `r >= 10*length(v)+71`. The generic `Rule30ForbiddenSuffix` criterion needs only a vacuum-free full-set image of the suffix. These are partial exclusions, not a solution of Problem 1. Proof and formalization by OpenAI Codex through `Troyusrex2`, using the existing white-pulse reduction. | `no_padding_suffix011_leftFinite`, `no_padding_suffix001001_leftFinite`, `no_padding_suffix111001_leftFinite`, `no_padding_suffix011_seed` |
| `Rule30FiveTail` | 2026-10-24 | No column of a configuration with a leftmost black cell eventually repeats `0^r u` when `r >= 69` and `u` has at most five bits; in particular every nonzero finite start and the single seed. The stronger `r >= 49` bound remains for at most four tail bits (`Rule30ShortTail`). Includes an arbitrary-tail white-pulse reduction and finite vacuum/endpoint criteria; certificate existence for every tail is not proved. Proof and formalization by OpenAI Codex, building on the catalog's uniform masked Jen theorem. Large data is in `Rule30Certificates`. | `no_five_tail_leftFinite`, `no_five_tail_finite`, `no_five_tail_seed` |
| `Rule30WhiteRunEight` | 2026-10-17 | The words `0^r 1 1` with `r ≥ 8` are excluded, for every transient: `Rule30BlackRuns.no_white_run_11` needs `r ≥ 10`. Proved on 2026-10-15 by the verifier of the white-run exclusion and left out of the catalog; ported here. | `no_white_run_11_ge8` |
| `Rule30PeriodTwoSideways` | 2026-10-17 | The coupled question `CQ01` in two more forms. It holds iff no configuration with finitely many black cells has center column `1, 0, 1, 0, …` from time 0. Sideways: for every finite right half `R`, one explicit left row `Psi R` (the constrained start whose free bits complement column 1 of the driven right half) has infinitely many black cells; this holds for `R` whenever it holds for the right half two steps later, or whenever column 1 of the driven right half is eventually periodic at the white steps. Exact death: a left row keeps the center alternating exactly until the first depth where it differs from `Psi R`. States the `R = ∅` milestone `CQ01Empty` (**open**). Barrier: from finite configurations the center alternates arbitrarily long, so no ranking through a finite abstraction of configurations decreases at every double step over which the center flips twice. | `CQ01_iff_no_finite_alternating`, `Q01_no_leftfinite_alternating`, `CQ01_iff_Psi`, `not_finSupp_Psi_of_R2`, `exact_death_center`, `truncation_death`, `CQ01Empty_iff`, `no_finite_abstract_ranking_coupled` |
| `Rule30FiniteConfigs` | 2026-10-17 | The single-seed theorems in their uniform form. For every configuration with a leftmost black cell (nonzero and left-finite): Jen's theorem (at most one column is eventually periodic) and period 1 (no column is eventually constant); the proofs use the seed only through its left edge. For nonzero finite configurations: `CQ01` holds iff none has an eventually 2-periodic center column, whatever the transient, so `CQ01` is exactly FinConf at period 2 for one column. `Q01` gives the same for every configuration with a leftmost black cell. | `jen`, `no_column_eventually_constant`, `jen_finite`, `no_column_eventually_constant_finite`, `CQ01_iff_no_finite_period_two`, `no_leftFinite_period_two_of_Q01` |
| `Rule30FiniteMaskedJen` | 2026-10-17 | The masked and window forms of Jen's theorem (`Rule30MaskedJen`) for every configuration with a leftmost black cell: if column `i` is eventually periodic, column `i + 1` is not periodic with the same period on the white times of column `i`, and `column i ∨ column (i + 1)` is not eventually periodic; with no periodicity assumed, two times never carry the same (column, or-column) window reaching the left edge; a periodic column has, in every window `[n, n + m)` with `n` past the transient and `m = n + i - lo`, a white time where the next column breaks the period. | `masked_jen`, `orCol_not_eventuallyPeriodic`, `window_jen_col`, `periodic_window` |
| `Rule30FiniteBlackRuns` | 2026-10-17 | The black-run exclusions of `Rule30BlackRuns`, for every configuration with a leftmost black cell and every column `i`. The nine-black shield holds in the evolution of every configuration; the exclusions then use the seed only through Jen's theorem and its masked form. If from some time on every black run of column `i` that is followed by white has length at least `9`, column `i` is not eventually periodic. If column `i` has period `P`, no period contains a black run of length `r` with `9 ⌈(P - r + 9) / 2⌉ ≤ r` (Theorem B), or a black run of length `≥ 9` followed by a long white run (Theorem D). The same for every nonzero finite configuration. | `nine_black`, `black_shield`, `not_eventuallyPeriodic_of_long_one_runs`, `no_long_black_run`, `no_black_white_run`, `not_eventuallyPeriodic_of_long_one_runs_finite` |
| `Rule30FiniteBlackRunBlocks` | 2026-10-17 | Theorem B′ of `Rule30BlackRunBlocks`, for every configuration with a leftmost black cell and every column `i`. If the finite check `Determined u j0` holds, column `i` is not eventually periodic with repeating word `1^r u` for any `r ≥ max 9 (9 j0)`, whatever the transient. The proof uses the seed only through Jen's theorem; the nine-black shield and the trace of the next column hold in every evolution. The kernel-checked blocks of `Rule30BlackRunBlocks` (`det_0`, …, `det_0110`) apply unchanged, for example `1^r 0` with `r ≥ 18`. The same for every nonzero finite configuration. | `no_black_run_block`, `no_period_black_run_then_white`, `no_black_run_block_finite`, `traceCol1_rowAt` |
| `Rule30FiniteDiagonals` | 2026-10-17 | The periodic diagonals of `Rule30Diagonals`, for every configuration with an edge. If `x` is white right of `hi`, the diagonal `t ↦ evol x t (hi + t - j)` is periodic from time 0 with period dividing `2^j`. If `x` is white left of `lo`, the diagonal `t ↦ evol x t (lo - t + j)` is eventually periodic with period `2^j`. Every column reads its array of diagonals along a line of slope one, as the center column of the seed does. So the periodic right diagonals behind the 2-adic odometer are not special to the seed. The bitwise form, for every starting value of `Φ(x) = x ⊕ (2x ∨ 4x)`, is `Rule30Equivalents.TFunction`. | `Rd_periodic`, `Ld_periodic`, `evol_eq_Rd`, `column_reads_periodic_rows` |
| `Rule30FiniteWhiteRuns` | 2026-10-17 | The exclusion of `Rule30WhiteRunEight` for every column of every nonzero finite configuration: no column is eventually `0^r 1 1` repeated, `r ≥ 8`, whatever the transient. The lemmas of `Rule30BlackRuns` (the first black cell right of the column moves left during a white run, and the period-start classes) hold for column `0` of any evolution; the seed's right edge becomes any black cell right of the column, which every nonzero finite configuration has from some time on; translation gives every column. | `no_white_run_11_col0`, `no_white_run_11_finite`, `evol_right_edge`, `exists_rightmost` |
| `Rule30Coupled` | 2026-10-17 | Every period, as coupled questions. In any configuration the two halves evolve as the halves driven by the center column, and the center is updated from its two driven neighbours; conversely, two driven halves glued to a column satisfying that update give a configuration with that center. `CQ ω` (**open** for every nonconstant periodic `ω`): no finite left half and finite right half are coupled to `ω`; it holds iff no finite configuration has center column `ω`. FinConf for one column is exactly the family `CQ ω` over all periodic `ω` with a black cell, and the family implies Problem 1. For the alternating column, `CQ` is `CQ01`. | `left_eq_L`, `right_eq_drv`, `evol_glue`, `CQ_iff_no_finite_config`, `CQ_altCol_iff_CQ01`, `finConf_center_iff`, `problem1_of_CQ` |
| `Rule30CoupledGerms` | 2026-10-26 | For an arbitrary driven RIGHT half, if the driver avoids adjacent black cells and the three-cell germ vanishes at every late fall, a subsequent black driver cell anchors exact transport to the complemented one-tick-delayed nearest-RIGHT trace. No periodicity or support premise is needed for this transport. For an eventually periodic, eventually no11 driver with arbitrarily late black cells, coupling and Jen rigidity force nonzero germs at arbitrarily late falls if the LEFT has a finite positive edge, or both halves are finite, including initially empty LEFT. Contributed by @Elijah08-GIT with OpenAI Codex. | `right_root_gamma_transport`, `coupled_gamma_cofinal_of_left_edge`, `coupled_finite_gamma_cofinal` |
| `Rule30LightCone` | 2026-10-17 | The locality behind space-efficient evaluation. A cell at time `t` depends only on the initial cells within distance `t`. With space blocks and time steps of width `b`, each block is a fixed function of the three blocks around it one time step earlier, so the center cell at time `m b` is the root of a fan-in-3 tree of `b`-bit blocks with height `m`. This is the shape that Williams's square-root-space simulation passes to Cook–Mertz tree evaluation, about `√n · log n` bits for the center cell at time `n`; neither algorithm is formalized. | `evol_window`, `block_step`, `center_eq_root` |
| `Rule30ZeroBoundaryStripeFour` | 2026-10-23 | Stripe prefixes with four and five tail cells. For every `m` and every tail `v` of four cells (`row4 m v`), the start `S[1..m] · v · 0^∞` first deviates from the stripe at some depth `d ≤ m + 6`, and depth `1` turns white at an even time `≤ d - 1 + 31`; every class `(m mod 2, v)` is covered except `v = 13` with `m` odd (`stripe_four_tail`). For every `m` and every tail `v` of five cells (`row5 m v`), the first deviation has depth `d ≤ m + 7` and depth `1` turns white at an even time `≤ d - 1 + 31` for every class except `v = 13` with `m` odd and `v = 27` with `m` even (`stripe_five_tail`), citing `Rule30ZeroBoundaryStripe.first_defect_hits` for odd-depth first deviations and eight width-32 cycles (`cyc5_17`–`cyc5_31`) in `Rule30Certificates/ZeroBoundaryStripeCycles3`. Four-cell family contributed by Ying Yin with Codex (GPT-6) (`R30-20261020-81df0e`) and ported to core Lean; five-cell family contributed by G.P.J.W. Quint and Gemini (Google) ([R30-20261024-f177ae](https://www.wolframcloud.com/obj/rule-30-prize/Agents/status/R30-20261024-f177ae), [R30-20261025-017d83](https://www.wolframcloud.com/obj/rule-30-prize/Agents/status/R30-20261025-017d83)). | `Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront.stripe_four_tail`, `Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront.family4_of_class`, `Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront.stripe_five_tail`, `Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront.family5_of_class` |
| `Rule30ZeroBoundaryStripeFrontLift` | 2026-10-24 | Front-window projection, universal return periods, parallel simulation and sparse return-map soundness. Contributed by Troy Lowry with OpenAI Codex. | `universal_front_period`, `initial_run_correct`, `return_map_cycle_lift` |
| `Rule30Certificates/StripeTail13Completion` | 2026-10-24 | The punctured width-34 cycle and 32-state parallel upper return certificate for tail 13. The lower cycle is by G.P.J.W. Quint and Gemini ([R30-20261024-f177ae](https://www.wolframcloud.com/obj/rule-30-prize/Agents/status/R30-20261024-f177ae)); the parallel completion is by Troy Lowry with OpenAI Codex. | `Ruliology.CellularAutomata.Rule30Tail13Completion.cyc13_period`, `Ruliology.CellularAutomata.Rule30Tail13Completion.cyc13_sig`, `Ruliology.CellularAutomata.Rule30Tail13Completion.run_full`, `Ruliology.CellularAutomata.Rule30Tail13Completion.return_cycle`, `Ruliology.CellularAutomata.Rule30Tail13Completion.rare_table` |
| `Rule30ZeroBoundaryStripeFourComplete` | 2026-10-24 | Completes the four-bit and five-bit stripe-tail families, including every odd prefix with tail 13 and every even prefix with five-bit tail 27, with a white witness by 45 steps after arrival. The `(13, 0)` completion is contributed by Troy Lowry with OpenAI Codex, using Ying Yin and Codex's catalog stripe-front method and the Quint/Gemini lower cycle; the five-cell completion on `cycle13_complete` is by G.P.J.W. Quint and Gemini ([R30-20261025-017d83](https://www.wolframcloud.com/obj/rule-30-prize/Agents/status/R30-20261025-017d83)). | `row4_13_all_odd`, `stripe_four_tail_complete`, `row5_13_all_odd`, `row5_27_all_even`, `stripe_five_tail_complete` |
| `Rule30WhiteEnd` | 2026-10-23 | The white end. For every `q ≥ 10`, no column of rule 30 is eventually the repeating word `1 0^q`, whatever the transient: for the single seed, `EventuallyWord (true :: List.replicate q false)` is false, and the same holds for every column of every configuration with a leftmost black cell, every finite nonzero one included. `Rule30StripCertificateTable` excludes only `q = 10, 11, 12`. A one-sided strip relaxation (eight cells right of the column, an arbitrary cell beyond) determines column `c + 1` after three periods; kernel checks cover `q = 10 … 25`, and the relaxation's white step satisfies `W^26 = W^22` on the sets that occur, which covers every `q ≥ 26`. Two adjacent columns periodic for ever then contradict Jen's theorem with a clock. The checks are in `Rule30Certificates/WhiteEndChecks`, where `control_q9` shows that the check fails at `q = 9`. Contributed by Gareth Herbert with Claude and GPT as Rule 30 Prize submission `R30-20261022-c27323`, and ported to core Lean. | `not_eventuallyWord_white_end`, `white_end_seed`, `white_end`, `white_end_finite` |
| `Rule30WhiteEndNine` | 2026-10-26 | The white end from `q = 9`, by one pumped mode certificate. For every `q ≥ 9`, the single-seed center column is not eventually the repeating word `1 0^q`, whatever the transient; `Rule30WhiteEnd` is not used. A *mode certificate* (`not_eventually_word_mode`, sound for every word, width, warm-up and label phase) lets column `1` carry one free bit per period at one white phase, the *label*, and checks two transition rules on the labels (after `1` comes `0`; after `0 0` comes `0`); the labels are then eventually 2-periodic and masked Jen gives the contradiction. For `1 0^q` the certificate is one formula in `q`: twelve cells, five warm-up periods, label phase `2`, the reachable set and two fixed label masks. Sets closed under white steps, checked once, cover every period of every `1 0^q` with `q ≥ 10` (`modeCert_pumped`, `pumpCheck_12`); at `q = 9`, where the label `1` occurs, the kernel evaluates the same formula (`modeCert_nine`), and `pumpCheck_12_nine` shows that the same pumped check fails from nine white steps. Set images are computed bit-parallel (`fimage`, proved sound), so the module builds in a few seconds. Contributed by AIOvernight with Claude (Anthropic) as Rule 30 Prize submission `R30-20261026-c389d5`. | `not_eventually_white_end_ge9`, `modeCert_white_end`, `modeCert_pumped`, `not_eventually_word_mode` |
| `Rule30Problem3` | 2026-10-24 | Prize Problem 3 on a one-tape Turing machine that reads the binary digits of `n`: the prize's formal statement (no machine computes `c(n)` in time `O(n)`), the verbal one (none in time `o(n)`) and the version that does not depend on the model (none in time `n^o(1)`), each implying the next. | `Problem3`, `Problem3Verbal`, `Problem3Robust`, `problem3Verbal_of_problem3`, `problem3Robust_of_problem3Verbal` |
| `Rule30WhitePad10111` | 2026-10-24 | No eventual repetition of `0^q 10111` for `q ≥ 9` in the single-seed center, using eight-cell reachable-set envelopes and masked Jen. Strengthens the tail-specific `q ≥ 62` bound in [Troy Lowry's pull request #1](https://github.com/WolframInstitute/Rule30PrizeKit/pull/1). Contributed by AIOvernight with OpenAI Codex as Rule 30 Prize submission `R30-20261023-7a9ed3`. | `not_eventually_zeros_10111` |
| `Rule30ColumnSeparation` | 2026-10-24 | Every pair of distinct spatial columns p, q of the single-seed pattern differs by time `max(abs(p),abs(q))+18`. Mirror columns -m, m differ by time m+18 for every m>0, using certified 20-bit edge cycles and all 256 phases. This is injectivity of complete traces starting at time zero; it does not exclude eventual equality or prove temporal nonperiodicity. Contributed by Troy Lowry with OpenAI Codex as Rule 30 Prize submission `R30-20261024-ad6cac`. | `mirror_columns_distinguishable`, `columns_distinguishable`, `columns_injective` |
| `Rule30TraceEdge` | 2026-10-24 | Conditional global reduction: the **open** hypothesis `EdgeObservable` (equal infinite traces of finite rows imply equal left edges) implies nonperiodicity for every nonzero finite start and the exact official Problem 1. The hypothesis is not proved. Also proves edge recovery when both edges are nonnegative. Contributed by Troy Lowry with OpenAI Codex. | `no_eventuallyPeriodic_of_edgeObservable`, `problem1_of_edgeObservable`, `edges_equal_of_nonnegative` |
| `Rule30TraceMerge` | 2026-10-24 | Exact obstruction to stronger left reconstruction after dropping initial right finiteness: two rows with edge -3 and different initial cells at -1 have identical entire center traces, merge after one step, and become finite after two. Both initial rows are infinite; their edges agree. Also proves that edge recovery for eventually finite rows is equivalent to the open finite-row hypothesis. Contributed by Troy Lowry with OpenAI Codex. | `no_left_recovery_from_eventual_finiteness`, `eventual_finite_edge_iff` |
| `Rule30TraceAmbiguity` | 2026-10-24 | For every horizon H, two finite initial rows with edge -3 and different initial cells at -1 agree on the first H center observations. Thus no horizon depending only on left depth recovers the initial left half when right support is unbounded. In contrast, four observations recover the left neighbor at depth two, for arbitrary right halves. This does not refute finite-row recovery from an entire infinite trace or edge recovery. Contributed by Troy Lowry with OpenAI Codex. | `arbitrarily_long_finite_left_ambiguity`, `no_uniform_finite_left_recovery`, `recover_left_neighbor_at_depth_two`, `left_neighbor_rigid_at_depth_two` |
| `Rule30SpacingRenormalization` | 2026-10-24 | Exact eight-column reconstruction identity under gate spacing at least three, with finite-support transfer. The spacing survives its transform exactly when the original gate is white at every index at least four; a period-five gate disproves unconditional iteration at depth seventeen. Does not exclude period two. Contributed by Troy Lowry with OpenAI Codex, following the one-step identity in [morpholib Theorem 14](https://github.com/fractastical/morpholib/blob/main/docs/RULE30_PRIZE_SUBMISSION.md). | `reconstruction_translate`, `finite_transfer`, `transform_spaced_iff`, `second_translation_fails` |
| `Rule30PackedReconstruction` | 2026-10-24 | A finite packed temporal-column computation agrees with the scalar sideways reconstruction inside its represented light cone. Contributed by Troy Lowry with OpenAI Codex. | `packed_sound` |
| `Rule30SpacingGapCounterexample` | 2026-10-24 | A period-31 gate has successive black spacings only three or five, yet its reconstructed initial row is white at all depths 528 through 544. Rules out extrapolating a sixteen-cell white-gap bound to all depths; makes no finite-right realizability claim. Contributed by Troy Lowry with OpenAI Codex. | `gate31_gaps`, `gate31_spaced`, `seventeen_white`, `no_uniform_gap_bound_sixteen` |
| `Rule30DrivenPrefix` | 2026-10-24 | Packed spatial rows of the alternating-driven right half, with exact bit soundness, prefix dependence and finite gate-window observations. Contributed by Troy Lowry with OpenAI Codex. | `packed_sound`, `double_prefix`, `iterate_mod_bit` |
| `Rule30ExactReturn` | 2026-10-24 | The full eight-column return holds exactly under spacing with only the initial distance-two pair exempted. For a spaced gate, this condition survives transformation exactly when the gate is white from index five onward; arbitrarily late black observations block a second return. Includes the sharp boundary example. Contributed by Troy Lowry with OpenAI Codex. | `translation_iff_nearSpaced`, `transformed_exactReturn_iff`, `infinite_gate_fails_arbitrarily_late`, `lastAllowed_transformed_return` |
| `Rule30ControlledResponse` | 2026-10-24 | Exact equivalence between responses to every left-boundary input and head/OR observations of the triangular diagonal map. Terminal rewrites `011 -> 01` and `101 -> 11` preserve these responses behind any common prefix and preserve the full Rule 30 center trace with any common initial left half. Includes explicit limits of short-window and fixed-driver tests. Normal-form completeness is not claimed. Contributed by Troy Lowry with OpenAI Codex. | `sameResponse_iff_diagonal`, `tail_011_drv`, `tail_101_drv`, `feedback_left_equal`, `tail_011_center`, `tail_101_center` |
| `Rule30PeriodicProfileCounter` | 2026-10-24 | Three explicit infinite-tail diagonal orbits of period eight: equal nonconstant head OR does not recover the head, and a period-two head need not detect the full period. All starts are proved to have infinite support. No finite-support conjecture is refuted. Contributed by Troy Lowry with OpenAI Codex. | `same_OR`, `OR_nonconstant`, `heads_differ`, `full_period_eight`, `loss_head_period_two`, `loss_full_period_lower_bound`, `loss_infinite` |
| `Rule30FeedbackErasure` | 2026-10-24 | Two distinct finite, nonzero configurations have identical complete center and right-head traces, both non-eventually-constant, while their initial right halves are not universally response equivalent. A white initial center erases that distinction in one step. Their left edges agree, and no eventual period is excluded. Contributed by Troy Lowry with OpenAI Codex. | `white_step_erases_distinction`, `same_left_forever`, `finite_feedback_counterexample` |
| `Rule30ClockMask` | 2026-10-24 | A local clock onset cannot be hidden by a shorter-period head OR: with an even half-clock H, one color-reversing column, its next two H-periodic neighbors, and an explicit 2H clock on the preceding column, the OR and one more predecessor cannot have period H. Arbitrary-prefix propagation and finite-tail period nonloss remain open. Contributed by Troy Lowry with OpenAI Codex. | `no_constant_OR_at_onset`, `OR_not_half_period`, `predecessor_not_half_period`, `orbit_onset_not_constant_OR` |
| `Rule30FiniteClockCertificate` | 2026-10-24 | Generic soundness of finite temporal-profile pools: checked left-extension closure covers every finite spatial width, and a checked detection condition propagates a head clock to every column. Includes arbitrary transient removal and actual triangular-orbit specialization. No arbitrary-clock induction or center-period exclusion. Contributed by Troy Lowry with OpenAI Codex. | `covers_finite_family`, `finite_family_clock_detected`, `finite_state_eventual_clock_detected` |
| `Rule30FiniteClockSixteen` | 2026-10-24 | A checked 68-node certificate proves that any eventual head period of a finite triangular orbit whose full clock divides sixteen is a period of the whole state. Spatial width and transient are unbounded. The full-clock bound is explicit and no center-column period is excluded. Contributed by Troy Lowry with OpenAI Codex. | `pool16_checked`, `detection16_all_head_clocks`, `eventual_period_detected`, `period_loss_requires_infinite_tail` |
| `Rule30TerminalClock` | 2026-10-24 | The known terminal response rewrites preserve every equality between full triangular orbit states, behind every shared finite prefix and at all times. In particular they preserve every full-state return time, with no temporal-clock bound. An indexed correspondence intertwines the full update and has inverse maps on linked states. Completeness of the rewrites and arbitrary head-clock detection remain open. Contributed by Troy Lowry with OpenAI Codex. | `linked_diagonal`, `iterate_equal_iff`, `tail_011_return_iff`, `tail_101_return_iff`, `rewrite_return_iff` |
| `Rule30CenterRuns` | 2026-10-24 | Runs of the center column are at most linear in time. A block of `L` consecutive cells of one color starting at time `a ≥ 1` (not necessarily maximal) has `L ≤ a` if black, attained at `a = 3`, and `L ≤ a - 1` if white, attained only at `a = 2`; for `a ≥ 3` a white block has `L ≤ a - 3`, not attained up to time 3000. So every window `[a, 2a]` holds a white cell and every window `[a, 2a)` a black cell (`[a, 2a - 2)` for `a ≥ 3`), and the counts grow at least logarithmically: `m + 1` black cells before `2^m`, so `Nat.log2 n ≤ blackCount n`, and `m` white cells before `4^m`. The black bound holds for every column of every configuration with a leftmost black cell, measured from the time the left edge passed the column. Black runs: left-permutivity forces the alternating row `… 0 1 0 1` under the run, which cannot cover the two adjacent leftmost black cells. White runs: the first black cell right of the center (`Rule30BlackRuns.front_moves`) fixes column `1`, which forces the row at the start of the run in closed form; it contradicts the left-edge diagonals `D 1`, …, `D 4` of `Rule30Diagonals`. Contributed by Luis Perez Morales, Claude (Fable 5.1), as Rule 30 Prize submission `R30-20261024-03b551` (superseding `R30-20261024-801153`, whose bounds were `L ≤ 3a - 2` for white runs and a black cell in every `[a, 4a)`), and ported to core Lean. | `black_run_le`, `white_run_le'`, `white_run_le_three`, `exists_white`, `exists_black'`, `exists_black_three`, `blackCount_pow_two`, `log_two_succ_le_blackCount`, `log_two_le_blackCount`, `whiteCount_pow_four`, `log_le_whiteCount`, `black_run_le_evol` |
| `Rule30EtherThreeErosion` | 2026-10-24 | The period-3 ether erodes, so it has no wall of any width. Erosion: let a rule-30 evolution of the columns `p ≥ 1` have column `0` driven by the 12 × 3 ether. If at some time the columns `1..k` carry the ether, the columns beyond `k + w` carry the ether, and some column does not, then within `3 w + 6` steps one of the columns `1..k` leaves the ether. No wall: for every attachment column `a` and every width `b ≥ 1`, `WallOK a b W` forces `W` empty. This extends `no_wall_le_12` of `Rule30EtherThreeNoWall` to every width, so `absorption3_excludes` is vacuous and the ether-and-wall route to least period 3 is closed. `AbsorptionT t001`, `Q001`, `C3s001` and `C3w(011)` do not involve walls and stay open. The leftmost defect (the front) has 24 states (class of its column mod 12, and whether the next column is a defect). A kernel check of 576 local patterns (`cert_all`, `decide +kernel`) shows one bad state, which alone can jump right by 3 or more and re-enters itself only by jumping at least 8. On the other 23 states a potential `ψ ≤ 10` makes `5 D + 2 t + ψ` non-increasing (`front_step`, `wake_good`). The rightmost defect moves right by exactly one per step (`redge_step`, left-permutivity), which bounds the run of bad steps (`run_bad`). A wall state plus one flipped cell then contradicts `trap_invariant3`. Contributed by Luis Perez Morales, Claude (Fable 5.1), as Rule 30 Prize submission `R30-20261024-1fc962`, and ported to core Lean. | `erosion3_fin`, `no_wall`, `wake_good`, `front_step`, `run_bad`, `cert_all`, `redge_step` |
| `Rule30WhiteTailErosion` | 2026-10-24 | Extends the preceding ether-erosion argument from finite ether perturbations to a white right tail. A speed-one bound on a defect witness replaces the rightmost defect. If column zero is driven by the period-three ether and the right half is white beyond W at time T, every prefix 1..k departs from the matching ether by T + 3 max(W + 12 - k, 0) + 6. Column one departs arbitrarily late. No width bound, no temporal-clock bound, and no center-period exclusion. Contributed by Troy Lowry with OpenAI Codex, building on Luis Perez Morales and Claude's front certificate and potential. | `run_bad_bounded`, `erosion_bounded`, `white_tail_evol`, `white_tail_defect`, `white_tail_erosion`, `white_tail_often_departs` |
| `Rule30XorRigidity` | 2026-10-24 | For any two ordinary Rule 30 histories on all integer sites, their pointwise XOR follows Rule 30 exactly when one history is zero or both are identical. No support or periodicity assumption; a nonzero history has precisely two XOR partners. The one-step identity also appears in [Dibujaron's notes](https://github.com/Dibujaron/rule30); compare Coven–Hedlund–Rhodes (1979) on commuting maps. Contributed by AIOvernight with OpenAI Codex as Rule 30 Prize submission `R30-20261024-ddbfbd`. | `xor_history_iff`, `standard_two_partners` |
| `Rule30StripeMeeting`, `Rule30Certificates.StripeMeeting` | 2026-10-24 | For arbitrary finite integer rows and every center index, a common stripe-prefix cut with a white separator preserves the entire center trace. The relation is preserved after two steps. If two rows become stripe-related at any finite time while their preceding center observations agree, they were related at time zero or one. A 2321-state kernel certificate is connected to arbitrary row sizes and the exact stripe grammar. Completeness for equal infinite traces, numerical-normalizer equivalence, and Problem 1 remain open. Contributed by Troy Lowry with OpenAI Codex. | `stripe_related_same_trace`, `stripe_related_preserves_two`, `stripe_meeting_is_early`, `no_delayed_stripe_meeting`, `eventually_stripe_iff_early` |
| `Rule30PaddedWords` | 2026-10-24 | One bound for each short tail. The center column of the single seed is not eventually `0^r u` for a tail `u` of at most six cells once `r ≥ paddedBound u`, the least bound the catalog proves: 8 for `11`, 9 for `10111`, 9 for `1`, and 49, 69 or 74 for any other tail of at most four, five or six cells. A better bound for a tail, or longer tails, is a change to this module. | `no_padded_word`, `not_eventuallyWord_zeros_11`, `not_eventuallyWord_zeros_one` |

## Certificate data

Some theorems rest on finite checks that the kernel evaluates with `decide`. Their data is in the modules under `Rule30Certificates/`:

| Data | For | What it checks |
|---|---|---|
| `ZeroBoundaryWidth52Chunks0`–`3` | `Rule30ZeroBoundaryWidth52` | Q01 for every start of width at most 52 |
| `EtherTrap0`–`5` | `Rule30EtherTrapWidth20` | that the pure ether lies in no trap of width at most 20 |
| `ZeroBoundaryStripeCycles0`–`3` | `Rule30ZeroBoundaryStripeFamily`, `Rule30ZeroBoundaryStripeFour` | the periodic front-window orbits of the stripe prefixes |
| `StripeTail13Completion` | `Rule30ZeroBoundaryStripeFourComplete` | a punctured lower cycle and parallel return map complete the omitted tail-13 family |
| `WhiteEndChecks` | `Rule30WhiteEnd` | the strip relaxation of `1 0^q` for `q = 10 … 25` |
| `WhitePaddingFamilies`, `FiveTailTube`, `SixTailBackward`, `SixTailEndpoints` | `Rule30ShortTail`, `Rule30FiveTail`, `Rule30SixTail`, `Rule30SixTailSharpened`, `Rule30SuffixFamilies` | the pumping, vacuum-avoidance and backward-tube certificates of the tails of at most six cells |
| `StripeMeeting` | `Rule30StripeMeeting` | a transducer of 2321 states for stripe relations |

The catalog takes certificate data only as a step in a theorem about an infinite family: all words of a shape, all widths, all phases, every configuration with a leftmost black cell. A list of words, widths, windows or depths for its own sake is not taken; it stays on the submissions site. A contribution uses an existing checker where one fits (the rank certificates of `Rule30StripCertificates`, the strips of `Rule30FiniteStrips`, the backward tubes of `Rule30BackwardTube`); a new checker comes with its soundness theorem and generalizes or replaces one. Its data goes in one module per family, which builds in under a minute and 4 GB; the heavier modules above are listed with their cost under [Building](#building). For padded words `0^r u`, a lower bound or a longer tail is a change to `Rule30PaddedWords`, not a new module.

## Which modules predate the attempt

The birth times of the catalog files (`stat -f %B`) and the docstrings agree. The *Added* column of the tables below uses these labels.

| Added | When | Modules |
|---|---|---|
| `10-10` | 2026-10-10 | Five catalog entries from Wolfram's writings, written before the attempt: `Rule30Predecessors`, `Rule30PredecessorCounts`, `BusyBeaverLifetimes`, `Rule30Blocks`, `Rule30Jen`. Their docstrings cite only Wolfram and the literature. |
| `start` | 2026-10-15, 04:07–04:16 | The first Rule 30 Prize modules, written before the multi-agent rounds: `Rule30Prize`, `Rule30Diagonals`, `Rule30Window`. Their docstrings do not cite the multi-agent project. |
| `R1`, `R2`, `final` | 2026-10-15, 07:18, 09:40, 11:49 | The other 46 modules: round 1 (11), round 2 (7) and the final batch (28, including the 13 in `Rule30Certificates/`). Their docstrings cite the Rule 30 Prize project (2026). |

## Modules by topic

All modules live in `Ruliology/CellularAutomata/`. Theorems live in the namespace `Ruliology.CellularAutomata.<Module>`, with these exceptions:

- `Rule30Predecessors` and `Rule30PredecessorCounts` use `…Rule30`.
- The six `Rule30EtherThree*` modules of the snapshot share `…Rule30EtherThree`; `Rule30EtherThreeErosion` uses its own.
- `Rule30EtherTrapWidth20` uses `…Rule30EtherTrap`.
- `Rule30ZeroBoundaryStripeFamily` and `Rule30ZeroBoundaryStripeFour` use `…Rule30ZeroBoundaryStripeFront`.
- The data modules in `Rule30Certificates/` use namespaces inside the module they serve, for example `…Rule30ZeroBoundaryWidth52.C0`.

"Open" marks a statement defined as a `Prop` but not proved.

### Period 1

| Module | Added | What it proves | Headline theorems |
|---|---|---|---|
| `Rule30Prize` | start | States Problems 1 and 2 as in formal-conjectures' `Other/Rule30.lean`. No column is eventually constant, so period 1 is excluded for every column and every transient. | `Problem1`, `Problem2`, `no_column_eventually_constant`, `center_not_eventually_period_one` |

### Windows

| Module | Added | What it proves | Headline theorems |
|---|---|---|---|
| `Rule30Window` | start | From the first 16,384 center bits, computed in the kernel: there is no eventual period P ≤ 4096 with transient ≤ 8192. | `no_small_eventual_period` |
| `Rule30FactorWindow` | R1 | Any eventual period P from time T has T + P ≥ 16359, because the first 16,384 bits have 16,359 distinct factors of length 26. | `transient_add_period_ge` |

### Black runs and strip certificates

| Module | Added | What it proves | Headline theorems |
|---|---|---|---|
| `Rule30BlackRuns` | R1 | Nine black cells in a column shield the right half (Lemma A). Long black runs exclude many periods (Theorems B and D). | `nine_black`, `black_shield`, `no_long_black_run`, `no_black_white_run`, `not_eventually_zero_ones`, `no_white_run_11` |
| `Rule30BlackRunBlocks` | R1 | Theorem B′: excludes repeating words `1^r u` for eight kernel-checked blocks `u`, provided the black run is long: `r ≥ 18` for `u = 0, 00, 000, 0000, 0100`, and `r ≥ 27` for `u = 010, 0010, 0110`. Short runs, such as the open words `10`, `100` and `1110`, are not covered. | `no_black_run_block`, `no_period_black_run_then_white` |
| `Rule30StripCertificates` | R1 | Problem 1 holds iff no word is an eventual tail. Bitmask and rank strip certificates are sound via masked Jen; three words are excluded. | `problem1_iff_no_word`, `not_eventually_word_strip`, `Cert.sound`, `not_eventually_00000011`, `not_eventually_000000000101` |
| `Rule30StripCertificateTable` | R1 | Kernel-checked certificates exclude 30 periodic words of length 8–13. | `not_eventually_certTable` |

### Jen and masked Jen

| Module | Added | What it proves | Headline theorems |
|---|---|---|---|
| `Rule30Jen` | 10-10 | Jen (1986): no two columns are both eventually periodic. | `jen`, `periodic_column_unique`, `not_adjacent` |
| `Rule30MaskedJen` | R1 | Masked, effective-boundary and window forms of Jen's theorem. | `masked_jen`, `orCol_not_eventuallyPeriodic`, `effective_step`, `window_jen`, `finitary_jen` |
| `Rule30DrivenLeft` | R1 | Jen's theorem for the left half driven by a boundary column: from a finite nonzero start, an eventually periodic driver makes no left column eventually periodic. A barrier: for a start whose leftmost black cell is at −n, column −1 can follow any target for the first n − 1 steps. | `no_periodic_column`, `barrier_exists`, `barrier_unique` |
| `Rule30WhiteSeed` | R1 | Of the center columns from a single black cell and from a single white cell, at least one is not eventually periodic. The same holds for rules 30 and 135. | `problem1_black_or_white`, `problem1_30_or_135` |

### Diagonals

| Module | Added | What it proves | Headline theorems |
|---|---|---|---|
| `Rule30Diagonals` | start | Right diagonals have period 2^j from the start, and left diagonals are eventually 2^j-periodic. | `R_periodic`, `D_periodic`, `center_eq_parity` |
| `Rule30RightPeriods` | R1 | Right-diagonal periods: the doubling rule, upper and lower bounds, rows at powers of two, restarts. | `e_step`, `per_bound`, `per_upper`, `rows_at_powers_of_two`, `not_half_lower` |

### Zero-boundary left half and period 2

| Module | Added | What it proves | Headline theorems |
|---|---|---|---|
| `Rule30PeriodTwo` | R1 | What an eventual period 2 forces. `Q01` (zero-driven left half; **open**) implies no eventual period 2. | `normalize`, `golden`, `not_eventually_period_two_of_Q01`, `stripe_fixed` |
| `Rule30ZeroBoundary` | R2 | The zero-boundary left half (ZBL): dynamics, realization, free bits, equivalent forms of `Q01`, Jen inside the ZBL. | `Q01_iff_Theta`, `Q01_iff_bounded`, `Q01_iff_staged`, `count_constrained`, `jen_clock`, `free_bits_no00_no11111` |
| `Rule30ZeroBoundaryStripe` | R2 | ZBL epochs, stripe stability and stripe absorption. | `stripe_absorb`, `Theta_eventually_stripe_iff`, `first_defect_phase` |
| `Rule30ZeroBoundarySmall` | R2 | `Q01` holds for every start of width ≤ 16 (kernel-checked search). | `q01_width_le_16`, `q01_width_le_15_odd` |
| `Rule30ZeroBoundaryLanes` | final | A bit-sliced `Q01` checker that runs in the kernel, with its soundness proof. | `q01_of_checks`, `q01_of_chunks` |
| `Rule30ZeroBoundaryWidth52` | final | `Q01` holds for every start of width ≤ 52: depth 1 turns white at an even time ≤ 96. | `q01_width_le_52`, `q01_width_le_52_linear`, `not_inX_of_width_le_52` |
| `Rule30Certificates/ZeroBoundaryWidth52Chunks0`–`3` | final | Data: the 256 chunk checks behind width 52, 64 per file (namespaces `Rule30ZeroBoundaryWidth52.C0`–`C15`). | — |
| `Rule30ZeroBoundaryStripeFront` | final | The front window of a stripe prefix evolves on its own; checked periodic orbits bound its death time. | `front_sound`, `family_of_class` |
| `Rule30ZeroBoundaryStripeFamily` | final | Every stripe prefix `S[1..m] · v · 0^∞` with \|v\| ≤ 3 dies within 31 steps of arrival. | `stripe_prefix_family`, `stripe_prefix_family_list` |
| `Rule30Certificates/ZeroBoundaryStripeCycles0`–`2` | final | Data: the eight window cycles behind the stripe-prefix family. | — |
| `Rule30PeriodTwoCoupled` | R2 | The coupled question `CQ01` (**open**): `Q01` implies `CQ01`, and `CQ01` excludes period 2. The ether is an infinite witness. | `CQ01_of_Q01`, `no_eventual_period_two_of_CQ01`, `ether_coupled_witness` |
| `Rule30PeriodTwoLanguage` | final | Under period 2: if a kernel check shows that no path inside the bad class of the right strip spells a word, then column 1 at the white times eventually never spells it. | `no_pattern` |
| `Rule30PeriodTwoWidth5` | final | Period-2 constraints at strip width 5; for example, the free bits never spell `00` or `11111`. | `col1_constraints`, `free_bit_constraints` |
| `Rule30PeriodTwoWidth6` | final | The same at strip width 6, with more forbidden patterns. | `col1_constraints`, `free_bit_constraints` |

Q01 was also kernel-checked for width ≤ 56 during the attempt. That finite check is not part of this kit.

### Ether and period 4

| Module | Added | What it proves | Headline theorems |
|---|---|---|---|
| `Rule30Ether` | R2 | The 7×4 ether, the 109-state wall and the ether-and-wall traps. Absorption (**open**) excludes `0001`, `0011` and `0111`. | `ether_rule`, `trap_invariant`, `no_ether_wall_entry`, `absorption_excludes`, `least_period_four_of_absorption` |
| `Rule30PeriodFourSkeleton` | R2 | The right-half skeletons that least period 4 forces, and a reduction to the left-half statements `C3` (**open**). | `skeleton_0001`, `skeleton_0011`, `column_m1_0111`, `least_period_four_of_C3` |
| `Rule30EtherTrap` | final | Traps of the strip relaxation, and a certificate check that a path escapes them. | `word_lemma`, `escapes_of_certOK`, `not_trap_of_certOK` |
| `Rule30EtherTrapWidth20` | final | The pure ether lies in no trap of width ≤ 20. | `pure_ether_not_in_trap_0001`, `pure_ether_not_in_trap_0011`, `pure_ether_not_in_trap_0111` |
| `Rule30Certificates/EtherTrap0`–`5` | final | Data: the 24 certificates behind width 20. | — |

### Period 3

| Module | Added | What it proves | Headline theorems |
|---|---|---|---|
| `Rule30EtherThree` | final | The 12×3 ether and the ether-and-wall framework for period 3. | `ether3_rule`, `alignments_001_complete`, `alignments_011_complete`, `absorption3_excludes` |
| `Rule30EtherThreeNoWall` | final | The period-3 ether has no wall of width ≤ 12. | `no_wall_le_12` |
| `Rule30EtherThreeTrap` | final | `t001`, a 47-column trap of period 21. `AbsorptionT t001` (**open**) excludes `001`. | `trap_001`, `absorptionT_excludes`, `not_eventually_001_of_absorption` |
| `Rule30EtherThreeReach` | final | The empty right half reaches `t001` at time 1270. | `t001_reached`, `absorbed_empty` |
| `Rule30EtherThreeLeft` | final | Reductions to the left half: `Q001` for `001` and `C3w` for `011` (both **open**). | `not_eventually_001_of_Q001`, `not_eventually_011_of_C3w`, `Q001_stripe`, `C3w_011_ether` |
| `Rule30EtherThreeSkeleton` | final | Right-half skeletons for `001` and `011`, and the reduction `C3s001` (**open**). | `skeleton_001`, `skeleton_011`, `not_eventually_001_of_C3s` |

### Barriers

| Module | Added | What it proves | Headline theorems |
|---|---|---|---|
| `Rule30Realization` | R1 | Some configuration realizes any right half together with any column 0. Rules 90, 150 and 210 meet Jen's hypotheses, yet their center columns are eventually constant. | `column_realizable_unique`, `seed_perturbation`, `barrier` |
| `Rule30ZeroBoundaryBarriers` | R2 | For `Q01` there is no ranking through a finite abstraction, no local ranking and no edge-DFA ranking. Also gives a two-sided barrier. | `finite_abstraction_has_lasso`, `no_local_ranking`, `no_edge_dfa_ranking`, `no_joint_local_ranking` |

### Other catalog entries (not about Problem 1)

| Module | Added | What it proves | Headline theorems |
|---|---|---|---|
| `Rule30Predecessors` | 10-10 | A corrected form of the Feynmans' predecessor theorem: rule 30 on a cyclic register. | `predCount_eq_three_iff`, `predCount_eq_one_iff` |
| `Rule30PredecessorCounts` | 10-10 | How many registers have 0, 1, 2 or 3 predecessors. | `sum_predCount`, `numWithPreds_zero` |
| `Rule30Blocks` | 10-10 | Only 24 of the 32 possible 3×2 blocks occur. | `blockAt_allowed`, `occurs_iff`, `occurs_single_cell` |
| `BusyBeaverLifetimes` | 10-10 | Busy-beaver lifetimes of four cellular automata. `Rule30Blocks` reuses its bit-plane simulation. | `lifetime450504084`, `lifetime5810255963295` |
