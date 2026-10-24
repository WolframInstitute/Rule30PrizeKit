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
| Least period 3 | Reduced. 001 needs one of AbsorptionT t001, Q001 or C3s001. 011 needs C3w(011). All four are **open**. | `Rule30EtherThree*` |
| Least period 4 | Reduced to Absorption, the ether-and-wall trap, which is **open**. The pure ether lies in no trap of width ≤ 20. | `Rule30Ether`, `Rule30PeriodFourSkeleton`, `Rule30EtherTrapWidth20` |
| Longer periods | **Open.** Some words are excluded, for example by long black runs, 30 certified words and every `1 0^q` with `q ≥ 10`. | `Rule30BlackRuns`, `Rule30BlackRunBlocks`, `Rule30StripCertificateTable`, `Rule30WhiteRunEight`, `Rule30WhiteEnd` |

Barriers are also proved:
- Rules 90, 150 and 210 share every structural fact the argument uses, yet their center columns are eventually constant (`Rule30Realization`).
- Local, strip, finite-state, additive and edge-DFA invariants cannot prove Q01 (`Rule30ZeroBoundaryBarriers`).

## Building

You need [elan](https://github.com/leanprover/elan); it installs Lean 4.35.0 from `lean-toolchain`.

`lake build` builds everything, but a cold build runs modules in parallel. The four `Rule30Certificates/ZeroBoundaryWidth52Chunks*` modules take about 20 s and 3 GB each, so a cold parallel build can need about 12.5 GB.

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
    Rule30ZeroBoundaryStripeFamily Rule30ZeroBoundaryStripeFour Rule30EtherTrap \
    Rule30Certificates.EtherTrap{0,1,2,3,4,5} \
    Rule30EtherTrapWidth20 Rule30PeriodTwoLanguage Rule30PeriodTwoWidth5 Rule30PeriodTwoWidth6 \
    Rule30EtherThree Rule30EtherThreeNoWall Rule30EtherThreeTrap Rule30EtherThreeReach \
    Rule30EtherThreeLeft Rule30EtherThreeSkeleton Rule30WhiteRunEight Rule30PeriodTwoSideways \
    Rule30LightCone Rule30FiniteConfigs Rule30FiniteMaskedJen Rule30Coupled Rule30FiniteBlackRuns Rule30FiniteBlackRunBlocks Rule30FiniteDiagonals Rule30FiniteWhiteRuns \
    Rule30Certificates.WhiteEndChecks Rule30WhiteEnd; do
  lake build Ruliology.CellularAutomata.$m || break
done
lake build
```

On 2026-10-15 this took 285 s in total on an Apple M3 Max with 48 GB; the four modules added on 2026-10-23 take about 45 s more. Every module not listed below built in under 7 s and 1.2 GB.

| Module | Time | Peak memory |
|---|---|---|
| `Rule30Certificates/ZeroBoundaryWidth52Chunks0`–`3` | 22–24 s each | 2.7–2.8 GB each |
| `Rule30StripCertificateTable` | 21 s | 3.9 GB |
| `Rule30BlackRunBlocks` | 20 s | 2.3 GB |
| `Rule30ZeroBoundarySmall` | 19 s | 3.2 GB |
| `Rule30ZeroBoundaryStripe` | 18 s | 1.8 GB |
| `Rule30Certificates/WhiteEndChecks` | 34 s | 0.8 GB |
| `Rule30EtherThreeNoWall` | 9 s | 1.1 GB |
| `Rule30BlackRuns` | 9 s | 2.2 GB |

The build prints no warnings.

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
| `Rule30WhiteRunEight` | 2026-10-17 | The words `0^r 1 1` with `r ≥ 8` are excluded, for every transient: `Rule30BlackRuns.no_white_run_11` needs `r ≥ 10`. Proved on 2026-10-15 by the verifier of the white-run exclusion and left out of the catalog; ported here. | `no_white_run_11_ge8` |
| `Rule30PeriodTwoSideways` | 2026-10-17 | The coupled question `CQ01` in two more forms. It holds iff no configuration with finitely many black cells has center column `1, 0, 1, 0, …` from time 0. Sideways: for every finite right half `R`, one explicit left row `Psi R` (the constrained start whose free bits complement column 1 of the driven right half) has infinitely many black cells; this holds for `R` whenever it holds for the right half two steps later, or whenever column 1 of the driven right half is eventually periodic at the white steps. Exact death: a left row keeps the center alternating exactly until the first depth where it differs from `Psi R`. States the `R = ∅` milestone `CQ01Empty` (**open**). Barrier: from finite configurations the center alternates arbitrarily long, so no ranking through a finite abstraction of configurations decreases at every double step over which the center flips twice. | `CQ01_iff_no_finite_alternating`, `Q01_no_leftfinite_alternating`, `CQ01_iff_Psi`, `not_finSupp_Psi_of_R2`, `exact_death_center`, `truncation_death`, `CQ01Empty_iff`, `no_finite_abstract_ranking_coupled` |
| `Rule30FiniteConfigs` | 2026-10-17 | The single-seed theorems in their uniform form. For every configuration with a leftmost black cell (nonzero and left-finite): Jen's theorem (at most one column is eventually periodic) and period 1 (no column is eventually constant); the proofs use the seed only through its left edge. For nonzero finite configurations: `CQ01` holds iff none has an eventually 2-periodic center column, whatever the transient, so `CQ01` is exactly FinConf at period 2 for one column. `Q01` gives the same for every configuration with a leftmost black cell. | `jen`, `no_column_eventually_constant`, `jen_finite`, `no_column_eventually_constant_finite`, `CQ01_iff_no_finite_period_two`, `no_leftFinite_period_two_of_Q01` |
| `Rule30FiniteMaskedJen` | 2026-10-17 | The masked and window forms of Jen's theorem (`Rule30MaskedJen`) for every configuration with a leftmost black cell: if column `i` is eventually periodic, column `i + 1` is not periodic with the same period on the white times of column `i`, and `column i ∨ column (i + 1)` is not eventually periodic; with no periodicity assumed, two times never carry the same (column, or-column) window reaching the left edge; a periodic column has, in every window `[n, n + m)` with `n` past the transient and `m = n + i - lo`, a white time where the next column breaks the period. | `masked_jen`, `orCol_not_eventuallyPeriodic`, `window_jen_col`, `periodic_window` |
| `Rule30FiniteBlackRuns` | 2026-10-17 | The black-run exclusions of `Rule30BlackRuns`, for every configuration with a leftmost black cell and every column `i`. The nine-black shield holds in the evolution of every configuration; the exclusions then use the seed only through Jen's theorem and its masked form. If from some time on every black run of column `i` that is followed by white has length at least `9`, column `i` is not eventually periodic. If column `i` has period `P`, no period contains a black run of length `r` with `9 ⌈(P - r + 9) / 2⌉ ≤ r` (Theorem B), or a black run of length `≥ 9` followed by a long white run (Theorem D). The same for every nonzero finite configuration. | `nine_black`, `black_shield`, `not_eventuallyPeriodic_of_long_one_runs`, `no_long_black_run`, `no_black_white_run`, `not_eventuallyPeriodic_of_long_one_runs_finite` |
| `Rule30FiniteBlackRunBlocks` | 2026-10-17 | Theorem B′ of `Rule30BlackRunBlocks`, for every configuration with a leftmost black cell and every column `i`. If the finite check `Determined u j0` holds, column `i` is not eventually periodic with repeating word `1^r u` for any `r ≥ max 9 (9 j0)`, whatever the transient. The proof uses the seed only through Jen's theorem; the nine-black shield and the trace of the next column hold in every evolution. The kernel-checked blocks of `Rule30BlackRunBlocks` (`det_0`, …, `det_0110`) apply unchanged, for example `1^r 0` with `r ≥ 18`. The same for every nonzero finite configuration. | `no_black_run_block`, `no_period_black_run_then_white`, `no_black_run_block_finite`, `traceCol1_rowAt` |
| `Rule30FiniteDiagonals` | 2026-10-17 | The periodic diagonals of `Rule30Diagonals`, for every configuration with an edge. If `x` is white right of `hi`, the diagonal `t ↦ evol x t (hi + t - j)` is periodic from time 0 with period dividing `2^j`. If `x` is white left of `lo`, the diagonal `t ↦ evol x t (lo - t + j)` is eventually periodic with period `2^j`. Every column reads its array of diagonals along a line of slope one, as the center column of the seed does. So the periodic right diagonals behind the 2-adic odometer are not special to the seed. The bitwise form, for every starting value of `Φ(x) = x ⊕ (2x ∨ 4x)`, is `Rule30Equivalents.TFunction`. | `Rd_periodic`, `Ld_periodic`, `evol_eq_Rd`, `column_reads_periodic_rows` |
| `Rule30FiniteWhiteRuns` | 2026-10-17 | The exclusion of `Rule30WhiteRunEight` for every column of every nonzero finite configuration: no column is eventually `0^r 1 1` repeated, `r ≥ 8`, whatever the transient. The lemmas of `Rule30BlackRuns` (the first black cell right of the column moves left during a white run, and the period-start classes) hold for column `0` of any evolution; the seed's right edge becomes any black cell right of the column, which every nonzero finite configuration has from some time on; translation gives every column. | `no_white_run_11_col0`, `no_white_run_11_finite`, `evol_right_edge`, `exists_rightmost` |
| `Rule30Coupled` | 2026-10-17 | Every period, as coupled questions. In any configuration the two halves evolve as the halves driven by the center column, and the center is updated from its two driven neighbours; conversely, two driven halves glued to a column satisfying that update give a configuration with that center. `CQ ω` (**open** for every nonconstant periodic `ω`): no finite left half and finite right half are coupled to `ω`; it holds iff no finite configuration has center column `ω`. FinConf for one column is exactly the family `CQ ω` over all periodic `ω` with a black cell, and the family implies Problem 1. For the alternating column, `CQ` is `CQ01`. | `left_eq_L`, `right_eq_drv`, `evol_glue`, `CQ_iff_no_finite_config`, `CQ_altCol_iff_CQ01`, `finConf_center_iff`, `problem1_of_CQ` |
| `Rule30LightCone` | 2026-10-17 | The locality behind space-efficient evaluation. A cell at time `t` depends only on the initial cells within distance `t`. With space blocks and time steps of width `b`, each block is a fixed function of the three blocks around it one time step earlier, so the center cell at time `m b` is the root of a fan-in-3 tree of `b`-bit blocks with height `m`. This is the shape that Williams's square-root-space simulation passes to Cook–Mertz tree evaluation, about `√n · log n` bits for the center cell at time `n`; neither algorithm is formalized. | `evol_window`, `block_step`, `center_eq_root` |
| `Rule30ZeroBoundaryStripeFour` | 2026-10-23 | Stripe prefixes with four tail cells. For every `m` and every tail `v` of four cells, the start `S[1..m] · v · 0^∞` first deviates from the stripe at some depth `d ≤ m + 6`, and depth `1` turns white at an even time `≤ d - 1 + 31`. Every class `(m mod 2, v)` is covered except `v = 13` with `m` odd. This carries `Rule30ZeroBoundaryStripeFamily` from tails of length at most 3 to length 4, by the same route: one kernel-checked periodic front-window orbit per class, from `Rule30Certificates/ZeroBoundaryStripeCycles0`–`3` (namespace `Rule30ZeroBoundaryStripeFront.StripeCycles3` for the new data module). Contributed by Ying Yin with Codex (GPT-6) as Rule 30 Prize submission `R30-20261020-81df0e`, and ported to core Lean. | `stripe_four_tail`, `family4_of_class` |
| `Rule30WhiteEnd` | 2026-10-23 | The white end. For every `q ≥ 10`, no column of rule 30 is eventually the repeating word `1 0^q`, whatever the transient: for the single seed, `EventuallyWord (true :: List.replicate q false)` is false, and the same holds for every column of every configuration with a leftmost black cell, every finite nonzero one included. `Rule30StripCertificateTable` excludes only `q = 10, 11, 12`. A one-sided strip relaxation (eight cells right of the column, an arbitrary cell beyond) determines column `c + 1` after three periods; kernel checks cover `q = 10 … 25`, and the relaxation's white step satisfies `W^26 = W^22` on the sets that occur, which covers every `q ≥ 26`. Two adjacent columns periodic for ever then contradict Jen's theorem with a clock. The checks are in `Rule30Certificates/WhiteEndChecks`, where `control_q9` shows that the check fails at `q = 9`. Contributed by Gareth Herbert with Claude and GPT as Rule 30 Prize submission `R30-20261022-c27323`, and ported to core Lean. | `not_eventuallyWord_white_end`, `white_end_seed`, `white_end`, `white_end_finite` |
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
| `Rule30CenterRuns` | 2026-10-23 | Runs of the center column are at most linear in time. A block of `L` consecutive cells of one color starting at time `a ≥ 1` (not necessarily maximal) has `L ≤ a` if black, attained at `a = 3`, and `L ≤ a - 1` if white, attained only at `a = 2`; for `a ≥ 3` a white block has `L ≤ a - 3`, not attained up to time 3000. So every window `[a, 2a]` holds a white cell and every window `[a, 2a)` a black cell (`[a, 2a - 2)` for `a ≥ 3`), and the counts grow at least logarithmically: `m + 1` black cells before `2^m`, so `Nat.log2 n ≤ blackCount n`, and `m` white cells before `4^m`. The black bound holds for every column of every configuration with a leftmost black cell, measured from the time the left edge passed the column. Black runs: left-permutivity forces the alternating row `… 0 1 0 1` under the run, which cannot cover the two adjacent leftmost black cells. White runs: the first black cell right of the center (`Rule30BlackRuns.front_moves`) fixes column `1`, which forces the row at the start of the run in closed form; it contradicts the left-edge diagonals `D 1`, …, `D 4` of `Rule30Diagonals`. Contributed by Luis Perez Morales, Claude (Fable 5.1), in the Rule 30 Prize submission that supersedes `R30-20261024-801153`, and ported to core Lean. | `black_run_le`, `white_run_le'`, `white_run_le_three`, `exists_white`, `exists_black'`, `exists_black_three`, `blackCount_pow_two`, `log_two_succ_le_blackCount`, `log_two_le_blackCount`, `whiteCount_pow_four`, `log_le_whiteCount`, `black_run_le_evol` |

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
- The six `Rule30EtherThree*` modules share `…Rule30EtherThree`.
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
