# Rule 30 Prize, Problem 1: a catalog of reformulations

Status as of 2026-10-15, after two formalization batches. Every "Proved (library)" entry is a theorem in
this folder's Lake project, checked by an independent verifier.

**Contents.** 1. Introduction · 2. Status of the equivalent forms · 3. Equivalent forms, by field
· 4. Stronger statements · 5. Weaker statements · 6. Related questions, including Problems 2 and 3
· 7. Broader perspectives · 8. References and provenance

---

## 1. Introduction

Problem 1 of the Rule 30 Prize asks whether the center column of rule 30, started from a single
black cell, ever becomes periodic [W19]. The conjecture is that it does not. This catalog collects
reformulations of the problem, in four kinds:

- **equivalent**: provably ⟺ Problem 1. Proving such an equivalence does not solve the problem; it
  moves the problem into another field, where other tools apply;
- **stronger**: implies Problem 1. Every stronger statement listed here is open;
- **weaker**: implied by Problem 1. Some are proved;
- **related**: no implication either way is known. Prize Problems 2 and 3 are in this group.

Every equivalent form has a Lean status (Section 2).

### The statement

Let c(t) be the color of the center cell after t steps (1 = black). Each step replaces every cell
by *left* XOR (*center* OR *right*). The column begins

c = 1101110011000101100100111010111001110101… (OEIS A051023).

The project states Problem 1 in its core-Lean catalog [`../lean`](../lean), which does not use
Mathlib:

```lean
-- ../lean/Ruliology/CellularAutomata/Rule30Jen.lean   (namespace Ruliology.CellularAutomata.Rule30Jen)
def rule (a b c : Bool) : Bool := xor a (b || c)
def cell : Nat → Int → Bool
  | 0, p => decide (p = 0)
  | t + 1, p => rule (cell t (p - 1)) (cell t p) (cell t (p + 1))
def EventuallyPeriodic (f : Nat → Bool) : Prop := ∃ T P : Nat, 0 < P ∧ ∀ t, T ≤ t → f (t + P) = f t

-- ../lean/Ruliology/CellularAutomata/Rule30Prize.lean (namespace Ruliology.CellularAutomata.Rule30Prize,
--                                                      with `open Rule30Jen`)
def center (t : Nat) : Bool := cell t 0
def Problem1 : Prop := ¬ EventuallyPeriodic center
```

The Mathlib-based library in this folder (namespace `Rule30Equivalents`, Mathlib `56a005855e`,
Lean 4.35.0) imports these definitions. [Rule30Equivalents/Basic.lean](Rule30Equivalents/Basic.lean)
adds two abbreviations:

```lean
abbrev c : Nat → Bool := Rule30Prize.center
abbrev EventuallyPeriodic (b : Nat → Bool) : Prop := Rule30Jen.EventuallyPeriodic b
theorem problem1_iff_not_eventuallyPeriodic : Rule30Prize.Problem1 ↔ ¬ EventuallyPeriodic c
```

`Problem1` is equivalent to `Rule30.centerColumn_not_eventually_periodic` in
google-deepmind/formal-conjectures; see [8].

**What is known.** Period 1 is excluded: no column of the pattern is eventually constant
(`Rule30Prize.no_column_eventually_constant`). Any eventual period P from time T has
T + P ≥ 16359 (`Rule30FactorWindow.transient_add_period_ge`, kernel-checked). Wolfram found the
column non-periodic over the first 10⁹ steps by computation [W19]. Section 5 lists the other
partial results.

### How this catalog was made

On 2026-10-15 six surveys collected candidate reformulations with their sources, one survey per
angle: Wolfram's writings; number theory; algebra, coding and cryptography; combinatorics on words
and dynamics; cellular-automaton structure; logic and computation. A synthesis merged them into 43
equivalent forms, re-derived every classification, and typechecked a Lean statement for most
forms. A critic then reviewed the synthesis. It found none of the 43 equivalences wrong, but it
corrected several side claims, two difficulty ratings and some references, and it proposed new
entries. This file applies all of those corrections. It adds the critic's entries: ten equivalent
forms ([44]–[53]), two stronger statements, one weaker statement and one related theorem. Section 8.2 lists the checks.

### Conventions

- **EP** means eventually periodic. S = {t : c(t) = 1} is the set of black times (OEIS A327984).
  x₂ = Σ_{t≥0} c(t)·2^−(t+1) is the column read as a binary number. σ is the shift,
  (σb)(t) = b(t + 1).
- **Difficulty** rates how hard it is to machine-check the stated *relation* to Problem 1, not the
  problem itself: trivial, easy, moderate, or hard (a classical theorem must be formalized first).
- **Sources.** Bracketed tags such as [W19] refer to Section 8. *Own reasoning* marks an argument
  made by this project's surveys or critic and not taken from a publication. *Own computation*
  marks numerics run by the project. *Data* is evidence about a finite prefix; it proves nothing
  about the tail. *Kernel-checked* marks a Lean theorem.
- **Lean blocks** show signatures. Proofs are in the files named in each entry's status line;
  statements marked *stated* have `sorry` proofs in the original survey's scratch files, which are
  not part of this kit.
- **The common pattern.** Most equivalences instantiate a general theorem
  `∀ b : ℕ → Bool, EventuallyPeriodic b ↔ X b` at b = c. Two kinds do not:
  - forms that cannot see a constant tail (greedy digits, gaps, run lengths) also need the proved
    fact that c is not eventually constant (`Rule30Prize.center_not_eventually_constant`);
  - *identity transfers* ([6], [8], [21], [22], [25], [26], [33]) use rule-30 lemmas to prove that
    another sequence equals c or ¬c, or is the unique solution of a causal system. They have no
    `∀ b` form.
- **Three mechanisms** produce almost every entry: pigeonhole on a finite state (a shift, a
  remainder, a recurrence window, an automaton state); digit expansions (a number is rational iff
  its digits are EP, in ℝ, in ℚ_p and in F_q((1/X))); and definability (the EP subsets of ℕ are
  exactly the Presburger-definable, semilinear, unary-regular and MSO(ℕ,<)-definable ones).

---

## 2. Status of the equivalent forms

**Lean status labels.**

- **Proved (library)**: proved in this folder's Lake project. Batch 1:
  [BinaryIrrational](Rule30Equivalents/BinaryIrrational.lean),
  [PowerSeriesF2](Rule30Equivalents/PowerSeriesF2.lean),
  [ShiftOrbit](Rule30Equivalents/ShiftOrbit.lean) and [Symmetry](Rule30Equivalents/Symmetry.lean).
  Batch 2: [NumberTheory](Rule30Equivalents/NumberTheory.lean), [TwoAdic](Rule30Equivalents/TwoAdic.lean),
  [LinearRelations](Rule30Equivalents/LinearRelations.lean),
  [WordsAutomata](Rule30Equivalents/WordsAutomata.lean) and
  [TransformsSeeds](Rule30Equivalents/TransformsSeeds.lean). Later (2026-10-17):
  [IntegerRows](Rule30Equivalents/IntegerRows.lean), [LogicAutomata](Rule30Equivalents/LogicAutomata.lean),
  [Realization](Rule30Equivalents/Realization.lean), [WordForms](Rule30Equivalents/WordForms.lean),
  [Expansions](Rule30Equivalents/Expansions.lean), [Holonomic](Rule30Equivalents/Holonomic.lean),
  [OmegaRegular](Rule30Equivalents/OmegaRegular.lean), [PisotNumbers](Rule30Equivalents/PisotNumbers.lean),
  [PisotBase](Rule30Equivalents/PisotBase.lean),
  [Automatic](Rule30Equivalents/Automatic.lean), [Transcendence](Rule30Equivalents/Transcendence.lean),
  [LempelZiv](Rule30Equivalents/LempelZiv.lean), [CoupledHalves](Rule30Equivalents/CoupledHalves.lean),
  [TailLanguage](Rule30Equivalents/TailLanguage.lean), [TFunction](Rule30Equivalents/TFunction.lean),
  [TFunctionCycles](Rule30Equivalents/TFunctionCycles.lean) and [DFinite](Rule30Equivalents/DFinite.lean).
  Each compiles with no `sorry`, `admit` or `native_decide`. For each module of the two batches an
  independent verifier recompiled it, checked that every theorem uses at most the axioms `propext`, `Classical.choice` and
  `Quot.sound`, and restated the main statements to confirm they say what they claim. The verifiers
  refuted nothing of substance; one unconfirmed theorem number and one overstated docstring
  sentence were corrected. The later modules were compiled and axiom-checked by their author; no
  independent verifier has restated them yet. [scripts/CheckAxioms.lean](scripts/CheckAxioms.lean)
  prints the axioms of all 222 library theorems whose names begin with `problem1_iff`,
  `problem1_of`, `problem2_iff` or `problem2_of`.
- **Sufficient direction proved (library)**: the library proves that the form implies Problem 1
  (`problem1_of_*`); the equivalence is only stated.
- **Proved (core catalog)**: proved in the core-Lean catalog [`../lean`](../lean).
- **Stated**: a Lean statement typechecks with `sorry` in a scratch statement file of the original
  survey, which is not part of this kit. The entry quotes it.
- **Sketch**: stating the form needs definitions that Mathlib lacks.

Library names below are relative to `Rule30Equivalents`, and core-catalog names are relative to
`Ruliology.CellularAutomata`. Stated theorems carry the names used in the scratch
files. The rows follow the order of Section 3.

| # | id | Field | Problem 1 ⟺ … | Lean status | Lean name |
|---|---|---|---|---|---|
| 7 | eventual-word | bookkeeping | c is not eventually w w w … for any nonempty word w | Proved (core catalog and library) | `Rule30StripCertificates.problem1_iff_no_word`, `WordsAutomata.problem1_iff_no_eventual_word` |
| 53 | mathlib-bridges | bookkeeping | the same, in Mathlib's vocabulary: `Filter.atTop` and `List.HasPeriod` forms | Proved (library) | `WordsAutomata.problem1_iff_filter`, `WordsAutomata.problem1_iff_no_hasPeriod_tail` |
| 8 | fc-bridge | bookkeeping | the formal-conjectures statement; Wolfram's 2019 statement, read as intended | Proved (library) | `TransformsSeeds.problem1_iff_fc`, `TransformsSeeds.problem1_iff_wolfram` |
| 14 | pi2-normal-form | logic | for all T and P ≥ 1 some t ≥ T has c(t+P) ≠ c(t); no eventual period k!; Diophantine form | Proved (library) | `TransformsSeeds.problem1_iff_pi2`, `TransformsSeeds.problem1_iff_factorial_periods`, `DiophantineGraph.center_diophFn`, `DiophantineGraph.problem1_iff_forall_exists_poly` |
| 25 | nks-integer-rows | bookkeeping | t ↦ bit t of a(t), where a(t+1) = a(t) ⊕ (2a(t) ∨ 4a(t)), is not EP | Proved (library) | `IntegerRows.problem1_iff_integer_rows`, `TFunction.problem1_iff_orbit` |
| 54 | black-wall | CA / automaton group | t ↦ bit t − 1 of aᵗ(0) is not EP, where a(y) = y ⊕ (2y ∨ 4y ∨ 3): the column at distance t − 1 from a black wall | Proved (library) | `AutomatonGroup.problem1_iff_black_wall` |
| 26 | diagonal-array | CA / odometer | the main diagonal of the right-diagonal array is not EP | Proved (library) | `IntegerRows.problem1_iff_diagArray`, `IntegerRows.diagArray_row_periodic`, `TFunction.testBit_orbit_periodic` |
| 1 | binary-irrational | real numbers | x₂ = 0.c(0)c(1)c(2)…₂ is irrational | Proved (library) | `BinaryIrrational.problem1_iff_irrational_binary` |
| 2 | base-b-irrational | real numbers | 0.c(0)c(1)… read in any integer base B ≥ 2 is irrational | Proved (library), including the `Real.ofDigits` and Cantor-function forms | `BinaryIrrational.problem1_iff_irrational_base`, `BinaryIrrational.problem1_iff_irrational_decimal`, `Realization.problem1_iff_irrational_ofDigits`, `Realization.problem1_iff_irrational_cantorFunction` |
| 16 | integer-digits | real numbers, without reals | no fraction p/q has binary digits c | Proved (library) | `NumberTheory.problem1_iff_not_rational_digits` |
| 11 | continued-fraction | real numbers | the continued fraction of x₂ does not terminate | Proved (library) | `NumberTheory.problem1_iff_cf_not_terminates` |
| 12 | dirichlet-liouville | Diophantine approximation | infinitely many rationals q have abs(x₂ − q) < 1/den(q)²; `LiouvilleWith 2 x₂` | Proved (library) | `NumberTheory.problem1_iff_dirichlet`, `NumberTheory.problem1_iff_liouvilleWith_two` |
| 10 | circle-rotation | circle dynamics | x₂ has infinite order in ℝ/ℤ; its multiples are dense; it is not preperiodic for doubling | Proved (library) | `NumberTheory.problem1_iff_infinite_order`, `NumberTheory.problem1_iff_dense_multiples`, `NumberTheory.problem1_iff_doubling_not_preperiodic` |
| 39 | lagrange | real numbers | θ = [1+c(0); 1+c(1), 1+c(2), …] is not a quadratic irrational | Proved (library) | `Lagrange.problem1_iff_not_quadratic`, `Lagrange.digit_periodic_iff` |
| 49 | minkowski | real numbers | ?⁻¹(x₂) = [0; 1, r₁, r₂, …] (r_k the run lengths) is not a quadratic irrational | Proved (library), for y defined by its continued fraction | `Minkowski.problem1_iff_minkowski_not_quadratic` |
| 50 | other-expansions | real numbers | the Engel, Sylvester and factorial-base expansions of x₂ are infinite; its Lüroth expansion is not EP | Proved (library), all four | `Expansions.problem1_iff_engel_infinite`, `Expansions.problem1_iff_sylvester_infinite`, `Expansions.problem1_iff_factorial_infinite`, `Expansions.problem1_iff_luroth_not_eventuallyPeriodic` |
| 48 | pisot-base | real numbers | Σ c(t)β^−(t+1) ∉ ℚ(β) for a Pisot number β > 2, such as 1 + √2 | Proved (library), for every Pisot number β > 2 | `PisotNumbers.problem1_iff_not_mem_adjoin`, `PisotBase.problem1_iff_not_mem_Q_sqrt_two` |
| 15 | two-adic | p-adic numbers | Σ c(t)2ᵗ ∈ ℤ₂ is not rational; an integer congruence form for every prime p | Proved (library) | `TwoAdic.problem1_iff_padic_irrational`, `TwoAdic.problem1_iff_padic_int` |
| 30 | fcsr-complexity | coding theory | the 2-adic (FCSR) complexity of c is unbounded | Proved (library) | `TwoAdic.problem1_iff_two_adic_complexity` |
| 5 | series-f2-lfsr | algebra, coding theory | Σ c(t)Xᵗ ∉ F₂(X); no eventual linear recurrence or LFSR over F₂ generates c; its linear complexity is unbounded | Proved (library) | `PowerSeriesF2.problem1_iff_series_not_rational` and five more |
| 17 | rational-any-field | algebra | Σ c(t)Xᵗ ∉ K(X) for any field K (rationality: any nontrivial commutative ring); c satisfies no `LinearRecurrence` over K | Proved (library) | `LinearRelations.problem1_iff_series_not_rational`, `LinearRelations.problem1_iff_no_linearRecurrence` |
| 44 | linear-relations | linear algebra | the shifts σⁿc are linearly independent over any field; their span is infinite-dimensional; no polynomial in σ kills c | Proved (library) | `LinearRelations.problem1_iff_shifts_linearIndependent`, `LinearRelations.problem1_iff_not_torsion` |
| 32 | hankel | linear algebra | the Hankel matrix (c(i+j)) has unbounded rank; det H_n ≠ 0 for infinitely many n (over ℤ or F₂) | Proved (library) | `LinearRelations.problem1_iff_hankel_rank_unbounded`, `LinearRelations.problem1_iff_hankel_det_int` |
| 45 | skolem-mahler-lech | algebra | S is not the zero set of a linear recurrence sequence over ℚ | Proved (library) | `SkolemMahlerLech.problem1_iff_not_LRS_zero_set`, `SkolemMahlerLech.skolem_mahler_lech`, `Strassmann.strassmann` |
| 31 | p-recursive | algebra | no polynomial-coefficient recurrence holds; Σ c(t)Xᵗ is not D-finite | Proved (library), both forms | `Holonomic.problem1_iff_not_pRecursive`, `DFinite.problem1_iff_not_dFinite` |
| 38 | fatou | algebra | Σ c(t)zᵗ is transcendental over ℚ(z) | Proved (library) | `AlgebraicDFinite.problem1_iff_transcendental`, `AlgebraicDFinite.exists_dfinite_of_isAlgebraic` |
| 28 | nlfsr | coding theory | no nonlinear feedback shift register generates c; maximum-order complexity is unbounded | Proved (library) | `WordsAutomata.problem1_iff_no_feedback_shift_register`, `WordsAutomata.problem1_iff_maxOrderComplexity_tendsto`, `WordsAutomata.problem1_iff_no_feedback_from_zero` |
| 41 | natural-boundary | complex analysis | Σ c(t)zᵗ has the unit circle as natural boundary | Proved (library), through Szegő's theorem | `Szego.problem1_iff_natural_boundary`, `Szego.eventuallyPeriodic_iff_continuation`, `SzegoContour.exists_approx_recurrence`, `SzegoPolynomial.exists_notch_poly`, `NaturalBoundary.problem1_of_natural_boundary`, `MeromorphicExtension.problem1_iff_no_meromorphic_extension`, `MeromorphicExtension.problem1_iff_no_meromorphicOn`, `RandomNaturalBoundary.ae_circleIsNaturalBoundary_trace`, `ApproximateRecurrence.problem1_iff_no_approx_recurrence` |
| 3 | shift-orbit | symbolic dynamics | the shifts of c are pairwise distinct; c is not a preperiodic point of the shift | Proved (library) | `ShiftOrbit.problem1_iff_infinite_shifts`, `ShiftOrbit.problem1_iff_injective_shifts`, `ShiftOrbit.problem1_iff_not_preperiodic` |
| 4 | morse-hedlund | words | c has at least n + 1 distinct factors of each length n | Proved (library) | `ShiftOrbit.problem1_iff_ncard_factors` and three more |
| 13 | orbit-closure | topological dynamics | the orbit closure of c in {0,1}^ℕ is infinite | Proved (library) | `WordsAutomata.problem1_iff_orbit_closure_infinite` |
| 23 | special-factors | words | c has a right-special factor of every length | Proved (library) | `WordsAutomata.problem1_iff_right_special` |
| 24 | finite-certificates | words, computation | for every N, some prefix has more than N distinct factors of one length | Proved (library) | `WordForms.problem1_iff_prefix_certificates` |
| 34 | omega-limit | topological dynamics | the ω-limit set of c under the shift is infinite | Proved (library) | `WordsAutomata.problem1_iff_omegaLimit_infinite` |
| 35 | tail-language | words | the words that occur infinitely often number at least n + 1 for each length n | Proved (library), all three forms | `WordsAutomata.problem1_iff_tail_complexity`, `TailLanguage.problem1_iff_tail_strictMono`, `TailLanguage.problem1_iff_tailSubshift_infinite` |
| 29 | return-words | words | the gaps between black cells, and the run lengths, are not EP | Proved (library) | `WordForms.problem1_iff_black_gaps`, `WordForms.problem1_iff_white_gaps`, `WordForms.problem1_iff_run_lengths`, `WordForms.problem1_iff_returnWords` |
| 47 | golden-power | words | infinitely many prefixes have no suffix of exponent ≥ φ² | Proved (library) | `WordForms.problem1_iff_infinitely_many_prefixes_without_golden_power`, `GoldenPowers.eventuallyPeriodic_of_gp` |
| 51 | unbordered-factors | words | every tail of c has unbordered factors of unbounded length | Proved (library) | `WordForms.problem1_iff_late_long_unbordered_factors`, `Lyndon.eventuallyPeriodic_of_bordered` |
| 19 | simple-transforms | words | ¬c, the shifts of c, the XOR derivative and the running parity are not EP | Proved (library) | `Symmetry.problem1_iff_complement`, `TransformsSeeds.problem1_iff_xor_derivative` |
| 20 | decimations | words | for each k some decimation c(kn+r) is not EP; every modulus has a non-constant residue class | Proved (library) | `TransformsSeeds.problem1_iff_decimation`, `TransformsSeeds.problem1_iff_nonconstant_class` |
| 6 | symmetric-rules | cellular automata | the center columns of rule 86 (black seed) and of rules 135 and 149 (white seed) are not EP | Proved (library) | `Symmetry.problem1_iff_rule86`, `Symmetry.problem1_iff_rule135`, `Symmetry.problem1_iff_rule149` |
| 21 | stripe-seeds | cellular automata | rule 30 from 1, 11, 101, 1011, … has a non-EP center column | Proved (library) | `TransformsSeeds.problem1_iff_stripeSeed` |
| 22 | realization | cellular automata | the single seed realizes no EP column | Proved (library) | `Realization.problem1_iff_realization` |
| 33 | coupled-halves | cellular automata | the causal coupled-halves system has no EP solution | Proved (library) | `CoupledHalves.problem1_iff_coupled_halves` |
| 9 | presburger | logic | S is not Presburger-definable; S is not semilinear | Proved (library) | `LogicAutomata.problem1_iff_not_presburger`, `LogicAutomata.problem1_iff_not_semilinear` |
| 18 | regular-languages | automata | {1ⁿ : c(n) = 1} and the prefix language of c are not regular | Proved (library) | `LogicAutomata.problem1_iff_unary_not_regular`, `LogicAutomata.problem1_iff_prefixes_not_regular` |
| 40 | context-free | automata | the same two languages are not context-free | Proved (library) | `ContextFree.problem1_iff_unary_not_contextFree`, `ContextFree.problem1_iff_prefixes_not_contextFree`, `ContextFree.pumping` |
| 36 | omega-regular | automata, logic | {c} is not ω-regular; S is not MSO(ℕ,<)-definable | Proved (library), both forms | `OmegaRegular.problem1_iff_not_omega_regular`, `MonadicLogic.problem1_iff_not_msoDefinable` |
| 27 | finite-state-machines | automata | every finite-state predictor errs infinitely often; no finite autonomous machine generates c | Proved (library) | `WordsAutomata.problem1_iff_unpredictable`, `WordsAutomata.problem1_iff_no_finite_generator` |
| 37 | lz76 | information theory | the Lempel–Ziv complexity of the prefixes is unbounded | Proved (library) | `LempelZiv.problem1_iff_lz_unbounded` |
| 52 | automatic-complexity | automata | the automatic complexity of the prefixes tends to ∞ | Proved (library) | `Automatic.problem1_iff_automaticComplexity_tendsto_top` |
| 42 | cobham-christol | automata, algebra | c is not both 2- and 3-automatic; Σ c(t)Xᵗ is transcendental over F₂(X) or over F₃(X); S is not definable in both (ℕ, +, V₂) and (ℕ, +, V₃); c is not both 2- and 3-regular | Proved (library), all forms | `Cobham.problem1_iff_not_two_three_automatic`, `Cobham.problem1_iff_exists_not_automatic`, `Christol.problem1_iff_transcendental_F2_or_F3`, `BuchiArithmetic.problem1_iff_not_buchi_definable`, `Cobham.eventuallyPeriodic_of_isAutomatic`, `Christol.isAutomatic_of_isAlgebraic`, `RegularSequences.problem1_iff_not_regularSeq_two_three` |
| 46 | durand-cobham | automata | c is not both α- and β-substitutive, for multiplicatively independent Perron numbers α, β | Stated; sufficient direction for integer bases and uniform case proved (library) | `problem1_iff_not_substitutive`; `Substitutive.problem1_of_not_substitutive`, `Substitutive.problem1_of_not_substitutive_two_three`, `UniformMorphic.problem1_iff_not_uniformMorphic_two_three`, `UniformMorphic.problem1_iff_not_uniformMorphic`, `PerronFrobenius.tendsto_pow_div`, `LinearRecurrence.isLinearlyRecurrent_of_isPrimitive` |
| 43 | gap-theorems | complexity theory | no one-tape TM decides {1ⁿ : c(n) = 1} in time o(n log n); no TM does it in space o(log log n) | Proved (library), all forms, also for digit input | `OneTapeGap.problem1_iff_no_fast_one_tape_decider`, `OneTapeRegular.problem1_iff_no_fast_digit_deciders`, `OfflineGap.problem1_iff_no_small_space_decider`, `OfflineGap.problem1_iff_no_small_space_digit_deciders` |

**Summary.** Of the 54 equivalent forms, 52 are proved in the library: 6 in batch 1, 21 in
batch 2, and 25 later: [25] and [26] in [IntegerRows](Rule30Equivalents/IntegerRows.lean), [9] and
[18] in [LogicAutomata](Rule30Equivalents/LogicAutomata.lean), [22] in
[Realization](Rule30Equivalents/Realization.lean), [24], [29], [47] and [51] in
[WordForms](Rule30Equivalents/WordForms.lean), [50] (Engel and Sylvester) in
[Expansions](Rule30Equivalents/Expansions.lean), [31] in [Holonomic](Rule30Equivalents/Holonomic.lean)
(the recurrence form) and [DFinite](Rule30Equivalents/DFinite.lean) (the D-finite form), [36] in
[OmegaRegular](Rule30Equivalents/OmegaRegular.lean) (Büchi) and [MonadicLogic](Rule30Equivalents/MonadicLogic.lean) (MSO), [48] in
[PisotNumbers](Rule30Equivalents/PisotNumbers.lean) (every Pisot base β > 2) and
[PisotBase](Rule30Equivalents/PisotBase.lean) (β = 1 + √2), [52] in [Automatic](Rule30Equivalents/Automatic.lean), and
[37] in [LempelZiv](Rule30Equivalents/LempelZiv.lean), and [33] in
[CoupledHalves](Rule30Equivalents/CoupledHalves.lean), [54] in
[AutomatonGroup](Rule30Equivalents/AutomatonGroup.lean), [39] in [Lagrange](Rule30Equivalents/Lagrange.lean),
[49] in [Minkowski](Rule30Equivalents/Minkowski.lean), [40] in
[ContextFree](Rule30Equivalents/ContextFree.lean), [38] in
[AlgebraicDFinite](Rule30Equivalents/AlgebraicDFinite.lean), [45] in
[SkolemMahlerLech](Rule30Equivalents/SkolemMahlerLech.lean), [42] in
[Cobham](Rule30Equivalents/Cobham.lean), [41] in [Szego](Rule30Equivalents/Szego.lean), and [43] in
[OneTapeGap](Rule30Equivalents/OneTapeGap.lean)
(time) and [OfflineGap](Rule30Equivalents/OfflineGap.lean) (space). One more, [7], is proved in the core catalog and
also has a library proof. All three parts of [14] are proved, the Diophantine graph included
([DiophantineGraph](Rule30Equivalents/DiophantineGraph.lean)). The MSO form of [36] is proved by the composition method,
with types of assignments instead of Büchi automata ([MonadicLogic](Rule30Equivalents/MonadicLogic.lean)). All four parts of [50] are proved, Lüroth included. [51] is proved through the
Ehrenfeucht–Silberger theorem for infinite words ([Lyndon](Rule30Equivalents/Lyndon.lean)). [39] is proved
through the Euler–Lagrange theorem ([Lagrange](Rule30Equivalents/Lagrange.lean)), and [49] from it and [29]
([Minkowski](Rule30Equivalents/Minkowski.lean)). [47] is proved through the Mignosi–Restivo–Salemi theorem
([GoldenPowers](Rule30Equivalents/GoldenPowers.lean)). [40] is proved through the pumping lemma for
context-free languages, which the library proves for every grammar
([ContextFree](Rule30Equivalents/ContextFree.lean)). [38] is proved through "algebraic ⟹ D-finite"
and [31], without Fatou's theorem ([AlgebraicDFinite](Rule30Equivalents/AlgebraicDFinite.lean)). [45] is
proved through the Skolem–Mahler–Lech theorem, which the library proves in the p-adic way, with
Strassmann's theorem ([Strassmann](Rule30Equivalents/Strassmann.lean),
[SkolemMahlerLech](Rule30Equivalents/SkolemMahlerLech.lean)). [42] is proved through Cobham's theorem,
in Krebs' short proof ([Cobham](Rule30Equivalents/Cobham.lean)), and its F₂/F₃ form also through
Christol's theorem ([Christol](Rule30Equivalents/Christol.lean)). [43] is proved through Hennie's
theorem: a one-tape machine that runs in time o(n log n) on unary input has bounded crossing
sequences, so it decides an eventually periodic language
([OneTapeGap](Rule30Equivalents/OneTapeGap.lean)); its space form through the theorem of Stearns,
Hartmanis and Lewis, with the same splicing on the input tape of an offline machine
([OfflineGap](Rule30Equivalents/OfflineGap.lean)). [41] is proved through Szegő's theorem for
0/1 sequences: Cauchy's theorem on an annular sector writes a recurrence combination of the
coefficients as a contour integral, and an explicit monic polynomial, small on a notched disk,
takes the place of logarithmic capacity ([Szego](Rule30Equivalents/Szego.lean)). 1 form is
stated, [46] ([Substitutive](Rule30Equivalents/Substitutive.lean)); its sufficient direction for
integer bases and its uniform case (uniform substitutions) are proved.

**Next targets after batch 2.** The critic's suggestions that batch 2 does not cover:

- automatic complexity [52]: done, `Automatic.problem1_iff_automaticComplexity_tendsto_top`;
- Kopra's limit-point theorems, a proved related result (Section 6.3): done, in
  [LimitPoints](Rule30Equivalents/LimitPoints.lean) and
  [RightHalfReturns](Rule30Equivalents/RightHalfReturns.lean).

Candidates for upstreaming to Mathlib:

- "`Real.ofDigits d` is rational iff d is eventually periodic", for arbitrary digits ℕ → Fin b;
- Morse–Hedlund;
- an eventually-periodic predicate in `Filter.atTop` form [53];
- finite-valued power series are rational iff their coefficients are EP;
- `Irrational x → LiouvilleWith 2 x`;
- Kronecker's Hankel criterion.

---

## 3. Equivalent forms, by field

Shared definitions. The scratch statements below use

```lean
noncomputable abbrev x₂ : ℝ := ∑' t, (if Rule30Prize.center t then (1 : ℝ) else 0) / 2 ^ (t + 1)
-- definitionally equal to the library's Rule30Equivalents.BinaryIrrational.centerBinary
noncomputable def series (K : Type*) [Field K] : PowerSeries K :=
  PowerSeries.mk fun t => if Rule30Prize.center t then (1 : K) else 0
```

with `open Ruliology.CellularAutomata` and `import Rule30Equivalents`.

### 3.1 Restatements and bookkeeping

**[7] eventual-word: no eventual word.**
- *Statement.* There is no nonempty word w and no time T with c(T + n) = w[n mod len(w)] for all n.
  So Problem 1 is the conjunction, over all primitive words w, of "c is not eventually w w w …".
  The project's period-specific reductions attack these conjuncts one at a time (Section 5).
- *Proof route.* An eventual word gives an eventual period len(w). Conversely, period P from T
  gives the word c(T)…c(T + P − 1).
- *Difficulty.* Trivial.
- *Lean.* Proved in the core catalog. A library copy is proved (batch 2:
  `WordsAutomata.problem1_iff_no_word`, `problem1_iff_no_eventual_word` and
  `problem1_iff_no_primitive_word`).

  ```lean
  -- ../lean/Ruliology/CellularAutomata/Rule30StripCertificates.lean
  def EventuallyWord (w : List Bool) : Prop :=
    ∃ T, ∀ t, T ≤ t → cell t 0 = w.getD ((t - T) % w.length) false
  theorem problem1_iff_no_word : Problem1 ↔ ∀ w : List Bool, w ≠ [] → ¬ EventuallyWord w
  ```

- *Sources.* [Project] (`Rule30StripCertificates`).

**[53] mathlib-bridges: the definition in Mathlib's vocabulary** (new).
- *Statement.* Problem 1 ⟺ (a) there is no P > 0 such that c(t + P) = c(t) holds eventually along
  `Filter.atTop` ⟺ (b) there are no T and P > 0 such that every prefix of the tail
  c(T), c(T + 1), … has period P in the sense of Mathlib's `List.HasPeriod`.
- *Proof route.* (a) `∀ᶠ t in atTop` unfolds to "for all t ≥ some T". (b) A word has period P iff
  its letters agree at distance P (`List.hasPeriod_iff_getElem?`). So "every prefix of the tail
  has period P" says exactly "period P from T". Own reasoning.
- *Why it matters.* (a) is the natural form for an upstream "eventually periodic" predicate. (b)
  links Problem 1 to Mathlib's Fine–Wilf lemma `List.HasPeriod.gcd`
  (Data/List/PeriodicityLemma.lean), which is useful for [37], [47], [51] and [52].
- *Difficulty.* Trivial.
- *Lean.* Proved in the library (batch 2: `WordsAutomata.problem1_iff_filter`, `problem1_iff_frequently_ne`
  and `problem1_iff_no_hasPeriod_tail`). Before batch 2 the statements were stated (critic):

  ```lean
  theorem problem1_iff_filter : Rule30Prize.Problem1 ↔
      ¬ ∃ P > 0, ∀ᶠ t in Filter.atTop, Rule30Prize.center (t + P) = Rule30Prize.center t
  theorem problem1_iff_no_hasPeriod_tail : Rule30Prize.Problem1 ↔
      ¬ ∃ T P : ℕ, 0 < P ∧ ∀ n : ℕ,
        ((List.range n).map fun j => Rule30Prize.center (T + j)).HasPeriod P
  ```

- *Sources.* [Mathlib]; critic.

**[8] fc-bridge: the formal-conjectures statement and Wolfram's statement.**
- *Statement.* Problem 1 is equivalent to `Rule30.centerColumn_not_eventually_periodic` in
  google-deepmind/formal-conjectures (`FormalConjectures/Other/Rule30.lean`, commit 7db2ea3 of
  2026-10-14). That file's `state t i` is our `cell t i`, and it quantifies ∃p ∃N where we quantify
  ∃T ∃P. Problem 1 is also equivalent to Wolfram's 2019 formal statement, read as intended: there
  are no p ≥ 1 and i with c(t + p) = c(t) for all t > i.
- *Caveat.* As printed, Wolfram's formula is degenerate [W19]. It is
  `NotExists[{p, i}, ForAll[t, t > i, c[t + p] == c[t]]]`, with
  `c[t_] := CellularAutomaton[30, {{1}, 0}, {t, {{0}}}]`. Two things go wrong. First, p = 0 is not
  excluded, so the literal `NotExists` is false. Second, `c[t]` is the list of the first t + 1
  values: Mathematica returns `c[5]` = {1, 1, 0, 1, 1, 1} (checked by the critic). So for p ≥ 1 the
  two sides are lists of different lengths. The intended reading needs p ≥ 1 and `Last[c[t]]`.
- *Proof route.* Prove `state t = fun i => cell t i` by induction (each step is `rfl`), then
  reorder the quantifiers. For Wolfram's form, t > i ⟺ t ≥ i + 1. This is an identity transfer.
- *Difficulty.* Trivial.
- *Lean.* Proved in the library (batch 2: `TransformsSeeds.problem1_iff_fc`, `problem1_iff_wolfram` and
  `problem1_iff_wolfram_last`; the batch-2 module also proves the literal reading degenerate).
  Before batch 2 the formal-conjectures form had a scratch proof, using only the axiom `Quot.sound`,
  and the Wolfram form was stated:

  ```lean
  namespace FC
  def step (row : ℤ → Bool) : ℤ → Bool := fun i => xor (row (i - 1)) (row i || row (i + 1))
  def state : ℕ → ℤ → Bool
    | 0 => fun i => decide (i = 0)
    | t + 1 => step (state t)
  def centerColumn (t : ℕ) : Bool := state t 0
  theorem problem1_iff_fc : Rule30Prize.Problem1 ↔
      ¬ ∃ p : ℕ, 0 < p ∧ ∃ N : ℕ, ∀ t : ℕ, N ≤ t → centerColumn (t + p) = centerColumn t
  end FC
  theorem problem1_iff_wolfram : Rule30Prize.Problem1 ↔
      ¬ ∃ p i : ℕ, 0 < p ∧ ∀ t, i < t → Rule30Prize.center (t + p) = Rule30Prize.center t
  ```

- *Sources.* [FC], [W19]; critic (Mathematica check).

**[14] pi2-normal-form: Π⁰₂ form, cofinal periods, Diophantine form.**
- *Statement.*
  - (a) For all T and all P ≥ 1 there is t ≥ T with c(t + P) ≠ c(t). Since c is primitive
    recursive, Problem 1 is a Π⁰₂ sentence and its negation is Σ⁰₂. Each instance (T, P) is Σ⁰₁,
    so finite computation can settle it. `Rule30Window` and `Rule30FactorWindow` are kernel-checked
    bundles of such instances.
  - (b) For every k ≥ 1, c has no eventual period k!. Any family of periods that is cofinal under
    divisibility works.
  - (c) The graph of c is Diophantine: there is a polynomial equation in n, y and further unknowns
    that has a solution exactly when y = c(n). So Problem 1 is a ∀∃ sentence about polynomial
    equations. Wolfram raises the
    possibility that Problem 1 is independent of PA or ZFC [W19]. In busy-beaver language, Problem 1
    says that a particular machine "beeps" infinitely often [Aar20].
- *Proof route.*
  - (a) Push the negation inward.
  - (b) An eventual period P is also an eventual period P!, since P divides P!.
  - (c) DPRM is not needed (critic, own reasoning). Mathlib already has Matiyasevich's
    exponentiation `Dioph.pow_dioph`, together with `Dioph.div_dioph`, `Dioph.mod_dioph`,
    `Dioph.sub_dioph` and `Dioph.dvd_dioph`. One rule-30 step on integer rows is
    Φ(x) = x ⊕ (2x ∨ 4x) ([25]; [NKS] p. 1160). Bitwise operations are Diophantine through binomial
    coefficients:
    - the bits of x are a subset of those of y iff C(y, x) is odd (Lucas [Luc78],
      `Choose.choose_modEq_prod_range_choose`);
    - a ∧ b = 0 iff C(a + b, a) is odd (Kummer [Kum52], `Nat.Prime.emultiplicity_choose`);
    - C(n, k) = ⌊(u + 1)ⁿ/uᵏ⌋ mod u for u > 2ⁿ.

    To iterate Φ, code the whole history in one number. Let w = 2n + 4. Then
    c(n) = ⌊H / 2^(nw + n)⌋ mod 2, where H is the unique number with H mod 2^w = 1,
    H < 2^((n+1)w) and ⌊H / 2^w⌋ = Φ(H mod 2^(nw)). Rows satisfy a(t) < 2^(2t+1), so they never
    spill into the next block, and induction forces H = Σ_t a(t)·2^(tw).
- *Difficulty.* Trivial for (a) and (b). (c) is moderate: elementary but long, several hundred
  lines by the critic's estimate. Earlier drafts rated (c) hard and listed DPRM as missing, which
  overstated the gap.
- *Lean.* (a) and (b): proved in the library (batch 2: `TransformsSeeds.problem1_iff_pi2`,
  `problem1_iff_forall_exists_refutes`, `problem1_iff_cofinal_periods` and
  `problem1_iff_factorial_periods`). Before batch 2, (a) had a scratch proof and (b) was stated.
  (c) is proved in [DiophantineGraph](Rule30Equivalents/DiophantineGraph.lean), in the graph form
  the critic suggests; it covers both colors, so it gives the ∀∃ form directly
  (`problem1_iff_forall_exists_poly`: one polynomial p with p(n, y, x) = 0 solvable iff y = c(n)).
  - `sub_iff_odd_choose`: Lucas mod 2. `choose_eq`: C(n, k) is digit k of (u + 1)ⁿ in base
    u = 2ⁿ + 1. With `Dioph.pow_dioph` this makes bit inclusion Diophantine.
  - `or_iff` and `xor_iff`, from the half adder x + y = (x ⊕ y) + 2(x ∧ y), make one step Φ
    Diophantine (`Φ_iff`).
  - `center_iff`: the history H has blocks of width w = 2n + 4. The conditions H mod 2^w = 1 and
    ⌊H/2^w⌋ = Φ(H mod 2^(nw)) force block t to be row a(t), by induction, because Φ acts block by
    block while rows stay below 2^(2t+1). Then c(n) is bit nw + n of H.

  ```lean
  theorem problem1_iff_pi2 : Rule30Prize.Problem1 ↔
      ∀ T P : ℕ, 0 < P → ∃ t, T ≤ t ∧ Rule30Prize.center (t + P) ≠ Rule30Prize.center t
  theorem problem1_iff_factorial_periods : Rule30Prize.Problem1 ↔
      ∀ k : ℕ, ¬ ∃ T, ∀ t, T ≤ t → Rule30Prize.center (t + (k + 1).factorial) = Rule30Prize.center t
  theorem center_diophFn :
      Dioph.DiophFn fun v : Fin 1 → ℕ => if Rule30Prize.center (v 0) then 1 else 0
  theorem problem1_iff_forall_exists_poly : ∃ (β : Type) (p : Poly (Option (Fin 1) ⊕ β)),
      (∀ n y, (if center n then 1 else 0) = y ↔ ∃ x, p (Sum.elim (Option.elim' y fun _ => n) x) = 0) ∧
      (Problem1 ↔ ∀ T P, 0 < P → ∃ t, T ≤ t ∧ ∃ x x', (p(t + P, 1, x) = 0 ∧ p(t, 0, x') = 0) ∨ …)
  ```

- *Sources.* [W19]; [NKS] p. 1160; [Dav73]; [Aar20]; [Luc78]; [Kum52]; critic (the coding
  argument).

**[25] nks-integer-rows: rows as integers ([NKS] p. 871).**
- *Statement.* Let a(0) = 1 and a(t + 1) = a(t) ⊕ (2a(t) ∨ 4a(t)) (OEIS A110240; one step is
  A269160, n ↦ n ⊕ (2n ∨ 4n)). Then cell(t, p) is bit t − p of a(t), so c(t) is bit t of a(t).
  Problem 1 ⟺ t ↦ bit t of a(t) is not EP.
- *Proof route.* Induction on t with the core lemmas `Nat.testBit_xor`, `Nat.testBit_or` and
  `Nat.testBit_shiftLeft`. The catalog's `Rule30Window.stepRow` and `row_testBit` encode rows with
  the opposite bit order. This is an identity transfer.
- *Why it is useful.* Fast evaluation and certificates. It also gives a 2-adic reading:
  Φ(x) = x ⊕ (2x ∨ 4x) is a T-function (bit k of Φ(x) depends only on bits ≤ k of x), and c(t) is
  bit t of Φᵗ(1). See [26] and Section 7.
- *Checks.* A Lean `#eval` reproduces 60 bits of A051023. Python reproduces 400 bits against a
  direct simulation (own computation, repeated by the critic).
- *Difficulty.* Easy.
- *Lean.* Proved in the library: `IntegerRows.problem1_iff_integer_rows`, and in the T-function
  language `TFunction.problem1_iff_orbit`. The original scratch statement was the following; the
  `let` avoids exponential evaluation.

  ```lean
  def nksRow : ℕ → ℕ
    | 0 => 1
    | t + 1 => let a := nksRow t; a ^^^ (2 * a ||| 4 * a)
  theorem problem1_iff_nksRow : Rule30Prize.Problem1 ↔
      ¬ Rule30Jen.EventuallyPeriodic (fun t => (nksRow t).testBit t)
  ```

- *Sources.* [NKS] p. 871 note; [W19]; OEIS A110240, A269160, A051023.

**[26] diagonal-array: the main diagonal of the right-diagonal array.**
- *Statement.* Let A(j, t) = cell(t, t − j), the cell at depth j from the right edge. It satisfies
  A(0, t) = 1, A(1, t) = [t odd], A(j + 2, 0) = 0 and
  A(j + 2, t + 1) = A(j + 2, t) ⊕ (A(j + 1, t) ∨ A(j, t)). Each row j is purely periodic with a
  period that *divides* 2^j. The least periods for j = 0, 1, 2, … are
  1, 2, 2, 4, 8, 8, 16, 32, 32, 64, 64, 64, 64, 64, 64, 128, … (OEIS A094605). The main diagonal is
  the center column: c(t) = A(t, t) (OEIS A363343). Problem 1 ⟺ the main diagonal of this array is
  not EP.
- *Correction.* Earlier versions said "period 2^j", but that is only an upper bound. The least
  period is 2, not 4, at j = 2, and it is 64 for j = 9, …, 14 (critic; recomputed here for j ≤ 15).
- *Proof route.* A equals the catalog's `Rule30Diagonals.R` by induction (`R_zero`, `R_one_succ`,
  `R_step`); then apply `center_eq_R`. A shorter route goes through [25] (the critic's own
  observation):
  - A(j, t) is bit j of a(t), so row j is bit j of the orbit of 1 under Φ.
  - Bit k of Φ(x) is x_k ⊕ (x_{k−1} ∨ x_{k−2}), so Φ permutes ℤ/2^(j+1).
  - The orbit of 1 there is purely periodic. Modulo 2 its length is 1, and each further bit at
    most doubles it, so modulo 2^(j+1) the length divides 2^j.
  - The cycle lengths of 1 under Φ modulo 2^(j+1) reproduce A094605 for j ≤ 15.

  This explains the odometer of [CPY07]: in the frame moving with the right edge, the orbit closure
  of the seed is the 2-adic odometer, and c is the diagonal of an odometer orbit. It also puts [25]
  and [26] one lemma apart. Both routes are identity transfers. The odometer itself is proved in
  [Odometer](Rule30Equivalents/Odometer.lean), for every nonzero finite configuration: rule 30 acts
  on the rows read from the right edge as the bijective isometry G(y)_j = y_j ⊕ (y_{j−1} ∨ y_{j−2})
  (Φ on binary expansions), and ψ_a(α)_j = bit j of Φ^(α mod 2^j)(a) is a closed embedding of ℤ₂
  onto the orbit closure of the right-edge reading of a, with ψ_a(α + 1) = G(ψ_a(α))
  (`isClosedEmbedding_ψ`, `range_ψ`, `ψ_add_one`; the seed is a = 1, `isClosedEmbedding_seed`).
  Injectivity: a repeat of all bits with period 2^(m−1) would give Φ^(2^(m−1))(a) = a, but Φ
  increases every nonzero number.

  The critic's argument is proved in [TFunction](Rule30Equivalents/TFunction.lean), for every
  starting value a, not only 1:
  - bit j of Φ(x) is x_j ⊕ (x_{j−1} ∨ x_{j−2}) (`testBit_Phi`);
  - Φ permutes ℤ/2ⁿ and is injective on ℕ (`mod_of_Phi_mod`, `Phi_injective`);
  - bit j of Φᵗ(a) has period dividing 2^j in t (`testBit_orbit_periodic`);
  - Φ^(2^j) is the identity modulo 2^(j+1) (`orbit_two_pow_mod`).

  Row t of the configuration whose cells at 0, −1, −2, … are the bits of a is Φᵗ(a)
  (`testBit_orbit`). The CA form, for every configuration that is white right of some cell, is
  `Rule30FiniteDiagonals.Rd_periodic`.

  The least periods follow from Klimov and Shamir's cycle theory, proved in
  [TFunctionCycles](Rule30Equivalents/TFunctionCycles.lean) for every invertible T-function. If bit i
  of f(x) is xᵢ ⊕ ψᵢ(x mod 2ⁱ), the cycle length of x modulo 2ⁿ starts at 1 and doubles at level i
  exactly when the parity of ψᵢ around the cycle modulo 2ⁱ is odd (`lift_iff`,
  `iterate_mod_iff_dvd`). For Φ, ψᵢ(y) = y_{i−1} ∨ y_{i−2}, and the rows 0, …, j of the array return
  to their values at time 0 exactly at the multiples of that cycle length for x = 1
  (`seed_rows_return_iff`). An `#eval` of it gives 1, 2, 2, 4, 8, 8, 16, 32, 32, 64 for
  j = 0, …, 9, the start of A094605.
  For every a ≠ 0 the cycle length of a modulo 2ⁿ is unbounded (`per_unbounded`): Φ raises the
  top bit of every nonzero number by two. So every nonzero finite configuration has the same
  infinite cycle structure at its right edge as the seed.
- *Difficulty.* Easy.
- *Lean.* Proved in the library: `IntegerRows.problem1_iff_diagArray`, with the periodicity of each
  row (`IntegerRows.diagArray_row_periodic`, period 2^j) and the T-function reading
  `TFunction.testBit_orbit_periodic`. The original scratch statement, with the bridge to [25], was
  the following.

  ```lean
  def diagArray : ℕ → ℕ → Bool
    | 0, _ => true
    | 1, t => decide (t % 2 = 1)
    | _ + 2, 0 => false
    | j + 2, t + 1 => xor (diagArray (j + 2) t) (diagArray (j + 1) t || diagArray j t)
  theorem problem1_iff_diagArray : Rule30Prize.Problem1 ↔
      ¬ Rule30Jen.EventuallyPeriodic (fun t => diagArray t t)
  theorem diagArray_eq_testBit (j t : ℕ) : diagArray j t = (nksRow t).testBit j
  ```

- *Sources.* [Row06]; [CPY07]; [Ner26a] and [Ner26b] (unrefereed); OEIS A363343, A094605; the
  catalog's `Rule30Diagonals`; critic (the T-function argument).

**[54] black-wall: the column next to a black wall** (new, 2026-10-17).
- *Statement.* Let a(y) = y ⊕ (2y ∨ 4y ∨ 3). This is one rule-30 step of the half-line whose two
  cells beyond the edge are frozen, with the first one black. Then Φᵗ(1) = 2·aᵗ(0) + 1, so
  c(t) = bit t − 1 of aᵗ(0) for t ≥ 1. Problem 1 ⟺ t ↦ bit t of a^(t+1)(0) is not EP. In words:
  the center column of the seed is the column at distance t − 1 from a black wall moving right at
  speed 1, read on the half-line that starts white.
- *Proof route.* Φ never changes the lowest bit. On odd numbers it continues as the automaton state
  that follows a 1, which is a: Φ(2y + 1) = 2·a(y) + 1, and Φ(2y) = 2·Φ(y). Induct on t.
- *Why it is useful.* a is one of the three states of rule 30's transducer, which generate automaton
  group 2369 (Section 7.9). This form places Problem 1 inside the family of frozen-boundary readouts
  of the stronger statement in Section 4.
- *Lean.* Proved in the library: `AutomatonGroup.problem1_iff_black_wall`, from `Phi_two_mul_add_one`
  and `orbit_one_eq_wall`.
- *Sources.* Own observation (2026-10-17); [BGK+08] for the automaton.

### 3.2 Real numbers and Diophantine approximation

**[1] binary-irrational: the binary number 0.c(0)c(1)c(2)…₂ is irrational.**
- *Statement.* x₂ = Σ_{t≥0} c(t)·2^−(t+1) = 0.11011100110001011001…₂
  = 0.862389783947384048640800246086751128108532963624… (OEIS A365254). Problem 1 ⟺ x₂ is
  irrational.
- *Proof route.* This is the classical theorem that a real number is rational iff its expansion in
  an integer base is eventually periodic.
  - EP ⟹ rational: by the geometric series, x₂ = (N_T + N/(2^P − 1))/2^T.
  - Rational ⟹ EP. If x₂ = p/q, the tail values x_t = 2ᵗx₂ − N_t lie in the finite set
    (1/q)ℤ ∩ [0, 1], so x_i = x_j for some i < j. If c has infinitely many 1s, then
    c(t) = [2x_t > 1] and x_{t+1} = 2x_t − c(t) are functions of x_t, so c has period j − i from
    i on. Otherwise c is eventually 0. This case split handles double expansions such as
    0.0111…₂ = 0.1₂.
- *Difficulty.* Easy.
- *Lean.* Proved (library), for every base B ≥ 2 at once.

  ```lean
  -- Rule30Equivalents/BinaryIrrational.lean, namespace Rule30Equivalents.BinaryIrrational
  theorem eventuallyPeriodic_iff_not_irrational {B : ℕ} (hB : 2 ≤ B) (b : ℕ → Bool) :
      EventuallyPeriodic b ↔
        ¬ Irrational (∑' t, (if b t then (1 : ℝ) else 0) / (B : ℝ) ^ (t + 1))
  noncomputable def centerBinary : ℝ := ∑' t, (if c t then 1 else 0) / 2 ^ (t + 1)
  theorem problem1_iff_irrational_binary : Rule30Prize.Problem1 ↔ Irrational centerBinary
  ```

  The proof uses Mathlib's `Irrational`, `exists_rat_of_not_irrational`, `Rat.not_irrational`,
  `tsum_geometric_two'` and `Set.Finite.exists_lt_map_eq_of_forall_mem`. Mathlib lacks
  "eventually periodic digits ⟺ rational" for arbitrary digits ℕ → Fin b, which would be a good
  upstream contribution.
- *Consequences.* The kernel bound T + P ≥ 16359 gives x₂ ≠ p/q for every q ≤ 16359. Write p/q in
  lowest terms with q = 2^a·q′, q′ odd. The expansion has preperiod a and period
  ord_{q′}(2) ≤ q′ − 1, so T + P ≤ q − 1. The dyadic case q′ = 1 is excluded because c is not
  eventually constant. (Own reasoning, from two surveys.)
- *Data.* Wolfram found no period in the first 10⁹ bits [W19]. A shift scan adds the p-extent
  (project round 2, 2026-10-23): for every p ≤ 2^18 some t ≤ 3,932,157 has c(t) ≠ c(t + p) within
  the first 2^22 bits, and no p ≤ 2^17 agrees with the last comparable bit of the first 2^24
  bits. The Berlekamp–Massey profile of [5] gives the stronger finite bound T + P ≥ 2,097,152
  (data, not kernel-checked).
- *Sources.* [HW] ch. IX; [Dic19] ch. VI, for the history: Wallis (1685), Lambert, Euler, and Gauss,
  *Disquisitiones* art. 312 ff.; [W19]; OEIS A365254, A092539.

**[2] base-b-irrational: every integer base, `Real.ofDigits`, the Cantor function.**
- *Statement.* For each integer B ≥ 2, Problem 1 ⟺ x_B = Σ c(t)·B^−(t+1) is irrational. Examples:
  the decimal number 0.11011100110001011001…₁₀, and x₃ = 0.462345072609503417371211…. The same
  holds for Mathlib's `Real.ofDigits` of the digit sequence c, and for
  `Cardinal.cantorFunction (1/B) c`, which equals B·x_B.
- *Proof route.* As in [1]. For B ≥ 3 the 0/1 expansion is unique.
- *Caution.* Only positional readings in an integer base are equivalent.
  - Σ c(t)/t! is irrational, and Σ c(t)·2^−t! is a Liouville number, for *every* 0/1 sequence
    with infinitely many 1s. These say nothing about Problem 1.
  - In a non-integer base the statement changes. In base φ (the golden ratio) the blocks 100 and
    011 have the same value; for Pisot bases β > 2 see [48].
- *Difficulty.* Easy.
- *Lean.* Series form: proved (library). `Real.ofDigits` form: proved (library),
  `Realization.problem1_iff_irrational_ofDigits`. Cantor-function form: proved (library),
  `Realization.problem1_iff_irrational_cantorFunction`.

  ```lean
  -- library, namespace Rule30Equivalents.BinaryIrrational
  theorem problem1_iff_irrational_base {B : ℕ} (hB : 2 ≤ B) :
      Rule30Prize.Problem1 ↔ Irrational (∑' t, (if c t then (1 : ℝ) else 0) / (B : ℝ) ^ (t + 1))
  noncomputable def centerDecimal : ℝ := ∑' t, (if c t then 1 else 0) / 10 ^ (t + 1)
  theorem problem1_iff_irrational_decimal : Rule30Prize.Problem1 ↔ Irrational centerDecimal
  -- library, namespace Rule30Equivalents.Realization; `[NeZero b]` follows from `hb`, but the
  -- digits `0, 1 : Fin b` in the statement need it as an instance
  theorem problem1_iff_irrational_ofDigits (b : ℕ) [NeZero b] (hb : 2 ≤ b) : Rule30Prize.Problem1 ↔
      Irrational (Real.ofDigits (b := b) fun t => if Rule30Prize.center t then 1 else 0)
  -- library, namespace Rule30Equivalents.Realization
  theorem problem1_iff_irrational_cantorFunction (b : ℕ) (hb : 2 ≤ b) : Rule30Prize.Problem1 ↔
      Irrational (Cardinal.cantorFunction (1 / (b : ℝ)) Rule30Prize.center)
  ```

- *Mathlib.* `Real.ofDigits`, `Real.ofDigitsTerm`, `Real.digits` and `Real.ofDigits_digits`
  (Analysis/Real/OfDigits.lean); `Cardinal.cantorFunction` (Analysis/Real/Cardinality.lean).
- *Sources.* [HW] ch. IX; [Mathlib].

**[16] integer-digits: the binary form without real numbers.**
- *Statement.* There are no p, q ∈ ℕ with q > 0 such that c(t) = ⌊2^(t+1)·p/q⌋ mod 2 for all t.
- *Proof route.* Write r_t = 2ᵗp mod q. Then ⌊2^(t+1)p/q⌋ mod 2 = ⌊2r_t/q⌋ and
  r_{t+1} = 2r_t mod q. This is a finite deterministic system, so such digit sequences are EP.
  Conversely, if c is EP, then c is the greedy expansion of its rational value, because c is not
  eventually 1 (`center_not_eventually_constant`). This form also fits the Mathlib-free core
  catalog.
- *Difficulty.* Easy.
- *Lean.* Proved in the library (batch 2: `NumberTheory.problem1_iff_not_rational_digits`, with a version for
  every base B ≥ 2 and one for base 10). Before batch 2 it was stated:

  ```lean
  theorem problem1_iff_not_rational_digits : Rule30Prize.Problem1 ↔
      ¬ ∃ p q : ℕ, 0 < q ∧ ∀ t, Rule30Prize.center t = decide (2 ^ (t + 1) * p / q % 2 = 1)
  ```

- *Sources.* As for [1]; own reasoning for the integer form.

**[11] continued-fraction.**
- *Statement.* The regular continued fraction of x₂ does not terminate.
- *Proof route.* Euclid's algorithm terminates iff the number is rational
  (`GenContFract.terminates_iff_rat`); then apply [1].
- *Difficulty.* Trivial.
- *Data.* x₂ = [0; 1, 6, 3, 1, 2, 1, 18, 7, 1, 19, 2, 39, 1, 2, 41, 1, 1, 1, 1, …]. The
  number-theory survey certified 9666 partial quotients from 32768 bits, and the critic certified
  1165 from 4000 bits. The Lévy statistic 1.1745 and the geometric mean 2.649 of the quotients are
  close to the almost-everywhere values 1.1866 and 2.6854 (Khinchin's constant). These are the
  statistics of a typical real number (own computation).
- *Lean.* Proved in the library (batch 2: `NumberTheory.problem1_iff_cf_not_terminates`). Before batch 2 it
  had a 5-line scratch proof:

  ```lean
  theorem problem1_iff_cf_not_terminates : Rule30Prize.Problem1 ↔ ¬ (GenContFract.of x₂).Terminates
  ```

- *Sources.* [Kh64]; [HW] ch. X; [Mathlib]
  (Algebra/ContinuedFractions/Computation/TerminatesIffRat.lean).

**[12] dirichlet-liouville: Diophantine approximation.**
- *Statement.* Problem 1 ⟺ infinitely many rationals q satisfy abs(x₂ − q) < 1/den(q)²
  ⟺ `LiouvilleWith 2 x₂`. The latter means: for some C there are infinitely many n with some m such
  that x₂ ≠ m/n and abs(x₂ − m/n) < C/n².
- *Proof route.* The first form is Mathlib's Dirichlet–Hurwitz equivalence
  (`Real.infinite_rat_abs_sub_lt_one_div_den_sq_iff_irrational`). For the second:
  - (⇐) `LiouvilleWith.irrational`, since 2 > 1;
  - (⇒) Dirichlet's approximations have unbounded denominators, so C = 1 works.
- *Difficulty.* Easy.
- *Lean.* Proved in the library (batch 2: `NumberTheory.problem1_iff_dirichlet`,
  `problem1_iff_liouvilleWith_two`, and `problem1_iff_liouvilleWith` for every exponent
  1 < p ≤ 2). Before batch 2 the Dirichlet form had a scratch proof and the `LiouvilleWith` form
  was stated:

  ```lean
  theorem problem1_iff_dirichlet : Rule30Prize.Problem1 ↔
      {q : ℚ | |x₂ - q| < 1 / (q.den : ℝ) ^ 2}.Infinite
  theorem problem1_iff_liouvilleWith_two : Rule30Prize.Problem1 ↔ LiouvilleWith 2 x₂
  ```

- *Note.* The statement that the irrationality exponent μ(x₂) is 2 is a stronger open statement
  (Section 4). It implies Problem 1 (`IrrationalityExponent.problem1_of_exponentTwo`) and holds for
  almost every configuration (`IrrationalityExponent.ae_exponentTwo_trace`).
- *Sources.* [Bug12]; [Mathlib] (NumberTheory/DiophantineApproximation/Basic.lean,
  NumberTheory/Transcendental/Liouville/LiouvilleWith.lean).

**[10] circle-rotation: x₂ on the circle ℝ/ℤ.**
- *Statement.* Problem 1 ⟺ each of:
  - x₂ has infinite additive order in ℝ/ℤ;
  - the integer multiples n·x₂ mod 1 are dense, i.e. rotation by x₂ is minimal;
  - x₂ is not a preperiodic point of the doubling map D(y) = 2y mod 1.

  Binary digits conjugate the shift on {0,1}^ℕ to D, so the last form is [3] seen on the circle.
- *Proof route.* The first two forms follow from [1] via Mathlib's `AddCircle` lemmas. For D,
  2ⁿy = 2ᵐy ⟺ (2ⁿ − 2ᵐ)y = 0, which means finite order. Conversely, a point of finite order q has
  its D-orbit inside the finite q-torsion subgroup (`AddCircle.finite_torsion`).
- *Difficulty.* Easy.
- *Lean.* Proved in the library (batch 2: `NumberTheory.problem1_iff_infinite_order`,
  `problem1_iff_addOrderOf_eq_zero`, `problem1_iff_dense_multiples` and
  `problem1_iff_doubling_not_preperiodic`). Before batch 2 the first two forms had scratch proofs
  and the third was stated:

  ```lean
  theorem problem1_iff_infinite_order : Rule30Prize.Problem1 ↔
      ¬ IsOfFinAddOrder (x₂ : AddCircle (1 : ℝ))
  theorem problem1_iff_dense_multiples : Rule30Prize.Problem1 ↔
      DenseRange (· • (x₂ : AddCircle (1 : ℝ)) : ℤ → AddCircle (1 : ℝ))
  theorem problem1_iff_doubling_not_preperiodic : Rule30Prize.Problem1 ↔
      ∀ m, (fun y : AddCircle (1 : ℝ) => 2 • y)^[m] (x₂ : AddCircle (1 : ℝ)) ∉
        Function.periodicPts (fun y : AddCircle (1 : ℝ) => 2 • y)
  ```

- *Mathlib.* `AddCircle.not_isOfFinAddOrder_iff_forall_rat_ne_div` and `AddCircle.finite_torsion`
  (Topology/Instances/AddCircle/Defs.lean); `AddCircle.denseRange_zsmul_coe_iff`
  (…/DenseSubgroup.lean); `Function.periodicPts`. `AddCircle.ergodic_nsmul` says that the doubling
  map is ergodic, which says nothing about the particular point x₂.
- *Sources.* [HW] ch. IX and ch. XXIII (Kronecker's theorem); [Mathlib].

**[39] lagrange: the continued fraction with partial quotients 1 + c(t).**
- *Statement.* θ = [1 + c(0); 1 + c(1), 1 + c(2), …] = 2.369341998498446546347094895460664321077441…
  is not a quadratic irrational. θ is irrational whatever c is, and it is badly approximable since
  its partial quotients are at most 2.
- *Proof route.* Euler–Lagrange: a real number has an eventually periodic regular continued
  fraction iff it is a quadratic irrational ([HW] §10.12; Theorem 177 is Lagrange's direction). The
  partial quotients 1 + c(t) are EP iff c is. Both directions of Euler–Lagrange are needed. This
  form is not a corollary of [1]: it needs its own hub, "eventually periodic continued fraction ⟺
  quadratic irrational" (critic).
- *Difficulty.* Hard. Grep finds neither direction of Euler–Lagrange in Mathlib.
- *Lean.* Proved in the library (2026-10-18): `Lagrange.problem1_iff_not_quadratic`, with
  `θ = Lagrange.theta`, the limit of the convergents of `[1 + c(0); 1 + c(1), …]`.
  - `Lagrange.digit_periodic_iff` is Euler–Lagrange for every irrational: its digits are eventually
    periodic iff it satisfies a nontrivial integer quadratic.
    - Euler: a periodic tail is a fixed point of an integer Möbius map, transported back with
      determinant ±1.
    - Lagrange: the leading coefficients `F(Pₙ, Qₙ)` are bounded because `|x Qₙ - Pₙ| ≤ 1/Qₙ`.
      The discriminant is invariant. So two complete quotients coincide.
  - `Lagrange.cfValue` builds the number with prescribed digits `bₖ ≥ 1`. It is irrational
    because Euclid's algorithm terminates on rationals.
  - The statement below, from the survey, used Mathlib's `GenContFract` convergents. The library
    uses its own continuants.

  ```lean
  noncomputable def θ : ℝ :=
    Filter.limUnder Filter.atTop
      (GenContFract.mk (1 + if Rule30Prize.center 0 then (1 : ℝ) else 0)
        (Stream'.Seq.ofStream fun t => ⟨1, 1 + if Rule30Prize.center (t + 1) then (1 : ℝ) else 0⟩)).convs
  theorem problem1_iff_not_quadratic : Rule30Prize.Problem1 ↔
      ¬ ∃ A B C : ℤ, (A, B, C) ≠ (0, 0, 0) ∧ (A : ℝ) * θ ^ 2 + B * θ + C = 0
  ```

- *Note.* "θ is transcendental" is only conditional: it would follow from Problem 1 if c were
  automatic [Bug13].
- *Sources.* [HW] §10.12; [AB05]; [Bug13].

**[49] minkowski: Minkowski's question-mark function** (new).
- *Statement.* Let r_1, r_2, … be the run lengths of c (OEIS A327983: 2, 1, 3, 2, 2, 3, 1, 1, …),
  and let y = ?⁻¹(x₂), where ? is Minkowski's question-mark function. Then
  y = [0; 1, r_1, r_2, r_3, …] ≈ 0.734976078619449957611903590207, and Problem 1 ⟺ y is not a
  quadratic irrational.
- *Proof route.* ? is an increasing homeomorphism of [0, 1]. It maps ℚ onto the dyadic rationals
  and the quadratic irrationals onto the non-dyadic rationals [Min04], [Sal43]. Its formula
  ?([0; a_1, a_2, …]) = 0.0^(a_1 − 1) 1^(a_2) 0^(a_3) …₂ gives y = [0; 1, r_1, r_2, …], because c
  starts with a black run. Since c is not eventually constant, x₂ is not dyadic and y is
  irrational. Hence y is quadratic ⟺ x₂ ∈ ℚ ⟺ c is EP. Without ?, the same argument is
  Euler–Lagrange plus "run lengths EP ⟺ c EP", i.e. [39] and [29] combined.
- *Difficulty.* Hard: it needs Euler–Lagrange or the properties of ?.
- *Data.* ?(y), computed from 400 partial quotients, agrees with x₂ to 38 digits (critic). The 30
  digits of y above were recomputed here from 3000 bits.
- *Lean.* Proved in the library (2026-10-18): `Minkowski.problem1_iff_minkowski_not_quadratic`.
  `yMink` is the reciprocal of `Lagrange.cfValue (1, r₁, r₂, …)`, so it is quadratic iff that number
  is. By Euler–Lagrange this holds iff the run lengths are eventually periodic, which is [29]. The
  identity y = ?⁻¹(x₂) is proved as `Minkowski.questionMark_yMink : ?(y) = x₂`. Mathlib has no
  `?`, so `questionMark` defines it on the irrationals of (0, 1) by the Denjoy–Salem series over
  the Gauss-map digits; summing x₂ run by run gives the same alternating series
  Σ (−1)^k 2^−(r₁ + ⋯ + r_k).
  The critic's statement was (`runLen` from `Nat.nth` of the change points):

  ```lean
  noncomputable def changePt (k : ℕ) : ℕ :=
    Nat.nth (fun t => Rule30Prize.center t ≠ Rule30Prize.center (t + 1)) k
  noncomputable def runLen : ℕ → ℕ
    | 0 => changePt 0 + 1
    | k + 1 => changePt (k + 1) - changePt k
  noncomputable def yMink : ℝ :=
    Filter.limUnder Filter.atTop
      (GenContFract.mk (0 : ℝ)
        (Stream'.Seq.ofStream fun k => ⟨1, if k = 0 then (1 : ℝ) else (runLen (k - 1) : ℝ)⟩)).convs
  theorem problem1_iff_minkowski_not_quadratic : Rule30Prize.Problem1 ↔
      ¬ ∃ A B C : ℤ, (A, B, C) ≠ (0, 0, 0) ∧ (A : ℝ) * yMink ^ 2 + B * yMink + C = 0
  ```

- *Sources.* [Min04]; [Sal43]; [Den38]; OEIS A327983; critic.

**[50] other-expansions: Engel, Sylvester, factorial base, Lüroth** (new).
- *Statement.* Problem 1 ⟺ any of the following holds for x₂:
  - its Engel expansion x₂ = 1/a_1 + 1/(a_1a_2) + …, with a_k nondecreasing, is infinite;
  - its Sylvester (greedy Egyptian-fraction) expansion is infinite;
  - its factorial-base expansion x₂ = Σ_{k≥2} d_k/k!, with 0 ≤ d_k < k, does not terminate;
  - its Lüroth expansion is not eventually periodic.
- *Proof route.* These are classical facts about the expansions; then apply [1].
  - In the Engel and Sylvester algorithms, a remainder p/q is followed by (ap − q)/q and
    (ap − q)/(aq) respectively, with a = ⌈q/p⌉. Since (a − 1)p < q, the numerator ap − q is smaller
    than p, so a rational number has finite expansions.
  - A rational p/q has a factorial-base expansion that stops by k = q, because q divides q!.
  - Lüroth (1883): a number is rational iff its Lüroth expansion is finite or eventually periodic.
  - An irrational number has infinite expansions in all four systems.
- *Difficulty.* Easy.
- *Data.* Engel digits of x₂: 2, 2, 3, 3, 22, 79, 250, 1981, 2718, 23578, 140432, …. Sylvester
  denominators: 2, 3, 35, 2062, 17860254, 1527430603451300, …. The critic computed these from 1500
  bits, and they were rechecked here from 3000 bits.
- *Lean.* The Engel and Sylvester forms are proved in the library:
  `Expansions.problem1_iff_engel_infinite` and `Expansions.problem1_iff_sylvester_infinite`, from
  `irrational_iff_engelRem_ne_zero` and `irrational_iff_sylvesterRem_ne_zero` (for x ≥ 0, each
  expansion is infinite iff x is irrational). The factorial-base form is proved too:
  `Expansions.problem1_iff_factorial_infinite`, with the remainders fract(k!·x₂) and the expansion
  identity `fract_eq_sum`. The Lüroth form is proved as well (2026-10-17), with the expansion defined in the
  library: `Expansions.problem1_iff_luroth_not_eventuallyPeriodic`. Its core is
  `lurothDigits_eventuallyPeriodic_iff`: for x ∈ (0, 1] the digits are eventually periodic iff x is
  rational. A rational orbit stays among the points k/q. Points with the same digits are within
  2⁻ⁿ for every n, so periodic digits make a remainder the fixed point of an affine map with
  rational coefficients. The critic's original statement was:

  ```lean
  noncomputable def engelRem : ℕ → ℝ
    | 0 => x₂
    | n + 1 => if engelRem n = 0 then 0 else (⌈(engelRem n)⁻¹⌉ : ℝ) * engelRem n - 1
  theorem problem1_iff_engel_infinite : Rule30Prize.Problem1 ↔ ∀ n, engelRem n ≠ 0
  ```

- *Sources.* [Gal76]; [ERS58]; [Lur83].

**[48] pisot-base: irrationality in a Pisot base such as 1 + √2** (new).
- *Statement.* For every Pisot number β > 2, for example β = 1 + √2 or 2 + √3, Problem 1 ⟺
  x_β = Σ_t c(t)·β^−(t+1) ∉ ℚ(β). For β = 1 + √2: there are no rationals a, b with
  x_β = a + b√2.
- *Proof route.* Because β > 2, every tail value lies in [0, 1/(β − 1)] ⊂ [0, 1), so the 0/1 digits
  form the greedy β-expansion of x_β. If c is EP, x_β ∈ ℚ(β) by the geometric series. Conversely,
  Bertrand [Ber77] and Schmidt [Sch80] proved that for a Pisot number β every element of
  ℚ(β) ∩ [0, 1) has an eventually periodic greedy β-expansion. There is also a self-contained
  route (critic, own reasoning). β is an algebraic integer, so the tails
  x_t = βᵗx_β − Σ_{s<t} c(s)β^(t−1−s) lie in (1/q)ℤ[β]. Each x_t lies in [0, 1/(β − 1)] and its
  conjugates are bounded, so only finitely many values occur, and c(t) = ⌊βx_t⌋.
- *Caution.* For 1 < β < 2, for example the golden ratio, 0/1 expansions are not unique and the
  equivalence fails. For a Salem number β > 2, x_β ∉ ℚ(β) still implies Problem 1
  (`PisotNumbers.problem1_of_not_mem_adjoin`, for every real β > 2), but the converse is open
  (Schmidt's conjecture).
- *Difficulty.* Moderate.
- *Lean.* Proved in the library for every Pisot number β > 2, in
  [PisotNumbers](Rule30Equivalents/PisotNumbers.lean): `problem1_iff_not_mem_adjoin`, from
  `eventuallyPeriodic_iff_mem_adjoin` (Schmidt's theorem for 0/1 digits). `IsPisot β` says that β
  is a real algebraic integer > 1 whose other complex conjugates, the roots of `minpoly ℤ β`, lie
  in the open unit disk; ℚ(β) is `IntermediateField.adjoin ℚ {β}`, a number field. The lattice
  argument above runs in it: q·x_t is an algebraic integer; an embedding φ : ℚ(β) → ℂ either fixes
  β, and is then the inclusion (`IntermediateField.adjoin_algHom_ext`), or sends it into the unit
  disk; so all conjugates of q·x_t are bounded, and Mathlib's
  `NumberField.Embeddings.finite_of_norm_le` leaves finitely many values. The case β = 1 + √2 is
  the corollary `PisotBase.problem1_iff_not_mem_Q_sqrt_two`, with explicit a + b√2 coordinates:
  1 + √2 is a root of X² − 2X − 1 (`isPisot_β`), and ℚ(1 + √2) = ℚ(√2) (`mem_adjoin_iff`).
  Mathlib has no β-expansions and no Pisot numbers.

  ```lean
  noncomputable def xβ (β : ℝ) : ℝ := ∑' t, (if Rule30Prize.center t then (1 : ℝ) else 0) / β ^ (t + 1)
  theorem problem1_iff_not_mem_Q_sqrt_two :
      Rule30Prize.Problem1 ↔ ¬ ∃ a b : ℚ, xβ (1 + Real.sqrt 2) = a + b * Real.sqrt 2
  ```

- *Sources.* [Sch80]; [Ber77]; critic (the specialization to 0/1 digits with β > 2, and the lattice
  argument).

### 3.3 p-adic numbers

**[15] two-adic.**
- *Statement.* α = Σ c(t)·2ᵗ ∈ ℤ₂ is not in ℚ. An integer form works for every prime p, reading the
  0/1 digits p-adically: there are no a, b ∈ ℤ with b ≠ 0 and pⁿ ∣ b·S_p(n) − a for all n, where
  S_p(n) = Σ_{t<n} c(t)·pᵗ.
- *Proof route.* A p-adic integer is rational iff its digits are EP [Gou97], [Kob].
  - EP ⟹ rational: α = A + p^T·B/(1 − p^P).
  - Rational ⟹ EP. The congruences say bα = a in ℤ_p. First divide out the power of p in b; it
    must also divide a. The remainders a_n = (a − b·S_n)/pⁿ are then integers with
    a_{n+1} = (a_n − b·c(n))/p and abs(a_{n+1}) ≤ (abs(a_n) + abs(b))/2, so eventually
    abs(a_n) ≤ abs(b). Since p ∤ b, c(n) ≡ a_n·b⁻¹ (mod p), and the system is finite and
    deterministic. The original survey sketch assumed p ∤ b; the synthesis added the reduction.
- *Difficulty.* Easy for the integer congruence form; moderate for the `PadicInt` form, because
  Mathlib has no digit expansions in ℤ_[p].
- *Consequence.* Any fraction a/b with b odd that equals α must satisfy log₂abs(a) + b ≥ 16357.
  This is the number-theory survey's own derivation from T + P ≥ 16359.
- *Lean.* Proved in the library (batch 2: `TwoAdic.problem1_iff_padic_irrational`,
  `problem1_iff_padicValue_irrational`, `problem1_iff_padic_int`, `problem1_iff_no_pow_dvd` for
  every base p ≥ 2, and `problem1_iff_no_odd_fraction`). Before batch 2 it was stated:

  ```lean
  noncomputable def α₂ : ℤ_[2] := ∑' t, (if Rule30Prize.center t then (1 : ℤ_[2]) else 0) * 2 ^ t
  theorem problem1_iff_padic_irrational : Rule30Prize.Problem1 ↔ ∀ q : ℚ, (α₂ : ℚ_[2]) ≠ q
  def S (p n : ℕ) : ℤ := ∑ t ∈ Finset.range n, (if Rule30Prize.center t then 1 else 0) * (p : ℤ) ^ t
  theorem problem1_iff_padic_int (p : ℕ) (hp : p.Prime) : Rule30Prize.Problem1 ↔
      ¬ ∃ a b : ℤ, b ≠ 0 ∧ ∀ n, (p : ℤ) ^ n ∣ b * S p n - a
  ```

- *Mathlib.* `PadicInt` (ℤ_[p]), `Padic`, `PadicInt.toZModPow` and `PadicInt.appr`. Summability
  comes from the additive form of `NonarchimedeanGroup.multipliable_of_tendsto_cofinite_one`.
  Missing: digit expansions in ℤ_[p].
- *Sources.* [Gou97]; [Kob]; [KG97].

**[30] fcsr-complexity: 2-adic complexity.**
- *Statement.* For every bound B there is an n such that no pair a, b with b ≠ 0, abs(a) ≤ B and
  abs(b) ≤ B satisfies 2ⁿ ∣ b·S_2(n) − a. Equivalently, no feedback-with-carry shift register
  (FCSR) generates c.
- *Proof route.* Only finitely many pairs satisfy the bound. If every n had one, a single pair
  would work for infinitely many n, hence for all n, since the congruences descend to smaller n.
  Then apply [15]. Klapper and Goresky's rational approximation algorithm is the 2-adic analogue of
  Berlekamp–Massey.
- *Difficulty.* Easy, given [15].
- *Data.* The log₂ of the 2-adic complexity stays close to n/2 for n ≤ 65536, as for a random
  sequence. On a dense grid (166 points: every n ≤ 24, the powers of two, 65530–65542 and every
  512th n ≤ 65536) the deviation reaches 6.18 bits at n = 59456; eight random control sequences
  on the same grid give maxima 2.88–6.29 bits (mean 4.42), seven of them above the 3.6 bits
  earlier reported from a coarser grid. The powers of two all sit slightly below n/2 in the
  controls as well — order statistics of the minimum, not column structure. (Project round 2,
  2026-10-23.)
- *Lean.* Proved in the library (batch 2: `TwoAdic.problem1_iff_two_adic_complexity`,
  `problem1_iff_two_adic_complexity_odd` and `problem1_iff_padic_complexity`). Before batch 2 it was
  stated, with S as in [15]:

  ```lean
  theorem problem1_iff_two_adic_complexity : Rule30Prize.Problem1 ↔
      ∀ B : ℕ, ∃ n, ¬ ∃ a b : ℤ, b ≠ 0 ∧ |a| ≤ B ∧ |b| ≤ B ∧ (2 : ℤ) ^ n ∣ b * S 2 n - a
  ```

- *Sources.* [KG97]; [GK12].

### 3.4 Algebra: linear recurrences, power series, coding theory

**[5] series-f2-lfsr: rational over F₂, LFSRs, linear complexity.**
- *Statement.* Each of the following is equivalent to Problem 1:
  - C(X) = Σ c(t)·Xᵗ ∈ F₂[[X]] is not rational: there is no Q ≠ 0 with Q·C a polynomial, or
    equivalently no P, Q with Q(0) ≠ 0 and C = P·Q⁻¹;
  - c satisfies no eventual linear recurrence over F₂;
  - no linear feedback shift register (LFSR) generates c, run from time 0 and with singular
    feedback allowed;
  - the linear complexity profile of c is unbounded.

  Function-field form: ξ = Σ c(t)·X^−(t+1) ∈ F₂((1/X)) is irrational, i.e. its continued fraction
  over F₂[X] is infinite. Berlekamp–Massey is Euclid's algorithm on ξ, and the jumps of the
  profile are the degrees of the partial quotients [Mil75], [WS79], [Dor87].
- *Proof route.* If c is EP with (T, P), then (1 − X^P)·C is a polynomial. Conversely, Q·C = P
  gives a recurrence starting from the lowest nonzero coefficient of Q, and pigeonhole on windows
  gives periodicity [LN97] ch. 8, [Mas69].
- *Difficulty.* Easy.
- *Lean.* Proved (library), six forms. Each is also proved as a general theorem about every
  b : ℕ → Bool.

  ```lean
  -- Rule30Equivalents/PowerSeriesF2.lean, namespace Rule30Equivalents.PowerSeriesF2
  noncomputable def series (b : ℕ → Bool) : PowerSeries (ZMod 2) :=
    PowerSeries.mk (fun t => if b t then 1 else 0)
  theorem problem1_iff_series_not_rational : Rule30Prize.Problem1 ↔
      ¬ ∃ P Q : Polynomial (ZMod 2), Q ≠ 0 ∧
        (Q : PowerSeries (ZMod 2)) * series c = (P : PowerSeries (ZMod 2))
  theorem problem1_iff_no_lfsr : Rule30Prize.Problem1 ↔
      ∀ d : ℕ, ¬ ∃ a : Fin d → ZMod 2, ∀ t,
        ((if c (t + d) then 1 else 0 : ZMod 2)) = ∑ i, a i * (if c (t + i) then 1 else 0)
  theorem problem1_iff_linear_complexity_unbounded : Rule30Prize.Problem1 ↔
      ∀ d : ℕ, ∃ n : ℕ, ¬ ∃ a : Fin d → ZMod 2, ∀ t, t + d < n →
        ((if c (t + d) then 1 else 0 : ZMod 2)) = ∑ i, a i * (if c (t + i) then 1 else 0)
  -- also problem1_iff_series_not_rational_coeff_zero, problem1_iff_series_ne_mul_inv,
  --   problem1_iff_no_eventual_linear_recurrence
  ```

- *Data.* L(c↾10⁶) = 499,998, and abs(L_n − n/2) ≤ 9.5 for all n ≤ 10⁶; two independent runs agree
  (project round 1; algebra survey). This is the profile of a random sequence. Since L_n ≤ T + P,
  it gives T + P ≥ 499,998 (data, not kernel-checked). A profile near n/2 does not separate random
  from automatic sequences: the Thue–Morse sequence also deviates from n/2 by at most 1 [MeWi17].
  Round 2 (2026-10-23): L(c↾2^22) = 2,097,152, and |L_n − n/2| ≤ 3 at every power of two up to
  2^22, so T + P ≥ 2,097,152 (data, not kernel-checked); computed with a big-integer
  Berlekamp–Massey cross-checked against a textbook reference on structured and random sequences.
- *Sources.* [LN97] ch. 8; [Mas69]; [Mil75]; [WS79]; [Dor87]; [Nie88]; [Rue86]; [W85c]; [W86].

**[17] rational-any-field: rationality and recurrences over any field.**
- *Statement.* Let K be any field, and read c in {0, 1} ⊆ K. Problem 1 ⟺ C(X) ∉ K(X), i.e. no
  Q ≠ 0 in K[X] has Q·C ∈ K[X] ⟺ c satisfies no constant-coefficient linear recurrence over K
  (Mathlib's `LinearRecurrence`, valid from n = 0).
- *Proof route.* The F₂ argument works verbatim. The lowest nonzero coefficient of Q is invertible,
  so the recurrence gives c(m) from the preceding window. The values lie in {0, 1} and 0 ≠ 1 in K,
  so the window takes finitely many states. Fatou's theorem is not needed. Invertibility is not
  needed either: for the lowest nonzero coefficient q, q·0 = 0 ≠ q·1, so the same argument works
  over every nontrivial commutative ring, such as ℤ or ℤ/4ℤ.
- *Difficulty.* Easy.
- *Data.* Over ℚ the Hankel rank of c is at least 44,999 ([32]; algebra survey).
- *Lean.* Proved in the library (batch 2: `LinearRelations.problem1_iff_series_not_rational`,
  `problem1_iff_no_linearRecurrence` and `problem1_iff_no_eventual_linearRecurrence`). The
  rational form now holds over every nontrivial commutative ring (`eventuallyPeriodic_of_mul_eq`
  through the window lemma `WordsAutomata.eventuallyPeriodic_of_determined`). Before
  batch 2 the recurrence form had a scratch proof (logic survey, any field) and the power-series
  form was stated. Here `series K` is the scratch definition above, not the library's
  `PowerSeriesF2.series`.

  ```lean
  theorem problem1_iff_series_not_rational (K : Type*) [Field K] : Rule30Prize.Problem1 ↔
      ¬ ∃ P Q : Polynomial K, Q ≠ 0 ∧ (Q : PowerSeries K) * series K = (P : PowerSeries K)
  theorem problem1_iff_no_linearRecurrence (K : Type*) [Field K] : Rule30Prize.Problem1 ↔
      ∀ E : LinearRecurrence K, ¬ E.IsSolution (fun t => if Rule30Prize.center t then (1 : K) else 0)
  ```

- *Mathlib.* `LinearRecurrence`, `LinearRecurrence.IsSolution`, `LinearRecurrence.mkSol` and
  `LinearRecurrence.charPoly` (Algebra/LinearRecurrence.lean).
- *Sources.* [LN97] ch. 8; [Fat06].

**[44] linear-relations: independent shifts, infinite-dimensional span, no annihilating polynomial**
(new).
- *Statement.* Fix any field K, and let c_K(t) be 1 in K if c(t) = 1 and 0 otherwise. Problem 1 ⟺
  each of:
  - the shifted sequences σⁿc_K = (c_K(n + t))_t, n ∈ ℕ, are linearly independent in K^ℕ;
  - they span an infinite-dimensional subspace;
  - c_K is not a torsion element of the K[X]-module K^ℕ in which X acts as the shift: no nonzero
    Q ∈ K[X] has Q(σ)c_K = 0.

  The unbounded Hankel rank of [32] is a fourth form of the same statement.
- *Proof route.* (⇐) If c is EP with (T, P), then σ^(T+P)c = σ^Tc. So the shifts are not injective,
  hence not independent (`LinearIndependent.injective`). They span at most T + P dimensions, and
  (X^(T+P) − X^T)·c_K = 0. (⇒) A nontrivial relation Σ_{i≤d} a_i σⁱc_K = 0 with a_d ≠ 0 is a linear
  recurrence valid from n = 0, and [17] makes c EP. (Own reasoning, standard.)
- *Difficulty.* Easy. No determinants are involved, so Kronecker's theorem is not needed.
- *Data.* σ⁰c, …, σ^16358 c are pairwise distinct (kernel-checked, `Rule30FactorWindow`). The
  nonvanishing Hankel determinants of [32] show that σ⁰c, …, σ^44998 c are linearly independent
  over ℚ already on a finite window (data).
- *Lean.* Proved in the library (batch 2: `LinearRelations.problem1_iff_shifts_linearIndependent`,
  `problem1_iff_shift_span_not_finiteDimensional` and `problem1_iff_not_torsion`). Before batch 2
  the first two were stated (critic):

  ```lean
  def cK (K : Type*) [Field K] (t : ℕ) : K := if Rule30Prize.center t then 1 else 0
  theorem problem1_iff_shifts_linearIndependent (K : Type*) [Field K] :
      Rule30Prize.Problem1 ↔ LinearIndependent K (fun n : ℕ => fun t : ℕ => cK K (n + t))
  theorem problem1_iff_shift_span_not_finiteDimensional (K : Type*) [Field K] :
      Rule30Prize.Problem1 ↔
        ¬ FiniteDimensional K (Submodule.span K (Set.range fun n : ℕ => fun t : ℕ => cK K (n + t)))
  ```

- *Mathlib.* `LinearIndependent`, `LinearIndependent.injective`, `Submodule.span`,
  `FiniteDimensional`, `LinearRecurrence`, and `Module.AEval` for the K[X]-module view. Nothing
  essential is missing.
- *Sources.* [Kro1881]; [Gan59] ch. XV; [LN97] ch. 8; critic.

**[32] hankel: Hankel matrices, unbounded rank and nonvanishing determinants (Kronecker).**
- *Statement.* Let H = (c(i + j))_{i,j≥0} and H_n = det(c(i + j))_{0≤i,j<n}. Problem 1 ⟺ the
  n × n leading blocks of H have unbounded rank, over any field ⟺ H_n ≠ 0 for infinitely many n
  (over ℤ) ⟺ H_n is odd for infinitely many n (over F₂).
- *Proof route.*
  - Rank form (critic, own reasoning). (⇐) If c is EP with (T, P), every block has rank at most
    T + P. (⇒) Suppose every leading block has rank at most r. For n ≥ r + 1 let V_n ⊆ K^(r+1) be
    the space of linear relations among σ⁰c, …, σ^r c on the window [0, n). The V_n form a
    decreasing chain of nonzero subspaces, so they stabilize at a nonzero space. A vector in it is
    a global relation, and [44] applies.
  - Determinant forms. (⇐, easy) If c is EP with (T, P), rows T and T + P of the n × n matrix
    coincide once n > T + P. (⇒) Kronecker 1881: a power series over a field is rational iff its
    Hankel determinants vanish from some n on. Then apply [17] or [5].
  - Over F₂, the n with H_n ≠ 0 are exactly the values taken by the Berlekamp–Massey profile. Two
    surveys checked this numerically for n < 600, and the critic for n < 120.
  - "H_n is odd for *every* n" (a perfect linear complexity profile) is false: H_3 = −2, and the
    Wang–Massey criterion [WM86] fails at i = 2 (synthesis).
- *Difficulty.* Easy for the rank form. For the determinant forms, "⇐" is easy and "⇒" is hard,
  since it needs Kronecker's theorem.
- *Data.* H_1, …, H_12 = 1, −1, −2, 3, 2, −1, 0, 0, −1, −10, 4, 378 (exact arithmetic; rechecked by
  the critic). H_m ≠ 0 for 9 ≤ m < 45,000, checked modulo a large prime (algebra survey). "H_m ≠ 0
  for all m ≥ 9" is a stronger statement (Section 4).
- *Lean.* Proved in the library (batch 2: `LinearRelations.problem1_iff_hankel_rank_unbounded`,
  `problem1_iff_hankel_det`, `problem1_iff_hankel_det_zmod_two`, `problem1_iff_hankel_det_int` and
  `problem1_iff_hankel_det_odd`). Before batch 2 all forms were stated (the rank form by the
  critic), with the determinant forms kept as targets for Kronecker's theorem:

  ```lean
  theorem problem1_iff_hankel_rank_unbounded (K : Type*) [Field K] :
      Rule30Prize.Problem1 ↔
        ∀ r : ℕ, ∃ n : ℕ, r ≤ (Matrix.of fun i j : Fin n => cK K ((i : ℕ) + (j : ℕ))).rank
  def hankel (R : Type*) [CommRing R] (n : ℕ) : R :=
    (Matrix.of fun i j : Fin n => if Rule30Prize.center ((i : ℕ) + (j : ℕ)) then (1 : R) else 0).det
  theorem problem1_iff_hankel_int : Rule30Prize.Problem1 ↔ ∀ N, ∃ n, N ≤ n ∧ hankel ℤ n ≠ 0
  theorem problem1_iff_hankel_F2 : Rule30Prize.Problem1 ↔ ∀ N, ∃ n, N ≤ n ∧ hankel (ZMod 2) n ≠ 0
  ```

- *Mathlib.* `Matrix.det`, `Matrix.of` and `Matrix.rank`. Missing: Hankel matrices and Kronecker's
  criterion.
- *Sources.* [Kro1881]; [Sal63] ch. I; [Gan59] ch. XV; [WM86]; critic.

**[45] skolem-mahler-lech: the black times as a zero set** (new).
- *Statement.* Problem 1 ⟺ S = {t : c(t) = 1} is not the zero set {t : u(t) = 0} of any linear
  recurrence sequence u over ℚ, or equivalently over any field of characteristic 0. The same
  equivalence holds over every finite field, where every linear recurrence sequence is EP.
- *Proof route.* (⇐) If c is EP, then u(t) = 1 − c(t) is EP. So it satisfies the linear
  recurrence u(t + T + P) = u(t + T), and its zero set is S. (⇒) By Skolem–Mahler–Lech, the zero
  set of a linear recurrence sequence in characteristic 0 is a finite set plus finitely many full
  arithmetic progressions, so it is EP as a set, and c would be EP. The finite-field version is
  elementary, since the windows take finitely many values. Over infinite fields of characteristic
  p, zero sets need not be EP, so that version is strictly stronger ([Der07]; Section 4).
- *Difficulty.* Hard: it needs Skolem–Mahler–Lech, which Mathlib lacks (proved here).
- *Lean.* Proved in the library
  ([SkolemMahlerLech](Rule30Equivalents/SkolemMahlerLech.lean)). The finite-field version is
  `LinearRelations.problem1_iff_not_zero_set`.

  ```lean
  theorem problem1_iff_not_LRS_zero_set :
      Rule30Prize.Problem1 ↔ ∀ (E : LinearRecurrence ℚ) (u : ℕ → ℚ), E.IsSolution u →
        {t | u t = 0} ≠ {t | c t = true}
  ```

  - `skolem_mahler_lech`: the zero set of a linear recurrence sequence over ℚ is eventually
    periodic. The proof is the p-adic one.
    - If a₀ = 0, the shifted sequence solves a shorter recurrence (induction on the order).
    - Otherwise pick an odd prime p dividing no denominator of the coefficients or initial values,
      nor the numerator of a₀. The state vectors are Aⁿv for a companion matrix A over ℤ_p that is
      invertible mod p.
    - A mod p has finite order m, so Aᵐ = 1 + pB (`exists_pow_eq_one_add`). Then
      u(r + mn) = Σₖ C(n, k) pᵏ βₖ, and C(n, k) = (n)ₖ / k! turns this into a power series in n.
      Its coefficients tend to 0 because ‖pᵏ / k!‖ ≤ p^(−k/2) by Legendre's formula.
  - `Strassmann.strassmann`: a nonzero power series over ℚ_p with coefficients tending to 0 has
    finitely many zeros in the unit ball. The proof divides by x − α at a zero α, which lowers the
    last index of a largest coefficient (Strassmann 1928). So along each residue class r mod m the
    zeros are finite or everything, and the zero set is eventually periodic.
- *Sources.* [Sko34]; [Mah35]; [Lec53]; [Str28]; [Der07].

**[31] p-recursive: polynomial-coefficient recurrences and D-finiteness.**
- *Statement.* Problem 1 ⟺ there is no recurrence Σ_{i≤d} p_i(n)·c(n + i) = 0 for n ≥ N with
  p_i ∈ ℤ[n] not all zero ⟺ C(X) is not D-finite over ℚ(X).
- *Proof route (elementary).* Let D be the largest degree of the p_i, and let a_i be their
  coefficients of n^D. Dividing the recurrence by n^D shows that Σ a_i·c(n + i) is O(1/n). It takes
  finitely many values, so it is eventually 0. That is a constant-coefficient recurrence, and [17]
  applies. Classical results: a finite-valued P-recursive sequence has a rational generating
  function [vdPS96], and P-recursive ⟺ D-finite [Sta80].
- *Consequence* (number-theory survey). If Problem 1 holds, methods that need a linear differential
  equation have nothing to work with. This covers Siegel–Shidlovskii and Apéry- or Beukers-type
  Padé approximations.
- *Difficulty.* Moderate.
- *Lean.* The recurrence form is proved in the library: `Holonomic.problem1_iff_not_pRecursive`,
  from `Holonomic.eventuallyPeriodic_iff_pRecursive`. The proof avoids the estimate above: past some
  point every window recurs, so for each window a the polynomial Σ aᵢ pᵢ has infinitely many roots
  and vanishes, and its top coefficients give a constant-coefficient recurrence. The D-finite form
  is proved in [DFinite](Rule30Equivalents/DFinite.lean): `DFinite.problem1_iff_not_dFinite`, from
  `eventuallyPeriodic_iff_dFinite`. An eventually periodic column has a rational series G/H, which
  solves H G · F′ − (G′H − G H′) · F = 0. Conversely, take the largest order i₀ with q_{i₀} ≠ 0 and a
  bound K on the degrees. Coefficient t + K of the equation is a polynomial in t once the window
  b(t), …, b(t + K + r) is fixed. A recurring window makes it vanish identically, and its
  coefficient of t^{i₀} is the constant-coefficient relation Σ_{m ≤ K} q_{i₀, K−m} · b(t + i₀ + m) = 0.

  ```lean
  theorem problem1_iff_not_pRecursive : Rule30Prize.Problem1 ↔
      ¬ ∃ (d N : ℕ) (p : Fin (d + 1) → Polynomial ℤ), (∃ i, p i ≠ 0) ∧
        ∀ n, N ≤ n → ∑ i : Fin (d + 1),
          (p i).eval (n : ℤ) * (if Rule30Prize.center (n + i) then 1 else 0) = 0
  ```

- *Sources.* [vdPS96]; [BC17]; [Sta80].

**[38] fatou: transcendence over ℚ(z).**
- *Statement.* C(z) = Σ c(t)zᵗ is transcendental over ℚ(z), equivalently over ℂ(z).
- *Proof route.* Fatou 1906: a power series with integer coefficients that converges in abs(z) < 1
  is either rational or transcendental. Combine this with [17]. Alternatively, algebraic ⟹ D-finite
  [Sta80], then apply [31].
- *The characteristic matters.* Over F_p(z), algebraic ⟺ p-automatic (Christol). So transcendence
  over F₂(z) is strictly stronger than Problem 1 (Section 4).
- *Difficulty.* Moderate along the D-finite route; Fatou's theorem is not needed.
- *Lean.* Proved in the library ([AlgebraicDFinite](Rule30Equivalents/AlgebraicDFinite.lean)).

  ```lean
  theorem problem1_iff_transcendental : Rule30Prize.Problem1 ↔
      Transcendental (RatFunc ℚ) ((LinearRelations.series ℚ c : PowerSeries ℚ) : ℚ⸨X⸩)
  ```

  - The sufficient direction, over every field, is `Transcendence.problem1_of_transcendental`, from
    `isAlgebraic_of_eventuallyPeriodic` (a rational series P/Q satisfies Q·s − P = 0 over K(X)).
  - `exists_dfinite_of_isAlgebraic`: over a field of characteristic zero, a power series F algebraic
    over K[X] is D-finite [Com64], [Sta80].
    - Take P of least degree d with P(F) = 0. Then P_Y(F) ≠ 0, and the chain rule gives
      P_Y(F)·F′ = −P^∂(F), where P^∂ differentiates the coefficients.
    - P_Y(F) is algebraic, so P_Y(F)·G(F) = r with r ∈ K[X] nonzero (Mathlib's
      `IsAlgebraic.exists_nonzero_eq_adjoin_mul`). Hence r·F′ ∈ K[X][F], and by induction
      r^m·F^(k) ∈ K[X][F] for every k.
    - A power of the leading coefficient of P puts each element of K[X][F] into the K[X]-span of
      1, F, …, F^(d−1). So d + 1 scaled derivatives lie in a module spanned by d elements, and the
      strong rank condition makes them linearly dependent.
  - `isAlgebraic_polynomial_of_isAlgebraic`: algebraic over ℚ(X) as a Laurent series means algebraic
    over ℚ[X] as a power series. Then `DFinite.eventuallyPeriodic_of_dFinite` ([31]) finishes.

- *Mathlib.* `Transcendental`, `IsAlgebraic`, `RatFunc`, `LaurentSeries`, `RatFunc.coeToLaurentSeries`
  and the scoped instance `RatFunc.liftAlgebra`. Missing: Fatou's theorem, and "algebraic ⟹ D-finite"
  (proved here).
- *Sources.* [Fat06]; [Com64]; [Sta80]; [BC17].

**[28] nlfsr: nonlinear feedback shift registers and maximum-order complexity.**
- *Statement.* Problem 1 ⟺ each of:
  - there are no m and F : {0,1}^m → {0,1} with c(i + m) = F(c(i), …, c(i + m − 1)) for all i;
  - the maximum-order complexity M_n(c) tends to ∞;
  - for every m, some two equal length-m windows of c have different successors.

  The same holds for the k-th order complexity (feedback functions of algebraic degree ≤ k) for
  each fixed k ≥ 1. The case k = 0 must be excluded: constant feedback generates only eventually
  constant sequences, so every non-constant periodic sequence has infinite 0-th order complexity
  (critic).
- *Proof route.* If c is EP with (T, P), windows of length T + P determine the next bit, because
  both successors lie in the periodic part at the same phase. For k ≥ 1 this feedback can even be
  linear: c(t + T + P) = c(t + T). Conversely, any feedback function makes the dynamics finite and
  deterministic. Each lower bound M_n ≥ m + 1 has a two-position certificate that `decide` can
  check.
- *Difficulty.* Easy.
- *Data* (algebra survey). M_n = 37 at n = 10⁶ and 44 at n = 10⁷; for random bits 2·log₂ n ≈ 40
  and 46.5.
- *Lean.* Proved in the library (batch 2: `WordsAutomata.problem1_iff_no_feedback_shift_register`,
  from some time on). The first two bullets are proved as stated:
  `problem1_iff_no_feedback_from_zero` (an eventually periodic sequence is generated from position 0
  by a register of length T + P) and `problem1_iff_maxOrderComplexity_tendsto`, with
  `maxOrderComplexity b n` the least m at which equal windows of length m inside the prefix of
  length n have equal successors (consistency is upward closed, `PrefixConsistent.mono`). The
  k-th order version, for every k ≥ 1, is `AlgebraicDegree.problem1_iff_no_feedback_degreeLE`:
  an EP column is generated from position 0 by the linear feedback c(i + T + P) = c(i + T), whose
  algebraic normal form has degree 1 (`DegreeLE`, through the ANF coefficients `coef`). For almost
  every configuration the center column has M_n = 2 log₂ n (1 + o(1)), the growth the data above
  show for the seed ([MaxOrderComplexity](Rule30Equivalents/MaxOrderComplexity.lean),
  `ae_tendsto_maxOrderComplexity_trace`; along every line too). From above, M_n > L needs two equal
  windows of length L among the n² pairs, each pair equal with probability 2^−L even when the
  windows overlap. From below, the birthday paradox: of the K² pairs of a block among the first K
  blocks of length B and a block among the next K, each agrees in its first B − 1 letters and
  differs in the last with probability 2^−B, any two such events are independent, and the
  second-moment method bounds the chance that none occurs by 2^B/K².

  ```lean
  theorem problem1_iff_no_nlfsr : Rule30Prize.Problem1 ↔
      ∀ m : ℕ, ¬ ∃ F : (Fin m → Bool) → Bool,
        ∀ i, Rule30Prize.center (i + m) = F (fun k => Rule30Prize.center (i + k))
  ```

- *Sources.* [JB89]; [Li24]; [AW85].

### 3.5 Complex analysis

**[41] natural-boundary: Szegő and Pólya–Carlson.**
- *Statement.* f(z) = Σ c(t)zᵗ has radius of convergence exactly 1, since c is bounded and not
  eventually 0. Problem 1 ⟺ f has no analytic continuation across any arc of the unit circle.
- *Proof route.* Szegő 1922: a power series with finitely many distinct coefficients that continues
  across some arc equals P(z)/(1 − z^m). Pólya–Carlson (Carlson 1921): a power series with integer
  coefficients and radius 1 is either rational or has the unit circle as natural boundary.
  Conversely, an EP sequence gives P(z)/(1 − z^P), which is meromorphic with poles only at roots of
  unity. Then apply [17] over ℂ.
- *Difficulty.* Hard: it needs Szegő's theorem or Pólya–Carlson, which Mathlib lacks (Szegő's
  theorem for 0/1 coefficients is proved here).
- *Lean.* Proved in the library ([Szego](Rule30Equivalents/Szego.lean)), through Szegő's theorem
  for 0/1 sequences, `Szego.eventuallyPeriodic_iff_continuation`.

  ```lean
  theorem problem1_iff_natural_boundary : Rule30Prize.Problem1 ↔
      ∀ z₀ : ℂ, ‖z₀‖ = 1 → ∀ r : ℝ, 0 < r → ¬ ∃ g : ℂ → ℂ,
        AnalyticOnNhd ℂ g (Metric.ball z₀ r) ∧
          ∀ z ∈ Metric.ball z₀ r, ‖z‖ < 1 → g z = NaturalBoundary.genFun c z
  ```

  - The sufficient direction ([NaturalBoundary](Rule30Equivalents/NaturalBoundary.lean),
    `problem1_of_natural_boundary`): if c has period P from time T, then on the unit disk
    (1 − z^P)·f(z) is a polynomial (`mul_genFun_eq`), so f continues as a rational function across
    the circle at z₀ = e^(iπ/P), where 1 − z₀^P = 2 (`exists_continuation`).
  - The coefficient identity ([SzegoContour](Rule30Equivalents/SzegoContour.lean)): rotate the arc
    to 1, so that a(n) = c(n)z₀ⁿ. For a monic W = Σ wⱼXʲ, Σⱼ wⱼ a(n + j) is (2πi)⁻¹ times the
    integral of the tail Tₙ(z) = Σₘ a(n + m)zᵐ against W(1/z)/z over a circle of radius ρ < 1
    (`circleIntegral_tail_mul`).
  - The contour: Cauchy's theorem on an annular sector, a rectangle in logarithmic coordinates
    (`sector_integral_eq`), moves the arc abs(arg z) ≤ τ out to a radius R > 1. There the tails
    continue as (g(z) − Σ_{j<n} aⱼzʲ)/zⁿ, at most abs(g(z)) + 1/(abs(z) − 1) (`norm_contTail_le`).
  - The polynomial: W(w) = W₀(w)(w − e^(iτ))(w − e^(−iτ)). The last two factors cancel the growth of
    the tails where the contour crosses the circle (`norm_contTail_mul_le`). W₀ is monic and at most
    2qᴰ, q < 1, on the reflected contour: the circle of radius 1/R and the part of the annulus
    1/R ≤ abs(w) ≤ 1/ρ where Re w ≤ abs(w) cos τ
    ([SzegoPolynomial](Rule30Equivalents/SzegoPolynomial.lean), `exists_notch_poly`). The classical
    proof gets W₀ from the logarithmic capacity of the notched disk, which is below 1. Mathlib has
    no capacity theory, so W₀ is explicit: wᴷᴰ · wᴰ T_D(ℓ(w)) up to a constant, with T_D the
    Chebyshev polynomial and ℓ(w) = (w² + (1 − κ)w + 1)/((1 + κ)w), κ = cos(τ/2), which maps the arc
    cos θ ≤ κ of the unit circle onto [−1, 1]. On the circle of radius 1/R the factor wᴷᴰ wins, and
    near the notch abs(ℓ(w) − 1) + abs(ℓ(w) + 1) ≤ 2 + O((abs(w) − 1)²).
  - The recurrence: so abs(Σⱼ wⱼ a(n + j)) ≤ C·qᴰ < 1/2 for every n
    (`SzegoContour.exists_approx_recurrence`), Q(X) = W(z₀X)/z₀ᵈ is a monic recurrence that c
    satisfies within 1/2, and c is eventually periodic
    ([ApproximateRecurrence](Rule30Equivalents/ApproximateRecurrence.lean),
    `eventuallyPeriodic_iff_approx_recurrence`): the candidates 0 and 1 for c(n + d) are 1 apart, so
    the window determines the next cell.
  - The disk form, the easy case of Szegő's theorem, is proved in
    [MeromorphicExtension](Rule30Equivalents/MeromorphicExtension.lean):
    `problem1_iff_no_meromorphic_extension`, Problem 1 ⟺ for no R > 1 and no polynomial Q ≠ 0 does
    Q·f extend holomorphically to abs(z) < R. The coefficients β(n) of Q·C take finitely many values
    (one per window of c), Cauchy's estimate on a circle of radius ρ ∈ (1, R) gives β(n) = O(ρ⁻ⁿ),
    so β is eventually 0 and C is rational ([17]). With Mathlib's `MeromorphicOn`:
    `problem1_iff_no_meromorphicOn`, Problem 1 ⟺ f agrees on the unit disk with no function
    meromorphic on a disk of radius R > 1; at each point x of a closed disk of radius ρ ∈ (1, R),
    some (z − x)ⁿ·g is analytic on a ball around x, finitely many balls cover the closed disk, and
    Q = ∏ (X − x)ⁿ clears the poles (`hasMeromorphicExtension_of_meromorphicOn`).
  - For almost every configuration the center column has the unit circle as natural boundary
    ([RandomNaturalBoundary](Rule30Equivalents/RandomNaturalBoundary.lean),
    `ae_circleIsNaturalBoundary_trace`; Steinhaus, Paley–Zygmund): along the radius to
    w = e^(iπ(2p+1)/(N+1)) the real part of 2f(tw) − 1/(1 − tw) is a weighted sum Σ tᵏ Re(wᵏ)(±1) of
    independent signs, with variance at least 1/(1 − t^(2N+2)) and fourth moment at most three times
    the squared variance, so by the Paley–Zygmund inequality it exceeds any bound near t = 1 with
    probability at least 1/6, and almost surely by Kolmogorov's zero-one law. These directions are
    dense, and a continuation across the circle at one of them would make the sum converge.
- *Mathlib.* `AnalyticOnNhd`, `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`,
  `FormalMultilinearSeries.radius`, `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`
  and `Polynomial.Chebyshev.T`. Missing: natural boundaries, logarithmic capacity, Szegő's theorem
  and Pólya–Carlson.
- *Sources.* [Sze22]; [Die57] (ch. X); [BEL08] (section 3); [Car21]; [Pol16]; [BC17] (its
  Theorem 1.1 states Szegő's theorem in this form);
  for random coefficients [Ste30]; [PZ32]; [Kah85].
  One survey cited Carlson's different 1921 paper, *Über ganzwertige Funktionen*; the correct one
  is [Car21].

### 3.6 Combinatorics on words and symbolic dynamics

**[3] shift-orbit: the shift orbit is infinite.**
- *Statement.* Problem 1 ⟺ the shifts σⁿc = (c(n + t))_t are pairwise distinct ⟺ there are
  infinitely many of them ⟺ c is not a preperiodic point of the shift map (no iterate of the
  shift sends it to a periodic point).
- *Proof route.* σ^(T+P)c = σ^Tc says exactly "period P from time T". Then use pigeonhole.
- *Difficulty.* Easy.
- *Lean.* Proved (library). Each form is also proved as a general theorem about every b.

  ```lean
  -- Rule30Equivalents/ShiftOrbit.lean, namespace Rule30Equivalents.ShiftOrbit
  theorem problem1_iff_infinite_shifts :
      Rule30Prize.Problem1 ↔ (Set.range (fun n : ℕ => fun t => c (n + t))).Infinite
  theorem problem1_iff_injective_shifts :
      Rule30Prize.Problem1 ↔ Function.Injective (fun n : ℕ => fun t => c (n + t))
  def shift (x : ℕ → Bool) : ℕ → Bool := fun t => x (t + 1)
  theorem problem1_iff_not_preperiodic :
      Rule30Prize.Problem1 ↔ ∀ m, shift^[m] c ∉ Function.periodicPts shift
  ```

  Mathlib's `SymbolicDynamics.FullShift.shift` gives the same orbit. A one-line bridge to it has a
  scratch proof (`problem1_iff_injective_fullShift`).
- *Data.* σ⁰c, …, σ^16358 c are pairwise distinct (kernel-checked, `Rule30FactorWindow`).
- *Sources.* [LM95]; [Mathlib] (Dynamics/PeriodicPts/Defs.lean, Dynamics/SymbolicDynamics/Basic.lean).

**[4] morse-hedlund: factor complexity.**
- *Statement.* Let p_c(n) be the number of distinct length-n factors (blocks) of c. Problem 1 ⟺
  p_c(n) ≥ n + 1 for all n ⟺ p_c is strictly increasing ⟺ p_c is unbounded.
- *Proof route.* This is the Morse–Hedlund theorem (1938), in the one-sided form of Coven–Hedlund
  (1973). Deleting the last letter maps the factors of length n + 1 onto those of length n, so p_c
  is non-decreasing. If p(m + 1) = p(m), every length-m factor has a unique right extension, so the
  window dynamics is a self-map of a finite set, and c is EP.
- *Difficulty.* Moderate.
- *Lean.* Proved (library), the full theorem in both directions.

  ```lean
  -- Rule30Equivalents/ShiftOrbit.lean
  def factors (b : ℕ → Bool) (n : ℕ) : Set (Fin n → Bool) :=
    Set.range (fun i : ℕ => fun j : Fin n => b (i + j))
  theorem problem1_iff_ncard_factors :
      Rule30Prize.Problem1 ↔ ∀ n, n + 1 ≤ (factors c n).ncard
  theorem problem1_iff_ncard_factors_lt_succ :
      Rule30Prize.Problem1 ↔ ∀ n, (factors c n).ncard < (factors c (n + 1)).ncard
  theorem problem1_iff_strictMono_ncard_factors :
      Rule30Prize.Problem1 ↔ StrictMono (fun n => (factors c n).ncard)
  theorem problem1_iff_ncard_factors_unbounded :
      Rule30Prize.Problem1 ↔ ∀ C, ∃ n, C < (factors c n).ncard
  ```

- *Data.* Kernel-checked: p_c(26) ≥ 16359. In the first 10⁷ bits p_c(n) = 2ⁿ for n ≤ 19, and 96
  of the 2^20 words of length 20 are absent, where a random model predicts about 76 (project
  data). Wolfram reports that every block of length k ≤ 22 occurs, the last of them by step
  58,671,803 [W19]. Round 2 (2026-10-23) reproduces that number exactly and extends the data:
  in the first 2^26 bits all 2^22 words of length 22 occur, the last at position 58,671,802
  (step 58,671,803); the covering times C(k) grow like 2^k·k·ln 2, the coupon-collector scale;
  and the absent words at k = 23, 24, 25 number 2,737, 305,474 and 4,536,800 against
  random-model predictions 2,814, 307,303 and 4,541,000 (model 2^k·(1−2^−k)^(N−k+1), the same
  as above).
- *Sources.* [MH38] Thms 7.3–7.4; [CH73]; [CN09] (its Theorem 4 states the one-sided form);
  [CN10].

**[13] orbit-closure.**
- *Statement.* The closure of {σⁿc : n ∈ ℕ} in {0,1}^ℕ, with the product topology, is infinite.
  Equivalently, it has an accumulation point.
- *Proof route.* Apply [3]: finite sets are closed in a T1 space.
- *Difficulty.* Trivial.
- *Data.* By the kernel results the closure has at least 16359 points.
- *Lean.* Proved in the library (batch 2: `WordsAutomata.problem1_iff_orbit_closure_infinite` and
  `problem1_iff_exists_accPt`). Before batch 2 it had a 6-line scratch proof:

  ```lean
  theorem problem1_iff_orbit_closure_infinite : Rule30Prize.Problem1 ↔
      (closure (Set.range fun n : ℕ => fun t => Rule30Prize.center (n + t))).Infinite
  ```

- *Sources.* [LM95]; [Kur03].

**[23] special-factors.**
- *Statement.* Problem 1 ⟺ for every n some word w of length n is right-special, meaning that both
  w0 and w1 occur in c. By König's lemma this is also ⟺ there is a left-infinite word all of whose
  suffixes are right-special.
- *Proof route.* For a one-sided binary word, p(n + 1) − p(n) is the number of right-special
  factors of length n; then apply [4]. For König's lemma, note that the right-special factors form
  a finitely branching tree under extension to the left.
- *Difficulty.* Easy.
- *Data.* In the first 10⁷ bits every word of length ≤ 18 is right-special (prefix data only).
- *Lean.* Proved in the library (batch 2: `WordsAutomata.problem1_iff_right_special` and
  `problem1_iff_right_special_branch`). Before batch 2 it was stated:

  ```lean
  def OccursThen (w : List Bool) (a : Bool) : Prop :=
    ∃ i : ℕ, (∀ j : Fin w.length, Rule30Prize.center (i + (j : ℕ)) = w.get j) ∧
      Rule30Prize.center (i + w.length) = a
  theorem problem1_iff_right_special : Rule30Prize.Problem1 ↔
      ∀ n, ∃ w : List Bool, w.length = n ∧ OccursThen w false ∧ OccursThen w true
  ```

- *Mathlib.* `exists_seq_covby_of_forall_covby_finite` (Order/KonigLemma.lean).
- *Sources.* [Cas97]; [CN10].

**[24] finite-certificates.**
- *Statement.* Problem 1 ⟺ for every N there are n and M such that more than N distinct length-n
  factors start below position M.
- *Why it is useful.* For fixed N the inner statement is Σ⁰₁, and it is equivalent to "no eventual
  period with T + P ≤ N". The reason is that for an EP c, sup_n p_c(n) = T_min + P_min (own
  reasoning, words survey, brute-force checked). `Rule30FactorWindow` is the kernel-checked
  instance N = 16358, with factor length 26 and M = 16384. The 10⁷-bit file gives N = 9,999,956 as
  data.
- *Proof route.* Apply [4], noting that every factor occurs in some finite prefix. For a concrete N
  the inner bound can be checked by `decide`.
- *Difficulty.* Easy.
- *Lean.* Proved in the library: `WordForms.problem1_iff_prefix_certificates`, from
  `ShiftOrbit.problem1_iff_ncard_factors_unbounded` and `WordForms.unbounded_iff_prefix_certificates`.

  ```lean
  theorem problem1_iff_prefix_certificates : Rule30Prize.Problem1 ↔
      ∀ N : ℕ, ∃ n M : ℕ, N < ((Finset.range M).image
        fun i => List.ofFn fun j : Fin n => Rule30Prize.center (i + j)).card
  ```

- *Sources.* [MH38]; [CH73]; [Project] (`Rule30FactorWindow`).

**[34] omega-limit.**
- *Statement.* The ω-limit set ω(c) of c under the shift is infinite. Equivalently, it contains a
  non-periodic point.
- *Width-1 trace view.* Let F be rule 30 on {0,1}^ℤ and Tr₀(x) = ((Fᵗx)₀)_t. Tr₀ is a factor map,
  and ω_σ(c) = Tr₀(ω_F(δ₀)), where δ₀ is the single seed (own reasoning, words survey; proved:
  `Genericity.image_trace_omegaLimit_seed`, from `image_omegaLimit_eq` for continuous
  semiconjugacies of compact spaces). So Problem 1 holds iff Tr₀(ω_F(δ₀)) is infinite
  (`Genericity.problem1_iff_trace_omegaLimit_seed_infinite`), iff some configuration in ω_F(δ₀) has
  a center column that is not periodic
  (`Genericity.problem1_iff_exists_omegaLimit_seed_not_periodic`). The set ω_F(δ₀) itself is
  infinite, since its right halves are Kopra's infinitely many limit points
  (`Genericity.infinite_omegaLimit_seed`; the same holds for every configuration with a leftmost
  black cell, `Genericity.infinite_omegaLimit`); Problem 1 asks for more, an infinite trace.
- *Proof route.* If c is EP, ω(c) is one periodic orbit. Conversely, a finite ω(c) is invariant, so
  it consists of periodic points. Choose L so that the length-(L − 1) prefixes separate those
  points. Eventually σᵗc shares its length-L prefix with some z_t ∈ ω(c), and this forces
  z_{t+1} = σz_t, so c is eventually a shifted periodic point (own reasoning, words survey).
- *Difficulty.* Moderate.
- *Lean.* Proved in the library (batch 2: `WordsAutomata.problem1_iff_omegaLimit_infinite`). Before batch 2 it
  was stated:

  ```lean
  theorem problem1_iff_omegaLimit_infinite : Rule30Prize.Problem1 ↔
      (omegaLimit Filter.atTop (fun (n : ℕ) (x : ℕ → Bool) => fun t => x (n + t))
        {Rule30Prize.center}).Infinite
  ```

- *Mathlib.* `omegaLimit`, `mem_omegaLimit_iff_frequently`, `isInvariant_omegaLimit` and
  `nonempty_omegaLimit` (Dynamics/OmegaLimit.lean).
- *Sources.* [Kop23]; [CFG10]; [LM95].

**[35] tail-language.**
- *Statement.* Let L∞(c) be the set of words that occur infinitely often in c, and p∞(n) the number
  of them of length n. Problem 1 ⟺ each of:
  - p∞(n) ≥ n + 1 for all n;
  - the two-sided subshift Ω(c) with language L∞(c) is infinite;
  - no Rauzy graph Γ_n of L∞(c) is a single cycle. (The Γ_n are strongly connected.)
- *Proof route.* L∞ is factorial and extendable on both sides. A flat step p∞(m + 1) = p∞(m) gives
  unique right extensions inside L∞. Only finitely many words of length m + 1 occur finitely often,
  and after the last such occurrence c follows the extension map. If c is EP with least period P,
  then p∞(n) = P for n ≥ P − 1. (Own reasoning, words survey; brute-force checked.)
- *Note.* No finite computation constrains L∞(c), yet this tail language alone decides every
  complexity form of Problem 1.
- *Difficulty.* Moderate.
- *Lean.* The complexity form is proved in the library (batch 2, beyond its assignment):
  `WordsAutomata.problem1_iff_tail_complexity`, with `tailFactors` defined through `∃ᶠ i in Filter.atTop`.
  The Rauzy-graph form is proved as strict growth of p∞ (a Rauzy graph is a single cycle exactly at a
  flat step): `TailLanguage.problem1_iff_tail_strictMono`, from `eventuallyPeriodic_iff_tail_flat`.
  The subshift form is proved: `TailLanguage.problem1_iff_tailSubshift_infinite`, from
  `infinite_tailSubshift_iff`. Here Ω(c) is `tailSubshift c`, the sequences ℤ → Bool all of
  whose windows lie in L∞(c). Every word of L∞(c) is a window of a point of Ω(c): take a cluster
  point, in the compact space ℤ → Bool, of the shifts of c that put an occurrence at 0
  (`exists_mem_tailSubshift`). The original statement of the complexity form was:

  ```lean
  def tailFactors (n : ℕ) : Set (Fin n → Bool) :=
    {w | ∀ N, ∃ i : ℕ, N ≤ i ∧ ∀ j : Fin n, Rule30Prize.center (i + (j : ℕ)) = w j}
  theorem problem1_iff_tail_complexity : Rule30Prize.Problem1 ↔
      ∀ n, n + 1 ≤ (tailFactors n).ncard
  ```

- *Sources.* [CN09]; [Rau83]; [MeSa17].

**[29] return-words: gaps and run lengths.**
- *Statement.* Problem 1 ⟺ each of the following is not EP:
  - the gaps between consecutive black cells (first differences of A327984);
  - the gaps between consecutive white cells (from A327985);
  - the run lengths (A327983);
  - for some recurrent word u (equivalently, for every one), the derived sequence of return words
    to u [Dur98].
- *Proof route.* There are infinitely many black and white cells
  (`center_not_eventually_constant`), so each of these sequences and c determine each other up to
  eventual periodicity. Since the colors of runs alternate, an odd period of the run lengths doubles
  in c.
- *Difficulty.* Moderate.
- *Data.* The longest runs in the first 10⁷ bits have length 22 (white) and 23 (black), close to
  log₂ 10⁷ ≈ 23. That is the Erdős–Rényi law: for almost every configuration the longest run of
  each color among the first n cells of the center column has length ⌊log₂ n⌋ (1 + o(1))
  (`LongestRuns.ae_tendsto_longestRun_trace`).
- *Lean.* Proved in the library: `WordForms.problem1_iff_black_gaps`, `problem1_iff_white_gaps` and
  `problem1_iff_run_lengths`, all from `WordForms.eventuallyPeriodic_iff_gap` (a sequence with
  infinitely many `true` values is EP iff the gaps between them are). The return-word form is
  proved too: `problem1_iff_returnWords` for every word u that occurs infinitely often, and
  `problem1_iff_returnWords_exists`, from `eventuallyPeriodic_iff_returnWord`. If b has period P
  from T, the occurrences of u past T shift by P after a fixed number N of them, so the return
  words repeat with period N; conversely equal return words at k and k + Q make b repeat with the
  total length of Q of them.

  ```lean
  noncomputable def blackGap (n : ℕ) : ℕ :=
    Nat.nth (fun t => Rule30Prize.center t = true) (n + 1) -
      Nat.nth (fun t => Rule30Prize.center t = true) n
  theorem problem1_iff_black_gaps : Rule30Prize.Problem1 ↔
      ¬ ∃ T P, 0 < P ∧ ∀ n, T ≤ n → blackGap (n + P) = blackGap n
  noncomputable def runLength (k : ℕ) : ℕ :=
    Nat.nth (fun t => Rule30Prize.center t ≠ Rule30Prize.center (t + 1)) (k + 1) -
      Nat.nth (fun t => Rule30Prize.center t ≠ Rule30Prize.center (t + 1)) k
  theorem problem1_iff_run_lengths : Rule30Prize.Problem1 ↔
      ¬ ∃ T P, 0 < P ∧ ∀ k, T ≤ k → runLength (k + P) = runLength k
  ```

- *Mathlib.* `Nat.nth` (Data/Nat/Nth.lean).
- *Sources.* [Dur98]; OEIS A327983, A327984, A327985.

**[47] golden-power: Mignosi–Restivo–Salemi local periodicity** (new).
- *Statement.* Let φ be the golden ratio. Problem 1 ⟺ infinitely many prefixes c(0)…c(n − 1)
  have no suffix that is a repetition of exponent ≥ φ² ≈ 2.618, i.e. no suffix of length
  ℓ ≥ φ²·p with period p.
- *Proof route.* Mignosi, Restivo and Salemi [MRS98] proved that an infinite word is ultimately
  periodic iff every sufficiently long prefix has a suffix that is a repetition of exponent φ². The
  constant is optimal, as the Fibonacci word shows. The direction "infinitely many prefixes without
  such a suffix ⟹ Problem 1" is easy (critic, own reasoning): if c = u v^ω, every prefix of length
  at least len(u) + 3·len(v) ends with a suffix of period len(v) and exponent ≥ 3 > φ².
- *Difficulty.* Hard: it needs the MRS theorem.
- *Data.* 2054 of the first 3000 prefixes of c have no suffix of exponent ≥ φ², including those of
  lengths 2989, 2990, 2996, 2997 and 2998 (critic, own computation). A random word behaves the same
  way.
- *Lean.* Proved in the library (2026-10-18):
  `WordForms.problem1_iff_infinitely_many_prefixes_without_golden_power`. Its converse direction is
  `GoldenPowers.eventuallyPeriodic_of_gp`, a formalization of [MRS98] that follows the paper's
  Lemmas 1–4 and Theorems 1–2.
  - Lemma 4: a window of length ⌈φP⌉ with periods P and Q, where φQ ≥ P, ends with a
    φ²-repetition of period P − Q.
  - Theorem 1 (`first_lt`, `period_until`): the first index Z where the φ-local period reaches its
    maximum P satisfies Z < k + P, and from Z − ⌈φ²P⌉ to every later index with local period P the
    word has period P.
  - Theorem 2: the local periods are therefore bounded by k, and an induction on the bound gives
    eventual periodicity.

  The sufficient direction was already `WordForms.problem1_of_infinitely_many_prefixes_without_golden_power`.
  The critic's statement was:

  ```lean
  def EndsWithGoldenPower (n : ℕ) : Prop :=
    ∃ p ℓ : ℕ, 0 < p ∧ ℓ ≤ n ∧ Real.goldenRatio ^ 2 * (p : ℝ) ≤ ℓ ∧
      ∀ i, n - ℓ ≤ i → i + p < n → Rule30Prize.center (i + p) = Rule30Prize.center i
  theorem problem1_iff_infinitely_many_prefixes_without_golden_power :
      Rule30Prize.Problem1 ↔ ∀ N, ∃ n, N ≤ n ∧ ¬ EndsWithGoldenPower n
  ```

- *Mathlib.* `Real.goldenRatio`, `List.HasPeriod` and the Fine–Wilf lemma `List.HasPeriod.gcd`.
  The MRS theorem is missing.
- *Sources.* [MRS98]; [Sha23].

**[51] unbordered-factors: long unbordered factors start arbitrarily late** (new).
- *Statement.* Problem 1 ⟺ for all n and L there is a factor c(i)…c(i + ℓ − 1) with i ≥ n and
  ℓ ≥ L that is unbordered: no nonempty proper prefix of it equals a suffix. Equivalently, every
  tail of c has unbordered factors of unbounded length.
- *Proof route.*
  - (⇐, easy) If a tail is purely periodic with period p, each of its factors of length ℓ > p has a
    border of length ℓ − p.
  - (⇒) Suppose every factor of length ≥ L starting at ≥ n has a border. Then the tail σⁿc has no
    unbordered factor of length ≥ L. By the extended Duval theorem [HN07], a finite word w whose
    longest unbordered factor has length μ(w) has least period μ(w) once len(w) ≥ 3μ(w); the
    optimal bound 7μ/3 is due to Holub and Nowotka [HN12]. So long prefixes of the tail have periods
    below L. Some p < L is a period of infinitely many prefixes, hence of all of them, and the tail
    is purely periodic.

  The infinite-word corollary is the critic's own reasoning, built on these theorems.
  Ehrenfeucht and Silberger [ES79] started this line of work.
- *Difficulty.* Hard through Duval's theorem. For infinite words, a shorter route works (2026-10-18):
  Lyndon words are unbordered, so if every long factor is bordered, every Lyndon factor is short.
  Repeatedly cutting off the longest Lyndon prefix gives Lyndon words `l₀ ≥ l₁ ≥ ⋯`, since
  `lₖ < lₖ₊₁` would make `lₖ lₖ₊₁` a longer Lyndon prefix. Finitely many words are that short, so
  the factors are eventually constant and the tail is eventually periodic.
- *Lean.* Proved in the library: `WordForms.problem1_iff_late_long_unbordered_factors`, from
  `Lyndon.eventuallyPeriodic_of_bordered` (Ehrenfeucht–Silberger for infinite words),
  `Lyndon.IsLyndon.not_bordered` and `Lyndon.IsLyndon.append`. The sufficient direction is
  `WordForms.problem1_of_late_long_unbordered_factors`. The critic's statement was:

  ```lean
  def Bordered (w : List Bool) : Prop :=
    ∃ k, 0 < k ∧ k < w.length ∧ w.take k = w.drop (w.length - k)
  theorem problem1_iff_late_long_unbordered_factors : Rule30Prize.Problem1 ↔
      ∀ n L : ℕ, ∃ i ℓ : ℕ, n ≤ i ∧ L ≤ ℓ ∧
        ¬ Bordered ((List.range ℓ).map fun j => Rule30Prize.center (i + j))
  ```

- *Sources.* [ES79]; [HN07]; [HN12].

**[19] simple-transforms.**
- *Statement.* Problem 1 ⟺ each of the following is not EP:
  - ¬c (A226474; the center column of rules 135 and 149 from a white cell);
  - c(· + k), for any fixed k;
  - the XOR derivative c(t) ⊕ c(t + 1) (A327974);
  - the running parity c(0) ⊕ … ⊕ c(t) (the parity of A327982);
  - any right-permutive sliding block code f(c(t), …, c(t + r)), with f bijective in its last
    argument.
- *Proof route.* Sliding block codes preserve EP. If the derivative has period P from T, then
  c(t + P) ⊕ c(t) is eventually constant, so c has period P or 2P. For permutive codes, the pair
  (window, phase) is finite-state (own reasoning, words survey).
- *Difficulty.* Easy.
- *Lean.* The complement is proved (library). The other transforms are proved in the library (batch 2:
  `TransformsSeeds.problem1_iff_shifted`, `problem1_iff_prepend`, `problem1_iff_xor_derivative`,
  `problem1_iff_running_parity`, `problem1_iff_blackCount_parity` and
  `problem1_iff_right_permutive_code`). Before batch 2 the derivative had a scratch proof and the
  shift and running-parity forms were stated.

  ```lean
  -- library: Rule30Equivalents/Symmetry.lean
  theorem problem1_iff_complement :
      Rule30Prize.Problem1 ↔ ¬ EventuallyPeriodic (fun t => !c t)
  -- statements used before batch 2
  theorem problem1_iff_shifted (k : ℕ) : Rule30Prize.Problem1 ↔
      ¬ Rule30Jen.EventuallyPeriodic (fun t => Rule30Prize.center (t + k))
  theorem problem1_iff_xor_derivative : Rule30Prize.Problem1 ↔ ¬ Rule30Jen.EventuallyPeriodic
      (fun t => xor (Rule30Prize.center t) (Rule30Prize.center (t + 1)))
  theorem problem1_iff_running_parity : Rule30Prize.Problem1 ↔ ¬ Rule30Jen.EventuallyPeriodic
      (fun t => ((List.range (t + 1)).map Rule30Prize.center).foldl xor false)
  ```

- *Sources.* OEIS A226474, A327974, A327982; [LM95]; [Hed69].

**[20] decimations.**
- *Statement.*
  - (a) For each fixed k ≥ 1, Problem 1 ⟺ some decimation n ↦ c(kn + r) with r < k is not EP. For
    example, c at even times or c at odd times is not EP.
  - (b) Problem 1 ⟺ for every P ≥ 1 some residue class k ↦ c(r + kP) is not eventually constant.
    The case P = 1 is the proved `center_not_eventually_constant`.
- *Proof route.*
  - (a) If decimation r has period P_r from T_r, then c has period k·lcm(P_r) from k·max T_r + k.
  - (b) c has period P from some time on ⟺ every residue class modulo P is eventually constant.
- *Note.* Read the right half of row t as y_t = Σ_{p≥0} cell(t, p)·2^−(p+1). Then
  c(t) = [y_t ≥ 1/2] exactly, since rows are finite. So Wolfram's suggestion that
  [y_{Pk+r} ≥ 1/2] is not eventually constant for some r is (b) again [W19].
- *Difficulty.* Easy.
- *Lean.* Proved in the library (batch 2: `TransformsSeeds.problem1_iff_decimation`,
  `problem1_iff_even_or_odd` and `problem1_iff_nonconstant_class`). Before batch 2, (b) had a
  scratch proof and (a) was stated:

  ```lean
  theorem problem1_iff_decimation (k : ℕ) (hk : 0 < k) : Rule30Prize.Problem1 ↔
      ∃ r < k, ¬ Rule30Jen.EventuallyPeriodic (fun n => Rule30Prize.center (k * n + r))
  theorem problem1_iff_nonconstant_class : Rule30Prize.Problem1 ↔
      ∀ P, 0 < P → ∃ r < P, ¬ ∃ K b, ∀ k, K ≤ k → Rule30Prize.center (r + k * P) = b
  ```

- *Sources.* [W19]; own reasoning (words survey).

### 3.7 Cellular-automaton structure

**[6] symmetric-rules: rules 86, 135 and 149.**
- *Statement.* Problem 1 ⟺ each of the following center columns is not EP:
  - rule 86 (the mirror image of rule 30) from a single black cell; its center column is c;
  - rule 135 (the color complement) from a single white cell on a black background; its center
    column is ¬c;
  - rule 149 (mirror and complement) from a single white cell; its center column is ¬c.
- *Proof route.* Reflection and color conjugation are symmetries of the elementary CA. If rule m is
  the mirror image (or the conjugate) of rule n, then m started from the mirrored (or complemented)
  row draws the mirrored (or complemented) pattern. The single black seed is its own mirror image,
  the white seed is its complement, and EP is invariant under complement. This is an identity
  transfer.
- *Caveat.* Rule 135 from a single *black* cell has a different center column: column −1 of rule
  30, complemented and delayed by one step. That is the white-seed problem, which is related but
  not known to be equivalent (Section 6.3). The library proves this identity
  (`evolve_135_blackSeed`).
- *Difficulty.* Easy.
- *Lean.* Proved (library). `decide` also checks the rule numbers, that {30, 86, 135, 149} is closed
  under mirror and conjugation (`class_30`), and the classical count of 88 classes (`card_classes`).
  Reading `card_classes` as "88 classes" uses a counting argument that is not formalized.

  ```lean
  -- Rule30Equivalents/Symmetry.lean, namespace Rule30Equivalents.Symmetry
  def ruleBit (rule : Nat) (l c r : Bool) : Bool :=
    rule.testBit (4 * l.toNat + 2 * c.toNat + r.toNat)
  def evolve (rule : Nat) (init : Int → Bool) : Nat → Int → Bool
    | 0, p => init p
    | t + 1, p =>
      ruleBit rule (evolve rule init t (p - 1)) (evolve rule init t p) (evolve rule init t (p + 1))
  def blackSeed (p : Int) : Bool := decide (p = 0)
  def whiteSeed (p : Int) : Bool := !blackSeed p
  theorem problem1_iff_rule86 :
      Rule30Prize.Problem1 ↔ ¬ EventuallyPeriodic (fun t => evolve 86 blackSeed t 0)
  theorem problem1_iff_rule135 :
      Rule30Prize.Problem1 ↔ ¬ EventuallyPeriodic (fun t => evolve 135 whiteSeed t 0)
  theorem problem1_iff_rule149 :
      Rule30Prize.Problem1 ↔ ¬ EventuallyPeriodic (fun t => evolve 149 whiteSeed t 0)
  ```

- *Sources.* [Wol83] (rule numbering); [LP90] (the two symmetries and the 88 classes; its Table 1
  lists the class 30 (86, 135, 149)); [MW]; OEIS A051023, A226474. We know of no separate source
  for the equivalences themselves.

**[21] stripe-seeds: finite seeds with exactly the same center column.**
- *Statement.* For n ≥ 0 let s_n be the row that is black exactly at the even positions of [0, n)
  and at n: 1, 11, 101, 1011, 10101, …. Rule 30 from s_n
  - agrees with the single-seed pattern at every (t, p) with p < t,
  - shows the fixed stripe (black at even p) on [t, t + n), and
  - has its right edge at t + n.

  So its center column is exactly c, and Problem 1 ⟺ the center column of rule 30 from s_n is not
  EP, for any n.
- *Proof route.* Induction on t with the explicit pattern. The stripe …1010… is a fixed point that
  always shows x_p ∨ x_{p+1} = 1 to its left neighbor (the "OR latch" of [Con26]), so the light cone
  left of p = t never sees it. This is an identity transfer. By contrast, changes on the left side
  never preserve c: flipping cell −m flips c(m).
- *Checks.* The pattern was checked numerically for n ≤ 11 and t < 400 (synthesis and critic), and
  for n ≤ 51 and t ≤ 2500 (CA-structure survey). An exhaustive search found that among the 1023
  nonzero rows supported in [0, 9], exactly s_0, …, s_9 give c; the seed 111 does not
  (CA-structure survey). The surveys found no literature for this observation; it is the
  CA-structure survey's own.
- *Difficulty.* Easy.
- *Lean.* Proved in the library (batch 2: `TransformsSeeds.problem1_iff_stripeSeed`). Before batch 2 it had a
  scratch proof in core Lean:

  ```lean
  def stripeSeed (n : ℕ) (p : ℤ) : Bool := decide (0 ≤ p ∧ p < n ∧ p % 2 = 0) || decide (p = n)
  theorem problem1_iff_stripeSeed (n : ℕ) : Rule30Prize.Problem1 ↔
      ¬ Rule30Jen.EventuallyPeriodic (fun t => Rule30Realization.evol (stripeSeed n) t 0)
  ```

- *Sources.* CA-structure survey (own observation); [Con26] (the OR latch and triangular
  uniqueness); [Row06].

**[22] realization: the inverse problem.**
- *Statement.* Keep the right half of the initial row white. Rule 30 is affine in its left cell
  (left-permutive), so every column u : ℕ → Bool is the center column of exactly one such row Λ(u).
  Λ(c) is the single seed, and Λ(u)(−m) depends only on u(0..m) and flips when u(m) flips.
  Problem 1 ⟺ no EP column u has Λ(u) equal to the single seed.
- *2-adic reading* (CA-structure survey, own reformulation). For a fixed right half, the trace map
  Σ x_{−m}·2^m ↦ Σ c_t·2ᵗ is an isometry of ℤ₂. The seed is the 2-adic integer 1, and Problem 1
  says that its image is not rational.
- *Proof route.* The catalog proves existence and uniqueness of Λ
  (`Rule30Realization.column_realizable_unique`, `realize`, `unique`, `evol_seed`). This is an
  identity transfer.
- *Barrier.* `seed_perturbation`: for every n, some row that agrees with the seed on [−n, ∞) has
  center column c up to time n and white afterwards. So no argument that looks only at a bounded
  part of the row can prove Problem 1.
- *Difficulty.* Easy.
- *Lean.* Proved in the library: `Realization.problem1_iff_realization`. The same module proves
  `problem1_iff_column_iff_both`: by Jen's theorem, an equivalence between Problem 1 and the same
  question for another column would prove both statements.

  ```lean
  theorem problem1_iff_realization : Rule30Prize.Problem1 ↔
      ∀ u : ℕ → Bool, Rule30Jen.EventuallyPeriodic u →
        Rule30Realization.conf Rule30Realization.seed u ≠ Rule30Realization.seed
  ```

- *Sources.* [W86] §§3–4 and 7; [NKS] p. 1087; [MS91]; [Con26] (its Theorems 2–3 compute Λ of the
  two constant columns).

**[33] coupled-halves: a causal fixed point.**
- *Statement.* Let L_u be rule 30 on p ≤ −1, started white and driven at p = 0 by the column u. Let
  R_u be rule 30 on p ≥ 1, started white and driven by u. The system u(0) = 1,
  u(t + 1) = rule(L_u(t, −1), u(t), R_u(t, 1)) is causal, and its unique solution is c. Problem 1 ⟺
  no solution of this system is EP.
- *Proof route.* L_u(t) and R_u(t) depend only on u(0..t). The catalog lemmas
  `Rule30DrivenLeft.cell_eq_L` and `Rule30Ether.cell_eq_drv` (with T = 0) identify the solution with
  c. The left half sees the center only through c(t) ∧ c(t + 1) (`Rule30MaskedJen.effective_step`).
  This is an identity transfer.
- *Context.* The project's period-specific reductions relax this system by dropping one half. Q01,
  Q001, C3, C3w and C3s001 keep the left half; Absorption and AbsorptionT keep the right half.
- *Difficulty.* Moderate.
- *Lean.* Proved in the library: `CoupledHalves.problem1_iff_coupled_halves`. The center column
  solves the system (`center_solves`), and it is the only solution (`eq_center_of_solves`), because
  the driven halves are causal (`L_causal`, `drv_causal`).

  ```lean
  theorem problem1_iff_coupled_halves : Rule30Prize.Problem1 ↔
      ∀ u : ℕ → Bool, u 0 = true →
        (∀ t, u (t + 1) = Rule30Jen.rule (Rule30DrivenLeft.L u (fun _ => false) t (-1)) (u t)
          (Rule30Ether.drv u (fun _ => false) t 1)) →
        ¬ Rule30Jen.EventuallyPeriodic u
  ```

- *Sources.* [Project] (`Rule30DrivenLeft`, `Rule30Ether`, `Rule30MaskedJen`); [W19], which notes
  that "a single column plus scattered cells in another column can't both be periodic".

### 3.8 Logic, automata and computation

**[9] presburger.**
- *Statement.* Problem 1 ⟺ S = {t : c(t) = 1} (A327984) is not definable in Presburger arithmetic
  (ℕ, 0, 1, +), even with parameters ⟺ S is not semilinear.
- *A further classical equivalent* (no Lean statement): (ℕ, +, S) defines an infinite set with
  unbounded gaps, and one formula works for every such S [MV96], [Mil16].
- *Proof route.* By Presburger's quantifier elimination, or by Ginsburg–Spanier, the definable
  subsets of ℕ are exactly the ultimately periodic sets. Mathlib proves this.
- *Difficulty.* Trivial.
- *Lean.* Proved in the library: `LogicAutomata.problem1_iff_not_presburger` (any parameter set)
  and `LogicAutomata.problem1_iff_not_semilinear`, through Mathlib's
  `presburger.definable₁_iff_ultimately_periodic` and `Nat.isSemilinearSet_iff_ultimately_periodic`.

  ```lean
  theorem problem1_iff_not_presburger (A : Set ℕ) : Rule30Prize.Problem1 ↔
      ¬ A.Definable₁ FirstOrder.Language.presburger {t | Rule30Prize.center t = true}
  theorem problem1_iff_not_semilinear : Rule30Prize.Problem1 ↔
      ¬ IsSemilinearSet {t : ℕ | Rule30Prize.center t = true}
  ```

- *Mathlib.* `FirstOrder.Language.presburger.definable₁_iff_ultimately_periodic` and
  `presburger.definable_iff_isSemilinearSet` (ModelTheory/Arithmetic/Presburger/Definability.lean);
  `Nat.isSemilinearSet_iff_ultimately_periodic` and `IsSemilinearSet` (…/Semilinear/Defs.lean).
  Missing: decidability of Presburger arithmetic.
- *Sources.* [Pre29]; [GS66]; [MV96]; [Mil16].

**[18] regular-languages.**
- *Statement.* Problem 1 ⟺ L₁ = {1ⁿ : c(n) = 1} is not regular (no unary DFA with output computes
  c) ⟺ the prefix language {c(0)…c(n − 1)} ⊆ {0,1}* is not regular.
- *Proof route.* By Myhill–Nerode, the left quotient of L₁ by 1ⁿ is the language of the shift σⁿc,
  and distinct sequences give distinct languages. So L₁ is regular ⟺ c has finitely many shifts ⟺
  c is EP ([3]). The prefix language works the same way.
- *Kernel consequence.* A unary DFA that computes c, if one existed, would need at least 16359
  states.
- *Difficulty.* Easy.
- *Lean.* Proved in the library: `LogicAutomata.problem1_iff_unary_not_regular` and
  `LogicAutomata.problem1_iff_prefixes_not_regular`, by counting left quotients (Myhill–Nerode).

  ```lean
  def unaryLang : Language Unit := {l | Rule30Prize.center l.length = true}
  theorem problem1_iff_unary_not_regular : Rule30Prize.Problem1 ↔ ¬ unaryLang.IsRegular
  def prefixLang : Language Bool := {l | l = (List.range l.length).map Rule30Prize.center}
  theorem problem1_iff_prefixes_not_regular : Rule30Prize.Problem1 ↔ ¬ prefixLang.IsRegular
  ```

- *Mathlib.* `Language.IsRegular` (Computability/DFA.lean); `Language.leftQuotient` and
  `Language.isRegular_iff_finite_range_leftQuotient` (Computability/MyhillNerode.lean).
- *Sources.* [HU79]; [Mathlib].

**[40] context-free.**
- *Statement.* Problem 1 ⟺ L₁ is not context-free ⟺ the prefix language is not context-free.
- *Proof route.* Unary context-free languages are regular [GR62], [Par66]. An infinite context-free
  language made of prefixes of a single infinite word forces that word to be ultimately periodic
  [Boo77]; Book's proof uses the context-free pumping lemma. Then apply [18].
- *Difficulty.* Moderate: both directions need only the pumping lemma [BPS61], and Parikh's theorem
  is not needed.
- *Lean.* Proved in the library ([ContextFree](Rule30Equivalents/ContextFree.lean)), with
  `LogicAutomata.unaryLang` and `LogicAutomata.prefLang` as in [18].

  ```lean
  theorem problem1_iff_unary_not_contextFree :
      Rule30Prize.Problem1 ↔ ¬ (LogicAutomata.unaryLang c).IsContextFree
  theorem problem1_iff_prefixes_not_contextFree :
      Rule30Prize.Problem1 ↔ ¬ (LogicAutomata.prefLang c).IsContextFree
  ```

  - `pumping`: the pumping lemma for every `ContextFreeGrammar`.
    - It works with derivation forests and forests with one hole.
    - Take a derivation of `w` with the fewest rule applications. If no node has a descendant with
      its own label, the yield has length at most `b ^ N`, where `b` bounds the rule lengths and
      `N` counts the nonterminals.
    - Otherwise some node has a descendant with its label, and none of its children does. The two
      nodes give the split `u v x y z` with `|v x y| ≤ b ^ (N + 1)`. Minimality makes `v y`
      nonempty.
  - `isContextFree_of_isRegular`: regular languages over a finite alphabet are context-free, through
    the right-linear grammar of a DFA.
  - Unary: each member `n ≥ p` has a pump of length `k ≤ p`, so `c(n) = 1` forces `c(n + p!) = 1`.
    Along each residue class mod `p!` the sequence is then monotone, hence eventually constant
    (`eventuallyPeriodic_of_imp`).
  - Prefixes: pumping the prefix of length `p` makes every `u vⁱ`, or every `u x yⁱ`, a prefix of
    c, so c is periodic after it (`periodic_of_pumped_prefixes`).
- *Mathlib.* `Language.IsContextFree`, `ContextFreeGrammar`, and the regular pumping lemmas
  `DFA.pumping_lemma` and `NFA.pumping_lemma`. Mathlib has neither the context-free pumping lemma nor
  the inclusion of regular languages in context-free ones (both proved here), nor Parikh's theorem.
- *A stronger relative.* "c is not morphic", equivalently "c is determined by no indexed language"
  [Smi14]; see Section 4.
- *Sources.* [GR62]; [Par66]; [Boo77]; [Smi14].

**[36] omega-regular.**
- *Statement.* Problem 1 ⟺ the singleton {c} ⊆ {0,1}^ω is not ω-regular (no Büchi automaton accepts
  exactly c) ⟺ S is not definable in MSO(ℕ, <), by Büchi's theorem.
- *Proof route.*
  - (⇐) If c = u v^ω, a deterministic lasso automaton accepts exactly c.
  - (⇒) An accepting run on c visits some accepting state twice. Pumping that loop gives an
    accepted ultimately periodic word, which must be c.
- *Kernel consequence.* A Büchi automaton accepting exactly {c}, if one existed, would need at
  least 16359 states (logic survey). The reason: if the run is in the same state at times m < n,
  then c(0)…c(m − 1) followed by σⁿc is also accepted, so σᵐc = σⁿc.
- *Difficulty.* Moderate for the Büchi form; hard for MSO, which needs Büchi's theorem or the
  composition method. Both forms are proved here.
- *Lean.* The Büchi form is proved in the library: `OmegaRegular.problem1_iff_not_omega_regular`,
  from `eventuallyPeriodic_iff_omegaRegular_singleton` (`lasso_accepts_iff` and
  `eventuallyPeriodic_of_accepts_iff`), with the definitions below. The MSO form is proved in
  [MonadicLogic](Rule30Equivalents/MonadicLogic.lean): `problem1_iff_not_msoDefinable`, from
  `eventuallyPeriodic_iff_msoDefinable`. `MSO` has first-order and set variables named by natural
  numbers, with atoms x < y and x ∈ X; `MSODefinable S` says that some formula holds exactly when
  its first-order variables are n ∈ S. The proof avoids Büchi automata and their complementation:
  - `MSO.toMSO0` translates into a logic with set variables only (first-order variables become
    singletons), with atoms X = ∅, X a singleton, X ⊆ Y, and "X entirely below Y".
  - `tp m k ρ`, the k-type of an assignment: its atomic facts and, for each variable, the set of
    (k − 1)-types of its modifications. Types range over a finite type, and equal k-types satisfy
    the same formulas of depth at most k (`holds_iff_of_tp_eq`).
  - `tp_shift`: putting one position in front of ℕ maps equal types to equal types. The
    assignments for n and n + 1 differ by such a shift, so by pigeonhole their types, and with
    them membership in S, are eventually periodic.
  - The converse, `periodicFormula`: "every family of sets that contains 0 and follows the
    counting automaton puts x into an accepting set".

  ```lean
  structure Buchi (α : Type) where
    Q : Type
    [fin : Finite Q]
    init : Q
    step : Q → α → Q → Prop
    acc : Set Q
  def Buchi.Accepts {α : Type} (B : Buchi α) (w : ℕ → α) : Prop :=
    ∃ r : ℕ → B.Q, r 0 = B.init ∧ (∀ n, B.step (r n) (w n) (r (n + 1))) ∧
      ∀ N, ∃ n, N ≤ n ∧ r n ∈ B.acc
  theorem problem1_iff_not_omega_regular : Rule30Prize.Problem1 ↔
      ¬ ∃ B : Buchi Bool, ∀ w, B.Accepts w ↔ w = Rule30Prize.center
  ```

- *Mathlib.* No ω-automata and no MSO. The logic survey reports ctchou/AutomataTheory, a Lean 4
  library with Büchi automata that is being ported to CSLib; this was not verified here.
- *Sources.* [Bue62]; [Tho90].

**[27] finite-state-machines: prediction and generation.**
- *Statement.* Problem 1 ⟺ either of:
  - every finite-state predictor errs infinitely often. A predictor has a finite set of states; it
    reads c(0), …, c(n − 1) and guesses g(state) for c(n);
  - no finite autonomous machine (F : σ → σ with output g) has c(t) = g(Fᵗs₀) for all large t.

  So no LFSR, NLFSR, FCSR or finite cyclic rule-30 register produces c from some time on.
- *Proof route.* If c is EP, a counter predictor works. Conversely, a predictor that is eventually
  always right effectively reads its own guesses. So it runs autonomously on a finite set, and its
  output is eventually periodic.
- *Stronger relative.* Finite-state unpredictability at error rate 1/2 implies both Problem 1 and
  Problem 2 (own reasoning: an EP column is predicted with error rate 0, and the two constant
  predictors measure the density; proved: `BoundedRemainder.problem1_of_unpredictable_half`,
  `problem2_of_unpredictable_half`). The hypothesis holds for almost every configuration: the errors
  of a finite-state predictor on a random trace are fair coins
  (`BoundedRemainder.ae_predictsAtHalf_trace`).
- *Difficulty.* Easy.
- *Lean.* Proved in the library (batch 2: `WordsAutomata.problem1_iff_unpredictable`,
  `problem1_iff_no_finite_generator` and `problem1_iff_no_regular_predictor`). Before batch 2 it was
  stated:

  ```lean
  def readState {σ : Type} (s₀ : σ) (δ : σ → Bool → σ) : ℕ → σ
    | 0 => s₀
    | n + 1 => δ (readState s₀ δ n) (Rule30Prize.center n)
  theorem problem1_iff_unpredictable : Rule30Prize.Problem1 ↔
      ∀ (σ : Type) [Finite σ] (s₀ : σ) (δ : σ → Bool → σ) (g : σ → Bool),
        ∀ N, ∃ n, N ≤ n ∧ g (readState s₀ δ n) ≠ Rule30Prize.center n
  theorem problem1_iff_no_finite_generator : Rule30Prize.Problem1 ↔
      ¬ ∃ (σ : Type) (_ : Finite σ) (s₀ : σ) (F : σ → σ) (g : σ → Bool) (T : ℕ),
        ∀ t, T ≤ t → Rule30Prize.center t = g (F^[t] s₀)
  ```

- *Sources.* [FMG92]; [SS72]; [W19] (on "predictable regularities").

**[37] lz76: Lempel–Ziv complexity.**
- *Statement.* Problem 1 ⟺ the Lempel–Ziv (1976) complexity of the prefixes c(0)…c(n − 1) is
  unbounded. Equivalently, it tends to ∞.
- *Proof route.*
  - If c is EP, the last component of the exhaustive history copies forever (with overlap), so the
    complexity is bounded.
  - Conversely, use the "fewest components" definition below (critic, own reasoning). Suppose a
    history with at most K components exists for infinitely many n. Pass to a subsequence on which
    the number of cut points is constant and each cut point is either constant or tends to ∞. The
    component that starts at the last bounded cut point p has unbounded length, so it is
    eventually a copy from some source s < p, and some s recurs. Then c(x + p − s) = c(x) for all
    x ≥ s, so c is EP.

  This argument needs no Lempel–Ziv optimality theorem, and it even gives complexity → ∞. The first
  component has no earlier source, so a definition must allow one-letter "innovation" components.
- *Difficulty.* Easy to moderate. Earlier drafts rated it moderate and required Lempel and Ziv's
  optimality theorem, which the critic showed is unnecessary.
- *Data* (logic survey). The complexity of the first 20000 bits is 1433, against 1437 for
  pseudorandom bits.
- *Lean.* Proved in the library: `LempelZiv.problem1_iff_lz_unbounded`, from
  `eventuallyPeriodic_iff_lz_bounded`. One direction is `WordForms.lzComplexity_le_of_eventuallyPeriodic`
  (single letters, then one overlapping copy). The other reorganizes the critic's argument without
  subsequences: if no cut point started arbitrarily long components, every history of a long
  prefix would have more than K + 1 cut points below a fixed bound (`exists_long_component`); a long
  component copies from finitely many sources, so one source works for all lengths.

  ```lean
  def IsLZHistory (n : ℕ) (b : List ℕ) : Prop :=
    b.head? = some 0 ∧ b.getLast? = some n ∧ List.IsChain (· < ·) b ∧
      ∀ p ∈ b.zip b.tail, p.2 = p.1 + 1 ∨ ∃ s < p.1, ∀ j, p.1 + j + 1 < p.2 →
        Rule30Prize.center (s + j) = Rule30Prize.center (p.1 + j)
  noncomputable def lzComplexity (n : ℕ) : ℕ := sInf {k | ∃ b, IsLZHistory n b ∧ b.length = k + 1}
  theorem problem1_iff_lz_unbounded : Rule30Prize.Problem1 ↔ ∀ K, ∃ n, K < lzComplexity n
  ```

- *Sources.* [LZ76]; critic.

**[52] automatic-complexity: automatic complexity of the prefixes** (new).
- *Statement.* Let A(x) be the deterministic automatic complexity of a finite word x [SW01]: the
  fewest states of a DFA that accepts x and no other word of the same length. Problem 1 ⟺
  A(c(0)…c(n − 1)) → ∞ ⟺ A(c(0)…c(n − 1)) is unbounded.
- *Proof route.* This is the critic's own proof; the critic did not find the equivalence stated in
  [SW01].
  - (⇐) If c = u v^ω, consider the lasso DFA with len(u) + len(v) states plus a dead state, whose
    accepting state is the one reached at time n. Among words of length n it accepts exactly the
    prefix of length n. So A stays bounded.
  - (⇒) Suppose A ≤ K for infinitely many n. There are finitely many DFAs on Fin K over {0,1}, so a
    single DFA M uniquely accepts the prefix for infinitely many n. Some state q is visited
    infinitely often by the run of M on c, at times t_0 < t_1 < …. Swapping two adjacent closed
    walks c[t_k, t_{k+1}) and c[t_{k+1}, t_{k+2}) at q gives another accepted word of the same
    length, so by uniqueness the two segments commute. By Lyndon–Schützenberger [LS62] they are all
    powers of one primitive word ρ, so c[t_0, ∞) = ρ^ω.
- *Difficulty.* Moderate.
- *Known.* Shallit and Wang show that A(x) ≥ n/13 for almost all binary words x of length n [SW01].
  Nothing has been computed for c.
- *Lean.* Proved in the library: `Automatic.problem1_iff_automaticComplexity_tendsto_top`. One
  direction is `autComplexityLE_of_eventuallyPeriodic` (the lasso DFA `lassoDFA` gives complexity
  ≤ T + P + 1); the other is `eventuallyPeriodic_of_frequently_autComplexityLE`, the swap argument
  above, which needs only B ++ A = A ++ B, not Lyndon–Schützenberger. Mathlib has `DFA`, `DFA.accepts`, `DFA.evalFrom` and `DFA.pumping_lemma`,
  plus `List.HasPeriod` and the Fine–Wilf lemma. It lacks automatic complexity and the commuting-words
  lemma (xy = yx ⟹ common root), which follows from Fine–Wilf.

  ```lean
  def UniquelyAccepts {σ : Type} (M : DFA Bool σ) (x : List Bool) : Prop :=
    x ∈ M.accepts ∧ ∀ y : List Bool, y.length = x.length → y ∈ M.accepts → y = x
  def AutComplexityLE (x : List Bool) (K : ℕ) : Prop :=
    ∃ M : DFA Bool (Fin K), UniquelyAccepts M x
  theorem problem1_iff_automaticComplexity_tendsto_top : Rule30Prize.Problem1 ↔
      ∀ K : ℕ, ∀ᶠ n in Filter.atTop,
        ¬ AutComplexityLE ((List.range n).map Rule30Prize.center) K
  ```

- *Sources.* [SW01] (the definition); [LS62]; critic (the proof).

**[42] cobham-christol.**
- *Statement.* Problem 1 ⟺ each of:
  - c is not both 2-automatic and 3-automatic (any multiplicatively independent pair of bases
    works);
  - C(X) is transcendental over F₂(X) or over F₃(X), reading the 0/1 values in F₂ and in F₃;
  - S is not definable in both Büchi arithmetics (ℕ, +, V₂) and (ℕ, +, V₃);
  - c is not both 2-regular and 3-regular in the sense of Allouche and Shallit, over any field;
  - c is not k-automatic for some k ≥ 2.
- *Proof route.*
  - EP ⟹ the k-kernel is finite for every k ⟹ c is k-automatic (Eilenberg's criterion).
  - Cobham 1969: a sequence that is k- and l-automatic, with k and l multiplicatively independent,
    is EP.
  - Christol 1979 and [CKMR80]: over F_p, p-automatic ⟺ algebraic over F_p(X).
  - Büchi–Bruyère: k-automatic ⟺ definable in (ℕ, +, V_k). Cobham–Semenov gives the two-base
    version.
- *Difficulty.* Hard: it needs Cobham's and Christol's theorems. Both are proved here, Christol in
  both directions (`Christol.isAutomatic_iff_isAlgebraic`).
- *Data.* The 2-kernel of c has at least 262,143 elements and the 3-kernel at least 265,720: the
  kernel sequences c(2^e·n + r) with e ≤ 17, and c(3^e·n + r) with e ≤ 11, have pairwise distinct
  40-bit prefixes (number-theory survey, own computation). A minimal LSD-first DFAO for a sequence
  has as many states as its 2-kernel has elements, so a DFAO generating c would need at least
  262,143 states (critic). An earlier bound of 8191 states has been attributed to [Ner26a], but
  that paper's abstract does not mention it; treat it as unverified. The kernel data supersede it
  in any case.
- *Lean.* The sufficient directions are proved in the library: `Automatic.problem1_of_not_automatic`
  (not k-automatic for some k ≥ 2) and `Automatic.problem1_of_not_two_three_automatic`, from
  `isAutomatic_of_eventuallyPeriodic` (an EP sequence has a finite k-kernel for every k ≥ 2), with the
  definitions below; and `Transcendence.problem1_of_transcendental_F2_or_F3` for the F₂/F₃ form.
  The automatic forms are proved in [Cobham](Rule30Equivalents/Cobham.lean):
  `problem1_iff_not_two_three_automatic` and `problem1_iff_exists_not_automatic`, from
  `eventuallyPeriodic_of_isAutomatic` (Cobham's theorem, for any multiplicatively independent bases).
  The proof follows [Kre18] with the kernel definition of automaticity.
  - `sig c f x`, the kernel values at x, x + 1 and x + 2, takes finitely many values. Equal
    signatures give f(x cⁿ + z) = f(y cⁿ + z) for all z ≤ 2cⁿ (`eq_of_sig_eq`). This replaces the
    automata over the extended digits 0, …, 2c of Krebs' Lemma 5.
  - `exists_close_powers` (Lemma 6): M |aᵐ − bⁿ| < bⁿ for some m, n ≥ 1, by pigeonhole on
    ⌊M aˣ / b^⌊log_b aˣ⌋⌋.
  - `locPer_of_pair`: two numbers u ≠ v with the same b- and a-signatures give a local period
    p = (u − v)(aᵐ − bⁿ) ≤ bⁿ/6 on an interval of radius 2bⁿ/3 around x bⁿ + bⁿ, for every x with
    their b-signature. `LocPer.glue` (Lemma 7) chains these local periods over consecutive x into
    one period.
  The F₂/F₃ form is proved in [Christol](Rule30Equivalents/Christol.lean):
  `problem1_iff_transcendental_F2_or_F3`, from `isAutomatic_of_isAlgebraic` (Christol's theorem, one
  direction, for every prime p) and Cobham's theorem.
  - `pow_eq_expand`: over F_p, h^p = h(X^p) (Mathlib's `map_frobenius_expand`). The Cartier operator
    Λ_r(Σ aₙXⁿ) = Σ a_{pn+r}Xⁿ satisfies Λ_r(h^p g) = h Λ_r g (`cartier_pow_mul`).
  - `exists_ore_relation` (Ore): an algebraic F satisfies Σ_{i≤d} cᵢ F^(pⁱ) = 0 with polynomial cᵢ
    and c₀ ≠ 0. The powers F^(pⁱ) are dependent over F_p[X], and Λ_r moves the lowest nonzero
    coefficient down to index 0 (`exists_ore`).
  - The g with c₀g = Σ hᵢ F^(pⁱ), deg hᵢ ≤ D, form a finite set that contains F and is closed under
    every Λ_r: c₀ Λ_r g = Λ_r(c₀^(p−1)·c₀g), and c₀F is a combination of higher powers. The p-kernel
    of c is the image of F under the iterated Λ's, so it is finite.
  The Büchi-arithmetic form is proved in [BuchiArithmetic](Rule30Equivalents/BuchiArithmetic.lean):
  `problem1_iff_not_buchi_definable`, with Mathlib's `Set.Definable₁` and the language
  `buchi k` = (0, 1, +, V_k), where V_k x is the largest power of k dividing x and V_k 0 = 0. The
  direction it needs, "definable in (ℕ, +, V_k) ⟹ k-automatic" (`isAutomatic_of_definable`), is
  proved without automata. A relation on ℕ^ι is `Recognizable` when it has finitely many sections
  {v | kᵉv + r ∈ R} with r < kᵉ. Recognizable relations are closed under complement, finite
  intersection, reindexing and projection: a section of {w | ∃ u, (w, u) ∈ R} is a union of
  projections of sections of R, one for each choice of the low digits of u, so it is determined by
  a subset of the finite kernel of R. The graphs of =, +, V_k and the constants have at most a
  handful of sections, so by induction every term graph and every formula is recognizable.
  Together with Cobham's theorem this gives `eventuallyPeriodic_of_definable` for any
  multiplicatively independent pair of bases. The converse, "k-automatic ⟹ definable", is proved
  in [BuchiConverse](Rule30Equivalents/BuchiConverse.lean), which completes the Büchi–Bruyère
  theorem for sets of naturals (`definable_iff_isAutomatic`, with any parameters). The formula
  reads the base-k digits of n through the automaton whose states are the k-kernel: the run is
  coded by one number per state, with digit 1 at the positions kⁱ where the run is in that
  state. "y is a power of k" (V_k y = y ≥ 1) and "the digit of x at y is j" (x = a + j y + b with
  a < y and b = 0 or k y ≤ V_k b) are definable through Mathlib's definable functions, and the
  conditions on the codes are definable by finite Boolean combinations and quantifiers.
  The k-regular form is proved in [RegularSequences](Rule30Equivalents/RegularSequences.lean):
  `problem1_iff_not_regularSeq_two_three`, from `isRegularSeq_iff_isAutomatic`. A 0/1 sequence
  whose k-kernel spans a finite-dimensional space over a field K has a finite kernel: a
  finite-dimensional space of sequences is determined by finitely many coordinates
  (`exists_eq_zero_of_vanish`, since the subspaces vanishing below N stabilize), so the kernel
  embeds into {0, 1}^N.

  ```lean
  def kernel (k : ℕ) (f : ℕ → Bool) : Set (ℕ → Bool) :=
    {g | ∃ e r, r < k ^ e ∧ g = fun n => f (k ^ e * n + r)}
  def IsAutomatic (k : ℕ) (f : ℕ → Bool) : Prop := (kernel k f).Finite
  theorem problem1_iff_not_two_three_automatic : Rule30Prize.Problem1 ↔
      ¬ (IsAutomatic 2 Rule30Prize.center ∧ IsAutomatic 3 Rule30Prize.center)
  open scoped RatFunc in
  theorem problem1_iff_transcendental_F2_or_F3 : Rule30Prize.Problem1 ↔
      Transcendental (RatFunc (ZMod 2)) ((series (ZMod 2) : PowerSeries (ZMod 2)) : LaurentSeries (ZMod 2)) ∨
      Transcendental (RatFunc (ZMod 3)) ((series (ZMod 3) : PowerSeries (ZMod 3)) : LaurentSeries (ZMod 3))
  ```

- *Mathlib.* It has `DFA`, `Language`, `RatFunc`, `LaurentSeries`, `Transcendental` and `ZMod`. It
  lacks automatic sequences, Christol's theorem, Cobham's theorem and Büchi arithmetic.
  formal-conjectures defines `AutomaticSequence.IsAutomatic` through kernels. The surveys found no
  formalization of Cobham's theorem in any proof assistant; [Kre18] gives a short proof.
- *Sources.* [Cob69]; [Kre18]; [Chr79]; [CKMR80]; [Sem77]; [BHMV94]; [AS03].

**[46] durand-cobham: Cobham's theorem for substitutions** (new).
- *Statement.* Let α and β be multiplicatively independent Perron numbers, for example 2 and 3, or
  2 and the golden ratio. Problem 1 ⟺ c is not both α-substitutive and β-substitutive. Here
  α-substitutive means a letter-to-letter image of a fixed point of a substitution whose dominant
  eigenvalue is α.
- *Proof route.* Durand [Dur11] proved that a sequence over a finite alphabet is both α- and
  β-substitutive iff it is ultimately periodic, for multiplicatively independent Perron numbers α
  and β. The critic checked on arXiv that the abstract states "if and only if". k-automatic
  sequences are k-substitutive, so the 2-and-3 form of [42] is a special case.
- *Difficulty.* Hard: it needs Durand's theorem.
- *Lean.* Stated against the library's definitions in
  [Substitutive](Rule30Equivalents/Substitutive.lean) (the statement below typechecks with
  `sorry`), with the sufficient direction proved for integer bases.

  ```lean
  theorem problem1_iff_not_substitutive {α β : ℝ} (hα : IsPerron α) (hβ : IsPerron β)
      (hαβ : ∀ p q : ℕ, 0 < p → 0 < q → α ^ p ≠ β ^ q) :
      Rule30Prize.Problem1 ↔
        ¬ (IsSubstitutive α Rule30Prize.center ∧ IsSubstitutive β Rule30Prize.center)
  ```

  - The definitions: `IsSubstitutive α f` says f = φ ∘ x for a coding φ and a fixed point x of a
    substitution σ : B → List B with nonempty images (σ(x 0) σ(x 1) ⋯ = x, `IsFixedPoint`),
    prolongable on x 0 (abs(σ(x 0)) > 1), with every letter of B occurring in x, and α the dominant
    eigenvalue of the incidence matrix M b c = abs(σ(b))_c: an eigenvalue at least the modulus of
    every complex eigenvalue (`IsDominantEigenvalue`). `IsPerron α` says α > 1 is a real algebraic
    integer exceeding the modulus of each of its other conjugates; the integers k ≥ 2 are Perron
    numbers (`isPerron_natCast`).
  - The sufficient direction for integer bases, `problem1_of_not_substitutive` for any a, b ≥ 2 and
    `problem1_of_not_substitutive_two_three`: an eventually periodic sequence is k-automatic, hence
    k-uniformly morphic, hence k-substitutive (`isSubstitutive_of_eventuallyPeriodic`), since a
    k-uniform substitution has incidence row sums k and so dominant eigenvalue k
    (`isDominantEigenvalue_of_sum_eq`). For other Perron numbers this direction needs Lind's theorem
    that every Perron number is the dominant eigenvalue of a primitive integer matrix.
  - The uniform case is proved in [UniformMorphic](Rule30Equivalents/UniformMorphic.lean): Cobham's
    "little" theorem `isAutomatic_iff_isUniformMorphic` (k-automatic ⟺ a coding of a fixed point of
    a k-uniform morphism; the alphabet is kernel → Bool, the letter at n the column g ↦ g(n) of the
    kernel), so with Cobham's theorem `problem1_iff_not_uniformMorphic_two_three`: Problem 1 ⟺ c is
    not both 2- and 3-uniformly morphic, and `problem1_iff_not_uniformMorphic` for any
    multiplicatively independent a, b ≥ 2.
  - The Perron–Frobenius theorem for primitive matrices, which Mathlib lacks, is proved in
    [PerronFrobenius](Rule30Equivalents/PerronFrobenius.lean) (`tendsto_pow_div`: Aʲ/rʲ → v wᵀ). A
    primitive incidence matrix has its Perron root as dominant eigenvalue
    (`Substitutive.isDominantEigenvalue_of_isPrimitive`), and the lengths abs(σʲ(a)), the row sums
    of Mʲ, grow like c_a rʲ.
  - Integer bases do not reduce to Cobham's theorem: a substitution whose dominant eigenvalue is an
    integer k need not generate a k-automatic sequence. Numerically the k-kernel does not stabilize
    for a → aab, b → bc, c → c (k = 2), nor for the primitive a → ac, b → bbc, c → aabb (k = 3,
    other eigenvalues ±√2).
  - Primitive substitutive sequences are linearly recurrent, proved in
    [LinearRecurrence](Rule30Equivalents/LinearRecurrence.lean)
    (`isLinearlyRecurrent_of_isPrimitive`, also for codings): every word u occurs in every interval
    of L·abs(u) positions. Some σᵏ(b) contains every letter, so the blocks σⁿ(b) of each level have
    comparable lengths, and a word shorter than every block of level n lies in two adjacent blocks,
    hence in every block of level n + m. With it the Durand–Host–Skau bound
    (`length_lt_of_occursAt`): if such a sequence is not eventually periodic, two occurrences
    p < p + d of u have abs(u) < L d, by Morse–Hedlund.
  - What is missing is Durand's theorem itself. His proof [Dur11] uses the theorem of Durand and
    Rigo that the words occurring infinitely often in a sequence that is both α- and β-substitutive
    occur with bounded gaps, his 2002 theorem for "good" substitutions (growing, with a primitive
    sub-substitution of the same dominant eigenvalue), and a counting argument on concatenations of
    return words for the others.
- *Known.* No data exist for non-integer Perron bases; the kernel bounds of [42] cover only the
  integer case.
- *Sources.* [Dur11]; [Cob69].

**[43] gap-theorems: Problem 1 as a lower bound for unary input.**
- *Statement.* Problem 1 ⟺ no one-tape deterministic Turing machine decides
  L₁ = {1ⁿ : c(n) = 1} in time o(n log n) ⟺ no deterministic Turing machine with a read-only input
  tape decides L₁ in space o(log log n). So Problem 1 is exactly a computational lower bound for
  *unary* input; Problem 3 asks for one with binary input.
- *Proof route.* Apply [18] together with two gap theorems: one-tape time o(n log n) decides only
  regular languages [Tra64], [Hen65], [Har68], and space o(log log n) decides only regular
  languages [SHL65]. Regular languages are decided in real time.
- *Difficulty.* Hard: it needs the gap theorems and a machine model. Both forms are proved here.
- *Digit input* (proved). The Hennie–Trakhtenbrot theorem holds for every finite input alphabet
  ([OneTapeRegular](Rule30Equivalents/OneTapeRegular.lean), `DecidesLang.isRegular`,
  `isRegular_iff_exists_fast_decider`): a language decided by a one-tape machine in time
  o(n log n) is regular. Splicing at equal crossing sequences bounds them as for unary input, and
  then a prefix has a finite type (the crossing sequences it shows at its right end, and the
  outcome for the even ones) that determines its left quotient (Myhill–Nerode). The base-k digit
  language of c, least significant digit first, is regular iff c is k-automatic (its left
  quotients are the digit languages of the k-kernel). With Cobham's theorem:
  Problem 1 ⟺ c(n) is not decided both from the base-2 and from the base-3 digits of n by
  one-tape machines in time o(ℓ log ℓ), ℓ the number of digits
  (`problem1_iff_no_fast_digit_deciders`). Problem 3 asks for time n, exponentially more. The
  theorem of Stearns, Hartmanis and Lewis also holds for every input alphabet
  ([OfflineGap](Rule30Equivalents/OfflineGap.lean), `DecidesInSpace.isRegular`,
  `isRegular_iff_exists_small_space_decider`), so Problem 1 ⟺ c(n) is not decided both from the
  base-2 and from the base-3 digits of n by offline machines in space o(log log ℓ)
  (`problem1_iff_no_small_space_digit_deciders`).
- *Lean.* The time form is proved in [OneTapeGap](Rule30Equivalents/OneTapeGap.lean):
  `problem1_iff_no_fast_one_tape_decider`, from `eventuallyPeriodic_iff_exists_fast_decider`.
  The machine model is the textbook one: finitely many states, a finite tape alphabet, a two-way
  infinite tape, and a transition that writes a symbol and moves the head one cell left or right,
  or leaves it. The crossing-sequence theory is developed for a `Machine` whose states and
  symbols are arbitrary types; `TM` adds finiteness.
  `DecidesInTime M f T` says that on input 1ⁿ the machine has halted by step T(n), in an accepting
  state iff f(n). Mathlib's `Turing.TM0` is not used: a step of it either moves or writes, and its
  tape moves with the head, which makes crossing sequences awkward.
  - `cs X b T` is the crossing sequence of a run at the boundary b, the states just after each
    crossing.
  - `splice`: two halting runs with equal crossing sequences at b₁ and b₂ can be cut there and
    joined. The joined run halts, keeps the crossing sequences on both sides, and ends in the final
    state of the left run if the crossing sequence has even length, of the right run otherwise.
    The proof is a simulation invariant (`SpliceInv`) that follows one time in each run.
  - `eventuallyPeriodic_of_bounded`: bounded crossing sequences give eventual periodicity. By
    splicing, f(a + r) is determined by a finite type of the left length a (the crossing sequences
    at a, and the answer for the even ones), so two left lengths of the same type give a period.
  - `time_lower_bound` and `bounded` (Hennie's argument): take a shortest input 1ⁿ with a crossing
    sequence longer than K. On each side of it, the boundaries 1, …, n have distinct crossing
    sequences, or cutting would give a shorter input. At most (q + 1)^ℓ of them are shorter than ℓ,
    so T(n) ≥ (n/4)·log_{q+1}(n/4), which time o(n log n) rules out for large K.
  - The converse: `periodicTM` decides an eventually periodic f in n + 1 steps.

  The space form is proved in [OfflineGap](Rule30Equivalents/OfflineGap.lean), for every input
  alphabet α: `isRegular_iff_exists_small_space_decider`, and for unary input
  `problem1_iff_no_small_space_decider` (with `LogicAutomata.unaryLang c`, through
  `eventuallyPeriodic_iff_unary_isRegular`). An `OTM α` has finitely many states and work symbols,
  a two-way read-only input tape holding a word over α with blanks on both sides, and a work tape;
  `DecidesInSpace M L s` says that on every input w it halts, accepting iff w ∈ L, and keeps its
  work head within s(|w|) cells of the start. Seen on its input tape it is a `Machine` whose
  states are the work configurations, so `splice` applies to runs on words.
  - `rs_nodup`: in a halting run that never writes, the configurations after two rightward
    crossings of one boundary differ, or the run would loop. So a crossing sequence through N work
    configurations has length at most 2N + 1.
  - `space_lower_bound` (the argument of [SHL65]): in a shortest input on which the work head goes
    beyond K, the boundaries on each side of the input head at that moment have distinct crossing
    sequences, since `splice` passes through the configuration that goes beyond K. This gives
    n ≤ 2(N + 1)^(2N + 1) with N ≤ C^(2s(n) + 1), so log log n ≤ 4(s(n) + 1) log C, which space
    o(log log n) rules out for large K.
  - Bounded space leaves finitely many crossing sequences, and
    `OneTapeRegular.DecidesLang.isRegular_of_finite` applies (Myhill–Nerode on the types of
    prefixes). The converse, `dfaOTM`, runs a finite automaton and uses no work space.

  ```lean
  theorem problem1_iff_no_fast_one_tape_decider : Rule30Prize.Problem1 ↔
      ¬ ∃ (M : TM) (T : ℕ → ℕ),
        (fun n => (T n : ℝ)) =o[Filter.atTop] (fun n => (n : ℝ) * Real.log n) ∧
        DecidesInTime M c T
  ```

- *Sources.* [Tra64]; [Hen65]; [Har68]; [SHL65]; [TYL03].

---

## 4. Stronger statements

Each statement below implies Problem 1. All are open. For several, the converse is known to fail,
so they are strictly stronger.

| Statement | Why it implies Problem 1 | What is known | Sources |
|---|---|---|---|
| **No column is EP**: for every j, t ↦ cell(t, j) is not EP | take j = 0 | At most one column is EP (`Rule30Jen.periodic_column_unique`). No column is eventually constant (`no_column_eventually_constant`). | [Jen86], [W86] §6 |
| **FinConf**: for every nonzero finite row, no column is EP | apply it to the seed | Jen: at most one EP column. Condrey: no eventually constant column. Both are proved in the kit for every nonzero row with a leftmost black cell, so for NumberLike rows too (`Rule30FiniteConfigs.jen`, `no_column_eventually_constant`). A project search found no row supported in [−9, 9] whose center column has period ≤ 512 on [1024, 2048). CQ01 is exactly FinConf at period 2 for one column, whatever the transient (`Rule30FiniteConfigs.CQ01_iff_no_finite_period_two`; from time 0: `Rule30PeriodTwoSideways.CQ01_iff_no_finite_alternating`). | [Jen90], [Con26], [Kop23] |
| **NumberLike**: for every nonzero left-finite row, no column is EP | it implies FinConf | Width-2 traces are never EP ([Kop23] Thm 3.5). | [Kop23] |
| **LHC**: for every primitive word w, no finite driven left half is consistent with w^∞ | LHC ⟹ NumberLike ⟹ FinConf ⟹ Problem 1, with period 1 from Condrey | Q01 is LHC(10) and Q001 is LHC(001); C3, C3w and C3s001 follow from LHC. Searches up to width about 36 found no survivors. | project, round 1 |
| **Frozen-boundary conjecture** (new): for each of the 8 frozen-boundary steps fΦ (f an automorphism of the two lowest bits), each seed a with an unbounded orbit, and each d, t ↦ bit t + d of (fΦ)ᵗ(a) is not EP | take f = id, a = 1, d = 0 (`AutomatonGroup.problem1_of_frozenBoundaryConjecture`) | It also implies FinConf (`column_not_eventuallyPeriodic_of_conjecture`). Data: no eventual period ≤ 600 in 4000 steps for the 8 steps with seeds 1, 3, 5. Among all 4096 depth-4 forcings ℓΦ in group 2369 with seed 1, the 384 eventually periodic readouts all come from forcings that stop the orbit; the 3712 growing orbits have no eventual period ≤ 300 in 1500 steps. The family is closed under sections (Section 7.9). **Structure** ([FrozenBoundary](Rule30Equivalents/FrozenBoundary.lean)). Each step is rule 30 in the bulk with an autonomous rule on the two edge cells. On the three genuine frozen boundaries Φ, b, a the conjecture is equivalent to FinConf (`genuineFrozen_iff_finConfRows`; b embeds through ι(y) = 4y + 2(y mod 2) + 1). **The core** ([FrozenBoundaryCore](Rule30Equivalents/FrozenBoundaryCore.lean)). Some steps change edge bits that the bulk sees only as a fixed pattern. Dropping those bits reduces (0,0,1), (0,1,0) and (0,1,1), and (1,0,1) on seeds whose bit 1 is black, to Φ and b. For example, (0,1,γ) maps 2z to 2·b(z), and (0,β,1) maps 4z + 1 to 4·b(z) + 1. So the conjecture is equivalent to FinConf together with its core, the white-blinking edge of (1,0,1) (bit 1 white, bit 0 blinking) and the step (1,1,1), which is Φ followed by complementing the two edge cells (`frozenBoundaryConjecture_iff_core`). Numerically, a further 3/16 of the residues of (1,0,1) match finite-seed diagonal pairs at depth 4 or 5, but not by any rule visible mod 16. (1,1,1) matches nowhere. Above the edge bits, the core is rule 30 whose frozen boundary switches periodically between genuine ones. The white-blinking edge alternates Φ and b, and (1,1,1) cycles through Φ, a, a, b (`step_101_two_steps`, `step_111_four_steps`), so the core is about the elements b∘Φ and b∘a∘a∘Φ of group 2369. Data: the scan covers every non-constant period word of length ≤ 8, every offset 2–6 and every right part, for both core pieces with Φ as control. The forced seed is never finite (depth 300, longest white tail 20). **Proved for all 8 steps:** no readout of an unbounded orbit is eventually constant (`frozenBoundary_period_one`), and no two adjacent readouts are both EP (`not_adjacent_readouts`). **Period 2** ([FrozenBoundaryPeriodTwo](Rule30Equivalents/FrozenBoundaryPeriodTwo.lean)). Every step is triangular, so a seed is determined by its bits below d and its readout d (`eq_of_readout_eq`, `exact_death`): each right part has at most one seed whose readout alternates. `Q01` implies period 2 for all 8 steps (`frozenBoundary_period_two_of_Q01`): above an alternating readout the bits evolve as the zero-boundary left half. For Φ the period-2 question is exactly `CQ01` (`alternationFree_white_iff_CQ01`), and a and b follow. Data: for every step, d ≤ 8 and every right part, the forced seed has black cells at every depth checked up to 1200 (longest white run 19), and up to 12000 for d = 1 (longest white run 14). For (1,1,1) the column next to an alternating readout is not a finite-seed column. Over d ≤ 7, only 12 of its 254 right parts give a column whose last 700 of 1400 bits occur in a finite-seed column (d ≤ 9). For (1,0,1) the count is 181 of 254, close to its 11/16. So the period-2 question for (1,1,1) is a coupled question of its own: it is implied by `Q01`, but no reduction to `CQ01` is known. | own, 2026-10-17 |
| **Effective boundary**: t ↦ c(t) ∧ c(t + 1) is not EP | an EP c makes it EP | open | `Rule30MaskedJen` |
| **Every line**: no line of rational slope s with abs(s) < 1 carries an EP sequence | slope 0 is Problem 1 | Slopes ±1 are periodic (`Rule30Diagonals`). The other slopes tested look aperiodic (data, CA-structure survey). For a random configuration the cells along every line of velocity other than 1 are independent fair coins, so the statement holds almost surely (`Mixing.measurePreserving_line`, `ae_isNormal_lines`, `ae_every_line`). | [W86] §6, [W19] |
| **Unbounded runs**: 0ⁿ (or 1ⁿ) occurs in c for every n | if c were EP, its runs would be bounded, because c is not eventually constant (`center_not_eventually_constant`) | Strictly stronger: Thue–Morse has no run longer than 2. In 10⁷ bits the longest runs have lengths 22 and 23. For almost every configuration the longest runs grow like log₂ n (`LongestRuns.ae_tendsto_longestRun_trace`, the Erdős–Rényi law). | words survey |
| **Unbounded abelian complexity** | an EP c has abelian complexity ≤ T + P | Strictly stronger, as Thue–Morse shows. | [RSZ11] |
| **Non-atomic limit**: some limit point of the empirical measures (δ_c + ⋯ + δ_{σᴺc})/(N + 1) has no atoms | for an EP c every empirical measure, hence every limit point, is carried by the finitely many shifts σᵐc, m < T + P (`EmpiricalMeasures.problem1_of_nonatomic_mapClusterPt`) | Strictly stronger: a sequence with sparse aperiodic defects has the atomic limit of its periodic part. Normality gives the fair-coin limit, which has no atoms. | own reasoning |
| **No bounded remainder**: the number N(n) of black cells among the first n is not αn + O(1) for any real α | an EP c has N(n) = αn + O(1), with α the density of black cells in a period (`BoundedRemainder.problem1_of_unbounded_remainder`) | Strictly stronger: Sturmian sequences are not EP and have bounded remainder. The same works for the occurrences of any word (`problem1_of_unbounded_word_remainder`). A disjunctive c satisfies it (`unbounded_remainder_of_disjunctive`): a run of m black cells raises N(n) − αn by (1 − α)m, and a run of m white cells lowers it by αm. | own reasoning |
| **Problem 2 with unbounded discrepancy**: c has density 1/2 and N(n) − n/2 is unbounded | an EP c with density 1/2 has N(n) = n/2 + O(1) (`BoundedRemainder.problem1_of_problem2_of_unbounded_discrepancy`) | Of the two assumptions, Problem 2 is open and so is the discrepancy; for a random configuration both hold almost surely (its trace is normal, hence disjunctive; `BoundedRemainder.ae_unbounded_remainder_trace`). | own reasoning |
| **Oscillating discrepancy**: N(n) − n/2 is unbounded above and below | an EP c has N(n) = αn + O(1), so N(n) − n/2 is bounded below if α ≥ 1/2 and bounded above if α ≤ 1/2 (`BoundedRemainder.problem1_of_oscillating_discrepancy`) | Strictly stronger: a non-EP sequence of density 1/3 has N(n) − n/2 → −∞. Unlike the previous row it assumes nothing about the density, and it implies the no-bounded-remainder form. For a random configuration it holds almost surely with room to spare: N(n) − n/2 exceeds K√n and falls below −K√n infinitely often for every K (`Fluctuations.ae_oscillating_discrepancy_trace`, from Kolmogorov's zero-one law and the central limit theorem). | own reasoning |
| **Anti-Toeplitz**: no residue class k ↦ c(r + kP) is eventually constant. Density 1/2 along every arithmetic progression implies it | if c had period P, every class modulo P would be eventually constant; form (b) of [20] needs only one non-constant class | Holds for P = 1. Equidistribution of y_{Pk+r} implies it [W19]. | [JK69], [Wal49] |
| **Disagreements of positive density**: for every τ ≥ 1, c(t) ≠ c(t + τ) for a set of t of positive upper density; vanishing autocorrelations | if c had period P from T, there would be no disagreement at τ = P after T | Data: at least 49.96% disagreement for τ ≤ 300 in 10⁷ bits. A normal sequence has disagreement frequency exactly 1/2 at every lag, so the statement holds for almost every configuration (`Autocorrelation.tendsto_disagreements_of_isNormal`, `ae_tendsto_disagreements_trace`, `ae_infinite_disagreements_trace`). | [Gol67], [MS97]; algebra survey (data) |
| **Positive Besicovitch distance** from every periodic sequence | an EP c has distance 0 from a periodic sequence | Data: excess agreement of random size for P ≤ 1024. A normal sequence differs from every periodic sequence at a quarter of the times or more, so the distance is at least 1/4 for almost every configuration (`Autocorrelation.far_from_periodic_of_isNormal`, `ae_far_from_periodic_trace`). | [BFK97]; words survey (data) |
| **Positive entropy** of the orbit closure, or an uncountable orbit closure | an EP c has a finite orbit closure | Conjectured: the orbit closure is the full shift. | [LM95] |
| **Disjunctive**: every finite word occurs in c | p_c(n) = 2ⁿ eventually exceeds T + P | Every word of length ≤ 22 occurs within the first 58,671,803 steps [W19]. | [W19], project data |
| **Normality** of x₂ in base 2 (⟺ finite-state dimension 1); the seed is generic for (rule 30, Bernoulli) | normal ⟹ disjunctive. Normality also gives Problem 2. | 500,025,038 ones in the first 10⁹ bits [W19]. | [Bor09], [Wal49], [DLLM04], [W19] |
| **x₂ is transcendental** (likewise x_B) | transcendental ⟹ irrational | Conditional only: if c were automatic, [AB07] would apply. | [AB07] |
| **μ(x₂) = 2** (irrationality exponent) | it includes irrationality | Numerically about 2.0017 for q > 2^4096. Holds for almost every configuration (`IrrationalityExponent.ae_exponentTwo_trace`). | [Bug11], [BHWY16]; number-theory survey (data) |
| **c is not 2-automatic** ⟺ C(X) is transcendental over F₂(X) (Christol) ⟺ the expansion complexity is unbounded; also: not k-automatic for any k, not k-regular, not morphic, not a Mahler function | EP ⟹ automatic ⟹ morphic | Kernel bounds as in [42]. The expansion complexity is maximal (178) at N = 16000. The first equivalence, for every prime p, is `Christol.not_isAutomatic_iff_transcendental`. | [Chr79], [Die12], [MNW17], [ABS23]; algebra survey (data) |
| **L_n/n → 1/2** (the F₂ irrationality exponent of ξ is 2) | it forces L_n → ∞ | abs(L_n − n/2) ≤ 9.5 for n ≤ 10⁶. Thue–Morse also satisfies it. For almost every sequence abs(2L_n − n) ≤ 2⌊log₂ n⌋ + 2 from some n on, by two first-moment bounds and Borel–Cantelli (`LinearComplexity.ae_eventually_linComplexity`), so the statement holds almost surely (`ae_tendsto_linComplexity_trace`). | [Nie88], [MeWi17]; algebra survey (data) |
| **H_m ≠ 0 for all m ≥ 9** (integer Hankel determinants) | infinitely many nonzero H_m suffice ([32]) | True for 9 ≤ m < 45,000 (data). Not typical: it fails with probability at least 2⁻⁹ for a random configuration (`Typicality.measure_hankel_det_eq_zero_trace`). | algebra survey, [WM86] |
| **Hypertranscendence** (new): C(z) satisfies no algebraic differential equation P(z, C, C′, …, C⁽ⁿ⁾) = 0 with P ≠ 0 over ℚ | if c is EP, C is rational, hence differentially algebraic | Strictly stronger: Σ z^(n²) is built on the non-EP set of squares, is a theta function, and satisfies an algebraic differential equation [Jac48]. A Mahler function is either rational or hypertranscendental [ADH21], so a non-EP automatic c would give a hypertranscendental C. In general neither "not automatic" nor "hypertranscendental" implies the other. | [ADH21], [Jac48] |
| **Not a zero set in characteristic p** (new): S is not the zero set of a linear recurrence sequence over an infinite field of characteristic p, such as F_p(x) | if c is EP, S is the zero set of 1 − c, which is EP and so linear-recurrent | Strictly stronger: over F_p(x), u(n) = (x + 1)ⁿ − xⁿ − 1 has the non-EP zero set {pᵏ : k ≥ 0}. Derksen showed that such zero sets are p-automatic of a special form, so "c is not p-automatic" implies this statement. Over F_p(x), and over every countable field, it holds for almost every configuration, since such zero sets are countably many (`TypicalConditions.ae_not_zero_set_ratFunc_trace`). | [Der07] |
| **Π⁰₁ defect bound**: for all T and P ≥ 1, some t ∈ [T, T + 3·log₂(T + P + 1)] has c(t + P) ≠ c(t) | an EP c has arbitrarily long stretches without a defect | Holds for T + P ≤ 65536, with maximum defect distance 29 (own computation, logic survey). | logic survey |
| **Th(ℕ, +, S) is undecidable** | if c is EP, S is Presburger-definable and the theory is decidable | It would follow from disjunctiveness (own reasoning, below). In definable form: if multiplication is definable in (ℕ, 0, 1, +, S), with any parameters, Problem 1 holds (`PresburgerExpansion.problem1_of_mul_definable`): for an EP c every set definable in (ℕ, +, S) is semilinear, and the graph of multiplication is not. | logic survey, critic; [KNO26] |
| **Problem 3 and its relatives**: no polylog-time digit extraction; circuit lower bounds for n ↦ c(n) | EP or automatic ⟹ O(log n) time | Beyond current techniques: the best general-circuit lower bound for any explicit function is about 3.1n. For almost every configuration, by Shannon's counting argument, no circuit with at most 2ᵏ/(8k) gates computes t ↦ c(t) on t < 2ᵏ from the k binary digits of t, for all large k (`Circuits.ae_circuit_lower_bound_trace`). | [W19], [LY22], [FGHK16] |

**Undecidability from disjunctiveness** (logic survey and critic, own reasoning). Suppose every
finite word occurs in c. Then, as x ranges over ℕ, the windows S ∩ [x, x + k) − x realize every
subset of [0, k). So (ℕ, +, S) can quantify over finite sets, and it interprets weak monadic
second-order logic over (ℕ, +). That logic defines squaring, through the finite set
{0, 1, 4, …, y²}, whose consecutive differences grow by 2. Squaring defines multiplication, so the
theory is undecidable. The abstract of [KNO26] treats ⟨ℕ; +, P⟩ for linear recurrences, special
functions and the totient function. It does not confirm that an arbitrary disjunctive S suffices,
so this argument should not be attributed to [KNO26]. *Lean* ([PresburgerExpansion](Rule30Equivalents/PresburgerExpansion.lean)): both
first-order halves are proved. `mul_definable_of_center_disjunctive`: if every finite word occurs
in c, multiplication is definable in (ℕ, 0, 1, +, S) without parameters; a window encodes
{0, 1, 4, …, y²} through gaps that grow by 2 (`sqPred_iff`), and ab = c iff
(a + b)² = a² + b² + 2c. `problem1_of_mul_definable`: if multiplication is definable there,
Problem 1 holds. The undecidability of the theory itself is not formalized.

Lean definitions for several of these typecheck in scratch files (the merge's `StmtStronger.lean`
and `StmtReal.lean`, and the critic's `Additions2.lean`):

```lean
def NoColumnPeriodic : Prop := ∀ j : ℤ, ¬ Rule30Jen.EventuallyPeriodic (fun t => Rule30Jen.cell t j)
def FinConf : Prop :=
  ∀ x : ℤ → Bool, (∃ W : ℕ, ∀ p : ℤ, W < p.natAbs → x p = false) → (∃ p, x p = true) →
    ∀ j : ℤ, ¬ Rule30Jen.EventuallyPeriodic (fun t => Rule30Realization.evol x t j)
def Disjunctive : Prop :=
  ∀ w : List Bool, ∃ i : ℕ, ∀ j : Fin w.length, Rule30Prize.center (i + (j : ℕ)) = w.get j
/-- Arbitrarily long white runs occur. This implies Problem 1 only together with the proved
`Rule30Prize.center_not_eventually_constant`; as a predicate on arbitrary sequences it does not
exclude eventual periodicity (0, 0, 0, … satisfies it). -/
def UnboundedWhiteRuns : Prop := ∀ n : ℕ, ∃ i : ℕ, ∀ j < n, Rule30Prize.center (i + j) = false
def DefectBound : Prop := ∀ T P : ℕ, 0 < P → ∃ t, T ≤ t ∧ t ≤ T + 3 * Nat.log 2 (T + P + 1) ∧
  Rule30Prize.center (t + P) ≠ Rule30Prize.center t
def Transc : Prop := Transcendental ℚ x₂
def ExponentTwo : Prop := Irrational x₂ ∧ ∀ p > (2 : ℝ), ¬ LiouvilleWith p x₂
noncomputable def C : PowerSeries ℚ := PowerSeries.mk fun t => if Rule30Prize.center t then (1 : ℚ) else 0
def Hypertranscendental : Prop :=
  ∀ (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℚ), P ≠ 0 →
    MvPolynomial.aeval (fun i : Fin (n + 2) =>
      if (i : ℕ) = 0 then (PowerSeries.X : PowerSeries ℚ)
      else (⇑(PowerSeries.derivative (R := ℚ)))^[(i : ℕ) - 1] C) P ≠ 0
def NotZeroSetCharTwo : Prop :=
  ∀ (E : LinearRecurrence (RatFunc (ZMod 2))) (u : ℕ → RatFunc (ZMod 2)), E.IsSolution u →
    {t | u t = 0} ≠ {t | Rule30Prize.center t = true}
example : NoColumnPeriodic → Rule30Prize.Problem1 := fun h => h 0
```

**Strengthenings that are probably false.** Each of these implies Problem 1, but each probably
fails for c, because a normal (or merely disjunctive) sequence fails it:

- *MSO(ℕ, <, S) is undecidable.* If c is EP, S is MSO-definable and the theory reduces to S1S,
  which Büchi proved decidable. If c is disjunctive, the theory is decidable by Semenov's criterion
  (logic survey, own reading of [Sem84]).
- *c is uniformly recurrent and not purely periodic.* A recurrent EP sequence is purely periodic, so
  this implies Problem 1 (`StrongerStatements.problem1_of_recurrent_not_purelyPeriodic`, with
  recurrence alone). A normal sequence is not uniformly recurrent.
- *Ω(c) is minimal and infinite* (Ω(c) as in [35]). A normal c has Ω(c) equal to the full shift,
  which is not minimal.
- *c is a non-periodic Toeplitz sequence.* Toeplitz sequences are uniformly recurrent, so this fails
  for a normal sequence.
- *The orbit closure of c is not sofic.* A disjunctive c has the full shift as its orbit closure,
  and the full shift is sofic.
- *The defect bound with coefficient 2.* Heuristically, this would eventually fail (logic survey).

*Correction.* Earlier versions listed "c is uniformly recurrent", "Ω(c) is minimal" and "c is a
Toeplitz sequence" without the added clauses. In that form they do not imply Problem 1: every purely
periodic sequence has all three properties (the Jacobs–Keane definition [JK69] admits periodic
Toeplitz sequences). Without the clauses they only reduce Problem 1 to "c is not purely periodic",
which is still open (Section 5). They also contradicted Section 6.3, which correctly treats
recurrence as independent of Problem 1 (critic).

*Lean.* The implications "statement ⟹ Problem 1" of the table are proved in
[StrongerStatements](Rule30Equivalents/StrongerStatements.lean) (`problem1_of_*`) for the effective
boundary, every line, unbounded runs, anti-Toeplitz, disagreements, the Besicovitch distance,
the orbit closure and positive entropy, disjunctive and normal, x₂ transcendental, Lₙ/n → 1/2,
the Hankel determinants, the defect bound, hypertranscendence, unbounded abelian complexity, the
irrationality exponent μ(x₂) ≥ 2 (`problem1_of_irrExponentGE`: a rational has only finitely many
approximations of order 3/2; by Dirichlet's theorem it is in fact equivalent to Problem 1,
`problem1_iff_irrExponentGE`) and "not a k-Mahler function" (`problem1_of_not_isMahler`: P/Q
satisfies P(z^k)Q(z)F(z) − P(z)Q(z^k)F(z^k) = 0) and unbounded expansion complexity
(`problem1_of_expansionComplexity_unbounded`: Q(X)Y − P(X) vanishes at C exactly), and "not
morphic" (`problem1_of_not_isMorphic`: an EP sequence is a coding of the fixed point of σ(0) = 0 1,
σ(i) = i + 1 on its positions; the fixed point must be generated from its first letter,
abs(σ(x(0))) ≥ 2, since otherwise the identity morphism makes every sequence morphic, and then
morphic sequences are countably many, `countable_setOf_isMorphic`), "not k-regular over some field"
(`RegularSequences.problem1_of_not_regularSeq`), and "x_β ∉ ℚ(β) for some real β > 2", for
example a Salem number (`PisotNumbers.problem1_of_not_mem_adjoin`). For a density or a distance the
hypothesis used is the weaker "infinitely many". The others are proved elsewhere: no column EP and
FinConf through Jen's theorem, the frozen-boundary conjecture
(`AutomatonGroup.problem1_of_frozenBoundaryConjecture`), not 2-automatic
(`Automatic.problem1_of_not_automatic`), the zero sets in any characteristic
(`LinearRelations.problem1_of_not_zero_set`), and Problem 3 ([ProblemThree](Rule30Equivalents/ProblemThree.lean)).

*Almost surely.* For almost every configuration the center column satisfies eighteen of these
statements ([Typicality](Rule30Equivalents/Typicality.lean), `ae_strongerStatements_trace`): the
effective boundary, every line, unbounded runs in both colors, anti-Toeplitz, disagreements, the
Besicovitch distance, the uncountable orbit closure, positive entropy, disjunctive and normal, x₂
transcendental, μ(x₂) ≥ 2, unbounded abelian complexity, not morphic, recurrent but not purely
periodic, Lₙ/n → 1/2 ([LinearComplexity](Rule30Equivalents/LinearComplexity.lean)), and not
k-Mahler for every k ≥ 2 (a solution of a Mahler equation is determined by finitely many
coefficients, `StrongerStatements.countable_setOf_isMahler`; every series is 1-Mahler), and
unbounded expansion complexity (a nonzero g(X, Y) over 𝔽₂ has finitely many roots in 𝔽₂⟦X⟧,
`finite_roots_series`). Most follow from disjunctivity alone. It also has μ(x₂) = 2
([IrrationalityExponent](Rule30Equivalents/IrrationalityExponent.lean), `ae_exponentTwo_trace`,
Khinchin's theorem): the first k digits determine ⌊2ᵏx₂⌋ up to one, so x₂ lies within ℓ of a
given point with probability at most 8ℓ, and for p > 2 the rationals m/n within C/n^p of x₂ have
summable probabilities (Borel–Cantelli). Transcendence uses that the binary value separates
sequences with infinitely many ones (`baseValue_injOn`) and that the fair-coin measure has no atoms
(`RandomConfigurations.coins_singleton`); "not morphic" uses that morphic sequences are countably many. The defect bound
is not typical: it fails with probability at least 2⁻⁵, whenever the column starts with five equal
cells (`measure_not_defectBound_trace`). Neither is H_m ≠ 0 for all m ≥ 9: it fails with
probability at least 2⁻⁹, whenever the column starts with nine white cells, since then the first
row of H_9 vanishes (`measure_hankel_det_eq_zero_trace`). The sufficient conditions proved in other
files hold almost
surely too ([TypicalConditions](Rule30Equivalents/TypicalConditions.lean),
`ae_sufficientConditions_trace`): unbounded remainders N(n) − αn for every α, also for every word
w (for α = 2^-|w| the block w^L raises the remainder), an oscillating discrepancy, unpredictability, a non-atomic limit of the empirical measures, not k-automatic (the
k-automatic sequences are countably many, `Automatic.countable_setOf_isAutomatic`), automatic
complexity → ∞, multiplication definable in (ℕ, +, S), density 1/2 along every progression, a
transcendental generating function over 𝔽_p(X) (Christol) and over ℚ(X), the golden-power, unbordered-factor and
Lempel–Ziv forms, black times that are not the zero set of a linear recurrence over ℚ
(Skolem–Mahler–Lech), a finite field or any countable field such as 𝔽_p(X) (such zero sets are
countably many, `ae_not_zero_set_countable_trace`), Prize Problem 3 in both readings (no one-tape machine
computes the column at all: a machine computes at most one sequence, and machines are countably
many up to relabeling, `countable_setOf_decidesBin`), and x_β ∉ ℚ(β) for every real β > 2
(`ae_value_not_mem_adjoin_trace`). So all three Prize problems hold for almost every configuration
(`TypicalConditions.ae_prizeProblems_trace`). The generating function has the unit circle as
natural boundary, the condition of [41]
([RandomNaturalBoundary](Rule30Equivalents/RandomNaturalBoundary.lean),
`ae_circleIsNaturalBoundary_trace`, by the Paley–Zygmund inequality and Kolmogorov's zero-one law).
The circuit relative of Problem 3 holds too: for all
large k no circuit with at most 2ᵏ/(8k) binary gates computes t ↦ c(t), t < 2ᵏ, from the binary
digits of t, since there are at most (16(k + s)²)^s circuits with s gates and each computes the
random function with probability 2^(−2ᵏ) ([Circuits](Rule30Equivalents/Circuits.lean),
`ae_circuit_lower_bound_trace`). In the sense of category the picture splits: a
countable set of center columns is meager, so for a comeager set of configurations the column is
not automatic, not morphic and not Mahler, and Problems 1 and 3 hold, but Problem 2 fails, since
density 1/2 is meager (`residual_trace_notMem`, `residual_prizeProblems_trace`).

---

## 5. Weaker statements

Each statement below is implied by Problem 1.

- **NoPer(P), for a fixed P**: c has no eventual period P. Status:
  - P = 1 is proved, for every column (`Rule30Prize.no_column_eventually_constant`).
  - Every P ≤ 4096 with transient T ≤ 8192 is excluded (`Rule30Window.no_small_eventual_period`,
    kernel-checked).
  - Any eventual period has T + P ≥ 16359 (`Rule30FactorWindow.transient_add_period_ge`,
    kernel-checked).
  - P = 2 is reduced to Q01 (`not_eventually_period_two_of_Q01`) and to CQ01. Q01 is proved for
    starts of width ≤ 52 (`q01_width_le_52`). CQ01 says that no finite
    configuration keeps the center alternating from time 0
    (`Rule30PeriodTwoSideways.CQ01_iff_no_finite_alternating`); equivalently, for every finite right
    half R one explicit left row Ψ(R) has infinitely many black cells (`CQ01_iff_Psi`), and a left
    row keeps the center alternating exactly until its first difference from Ψ(R)
    (`exact_death_center`).
  - Least period 3 is reduced: for the word 001 to AbsorptionT t001, Q001 or C3s001; for 011 to
    C3w.
  - Least period 4 is reduced to Absorption (`least_period_four_of_absorption`).
  - Strip certificates exclude 30 periodic words of lengths 8–13 (`Rule30StripCertificateTable`),
    and long black runs exclude many periods (`Rule30BlackRuns`).
  - The 10⁹-bit data exclude P ≤ 2.5·10⁸ with T ≤ 5·10⁸ (data only; project brief).
  - Problem 1 is the conjunction of NoPer(k!) over all k ([14]).
- **Not purely periodic** (the case T = 0). The kernel gives P ≥ 16359. This statement would be
  equivalent to Problem 1 if c were known to be recurrent, since a recurrent EP sequence is purely
  periodic (`StrongerStatements.IsRecurrent.purelyPeriodic`,
  `problem1_iff_not_purelyPeriodic_of_recurrent`).
- **No eventual period 2^k.** Equivalent forms: no tail extends to a continuous function ℤ₂ → F₂;
  the F₂ Mahler (binomial) coefficients of every tail are not eventually 0 (via Lucas' theorem).
  This is open, since it includes periods 2 and 4. Replacing ℤ₂ by the profinite integers gives back
  Problem 1. Mathlib has `PadicInt.mahler`, `PadicInt.mahlerEquiv` and `PadicInt.hasSum_mahler`
  (number-theory and algebra surveys).
  - *Lean.* Both equivalences are proved in [TwoAdicPeriods](Rule30Equivalents/TwoAdicPeriods.lean),
    for every prime p in place of 2: for every bit sequence (`exists_continuous_extension_iff`,
    `exists_fwdDiff_eq_zero_iff`), and for c (`noPrimePowPeriod_iff_not_continuous`,
    `noPrimePowPeriod_iff_fwdDiff`; for p = 2 `noTwoPowPeriod_iff_not_continuous`,
    `noTwoPowPeriod_iff_fwdDiff`). A continuous ℤ_p → Bool is constant on all balls of some radius
    (Lebesgue's number lemma on the compact ℤ_p), so it reads only α mod p^k. The Mahler
    coefficients are Mathlib's forward differences Δⁿu(0); over F₂ they are Σ_{j ≤ n} C(n, j)u(j).
    Lucas' theorem is not needed: in characteristic p the coefficients C(p, j) with 0 < j < p
    vanish, so Δ^(p^k)u(t) = u(t + p^k) − u(t), and Newton's forward formula writes Δ^(p^k)u(t)
    through the coefficients Δ^(j + p^k)u(0). The profinite form is proved in
    [ProfiniteIntegers](Rule30Equivalents/ProfiniteIntegers.lean):
    `problem1_iff_no_continuous_extension`, Problem 1 ⟺ no tail of c extends to a continuous
    function Ẑ → Bool. Mathlib has no Ẑ, so `Zhat` is the inverse limit of the rings ℤ/(k+1)!ℤ, a
    cofinal subsystem, inside the product of the finite discrete spaces Fin (k+1)!. A continuous
    function to Bool is constant on a cylinder around each point, hence (the system is a chain)
    on a cylinder over one coordinate; compactness gives one coordinate K for all points, so the
    tail has period (K+1)! (`exists_level`, `exists_continuous_extension_iff`).
- **Jen's pairs and masked Jen** (proved):
  - c and column j ≠ 0 are not both EP (`Rule30Jen.jen`);
  - c and c ∨ (column 1) are not both EP;
  - c and column 1 restricted to the white times of c are not both EP
    (`Rule30MaskedJen.masked_jen`, `orCol_not_eventuallyPeriodic`, `window_jen`, `finitary_jen`).

  Barrier: rules 90, 150 and 210 satisfy all of these, yet their center columns are eventually
  constant (`Rule30Realization.barrier`). So these facts alone cannot give Problem 1.
- **Number-theoretic shadows of the kernel bounds**: x₂ ≠ p/q for every q ≤ 16359 ([1]); a fraction
  a/b with b odd equal to α must have log₂abs(a) + b ≥ 16357 ([15]).
- **S is not first-order definable in (ℕ, <)** (new; true). S is not definable, even with
  parameters, in (ℕ, <) or in (ℕ, succ). The subsets of ℕ definable there are exactly the finite
  and the cofinite sets (quantifier elimination for (ℕ, <, 0, succ), or an Ehrenfeucht–Fraïssé
  argument). So the statement is equivalent to "c is not eventually constant", which is the proved
  `Rule30Prize.center_not_eventually_constant`. It is the bottom rung of a logic ladder (Section 7).
  - *Difficulty.* Moderate: the model-theoretic lemma must be formalized.
  - *Lean.* Proved in [OrderDefinable](Rule30Equivalents/OrderDefinable.lean):
    `not_definable_order` (the statement below), and `not_definable` for any set of parameters.
    `eventually_const_of_definable` shows that every set definable in (ℕ, ≤), with any parameters,
    is eventually constant, by an Ehrenfeucht–Fraïssé argument on clamped distances: assignments
    whose points (variables, constants of the formula, and 0) have the same pairwise distances cut
    off at ± 2^d satisfy the same formulas of quantifier depth d (`realize_iff_of_clamp`), because
    a new point can always be matched with distances cut off at half the bound (`exists_extension`).
    `orderStructure` is a definition, not an instance, so the statement needs `letI`:

    ```lean
    theorem not_definable_order :
        letI := FirstOrder.Language.orderStructure (M := ℕ)
        ¬ (Set.univ : Set ℕ).Definable₁ FirstOrder.Language.order {t | Rule30Prize.center t = true}
    ```

  - *Sources.* [Mar02] §3.1; critic.

---

## 6. Related questions, including Problems 2 and 3

### 6.1 Problem 2: density 1/2

Prize Problem 2 asks whether each color occurs on average equally often in the center column
[W19]. Its forms:

- the project's `Rule30Prize.Problem2`, stated with integers:

  ```lean
  def blackCount (n : Nat) : Nat := ((List.range n).filter center).length
  def Problem2 : Prop :=
    ∀ k : Nat, 0 < k → ∃ N, ∀ n, N ≤ n → k * (2 * (blackCount n : Int) - n).natAbs ≤ n
  ```

- formal-conjectures: `{t | centerColumn t}.HasDensity (1/2)`, where `Set.HasDensity` comes from
  its own ForMathlib layer [FC];
- Wolfram: `DiscreteLimit[Total[c[t]]/t, t -> Infinity] == 1/2` [W19] (proved:
  `ProblemTwo.problem2_iff_tendsto`, the instance for c of `halfDensity_iff_tendsto`, which holds
  for every bit sequence);
- x₂ is simply normal in base 2. This uses that c is not eventually constant, so c is the unique
  binary expansion of x₂ (proved: `ProblemTwo.problem2_iff_simplyNormal`, through
  `binDigit_centerBinary`);
- the orbit of x₂ under the doubling map y ↦ 2y mod 1 lies in the upper half (1/2, 1) of the circle
  with frequency 1/2, since c(t) is black iff 2ᵗx₂ mod 1 > 1/2 (proved:
  `NumberTheory.problem2_iff_doubling`, through `center_iff_fract`; the Problem 1 form is
  `problem1_iff_doubling_not_preperiodic`);
- lim_{x→1⁻} (1 − x)·Σ c(t)xᵗ = 1/2. The Abelian direction is elementary. The converse is the
  Hardy–Littlewood–Karamata Tauberian theorem [HL14], [Kar30], which applies because the
  coefficients are nonnegative;
- the same density statement for the center columns of rules 86 (single black cell), 135 and 149
  (single white cell on a black background), by the reflection and complement symmetries
  (proved: `Symmetry.problem2_iff_rule86`, `problem2_iff_rule135`, `problem2_iff_rule149`;
  complementing a sequence keeps density 1/2, `halfDensity_not_iff`);
- the Hölder means of every order k ≥ 1 (the k-fold iterated Cesàro means) of c tend to 1/2
  (proved: `HolderMeans.problem2_iff_holder`). Iterating means preserves limits; conversely the
  mean of a bounded sequence has increments O(1/n), and Hardy's Tauberian theorem
  (`tendsto_of_tendsto_mean`: Cesàro limit plus increments O(1/n) give convergence) removes one
  mean at a time;
- the Cesàro means (C, k) of c tend to 1/2, for every k ≥ 1 (proved:
  `CesaroMeans.problem2_iff_cesaroMean`). By Toeplitz's lemma for regular weighted means
  (`tendsto_weighted`), (C, k) gives (C, k + 1) (hockey-stick weights) and the Abel mean (weights
  (1 − x)^(k+1) C(n + k, k) xⁿ, through ∑ aₙxⁿ = (1 − x)ᵏ ∑ S⁽ᵏ⁾ₙ xⁿ), and the
  Hardy–Littlewood–Karamata theorem returns from the Abel mean to (C, 1);
- the k-th black cell of c occurs at time 2k + o(k), equivalently the mean gap between
  consecutive black cells tends to 2 (proved: `BlackTimes.problem2_iff_trueTime`,
  `problem2_iff_mean_gap`). The time of the k-th black cell (`Nat.nth`) and the number of black
  cells before n (`Nat.count`) are inverse to each other, so density L > 0 is the same as the k-th
  occurrence at time k/L + o(k) (`tendsto_count_div_iff`);
- the ergodic form: every limit point ν of the empirical measures
  (δ_c + δ_{σc} + ⋯ + δ_{σᴺc})/(N + 1) on {0,1}^ℕ has ν[1] = 1/2 (proved:
  `EmpiricalMeasures.problem2_iff_mapClusterPt`). The space of probability measures on {0,1}^ℕ is
  compact (Mathlib's Prokhorov theorem), ν ↦ ν[1] is continuous because [1] is clopen
  (portmanteau), and the mass of [1] under the N-th empirical measure is the proportion of black
  cells. Every such limit point is shift-invariant (Krylov–Bogolyubov,
  `EmpiricalMeasures.map_shift_of_mapClusterPt`). In the same terms, c is normal iff its empirical measures converge weakly to the
  fair-coin measure (`EmpiricalMeasures.isNormal_iff_tendsto_empirical`; cylinders form a
  π-system of small clopen neighbourhoods), and the trace of almost every configuration is
  generic for the fair coin (`ae_tendsto_empirical_trace`).

Both Lean forms are proved in [ProblemTwo](Rule30Equivalents/ProblemTwo.lean), the second through
the Hardy–Littlewood–Karamata theorem, which the kit proves in
[Tauberian](Rule30Equivalents/Tauberian.lean) (`tendsto_cesaro_of_tendsto_abel`, Karamata's
proof: polynomial weights, the Weierstrass theorem, and continuous ramps around the indicator of
[e⁻¹, 1]), together with the Abelian direction for bounded sequences
(`tendsto_abel_of_tendsto_cesaro`):

```lean
theorem problem2_iff_tendsto : Rule30Prize.Problem2 ↔
    Filter.Tendsto (fun n : ℕ => (Rule30Prize.blackCount n : ℝ) / n) Filter.atTop (nhds (1 / 2))
theorem problem2_iff_abel : Rule30Prize.Problem2 ↔
    Filter.Tendsto (fun x : ℝ => (1 - x) * ∑' t, (if Rule30Prize.center t then (1 : ℝ) else 0) * x ^ t)
      (nhdsWithin 1 (Set.Iio 1)) (nhds (1 / 2))
```

Mathlib has Abel's theorem (`Complex.tendsto_tsum_powerSeries_nhdsWithin_stolzSet`,
`Real.tendsto_tsum_powerSeries_nhdsWithin_lt`, Analysis/Complex/AbelLimit.lean). It has no
Tauberian theorem, no normal numbers, and no natural-density predicate; `schnirelmannDensity` is a
different notion.

Problem 2 transfers verbatim to rule 86 and to the stripe seeds (same column), and to rules 135 and
149 (complemented column; density 1/2 is preserved).

Relation to Problem 1:

- As properties of sequences the two are independent: (01)^∞ has density 1/2 and is periodic, and
  non-EP sequences of density 1/3 exist.
- Normality implies both (`StrongerStatements.problem1_of_isNormal`,
  `ProblemTwo.problem2_of_isNormal`). In the dynamical reading of Borel and Wall, c is normal iff the
  orbit of x₂ under the doubling map visits every dyadic interval [k/2^m, (k + 1)/2^m) with
  frequency 2^−m (`NumberTheory.isNormal_iff_doubling`): the word w occurs at t iff 2ᵗx₂ mod 1 lies
  in the dyadic interval of the numeral of w (`occurs_iff_fract`).
- Density 1/2 along every arithmetic progression implies the anti-Toeplitz statement, which implies
  Problem 1 (Section 4; `ProblemTwo.problem1_of_density_on_progressions`).
- Problem 2 together with an unbounded discrepancy N(n) − n/2 implies Problem 1, because an
  eventually periodic sequence of density 1/2 has N(n) = n/2 + O(1) (Section 4;
  `BoundedRemainder.problem1_of_problem2_of_unbounded_discrepancy`).
- A discrepancy N(n) − n/2 that is unbounded above and below implies Problem 1 with no assumption on
  the density, because an eventually periodic sequence has bounded discrepancy on the side of its
  density (`BoundedRemainder.problem1_of_oscillating_discrepancy`).
- An explicit periodic tail would decide Problem 2 [W19].

Problem 2 is Π⁰₃ (`Computability.problem2_iff_forall_exists_forall`). For a random configuration the
trace is a fair-coin sequence, and the number of black cells among the first n deviates from n/2 on
the scale √n/2: (count − n/2)/√n converges in distribution to the normal law with variance 1/4
(`RandomConfigurations.tendstoInDistribution_count_trace`, through Mathlib's central limit theorem).
At every finite n, a deviation of at least nδ has probability at most 2·exp(−2nδ²)
(`RandomConfigurations.measureReal_abs_count_trace_ge_le`, through Mathlib's Hoeffding inequality),
so by Borel–Cantelli, for almost every configuration, the count is within √(n log n) of n/2 for all
large n (`RandomConfigurations.ae_eventually_abs_count_trace_lt`). In the other direction, for every
K the count exceeds n/2 + K√n and falls below n/2 − K√n infinitely often, so it equals n/2 for
infinitely many n (`Fluctuations.ae_frequently_le_imbalance_trace`,
`ae_frequently_imbalance_le_trace`, `ae_frequently_balanced_trace`; by Kolmogorov's zero-one law,
with the central limit theorem for positive probability). So random fluctuations lie between K√n,
for every K, and √(n log n). That is the yardstick for the data: the first 10⁹ bits contain
500,025,038 ones, about 1.6 standard deviations from half [W19].

### 6.2 Problem 3: computational effort

Prize Problem 3 asks whether computing c(n) requires at least O(n) effort [W19]. Wolfram's formal
statement is
`NotExists[m, ForAll[n, machine[m][n][[1]] == Last[c[n]]] && MaxLimit[machine[m][n][[2]]/n, n -> Infinity] < Infinity]`,
with Turing machines reading n. Notes:

- Read literally, it forbids even O(n) algorithms, which is stronger than the verbal "at least
  O(n)" (Wolfram survey).
- The machine model matters. On a unit-cost RAM with bitwise operations on unbounded integers, [25]
  computes c(n) in O(n) operations, so the literal statement is false in that model (synthesis, own
  reasoning).
- Chain of implications: Problem 3 ⟹ no polylog-time digit extraction ⟹ c is not automatic ⟹
  Problem 1. Wolfram notes that Problem 3 implies Problem 1 [W19].
- Problem 1 is itself exactly the analogous statement for *unary* input ([43]).
- The literal statement is Π⁰₂.
- Elsewhere it is formalized nowhere, and formal-conjectures omits it as model-relative. Mathlib's
  `Turing.TM2ComputableInTime` measures time in the input length, so "O(n)" would correspond to
  O(2^len).
- *Lean.* [ProblemThree](Rule30Equivalents/ProblemThree.lean) states it in the one-tape model of
  [OneTapeGap](Rule30Equivalents/OneTapeGap.lean), with the binary digits of n (least significant
  first) as input: `Problem3` (literal: no machine computes c(n) in time O(n)) and `Problem3Verbal`
  (verbal: none in time o(n)), with `problem3Verbal_of_problem3`. A machine whose states are the
  2-kernel computes every 2-automatic sequence in |bin n| + 1 = O(log n) steps
  (`decidesBinInTime_kernelTM`), so `not_isAutomatic_of_problem3Verbal`, `problem1_of_problem3Verbal` and
  `problem1_of_problem3` hold: the chain above, formally.
- Its circuit-complexity strengthenings are beyond current lower-bound techniques [LY22], [FGHK16],
  and natural proofs are a barrier [RR97].
- In the query model the t-step map is provably linear. A decision tree that reads cells of the
  initial row one at a time and computes the center cell after t ≥ 2 steps has depth at least
  2t − 1, since a tree of depth d computes a function of algebraic degree at most d over 𝔽₂ and
  the t-step map has degree 2t − 1 (Section 6.3). Lean:
  [QueryComplexity](Rule30Equivalents/QueryComplexity.lean), `le_depth_of_eval_eq`, from
  `coef_eval_eq_zero` and `AlgebraicDegree.coef_center_top`; querying the whole light cone, depth
  2t + 1, suffices (`exists_depth_eq`). This concerns arbitrary initial rows;
  for the single seed there is nothing to query, and Problem 3 asks about the input n.
- Problem 3 transfers to rules 86, 135 and 149 and to the stripe seeds, since their columns are
  identical or complemented (an O(1) difference).

### 6.3 Other related questions

- **Column j ≠ 0, and the white seed (column −1).** "Problem 1 or column j is not EP" is proved
  (Jen). So proving "Problem 1 ⟺ column j is not EP" is the same as proving both (library,
  `Realization.problem1_iff_column_iff_both`). No other column can be shown equivalent to Problem 1 without
  solving both problems. See also `Rule30WhiteSeed.problem1_black_or_white` and
  `problem1_30_or_135`.
- **Diagonals (solved).** Right diagonals are purely periodic, with periods dividing 2^j ([26]).
  Left diagonals are eventually periodic (`Rule30Diagonals.R_periodic`, `D_periodic`; [Jen86]
  Thm 4; [Row06]). Records of the left periods occur at 1, 4, 9, 30, 401, 87868 (A364239). The
  abstracts of [Ner26a] and [Ner26b] support unbounded diagonal periods and a lower bound
  ⌊m/2⌋ + 1 on the period at depth m (checked by the critic).
- **Lines of a single other slope** p/q ∉ {0, ±1}: open, and numerically aperiodic (CA-structure
  survey, 6000 rows).
- **Powers of 3: the same readout with carries.** x ↦ 3x is also an invertible T-function. The
  columns of the bit grid of 3ⁿ are periodic from the start, and the middle looks random [Row09].
  The readout "bit t of 3ᵗ" is the analogue of Problem 1, and it is open. The difference is memory:
  bit i of Φ(x) reads only bits i, i − 1, i − 2, so Φ has a light cone and rule 30's group is
  locally-finite-by-ℤ (Section 7.9). Multiplication by 3 carries, and its bit i reads every lower
  bit.
- **The project's period reductions**: Q01, CQ01, Q001, C3, C3w, C3s001, Absorption and AbsorptionT.
  Each is uniform over finite rows, and each is used to exclude one period or one word. Problem 1
  implies none of them.
- **Finite rings.** Rule 30 on a ring of n cells has periods of about 2^(0.61n) to 2^(0.63n).
  Started from one black cell, the ring's center agrees with c(t) for every t < n, because the cell
  (t, 0) sees only the cells −t, …, t, and the whole light cone agrees while 2t < n
  ([FiniteRings](Rule30Equivalents/FiniteRings.lean): `evol_ringSeed_eq_center`,
  `evol_ringSeed_eq_cell`). *Correction:* an earlier version gave t ≤ (n − 1)/2 for the center,
  which is the bound for the whole cone. For n = 3 the ring's center is 1, 1, 0, 0 against c = 1, 1,
  0, 1, so t < n cannot be improved in general. No implication is known [W86], [W19]. Wolfram
  (2019): "I, at least, don't immediately see."
- **Other rules.** Rule 45, code 10, rule 22 with two seeds, and the 4-color code 150898, which has a
  long transient. Rules 161 and 69540422 have non-periodic center columns that are nonetheless
  regular (automatic). Rules 90, 150 and 210 are barrier rules with eventually constant centers
  ([W19], [NKS]; Wolfram survey). The NKS p. 956 note says that rule 30 is the square of the
  3-color, radius-1/2 rules 11736, 11739 and 11742; this was not checked here.
- **Other seeds and backgrounds**: a single white cell; defects in periodic backgrounds; random
  initial conditions. Under the uniform Bernoulli measure every block occurs in every column with
  equal frequency [W86] (proved: `Mixing.ae_isNormal_columns`), but that says nothing about the
  single seed.
- **Mahler's 3/2 problem, Z-numbers, and Kopra's ×p/q automata.** Wolfram's 1985 list of open
  problems already notes that the leading binary digits of the fractional parts of (3/2)ⁿ form the
  center column of a particular CA [W85]. Rule 30 and the ×p/q automata are both rapidly left
  expansive [Kop23]. Width-1 aperiodicity is solved for ×p/q [Kop21] but open for rule 30. Kopra's
  Problem 4.8 is Problem 1.
- **Kopra's limit-point theorems** (new; proved, related). For the single seed δ:
  - the right halves frac(F^t δ) = (cell(t, p))_{p≥0} ∈ {0,1}^ℕ have infinitely many limit points
    ([Kop23] Thm 4.7);
  - frac(F^t δ) = frac(δ) holds for only finitely many t ([Kop23] Thm 4.5).

  In terms of the dyadic numbers y_t = Σ_{p≥0} cell(t, p)·2^−(p+1), where c(t) = [y_t ≥ 1/2],
  Problem 1 is the open question of whether the first-digit sequence of (y_t) is EP. Kopra derives
  both results from Thm 4.6: if (frac F^t x) had finitely many limit points, then for every w some
  width-w trace would be EP. That contradicts Thm 3.5, which for rule 30 is Jen's two-column
  theorem. These are the rule-30 analogues of Pisot–Vijayaraghavan (Thm 4.7) and of Dubickas
  (Thm 4.5) for (p/q)ⁿ mod 1 [Vij40], [Dub08]. They are proved, but they neither imply nor follow
  from Problem 1. *Lean:* proved in [LimitPoints](Rule30Equivalents/LimitPoints.lean), with
  Mathlib's `MapClusterPt` for limit points. `exists_periodic_window` is Thm 4.6 for every
  radius-1 automaton: the windows that occur infinitely often number at most the limit points (by
  compactness of {0,1}^ℕ each extends to one), and along k + 1 nested windows the count cannot drop
  every time; where it does not, the window at the next time is a function of the window now, so it
  is eventually periodic. `infinite_limitPoints_cell` and `infinite_limitPoints_evol` are Thm 4.7
  for the single seed and for every configuration with a leftmost black cell, through
  `Rule30Jen.not_adjacent` and `Rule30FiniteConfigs.not_adjacent`. Thm 4.5 is
  `half_cell_eq_zero_iff` for the single seed (the right edge rules out any return), and
  `RightHalfReturns.finite_returns` for every configuration with a leftmost black cell, also
  infinite to the right ([RightHalfReturns](Rule30Equivalents/RightHalfReturns.lean)). Its
  Lemma 4.3 (`eventuallyPeriodic_of_return`): one return at t ≥ 1 makes the right half of x
  eventually periodic, since after it the column pairs far right repeat with period t, by
  left-permutivity they determine the cells to their left, and Morse–Hedlund applies to the
  at most 4ᵗ factors of length 4ᵗ. Its Lemma 4.4 (`periodic_rows`): rows between two P-periodic
  rows are P-periodic. Infinitely many returns then make two adjacent columns periodic, against
  Jen's theorem for such configurations. Wolfram (2019) plots y_t and asks
  about the equidistribution of y_{Pk+r} [W19]. For the single seed this is open; at the level of
  digits it holds for almost every configuration (`OrbitFrequencies.ae_orbit_frequency_progression`).
- **Recurrence and uniform recurrence of c.** As properties of sequences, these are independent of
  Problem 1. A normal sequence is recurrent but not uniformly recurrent
  (`Typicality.isRecurrent_of_disjunctive`, `not_uniformlyRecurrent_of_disjunctive`, already for
  every disjunctive sequence; so for almost every configuration,
  `ae_recurrent_not_uniformlyRecurrent_trace`). Quantitatively, the prefix of length n of a random
  center column first occurs again after 2^(n(1 + o(1))) steps (the recurrence theorem of Wyner and
  Ziv, [ReturnTimes](Rule30Equivalents/ReturnTimes.lean): `ae_tendsto_logb_returnTime_trace`). A recurrent EP sequence is
  purely periodic, so "c is recurrent" would reduce Problem 1 to the T = 0 case (Section 5).
- **Kolmogorov complexity.** K(c↾n) = K(n) + O(1), as for every computable sequence, so it cannot
  see Problem 1 [LV19]. The resource-bounded measures of [5], [27], [28], [37] and [52] can.
- **Two exact formulas for the center** (proved, [CenterFormulas](Rule30Equivalents/CenterFormulas.lean);
  round-1 research claims). Over 𝔽₂:
  - *From the right half* (`toF_center_eq_sum`): for t ≥ 1 and every period K ≥ t of the diagonal
    t, for example K = 2ᵗ, c(t) = Σ_{t ≤ s < K} [cell(s, s−t+1) ∨ cell(s, s−t+2)]. The cells summed
    lie in the columns ≥ 1, so c is determined by the right half: each step down the diagonal adds
    one of them, and the diagonal is back at 0 at time K.
  - *Duhamel's formula* (`duhamel`, `center_duhamel`): rule 30 is rule 150 plus the product of the
    center and right cells, x′ = Lx + N(x) with (Lx)_p = x_{p−1} + x_p + x_{p+1} and
    N(x)_p = x_p x_{p+1}. So x(t) = Lᵗx(0) + Σ_{s<t} L^(t−1−s) N(x(s)), and for the single seed
    c(t) = 1 + Σ_{s<t} Σ_{|p| ≤ t−1−s} T(t−1−s, p)·cell(s, p)·cell(s, p+1), where T(m, ·) is rule
    150 from a single seed (trinomial coefficients mod 2; its center is 1). The nonlinear term is
    all that separates c from rule 150's constant center column.

- **The algebraic degree of the t-step map** (proved). For t ≥ 2, the center cell after t steps, as
  a Boolean function of the 2t + 1 initial cells, has algebraic normal form of degree 2t − 1, and
  for t ≥ 3 its only monomial of that degree is x_{2−t} ⋯ x_t. The formula fails at t = 1: the
  local rule l ⊕ c ⊕ r ⊕ cr has degree 2. The degrees for t = 1, …, 7 are 2, 3, 5, 7, 9, 11, 13
  (critic; recomputed here for t ≤ 6). The coefficient of x₀ is c(t), so Problem 1 is about the
  linear part. The statement concerns all seeds jointly, and rules of maximal degree with EP
  centers show that it cannot decide Problem 1 (synthesis). *Lean:* proved in
  [AlgebraicDegree](Rule30Equivalents/AlgebraicDegree.lean) (`isGreatest_card_coef_center`,
  `eq_top_of_coef_center_ne_zero`, `coef_center_singleton`). The coefficient of the monomial S is
  the Möbius transform Σ_{U ⊆ S} Φ_t(1_U) over 𝔽₂. Upper bound: rule 30 is left-permutive, so the
  leftmost variable enters linearly, and the derivative along the next one telescopes along the
  left diagonal into cells that are again linear in their leftmost variable. Lower bound: the
  coefficient of x_{2−t} ⋯ x_t is the parity of the number of configurations whose cone has a
  white right diagonal; running rule 30 sideways maps them bijectively to the words w of length
  t − 1 with f_{2t−2}(w) = 0, and the top coefficient of f_{2m} is 1 by induction on m. Also,
  Φ_t is balanced and its Walsh coefficient vanishes at every linear function that does not
  involve x_{−t} (`walsh_center_eq_zero`, `card_center_true`), since Φ_t flips with x_{−t}.
- **Rowland's Conjecture 1** (rigidity of the right edge) has no known relation to Problem 1. The
  stripe seeds [21] show that the center column does not determine the right edge.

---

## 7. Broader perspectives

1. **Hubs.** A handful of general lemmas about 0/1 sequences generate most of the catalog:
   - "rational ⟺ EP digits", for real, p-adic and function-field expansions, and for Pisot bases
     ([48]);
   - "finitely many shifts ⟺ EP", which gives regular languages, the orbit closure, the ω-limit
     and Myhill–Nerode;
   - "a finite-state deterministic system has EP output", which gives recurrences, LFSRs, NLFSRs,
     FCSRs, predictors, Büchi lassos, LZ76 and automatic complexity;
   - "EP sets are the Presburger-definable and semilinear sets";
   - "no linear relation among the shifts" ([44]), which gives the field-independent algebraic
     forms and the Hankel rank.

   Two kinds of entry need more: continued fractions need the Euler–Lagrange hub ([39], [49]), and
   the CA-structure entries are identity transfers ([6], [21], [22], [25], [26], [33]).
   Formalizing each hub once, in Mathlib form, gives most entries cheaply.
2. **A ladder of randomness criteria** [W19]. Problem 3 ⟹ no polylog digit extraction ⟹ not
   automatic ⟹ Problem 1. Normal ⟹ disjunctive ⟹ positive entropy ⟹ Problem 1, and
   normal ⟹ Problem 2 (for every bit sequence: `StrongerStatements.disjunctive_of_isNormal`,
   `not_eventuallyPeriodic_of_disjunctive`, `ProblemTwo.halfDensity_of_isNormal`). Problems 1 and
   2 are independent as properties of sequences.
3. **A ladder of logics** (critic). FO(ℕ, <): S is not definable, which is proved (Section 5).
   Presburger arithmetic, which here coincides with MSO(ℕ, <) on unary sets: non-definability is
   Problem 1 ([9], [36]). (ℕ, +, V_k): non-definability means "not k-automatic", which is stronger
   (`BuchiConverse.not_definable_iff_not_isAutomatic`, both directions of Büchi–Bruyère).
   Undecidability of Th(ℕ, +, S) is stronger still (Section 4).
4. **The digits-of-π analogy** [W19]. Problem 1 corresponds to irrationality, Problem 2 to simple
   normality (the block version to normality), and Problem 3 to the absence of BBP-type digit
   extraction. Irrationality of specific constants has been proved in several ways (critic):
   - by explicit rational approximations of arithmetic origin, such as Apéry's and Beukers'
     [Ape79], [Beu79];
   - by Mahler's method, through functional equations, which covers automatic numbers [Mah29];
   - by lacunary or Liouville-type gap arguments [Liu51];
   - by Erdős's elementary method for Σ 1/(2ⁿ − 1) [Erd48];
   - by criteria based on the subspace theorem [AB07].

   All of these need arithmetic approximations or structure (functional equations, gaps, early
   repetitions) that x₂ is not known to have.
5. **A number-theoretic barrier** (number-theory survey). Classical irrationality and transcendence
   methods need a functional equation or repetitions:
   - D-finite ⟺ EP for 0/1 sequences [vdPS96];
   - Mahler functions ⟺ automatic sequences for 0/1 coefficients [ABS23];
   - criteria based on the subspace theorem need sublinear complexity or early repetitions [AB07].

   For c, Problem 1 or the data rules out each of these. A proof must build arithmetic structure
   out of the CA dynamics.
6. **Left-permutivity and sideways evolution.** Rule 30 is affine in its left cell. Two adjacent
   columns, or one column plus the neighboring column at the times when the first is white,
   determine everything to their left, and every single column is realizable ([22]). This drives
   Jen's theorem and the realization form. Rules 90, 150 and 210 share all of this but have
   eventually constant centers (`Rule30Realization.barrier`), so a proof must use the nonlinear OR,
   the product term in l ⊕ c ⊕ r ⊕ cr.
7. **Jen's dichotomy blocks equivalences.** If A ∨ B is a theorem, proving A ⟺ B is as hard as
   proving A ∧ B. So neither another column nor the white seed can be proved equivalent to
   Problem 1 without solving both problems.
8. **A uniformity hierarchy** (CA-structure survey). LHC ⟹ NumberLike ⟹ FinConf ⟹ Problem 1
   (Section 4). At period 2 one rung is exact: CQ01 holds iff no finite configuration has center
   column 1, 0, 1, 0, … from time 0 (`Rule30PeriodTwoSideways.CQ01_iff_no_finite_alternating`). Every classical partial result (Jen; Kopra's width 2; Condrey's period 1), the black-run
   and white-run exclusions, Theorem B′ included (`Rule30FiniteBlackRuns`, `Rule30FiniteBlackRunBlocks`,
   `Rule30FiniteWhiteRuns`) and every project
   reduction are uniform over finite rows. So is the periodicity of the diagonals (item 9). A proof of Problem 1 that does not
   also prove FinConf must use something specific to the seed's orbit, and the odometer
   structure of its right edge is not such a thing.
9. **Odometer and diagonals.** In the frame of the right edge, the orbit closure of the seed is the
   2-adic odometer [CPY07] (proved: `Odometer.isClosedEmbedding_seed`, and
   `Odometer.isClosedEmbedding_ψ` for every nonzero finite configuration). The T-function Φ(x) = x ⊕ (2x ∨ 4x) makes this concrete (critic):
   - row j of the diagonal array is bit j of the Φ-orbit of 1;
   - Φ is a bijection of ℤ₂, and its cycle through 1 modulo 2^(j+1) has length dividing 2^j
     ([26]).

   c(t) reads row t of this array at time t, inside that row's first period. The left diagonals,
   which are only eventually periodic, are read inside their transients. This is why diagonal
   periodicity does not reach c.

   Read from the least significant bit, Φ is a 3-state Mealy automaton: c = (c, a),
   a = σ(b, a), b = σ(c, a), with c = Φ. It is automaton 2369 of the classification [BGK+08].
   That entry gives no isomorphism type for the group G2369, records it as self-replicating and
   not contracting, and lists the relators (a⁻¹b)², (b⁻¹c)², [a, b]², (a⁻¹c)⁴. Its proof that a
   has infinite order is the growth of rule 30: the orbit of 10^∞ is infinite because the nonzero
   prefix grows by 2 at each step. The classification does not mention rule 30.

   **G2369 is locally-finite-by-ℤ** (2026-10-17). The states are b = σΦ and a = τΦ, where σ and τ
   change only the two lowest bits, so G2369 = ⟨Φ, σ, τ⟩ with ⟨σ, τ⟩ the 8-element automorphism
   group of the depth-2 tree. By rule 30's light cone, every conjugate Φⁿ f Φ⁻ⁿ (n ≥ 0) of such an f
   is finitary. These conjugates generate a locally finite 2-group L with Φ L Φ⁻¹ ⊆ L. The normal
   closure N of ⟨σ, τ⟩ is the ascending union of the Φ⁻ᵐ L Φᵐ, and Φ has infinite order. So
   G2369 = N ⋊ ⟨Φ⟩ is an ascending HNN extension of L. It is elementary amenable, of exponential
   growth (Chou), and not finitely presented (Bieri–Strebel). This is the argument of Silva and
   Steinberg for reset automata; the automaton here is 2-definite. The Lean inputs are in
   [AutomatonGroup](Rule30Equivalents/AutomatonGroup.lean). The proof and the GAP and word-problem
   computations are in the vibe-proof repository, `research/g2369/`.

   None of this is special to the seed. For every starting value a, Φ^(2^j) is the identity
   modulo 2^(j+1) (`TFunction.orbit_two_pow_mod`). For every configuration that is white right
   of some cell, the right diagonals have period dividing 2^j
   (`Rule30FiniteDiagonals.Rd_periodic`). For every configuration that is white left of some
   cell, the left diagonals are eventually periodic with period 2^j (`Ld_periodic`). Every column
   reads its array along a line of slope one (`column_reads_periodic_rows`).
10. **Distribution mod 1 and Mahler.** Rows of rule 30 are dyadic numbers, and c(t) is the first
    binary digit of the right half of row t ([20]). Kopra [Kop23] puts rule 30 and the ×p/q automata
    in one class, the rapidly left expansive automata (number-like configurations are the nonzero
    left-finite ones, Def. 2.4). His Thm 3.5 says that such an automaton of width w has no EP
    width-w trace from a number-like configuration; rule 30 has width 2, and the theorem generalizes
    [Jen90] Prop. 3. The analogues of Dubickas (Thm 4.5) and of Pisot–Vijayaraghavan (Thm 4.7) are
    proved for rule 30 (Section 6.3). Mahler's Z-number problem and the equidistribution of
    (3/2)ⁿ mod 1 remain the open counterparts [Mah68], [FLP95]. Theorem numbers refer to the arXiv
    version of [Kop23].
11. **Generic versus special points.** For μ-almost every configuration, with μ the uniform
    Bernoulli measure, the center trace is normal. The trace map Tr₀ pushes μ forward to μ, because
    c(t) = x_{−t} ⊕ g_t(x_{−t+1}, …, x_t) and the cell x_{−t} is used by no earlier c(s). In finite
    form this is proved (`AlgebraicDegree.card_trace`): each word w(0), …, w(n) is the center trace
    of exactly 2ⁿ of the 2^(2n+1) configurations on [−n, n]; likewise each word on m cells of the
    t-th row comes from exactly 4ᵗ of the 2^(m+2t) configurations under its light cone
    (`AlgebraicDegree.card_window`, Hedlund's balance for rule 30). In measure form it is proved too
    ([RandomConfigurations](Rule30Equivalents/RandomConfigurations.lean)): Tr₀ is measure preserving
    from the fair-coin measure on {0,1}^ℤ to the one on {0,1}^ℕ (`measurePreserving_trace`; flipping
    x_{−(n+1)} preserves μ, fixes c(0..n) and flips c(n+1), so every prefix has probability
    2^−(n+1), `measure_prefix`). With Borel's normal number theorem for fair coins (`ae_isNormal`:
    along each residue class modulo m the blocks of length m are independent fair words, and the
    strong law of large numbers applies), the trace is normal for μ-almost every configuration
    (`ae_isNormal_trace`); the right half does not matter, since for every fixed right half R (all
    white, as for the seed) a fair-coin left half gives a normal trace almost surely
    (`ae_isNormal_trace_glue`), and the trace of a fair-coin configuration is independent of its
    right half x₁, x₂, … (`indepFun_trace_rightHalf`: conditioned on any event about the right half,
    the trace is still a fair-coin sequence, `measure_inter_prefix_of_flipsLeft`). So the
    configuration space is the product of the center column and the right half: x ↦ (trace, x₁ x₂ …)
    is a homeomorphism {0,1}^ℤ ≃ {0,1}^ℕ × {0,1}^ℕ carrying μ to the product of fair-coin measures
    (`traceRightHalf`, `measurePreserving_traceRightHalf`). So the trace has density 1/2, is
    disjunctive and is not eventually periodic (`ae_halfDensity_trace`, `ae_disjunctive_trace`,
    `ae_not_eventuallyPeriodic_trace`). Its discrepancy N(n) − n/2 exceeds K√n and falls below −K√n
    infinitely often for every K, so it is exactly balanced infinitely often
    ([Fluctuations](Rule30Equivalents/Fluctuations.lean): `ae_frequently_balanced_trace`, by
    Kolmogorov's zero-one law and the central limit theorem), and it stays within
    √(2n log log n) from some n on (`ae_eventually_abs_discrepancy_lt_trace`, by Lévy's maximal
    inequality and Hoeffding's along n = 2^j). Sharply, the walk W(n) = 2N(n) − n obeys Khinchin's
    law of the iterated logarithm: the limsup and liminf of W(n)/√(2n log log n) are 1 and −1
    ([IteratedLogarithm](Rule30Equivalents/IteratedLogarithm.lean), `ae_limsup_liminf_walk_trace`;
    the lower half bounds the fair binomial tail from below at moderate deviations and applies the
    second Borel–Cantelli lemma to the windows [2bᵏ, 2bᵏ⁺¹)), and its limit points form exactly
    [−1, 1] (`ae_clusterPt_walk_trace`). In the sense of category the oscillation is maximal instead:
    for a comeager set of configurations limsup W(n)/n = 1 and liminf W(n)/n = −1
    (`residual_limsup_liminf_walk_div_trace`). Large deviations of the density are exponentially
    rare at Cramér's rate: for 1/2 ≤ a < 1, (1/n) log P(N(n) ≥ an) → H(a) − log 2, H the binary
    entropy ([LargeDeviations](Rule30Equivalents/LargeDeviations.lean),
    `tendsto_log_measureReal_trace`; Chernoff's bound from above, the mode of the binomial
    distribution from below). Locally the count is Gaussian, by the theorem of de Moivre and Laplace:
if (kₙ − n/2)/√n → x, then √n P(N(n) = kₙ) → √(2/π) e^(−2x²)
([LocalLimit](Rule30Equivalents/LocalLimit.lean), `tendsto_sqrt_mul_measureReal_trace`, from
Stirling's formula), so the first 2n cells are exactly half black with probability
(1 + o(1))/√(πn) (`tendsto_sqrt_mul_measureReal_balanced_trace`). The densest windows follow the
Erdős–Rényi law: for 1/2 < α < 1 the
    windows of length L(n) = ⌊log n/(log 2 − H(α))⌋ inside the first n cells are at most a fraction
    α + o(1) black, and some of them reach it ([ErdosRenyi](Rule30Equivalents/ErdosRenyi.lean),
    `ae_tendsto_maxWindow_trace`; the longest runs are the case α = 1). Its maximum-order complexity
is 2 log₂ n (1 + o(1)) ([MaxOrderComplexity](Rule30Equivalents/MaxOrderComplexity.lean),
`ae_tendsto_maxOrderComplexity_trace`, by the birthday paradox). The configurations with an
    eventually
    periodic trace are dense, meager and null (`dense_isMeagre_null_eventuallyPeriodic_trace`). The
    same flips show that rule 30 is a mixing measure-preserving system
    ([Mixing](Rule30Equivalents/Mixing.lean)): every iterate preserves μ (`measurePreserving_evol`,
    Hedlund's theorem for rule 30); the window J of x and the window I of its t-th image are
    independent once t > max I − min J (`measure_window_inter_window`); approximating measurable
    sets by cylinders, μ(A ∩ F^{−t}B) → μ(A)μ(B) for all measurable A, B
    (`tendsto_measure_inter_preimage`), so rule 30 is mixing and ergodic (`ergodic_evol_one`,
    Mathlib's `Ergodic`; in L², the averages of g ∘ Fⁿ converge to ∫ g,
    `tendsto_birkhoffAverage_integral`), and topologically mixing (`exists_mem_evol_mem`). It is
    even mixing of all orders: cylinders at times whose gaps exceed the width of their windows are
    independent (`measure_biInter_preimage_cylinder`), so μ(F^{−t₀}A₀ ∩ ⋯ ∩ F^{−t_{n−1}}A_{n−1}) →
    μ(A₀)⋯μ(A_{n−1}) as the gaps grow (`mixing_all_orders`). For μ-almost every configuration, and
    for a comeager set of them, the orbit enters every nonempty open set at arbitrarily large times
    (`ae_frequently_mem`, `residual_frequently_mem`), and every pattern on every window [−n, n]
    appears in the rows with frequency 2^−(2n+1), a pointwise ergodic theorem for local patterns
    proved from Etemadi's strong law, since rows far apart in time are independent on a window
    ([OrbitFrequencies](Rule30Equivalents/OrbitFrequencies.lean), `ae_orbit_frequency`), and so
    along every arithmetic progression of times (`ae_orbit_frequency_progression`; at the level of
    digits, Wolfram's question on the equidistribution of y_{Pk+r} [W19] has a positive answer for
    almost every configuration); so almost every configuration is generic, the empirical measures of
    its orbit converging weakly to μ (`ae_tendsto_orbit_empirical`), and the right halves of its
    rows have every sequence as a limit point (`ae_rightHalves_frequently`; for the seed, Kopra's
    theorem gives infinitely many); rule 30 is sensitive to initial conditions, and the right front
    of a perturbation moves at speed one (`sensitive`, `evol_flip_front`); rule 30 has topological
    entropy at least log 2, since the trace is a factor map onto the full shift
    (`log_two_le_coverEntropy`, Mathlib's `coverEntropy`; the trace intertwines rule 30 with the
    shift, `RandomConfigurations.trace_evol_one`), and at most log 3 (`coverEntropy_le_log_three`):
    by left permutivity the columns N, N + 1 determine everything to their left, and in their words
    a black cell in column N + 1 is followed by the complement of its left neighbor, so each word
    extends backward in time by at most three of the four letters (`card_pairWords_le`). The
    column pairs are themselves a factor, so the entropy is exactly the growth rate of their
    words. Numerically it is log 2: over n steps (n ≤ 15) a column-0 word has at most about n²/4
    column-1 partners (6², 7², 8² for the alternating word at n = 14, 16, 18), so the column-pair
    words number about 2^n n², not 3^n. Wolfram's notes give evidence that the spacetime
    entropy is 1 bit ([NKS] note to p. 960). Proving h = log 2 is open (own computation); and for
    μ-almost every configuration every column of the space-time diagram is normal, and so is the
    right half of every row (`ae_isNormal_columns`, `ae_isNormal_rows`). More generally, cells
    whose feet i − t are pairwise distinct are independent fair coins (`measure_cells`,
    `measurePreserving_cells`): so are the cells along any path that never moves right
    (p(t + 1) ≤ p(t): columns, the left edge of the light cone; `measurePreserving_path`,
    `ae_isNormal_path`) and along every line of velocity other than 1 (`measurePreserving_line`,
    `ae_isNormal_lines`). So every almost-sure law of fair coins holds along all these lines at
    once (`ae_lines_of_ae`): normality, the law of the iterated logarithm with its limit points, the
    longest runs, the return times, the linear complexity and the Erdős–Rényi law
    ([Lines](Rule30Equivalents/Lines.lean)). Along a right diagonal they are not: the cells (t, a) and
    (t + 1, a + 1) agree with probability 1/4 (`measure_diag_eq`). Topologically the picture is reversed (critic, own reasoning from standard
    facts):
    - Tr₀ is continuous, surjective and open: by left-permutivity, the image of the cylinder fixing
      x[−n, n] is the cylinder fixing c(0..n);
    - normal sequences form a meager set [Oxt80], [Šal66], so the configurations with a normal
      trace form a meager set;
    - disjunctive sequences form a dense G_δ, so the configurations with a disjunctive trace form
      a comeager set, while those whose trace is even simply normal form a meager set.

    The single seed lies in the countable, null, meager set of finite configurations, so neither
    statement says anything about it. *Lean* ([Genericity](Rule30Equivalents/Genericity.lean)): the
    trace map is continuous, open and onto (`continuous_trace`, `isOpenMap_trace`,
    `surjective_trace`; flipping x_{−m} flips c(m) and nothing before, `exists_extend`); the
    configurations with a disjunctive trace form a comeager set (`residual_disjunctive_trace`), and
    those whose trace has density 1/2 a meager set (`isMeagre_halfDensity_trace`, so a fortiori
    those with a normal trace), which has full measure
    (`RandomConfigurations.isMeagre_and_ae_halfDensity_trace`). Rule 30 itself is onto
    (`surjective_evol_one`); every configuration has at most three preimages, which the black
    configuration attains (sharper than Hedlund's bound 4: distinct preimages differ on a pair of
    cells far right, and one of the four pairs is always impossible), configurations with the same
    image that agree right of some cell are equal, and every configuration that is white from some
    cell on (the white configuration, every finite configuration, every row of the seed pattern) has
    exactly two preimages, one white and one black from that cell on, and every configuration that
    is black from some cell on has exactly three, repeating 100 in its three phases, so the counts 2
    and 3 each occur on a dense set (`dense_two_preimages`, `dense_three_preimages`)
    ([Preimages](Rule30Equivalents/Preimages.lean): `card_le_three`, `exists_card_eq_three`,
    `eq_of_evol_one_eq_of_right`, `evol_one_eq_iff_of_eventually_white`,
    `evol_one_eq_iff_of_eventually_black`, `preimage_white`; for row t + 1 of the seed pattern the
    two preimages are row t and one that is black from the cell t + 1 on, `evol_one_eq_row_iff`);
    but two different configurations that agree left of a cell can have the same image, so rule 30
    is not positively expansive (`exists_ne_left_eq`, `not_positivelyExpansive`). Still, rule 30 is
    invertible almost everywhere and generically: an image showing 010 at the cells q, q + 1, q + 2
    forces the preimage to be black at q − 1 (`eq_true_of_window`), so the cell p of a preimage is
    determined by the image on the cells p + 1, …, q + 2 for any such q > p
    (`eq_of_evol_one_eq_on_of_window`), and a configuration that shows 010 arbitrarily far to the
    right has exactly one preimage (`eq_of_evol_one_eq_of_frequently`). Almost every configuration
    does, and so does a comeager set of them, so rule 30 is injective on a set of full measure, and
    every row of the space-time diagram of almost every configuration determines it
    (`Mixing.ae_existsUnique_preimage`, `Mixing.exists_injOn_ae`,
    `Mixing.residual_existsUnique_preimage`, `Mixing.ae_injective_iterate`). Its periodic points are
    all spatially periodic: F^k x = x forces period (4^k)!, and so does F^k x = σ^d x for 1 − k ≤ d
    ≤ k, so rule 30 has no gliders with velocity in [−1, 1) (`recurs_add_factorial`); at most 4^k
    configurations satisfy it, and F itself has exactly three fixed points, all white and the two
    phases of …0101… ([PeriodicPoints](Rule30Equivalents/PeriodicPoints.lean): `evol_add_factorial`,
    `ncard_fixedPoints_le`, `evol_one_eq_self_iff`). So rule 30 is an automorphism of μ modulo null
    sets, with a measurable, measure-preserving inverse G
    ([Invertibility](Rule30Equivalents/Invertibility.lean): `exists_measurePreserving_inverse`), and
    the center column of a random configuration, run forward with rule 30 and backward with G, is a
    two-sided sequence of independent fair coins (`measurePreserving_twoSidedTrace`): the two-sided
    Bernoulli shift is a factor of rule 30. Likewise, ergodicity of the doubling map
    (`AddCircle.ergodic_nsmul`) says nothing about one specific number. *Correction:* an earlier
    version said that the trace is normal for a comeager set of configurations; that is false.
12. **Proof theory.** Problem 1 is Π⁰₂ and its negation is Σ⁰₂, so finite computation settles
    neither. This is formal ([Computability](Rule30Equivalents/Computability.lean)): the center
    column is primitive recursive (`primrec_center`), Problem 1 says that for every T and P some t ≥
    T has c(t + P + 1) ≠ c(t) (`problem1_iff_forall_exists_defect`), and it holds iff the unbounded
    search for such a t, a partial recursive function, halts on every input (T, P)
    (`problem1_iff_firstDefect_dom`). Problem 2 is Π⁰₃ (`problem2_iff_forall_exists_forall`). The
    seed is special here as well: the center column of almost every and of a generic configuration
    is not computable (`ae_not_computable_trace`, `residual_not_computable_trace`). Independence
    from PA or ZFC is conceivable [W19]. A proof in PA would yield, by proof mining, a provably
    total bound on the defects, which is a Π⁰₁ strengthening like the defect bound of Section 4 (own
    reasoning, logic survey).
13. **Complexity profiles from cryptography.** For each finite-register model, "profile bounded ⟺
    EP" holds: LFSR linear complexity, FCSR 2-adic complexity, maximum-order and k-th order
    complexity (k ≥ 1), finite-state generation, and automatic complexity ([52]). For c, every
    profile computed so far looks random. As numeric certificates they are weaker per bit than the
    kernel's factor count: about n/2 for T + P from n bits, against about n (algebra survey).
14. **Mathlib infrastructure.**
    - Mathlib already has: Presburger definability; Myhill–Nerode; `LinearRecurrence`; AddCircle
      torsion and density; continued fractions over ordered fields; p-adic numbers and the Mahler
      basis; `PowerSeries`, `RatFunc`, `LaurentSeries` and `PowerSeries.derivative`; `omegaLimit`;
      `SymbolicDynamics`; König's lemma; `Dioph` with `Dioph.pow_dioph`; Lucas' theorem
      (`Choose.choose_modEq_prod_range_choose`) and Kummer's theorem
      (`Nat.Prime.emultiplicity_choose`); `List.HasPeriod` with the Fine–Wilf lemma
      `List.HasPeriod.gcd`; `schnirelmannDensity`; and `Module.AEval`.
    - Mathlib lacks: an eventually-periodic predicate; the digits-rationality lemma for arbitrary
      digits; Morse–Hedlund; Kronecker's, Fatou's, Szegő's, Pólya–Carlson's, Euler–Lagrange's and
      Skolem–Mahler–Lech's theorems; Christol's and Cobham's theorems; Strassmann's theorem;
      automatic sequences; Büchi automata and MSO; Parikh's theorem; the context-free pumping
      lemma; the gap theorems; normal numbers; natural density; Tauberian theorems; the pointwise
      ergodic theorem (Mathlib has Birkhoff sums and the von Neumann mean ergodic theorem); and
      cellular automata.
    - This library now proves, in general form: Morse–Hedlund, Euler–Lagrange, Strassmann,
      Skolem–Mahler–Lech over ℚ, Christol (both directions) and Cobham, Büchi–Bruyère (both
      directions), automatic and k-regular sequences, Büchi automata and the MSO composition method,
      the context-free pumping lemma, the time and space gap theorems (Hennie–Trakhtenbrot and
      Stearns–Hartmanis–Lewis), meromorphic continuation of finite-valued power series (the disk
      form of Fatou–Szegő), Szegő's theorem for 0/1 coefficients (a continuation across any arc
      of the unit circle makes the sequence eventually periodic), the Perron–Frobenius theorem
      for primitive matrices, the Hardy–Littlewood–Karamata
      and Hardy Tauberian theorems, Borel's normal number theorem for fair coins, and, for rule 30,
      Hedlund's measure preservation, mixing and ergodicity. Pólya–Carlson's theorem is still
      missing.

---

## 8. References and provenance

### 8.1 References

Wolfram, the prize and formal statements

- [W19] S. Wolfram, Announcing the Rule 30 Prizes, Stephen Wolfram Writings, October 2019,
  https://writings.stephenwolfram.com/2019/10/announcing-the-rule-30-prizes/ ; prize site
  https://www.rule30prize.org/
- [W86] S. Wolfram, Random sequence generation by cellular automata, Adv. Appl. Math. 7 (1986)
  123–169.
- [W85] S. Wolfram, Twenty problems in the theory of cellular automata, Physica Scripta T9 (1985)
  170–183.
- [W85c] S. Wolfram, Cryptography with cellular automata, CRYPTO '85, LNCS 218 (1986) 429–432.
- [Wol83] S. Wolfram, Statistical mechanics of cellular automata, Rev. Mod. Phys. 55 (1983) 601–644.
- [NKS] S. Wolfram, A New Kind of Science, Wolfram Media (2002); notes to pp. 871, 956, 960, 975,
  1087, 1149 and 1160.
- [MW] MathWorld, Rule 30, https://mathworld.wolfram.com/Rule30.html
- [FC] google-deepmind/formal-conjectures, FormalConjectures/Other/Rule30.lean, commit 7db2ea3
  (2026-10-14).
- [OEIS] A051023, A365254, A092539, A110240, A269160, A226474, A327974, A327982, A327983, A327984,
  A327985, A328102, A363343, A094605, A363345, A364239.

Number theory and Diophantine approximation

- [HW] G. H. Hardy, E. M. Wright, An Introduction to the Theory of Numbers, Oxford (1938 and later
  editions), ch. IX, X and XXIII.
- [Dic19] L. E. Dickson, History of the Theory of Numbers, vol. I (1919), ch. VI.
- [Kh64] A. Ya. Khinchin, Continued Fractions, Univ. of Chicago Press (1964).
- [Bug12] Y. Bugeaud, Distribution Modulo One and Diophantine Approximation, Cambridge Tracts in
  Math. 193, CUP (2012).
- [Gou97] F. Q. Gouvêa, p-adic Numbers: An Introduction, 2nd ed., Springer (1997).
- [Kob] N. Koblitz, p-adic Numbers, p-adic Analysis, and Zeta-Functions, GTM 58, Springer.
- [KG97] A. Klapper, M. Goresky, Feedback shift registers, 2-adic span, and combiners with memory,
  J. Cryptology 10 (1997) 111–147.
- [GK12] M. Goresky, A. Klapper, Algebraic Shift Register Sequences, CUP (2012).
- [Min04] H. Minkowski, Zur Geometrie der Zahlen, Verhandlungen des III. Internationalen
  Mathematiker-Kongresses, Heidelberg 1904, 164–173.
- [Sal43] R. Salem, On some singular monotonic functions which are strictly increasing, Trans. Amer.
  Math. Soc. 53 (1943) 427–439.
- [Den38] A. Denjoy, Sur une fonction réelle de Minkowski, J. Math. Pures Appl. 17 (1938) 105–151.
- [Gal76] J. Galambos, Representations of Real Numbers by Infinite Series, LNM 502, Springer (1976).
- [ERS58] P. Erdős, A. Rényi, P. Szüsz, On Engel's and Sylvester's series, Ann. Univ. Sci.
  Budapest. Eötvös Sect. Math. 1 (1958) 7–32.
- [Lur83] J. Lüroth, Ueber eine eindeutige Entwickelung von Zahlen in eine unendliche Reihe, Math.
  Ann. 21 (1883) 411–423.
- [Sch80] K. Schmidt, On periodic expansions of Pisot numbers and Salem numbers, Bull. London Math.
  Soc. 12 (1980) 269–278.
- [Ber77] A. Bertrand, Développements en base de Pisot et répartition modulo 1, C. R. Acad. Sci.
  Paris Sér. A 285 (1977) 419–421.
- [AB05] B. Adamczewski, Y. Bugeaud, On the complexity of algebraic numbers II. Continued
  fractions, Acta Math. 195 (2005) 1–20.
- [AB07] B. Adamczewski, Y. Bugeaud, On the complexity of algebraic numbers I. Expansions in
  integer bases, Ann. of Math. 165 (2007) 547–565.
- [Bug11] Y. Bugeaud, On the rational approximation to the Thue–Morse–Mahler numbers, Ann. Inst.
  Fourier 61 (2011) 2065–2076.
- [Bug13] Y. Bugeaud, Automatic continued fractions are transcendental or quadratic, Ann. Sci. Éc.
  Norm. Supér. (4) 46 (2013) 1005–1022.
- [BHWY16] Y. Bugeaud, G.-N. Han, Z.-Y. Wen, J.-Y. Yao, Hankel determinants, Padé approximations, and
  irrationality exponents, IMRN (2016), arXiv:1503.02797.
- [Bor09] É. Borel, Les probabilités dénombrables et leurs applications arithmétiques, Rend. Circ.
  Mat. Palermo 27 (1909) 247–271.
- [Wal49] D. D. Wall, Normal Numbers, PhD thesis, UC Berkeley (1949).
- [Erd48] P. Erdős, On arithmetical properties of Lambert series, J. Indian Math. Soc. (N.S.) 12
  (1948) 63–66.
- [Liu51] J. Liouville, Sur des classes très-étendues de quantités dont la valeur n'est ni
  algébrique, ni même réductible à des irrationnelles algébriques, J. Math. Pures Appl. 16 (1851)
  133–142.
- [Ape79] R. Apéry, Irrationalité de ζ(2) et ζ(3), Astérisque 61 (1979) 11–13.
- [Beu79] F. Beukers, A note on the irrationality of ζ(2) and ζ(3), Bull. London Math. Soc. 11 (1979)
  268–272.
- [Mah29] K. Mahler, Arithmetische Eigenschaften der Lösungen einer Klasse von
  Funktionalgleichungen, Math. Ann. 101 (1929) 342–366.
- [Mah68] K. Mahler, An unsolved problem on the powers of 3/2, J. Austral. Math. Soc. 8 (1968)
  313–321.
- [FLP95] L. Flatto, J. C. Lagarias, A. D. Pollington, On the range of fractional parts
  {ξ(p/q)ⁿ}, Acta Arith. 70 (1995) 125–147.
- [Dub08] A. Dubickas, On the powers of 3/2 and other rational numbers, Math. Nachr. 281 (2008)
  951–958.
- [Vij40] T. Vijayaraghavan, On the fractional parts of the powers of a number, J. London Math. Soc.
  15 (1940) 159–160.
- [Luc78] É. Lucas, Théorie des fonctions numériques simplement périodiques, Amer. J. Math. 1 (1878)
  184–240 and 289–321.
- [Kum52] E. E. Kummer, Über die Ergänzungssätze zu den allgemeinen Reciprocitätsgesetzen, J. reine
  angew. Math. 44 (1852) 93–146.

Algebra, power series and coding theory

- [LN97] R. Lidl, H. Niederreiter, Finite Fields, 2nd ed., Encyclopedia Math. Appl. 20, CUP (1997),
  ch. 8.
- [Mas69] J. L. Massey, Shift-register synthesis and BCH decoding, IEEE Trans. Inform. Theory 15
  (1969) 122–127.
- [Mil75] W. H. Mills, Continued fractions and linear recurrences, Math. Comp. 29 (1975) 173–180.
- [WS79] L. R. Welch, R. A. Scholtz, Continued fractions and Berlekamp's algorithm, IEEE Trans.
  Inform. Theory 25 (1979) 19–27.
- [Dor87] J.-L. Dornstetter, On the equivalence between Berlekamp's and Euclid's algorithms, IEEE
  Trans. Inform. Theory 33 (1987) 428–431.
- [Nie88] H. Niederreiter, Sequences with almost perfect linear complexity profile, EUROCRYPT '87,
  LNCS 304 (1988) 37–51.
- [Rue86] R. A. Rueppel, Analysis and Design of Stream Ciphers, Springer (1986).
- [WM86] M. Z. Wang, J. L. Massey, The characterization of all binary sequences with perfect linear
  complexity profiles, EUROCRYPT '86 abstracts (1986).
- [MeWi17] L. Mérai, A. Winterhof, On the Nth linear complexity of automatic sequences,
  arXiv:1711.10764.
- [Kro1881] L. Kronecker, Zur Theorie der Elimination einer Variabeln aus zwei algebraischen
  Gleichungen, Monatsber. Königl. Preuss. Akad. Wiss. Berlin (1881) 535–600.
- [Sal63] R. Salem, Algebraic Numbers and Fourier Analysis, Heath (1963), ch. I.
- [Gan59] F. R. Gantmacher, The Theory of Matrices, vol. II, Chelsea (1959), ch. XV.
- [vdPS96] A. J. van der Poorten, I. E. Shparlinski, On linear recurrence sequences with polynomial
  coefficients, Glasgow Math. J. 38 (1996) 147–155.
- [BC17] J. P. Bell, S. Chen, Power series with coefficients from a finite set, J. Combin. Theory
  Ser. A (2017), arXiv:1606.04986.
- [Sta80] R. P. Stanley, Differentiably finite power series, European J. Combin. 1 (1980) 175–188.
- [Com64] L. Comtet, Calcul pratique des coefficients de Taylor d'une fonction algébrique, Enseign.
  Math. 10 (1964) 267–270.
- [Fat06] P. Fatou, Séries trigonométriques et séries de Taylor, Acta Math. 30 (1906) 335–400.
- [Sze22] G. Szegő, Über Potenzreihen mit endlich vielen verschiedenen Koeffizienten, Sitzungsber.
  Preuss. Akad. Wiss. (1922) 88–91.
- [Die57] P. Dienes, The Taylor Series, Dover (1957), reprint of the Oxford edition (1931).
- [BEL08] P. Borwein, T. Erdélyi, F. Littmann, Polynomials with coefficients from a finite set,
  Trans. Amer. Math. Soc. 360 (2008) 5145–5154.
- [Car21] F. Carlson, Über Potenzreihen mit ganzzahligen Koeffizienten, Math. Z. 9 (1921) 1–13.
- [Pol16] G. Pólya, Über Potenzreihen mit ganzzahligen Koeffizienten, Math. Ann. 77 (1916) 497–513.
- [Ste30] H. Steinhaus, Über die Wahrscheinlichkeit dafür, daß der Konvergenzkreis einer Potenzreihe
  ihre natürliche Grenze ist, Math. Z. 31 (1930) 408–416.
- [PZ32] R. E. A. C. Paley, A. Zygmund, On some series of functions (3), Proc. Cambridge Philos.
  Soc. 28 (1932) 190–205.
- [Kah85] J.-P. Kahane, Some Random Series of Functions, 2nd ed., Cambridge Univ. Press (1985).
- [JB89] C. J. A. Jansen, D. E. Boekee, The shortest feedback shift register that can generate a
  given sequence, CRYPTO '89, LNCS 435 (1990) 90–99.
- [Li24] C. Li, A survey on complexity measures of pseudo-random sequences, arXiv:2405.08479 (2024).
- [AW85] R. Arratia, M. S. Waterman, An Erdős–Rényi law with shifts, Adv. Math. 55 (1985) 13–23.
- [Sko34] T. Skolem, Ein Verfahren zur Behandlung gewisser exponentialer Gleichungen und
  diophantischer Gleichungen, Comptes Rendus 8e Congrès des Mathématiciens Scandinaves, Stockholm
  (1934).
- [Mah35] K. Mahler, Eine arithmetische Eigenschaft der Taylor-Koeffizienten rationaler Funktionen,
  Proc. Akad. Wetensch. Amsterdam 38 (1935) 50–60.
- [Lec53] C. Lech, A note on recurring series, Ark. Mat. 2 (1953) 417–421.
- [Str28] R. Strassmann, Über den Wertevorrat von Potenzreihen im Gebiet der p-adischen Zahlen, J.
  Reine Angew. Math. 159 (1928) 13–28.
- [Der07] H. Derksen, A Skolem–Mahler–Lech theorem in positive characteristic and finite automata,
  Invent. Math. 168 (2007) 175–224.
- [ADH21] B. Adamczewski, T. Dreyfus, C. Hardouin, Hypertranscendence and linear difference
  equations, J. Amer. Math. Soc. 34 (2021) 475–503.
- [Jac48] C. G. J. Jacobi, Über die Differentialgleichung, welcher die Reihen 1 ± 2q + 2q⁴ ± … Genüge
  leisten, J. reine angew. Math. 36 (1848) 97–112.
- [Die12] C. Diem, On the use of expansion series for stream ciphers, LMS J. Comput. Math. 15 (2012)
  326–340.
- [MNW17] L. Mérai, H. Niederreiter, A. Winterhof, Expansion complexity and linear complexity of
  sequences over finite fields, Cryptogr. Commun. (2017), arXiv:1606.06482.
- [ABS23] B. Adamczewski, J. P. Bell, D. Smertnig, A height gap theorem for coefficients of Mahler
  functions, J. Eur. Math. Soc. 25 (2023) 2525–2571.
- [Gol67] S. W. Golomb, Shift Register Sequences, Holden-Day (1967).
- [MS97] C. Mauduit, A. Sárközy, On finite pseudorandom binary sequences I, Acta Arith. 82 (1997)
  365–377.

Combinatorics on words and dynamics

- [MH38] M. Morse, G. A. Hedlund, Symbolic dynamics, Amer. J. Math. 60 (1938) 815–866.
- [CH73] E. M. Coven, G. A. Hedlund, Sequences with minimal block growth, Math. Systems Theory 7
  (1973) 138–153.
- [CN09] J. Cassaigne, F. Nicolas, On the Morse–Hedlund complexity gap, arXiv:0903.1627.
- [CN10] J. Cassaigne, F. Nicolas, Factor complexity, in V. Berthé, M. Rigo (eds.), Combinatorics,
  Automata and Number Theory, Encyclopedia Math. Appl. 135, CUP (2010), ch. 4.
- [Cas97] J. Cassaigne, Complexité et facteurs spéciaux, Bull. Belg. Math. Soc. 4 (1997) 67–88.
- [Rau83] G. Rauzy, Suites à termes dans un alphabet fini, Sém. Théorie des Nombres de Bordeaux
  1982–1983, exp. 25.
- [Dur98] F. Durand, A characterization of substitutive sequences using return words, Discrete Math.
  179 (1998) 89–101.
- [Dur11] F. Durand, Cobham's theorem for substitutions, J. Eur. Math. Soc. 13 (2011) 1799–1814,
  arXiv:1010.4009.
- [LM95] D. Lind, B. Marcus, An Introduction to Symbolic Dynamics and Coding, CUP (1995).
- [Kur03] P. Kůrka, Topological and Symbolic Dynamics, Cours Spécialisés 11, SMF (2003).
- [Hed69] G. A. Hedlund, Endomorphisms and automorphisms of the shift dynamical system, Math. Systems
  Theory 3 (1969) 320–375.
- [MeSa17] T. Meyerovitch, V. Salo, On pointwise periodicity in tilings, cellular automata and
  subshifts, arXiv:1703.10013.
- [CFG10] J. Cervelle, E. Formenti, P. Guillon, Ultimate traces of cellular automata, STACS 2010,
  arXiv:1001.0251.
- [MRS98] F. Mignosi, A. Restivo, S. Salemi, Periodicity and the golden ratio, Theoret. Comput. Sci.
  204 (1998) 153–167.
- [Sha23] J. Shallit, Prefixes of the Fibonacci word, arXiv:2302.04640 (2023).
- [ES79] A. Ehrenfeucht, D. M. Silberger, Periodicity and unbordered segments of words, Discrete
  Math. 26 (1979) 101–109.
- [HN07] T. Harju, D. Nowotka, Periodicity and unbordered words: a proof of the extended Duval
  conjecture, J. ACM 54 (2007), arXiv:cs/0305039.
- [HN12] Š. Holub, D. Nowotka, The Ehrenfeucht–Silberger problem, J. Combin. Theory Ser. A 119
  (2012) 668–682.
- [LS62] R. C. Lyndon, M. P. Schützenberger, The equation a^M = b^N c^P in a free group, Michigan
  Math. J. 9 (1962) 289–298.
- [RSZ11] G. Richomme, K. Saari, L. Q. Zamboni, Abelian complexity of minimal subshifts, J. London
  Math. Soc. 83 (2011) 79–95.
- [BFK97] F. Blanchard, E. Formenti, P. Kůrka, Cellular automata in the Cantor, Besicovitch and Weyl
  topological spaces, Complex Systems 11 (1997) 107–123.
- [JK69] K. Jacobs, M. Keane, 0-1-sequences of Toeplitz type, Z. Wahrscheinlichkeitstheorie verw.
  Geb. 13 (1969) 123–131.
- [Oxt80] J. C. Oxtoby, Measure and Category, 2nd ed., GTM 2, Springer (1980).
- [Šal66] T. Šalát, A remark on normal numbers, Rev. Roumaine Math. Pures Appl. 11 (1966) 53–56.

Cellular automata

- [Jen86] E. Jen, Global properties of cellular automata, J. Stat. Phys. 43 (1986) 219–242.
- [Jen90] E. Jen, Aperiodicity in one-dimensional cellular automata, Physica D 45 (1990) 3–18.
- [Kop21] J. Kopra, On the trace subshifts of fractional multiplication automata, Theoret. Comput.
  Sci. 851 (2021) 92–110, arXiv:2005.05112.
- [Kop23] J. Kopra, Rapid left expansivity, a commonality between Wolfram's Rule 30 and powers of
  p/q, Theoret. Comput. Sci. 946 (2023) 113668; arXiv:2202.13809, whose title is "A natural class of
  cellular automata containing fractional multiplication automata, Rule 30, and others". Theorem
  numbers in this catalog follow the arXiv version: Def. 2.4, Thms 3.5, 4.5, 4.6 and 4.7,
  Problem 4.8.
- [Con26] D. L. Condrey, Finite configurations cannot generate a constant trace in Rule 30,
  arXiv:2609.09431 (2026, unrefereed).
- [Ner26a] Nersissian, Diagonal Periods and Newton Supports of Rules 30, 86 and 135,
  arXiv:2609.25077 (2026, unrefereed). Its abstract does not mention the 8191-state bound
  attributed to it in earlier drafts.
- [Ner26b] Nersissian, Diagonal Bases and Diagonal Periods of Elementary Cellular Automata,
  arXiv:2609.25078 (2026, unrefereed).
- [Row06] E. S. Rowland, Local nested structure in Rule 30, Complex Systems 16 (2006) 239–258.
- [Row09] E. S. Rowland, Regularity versus complexity in the binary representation of 3ⁿ,
  arXiv:0902.3257 (2009).
- [BGK+08] I. Bondarenko, R. Grigorchuk, R. Kravchenko, Ye. Muntyan, V. Nekrashevych, D. Savchuk,
  Z. Šunić, On classification of groups generated by 3-state automata over a 2-letter alphabet,
  Algebra Discrete Math. 7 (2008) no. 1, 1–163; arXiv:math/0612178 for part I.
- [CPY07] E. M. Coven, M. Pivato, R. Yassawi, Prevalence of odometers in cellular automata, Proc.
  Amer. Math. Soc. 135 (2007) 815–821.
- [MS91] W. Meier, O. Staffelbach, Analysis of pseudo random sequences generated by cellular
  automata, EUROCRYPT '91, LNCS 547 (1991) 186–199.
- [LP90] W. Li, N. Packard, The structure of the elementary cellular automata rule space, Complex
  Systems 4 (1990) 281–297.

Logic, automata and computation

- [Pre29] M. Presburger, Über die Vollständigkeit eines gewissen Systems der Arithmetik ganzer
  Zahlen, in welchem die Addition als einzige Operation hervortritt, Comptes Rendus du I Congrès
  des Mathématiciens des Pays Slaves, Warsaw (1929) 92–101.
- [GS66] S. Ginsburg, E. H. Spanier, Semigroups, Presburger formulas, and languages, Pacific J.
  Math. 16 (1966) 285–296.
- [MV96] C. Michaux, R. Villemaire, Presburger arithmetic and recognizability of sets of natural
  numbers by automata: new proofs of Cobham's and Semenov's theorems, Ann. Pure Appl. Logic 77
  (1996) 251–277.
- [Mil16] A. Milchior, Uniform definition of sets using relations and complement of Presburger
  arithmetic, arXiv:1611.03839.
- [Mar02] D. Marker, Model Theory: An Introduction, GTM 217, Springer (2002).
- [HU79] J. E. Hopcroft, J. D. Ullman, Introduction to Automata Theory, Languages, and Computation,
  Addison-Wesley (1979).
- [BPS61] Y. Bar-Hillel, M. Perles, E. Shamir, On formal properties of simple phrase structure
  grammars, Z. Phonetik Sprachwiss. Kommunikationsforsch. 14 (1961) 143–172.
- [GR62] S. Ginsburg, H. G. Rice, Two families of languages related to ALGOL, J. ACM 9 (1962)
  350–371.
- [Par66] R. J. Parikh, On context-free languages, J. ACM 13 (1966) 570–581.
- [Boo77] R. V. Book, On languages with a certain prefix property, Math. Systems Theory 10 (1977)
  229–237.
- [Smi14] T. Smith, On infinite words determined by indexed languages, MFCS 2014, arXiv:1406.3373.
- [Bue62] J. R. Büchi, On a decision method in restricted second order arithmetic, Proc. 1960 Int.
  Congr. Logic, Methodology and Philosophy of Science, Stanford Univ. Press (1962) 1–11.
- [Tho90] W. Thomas, Automata on infinite objects, Handbook of Theoretical Computer Science, vol. B
  (1990) 133–191.
- [Sem77] A. L. Semenov, Presburgerness of predicates regular in two number systems, Siberian Math. J.
  18 (1977) 289–300.
- [Sem84] A. L. Semenov, Logical theories of one-place functions on the set of natural numbers, Math.
  USSR Izvestiya 22 (1984) 587–618.
- [BHMV94] V. Bruyère, G. Hansel, C. Michaux, R. Villemaire, Logic and p-recognizable sets of
  integers, Bull. Belg. Math. Soc. 1 (1994) 191–238.
- [Cob69] A. Cobham, On the base-dependence of sets of numbers recognizable by finite automata, Math.
  Systems Theory 3 (1969) 186–192.
- [Kre18] T. J. P. Krebs, A more reasonable proof of Cobham's theorem, arXiv:1801.06704.
- [Chr79] G. Christol, Ensembles presque périodiques k-reconnaissables, Theoret. Comput. Sci. 9
  (1979) 141–145.
- [CKMR80] G. Christol, T. Kamae, M. Mendès France, G. Rauzy, Suites algébriques, automates et
  substitutions, Bull. Soc. Math. France 108 (1980) 401–419.
- [AS03] J.-P. Allouche, J. Shallit, Automatic Sequences, CUP (2003).
- [SW01] J. Shallit, M.-w. Wang, Automatic complexity of strings, J. Autom. Lang. Comb. 6 (2001)
  537–554.
- [LZ76] A. Lempel, J. Ziv, On the complexity of finite sequences, IEEE Trans. Inform. Theory 22
  (1976) 75–81.
- [FMG92] M. Feder, N. Merhav, M. Gutman, Universal prediction of individual sequences, IEEE Trans.
  Inform. Theory 38 (1992) 1258–1270.
- [SS72] C. P. Schnorr, H. Stimm, Endliche Automaten und Zufallsfolgen, Acta Informatica 1 (1972)
  345–359.
- [DLLM04] J. Dai, J. Lathrop, J. Lutz, E. Mayordomo, Finite-state dimension, Theoret. Comput. Sci.
  310 (2004) 1–33.
- [LV19] M. Li, P. Vitányi, An Introduction to Kolmogorov Complexity and Its Applications, 4th ed.,
  Springer (2019).
- [Tra64] B. A. Trakhtenbrot, Turing computations with logarithmic delay, Algebra i Logika 3 (1964)
  33–48.
- [Hen65] F. C. Hennie, One-tape, off-line Turing machine computations, Information and Control 8
  (1965) 553–578.
- [Har68] J. Hartmanis, Computational complexity of one-tape Turing machine computations, J. ACM 15
  (1968) 325–339.
- [SHL65] R. E. Stearns, J. Hartmanis, P. M. Lewis, Hierarchies of memory limited computations, IEEE
  SWCT (1965) 179–190.
- [TYL03] K. Tadaki, T. Yamakami, J. C. H. Lin, Theory of one-tape linear-time Turing machines,
  arXiv:cs/0310046.
- [Dav73] M. Davis, Hilbert's tenth problem is unsolvable, Amer. Math. Monthly 80 (1973) 233–269.
- [Aar20] S. Aaronson, The Busy Beaver Frontier, SIGACT News 51(3) (2020) 32–54.
- [KNO26] T. Karimov, J. Nieuwveld, J. Ouaknine, Rich sequences and decidability of arithmetic
  theories, arXiv:2609.20415 (17 September 2026). Its abstract treats ⟨ℕ; +, P⟩ for linear
  recurrences, special functions and the totient function.
- [LY22] J. Li, T. Yang, 3.1n − o(n) circuit lower bounds for explicit functions, STOC 2022.
- [FGHK16] M. G. Find, A. Golovnev, E. A. Hirsch, A. S. Kulikov, A better-than-3n lower bound for the
  circuit complexity of an explicit function, FOCS 2016.
- [RR97] A. A. Razborov, S. Rudich, Natural proofs, J. Comput. System Sci. 55 (1997) 24–35.

Analysis

- [HL14] G. H. Hardy, J. E. Littlewood, Tauberian theorems concerning power series and Dirichlet's
  series whose coefficients are positive, Proc. London Math. Soc. (2) 13 (1914) 174–191.
- [Kar30] J. Karamata, Über die Hardy–Littlewoodschen Umkehrungen des Abelschen Stetigkeitssatzes,
  Math. Z. 32 (1930) 319–320.

Software and project

- [Mathlib] mathlib4, commit c5ea00351c28e24afc9f0f84379aa41082b1188f (2026-05-26); file paths
  are given in each entry.
- [Project] The core-catalog modules named in each entry, in [`../lean`](../lean).

### 8.2 Provenance and checks

**Lean.**
- *Library, batch 1*: [Rule30Equivalents/](Rule30Equivalents/) (`Basic`, `BinaryIrrational`,
  `PowerSeriesF2`, `ShiftOrbit`, `Symmetry`), imported by
  [Rule30Equivalents.lean](Rule30Equivalents.lean). Axioms: [scripts/CheckAxioms.lean](scripts/CheckAxioms.lean).
- *Library, batch 2* (proved, verified and imported by the root module): `NumberTheory`, `TwoAdic`, `LinearRelations`,
  `WordsAutomata` and `TransformsSeeds` in the same folder.
- *Library, later*: `IntegerRows` ([25], [26]), `LogicAutomata` ([9], [18]) and `Realization`
  ([22], the `Real.ofDigits` form of [2]), ported from the scratch proofs on 2026-10-17.
- *Core catalog*: [`../lean`](../lean), with `SHA256SUMS` for its sources.
- *Scratch files* of the original survey, not part of this kit, at the paths below. They are
  not part of the library build. The statement files contain `sorry` on purpose, marking
  statements that are not yet proved.
  - The merge's statement files: `merge/StmtCore.lean`, `StmtReal.lean`, `StmtAlg.lean` and
    `StmtStronger.lean`. They typecheck against Mathlib c5ea00351c, the core catalog and the library,
    with `sorry` where unproved.
  - The merge's proofs: `merge/QuickProofs.lean` and `merge/OfDigitsBridge.lean`.
  - The critic's statements: `critique/Additions.lean` and `critique/Additions2.lean`.
  - The survey proofs: `logic-computation/lean/` (`PresburgerTest`, `RegularTest`, `PrefixTest`,
    `LinRecTest`), `words-dynamics/` (`CoreEquiv`, `PresburgerCheck`) and `ca-structure/lean/`
    (`SymSeeds`, `CQ01Finite`). The library and the kit's `Rule30PeriodTwoSideways` now hold all of
    these proofs.

  The critic recompiled `SymSeeds`, `LinRecTest` and `CoreEquiv`, which are axiom-clean, and found
  no `sorry` in the library.

**Checks by the critic.**
- Wolfram's formula: Mathematica gives `c[5]` = {1,1,0,1,1,1}.
- The formal-conjectures text.
- The digits of x₂, x₃ and θ, and the continued fraction of x₂ (1165 quotients from 4000 bits).
- H_1, …, H_12.
- The stripe seeds s_0, …, s_11 for t ≤ 400, and that 111 fails.
- 400 bits of `nksRow`, and the diagonals A(0, t) and A(1, t).
- That the odd H_n for n < 120 are the Berlekamp–Massey values.
- The OEIS entries A365254, A092539, A110240, A269160, A327974, A327982–A327985, A226474, A094605,
  A363343, A363345, A364239 and A328102 against their stated descriptions.
- About 50 Mathlib names, by grep.

**Checks made while writing this file** (python3 -I and core Lean, each under 60 s).
- The first 40 bits of c.
- The least periods of rows j ≤ 15 of the diagonal array (700 rows), and the cycle lengths of 1
  under Φ modulo 2^(j+1) for j ≤ 15. Both give 1, 2, 2, 4, 8, 8, 16, 32, 32, 64, 64, 64, 64, 64,
  64, 128.
- The ANF degrees 2, 3, 5, 7, 9, 11 for t = 1, …, 6.
- The Engel and Sylvester digits of x₂ and the value of y = ?⁻¹(x₂), from 3000 bits.
- That `diagArray_eq_testBit` typechecks in core Lean, with `#eval` agreeing for j, t < 10.
- Grep for the Mathlib names that this file adds (`List.HasPeriod.gcd`, `List.hasPeriod_iff_getElem?`,
  `Dioph.DiophFn`, `schnirelmannDensity`, `Nat.Prime.emultiplicity_choose`, `Module.AEval`,
  `PowerSeries.derivative`, `Real.goldenRatio`, `PadicInt.mahlerEquiv`,
  `LinearIndependent.injective`) in the pinned checkout.

**Survey data, reported but not rerun here.**
- The 10⁷-bit factor counts, runs and right-special counts.
- The 2- and 3-kernel bounds.
- The Berlekamp–Massey profile to 10⁶.
- The 2-adic, maximum-order and Lempel–Ziv profiles.
- The continued-fraction statistics.
- The Hankel determinants up to 45,000.
- The defect computation for T + P ≤ 65536.
- The 10⁹-bit facts, from [W19].

**Unverified or second-hand claims, kept with flags.**
- [Con26], [Ner26a] and [Ner26b] are unrefereed and were read through the project's literature
  notes and their abstracts.
- "Period 1 holds for number-like rows" is the CA-structure survey's own derivation.
- The contents of ctchou/AutomataTheory were not checked.
- Rule 30 as the square of 3-color rules (NKS p. 956) was not checked.
- One survey cited OEIS A327980 and A327981. This catalog uses A327984 and A327985 (positions of
  the 1s and of the 0s), whose titles were checked.
