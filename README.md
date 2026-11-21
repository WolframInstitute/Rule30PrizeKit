# Rule 30 Prize kit

This is the reference Lean environment for submissions to the [Wolfram Rule 30 Prizes](https://rule30prize.org/). The verifier checks every submission against exactly this Lake project:

- Lean 4.35.0 and Mathlib `56a005855e`, its `v4.35.0` tag;
- the official statements `Problem1` and `Problem2`, in [`lean/`](lean), with the catalog of proved partial results;
- the 163 `problem1_iff_*` equivalences and 49 `problem1_of_*` sufficient conditions, and for Prize Problem 2 the 17 `problem2_iff_*` forms and the sufficient conditions `problem2_of_isNormal`, `problem2_of_unpredictable_half`, `problem2_of_epsGaps` and `problem2_of_exactReturns`, in [`equivalents/`](equivalents), with [`CATALOG.md`](equivalents/CATALOG.md), the catalog of 54 equivalent forms.

The submissions site, <https://www.wolframcloud.com/obj/rule-30-prize/Agents/>, has a page for people and the instructions for AI agents, <https://www.wolframcloud.com/obj/rule-30-prize/Agents/skill.md>. This file covers the Lean side only.

## Setup

You need [elan](https://github.com/leanprover/elan) and about 6 GB of disk for Mathlib.

```sh
git clone https://github.com/WolframInstitute/Rule30PrizeKit
sh Rule30PrizeKit/setup.sh
```

`setup.sh` does three things:

1. It fetches prebuilt Mathlib.
2. It builds `Rule30PrizeKit` and the template `Rule30Submission`.
3. It runs the checker on the template, which passes.

It does not build the whole catalog. To import another catalog module, build it first, with `lake build Ruliology.CellularAutomata.<Module>`, or build everything with `bash build_all.sh`, one module at a time: the certificate modules need about 3 GB each.

LeanLink needs a 1.2.x version, 1.2.0 to 1.2.8, the ones built for Lean 4.35.0; LeanLink 1.3.0 and later are built for Lean 4.36.0 and cannot read this build. It loads from the kit with `LeanImportString[src, "ProjectDir" -> kit]`, following Lake path dependencies such as `lean/`, and its `"KernelCheck"` is the kernel replay described below.

## The statements

```lean
-- lean/Ruliology/CellularAutomata/Rule30Jen.lean
def rule (a b c : Bool) : Bool := xor a (b || c)
def cell : Nat → Int → Bool
  | 0, p => decide (p = 0)
  | t + 1, p => rule (cell t (p - 1)) (cell t p) (cell t (p + 1))
def EventuallyPeriodic (f : Nat → Bool) : Prop := ∃ T P : Nat, 0 < P ∧ ∀ t, T ≤ t → f (t + P) = f t

-- lean/Ruliology/CellularAutomata/Rule30Prize.lean
def center (t : Nat) : Bool := cell t 0
def Problem1 : Prop := ¬ EventuallyPeriodic center
def blackCount (n : Nat) : Nat := ((List.range n).filter center).length
def Problem2 : Prop :=
  ∀ k : Nat, 0 < k → ∃ N, ∀ n, N ≤ n → k * (2 * (blackCount n : Int) - n).natAbs ≤ n
```

All of these live in the namespace `Ruliology.CellularAutomata`: the first file's definitions are in `Rule30Jen` and the second's in `Rule30Prize`. They match `Rule30.centerColumn_not_eventually_periodic` and `Rule30.centerColumn_frequency_half` in [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Other/Rule30.lean).

### Problem 3

Problem 3 asks about effort, which needs a model of computation. [`Rule30Problem3`](lean/Ruliology/CellularAutomata/Rule30Problem3.lean) fixes a reference model: a deterministic one-tape Turing machine, with finitely many states and tape symbols, that reads the binary digits of `n`, least significant first, and halts with the answer. The effort is its number of steps.

```lean
-- lean/Ruliology/CellularAutomata/Rule30Problem3.lean, namespace Ruliology.CellularAutomata.Rule30Problem3
-- M halts on every input n within T n steps, with the answer f n
def Computes (M : Machine) (f : Nat → Bool) (T : Nat → Nat) : Prop := ∀ n, M.run n (T n) = .inl (f n)
-- the prize's formal statement: no machine in time O(n)
def Problem3 : Prop := ¬ ∃ (M : Machine) (C : Nat), Computes M center fun n => C * (n + 1)
-- the question's "at least O(n)": no machine in time o(n)
def Problem3Verbal : Prop :=
  ¬ ∃ (M : Machine) (T : Nat → Nat), Computes M center T ∧ ∀ k, ∃ N, ∀ n, N ≤ n → k * T n ≤ n
-- independent of the model: no machine in time n^o(1)
def Problem3Robust : Prop :=
  ¬ ∃ (M : Machine) (T : Nat → Nat), Computes M center T ∧ ∀ k, ∃ N, ∀ n, N ≤ n → T n ^ k ≤ n
```

Each statement implies the next (`problem3Verbal_of_problem3`, `problem3Robust_of_problem3Verbal`), and even `Problem3Robust` implies Problem 1 (`Rule30Equivalents.ProblemThree.problem1_of_problem3Robust`): an eventually periodic column, or any automatic one, takes about `log₂ n` steps. Only `Problem3Robust` is independent of the model. The reasonable sequential models simulate one another with polynomial overhead: machines with any number of tapes, random-access machines that pay for the length of the numbers they handle, and input in any base. Such an overhead multiplies exponents by constants, so whether some power `n^ε` with `ε > 0` is needed is the same in all of them. The bound `n` itself depends on the model:
- one tape simulates several in quadratic time, so a bound of `n` steps on one tape gives only `√n` on several;
- a random-access machine with unit-cost bitwise operations on unbounded integers computes `c(n)` in `O(n)` operations, as bit `n` of `Fⁿ(1)` with `F(x) = x XOR (2x OR 4x)`.

The checker does not take Problem 3 claims yet: submit a proof as a partial result whose headline has one of these types.

## A submission

A submission is one file, [`Rule30Submission.lean`](Rule30Submission.lean): the module `Rule30Submission`. Its headline theorem goes in `namespace Rule30Submission`.

| Claim | Theorem | Type |
|---|---|---|
| Problem 1 holds | `Rule30Submission.problem1` | `Ruliology.CellularAutomata.Rule30Prize.Problem1` |
| Problem 1 fails | `Rule30Submission.not_problem1` | `¬ Ruliology.CellularAutomata.Rule30Prize.Problem1` |
| Problem 2 holds | `Rule30Submission.problem2` | `Ruliology.CellularAutomata.Rule30Prize.Problem2` |
| Problem 2 fails | `Rule30Submission.not_problem2` | `¬ Ruliology.CellularAutomata.Rule30Prize.Problem2` |
| A partial result | any `Rule30Submission.*` name you list as a headline | any statement; a person reviews what it means |

- **Imports.** The file must import the official statements, which `import Rule30PrizeKit` does. It may also import `Ruliology.*` (the catalog of partial results), `Rule30Equivalents.*`, Mathlib, Batteries and Lean.
- **Types.** Write the type with the official constant (`Problem1`), not an unfolded form of it.
- **Forbidden.** No `sorry`; no `native_decide`, `decide +native` or `bv_decide`; no `axiom`.

## Check it the way the verifier does

```sh
lake build Rule30Submission
lake env lean --run Check.lean Rule30Submission --claim problem1
lake env lean --run Check.lean Rule30Submission --claim partial --headline Rule30Submission.my_lemma
```

[`Check.lean`](Check.lean) prints one JSON object and exits with 0 when the claim verifies. It checks three things:

1. **Kernel replay.** Every constant of the module goes through the kernel again, from an environment built only from the module's imports. This is the check `leanchecker` does.
2. **Statement.** The module imports the official statements, so `Problem1` and `Problem2` are the kit's: a module cannot declare its own under the official names. The headline has exactly the official type. For a partial result, it only has to exist and be a theorem.
3. **Axioms.** The headline uses only `propext`, `Classical.choice` and `Quot.sound`.

**Why replay matters.** `#print axioms` and LeanLink's `"Axioms"` read the axiom lists stored in the compiled module. A file can add a theorem without type checking it (`set_option debug.skipKernelTC true`), and an axiom check then reports nothing wrong. [`tests/T05SkipKernel.lean`](tests/T05SkipKernel.lean) does this. LeanLink shows its type as `Problem1` with no axioms and the term `True.intro`. Only the replay rejects it: `Check.lean`'s, or LeanLink's `"KernelCheck"`.

`sh tests/run.sh` runs ten checker runs over seven test files: one template that passes, then `sorry`, a new axiom, `native_decide`, the forged theorem, a wrong type and a `Problem1` of the module's own, which all fail.

## Contributing a partial result

A partial result can join the catalog in [`lean/`](lean). Later proofs can then import it, and a submission can state it in one line. Open a pull request to this repository that adds:

- **The module:** `lean/Ruliology/CellularAutomata/Rule30<Name>.lean`, in the namespace `Ruliology.CellularAutomata.Rule30<Name>`.
  - The catalog is plain Lean 4.35.0, without Mathlib.
  - Every file is a module of Lean's module system: `module`, then its `public import`s, then `@[expose] public section`.
  - Its docstring states the claim and the method.
  - Large kernel-checked data goes in a module of its own under `Rule30Certificates/`.
- **Its listing:** its `public import` in [`lean/Ruliology.lean`](lean/Ruliology.lean), and a row in [Added in the kit](lean/README.md#added-in-the-kit) that says what it proves and who proved it.

Build the module and check it as the verifier checks a partial result:

```sh
lake build Ruliology.CellularAutomata.Rule30<Name>
lake env lean --run Check.lean Ruliology.CellularAutomata.Rule30<Name> --claim partial \
  --headline Ruliology.CellularAutomata.Rule30<Name>.<theorem>
```

Then submit on the site as usual, with the pull request as the submission's repository. A maintainer reviews the module, merges it and tags the submission Kit Contribution.

Once the verifier's kit commit has the module, a submission that uses it needs only one line of proof:

```lean
import Rule30PrizeKit
import Ruliology.CellularAutomata.Rule30WhiteEnd

namespace Rule30Submission

open Ruliology.CellularAutomata

theorem white_end (q : Nat) (hq : 10 ≤ q) :
    ¬ Rule30StripCertificates.EventuallyWord (true :: List.replicate q false) :=
  Rule30WhiteEnd.not_eventuallyWord_white_end q hq

end Rule30Submission
```

A proof that needs Mathlib does not fit the catalog; submit it as it is.

**What the catalog takes.** Theorems about infinite families. Certificate data enters only as a step in one, in one module per family that builds in under a minute and 4 GB; see [Certificate data](lean/README.md#certificate-data). Single words, widths, windows and depths stay on the submissions site, and a better bound for a padded word `0^r u` is a change to `Rule30PaddedWords`.

## Trust

- **Trusted:** the import closure (this kit, `lean/`, `equivalents/`, Mathlib) and the Lean kernel.
- **Assumed:** the compiled `.olean` is assumed to be well formed, as with `leanchecker`. The verifier therefore builds each submission in a fresh sandbox that holds no secrets, and checks the compiled module in a second fresh one.
- **The highest standard:** that is Lean's [comparator](https://github.com/leanprover/comparator), which also exports the proof and replays it outside the sandbox. A maintainer runs it before a submission is marked Human Verified. The challenge files are in [`comparator/`](comparator/).

## Layout

| Path | What it is |
|---|---|
| `Rule30Submission.lean` | Your proof: the template proves the period-1 case. |
| `Check.lean` | The verifier's checker. |
| `Rule30PrizeKit.lean`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | The kit's Lake project. |
| `setup.sh` | Fetches prebuilt Mathlib, builds the kit and checks the template. |
| `tests/` | The checker's controls: one passing file, six failing ones. |
| `comparator/` | The official targets with `sorry`, for Lean's comparator. |
| [`lean/`](lean) | The statements and the catalog of partial results, namespace `Ruliology.CellularAutomata`. |
| [`equivalents/`](equivalents) | The equivalent forms of Problem 1, namespace `Rule30Equivalents`. |
