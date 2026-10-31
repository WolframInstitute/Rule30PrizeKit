import Ruliology.CellularAutomata.Rule30Prize
import Ruliology.CellularAutomata.Rule30Problem3
import Rule30Equivalents

/-!
# Rule 30 Prize kit, version 1

The reference Lean environment for submissions to the Rule 30 Prize: Lean 4.35.0 and
Mathlib `56a005855e` (its `v4.35.0` tag), pinned by `lean-toolchain` and `lake-manifest.json`.

* **The statements.** `Ruliology.CellularAutomata.Rule30Prize.Problem1` and `Problem2`, in
  `lean/Ruliology/CellularAutomata/Rule30Prize.lean`, with the rule-30 pattern `cell` from
  `Rule30Jen.lean`. They match `Rule30.centerColumn_not_eventually_periodic` and
  `Rule30.centerColumn_frequency_half` in google-deepmind/formal-conjectures. Problem 3 needs a model
  of computation: `Ruliology.CellularAutomata.Rule30Problem3` states it on a one-tape Turing machine,
  as `Problem3` (the prize's formal statement), `Problem3Verbal` and `Problem3Robust`, the version
  that does not depend on the model.
* **Equivalent forms.** `Rule30Equivalents` proves 120 theorems `problem1_iff_*`, for example
  `Rule30Equivalents.BinaryIrrational.problem1_iff_irrational_binary`: Problem 1 holds iff the binary
  number `0.c(0)c(1)c(2)…` is irrational. A proof of any of these right-hand sides proves Problem 1.
* **Partial results.** `import Ruliology` brings the whole catalog, 172 modules (periods 1 to 4,
  black runs, Jen's theorem, barriers, finite configurations). This root does not import it, because the catalog's
  certificate modules are slow to build; import the modules you need.

A submission is the single module `Rule30Submission` (file `Rule30Submission.lean`). Its headline
theorem sits in `namespace Rule30Submission` with an official name and type, listed in `Check.lean`,
for example `theorem problem1 : Ruliology.CellularAutomata.Rule30Prize.Problem1`.
-/
