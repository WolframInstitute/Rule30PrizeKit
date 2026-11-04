module

public import Ruliology.CellularAutomata.Rule30BlackRuns

/-!
# Rule 30: a long black run followed by a specific block (Theorem B′)

A sharper, block-specific form of Theorem B (`Rule30BlackRuns.no_long_black_run`). Suppose the
center column `c` is periodic from some time on, and its repeating word is `1^r u`: a black run
of length `r` followed by a block `u`. By Lemma A* (`Rule30BlackRuns.black_shield`), at the end
of each black run columns `1, …, 2 j0` read `(white black)^j0` as soon as `r ≥ 9 j0`. The finite
check `Determined u j0` says that every row of `u.length + 10` cells that starts with this
pattern produces the same column-1 trace under the driver `u` followed by nine black cells.
Then column `1` is eventually periodic, which Jen's theorem forbids.

* `no_black_run_block` (**Theorem B′**): if `Determined u j0` holds, the center column is not
  eventually periodic with repeating word `1^r u` for any `r ≥ max 9 (9 j0)`, whatever the
  transient.
* `det_0`, `det_00`, `det_000`, `det_0000`, `det_0100` (`j0 = 2`) and `det_010`, `det_0010`,
  `det_0110` (`j0 = 3`): kernel-checked instances. So `1^r u` is excluded for
  `u = 0, 00, 000, 0000, 0100` and `r ≥ 18`, and for `u = 010, 0010, 0110` and `r ≥ 27`.
* `no_period_black_run_then_white`: the instance `1^r 0`, `r ≥ 18`, spelled out.

The blocks and their `j0` were found by a SAT search and are checked here by the kernel.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30BlackRunBlocks

open Rule30Jen Rule30Prize Rule30BlackRuns

/-! ### Theorem B′: a black run followed by a specific block

For a specific block `u` following the black run, a finite check (`Determined u j0`) replaces
the crude cone bound of Theorem B: if every row whose first `2 j0` cells read `(white black)^j0`
produces the same column-1 trace under the driver `u` followed by nine black cells, then a black
run of length `r ≥ max 9 (9 j0)` before `u` forces column 1 to be periodic. -/

/-- Column-1 trace of a finite row under a driver list: values at times `0 … ds.length`. -/
def traceCol1 : List Bool → List Bool → List Bool
  | [], row => [row.headD false]
  | c :: cs, row => row.headD false :: traceCol1 cs (stepRow c row)

/-- Column 1 at times `e, e + 1, …, e + n`. -/
def colTrace (e : Nat) : Nat → List Bool
  | 0 => [cell e 1]
  | n + 1 => cell e 1 :: colTrace (e + 1) n

theorem colTrace_getD : ∀ (n e s : Nat), s ≤ n → (colTrace e n).getD s false = cell (e + s) 1
  | 0, e, s, h => by
    have : s = 0 := by omega
    subst this; rfl
  | n + 1, e, 0, _ => rfl
  | n + 1, e, s + 1, h => by
    show (colTrace (e + 1) n).getD s false = cell (e + (s + 1)) 1
    rw [colTrace_getD n (e + 1) s (by omega), show e + 1 + s = e + (s + 1) by omega]

theorem traceCol1_rowAt : ∀ (ds : List Bool) (e : Nat),
    (∀ i, i < ds.length → cell (e + i) 0 = ds.getD i false) →
    traceCol1 ds (rowAt e 1 (ds.length + 1)) = colTrace e ds.length
  | [], e, _ => rfl
  | c :: cs, e, h => by
    have h0 : cell e 0 = c := by simpa using h 0 (by simp)
    have hstep : stepRow c (rowAt e 1 (cs.length + 1 + 1)) = rowAt (e + 1) 1 (cs.length + 1) := by
      have := stepRow_rowAt e (cs.length + 1) 1
      rw [show (1 : Int) - 1 = 0 by rfl, h0] at this
      exact this
    have ih := traceCol1_rowAt cs (e + 1) (fun i hi => by
      have := h (i + 1) (by simp; omega)
      rw [show e + (i + 1) = e + 1 + i by omega] at this
      simpa using this)
    show cell e 1 :: traceCol1 cs (stepRow c (rowAt e 1 (cs.length + 1 + 1))) =
      cell e 1 :: colTrace (e + 1) cs.length
    rw [hstep, ih]

/-- `(white black)^j`. -/
def wbPattern : Nat → List Bool
  | 0 => []
  | j + 1 => false :: true :: wbPattern j

theorem length_wbPattern : ∀ j, (wbPattern j).length = 2 * j
  | 0 => rfl
  | j + 1 => by simp [wbPattern, length_wbPattern j]; omega

/-- The driver after the black run: the block `u`, then nine black cells. -/
def drv (u : List Bool) : List Bool := u ++ List.replicate 9 true

theorem getD_replicate_black : ∀ i, i < 9 → (List.replicate 9 true).getD i false = true := by
  decide

theorem getD_drv_black : ∀ (u : List Bool) (i : Nat), u.length ≤ i → i < u.length + 9 →
    (drv u).getD i false = true
  | [], i, _, h => getD_replicate_black i (by simpa using h)
  | a :: u, i, h1, h2 => by
    cases i with
    | zero => simp at h1
    | succ i =>
      show (drv u).getD i false = true
      exact getD_drv_black u i (by simp at h1; omega) (by simp at h2; omega)

/-- The finite check: all rows with prefix `(white black)^j0` give the same column-1 trace. -/
def Determined (u : List Bool) (j0 : Nat) : Bool :=
  (allLists (u.length + 10 - 2 * j0)).all fun tail =>
    traceCol1 (drv u) (wbPattern j0 ++ tail) ==
      traceCol1 (drv u) (wbPattern j0 ++ List.replicate (u.length + 10 - 2 * j0) false)

theorem rowAt_split (t : Nat) :
    ∀ (a b : Nat) (p : Int), rowAt t p (a + b) = rowAt t p a ++ rowAt t (p + a) b
  | 0, b, p => by simp [rowAt]
  | a + 1, b, p => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    show cell t p :: rowAt t (p + 1) (a + b) =
      cell t p :: rowAt t (p + 1) a ++ rowAt t (p + ((a + 1 : Nat) : Int)) b
    rw [rowAt_split t a b (p + 1), show p + 1 + (a : Int) = p + ((a + 1 : Nat) : Int) by omega]
    rfl

theorem rowAt_wb (t : Nat) (p : Int) : ∀ j : Nat, (∀ i : Nat, 1 ≤ i → i ≤ j →
    cell t (p + 2 * (i : Int) - 2) = false ∧ cell t (p + 2 * (i : Int) - 1) = true) →
    rowAt t p (2 * j) = wbPattern j
  | 0, _ => rfl
  | j + 1, h => by
    have h1 := h 1 (by omega) (by omega)
    rw [show p + 2 * ((1 : Nat) : Int) - 2 = p by omega,
      show p + 2 * ((1 : Nat) : Int) - 1 = p + 1 by omega] at h1
    have ih := rowAt_wb t (p + 2) j (fun i hi1 hij => by
      have := h (i + 1) (by omega) (by omega)
      rw [show p + 2 * ((i + 1 : Nat) : Int) - 2 = p + 2 + 2 * (i : Int) - 2 by omega,
        show p + 2 * ((i + 1 : Nat) : Int) - 1 = p + 2 + 2 * (i : Int) - 1 by omega] at this
      exact this)
    show cell t p :: cell t (p + 1) :: rowAt t (p + 1 + 1) (2 * j) = false :: true :: wbPattern j
    rw [h1.1, h1.2, show p + 1 + 1 = p + 2 by omega, ih]

/-- **Theorem B′.** A black run of length `r ≥ max 9 (9 j0)` followed by a block `u` with
`Determined u j0` cannot be the repeating word of an eventually periodic center column. -/
theorem no_black_run_block (u : List Bool) (j0 : Nat) (hdet : Determined u j0 = true)
    (hj0 : 2 * j0 ≤ u.length + 10)
    (T r t1 : Nat) (hper : ∀ t, T ≤ t → center (t + (r + u.length)) = center t)
    (ht1 : T ≤ t1) (hr9 : 9 ≤ r) (hrj : 9 * j0 ≤ r)
    (hrun : ∀ s, s < r → center (t1 + s) = true)
    (hu : ∀ i, i < u.length → center (t1 + r + i) = u.getD i false) : False := by
  generalize hPdef : r + u.length = P at hper
  have hP : 0 < P := by omega
  have hperk : ∀ k t, T ≤ t → center (t + k * P) = center t := periodic_mul hper
  have hblack : ∀ k s, s < r → cell (t1 + k * P + s) 0 = true := by
    intro k s hs
    have := hperk k (t1 + s) (by omega)
    show center (t1 + k * P + s) = true
    rw [show t1 + k * P + s = t1 + s + k * P by omega, this]
    exact hrun s hs
  have hublock : ∀ k i, i < u.length → cell (t1 + r + k * P + i) 0 = u.getD i false := by
    intro k i hi
    have := hperk k (t1 + r + i) (by omega)
    show center (t1 + r + k * P + i) = _
    rw [show t1 + r + k * P + i = t1 + r + i + k * P by omega, this]
    exact hu i hi
  -- the drivers from e_k = t1 + r + k P: u, then nine black cells
  have hdrv : ∀ k i, i < (drv u).length → cell (t1 + r + k * P + i) 0 = (drv u).getD i false := by
    intro k i hi
    simp only [drv, List.length_append, List.length_replicate] at hi
    by_cases hiu : i < u.length
    · rw [hublock k i hiu]; simp [drv, List.getD_eq_getElem?_getD, List.getElem?_append_left hiu]
    · have hPk : (k + 1) * P = k * P + P := Nat.succ_mul k P
      have := hblack (k + 1) (i - u.length) (by omega)
      rw [hPk, show t1 + (k * P + P) + (i - u.length) = t1 + r + k * P + i by omega] at this
      rw [this, getD_drv_black u i (by omega) (by omega)]
  -- the row at e_k: (white black)^j0, then some tail
  have hrow : ∀ k, rowAt (t1 + r + k * P) 1 (2 * j0) = wbPattern j0 := by
    intro k
    apply rowAt_wb
    intro i hi1 hij
    have := black_shield 0 j0 (t1 + k * P + (r - 9 * j0)) (fun s hs => by
        have := hblack k (r - 9 * j0 + s) (by omega)
        rwa [show t1 + k * P + (r - 9 * j0 + s) = t1 + k * P + (r - 9 * j0) + s by omega] at this)
      i hi1 hij
    rw [show t1 + k * P + (r - 9 * j0) + 9 * j0 = t1 + r + k * P by omega] at this
    rw [show (1 : Int) + 2 * (i : Int) - 2 = 0 + 2 * (i : Int) - 1 by omega,
      show (1 : Int) + 2 * (i : Int) - 1 = 0 + 2 * (i : Int) by omega]
    exact this
  -- the column-1 trace from e_k does not depend on k
  have htrace : ∀ k, colTrace (t1 + r + k * P) (drv u).length =
      traceCol1 (drv u) (wbPattern j0 ++ List.replicate (u.length + 10 - 2 * j0) false) := by
    intro k
    rw [← traceCol1_rowAt (drv u) (t1 + r + k * P) (hdrv k)]
    have hlen : (drv u).length + 1 = 2 * j0 + (u.length + 10 - 2 * j0) := by
      simp [drv]; omega
    rw [hlen, rowAt_split, hrow k]
    have hmem : rowAt (t1 + r + k * P) (1 + ((2 * j0 : Nat) : Int)) (u.length + 10 - 2 * j0) ∈
        allLists (u.length + 10 - 2 * j0) := by
      have := mem_allLists
        (rowAt (t1 + r + k * P) (1 + ((2 * j0 : Nat) : Int)) (u.length + 10 - 2 * j0))
      rwa [length_rowAt] at this
    have := List.all_eq_true.mp hdet _ hmem
    simpa using this
  have hcol : ∀ k s, s < P → cell (t1 + r + s) 1 = cell (t1 + r + k * P + s) 1 := by
    intro k s hs
    by_cases hs1 : s < (drv u).length + 1
    · have a := congrArg (fun l => l.getD s false) (htrace 0)
      have b := congrArg (fun l => l.getD s false) (htrace k)
      simp only [Nat.zero_mul, Nat.add_zero] at a b
      rw [colTrace_getD _ _ _ (by omega)] at a b
      rw [a, b]
    · simp only [drv, List.length_append, List.length_replicate] at hs1
      have white1 : ∀ t', (∀ s', s' < 9 → cell (t' + s') 0 = true) → cell (t' + 9) 1 = false := by
        intro t' h
        have := (nine_black t' 0 h).1
        simpa using this
      have hPk : ∀ k', (k' + 1) * P = k' * P + P := fun k' => Nat.succ_mul k' P
      have wk : ∀ k', cell (t1 + r + k' * P + s) 1 = false := by
        intro k'
        have := white1 (t1 + r + k' * P + s - 9) (fun s' hs' => by
          have := hblack (k' + 1) (s - 9 + s' - u.length) (by omega)
          rwa [hPk, show t1 + (k' * P + P) + (s - 9 + s' - u.length) =
            t1 + r + k' * P + s - 9 + s' by omega] at this)
        rwa [show t1 + r + k' * P + s - 9 + 9 = t1 + r + k' * P + s by omega] at this
      have w0 := wk 0
      simp only [Nat.zero_mul, Nat.add_zero] at w0
      rw [w0, wk k]
  have h1 : EventuallyPeriodic (fun t => cell t (0 + 1)) := by
    refine ⟨t1 + r, P, hP, fun t ht => ?_⟩
    show cell (t + P) (0 + 1) = cell t (0 + 1)
    rw [show (0 : Int) + 1 = 1 by rfl]
    have hdm := Nat.div_add_mod (t - (t1 + r)) P
    generalize (t - (t1 + r)) / P = q at hdm
    have hmod := Nat.mod_lt (t - (t1 + r)) hP
    generalize (t - (t1 + r)) % P = s at hdm hmod
    have hq1 : (q + 1) * P = q * P + P := Nat.succ_mul q P
    have e1 := hcol q s hmod
    have e2 := hcol (q + 1) s hmod
    rw [hq1] at e2
    have hcomm : P * q = q * P := Nat.mul_comm P q
    rw [show t + P = t1 + r + (q * P + P) + s by omega, ← e2, e1,
      show t1 + r + q * P + s = t by omega]
  have h0 : EventuallyPeriodic (fun t => cell t 0) := ⟨T, P, hP, hper⟩
  exact not_adjacent 0 h0 h1

/-- The block `0` with `j0 = 2`: `1^r 0` is excluded for every `r ≥ 18`. -/
theorem det_0 : Determined [false] 2 = true := by decide +kernel

/-- Blocks of length `2 … 4` that start and end white, with their `j0` (kernel-checked).
Theorem B′ then excludes `1^r u` for every `r ≥ max 9 (9 j0)`. -/
theorem det_00 : Determined [false, false] 2 = true := by decide +kernel
theorem det_000 : Determined [false, false, false] 2 = true := by decide +kernel
theorem det_010 : Determined [false, true, false] 3 = true := by decide +kernel
theorem det_0000 : Determined [false, false, false, false] 2 = true := by decide +kernel
theorem det_0010 : Determined [false, false, true, false] 3 = true := by decide +kernel
theorem det_0100 : Determined [false, true, false, false] 2 = true := by decide +kernel
theorem det_0110 : Determined [false, true, true, false] 3 = true := by decide +kernel

/-- The center column is never eventually periodic with repeating word `1^r 0`, `r ≥ 18`,
whatever the transient. -/
theorem no_period_black_run_then_white (T r t1 : Nat) (hr : 18 ≤ r)
    (hper : ∀ t, T ≤ t → center (t + (r + 1)) = center t) (ht1 : T ≤ t1)
    (hrun : ∀ s, s < r → center (t1 + s) = true) (hw : center (t1 + r) = false) : False :=
  no_black_run_block [false] 2 det_0 (by decide) T r t1 hper ht1 (by omega) (by omega) hrun
    (fun i hi => by
      have : i = 0 := by simp at hi; omega
      subst this; simpa using hw)

/-! ### Complete Center-Column Exclusions for All Certified Blocks and All White-Bounded Blocks of Length `≤ 4` -/

/-- The center column is never eventually periodic with repeating word `1^r 00`, `r ≥ 18`. -/
theorem no_period_black_run_then_00 (T r t1 : Nat) (hr : 18 ≤ r)
    (hper : ∀ t, T ≤ t → center (t + (r + 2)) = center t) (ht1 : T ≤ t1)
    (hrun : ∀ s, s < r → center (t1 + s) = true)
    (hw0 : center (t1 + r) = false) (hw1 : center (t1 + r + 1) = false) : False :=
  no_black_run_block [false, false] 2 det_00 (by decide) T r t1 hper ht1 (by omega) (by omega) hrun
    (fun i hi => by
      have hi2 : i = 0 ∨ i = 1 := by simp at hi; omega
      rcases hi2 with rfl | rfl
      · simpa using hw0
      · simpa using hw1)

/-- The center column is never eventually periodic with repeating word `1^r 000`, `r ≥ 18`. -/
theorem no_period_black_run_then_000 (T r t1 : Nat) (hr : 18 ≤ r)
    (hper : ∀ t, T ≤ t → center (t + (r + 3)) = center t) (ht1 : T ≤ t1)
    (hrun : ∀ s, s < r → center (t1 + s) = true)
    (hw0 : center (t1 + r) = false) (hw1 : center (t1 + r + 1) = false)
    (hw2 : center (t1 + r + 2) = false) : False :=
  no_black_run_block [false, false, false] 2 det_000 (by decide) T r t1 hper ht1 (by omega) (by omega) hrun
    (fun i hi => by
      have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by simp at hi; omega
      rcases hi3 with rfl | rfl | rfl
      · simpa using hw0
      · simpa using hw1
      · simpa using hw2)

/-- The center column is never eventually periodic with repeating word `1^r 010`, `r ≥ 27`. -/
theorem no_period_black_run_then_010 (T r t1 : Nat) (hr : 27 ≤ r)
    (hper : ∀ t, T ≤ t → center (t + (r + 3)) = center t) (ht1 : T ≤ t1)
    (hrun : ∀ s, s < r → center (t1 + s) = true)
    (hw0 : center (t1 + r) = false) (hb1 : center (t1 + r + 1) = true)
    (hw2 : center (t1 + r + 2) = false) : False :=
  no_black_run_block [false, true, false] 3 det_010 (by decide) T r t1 hper ht1 (by omega) (by omega) hrun
    (fun i hi => by
      have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by simp at hi; omega
      rcases hi3 with rfl | rfl | rfl
      · simpa using hw0
      · simpa using hb1
      · simpa using hw2)

/-- The center column is never eventually periodic with repeating word `1^r 0000`, `r ≥ 18`. -/
theorem no_period_black_run_then_0000 (T r t1 : Nat) (hr : 18 ≤ r)
    (hper : ∀ t, T ≤ t → center (t + (r + 4)) = center t) (ht1 : T ≤ t1)
    (hrun : ∀ s, s < r → center (t1 + s) = true)
    (hw0 : center (t1 + r) = false) (hw1 : center (t1 + r + 1) = false)
    (hw2 : center (t1 + r + 2) = false) (hw3 : center (t1 + r + 3) = false) : False :=
  no_black_run_block [false, false, false, false] 2 det_0000 (by decide) T r t1 hper ht1 (by omega) (by omega) hrun
    (fun i hi => by
      have hi4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by simp at hi; omega
      rcases hi4 with rfl | rfl | rfl | rfl
      · simpa using hw0
      · simpa using hw1
      · simpa using hw2
      · simpa using hw3)

/-- The center column is never eventually periodic with repeating word `1^r 0010`, `r ≥ 27`. -/
theorem no_period_black_run_then_0010 (T r t1 : Nat) (hr : 27 ≤ r)
    (hper : ∀ t, T ≤ t → center (t + (r + 4)) = center t) (ht1 : T ≤ t1)
    (hrun : ∀ s, s < r → center (t1 + s) = true)
    (hw0 : center (t1 + r) = false) (hw1 : center (t1 + r + 1) = false)
    (hb2 : center (t1 + r + 2) = true) (hw3 : center (t1 + r + 3) = false) : False :=
  no_black_run_block [false, false, true, false] 3 det_0010 (by decide) T r t1 hper ht1 (by omega) (by omega) hrun
    (fun i hi => by
      have hi4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by simp at hi; omega
      rcases hi4 with rfl | rfl | rfl | rfl
      · simpa using hw0
      · simpa using hw1
      · simpa using hb2
      · simpa using hw3)

/-- The center column is never eventually periodic with repeating word `1^r 0100`, `r ≥ 18`. -/
theorem no_period_black_run_then_0100 (T r t1 : Nat) (hr : 18 ≤ r)
    (hper : ∀ t, T ≤ t → center (t + (r + 4)) = center t) (ht1 : T ≤ t1)
    (hrun : ∀ s, s < r → center (t1 + s) = true)
    (hw0 : center (t1 + r) = false) (hb1 : center (t1 + r + 1) = true)
    (hw2 : center (t1 + r + 2) = false) (hw3 : center (t1 + r + 3) = false) : False :=
  no_black_run_block [false, true, false, false] 2 det_0100 (by decide) T r t1 hper ht1 (by omega) (by omega) hrun
    (fun i hi => by
      have hi4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by simp at hi; omega
      rcases hi4 with rfl | rfl | rfl | rfl
      · simpa using hw0
      · simpa using hb1
      · simpa using hw2
      · simpa using hw3)

/-- The center column is never eventually periodic with repeating word `1^r 0110`, `r ≥ 27`. -/
theorem no_period_black_run_then_0110 (T r t1 : Nat) (hr : 27 ≤ r)
    (hper : ∀ t, T ≤ t → center (t + (r + 4)) = center t) (ht1 : T ≤ t1)
    (hrun : ∀ s, s < r → center (t1 + s) = true)
    (hw0 : center (t1 + r) = false) (hb1 : center (t1 + r + 1) = true)
    (hb2 : center (t1 + r + 2) = true) (hw3 : center (t1 + r + 3) = false) : False :=
  no_black_run_block [false, true, true, false] 3 det_0110 (by decide) T r t1 hper ht1 (by omega) (by omega) hrun
    (fun i hi => by
      have hi4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by simp at hi; omega
      rcases hi4 with rfl | rfl | rfl | rfl
      · simpa using hw0
      · simpa using hb1
      · simpa using hb2
      · simpa using hw3)

/-- **Exhaustive Classification of White-Bounded Blocks of Length `1 ≤ |u| ≤ 4`
(`white_bounded_len_le_4_classify`):** every Boolean list `u` of length `1 ≤ u.length ≤ 4` whose
first and last entries are `false` is one of the 8 certified blocks `[false]`, `[false, false]`,
`[false, false, false]`, `[false, true, false]`, `[false, false, false, false]`,
`[false, false, true, false]`, `[false, true, false, false]`, or `[false, true, true, false]`. -/
theorem white_bounded_len_le_4_classify (u : List Bool)
    (h1 : 1 ≤ u.length) (h4 : u.length ≤ 4)
    (hhead : u.getD 0 true = false) (hlast : u.getD (u.length - 1) true = false) :
    (u = [false] ∨ u = [false, false] ∨ u = [false, false, false] ∨
      u = [false, false, false, false] ∨ u = [false, true, false, false]) ∨
    (u = [false, true, false] ∨ u = [false, false, true, false] ∨
      u = [false, true, true, false]) := by
  rcases u with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, tl⟩⟩⟩⟩⟩
  · simp at h1
  · simp at hhead; subst hhead; exact Or.inl (Or.inl rfl)
  · simp at hhead hlast; subst hhead; subst hlast; exact Or.inl (Or.inr (Or.inl rfl))
  · simp at hhead hlast; subst hhead; subst hlast
    cases b1
    · exact Or.inl (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inl rfl)
  · simp at hhead hlast; subst hhead; subst hlast
    cases b1 <;> cases b2
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    · exact Or.inr (Or.inr (Or.inr rfl))
  · simp at h4

/-- **Universal Determinacy of White-Bounded Blocks of Length `≤ 4`
(`determined_of_white_bounded_len_le_4`):** every white-bounded block `u` of length `1 ≤ u.length ≤ 4`
satisfies `Determined u 2 = true` or `Determined u 3 = true`. -/
theorem determined_of_white_bounded_len_le_4 (u : List Bool)
    (h1 : 1 ≤ u.length) (h4 : u.length ≤ 4)
    (hhead : u.getD 0 true = false) (hlast : u.getD (u.length - 1) true = false) :
    Determined u 2 = true ∨ Determined u 3 = true := by
  rcases white_bounded_len_le_4_classify u h1 h4 hhead hlast with
    (rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl)
  · exact Or.inl det_0
  · exact Or.inl det_00
  · exact Or.inl det_000
  · exact Or.inl det_0000
  · exact Or.inl det_0100
  · exact Or.inr det_010
  · exact Or.inr det_0010
  · exact Or.inr det_0110

/-- **Complete Exclusion of All White-Bounded Blocks of Length `1 ≤ |u| ≤ 4`
(`no_period_black_run_then_white_bounded_le_4`):** for every white-bounded block `u` of length
`1 ≤ u.length ≤ 4` and every black-run length `r ≥ 27`, the center column is never eventually
periodic with repeating word `1^r u`. -/
theorem no_period_black_run_then_white_bounded_le_4 (u : List Bool)
    (h1 : 1 ≤ u.length) (h4 : u.length ≤ 4)
    (hhead : u.getD 0 true = false) (hlast : u.getD (u.length - 1) true = false)
    (T r t1 : Nat) (hr : 27 ≤ r)
    (hper : ∀ t, T ≤ t → center (t + (r + u.length)) = center t)
    (ht1 : T ≤ t1) (hrun : ∀ s, s < r → center (t1 + s) = true)
    (hu : ∀ i, i < u.length → center (t1 + r + i) = u.getD i false) : False := by
  rcases determined_of_white_bounded_len_le_4 u h1 h4 hhead hlast with hdet2 | hdet3
  · exact no_black_run_block u 2 hdet2 (by omega) T r t1 hper ht1 (by omega) (by omega) hrun hu
  · exact no_black_run_block u 3 hdet3 (by omega) T r t1 hper ht1 (by omega) (by omega) hrun hu

end Rule30BlackRunBlocks
end Ruliology.CellularAutomata
