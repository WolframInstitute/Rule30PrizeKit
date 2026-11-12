module

public import Ruliology.CellularAutomata.Rule30BlackRunBlocks
public import Ruliology.CellularAutomata.Rule30FiniteBlackRuns

/-!
# Theorem B′ for every configuration with a leftmost black cell

`Rule30BlackRunBlocks.no_black_run_block` (Theorem B′) excludes the repeating word `1^r u` from the
center column of the single black cell whenever the finite check `Determined u j0` holds. Its proof
uses the seed only through Jen's theorem. The nine-black shield and the column-1 trace hold in every
evolution (`Rule30FiniteBlackRuns.black_shield`, `nine_black`). So Theorem B′ holds for every
configuration with a leftmost black cell and every column `i`, as Theorems B and D do in
`Rule30FiniteBlackRuns`.

* `colTraceAt`, `traceCol1_rowAt`, `rowAt_split`, `rowAt_wb`: the trace of column `i + 1` driven by
  column `i`, and the `(white black)^j` rows, in the evolution `evol x` of any configuration.
* `no_black_run_block` (**Theorem B′**, any configuration with a leftmost black cell, any column
  `i`): if `Determined u j0` holds, column `i` is not eventually periodic with repeating word
  `1^r u` for any `r ≥ max 9 (9 j0)`, whatever the transient.
* `no_period_black_run_then_white`: the instance `1^r 0`, `r ≥ 18`, from the existing check
  `Rule30BlackRunBlocks.det_0`. The other checked blocks (`det_00`, …, `det_0110`) apply in the same
  way.
* `no_black_run_block_finite`: Theorem B′ for every nonzero finite configuration.

Source: as for `Rule30BlackRunBlocks`. The port follows `Rule30FiniteBlackRuns`.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30FiniteBlackRunBlocks

open Rule30Jen Rule30Realization Rule30PeriodTwoSideways Rule30FiniteConfigs Rule30FiniteBlackRuns
open Rule30BlackRuns (stepRow)
open Rule30BlackRunBlocks (traceCol1 wbPattern drv getD_drv_black Determined)

/-! ### Traces and rows of any evolution -/

/-- Column `p` at times `e, e + 1, …, e + n`. -/
def colTraceAt (x : Int → Bool) (p : Int) (e : Nat) : Nat → List Bool
  | 0 => [evol x e p]
  | n + 1 => evol x e p :: colTraceAt x p (e + 1) n

theorem colTraceAt_getD (x : Int → Bool) (p : Int) : ∀ (n e s : Nat), s ≤ n →
    (colTraceAt x p e n).getD s false = evol x (e + s) p
  | 0, e, s, h => by
    have : s = 0 := by omega
    subst this; rfl
  | n + 1, e, 0, _ => rfl
  | n + 1, e, s + 1, h => by
    show (colTraceAt x p (e + 1) n).getD s false = evol x (e + (s + 1)) p
    rw [colTraceAt_getD x p n (e + 1) s (by omega), show e + 1 + s = e + (s + 1) by omega]

/-- The column-`(i + 1)` trace of the row right of column `i`, driven by column `i`. -/
theorem traceCol1_rowAt (x : Int → Bool) (i : Int) : ∀ (ds : List Bool) (e : Nat),
    (∀ k, k < ds.length → evol x (e + k) i = ds.getD k false) →
    traceCol1 ds (rowAt x e (i + 1) (ds.length + 1)) = colTraceAt x (i + 1) e ds.length
  | [], e, _ => rfl
  | c :: cs, e, h => by
    have h0 : evol x e i = c := by simpa using h 0 (by simp)
    have hstep : stepRow c (rowAt x e (i + 1) (cs.length + 1 + 1)) =
        rowAt x (e + 1) (i + 1) (cs.length + 1) := by
      have := stepRow_rowAt x e (cs.length + 1) (i + 1)
      rw [show i + 1 - 1 = i by omega, h0] at this
      exact this
    have ih := traceCol1_rowAt x i cs (e + 1) (fun k hk => by
      have := h (k + 1) (by simp; omega)
      rw [show e + (k + 1) = e + 1 + k by omega] at this
      simpa using this)
    show evol x e (i + 1) :: traceCol1 cs (stepRow c (rowAt x e (i + 1) (cs.length + 1 + 1))) =
      evol x e (i + 1) :: colTraceAt x (i + 1) (e + 1) cs.length
    rw [hstep, ih]

theorem rowAt_split (x : Int → Bool) (t : Nat) :
    ∀ (a b : Nat) (p : Int), rowAt x t p (a + b) = rowAt x t p a ++ rowAt x t (p + a) b
  | 0, b, p => by simp [rowAt]
  | a + 1, b, p => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    show evol x t p :: rowAt x t (p + 1) (a + b) =
      evol x t p :: rowAt x t (p + 1) a ++ rowAt x t (p + ((a + 1 : Nat) : Int)) b
    rw [rowAt_split x t a b (p + 1), show p + 1 + (a : Int) = p + ((a + 1 : Nat) : Int) by omega]
    rfl

theorem rowAt_wb (x : Int → Bool) (t : Nat) (p : Int) : ∀ j : Nat, (∀ m : Nat, 1 ≤ m → m ≤ j →
    evol x t (p + 2 * (m : Int) - 2) = false ∧ evol x t (p + 2 * (m : Int) - 1) = true) →
    rowAt x t p (2 * j) = wbPattern j
  | 0, _ => rfl
  | j + 1, h => by
    have h1 := h 1 (by omega) (by omega)
    rw [show p + 2 * ((1 : Nat) : Int) - 2 = p by omega,
      show p + 2 * ((1 : Nat) : Int) - 1 = p + 1 by omega] at h1
    have ih := rowAt_wb x t (p + 2) j (fun m hm1 hmj => by
      have := h (m + 1) (by omega) (by omega)
      rw [show p + 2 * ((m + 1 : Nat) : Int) - 2 = p + 2 + 2 * (m : Int) - 2 by omega,
        show p + 2 * ((m + 1 : Nat) : Int) - 1 = p + 2 + 2 * (m : Int) - 1 by omega] at this
      exact this)
    show evol x t p :: evol x t (p + 1) :: rowAt x t (p + 1 + 1) (2 * j) =
      false :: true :: wbPattern j
    rw [h1.1, h1.2, show p + 1 + 1 = p + 2 by omega, ih]

/-! ### Theorem B′, for every configuration with a leftmost black cell -/

section LeftEdge
variable {x : Int → Bool} {lo : Int} (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
include hlo hzero

/-- **Theorem B′, any configuration with a leftmost black cell, any column.** A black run of length
`r ≥ max 9 (9 j0)` followed by a block `u` with `Determined u j0` cannot be the repeating word of an
eventually periodic column `i`. -/
theorem no_black_run_block (i : Int) (u : List Bool) (j0 : Nat) (hdet : Determined u j0 = true)
    (hj0 : 2 * j0 ≤ u.length + 10) (T r t1 : Nat)
    (hper : ∀ t, T ≤ t → evol x (t + (r + u.length)) i = evol x t i)
    (ht1 : T ≤ t1) (hr9 : 9 ≤ r) (hrj : 9 * j0 ≤ r)
    (hrun : ∀ s, s < r → evol x (t1 + s) i = true)
    (hu : ∀ k, k < u.length → evol x (t1 + r + k) i = u.getD k false) : False := by
  generalize hPdef : r + u.length = P at hper
  have hP : 0 < P := by omega
  have hperk : ∀ k t, T ≤ t → evol x (t + k * P) i = evol x t i :=
    periodic_mul (f := fun t => evol x t i) hper
  have hblack : ∀ k s, s < r → evol x (t1 + k * P + s) i = true := by
    intro k s hs
    have := hperk k (t1 + s) (by omega)
    rw [show t1 + k * P + s = t1 + s + k * P by omega, this]
    exact hrun s hs
  have hublock : ∀ k m, m < u.length → evol x (t1 + r + k * P + m) i = u.getD m false := by
    intro k m hm
    have := hperk k (t1 + r + m) (by omega)
    rw [show t1 + r + k * P + m = t1 + r + m + k * P by omega, this]
    exact hu m hm
  -- the drivers from e_k = t1 + r + k P: u, then nine black cells
  have hdrv : ∀ k m, m < (drv u).length →
      evol x (t1 + r + k * P + m) i = (drv u).getD m false := by
    intro k m hm
    simp only [drv, List.length_append, List.length_replicate] at hm
    by_cases hmu : m < u.length
    · rw [hublock k m hmu]; simp [drv, List.getD_eq_getElem?_getD, List.getElem?_append_left hmu]
    · have hPk : (k + 1) * P = k * P + P := Nat.succ_mul k P
      have := hblack (k + 1) (m - u.length) (by omega)
      rw [hPk, show t1 + (k * P + P) + (m - u.length) = t1 + r + k * P + m by omega] at this
      rw [this, getD_drv_black u m (by omega) (by omega)]
  -- the row at e_k right of column i: (white black)^j0, then some tail
  have hrow : ∀ k, rowAt x (t1 + r + k * P) (i + 1) (2 * j0) = wbPattern j0 := by
    intro k
    apply rowAt_wb
    intro m hm1 hmj
    have := black_shield x i j0 (t1 + k * P + (r - 9 * j0)) (fun s hs => by
        have := hblack k (r - 9 * j0 + s) (by omega)
        rwa [show t1 + k * P + (r - 9 * j0 + s) = t1 + k * P + (r - 9 * j0) + s by omega] at this)
      m hm1 hmj
    rw [show t1 + k * P + (r - 9 * j0) + 9 * j0 = t1 + r + k * P by omega] at this
    rw [show i + 1 + 2 * (m : Int) - 2 = i + 2 * (m : Int) - 1 by omega,
      show i + 1 + 2 * (m : Int) - 1 = i + 2 * (m : Int) by omega]
    exact this
  -- the column-(i+1) trace from e_k does not depend on k
  have htrace : ∀ k, colTraceAt x (i + 1) (t1 + r + k * P) (drv u).length =
      traceCol1 (drv u) (wbPattern j0 ++ List.replicate (u.length + 10 - 2 * j0) false) := by
    intro k
    rw [← traceCol1_rowAt x i (drv u) (t1 + r + k * P) (hdrv k)]
    have hlen : (drv u).length + 1 = 2 * j0 + (u.length + 10 - 2 * j0) := by
      simp [drv]; omega
    rw [hlen, rowAt_split, hrow k]
    have hmem : rowAt x (t1 + r + k * P) (i + 1 + ((2 * j0 : Nat) : Int)) (u.length + 10 - 2 * j0) ∈
        allLists (u.length + 10 - 2 * j0) := by
      have := mem_allLists
        (rowAt x (t1 + r + k * P) (i + 1 + ((2 * j0 : Nat) : Int)) (u.length + 10 - 2 * j0))
      rwa [length_rowAt] at this
    have := List.all_eq_true.mp hdet _ hmem
    simpa using this
  have hcol : ∀ k s, s < P →
      evol x (t1 + r + s) (i + 1) = evol x (t1 + r + k * P + s) (i + 1) := by
    intro k s hs
    by_cases hs1 : s < (drv u).length + 1
    · have a := congrArg (fun l => l.getD s false) (htrace 0)
      have b := congrArg (fun l => l.getD s false) (htrace k)
      simp only [Nat.zero_mul, Nat.add_zero] at a b
      rw [colTraceAt_getD _ _ _ _ _ (by omega)] at a b
      rw [a, b]
    · simp only [drv, List.length_append, List.length_replicate] at hs1
      have white1 : ∀ t', (∀ s', s' < 9 → evol x (t' + s') i = true) →
          evol x (t' + 9) (i + 1) = false := fun t' h => (nine_black x t' i h).1
      have hPk : ∀ k', (k' + 1) * P = k' * P + P := fun k' => Nat.succ_mul k' P
      have wk : ∀ k', evol x (t1 + r + k' * P + s) (i + 1) = false := by
        intro k'
        have := white1 (t1 + r + k' * P + s - 9) (fun s' hs' => by
          have := hblack (k' + 1) (s - 9 + s' - u.length) (by omega)
          rwa [hPk, show t1 + (k' * P + P) + (s - 9 + s' - u.length) =
            t1 + r + k' * P + s - 9 + s' by omega] at this)
        rwa [show t1 + r + k' * P + s - 9 + 9 = t1 + r + k' * P + s by omega] at this
      have w0 := wk 0
      simp only [Nat.zero_mul, Nat.add_zero] at w0
      rw [w0, wk k]
  have h1 : EventuallyPeriodic (fun t => evol x t (i + 1)) := by
    refine ⟨t1 + r, P, hP, fun t ht => ?_⟩
    show evol x (t + P) (i + 1) = evol x t (i + 1)
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
  exact not_adjacent hlo hzero i ⟨T, P, hP, hper⟩ h1

/-- **The block `0`**: no column of a configuration with a leftmost black cell is eventually
periodic with repeating word `1^r 0`, `r ≥ 18`, whatever the transient. -/
theorem no_period_black_run_then_white (i : Int) (T r t1 : Nat) (hr : 18 ≤ r)
    (hper : ∀ t, T ≤ t → evol x (t + (r + 1)) i = evol x t i) (ht1 : T ≤ t1)
    (hrun : ∀ s, s < r → evol x (t1 + s) i = true) (hw : evol x (t1 + r) i = false) : False :=
  no_black_run_block hlo hzero i [false] 2 Rule30BlackRunBlocks.det_0 (by decide) T r t1 hper ht1
    (by omega) (by omega) hrun (fun k hk => by
      have : k = 0 := by simp at hk; omega
      subst this; simpa using hw)

end LeftEdge

/-! ### Finite configurations -/

/-- **Theorem B′, every nonzero finite configuration.** -/
theorem no_black_run_block_finite {x : Int → Bool} (hfin : FinConfig x) (hne : ∃ p, x p = true)
    (i : Int) (u : List Bool) (j0 : Nat) (hdet : Determined u j0 = true)
    (hj0 : 2 * j0 ≤ u.length + 10) (T r t1 : Nat)
    (hper : ∀ t, T ≤ t → evol x (t + (r + u.length)) i = evol x t i)
    (ht1 : T ≤ t1) (hr9 : 9 ≤ r) (hrj : 9 * j0 ≤ r)
    (hrun : ∀ s, s < r → evol x (t1 + s) i = true)
    (hu : ∀ k, k < u.length → evol x (t1 + r + k) i = u.getD k false) : False := by
  obtain ⟨lo, hlo, hzero⟩ := exists_leftmost hfin hne
  exact no_black_run_block hlo hzero i u j0 hdet hj0 T r t1 hper ht1 hr9 hrj hrun hu

/-! ### Exact length of `colTraceAt` and finite-configuration (`FinConfig`) exclusion of `1^r 0` (`r ≥ 18`) -/

/-- **Exact Length of `colTraceAt` (`colTraceAt_length`).** -/
theorem colTraceAt_length (x : Int → Bool) (p : Int) :
    ∀ (n e : Nat), (colTraceAt x p e n).length = n + 1
  | 0, _ => rfl
  | n + 1, e => by simp [colTraceAt, colTraceAt_length x p n (e + 1)]

/-- **Finite-Configuration (`FinConfig`) Exclusion of Repeating `1^r 0` for `r ≥ 18` (`no_period_black_run_then_white_finite`).** -/
theorem no_period_black_run_then_white_finite {x : Int → Bool}
    (hfin : Rule30PeriodTwoSideways.FinConfig x) (hne : ∃ p, x p = true)
    (i : Int) (T r t1 : Nat) (hr : 18 ≤ r)
    (hper : ∀ t, T ≤ t → evol x (t + (r + 1)) i = evol x t i) (ht1 : T ≤ t1)
    (hrun : ∀ s, s < r → evol x (t1 + s) i = true) (hw : evol x (t1 + r) i = false) : False := by
  obtain ⟨lo, hlo, hzero⟩ := exists_leftmost hfin hne
  exact no_period_black_run_then_white hlo hzero i T r t1 hr hper ht1 hrun hw

end Rule30FiniteBlackRunBlocks
end Ruliology.CellularAutomata
