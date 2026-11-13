module

public import Ruliology.CellularAutomata.Rule30BlackRuns
public import Ruliology.CellularAutomata.Rule30FiniteMaskedJen

/-!
# Long black runs, for every configuration with a leftmost black cell

`Rule30BlackRuns` proves its exclusions for the single black cell. The nine-black shield is a
statement about light cones, so it holds in the evolution `evol x` of every configuration `x`.
The exclusions then use the seed only through Jen's theorem and its masked form, which
`Rule30FiniteConfigs` and `Rule30FiniteMaskedJen` prove for every configuration with a leftmost
black cell. So each exclusion holds for every such configuration and for every column `i`, not
only for the center column of the seed.

**Every configuration.**
* `nine_black`: if column `m` is black at times `t, …, t + 8`, then at time `t + 9` column
  `m + 1` is white and column `m + 2` is black. The finite core is `Rule30BlackRuns.nine_black_core`
  (all `2 ^ 11` rows of length 11), applied to the row of `evol x`.
* `black_shield`: if column `m` is black for `9 j` consecutive steps, columns `m + 1, …, m + 2 j`
  read `(white black)^j` right after them.
* `cone_agree`, `black_stays`, `col_in_white_run`: the right neighbourhood of a column, driven by
  the column.

**Every configuration with a leftmost black cell, every column `i`.**
* `not_eventuallyPeriodic_of_long_one_runs`: if from some time on every black run of column `i`
  that is followed by a white cell has length at least `9`, column `i` is not eventually
  periodic. `not_eventually_zero_ones`: so column `i` is never eventually `0 1^k` repeated with
  `k ≥ 9`.
* `no_long_black_run` (Theorem B): if column `i` has period `P` from `T`, no period contains a
  black run of length `r` with `9 ⌈(P - r + 9) / 2⌉ ≤ r`.
* `no_black_white_run` (Theorem D): no period contains a black run of length `s ≥ 9` followed by
  a white run of length `r ≥ 1 + 9 ⌈(k + 8) / 2⌉`, where `k = P - s - r`.
* `not_eventuallyPeriodic_of_long_one_runs_finite`, `no_long_black_run_finite`,
  `no_black_white_run_finite`: the same for every nonzero finite configuration.

So the black-run exclusions are uniform (FinConf and NumberLike): they
say nothing that singles out the seed.

Source: E. Jen, *Global properties of cellular automata*, J. Stat. Phys. 43 (1986) 219–242; the
exclusions are those of `Rule30BlackRuns`.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30FiniteBlackRuns

open Rule30Jen Rule30Realization Rule30PeriodTwoSideways Rule30FiniteConfigs Rule30FiniteMaskedJen
open Rule30BlackRuns (stepRow runBlack nine_black_core trailing)

/-! ### Finite rows of any evolution -/

/-- The cells at columns `p, p + 1, …, p + n - 1` at time `t` of the evolution of `x`. -/
def rowAt (x : Int → Bool) (t : Nat) (p : Int) : Nat → List Bool
  | 0 => []
  | n + 1 => evol x t p :: rowAt x t (p + 1) n

theorem length_rowAt (x : Int → Bool) (t : Nat) :
    ∀ (n : Nat) (p : Int), (rowAt x t p n).length = n
  | 0, _ => rfl
  | n + 1, p => by simp [rowAt, length_rowAt x t n (p + 1)]

theorem stepRow_rowAt (x : Int → Bool) (t : Nat) : ∀ (n : Nat) (p : Int),
    stepRow (evol x t (p - 1)) (rowAt x t p (n + 1)) = rowAt x (t + 1) p n
  | 0, _ => rfl
  | n + 1, p => by
    have ih := stepRow_rowAt x t n (p + 1)
    rw [show p + 1 - 1 = p by omega] at ih
    show rule (evol x t (p - 1)) (evol x t p) (evol x t (p + 1)) ::
        stepRow (evol x t p) (rowAt x t (p + 1) (n + 1)) =
      evol x (t + 1) p :: rowAt x (t + 1) (p + 1) n
    rw [ih]
    rfl

theorem runBlack_rowAt (x : Int → Bool) (m : Int) : ∀ (k n t : Nat),
    (∀ s, s < k → evol x (t + s) m = true) →
      runBlack k (rowAt x t (m + 1) (n + k)) = rowAt x (t + k) (m + 1) n
  | 0, n, t, _ => by simp [runBlack]
  | k + 1, n, t, h => by
    have h0 : evol x t m = true := by simpa using h 0 (by omega)
    have hstep : stepRow true (rowAt x t (m + 1) (n + k + 1)) =
        rowAt x (t + 1) (m + 1) (n + k) := by
      have := stepRow_rowAt x t (n + k) (m + 1)
      rw [show m + 1 - 1 = m by omega, h0] at this
      exact this
    have ih := runBlack_rowAt x m k n (t + 1) (fun s hs => by
      have := h (s + 1) (by omega)
      rwa [show t + (s + 1) = t + 1 + s by omega] at this)
    show runBlack k (stepRow true (rowAt x t (m + 1) (n + (k + 1)))) =
      rowAt x (t + (k + 1)) (m + 1) n
    rw [show n + (k + 1) = n + k + 1 by omega, hstep, ih, show t + 1 + k = t + (k + 1) by omega]

/-! ### The nine-black shield, in any evolution -/

/-- **The nine-black shield.** In the evolution of any configuration, a column black for 9
consecutive steps forces white, black right after them in the next two columns. -/
theorem nine_black (x : Int → Bool) (t : Nat) (m : Int)
    (h : ∀ s, s < 9 → evol x (t + s) m = true) :
    evol x (t + 9) (m + 1) = false ∧ evol x (t + 9) (m + 2) = true := by
  have h1 := runBlack_rowAt x m 9 2 t h
  have hmem : rowAt x t (m + 1) (2 + 9) ∈ allLists 11 := by
    have := mem_allLists (rowAt x t (m + 1) (2 + 9))
    rwa [length_rowAt] at this
  rw [nine_black_core _ hmem] at h1
  have h2 : rowAt x (t + 9) (m + 1) 2 = [evol x (t + 9) (m + 1), evol x (t + 9) (m + 1 + 1)] := rfl
  rw [h2] at h1
  simp only [List.cons.injEq] at h1
  refine ⟨h1.1.symm, ?_⟩
  rw [show m + 2 = m + 1 + 1 by omega]
  exact h1.2.1.symm

/-- **The `9 j` shield.** In the evolution of any configuration, a column black for `9 j`
consecutive steps forces `(white black)^j` in the next `2 j` columns right after them. -/
theorem black_shield (x : Int → Bool) (m : Int) : ∀ (j t : Nat),
    (∀ s, s < 9 * j → evol x (t + s) m = true) → ∀ i : Nat, 1 ≤ i → i ≤ j →
      evol x (t + 9 * j) (m + 2 * (i : Int) - 1) = false ∧
        evol x (t + 9 * j) (m + 2 * (i : Int)) = true
  | 0, _, _, i, hi1, hij => by omega
  | j + 1, t, h, i, hi1, hij => by
    by_cases hi : i ≤ j
    · have ih := black_shield x m j (t + 9) (fun s hs => by
        have := h (9 + s) (by omega)
        rwa [show t + (9 + s) = t + 9 + s by omega] at this) i hi1 hi
      rwa [show t + 9 + 9 * j = t + 9 * (j + 1) by omega] at ih
    · have hieq : i = j + 1 := by omega
      subst hieq
      -- column m + 2 j is black at the 9 times t + 9 j + s, s < 9
      have hcol : ∀ s, s < 9 → evol x (t + 9 * j + s) (m + 2 * (j : Int)) = true := by
        intro s hs
        by_cases hj : j = 0
        · subst hj
          have := h s (by omega)
          simpa using this
        · have ih := black_shield x m j (t + s) (fun s' hs' => by
            have := h (s + s') (by omega)
            rwa [show t + (s + s') = t + s + s' by omega] at this) j (by omega) (by omega)
          rw [show t + s + 9 * j = t + 9 * j + s by omega] at ih
          exact ih.2
      have hA := nine_black x (t + 9 * j) (m + 2 * (j : Int)) hcol
      rw [show t + 9 * j + 9 = t + 9 * (j + 1) by omega,
        show m + 2 * (j : Int) + 1 = m + 2 * ((j + 1 : Nat) : Int) - 1 by omega,
        show m + 2 * (j : Int) + 2 = m + 2 * ((j + 1 : Nat) : Int) by omega] at hA
      exact hA

/-- Agreement in the shrinking cone right of column `i`, driven by column `i`. -/
theorem cone_agree (x : Int → Bool) (i : Int) (t0 t1 n : Nat)
    (hdrv : ∀ s, evol x (t0 + s) i = evol x (t1 + s) i)
    (hrow : ∀ p : Int, i + 1 ≤ p → p ≤ i + n → evol x t0 p = evol x t1 p) :
    ∀ s : Nat, ∀ p : Int, i + 1 ≤ p → p + s ≤ i + n → evol x (t0 + s) p = evol x (t1 + s) p
  | 0, p, h1, h2 => by simpa using hrow p h1 (by omega)
  | s + 1, p, h1, h2 => by
    show rule (evol x (t0 + s) (p - 1)) (evol x (t0 + s) p) (evol x (t0 + s) (p + 1)) =
      rule (evol x (t1 + s) (p - 1)) (evol x (t1 + s) p) (evol x (t1 + s) (p + 1))
    have hl : evol x (t0 + s) (p - 1) = evol x (t1 + s) (p - 1) := by
      by_cases hp : p = i + 1
      · rw [show p - 1 = i by omega]; exact hdrv s
      · exact cone_agree x i t0 t1 n hdrv hrow s (p - 1) (by omega) (by omega)
    rw [hl, cone_agree x i t0 t1 n hdrv hrow s p h1 (by omega),
      cone_agree x i t0 t1 n hdrv hrow s (p + 1) (by omega) (by omega)]

/-- During a white run of column `i`, a black cell in column `i + 1` stays black. -/
theorem black_stays (x : Int → Bool) (i : Int) (a n : Nat)
    (hc : ∀ k, k < n → evol x (a + k) i = false) (h1 : evol x a (i + 1) = true) :
    ∀ k, k ≤ n → evol x (a + k) (i + 1) = true
  | 0, _ => by simpa using h1
  | k + 1, hk => by
    have ih := black_stays x i a n hc h1 k (by omega)
    show rule (evol x (a + k) (i + 1 - 1)) (evol x (a + k) (i + 1))
      (evol x (a + k) (i + 1 + 1)) = true
    rw [show i + 1 - 1 = i by omega, hc k (by omega), ih]
    rfl

/-- A white run of column `i` right after nine black cells: column `i + 1` is white at the first
white cell and black at the later ones. -/
theorem col_in_white_run' (x : Int → Bool) (i : Int) :
    ∀ k u, (∀ s, s < 9 → evol x (u + s) i = true) →
      (∀ j, j ≤ k → evol x (u + 9 + j) i = false) →
      evol x (u + 9 + k) (i + 1) = decide (k ≠ 0) ∧
        (k = 0 → evol x (u + 9) (i + 1 + 1) = true) := by
  intro k
  induction k with
  | zero =>
    intro u h9s hz
    have h9 := nine_black x u i h9s
    rw [show i + 2 = i + 1 + 1 by omega] at h9
    exact ⟨h9.1, fun _ => h9.2⟩
  | succ k ih =>
    intro u h9s hz
    refine ⟨?_, fun h => absurd h (by omega)⟩
    have hk0 : evol x (u + 9 + k) i = false := hz k (by omega)
    have hstep : evol x (u + 9 + (k + 1)) (i + 1) =
        rule (evol x (u + 9 + k) i) (evol x (u + 9 + k) (i + 1))
          (evol x (u + 9 + k) (i + 1 + 1)) := by
      show rule (evol x (u + 9 + k) (i + 1 - 1)) (evol x (u + 9 + k) (i + 1))
        (evol x (u + 9 + k) (i + 1 + 1)) = _
      rw [show i + 1 - 1 = i by omega]
    have ih' := ih u h9s (fun j hj => hz j (by omega))
    rw [hstep, hk0]
    cases k with
    | zero =>
      have e1 : evol x (u + 9 + 0) (i + 1) = false := ih'.1
      have e2 : evol x (u + 9) (i + 1 + 1) = true := ih'.2 rfl
      rw [e1, show u + 9 + 0 = u + 9 from rfl, e2]
      rfl
    | succ k =>
      rw [ih'.1]
      rfl

/-- Inside a white run of column `i` that starts right after nine black cells, column `i + 1` is
white at the first white cell and black at the later ones. -/
theorem col_in_white_run (x : Int → Bool) (i : Int) {T : Nat}
    (hruns : ∀ u, T ≤ u → evol x (u + 9) i = false → evol x (u + 8) i = true →
      ∀ s, s < 9 → evol x (u + s) i = true) :
    ∀ k u, T ≤ u → evol x (u + 8) i = true → (∀ j, j ≤ k → evol x (u + 9 + j) i = false) →
      evol x (u + 9 + k) (i + 1) = decide (k ≠ 0) ∧
        (k = 0 → evol x (u + 9) (i + 1 + 1) = true) :=
  fun k u hu h8 hz => col_in_white_run' x i k u (hruns u hu (hz 0 (by omega)) h8) hz

/-! ### Exclusions, for every configuration with a leftmost black cell -/

section LeftEdge
variable {x : Int → Bool} {lo : Int} (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
include hlo hzero

/-- **Long black runs exclude periodicity, any configuration, any column.** If from time `T` on
every black run of column `i` that is followed by a white cell has length at least `9`, then
column `i` is not eventually periodic. -/
theorem not_eventuallyPeriodic_of_long_one_runs (i : Int) {T : Nat}
    (hruns : ∀ u, T ≤ u → evol x (u + 9) i = false → evol x (u + 8) i = true →
      ∀ s, s < 9 → evol x (u + s) i = true) :
    ¬ EventuallyPeriodic fun t => evol x t i := by
  intro hc
  obtain ⟨T₀, P, hP, hper⟩ := hc
  have hper' : ∀ t, T₀ ≤ t → evol x (t + P) i = evol x t i := hper
  by_cases hw : ∃ t, T₀ ≤ t ∧ ∀ s, s < P → evol x (t + s) i = false
  · -- a white period window: column `i` is eventually white
    obtain ⟨t, ht, hs⟩ := hw
    have hk : ∀ k s, s < P → evol x (t + k * P + s) i = false := by
      intro k
      induction k with
      | zero => intro s hs'; simpa using hs s hs'
      | succ k ih =>
        intro s hs'
        rw [show t + (k + 1) * P + s = (t + k * P + s) + P by rw [Nat.succ_mul]; omega,
          hper' _ (by omega)]
        exact ih s hs'
    refine no_column_eventually_constant hlo hzero i ⟨t, false, fun u hu => ?_⟩
    have := hk ((u - t) / P) ((u - t) % P) (Nat.mod_lt _ hP)
    rwa [show t + (u - t) / P * P + (u - t) % P = u by
      have := Nat.div_add_mod (u - t) P; rw [Nat.mul_comm] at this; omega] at this
  · -- every period window after `T₀` contains a black cell
    have hblack : ∀ t, T₀ ≤ t → ∃ s, s < P ∧ evol x (t + s) i = true := by
      intro t ht
      refine Classical.byContradiction fun hne => hw ⟨t, ht, fun s hs => ?_⟩
      cases h : evol x (t + s) i
      · rfl
      · exact absurd ⟨s, hs, h⟩ hne
    let B := T + T₀ + P + 10
    have hform : ∀ t, B ≤ t → orCol x i t = (evol x t i || !evol x (t - 1) i) := by
      intro t ht
      cases h0 : evol x t i
      · rcases trailing (fun u => evol x u i) t h0 P with hall | ⟨k, hk, h1, h2⟩
        · obtain ⟨s, hs, hb⟩ := hblack (t - P) (by omega)
          have := hall (P - s) (by omega)
          rw [show t - (P - s) = t - P + s by omega, hb] at this
          exact absurd this (by decide)
        · have hrun := col_in_white_run x i hruns k (t - (k + 1) - 8) (by omega)
            (by rw [show t - (k + 1) - 8 + 8 = t - (k + 1) by omega]; exact h1)
            (fun j hj => by
              rw [show t - (k + 1) - 8 + 9 + j = t - (k - j) by omega]; exact h2 (k - j) (by omega))
          rw [show t - (k + 1) - 8 + 9 + k = t by omega] at hrun
          unfold orCol
          rw [h0, Bool.false_or, Bool.false_or, hrun.1]
          cases k with
          | zero =>
            have : evol x (t - 1) i = true := by simpa using h1
            rw [this]; rfl
          | succ k =>
            have : evol x (t - 1) i = false := by simpa using h2 1 (by omega)
            rw [this]; rfl
      · unfold orCol; rw [h0]; rfl
    refine orCol_not_eventuallyPeriodic hlo hzero i ⟨T₀, P, hP, hper⟩ ⟨B, P, hP, fun t ht => ?_⟩
    show orCol x i (t + P) = orCol x i t
    rw [hform t (by omega), hform (t + P) (by omega), hper' t (by omega),
      show t + P - 1 = (t - 1) + P by omega, hper' (t - 1) (by omega)]

/-- **The words `0 1^k`, `k ≥ 9`, are excluded**, in every column: column `i` is not eventually
equal to `0 1^k` repeated, whatever the transient. -/
theorem not_eventually_zero_ones (i : Int) (k : Nat) (hk : 9 ≤ k) (T : Nat) :
    ¬ ∀ t, T ≤ t → evol x t i = decide ((t - T) % (k + 1) ≠ 0) := by
  intro h
  refine not_eventuallyPeriodic_of_long_one_runs hlo hzero i (T := T)
    (fun u hu h9 _ s hs => ?_) ⟨T, k + 1, by omega, fun t ht => ?_⟩
  · -- `u + 9 - T` is a multiple of `k + 1`, so `u + s - T` is not
    rw [h (u + 9) (by omega)] at h9
    have hz : (u + 9 - T) % (k + 1) = 0 := by simpa using h9
    rw [h (u + s) (by omega)]
    simp only [decide_eq_true_eq]
    intro hm
    have e1 := Nat.div_add_mod (u + 9 - T) (k + 1)
    have e2 := Nat.div_add_mod (u + s - T) (k + 1)
    rw [hz] at e1
    rw [hm] at e2
    have hlt : (u + s - T) / (k + 1) < (u + 9 - T) / (k + 1) :=
      Nat.lt_of_mul_lt_mul_left (a := k + 1) (by omega)
    have hle := Nat.mul_le_mul_left (k + 1) (Nat.succ_le_of_lt hlt)
    rw [Nat.mul_succ] at hle
    omega
  · show evol x (t + (k + 1)) i = evol x t i
    rw [h (t + (k + 1)) (by omega), h t ht, show t + (k + 1) - T = (t - T) + (k + 1) by omega,
      Nat.add_mod_right]

/-- **Theorem B, any configuration, any column.** If column `i` has period `P` from time `T` on,
no period contains a black run of length `r` with `9 ⌈(P - r + 9) / 2⌉ ≤ r`. -/
theorem no_long_black_run (i : Int) (T P r t1 : Nat)
    (hper : ∀ t, T ≤ t → evol x (t + P) i = evol x t i)
    (ht1 : T ≤ t1) (hr : r ≤ P) (hrun : ∀ s, s < r → evol x (t1 + s) i = true)
    (hlong : 9 * ((P - r + 10) / 2) ≤ r) : False := by
  have hP : 0 < P := by omega
  -- j = ⌈(P - r + 9) / 2⌉
  have hj1 : P - r + 9 ≤ 2 * ((P - r + 10) / 2) := by omega
  generalize hjdef : (P - r + 10) / 2 = j at hj1 hlong
  have hperk : ∀ k t, T ≤ t → evol x (t + k * P) i = evol x t i :=
    periodic_mul (f := fun t => evol x t i) hper
  have hblack : ∀ k s, s < r → evol x (t1 + k * P + s) i = true := by
    intro k s hs
    have := hperk k (t1 + s) (by omega)
    rw [show t1 + k * P + s = t1 + s + k * P by omega, this]
    exact hrun s hs
  -- the row right after each black run reads (white black)^j on columns i + 1 .. i + 2j
  have hrowk : ∀ k m, 1 ≤ m → m ≤ j →
      evol x (t1 + r + k * P) (i + 2 * (m : Int) - 1) = false ∧
        evol x (t1 + r + k * P) (i + 2 * (m : Int)) = true := by
    intro k m hm1 hmj
    have := black_shield x i j (t1 + k * P + (r - 9 * j)) (fun s hs => by
        have := hblack k (r - 9 * j + s) (by omega)
        rwa [show t1 + k * P + (r - 9 * j + s) = t1 + k * P + (r - 9 * j) + s by omega] at this)
      m hm1 hmj
    rwa [show t1 + k * P + (r - 9 * j) + 9 * j = t1 + r + k * P by omega] at this
  have hrowagree : ∀ k, ∀ p : Int, i + 1 ≤ p → p ≤ i + ((2 * j : Nat) : Int) →
      evol x (t1 + r) p = evol x (t1 + r + k * P) p := by
    intro k p hp1 hp2
    have a0 := hrowk 0
    simp only [Nat.zero_mul, Nat.add_zero] at a0
    by_cases hpar : (p - i) % 2 = 0
    · have hi : p = i + 2 * ((((p - i) / 2).toNat : Nat) : Int) := by omega
      rw [hi, (a0 _ (by omega) (by omega)).2, (hrowk k _ (by omega) (by omega)).2]
    · have hi : p = i + 2 * ((((p - i + 1) / 2).toNat : Nat) : Int) - 1 := by omega
      rw [hi, (a0 _ (by omega) (by omega)).1, (hrowk k _ (by omega) (by omega)).1]
  have hdrv : ∀ k s, evol x (t1 + r + s) i = evol x (t1 + r + k * P + s) i := by
    intro k s
    have := hperk k (t1 + r + s) (by omega)
    rw [show t1 + r + k * P + s = t1 + r + s + k * P by omega, this]
  -- column i + 1 is white 9 steps into a black run of column i
  have white1 : ∀ t', (∀ s', s' < 9 → evol x (t' + s') i = true) →
      evol x (t' + 9) (i + 1) = false :=
    fun t' h => (nine_black x t' i h).1
  have hcol : ∀ k s, s < P →
      evol x (t1 + r + s) (i + 1) = evol x (t1 + r + k * P + s) (i + 1) := by
    intro k s hs
    by_cases hs1 : s + 1 ≤ 2 * j
    · exact cone_agree x i (t1 + r) (t1 + r + k * P) (2 * j) (hdrv k) (hrowagree k) s (i + 1)
        (by omega) (by omega)
    · have hPk : (k + 1) * P = k * P + P := Nat.succ_mul k P
      have a : evol x (t1 + r + s) (i + 1) = false := by
        have := white1 (t1 + r + s - 9) (fun s' hs' => by
          have := hblack 1 (s - 9 + s' - (P - r)) (by omega)
          rwa [show t1 + 1 * P + (s - 9 + s' - (P - r)) = t1 + r + s - 9 + s' by omega] at this)
        rwa [show t1 + r + s - 9 + 9 = t1 + r + s by omega] at this
      have b : evol x (t1 + r + k * P + s) (i + 1) = false := by
        have := white1 (t1 + r + k * P + s - 9) (fun s' hs' => by
          have := hblack (k + 1) (s - 9 + s' - (P - r)) (by omega)
          rwa [hPk, show t1 + (k * P + P) + (s - 9 + s' - (P - r)) =
            t1 + r + k * P + s - 9 + s' by omega] at this)
        rwa [show t1 + r + k * P + s - 9 + 9 = t1 + r + k * P + s by omega] at this
      rw [a, b]
  -- column i + 1 is eventually periodic, against Jen's theorem
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

/-- **Theorem D, any configuration, any column.** If column `i` has period `P` from `T` on, a
period cannot contain a black run of length `s ≥ 9` immediately followed by a white run of length
`r` with `r ≥ 1 + 9 ⌈(k + 8) / 2⌉`, where `k = P - s - r` is the length of the rest of the
period. -/
theorem no_black_white_run (i : Int) (T P s r t1 : Nat)
    (hper : ∀ t, T ≤ t → evol x (t + P) i = evol x t i)
    (ht1 : T ≤ t1) (hs : 9 ≤ s) (hsr : s + r ≤ P)
    (hblk : ∀ n, n < s → evol x (t1 + n) i = true)
    (hwht : ∀ n, n < r → evol x (t1 + s + n) i = false)
    (hlong : 1 + 9 * ((P - s - r + 9) / 2) ≤ r) : False := by
  have hP : 0 < P := by omega
  have hj1 : P - s - r + 8 ≤ 2 * ((P - s - r + 9) / 2) := by omega
  generalize hjdef : (P - s - r + 9) / 2 = j at hj1 hlong
  have hperk : ∀ k t, T ≤ t → evol x (t + k * P) i = evol x t i :=
    periodic_mul (f := fun t => evol x t i) hper
  have hMul : ∀ k, (k + 1) * P = k * P + P := fun k => Nat.succ_mul k P
  have cblk : ∀ k n, n < s → evol x (t1 + k * P + n) i = true := by
    intro k n hn
    have := hperk k (t1 + n) (by omega)
    rw [show t1 + k * P + n = t1 + n + k * P by omega, this]; exact hblk n hn
  have cwht : ∀ k n, n < r → evol x (t1 + s + k * P + n) i = false := by
    intro k n hn
    have := hperk k (t1 + s + n) (by omega)
    rw [show t1 + s + k * P + n = t1 + s + n + k * P by omega, this]; exact hwht n hn
  -- start of the white run of period k: column i + 1 white, column i + 2 black
  have hstart : ∀ k, evol x (t1 + s + k * P) (i + 1) = false ∧
      evol x (t1 + s + k * P) (i + 2) = true := by
    intro k
    have := nine_black x (t1 + k * P + (s - 9)) i (fun n hn => by
      have := cblk k (s - 9 + n) (by omega)
      rwa [show t1 + k * P + (s - 9 + n) = t1 + k * P + (s - 9) + n by omega] at this)
    rwa [show t1 + k * P + (s - 9) + 9 = t1 + s + k * P by omega] at this
  -- column i + 1 is black during the rest of the white run
  have hrun1 : ∀ k n, 1 ≤ n → n ≤ r → evol x (t1 + s + k * P + n) (i + 1) = true := by
    intro k n hn1 hnr
    have c1 : evol x (t1 + s + k * P + 1) (i + 1) = true := by
      show rule (evol x (t1 + s + k * P) (i + 1 - 1)) (evol x (t1 + s + k * P) (i + 1))
        (evol x (t1 + s + k * P) (i + 1 + 1)) = true
      have h0 := cwht k 0 (by omega)
      rw [show t1 + s + k * P + 0 = t1 + s + k * P by omega] at h0
      rw [show i + 1 - 1 = i by omega, show i + 1 + 1 = i + 2 by omega, h0, (hstart k).1,
        (hstart k).2]
      rfl
    have := black_stays x i (t1 + s + k * P + 1) (r - 1) (fun n' hn' => by
      have := cwht k (1 + n') (by omega)
      rwa [show t1 + s + k * P + (1 + n') = t1 + s + k * P + 1 + n' by omega] at this) c1
      (n - 1) (by omega)
    rwa [show t1 + s + k * P + 1 + (n - 1) = t1 + s + k * P + n by omega] at this
  -- at the end of the white run: column i + 1 black, columns i + 2 .. i + 2j + 1 read
  -- (white black)^j
  have hend : ∀ k m, 1 ≤ m → m ≤ j →
      evol x (t1 + s + r + k * P) (i + 1 + 2 * (m : Int) - 1) = false ∧
        evol x (t1 + s + r + k * P) (i + 1 + 2 * (m : Int)) = true := by
    intro k m hm1 hmj
    have := black_shield x (i + 1) j (t1 + s + k * P + (r - 9 * j)) (fun n hn => by
        have := hrun1 k (r - 9 * j + n) (by omega) (by omega)
        rwa [show t1 + s + k * P + (r - 9 * j + n) = t1 + s + k * P + (r - 9 * j) + n by omega]
          at this) m hm1 hmj
    rwa [show t1 + s + k * P + (r - 9 * j) + 9 * j = t1 + s + r + k * P by omega] at this
  have hrowagree : ∀ k, ∀ p : Int, i + 1 ≤ p → p ≤ i + ((2 * j + 1 : Nat) : Int) →
      evol x (t1 + s + r) p = evol x (t1 + s + r + k * P) p := by
    intro k p hp1 hp2
    by_cases hp : p = i + 1
    · subst hp
      have a := hrun1 0 r (by omega) (Nat.le_refl r)
      have b := hrun1 k r (by omega) (Nat.le_refl r)
      simp only [Nat.zero_mul, Nat.add_zero] at a
      rw [show t1 + s + k * P + r = t1 + s + r + k * P by omega] at b
      rw [a, b]
    have a0 := hend 0
    simp only [Nat.zero_mul, Nat.add_zero] at a0
    by_cases hpar : (p - i) % 2 = 0
    · have hi : p = i + 1 + 2 * ((((p - i) / 2).toNat : Nat) : Int) - 1 := by omega
      rw [hi, (a0 _ (by omega) (by omega)).1, (hend k _ (by omega) (by omega)).1]
    · have hi : p = i + 1 + 2 * ((((p - i - 1) / 2).toNat : Nat) : Int) := by omega
      rw [hi, (a0 _ (by omega) (by omega)).2, (hend k _ (by omega) (by omega)).2]
  have hdrv : ∀ k n, evol x (t1 + s + r + n) i = evol x (t1 + s + r + k * P + n) i := by
    intro k n
    have := hperk k (t1 + s + r + n) (by omega)
    rw [show t1 + s + r + k * P + n = t1 + s + r + n + k * P by omega, this]
  have white1 : ∀ t', (∀ n, n < 9 → evol x (t' + n) i = true) →
      evol x (t' + 9) (i + 1) = false :=
    fun t' h => (nine_black x t' i h).1
  -- column i + 1 over one period starting at the white run: independent of the period index
  have hcol : ∀ k n, n < P →
      evol x (t1 + s + n) (i + 1) = evol x (t1 + s + k * P + n) (i + 1) := by
    intro k n hn
    by_cases hn0 : n = 0
    · subst hn0
      have a := (hstart 0).1
      simp only [Nat.zero_mul, Nat.add_zero] at a
      simp only [Nat.add_zero]
      rw [a, (hstart k).1]
    by_cases hnr : n ≤ r
    · have a := hrun1 0 n (by omega) hnr
      simp only [Nat.zero_mul, Nat.add_zero] at a
      rw [a, hrun1 k n (by omega) hnr]
    by_cases hnc : n ≤ r + 2 * j
    · have := cone_agree x i (t1 + s + r) (t1 + s + r + k * P) (2 * j + 1) (hdrv k)
        (hrowagree k) (n - r) (i + 1) (by omega) (by omega)
      rwa [show t1 + s + r + (n - r) = t1 + s + n by omega,
        show t1 + s + r + k * P + (n - r) = t1 + s + k * P + n by omega] at this
    · -- at least nine steps into the next black run
      have wk : ∀ k', evol x (t1 + s + k' * P + n) (i + 1) = false := by
        intro k'
        have := white1 (t1 + s + k' * P + n - 9) (fun n' hn' => by
          have := cblk (k' + 1) (s + n - 9 + n' - P) (by omega)
          rwa [hMul k', show t1 + (k' * P + P) + (s + n - 9 + n' - P) =
            t1 + s + k' * P + n - 9 + n' by omega] at this)
        rwa [show t1 + s + k' * P + n - 9 + 9 = t1 + s + k' * P + n by omega] at this
      have w0 := wk 0
      simp only [Nat.zero_mul, Nat.add_zero] at w0
      rw [w0, wk k]
  have h1 : EventuallyPeriodic (fun t => evol x t (i + 1)) := by
    refine ⟨t1 + s, P, hP, fun t ht => ?_⟩
    show evol x (t + P) (i + 1) = evol x t (i + 1)
    have hdm := Nat.div_add_mod (t - (t1 + s)) P
    generalize (t - (t1 + s)) / P = q at hdm
    have hmod := Nat.mod_lt (t - (t1 + s)) hP
    generalize (t - (t1 + s)) % P = n at hdm hmod
    have hq1 : (q + 1) * P = q * P + P := Nat.succ_mul q P
    have hcomm : P * q = q * P := Nat.mul_comm P q
    have e1 := hcol q n hmod
    have e2 := hcol (q + 1) n hmod
    rw [hq1] at e2
    rw [show t + P = t1 + s + (q * P + P) + n by omega, ← e2, e1,
      show t1 + s + q * P + n = t by omega]
  exact not_adjacent hlo hzero i ⟨T, P, hP, hper⟩ h1

end LeftEdge

/-! ### Finite configurations -/

section Finite
variable {x : Int → Bool} (hfin : FinConfig x) (hne : ∃ p, x p = true)
include hfin hne

/-- **Long black runs, every nonzero finite configuration.** -/
theorem not_eventuallyPeriodic_of_long_one_runs_finite (i : Int) {T : Nat}
    (hruns : ∀ u, T ≤ u → evol x (u + 9) i = false → evol x (u + 8) i = true →
      ∀ s, s < 9 → evol x (u + s) i = true) :
    ¬ EventuallyPeriodic fun t => evol x t i := by
  obtain ⟨lo, hlo, hzero⟩ := exists_leftmost hfin hne
  exact not_eventuallyPeriodic_of_long_one_runs hlo hzero i hruns

/-- **Theorem B, every nonzero finite configuration.** -/
theorem no_long_black_run_finite (i : Int) (T P r t1 : Nat)
    (hper : ∀ t, T ≤ t → evol x (t + P) i = evol x t i)
    (ht1 : T ≤ t1) (hr : r ≤ P) (hrun : ∀ s, s < r → evol x (t1 + s) i = true)
    (hlong : 9 * ((P - r + 10) / 2) ≤ r) : False := by
  obtain ⟨lo, hlo, hzero⟩ := exists_leftmost hfin hne
  exact no_long_black_run hlo hzero i T P r t1 hper ht1 hr hrun hlong

/-- **Theorem D, every nonzero finite configuration.** -/
theorem no_black_white_run_finite (i : Int) (T P s r t1 : Nat)
    (hper : ∀ t, T ≤ t → evol x (t + P) i = evol x t i)
    (ht1 : T ≤ t1) (hs : 9 ≤ s) (hsr : s + r ≤ P)
    (hblk : ∀ n, n < s → evol x (t1 + n) i = true)
    (hwht : ∀ n, n < r → evol x (t1 + s + n) i = false)
    (hlong : 1 + 9 * ((P - s - r + 9) / 2) ≤ r) : False := by
  obtain ⟨lo, hlo, hzero⟩ := exists_leftmost hfin hne
  exact no_black_white_run hlo hzero i T P s r t1 hper ht1 hs hsr hblk hwht hlong

end Finite

/-! ### Finite-configuration (`FinConfig`) exclusion of `0 1^k` (`k ≥ 9`) and post-shield white-run persistence -/

/-- **The words `0 1^k`, `k ≥ 9`, are excluded for every nonzero finite configuration (`not_eventually_zero_ones_finite`).** -/
theorem not_eventually_zero_ones_finite {x : Int → Bool}
    (hfin : Rule30PeriodTwoSideways.FinConfig x) (hne : ∃ p, x p = true)
    (i : Int) (k : Nat) (hk : 9 ≤ k) (T : Nat) :
    ¬ ∀ t, T ≤ t → evol x t i = decide ((t - T) % (k + 1) ≠ 0) := by
  obtain ⟨lo, hlo, hzero⟩ := exists_leftmost hfin hne
  exact not_eventually_zero_ones hlo hzero i k hk T

/-- **Post-Shield White-to-Black Transition on Column `i + 1` (`nine_black_then_white_run_col1`):**
if column `i` is black for `9` steps from `u` and then white through `u + 9 + r`, column `i + 1`
is white at `u + 9`, column `i + 2` is black at `u + 9`, and column `i + 1` is black for all `1 ≤ k ≤ r`. -/
theorem nine_black_then_white_run_col1 (x : Int → Bool) (i : Int) (u r : Nat)
    (h9 : ∀ s, s < 9 → evol x (u + s) i = true)
    (hw : ∀ j, j ≤ r → evol x (u + 9 + j) i = false) :
    evol x (u + 9) (i + 1) = false ∧
    evol x (u + 9) (i + 2) = true ∧
    ∀ k, 1 ≤ k → k ≤ r → evol x (u + 9 + k) (i + 1) = true := by
  have hbase := col_in_white_run' x i 0 u h9 (fun j hj => hw j (by omega))
  refine ⟨hbase.1, by simpa [show i + 1 + 1 = i + 2 by omega] using hbase.2 rfl, fun k hk1 hkr => ?_⟩
  have hk := (col_in_white_run' x i k u h9 (fun j hj => hw j (by omega))).1
  rw [hk]
  exact decide_eq_true (by omega)

end Rule30FiniteBlackRuns
end Ruliology.CellularAutomata
