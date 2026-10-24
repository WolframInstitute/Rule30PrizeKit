module

public import Ruliology.CellularAutomata.Rule30Jen
public import Ruliology.CellularAutomata.Rule30Prize
public import Ruliology.CellularAutomata.Rule30Diagonals
public import Ruliology.CellularAutomata.Rule30BlackRuns
public import Ruliology.CellularAutomata.Rule30Realization
public import Ruliology.CellularAutomata.Rule30FiniteConfigs

/-!
# Runs of the center column are at most linear in time, so both colors recur geometrically

**Partial result.** For the center column `c t = Rule30Prize.center t` of rule 30 from a single
black cell. A *run of length `L` starting at time `a`* is any block of `L` consecutive cells
`c a, …, c (a + L - 1)` of one color, stated as `∀ i, i < L → center (a + i) = b`. It does not have
to be maximal: `c (a - 1)` is unconstrained.

* **Black runs.** A black run that starts at time `a ≥ 1` has length at most `a` (`black_run_le`).
  The bound is attained at `a = 3` (`c 3 = c 4 = c 5 = 1`).
* **White runs.** A white run that starts at time `a ≥ 1` has length at most `a - 1`
  (`white_run_le'`), and for `a ≥ 3` at most `a - 3` (`white_run_le_three`). With truncated
  subtraction, `a = 1` says `c 1 = 1`. The bound `a - 1` is attained only at `a = 2` (`c 2 = 0`);
  `a - 3` is not attained up to time 3000, where the closest case is `a = 6` (`c 6 = c 7 = 0`,
  length `2 = a - 4`).
* **Recurrence.** Every window `[a, 2a]` holds a white cell (`exists_white`). Every window `[a, 2a)`
  holds a black cell (`exists_black'`), and so does `[a, 2a - 2)` for `a ≥ 3`
  (`exists_black_three`).
* **Counts.** Before time `2^m` there are at least `m + 1` black cells (`blackCount_pow_two`), so
  `Nat.log2 n + 1 ≤ blackCount n` for `n ≥ 1` (`log_two_succ_le_blackCount`) and
  `Nat.log2 n ≤ blackCount n` (`log_two_le_blackCount`). Before time `4^m` there are at least `m`
  white cells (`whiteCount_pow_four`), so `Nat.log2 n / 2 ≤ whiteCount n` (`log_le_whiteCount`);
  `Nat.log2 n / 2` is `⌊log₄ n⌋`. The catalog has no `Nat.log`, so the logarithms are core's
  `Nat.log2`.
* **Every configuration with a leftmost black cell.** The black bound holds for every column `i`
  of every configuration whose leftmost black cell is at `lo`, measured from the time the left edge
  passed the column: a black run of column `i` from time `a ≥ 1` (with `lo - i < a`) has length at
  most `a + i - lo` (`black_run_le_evol`).

`Rule30BlackRuns` excludes long black runs from an eventually periodic center column; the bounds
here hold at every time, with no periodicity assumed. They use the left-edge diagonals `D` of
`Rule30Diagonals` (`D 0 = D 1 = 1` from time 1) and the white-run lemmas of `Rule30BlackRuns`
(`first_black`, `front_moves`, `black_stays`). Numerically the longest runs are far shorter, about
logarithmic in the time: up to time 10^6 the longest white run is 19 and the longest black run 22.

**The argument.**

*Black runs.* While the center is black, `c (t + 1) = ¬ cell t (-1)`, since `rule l 1 r = ¬ l`.
Left-permutivity (`Rule30Jen.cell_left`) pushes the pattern outward: at the start `a` of a black
run of length `L`, the row reads `… 0 1 0 1` over the `L` cells ending at the center
(`black_triangle`). The row's two leftmost black cells, at `-a` and `-a + 1`, are adjacent
(`cell_left_edge`, `D_one`), so the alternating block cannot cover them: `L ≤ a`.

*White runs.* During a white run the first black cell right of the center, at column `ℓ + 1`, moves
left one column per step (`front_moves`); once in column `1` it stays there (`black_stays`). So
column `1` is white before time `a + ℓ` and black from then on, whether or not the front arrives
during the run (`col_one`). Left-permutivity then determines the whole row left of the center
inside the run's light cone through one closed form, `preRow k (a + ℓ - t)` (`pre_triangle`). At
time `a` the row reads `0^(ℓ+1) 1` and then alternates (`row_at_start`). The left-edge diagonals
are rigid: `D 2 = 0`, `D 3 = [t odd]` and `D 4 = 1` from time 2 (`D_two`, `D_three`, `D_four`). The
forced row cannot match `D 1`, …, `D 4` once the run reaches column `-(a - 4)`, which gives
`L ≤ a - 3`, and `L ≤ a - 1` for every `a ≥ 1`.

*Every configuration.* `black_triangle_evol` is `black_triangle` for any column of any evolution
(`Rule30FiniteConfigs.evol_left`), and `evol_left_edge_succ` says the two leftmost black cells
are adjacent at every time `t ≥ 1`.

**Not claimed.** Nothing sublinear: runs of length about `log a` are what the data show, and a
bound like `a / 2` would need a speed bound on the left edge of the chaotic region. This is a
partial result, not a solution of Problem 1.

Proved by Luis Perez Morales and Claude (Fable 5.1), in the Rule 30 Prize submission that
supersedes `R30-20261024-801153` (whose bounds were `L ≤ 3a - 2` for white runs and a black cell in
every `[a, 4a)`), and ported to core Lean.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30CenterRuns

open Ruliology.CellularAutomata
open Rule30Jen Rule30Prize Rule30Diagonals Rule30BlackRuns

/-- `ev k` is `true` iff `k` is even. -/
def ev (k : Nat) : Bool := decide (k % 2 = 0)

theorem ev_zero : ev 0 = true := rfl

theorem ev_succ (k : Nat) : ev (k + 1) = !ev k := by
  unfold ev
  by_cases h : k % 2 = 0
  · rw [decide_eq_true h, decide_eq_false (by omega)]; rfl
  · rw [decide_eq_false h, decide_eq_true (by omega)]; rfl

/-! ### Black runs -/

/-- Under a black run of the center from time `a` of length `L`, the cell `k` to the left at time
`t` is black iff `k` is even, as long as `t + k < a + L`. -/
theorem black_triangle (a L : Nat) (h : ∀ i, i < L → cell (a + i) 0 = true) :
    ∀ k t, a ≤ t → t + k < a + L → cell t (-(k : Int)) = ev k
  | 0, t, hat, htk => by
    have := h (t - a) (by omega)
    rw [show a + (t - a) = t by omega] at this
    simpa [ev] using this
  | k + 1, t, hat, htk => by
    have e : cell t (-((k + 1 : Nat) : Int)) =
        xor (cell (t + 1) (-(k : Int))) (cell t (-(k : Int)) || cell t (-(k : Int) + 1)) := by
      have := cell_left t (-(k : Int))
      rwa [show -(k : Int) - 1 = -((k + 1 : Nat) : Int) by omega] at this
    rw [e, black_triangle a L h k (t + 1) (by omega) (by omega),
      black_triangle a L h k t hat (by omega)]
    cases k with
    | zero => simp [ev]
    | succ k' =>
      have := black_triangle a L h k' t hat (by omega)
      rw [show -((k' + 1 : Nat) : Int) + 1 = -(k' : Int) by omega, this]
      simp only [ev_succ]
      cases ev k' <;> rfl

/-- **A black run of the center column starting at time `a ≥ 1` has length at most `a`.** Attained
at `a = 3`. -/
theorem black_run_le (a L : Nat) (ha : 1 ≤ a) (h : ∀ i, i < L → center (a + i) = true) :
    L ≤ a := by
  refine Classical.byContradiction fun hcon => ?_
  have hlt : a < L := Nat.lt_of_not_le hcon
  have h' : ∀ i, i < L → cell (a + i) 0 = true := h
  have h1 := black_triangle a L h' a a (Nat.le_refl a) (by omega)
  have h2 := black_triangle a L h' (a - 1) a (Nat.le_refl a) (by omega)
  rw [cell_left_edge] at h1
  have hD : D 1 a = true := by
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    exact D_one a'
  have e : cell a (-((a - 1 : Nat) : Int)) = D 1 a := cell_congr (by omega)
  rw [e, hD] at h2
  have := ev_succ (a - 1)
  rw [show a - 1 + 1 = a by omega, ← h1, ← h2] at this
  exact Bool.noConfusion this

/-- Every window `[a, 2a]`, `a ≥ 1`, holds a white cell of the center column. -/
theorem exists_white (a : Nat) (ha : 1 ≤ a) : ∃ t, a ≤ t ∧ t ≤ 2 * a ∧ center t = false := by
  refine Classical.byContradiction fun hcon => ?_
  have h : ∀ i, i < a + 1 → center (a + i) = true := by
    intro i hi
    cases hc : center (a + i)
    · exact absurd ⟨a + i, by omega, by omega, hc⟩ hcon
    · rfl
  have := black_run_le a (a + 1) ha h
  omega

/-! ### White runs: the row is forced already at the start of the run

During a white run starting at time `a`, let the first black cell right of the center be at column
`ℓ + 1`. Column `1` is white before time `a + ℓ` and black from then on (`col_one`), so
left-permutivity determines the row left of the center at every time `t` of the run, through a
closed form `preRow k (a + ℓ - t)` (`pre_triangle`). At time `a` the row reads `0^(ℓ+1) 1` and then
alternates; it cannot agree with the left-edge diagonals `D 1 = 1`, `D 2 = 0`, `D 3 = [a odd]`,
`D 4 = 1` if the run reaches column `-(a - 1)`. -/

/-- The cell `k` left of the center, `m` steps before column `1` turns black (`m = 0`: after). -/
def preRow (k m : Nat) : Bool := decide (m < k ∧ (k % 2 = 1 ∨ k = m + 1))

theorem preRow_step (k m : Nat) :
    preRow (k + 2) m = xor (preRow (k + 1) (m - 1)) (preRow (k + 1) m || preRow k m) := by
  unfold preRow
  by_cases h1 : m < k + 2 ∧ ((k + 2) % 2 = 1 ∨ k + 2 = m + 1) <;>
  by_cases h2 : m - 1 < k + 1 ∧ ((k + 1) % 2 = 1 ∨ k + 1 = m - 1 + 1) <;>
  by_cases h3 : m < k + 1 ∧ ((k + 1) % 2 = 1 ∨ k + 1 = m + 1) <;>
  by_cases h4 : m < k ∧ (k % 2 = 1 ∨ k = m + 1) <;>
  simp only [h1, h2, h3, h4, decide_false] <;>
  first | rfl | omega

/-- Column `1` during a white run of the center from time `a`: black exactly from time `a + ℓ`. -/
theorem col_one (a ℓ L : Nat) (h0 : ∀ i, i < L → cell (a + i) 0 = false)
    (hw : ∀ p : Nat, 1 ≤ p → p ≤ ℓ → cell a p = false) (hb : cell a ((ℓ + 1 : Nat) : Int) = true) :
    ∀ t, a ≤ t → t < a + L → cell t 1 = decide (a + ℓ ≤ t) := by
  intro t hat htL
  by_cases hlt : t < a + ℓ
  · obtain ⟨hw', _⟩ := front_moves a ℓ L h0 hw hb (t - a) (by omega) (by omega)
    have := hw' 1 (Nat.le_refl 1) (by omega)
    rw [show a + (t - a) = t by omega] at this
    have hd : decide (a + ℓ ≤ t) = false := decide_eq_false (by omega)
    rw [hd]
    exact this
  · obtain ⟨_, hb1⟩ := front_moves a ℓ L h0 hw hb ℓ (by omega) (Nat.le_refl ℓ)
    have hb1' : cell (a + ℓ) 1 = true := by
      have e : cell (a + ℓ) ((ℓ - ℓ + 1 : Nat) : Int) = cell (a + ℓ) 1 := cell_congr (by omega)
      rwa [e] at hb1
    have h0' : ∀ i, i < L - ℓ → cell (a + ℓ + i) 0 = false := fun i hi => by
      have := h0 (ℓ + i) (by omega)
      rwa [show a + (ℓ + i) = a + ℓ + i by omega] at this
    have := black_stays (a + ℓ) (L - ℓ) h0' hb1' (t - (a + ℓ)) (by omega)
    rw [show a + ℓ + (t - (a + ℓ)) = t by omega] at this
    have hd : decide (a + ℓ ≤ t) = true := decide_eq_true (by omega)
    rw [hd]
    exact this

/-- **The row during a white run, before and after column `1` turns black.** Under a white run of
the center from time `a` of length `L`, with column `1` black exactly from time `a + ℓ`, the cell
`k` to the left at time `t` is `preRow k (a + ℓ - t)`, as long as `t + k < a + L`. -/
theorem pre_triangle (a ℓ L : Nat) (h0 : ∀ i, i < L → cell (a + i) 0 = false)
    (h1 : ∀ t, a ≤ t → t < a + L → cell t 1 = decide (a + ℓ ≤ t)) :
    ∀ k t, a ≤ t → t + k < a + L → cell t (-(k : Int)) = preRow k (a + ℓ - t)
  | 0, t, hat, htk => by
    have := h0 (t - a) (by omega)
    rw [show a + (t - a) = t by omega] at this
    have hd : preRow 0 (a + ℓ - t) = false := decide_eq_false (by omega)
    rw [hd]
    simpa using this
  | k + 1, t, hat, htk => by
    have e : cell t (-((k + 1 : Nat) : Int)) =
        xor (cell (t + 1) (-(k : Int))) (cell t (-(k : Int)) || cell t (-(k : Int) + 1)) := by
      have := cell_left t (-(k : Int))
      rwa [show -(k : Int) - 1 = -((k + 1 : Nat) : Int) by omega] at this
    rw [e, pre_triangle a ℓ L h0 h1 k (t + 1) (by omega) (by omega),
      pre_triangle a ℓ L h0 h1 k t hat (by omega),
      show a + ℓ - (t + 1) = a + ℓ - t - 1 by omega]
    cases k with
    | zero =>
      have e1 : cell t (-((0 : Nat) : Int) + 1) = cell t 1 := cell_congr (by omega)
      rw [e1, h1 t hat (by omega)]
      have hz : ∀ m, preRow 0 m = false := fun m => decide_eq_false (by omega)
      rw [hz, hz]
      by_cases hc : a + ℓ ≤ t
      · have h1' : preRow (0 + 1) (a + ℓ - t) = true := decide_eq_true (by omega)
        rw [decide_eq_true hc, h1']; rfl
      · have h1' : preRow (0 + 1) (a + ℓ - t) = false := decide_eq_false (by omega)
        rw [decide_eq_false hc, h1']; rfl
    | succ k' =>
      have := pre_triangle a ℓ L h0 h1 k' t hat (by omega)
      rw [show -((k' + 1 : Nat) : Int) + 1 = -(k' : Int) by omega, this]
      exact (preRow_step k' (a + ℓ - t)).symm

/-- At the start `a ≥ 1` of a white run of length `L`, the row left of the center is `preRow k ℓ`
for some `ℓ` (the first black cell right of the center is at column `ℓ + 1`). -/
theorem row_at_start (a L : Nat) (ha : 1 ≤ a) (h : ∀ i, i < L → center (a + i) = false) :
    ∃ ℓ, ∀ k, k < L → cell a (-(k : Int)) = preRow k ℓ := by
  have h' : ∀ i, i < L → cell (a + i) 0 = false := h
  obtain ⟨ℓ, hw, hb⟩ := first_black a ha
  refine ⟨ℓ, fun k hk => ?_⟩
  have := pre_triangle a ℓ L h' (col_one a ℓ L h' hw hb) k a (Nat.le_refl a) (by omega)
  rwa [show a + ℓ - a = ℓ by omega] at this

/-! #### The left-edge diagonals `D 2`, `D 3`, `D 4` -/

theorem D_two (t : Nat) : D 2 (t + 2) = false := by
  have e : D 2 (t + 2) = xor (D 0 (t + 1)) (D 1 (t + 1) || D 2 (t + 1)) := D_step 0 (t + 1)
  rw [e, D_zero, D_one]
  rfl

theorem D_three : ∀ t, D 3 (t + 2) = decide (t % 2 = 1)
  | 0 => by decide
  | t + 1 => by
    have e : D 3 (t + 1 + 2) = xor (D 1 (t + 2)) (D 2 (t + 2) || D 3 (t + 2)) := D_step 1 (t + 2)
    rw [e, show t + 2 = (t + 1) + 1 by omega, D_one, show t + 1 + 1 = t + 2 by omega, D_two,
      D_three t]
    rcases Nat.mod_two_eq_zero_or_one t with h | h
    · rw [decide_eq_false (by omega), decide_eq_true (by omega)]; rfl
    · rw [decide_eq_true (by omega), decide_eq_false (by omega)]; rfl

theorem D_four : ∀ t, D 4 (t + 2) = true
  | 0 => by decide
  | t + 1 => by
    have e : D 4 (t + 1 + 2) = xor (D 2 (t + 2)) (D 3 (t + 2) || D 4 (t + 2)) := D_step 2 (t + 2)
    rw [e, D_two, D_four t]
    cases D 3 (t + 2) <;> rfl

/-- The cell `k` left of the center at time `a` is the left diagonal `D (a - k) a`. -/
theorem cell_neg_eq_D (a k : Nat) (hk : k ≤ a) : cell a (-(k : Int)) = D (a - k) a :=
  cell_congr (by omega)

theorem preRow_eq_true {k m : Nat} (h : preRow k m = true) : m < k ∧ (k % 2 = 1 ∨ k = m + 1) :=
  of_decide_eq_true h

theorem preRow_eq_false {k m : Nat} (h : preRow k m = false) :
    ¬ (m < k ∧ (k % 2 = 1 ∨ k = m + 1)) :=
  of_decide_eq_false h

/-- **A white run of the center column starting at time `a ≥ 1` has length at most `a - 1`.**
Attained only at `a = 2`. -/
theorem white_run_le' (a L : Nat) (ha : 1 ≤ a) (h : ∀ i, i < L → center (a + i) = false) :
    L ≤ a - 1 := by
  refine Classical.byContradiction fun hcon => ?_
  rcases (show a = 1 ∨ a = 2 ∨ 3 ≤ a by omega) with rfl | rfl | ha3
  · have := h 0 (by omega)
    exact Bool.noConfusion ((show center (1 + 0) = true by decide).symm.trans this)
  · have := h 1 (by omega)
    exact Bool.noConfusion ((show center (2 + 1) = true by decide).symm.trans this)
  obtain ⟨ℓ, hrow⟩ := row_at_start a L ha h
  have k1 := hrow (a - 1) (by omega)
  have k2 := hrow (a - 2) (by omega)
  have k3 := hrow (a - 3) (by omega)
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 3 := ⟨a - 3, by omega⟩
  rw [cell_neg_eq_D _ _ (by omega), show b + 3 - (b + 3 - 1) = 1 by omega,
    show b + 3 = (b + 2) + 1 by omega, D_one] at k1
  rw [cell_neg_eq_D _ _ (by omega), show b + 3 - (b + 3 - 2) = 2 by omega,
    show b + 3 = (b + 1) + 2 by omega, D_two] at k2
  rw [cell_neg_eq_D _ _ (by omega), show b + 3 - (b + 3 - 3) = 3 by omega,
    show b + 3 = (b + 1) + 2 by omega, D_three] at k3
  have p1 := preRow_eq_true k1.symm
  have p2 := preRow_eq_false k2.symm
  rcases Nat.mod_two_eq_zero_or_one (b + 1) with hpar | hpar
  · -- `a` even: `D 3 = 0`, and `D 4 = 1` rules out `ℓ = a - 2`
    rw [decide_eq_false (by omega)] at k3
    have p3 := preRow_eq_false k3.symm
    rcases Nat.eq_zero_or_pos b with hb0 | hb0
    · omega
    have k4 := hrow (b + 3 - 4) (by omega)
    obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
    rw [cell_neg_eq_D _ _ (by omega), show c + 1 + 3 - (c + 1 + 3 - 4) = 4 by omega,
      show c + 1 + 3 = (c + 2) + 2 by omega, D_four] at k4
    have p4 := preRow_eq_true k4.symm
    omega
  · -- `a` odd: `D 3 = 1`
    rw [decide_eq_true (by omega)] at k3
    have p3 := preRow_eq_true k3.symm
    omega

/-- **For every `a ≥ 3`, a white run of the center column starting at time `a` has length at most
`a - 3`.** Only the left-edge diagonals `D 3 = [a odd]` and `D 4 = 1` are used. Not attained up to
time 3000; the closest case is `a = 6` (`c 6 = c 7 = 0`, `L = 2 = a - 4`). -/
theorem white_run_le_three (a L : Nat) (ha : 3 ≤ a) (h : ∀ i, i < L → center (a + i) = false) :
    L ≤ a - 3 := by
  refine Classical.byContradiction fun hcon => ?_
  rcases (show a = 3 ∨ 4 ≤ a by omega) with rfl | ha4
  · have := h 0 (by omega)
    exact Bool.noConfusion ((show center (3 + 0) = true by decide).symm.trans this)
  obtain ⟨ℓ, hrow⟩ := row_at_start a L (by omega) h
  have k3 := hrow (a - 3) (by omega)
  have k4 := hrow (a - 4) (by omega)
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 4 := ⟨a - 4, by omega⟩
  rw [cell_neg_eq_D _ _ (by omega), show b + 4 - (b + 4 - 3) = 3 by omega,
    show b + 4 = (b + 2) + 2 by omega, D_three] at k3
  rw [cell_neg_eq_D _ _ (by omega), show b + 4 - (b + 4 - 4) = 4 by omega,
    show b + 4 = (b + 2) + 2 by omega, D_four] at k4
  have p4 := preRow_eq_true k4.symm
  rcases Nat.mod_two_eq_zero_or_one (b + 2) with hpar | hpar
  · -- `a` even: `D 3 = 0` forces `ℓ ≥ a - 3`, while `D 4 = 1` forces `ℓ = a - 5`
    rw [decide_eq_false (by omega)] at k3
    have p3 := preRow_eq_false k3.symm
    omega
  · -- `a` odd: `D 3 = 1` forces `ℓ = a - 4`, while `D 4 = 1` forces `ℓ < a - 4`
    rw [decide_eq_true (by omega)] at k3
    have p3 := preRow_eq_true k3.symm
    omega

/-! ### Both colors recur geometrically -/

/-- Every window `[a, 2a)`, `a ≥ 1`, holds a black cell of the center column. -/
theorem exists_black' (a : Nat) (ha : 1 ≤ a) : ∃ t, a ≤ t ∧ t < 2 * a ∧ center t = true := by
  refine Classical.byContradiction fun hcon => ?_
  have h : ∀ i, i < a → center (a + i) = false := by
    intro i hi
    cases hc : center (a + i)
    · rfl
    · exact absurd ⟨a + i, by omega, by omega, hc⟩ hcon
  have := white_run_le' a a ha h
  omega

/-- Every window `[a, 2a - 2)`, `a ≥ 3`, holds a black cell of the center column. -/
theorem exists_black_three (a : Nat) (ha : 3 ≤ a) :
    ∃ t, a ≤ t ∧ t < 2 * a - 2 ∧ center t = true := by
  refine Classical.byContradiction fun hcon => ?_
  have h : ∀ i, i < a - 2 → center (a + i) = false := by
    intro i hi
    cases hc : center (a + i)
    · rfl
    · exact absurd ⟨a + i, by omega, by omega, hc⟩ hcon
  have := white_run_le_three a (a - 2) ha h
  omega

/-! ### Counts -/

/-- The number of white cells among the first `n` cells of the center column
(`Rule30Prize.blackCount` counts the black ones). -/
def whiteCount (n : Nat) : Nat := ((List.range n).filter fun t => !center t).length

theorem blackCount_succ (n : Nat) :
    blackCount (n + 1) = blackCount n + (if center n then 1 else 0) := by
  unfold blackCount
  rw [List.range_succ, List.filter_append, List.length_append]
  simp only [List.filter_cons, List.filter_nil]
  cases center n <;> simp

theorem whiteCount_succ (n : Nat) :
    whiteCount (n + 1) = whiteCount n + (if center n then 0 else 1) := by
  unfold whiteCount
  rw [List.range_succ, List.filter_append, List.length_append]
  simp only [List.filter_cons, List.filter_nil]
  cases center n <;> simp

theorem blackCount_mono : ∀ m n, m ≤ n → blackCount m ≤ blackCount n
  | m, 0, h => by rw [Nat.le_zero.mp h]; exact Nat.le_refl _
  | m, n + 1, h => by
    rcases Nat.lt_or_eq_of_le h with h | h
    · have := blackCount_mono m n (by omega)
      rw [blackCount_succ]; omega
    · rw [h]; exact Nat.le_refl _

theorem whiteCount_mono : ∀ m n, m ≤ n → whiteCount m ≤ whiteCount n
  | m, 0, h => by rw [Nat.le_zero.mp h]; exact Nat.le_refl _
  | m, n + 1, h => by
    rcases Nat.lt_or_eq_of_le h with h | h
    · have := whiteCount_mono m n (by omega)
      rw [whiteCount_succ]; omega
    · rw [h]; exact Nat.le_refl _

theorem blackCount_lt {a b t : Nat} (hat : a ≤ t) (htb : t < b) (ht : center t = true) :
    blackCount a < blackCount b := by
  have h1 := blackCount_mono a t hat
  have h2 := blackCount_mono (t + 1) b htb
  rw [blackCount_succ, ht] at h2
  simp at h2
  omega

theorem whiteCount_lt {a b t : Nat} (hat : a ≤ t) (htb : t < b) (ht : center t = false) :
    whiteCount a < whiteCount b := by
  have h1 := whiteCount_mono a t hat
  have h2 := whiteCount_mono (t + 1) b htb
  rw [whiteCount_succ, ht] at h2
  simp at h2
  omega

/-- **Before time `2^m` the center column has at least `m + 1` black cells** (counting
`c 0 = 1`). -/
theorem blackCount_pow_two : ∀ m, m + 1 ≤ blackCount (2 ^ m)
  | 0 => by decide
  | m + 1 => by
    obtain ⟨t, h1, h2, h3⟩ := exists_black' (2 ^ m) Nat.one_le_two_pow
    have := blackCount_lt (b := 2 ^ (m + 1)) h1 (by rw [Nat.pow_succ]; omega) h3
    have ih := blackCount_pow_two m
    omega

/-- `log₂ n + 1 ≤ blackCount n` for `n ≥ 1`, with core's `Nat.log2`. -/
theorem log_two_succ_le_blackCount (n : Nat) (hn : 1 ≤ n) : Nat.log2 n + 1 ≤ blackCount n := by
  have h1 := blackCount_pow_two (Nat.log2 n)
  have h2 := blackCount_mono _ _ (Nat.log2_self_le (by omega : n ≠ 0))
  omega

/-- `log₂ n ≤ blackCount n`: among the first `n` cells of the center column at least `log₂ n`
are black. -/
theorem log_two_le_blackCount (n : Nat) : Nat.log2 n ≤ blackCount n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [Nat.log2_zero]
  · have := log_two_succ_le_blackCount n hn
    omega

/-- **Before time `4^m` the center column has at least `m` white cells.** -/
theorem whiteCount_pow_four : ∀ m, m ≤ whiteCount (4 ^ m)
  | 0 => Nat.zero_le _
  | m + 1 => by
    have hp : 1 ≤ 4 ^ m := Nat.one_le_pow _ _ (by decide)
    obtain ⟨t, h1, h2, h3⟩ := exists_white (4 ^ m) hp
    have := whiteCount_lt (b := 4 ^ (m + 1)) h1 (by rw [Nat.pow_succ]; omega) h3
    have ih := whiteCount_pow_four m
    omega

/-- `⌊log₄ n⌋ ≤ whiteCount n`, where `⌊log₄ n⌋ = Nat.log2 n / 2`. -/
theorem log_le_whiteCount (n : Nat) : Nat.log2 n / 2 ≤ whiteCount n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [Nat.log2_zero]
  · have h1 := whiteCount_pow_four (Nat.log2 n / 2)
    have h4 : 4 ^ (Nat.log2 n / 2) ≤ n := by
      have e : 4 ^ (Nat.log2 n / 2) = 2 ^ (2 * (Nat.log2 n / 2)) := by
        rw [Nat.pow_mul]
      rw [e]
      exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega))
        (Nat.log2_self_le (by omega : n ≠ 0))
    have h2 := whiteCount_mono _ _ h4
    omega

/-! ### The black bound for every configuration with a leftmost black cell -/

section General
open Rule30Realization Rule30FiniteConfigs

variable {x : Int → Bool} {lo : Int} (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)

/-- `black_triangle` for column `i` of any evolution. -/
theorem black_triangle_evol (x : Int → Bool) (i : Int) (a L : Nat)
    (h : ∀ j, j < L → evol x (a + j) i = true) :
    ∀ k t, a ≤ t → t + k < a + L → evol x t (i - k) = ev k
  | 0, t, hat, htk => by
    have := h (t - a) (by omega)
    rw [show a + (t - a) = t by omega] at this
    simpa [ev] using this
  | k + 1, t, hat, htk => by
    have e : evol x t (i - ((k + 1 : Nat) : Int)) =
        xor (evol x (t + 1) (i - k)) (evol x t (i - k) || evol x t (i - k + 1)) := by
      have := evol_left x t (i - k)
      rwa [show i - (k : Int) - 1 = i - ((k + 1 : Nat) : Int) by omega] at this
    rw [e, black_triangle_evol x i a L h k (t + 1) (by omega) (by omega),
      black_triangle_evol x i a L h k t hat (by omega)]
    cases k with
    | zero =>
      have e1 : evol x t (i - ((0 : Nat) : Int) + 1) = evol x t (i + 1) := by
        show evol x t _ = evol x t _; congr 1; omega
      rw [e1]
      simp [ev]
    | succ k' =>
      have := black_triangle_evol x i a L h k' t hat (by omega)
      rw [show i - ((k' + 1 : Nat) : Int) + 1 = i - (k' : Int) by omega, this]
      simp only [ev_succ]
      cases ev k' <;> rfl

include hlo hzero in
/-- At every time `t ≥ 1` the two leftmost black cells, at `lo - t` and `lo - t + 1`, are adjacent. -/
theorem evol_left_edge_succ (t : Nat) : evol x (t + 1) (lo - (t + 1 : Nat) + 1) = true := by
  show rule (evol x t (lo - ((t + 1 : Nat) : Int) + 1 - 1)) (evol x t (lo - ((t + 1 : Nat) : Int) + 1))
    (evol x t (lo - ((t + 1 : Nat) : Int) + 1 + 1)) = true
  rw [evol_eq_false_of_lt hzero t _ (by omega),
    show lo - ((t + 1 : Nat) : Int) + 1 = lo - (t : Int) by omega, evol_left_edge hlo hzero t]
  rfl

include hlo hzero in
/-- **In any configuration with a leftmost black cell `lo`, a black run of column `i` starting at
time `a ≥ 1` has length at most `a + i - lo`**, the time since the left edge passed the column
(which it must have, `lo - i < a`). -/
theorem black_run_le_evol (i : Int) (a L : Nat) (ha : 1 ≤ a) (hd : lo - i < a)
    (h : ∀ j, j < L → evol x (a + j) i = true) : (L : Int) ≤ a + i - lo := by
  refine Classical.byContradiction fun hcon => ?_
  have hlt : (a : Int) + i - lo < L := by omega
  -- `k₁ = i - (lo - a)` and `k₀ = k₁ - 1` are both below `L`
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : Nat, (k₀ : Int) = i - (lo - a) - 1 := ⟨(i - (lo - a) - 1).toNat, by omega⟩
  have h1 := black_triangle_evol x i a L h (k₀ + 1) a (Nat.le_refl a) (by omega)
  have h2 := black_triangle_evol x i a L h k₀ a (Nat.le_refl a) (by omega)
  have e1 : evol x a (i - ((k₀ + 1 : Nat) : Int)) = evol x a (lo - a) := by congr 1; omega
  have e2 : evol x a (i - (k₀ : Int)) = evol x a (lo - a + 1) := by congr 1; omega
  rw [e1, evol_left_edge hlo hzero a] at h1
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  rw [e2, evol_left_edge_succ hlo hzero a'] at h2
  rw [ev_succ, ← h2] at h1
  exact Bool.noConfusion h1

end General

end Ruliology.CellularAutomata.Rule30CenterRuns
