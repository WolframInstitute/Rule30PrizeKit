module

public import Ruliology.CellularAutomata.Rule30Realization
public import Ruliology.CellularAutomata.Rule30ZeroBoundary

/-!
# Rule 210 beside the period-2 clock: the one-sided question is false, the two-sided one is true

Rule 210 is `left xor (!center && right)`, the kit's `Rule30Realization.g210`. It shares left-permutivity, the moving
edge and Jen's theorem with rule 30, which is why `Rule30Realization.barrier` shows that those cannot decide
Problem 1 alone. This module asks rule 210 the period-2 question in both of the kit's forms, and the answers differ.

**The one-sided form is false** (`not_Q01_210`). `zrow210 L t k` is rule 210's left half with the period-2 clock at
the wall, in the encoding of `Rule30ZeroBoundary`: depth `k` is position `-k`, and the wall is black at the even steps.
`InX210` and `Q01_210` are the kit's `InX` and `Q01` with rule 210 in place of rule 30. The empty start keeps the
clock for ever (`white_start_inX`), because every black cell `(t, k)` of its run has `t + k` even
(`white_start_parity`).
* `parity_invariant`, `no_adjacent`, `linear`: for every start consistent with the clock, every black cell has
  `t + k` even. So no two adjacent cells are both black, the gate `!center && right` is `right`, and the left half
  evolves as rule 90's does.

**The two-sided form is true** (`no_finite_clock`). `run210 x0` is rule 210 from any `x0 : Int → Bool`, with
`run210_seed` for the kit's single seed. No finite configuration (`Finite210`: white outside `[-R, R]`) has a center
column reading the clock `0101…`.
* `no_finite_eventually_alternating`: none has an eventually alternating center column, in either phase.
* `seed_not_eventually_alternating`: neither does the seed, in the kit's `run g210`.

**Method.**
* *Parity* (`parity_of_even_white`, `parity_left_of_clock`). Under the clock the whole left half is parity-sparse,
  whatever the right half.
* *The background* (`clock_bg`). Every admissible left row `L` has a parity-sparse clock realization `bg L`. It is
  built sideways from the clock: the left half by the evolution with the clock at the wall, the right columns by
  rule 90's right-permutivity.
* *The freshman's dream* (`run90_pow2`, `no_finite_clock90`). Rule 90 is linear, so at time `2^n` it is the sum of
  the two shifts by `2^n`. For a start supported on `[-R, R]`, choose `2^n > R + 1`. Rule 90 is then white at the
  center at time `2^n + 1`, when the clock is black. This applies to rule 210 on the parity-sparse background.
* *The deviation* (`Dev`). Take a finite clock orbit, and the first cell `e ≥ 1` where it differs from the
  background of its own left row.
  * If `e` is odd, the two orbits differ on diagonal `e` for ever, so also at its clock time (`Dev.odd_impossible`).
  * If `e` is even, a gate left of the deviation fires at a time `τ ≤ e - 1` (`Dev.tau`). A clearing front then
    carries the deviation right, pair by pair (`marker`, `propagate`, `front`). At the first initially black
    background gate `w`, the clock fails at time `e + 2w + 1` (`Dev.even_impossible`).
  * If every background gate beyond `e` is initially white, the background is itself finite and the freshman's dream applies.
* *Phase* (`run210_add`, `finite_run210`). A clock from time `T` in either phase is a clock from time `0` for the
  configuration at a later time, which is still finite.

Nothing here is about rule 30's center column. Beside the kit: `Rule30Realization` has the single seed's
`run g210` (`run210_eq`, `center210`). This module is about the period-2 question itself, for every finite
configuration.

**Credit.** Left-permutivity is used as in Jen's theorem (E. Jen, J. Stat. Phys. 43, 1986). The module joins the
Lean-verified submissions `R30-20261022-920c1b` (the one-sided form) and `R30-20261023-1bf4dc` (the two-sided form).
Core Lean has no `Nat.find` and no `|·|`. So `Dev.tau` is the least witness from `exists_least`, and `Finite210` reads
`R < i.natAbs` for `(R : Int) < |i|`.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Rule210Clock

open Rule30ZeroBoundary (FinSupp)
open Rule30Realization (run g210)

/-! ## The one-sided question, in the kit's zero-boundary encoding -/
/-- Rule 210's left half with the period-2 clock at the wall: depth `k` is position `-k`; depth `0` is the wall,
black at the even steps; the start `L` is read at depths `k ≥ 1`. The step at depth `k + 1` is rule 210 read
leftward: `left xor (!center && right)` with the left neighbour at depth `k + 2` and the right one at depth `k`. -/
def zrow210 (L : Nat → Bool) : Nat → Nat → Bool
  | 0, 0 => true
  | 0, k + 1 => L (k + 1)
  | t + 1, 0 => decide ((t + 1) % 2 = 0)
  | t + 1, k + 1 => xor (zrow210 L t (k + 2)) (!zrow210 L t (k + 1) && zrow210 L t k)

theorem zrow210_wall (L : Nat → Bool) : ∀ t, zrow210 L t 0 = decide (t % 2 = 0)
  | 0 => rfl
  | _ + 1 => rfl

theorem zrow210_start (L : Nat → Bool) (k : Nat) : zrow210 L 0 (k + 1) = L (k + 1) := rfl

theorem zrow210_succ (L : Nat → Bool) (t k : Nat) :
    zrow210 L (t + 1) (k + 1) = xor (zrow210 L t (k + 2)) (!zrow210 L t (k + 1) && zrow210 L t k) := rfl

/-- Left permutivity: the cell at depth `k + 2` from the next cell at depth `k + 1` and the cells at depths
`k + 1` and `k`. -/
theorem zrow210_inv (L : Nat → Bool) (t k : Nat) :
    zrow210 L t (k + 2) = xor (zrow210 L (t + 1) (k + 1)) (!zrow210 L t (k + 1) && zrow210 L t k) := by
  rw [zrow210_succ]
  cases zrow210 L t (k + 2) <;> cases (!zrow210 L t (k + 1) && zrow210 L t k) <;> rfl

/-- Starts consistent with the clock: column `-1` is white at every even step. (Under the clock, black at the even
steps at the wall, rule 210 at position `0` reads `clock (t + 1) = xor (col (-1) t) (!clock t && col 1 t)`: at even
`t` this forces column `-1` white, at odd `t` it determines column `1`.) -/
def InX210 (L : Nat → Bool) : Prop := ∀ s, zrow210 L (2 * s) 1 = false

/-- The kit's `Q01` for rule 210: no finitely supported start keeps the clock. -/
def Q01_210 : Prop := ∀ L : Nat → Bool, FinSupp L → ¬ InX210 L

/-- From a white start every black cell `(t, k)` has `t + k` even. -/
theorem white_start_parity (L : Nat → Bool) (hL : ∀ k, L k = false) :
    ∀ t k, zrow210 L t k = true → (t + k) % 2 = 0 := by
  intro t
  induction t with
  | zero =>
    intro k h
    rcases k with _ | k
    · rfl
    · rw [zrow210_start, hL] at h; exact absurd h (by decide)
  | succ t ih =>
    intro k h
    rcases k with _ | k
    · rw [zrow210_wall] at h; simp only [decide_eq_true_eq] at h; omega
    · rw [zrow210_succ] at h
      by_cases h1 : zrow210 L t (k + 2) = true
      · have := ih (k + 2) h1; omega
      · have h1' : zrow210 L t (k + 2) = false := by simpa using h1
        rw [h1'] at h
        have hk : zrow210 L t k = true := by
          revert h; cases zrow210 L t (k + 1) <;> cases zrow210 L t k <;> simp
        have := ih k hk; omega

/-- The white start keeps the clock for ever. -/
theorem white_start_inX (L : Nat → Bool) (hL : ∀ k, L k = false) : InX210 L := by
  intro s
  refine Classical.byContradiction fun hne => ?_
  have h : zrow210 L (2 * s) 1 = true := by simpa using hne
  have := white_start_parity L hL (2 * s) 1 h
  omega

/-- **The one-sided period-2 statement is false for rule 210**: the empty start is finitely supported and keeps the
clock. -/
theorem not_Q01_210 : ¬ Q01_210 :=
  fun hQ => hQ (fun _ => false) ⟨0, fun _ _ => rfl⟩ (white_start_inX _ (fun _ => rfl))

/-- **The parity invariant.** For every start consistent with the clock, every black cell `(t, k)` has `t + k`
even. By induction on the depth, with left permutivity. -/
theorem parity_invariant (L : Nat → Bool) (hX : InX210 L) :
    ∀ k t, zrow210 L t k = true → (t + k) % 2 = 0 := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro t h
    rcases k with _ | _ | k
    · rw [zrow210_wall] at h; simp only [decide_eq_true_eq] at h; omega
    · rcases Nat.mod_two_eq_zero_or_one t with hs | hs
      · exfalso
        have := hX (t / 2)
        rw [show 2 * (t / 2) = t by omega, h] at this
        exact absurd this (by decide)
      · omega
    · rw [zrow210_inv] at h
      by_cases h1 : zrow210 L (t + 1) (k + 1) = true
      · have := ih (k + 1) (by omega) (t + 1) h1; omega
      · have h1' : zrow210 L (t + 1) (k + 1) = false := by simpa using h1
        rw [h1'] at h
        have hk : zrow210 L t k = true := by
          revert h; cases zrow210 L t (k + 1) <;> cases zrow210 L t k <;> simp
        have := ih k (by omega) t hk; omega

/-- **Beside the clock, rule 210's left half is rule 90's.** Two horizontally adjacent cells are never both black,
so the gate `!center && right` is `right`. -/
theorem linear (L : Nat → Bool) (hX : InX210 L) (t k : Nat) :
    zrow210 L (t + 1) (k + 1) = xor (zrow210 L t (k + 2)) (zrow210 L t k) := by
  rw [zrow210_succ]
  have : (!zrow210 L t (k + 1) && zrow210 L t k) = zrow210 L t k := by
    by_cases hk : zrow210 L t k = true
    · have hk1 : zrow210 L t (k + 1) = false := by
        refine Classical.byContradiction fun hne => ?_
        have h1 := parity_invariant L hX (k + 1) t (by simpa using hne)
        have h0 := parity_invariant L hX k t hk
        omega
      rw [hk, hk1]; rfl
    · have hk' : zrow210 L t k = false := by simpa using hk
      rw [hk']; simp
  rw [this]

/-- No two horizontally adjacent black cells, for every start consistent with the clock. -/
theorem no_adjacent (L : Nat → Bool) (hX : InX210 L) (t k : Nat) :
    ¬ (zrow210 L t k = true ∧ zrow210 L t (k + 1) = true) := by
  rintro ⟨h0, h1⟩
  have := parity_invariant L hX k t h0
  have := parity_invariant L hX (k + 1) t h1
  omega


/-! ## The two-sided statement: no finite configuration keeps the clock -/
/-! ## Rule 210 on a general configuration -/

/-- Rule 210, `left xor (!center && right)`, from any configuration. The kit's `run g210` is the single seed. -/
def run210 (x0 : Int → Bool) : Nat → Int → Bool
  | 0, i => x0 i
  | t + 1, i => xor (run210 x0 t (i - 1)) (!(run210 x0 t i) && run210 x0 t (i + 1))

theorem run210_succ (x0 : Int → Bool) (t : Nat) (i : Int) :
    run210 x0 (t + 1) i = xor (run210 x0 t (i - 1)) (!(run210 x0 t i) && run210 x0 t (i + 1)) := rfl

/-- The kit's single-seed `run g210` is `run210` from the seed. -/
theorem run210_seed : ∀ t p, run210 (fun p => decide (p = 0)) t p = run g210 t p
  | 0, p => rfl
  | t + 1, p => by
    rw [run210_succ]
    show _ = xor (run g210 t (p - 1)) (g210 (run g210 t p) (run g210 t (p + 1)))
    rw [run210_seed t (p - 1), run210_seed t p, run210_seed t (p + 1)]; rfl

/-- The center column reads the clock, white at even times. -/
def Clock210 (x0 : Int → Bool) : Prop := ∀ t : Nat, run210 x0 t 0 = decide (t % 2 = 1)

/-- The left diagonal `c`: the cell `c - s` at time `s`. -/
def Diag210 (x0 : Int → Bool) (c : Int) (s : Nat) : Bool := run210 x0 s (c - (s : Int))

def FinLeft210 (x0 : Int → Bool) : Prop := ∃ R : Nat, ∀ i : Int, i < -(R : Int) → x0 i = false

/-- Finite: white outside `[-R, R]`. (`R < i.natAbs` is `(R : Int) < |i|`; core Lean has no `|·|`.) -/
def Finite210 (x0 : Int → Bool) : Prop := ∃ R : Nat, ∀ i : Int, R < i.natAbs → x0 i = false

/-- **D1.** The diagonal recursion. -/
theorem diag_succ (x0 : Int → Bool) (c : Int) (s : Nat) :
    Diag210 x0 c (s + 1) = xor (Diag210 x0 (c - 2) s) (!(Diag210 x0 (c - 1) s) && Diag210 x0 c s) := by
  unfold Diag210
  rw [run210_succ]
  have e1 : c - ((s + 1 : Nat) : Int) - 1 = (c - 2) - (s : Int) := by omega
  have e2 : c - ((s + 1 : Nat) : Int) = (c - 1) - (s : Int) := by omega
  have e3 : c - ((s + 1 : Nat) : Int) + 1 = c - (s : Int) := by omega
  rw [e1, e3, e2]

theorem diag_zero (x0 : Int → Bool) (c : Int) : Diag210 x0 c 0 = x0 c := by simp [Diag210, run210]

/-- **D2.** Left locality: agreement of the initial rows left of `e` gives agreement of every diagonal left of `e`. -/
theorem diag_local (x0 y0 : Int → Bool) (e : Int) (h : ∀ i, i < e → x0 i = y0 i) :
    ∀ s, ∀ c, c < e → Diag210 x0 c s = Diag210 y0 c s := by
  intro s
  induction s with
  | zero => intro c hc; rw [diag_zero, diag_zero]; exact h c hc
  | succ s ih =>
    intro c hc
    rw [diag_succ, diag_succ, ih (c - 2) (by omega), ih (c - 1) (by omega), ih c hc]

/-- The light cone: the cell `i` at time `t` depends on the initial sites in `[i - t, i + t]`. -/
theorem run210_cone (x0 y0 : Int → Bool) : ∀ t : Nat, ∀ i : Int,
    (∀ j, i - t ≤ j → j ≤ i + t → x0 j = y0 j) → run210 x0 t i = run210 y0 t i := by
  intro t
  induction t with
  | zero => intro i h; simpa [run210] using h i (by simp) (by simp)
  | succ t ih =>
    intro i h
    rw [run210_succ, run210_succ,
      ih (i - 1) (fun j h1 h2 => h j (by push_cast at h1 ⊢; omega) (by push_cast at h2 ⊢; omega)),
      ih i (fun j h1 h2 => h j (by push_cast at h1 ⊢; omega) (by push_cast at h2 ⊢; omega)),
      ih (i + 1) (fun j h1 h2 => h j (by push_cast at h1 ⊢; omega) (by push_cast at h2 ⊢; omega))]

/-! ## Parity: the forced left half -/

/-- **P1.** From a configuration white on the even sites, every black cell `(t, i)` has `t + i` odd. -/
theorem parity_of_even_white (x0 : Int → Bool) (h : ∀ i, i % 2 = 0 → x0 i = false) :
    ∀ t : Nat, ∀ i : Int, run210 x0 t i = true → ((t : Int) + i) % 2 = 1 := by
  intro t
  induction t with
  | zero =>
    intro i hi
    refine Classical.byContradiction fun hne => ?_
    have : i % 2 = 0 := by omega
    have := h i this
    simp [run210] at hi
    rw [hi] at this; exact absurd this (by decide)
  | succ t ih =>
    intro i hi
    rw [run210_succ] at hi
    by_cases hl : run210 x0 t (i - 1) = true
    · have := ih (i - 1) hl; push_cast; omega
    · have hl' : run210 x0 t (i - 1) = false := by simpa using hl
      rw [hl'] at hi
      have hr : run210 x0 t (i + 1) = true := by
        revert hi; cases run210 x0 t i <;> cases run210 x0 t (i + 1) <;> simp
      have := ih (i + 1) hr; push_cast; omega

/-- **P1′.** On such an orbit the gate is rule 90's: `left xor right`. -/
theorem rule90_of_even_white (x0 : Int → Bool) (h : ∀ i, i % 2 = 0 → x0 i = false) (t : Nat) (i : Int) :
    run210 x0 (t + 1) i = xor (run210 x0 t (i - 1)) (run210 x0 t (i + 1)) := by
  rw [run210_succ]
  have : (!(run210 x0 t i) && run210 x0 t (i + 1)) = run210 x0 t (i + 1) := by
    by_cases hr : run210 x0 t (i + 1) = true
    · have hc : run210 x0 t i = false := by
        refine Classical.byContradiction fun hne => ?_
        have h1 := parity_of_even_white x0 h t i (by simpa using hne)
        have h2 := parity_of_even_white x0 h t (i + 1) hr
        omega
      rw [hc, hr]; rfl
    · have hr' : run210 x0 t (i + 1) = false := by simpa using hr
      rw [hr']; simp
  rw [this]

/-- **P2.** Under the clock, every black cell `(t, i)` with `i ≤ 0` has `t + i` odd: the left half is parity-sparse,
whatever the right half. By strong induction on the depth `-i`, with left-permutivity. -/
theorem parity_left_of_clock (x0 : Int → Bool) (hc : Clock210 x0) :
    ∀ k : Nat, ∀ t : Nat, run210 x0 t (-(k : Int)) = true → ((t : Int) - k) % 2 = 1 := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro t h
    rcases k with _ | _ | k
    · -- depth 0: the clock
      have := hc t
      simp only [Int.natCast_zero, Int.neg_zero] at h
      rw [this] at h
      simp only [decide_eq_true_eq] at h
      omega
    · -- depth 1: at odd `t` the clock is black and the next clock bit white forces column `-1` white
      refine Classical.byContradiction fun hpar => ?_
      have hodd : t % 2 = 1 := by omega
      have h0 : run210 x0 t 0 = true := by rw [hc t]; simp [hodd]
      have h1 : run210 x0 (t + 1) 0 = false := by rw [hc (t + 1)]; simp; omega
      rw [run210_succ, h0] at h1
      simp only [Int.zero_sub, Int.zero_add] at h1
      rw [show (-((0 + 1 : Nat) : Int)) = -1 by omega] at h
      rw [h] at h1
      simp at h1
    · -- depth k + 2: left-permutivity at column -(k+1)
      have hinv := run210_succ x0 t (-((k + 1 : Nat) : Int))
      -- hinv : run (t+1) (-(k+1)) = xor (run t (-(k+1) - 1)) (!(run t (-(k+1))) && run t (-(k+1) + 1))
      have e1 : (-((k + 1 : Nat) : Int)) - 1 = -((k + 1 + 1 : Nat) : Int) := by omega
      have e2 : (-((k + 1 : Nat) : Int)) + 1 = -((k : Nat) : Int) := by omega
      rw [e1, e2] at hinv
      rw [h] at hinv
      -- hinv : run (t+1) (-(k+1)) = xor true (!(run t (-(k+1))) && run t (-k))
      by_cases hmid : run210 x0 t (-((k + 1 : Nat) : Int)) = true
      · -- then run (t+1) (-(k+1)) = true, and parity at depth k+1, time t+1
        rw [hmid] at hinv
        have hinv' : run210 x0 (t + 1) (-((k + 1 : Nat) : Int)) = true := by rw [hinv]; rfl
        have := ih (k + 1) (by omega) (t + 1) hinv'
        push_cast at this ⊢; omega
      · have hmid' : run210 x0 t (-((k + 1 : Nat) : Int)) = false := by simpa using hmid
        rw [hmid'] at hinv
        by_cases hr : run210 x0 t (-((k : Nat) : Int)) = true
        · have := ih k (by omega) t hr; push_cast at this ⊢; omega
        · have hr' : run210 x0 t (-((k : Nat) : Int)) = false := by simpa using hr
          rw [hr'] at hinv
          have hinv' : run210 x0 (t + 1) (-((k + 1 : Nat) : Int)) = true := by rw [hinv]; rfl
          have := ih (k + 1) (by omega) (t + 1) hinv'
          push_cast at this ⊢; omega

/-- **P2′.** Under the clock, the initial row is white at `0` and at every even negative site. -/
theorem left_row_of_clock (x0 : Int → Bool) (hc : Clock210 x0) (i : Int) (hi : i ≤ 0) (he : i % 2 = 0) :
    x0 i = false := by
  refine Classical.byContradiction fun hne => ?_
  have hb : run210 x0 0 (-((-i).toNat : Int)) = true := by
    rw [show (-((-i).toNat : Int)) = i by omega]; simpa [run210] using hne
  have := parity_left_of_clock x0 hc (-i).toNat 0 hb
  omega

/-- **P3.** Two clock orbits with the same initial row on `i ≤ 0` agree on `i ≤ 0` for ever. -/
theorem left_det (x0 y0 : Int → Bool) (hx : Clock210 x0) (hy : Clock210 y0) (h : ∀ i, i ≤ 0 → x0 i = y0 i) :
    ∀ t : Nat, ∀ i, i ≤ 0 → run210 x0 t i = run210 y0 t i := by
  intro t
  induction t with
  | zero => intro i hi; simpa [run210] using h i hi
  | succ t ih =>
    intro i hi
    rcases Int.lt_or_eq_of_le hi with hlt | heq
    · rw [run210_succ, run210_succ, ih (i - 1) (by omega), ih i hi, ih (i + 1) (by omega)]
    · subst heq; rw [hx, hy]


/-! ## Rule 90: linearity, the semigroup, and the freshman's dream -/

def run90 (x0 : Int → Bool) : Nat → Int → Bool
  | 0, i => x0 i
  | t + 1, i => xor (run90 x0 t (i - 1)) (run90 x0 t (i + 1))

theorem run90_succ (x0 : Int → Bool) (t : Nat) (i : Int) :
    run90 x0 (t + 1) i = xor (run90 x0 t (i - 1)) (run90 x0 t (i + 1)) := rfl

theorem run90_zero (x0 : Int → Bool) (i : Int) : run90 x0 0 i = x0 i := rfl

theorem run90_one (x0 : Int → Bool) (i : Int) : run90 x0 1 i = xor (x0 (i - 1)) (x0 (i + 1)) := rfl

/-- On a configuration white at the even sites, rule 210 is rule 90. -/
theorem run210_eq_run90 (x0 : Int → Bool) (h : ∀ i, i % 2 = 0 → x0 i = false) :
    ∀ t i, run210 x0 t i = run90 x0 t i := by
  intro t
  induction t with
  | zero => intro i; rfl
  | succ t ih => intro i; rw [rule90_of_even_white x0 h, run90_succ, ih, ih]

/-- Linearity. -/
theorem run90_xor (x0 y0 : Int → Bool) : ∀ t i, run90 (fun j => xor (x0 j) (y0 j)) t i = xor (run90 x0 t i) (run90 y0 t i) := by
  intro t
  induction t with
  | zero => intro i; rfl
  | succ t ih =>
    intro i
    rw [run90_succ, run90_succ, run90_succ, ih, ih]
    cases run90 x0 t (i - 1) <;> cases run90 y0 t (i - 1) <;> cases run90 x0 t (i + 1) <;> cases run90 y0 t (i + 1) <;> rfl

/-- The semigroup property. -/
theorem run90_add (x0 : Int → Bool) (a : Nat) : ∀ b i, run90 (run90 x0 a) b i = run90 x0 (a + b) i := by
  intro b
  induction b with
  | zero => intro i; rfl
  | succ b ih => intro i; rw [run90_succ, ih, ih, show a + (b + 1) = (a + b) + 1 by omega, run90_succ]

/-- Shifts commute with the rule. -/
theorem run90_shift (x0 : Int → Bool) (d : Int) : ∀ t i, run90 (fun j => x0 (j + d)) t i = run90 x0 t (i + d) := by
  intro t
  induction t with
  | zero => intro i; rfl
  | succ t ih =>
    intro i
    rw [run90_succ, run90_succ, ih, ih, show i - 1 + d = i + d - 1 by omega, show i + 1 + d = i + d + 1 by omega]

/-- **The freshman's dream:** at time `2^n` rule 90 is the sum of the two shifts by `2^n`. -/
theorem run90_pow2 (x0 : Int → Bool) : ∀ n : Nat, ∀ i, run90 x0 (2 ^ n) i = xor (x0 (i - 2 ^ n)) (x0 (i + 2 ^ n)) := by
  intro n
  induction n with
  | zero => intro i; rw [Nat.pow_zero, run90_one]; simp
  | succ n ih =>
    intro i
    have e5 : (2 : Int) ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [Int.pow_succ]; omega
    rw [e5, Nat.pow_succ, show 2 ^ n * 2 = 2 ^ n + 2 ^ n by omega, ← run90_add]
    -- run90 (run90 x0 (2^n)) (2^n) i
    have hf : run90 x0 (2 ^ n) = fun j => xor (x0 (j - 2 ^ n)) (x0 (j + 2 ^ n)) := funext (ih)
    rw [hf]
    have hl : (fun j => xor (x0 (j - 2 ^ n)) (x0 (j + 2 ^ n))) =
        fun j => xor ((fun j => x0 (j + (-(2 ^ n : Int)))) j) ((fun j => x0 (j + (2 ^ n : Int))) j) := by
      funext j; simp [Int.sub_eq_add_neg]
    rw [hl, run90_xor, run90_shift, run90_shift, ih, ih]
    push_cast
    have e1 : i + -(2 ^ n : Int) - 2 ^ n = i - (2 ^ n + 2 ^ n) := by omega
    have e2 : i + -(2 ^ n : Int) + 2 ^ n = i := by omega
    have e3 : i + (2 ^ n : Int) - 2 ^ n = i := by omega
    have e4 : i + (2 ^ n : Int) + 2 ^ n = i + (2 ^ n + 2 ^ n) := by omega
    rw [e1, e2, e3, e4]
    cases x0 (i - (2 ^ n + 2 ^ n)) <;> cases x0 i <;> cases x0 (i + (2 ^ n + 2 ^ n)) <;> rfl

/-- **No finite configuration keeps the clock under rule 90**. For support in `[-R, R]` choose `2^n > R + 1`. At time
`2^n + 1` all four contributing initial sites are outside the support, so the center is white when the clock is black. -/
theorem no_finite_clock90 (x0 : Int → Bool) (R : Nat) (hR : ∀ i : Int, R < i.natAbs → x0 i = false)
    (hc : ∀ t : Nat, run90 x0 t 0 = decide (t % 2 = 1)) : False := by
  obtain ⟨n, hn⟩ : ∃ n : Nat, (R : Int) + 1 < 2 ^ n := by
    refine ⟨R + 1, ?_⟩
    have := Nat.lt_two_pow_self (n := R + 1)
    have hc : ((2 ^ (R + 1) : Nat) : Int) = (2 : Int) ^ (R + 1) := Int.natCast_pow 2 (R + 1)
    omega
  have h := hc (2 ^ n + 1)
  have hodd : (2 ^ n + 1) % 2 = 1 := by
    have : 2 ^ n % 2 = 0 := by
      rcases n with _ | n
      · rw [Int.pow_zero] at hn; omega
      · rw [Nat.pow_succ]; omega
    omega
  rw [show 2 ^ n + 1 = 1 + 2 ^ n by omega, ← run90_add, run90_pow2] at h
  have hodd' : (1 + 2 ^ n) % 2 = 1 := by omega
  simp only [hodd', decide_true] at h
  rw [run90_one, run90_one] at h
  rw [hR _ (by omega), hR _ (by omega), hR _ (by omega), hR _ (by omega)] at h
  exact absurd h (by decide)


/-! ## The background: the parity realization of a left row, built sideways from the clock -/

/-- The clock, white at even times. -/
def clk (t : Nat) : Bool := decide (t % 2 = 1)

/-- The left half driven by the clock at column `0`, from the left row `L` (depth `k` is position `-k`). -/
def lft (L : Nat → Bool) : Nat → Int → Bool
  | 0, i => if i < 0 then L (-i).toNat else false
  | t + 1, i => if i = 0 then clk (t + 1) else xor (lft L t (i - 1)) (lft L t (i + 1))

theorem lft_zero_pos (L : Nat → Bool) (t : Nat) : lft L t 0 = clk t := by
  cases t with
  | zero => simp [lft, clk]
  | succ t => simp [lft]

theorem lft_succ_neg (L : Nat → Bool) (t : Nat) (i : Int) (hi : i ≠ 0) :
    lft L (t + 1) i = xor (lft L t (i - 1)) (lft L t (i + 1)) := by
  simp [lft, hi]

/-- The columns to the right, by right-permutivity of rule 90: `colR (j+2) t = colR (j+1) (t+1) xor colR j t`. -/
def colR (L : Nat → Bool) : Nat → Nat → Bool
  | 0, t => clk t
  | 1, t => xor (clk (t + 1)) (lft L t (-1))
  | j + 2, t => xor (colR L (j + 1) (t + 1)) (colR L j t)

/-- The background configuration and its intended space-time diagram. -/
def bgCol (L : Nat → Bool) (t : Nat) (i : Int) : Bool := if i ≤ 0 then lft L t i else colR L i.toNat t

def bg (L : Nat → Bool) : Int → Bool := bgCol L 0

theorem bgCol_zero (L : Nat → Bool) (t : Nat) : bgCol L t 0 = clk t := by simp [bgCol, lft_zero_pos]

theorem bgCol_pos (L : Nat → Bool) (t : Nat) (j : Nat) : bgCol L t ((j : Int) + 1) = colR L (j + 1) t := by
  unfold bgCol
  rw [ite_eq_right (by omega), show ((j : Int) + 1).toNat = j + 1 by omega]

/-- **The background evolves as built**: rule 90 from `bg L` is `bgCol L`. -/
theorem run90_bg (L : Nat → Bool) : ∀ t i, run90 (bg L) t i = bgCol L t i := by
  intro t
  induction t with
  | zero => intro i; rfl
  | succ t ih =>
    intro i
    rw [run90_succ, ih, ih]
    rcases Int.lt_trichotomy i 0 with hneg | hzero | hpos
    · -- left of the center: the Dirichlet evolution
      have h1 : i - 1 ≤ 0 := by omega
      have h2 : i + 1 ≤ 0 := by omega
      simp only [bgCol, ite_eq_left h1, ite_eq_left h2, ite_eq_left (Int.le_of_lt hneg)]
      try rw [lft_succ_neg L t i (Int.ne_of_lt hneg)]
    · subst hzero
      rw [bgCol_zero, show (0 : Int) - 1 = -1 by omega, show (0 : Int) + 1 = (0 : Nat) + 1 by omega, bgCol_pos]
      simp only [bgCol, ite_eq_left (by omega : (-1 : Int) ≤ 0)]
      show xor (lft L t (-1)) (xor (clk (t + 1)) (lft L t (-1))) = clk (t + 1)
      cases lft L t (-1) <;> cases clk (t + 1) <;> rfl
    · obtain ⟨j, rfl⟩ : ∃ j : Nat, i = (j : Int) + 1 := ⟨(i - 1).toNat, by omega⟩
      rw [bgCol_pos, show (j : Int) + 1 + 1 = ((j + 1 : Nat) : Int) + 1 by omega, bgCol_pos,
        show (j : Int) + 1 - 1 = (j : Int) by omega]
      rcases j with _ | j
      · rw [show ((0 : Nat) : Int) = 0 from rfl, bgCol_zero]
        show xor (clk t) (xor (colR L 1 (t + 1)) (clk t)) = colR L 1 (t + 1)
        cases clk t <;> cases colR L 1 (t + 1) <;> rfl
      · rw [show ((j + 1 : Nat) : Int) = (j : Int) + 1 by omega, bgCol_pos]
        show xor (colR L (j + 1) t) (xor (colR L (j + 2) (t + 1)) (colR L (j + 1) t)) = colR L (j + 2) (t + 1)
        cases colR L (j + 1) t <;> cases colR L (j + 2) (t + 1) <;> rfl

/-- An admissible left row: white at depth `0` and at every even depth. -/
def Admissible (L : Nat → Bool) : Prop := ∀ k, k % 2 = 0 → L k = false

theorem lft_parity (L : Nat → Bool) (hL : Admissible L) :
    ∀ t : Nat, ∀ i : Int, i ≤ 0 → lft L t i = true → ((t : Int) + i) % 2 = 1 := by
  intro t
  induction t with
  | zero =>
    intro i hi h
    simp only [lft] at h
    by_cases hneg : i < 0
    · rw [ite_eq_left hneg] at h
      refine Classical.byContradiction fun hpar => ?_
      have hk : (-i).toNat % 2 = 0 := by omega
      rw [hL _ hk] at h; exact absurd h (by decide)
    · rw [ite_eq_right hneg] at h; exact absurd h (by decide)
  | succ t ih =>
    intro i hi h
    by_cases h0 : i = 0
    · subst h0; simp only [lft, ite_true, clk, decide_eq_true_eq] at h; push_cast; omega
    · rw [lft_succ_neg L t i h0] at h
      by_cases hl : lft L t (i - 1) = true
      · have := ih (i - 1) (by omega) hl; push_cast; omega
      · have hl' : lft L t (i - 1) = false := by simpa using hl
        rw [hl'] at h
        have hr : lft L t (i + 1) = true := by revert h; cases lft L t (i + 1) <;> simp
        have := ih (i + 1) (by omega) hr; push_cast; omega

theorem colR_parity (L : Nat → Bool) (hL : Admissible L) :
    ∀ j t : Nat, colR L j t = true → (t + j) % 2 = 1 := by
  intro j
  induction j using Nat.strongRecOn with
  | ind j ih =>
    intro t h
    rcases j with _ | _ | j
    · simp only [colR, clk, decide_eq_true_eq] at h; omega
    · simp only [colR] at h
      by_cases hc : clk (t + 1) = true
      · simp only [clk, decide_eq_true_eq] at hc; omega
      · have hc' : clk (t + 1) = false := by simpa using hc
        rw [hc'] at h
        have hl : lft L t (-1) = true := by revert h; cases lft L t (-1) <;> simp
        have := lft_parity L hL t (-1) (by omega) hl
        omega
    · simp only [colR] at h
      by_cases h1 : colR L (j + 1) (t + 1) = true
      · have := ih (j + 1) (by omega) (t + 1) h1; omega
      · have h1' : colR L (j + 1) (t + 1) = false := by simpa using h1
        rw [h1'] at h
        have h2 : colR L j t = true := by revert h; cases colR L j t <;> simp
        have := ih j (by omega) t h2; omega

/-- The background is white at the even sites. -/
theorem bg_even_white (L : Nat → Bool) (hL : Admissible L) : ∀ i, i % 2 = 0 → bg L i = false := by
  intro i hi
  refine Classical.byContradiction fun hne => ?_
  have hb : bg L i = true := by simpa using hne
  simp only [bg, bgCol] at hb
  by_cases hle : i ≤ 0
  · rw [ite_eq_left hle] at hb; have := lft_parity L hL 0 i hle hb; omega
  · rw [ite_eq_right hle] at hb; have := colR_parity L hL i.toNat 0 hb; omega

/-- **The background keeps the clock**, under rule 210. -/
theorem clock_bg (L : Nat → Bool) (hL : Admissible L) : Clock210 (bg L) := by
  intro t
  rw [run210_eq_run90 (bg L) (bg_even_white L hL), run90_bg, bgCol_zero]; rfl

/-- The background's left row is `L`. -/
theorem bg_left (L : Nat → Bool) (i : Int) (hi : i < 0) : bg L i = L (-i).toNat := by
  simp [bg, bgCol, lft, hi, Int.le_of_lt hi]

theorem bg_zero (L : Nat → Bool) : bg L 0 = false := by simp [bg, bgCol, lft]


/-! ## The deviation argument: a candidate that leaves the background fails the clock -/

/-- The background's even diagonals are white. -/
theorem bg_diag_even (L : Nat → Bool) (hL : Admissible L) (c : Int) (hc : c % 2 = 0) (s : Nat) :
    Diag210 (bg L) c s = false := by
  refine Classical.byContradiction fun hne => ?_
  have hb : run210 (bg L) s (c - s) = true := by simpa [Diag210] using hne
  have := parity_of_even_white (bg L) (bg_even_white L hL) s (c - s) hb
  omega

/-- The background's diagonal recursion is rule 90's. -/
theorem bg_diag_succ (L : Nat → Bool) (hL : Admissible L) (c : Int) (s : Nat) :
    Diag210 (bg L) c (s + 1) = xor (Diag210 (bg L) (c - 2) s) (Diag210 (bg L) c s) := by
  rw [diag_succ]
  have : (!(Diag210 (bg L) (c - 1) s) && Diag210 (bg L) c s) = Diag210 (bg L) c s := by
    by_cases h : Diag210 (bg L) c s = true
    · have h1 : Diag210 (bg L) (c - 1) s = false := by
        refine Classical.byContradiction fun hne => ?_
        have hb1 : run210 (bg L) s (c - 1 - s) = true := by simpa [Diag210] using hne
        have hb2 : run210 (bg L) s (c - s) = true := by simpa [Diag210] using h
        have := parity_of_even_white (bg L) (bg_even_white L hL) s _ hb1
        have := parity_of_even_white (bg L) (bg_even_white L hL) s _ hb2
        omega
      rw [h1, h]; rfl
    · have h' : Diag210 (bg L) c s = false := by simpa using h
      rw [h']; simp
  rw [this]

/-- The clock on a diagonal: the cell at the center at time `c`. -/
theorem diag_clock (x0 : Int → Bool) (hx : Clock210 x0) (c : Nat) : Diag210 x0 c c = decide (c % 2 = 1) := by
  unfold Diag210; rw [Int.sub_self]; exact hx c

/-- The least witness of a property of the natural numbers. Core Lean has no `Nat.find`; this is its use here. -/
theorem exists_least {p : Nat → Prop} (h : ∃ n, p n) : ∃ n, p n ∧ ∀ m, m < n → ¬ p m := by
  obtain ⟨n, hn⟩ := h
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hm : ∃ m, m < n ∧ p m
    · obtain ⟨m, hmn, hpm⟩ := hm
      exact ih m hmn hpm
    · exact ⟨n, hn, fun m hmn hpm => hm ⟨m, hmn, hpm⟩⟩

/-- The setting of the deviation argument: a clock orbit `x0` whose left row is the admissible `L`, agreeing with the
background `bg L` left of `e ≥ 1` and differing at `e`. -/
structure Dev (x0 : Int → Bool) (L : Nat → Bool) (e : Nat) : Prop where
  hx : Clock210 x0
  hL : Admissible L
  he : 1 ≤ e
  hfirst : ∀ i : Int, i < e → x0 i = bg L i
  hdev : x0 e ≠ bg L e

namespace Dev

variable {x0 : Int → Bool} {L : Nat → Bool} {e : Nat}

theorem local_diag (h : Dev x0 L e) (c : Int) (hc : c < e) (s : Nat) : Diag210 x0 c s = Diag210 (bg L) c s :=
  diag_local x0 (bg L) e h.hfirst s c hc

/-- **F1.** An odd first deviation differs on its diagonal for ever, and so at its own clock time. -/
theorem odd_impossible (h : Dev x0 L e) (hodd : e % 2 = 1) : False := by
  have key : ∀ s, Diag210 x0 e s ≠ Diag210 (bg L) e s := by
    intro s
    induction s with
    | zero => rw [diag_zero, diag_zero]; exact h.hdev
    | succ s ih =>
      rw [diag_succ, diag_succ, h.local_diag (e - 2) (by omega), h.local_diag (e - 1) (by omega),
        bg_diag_even L h.hL (e - 1) (by omega)]
      intro heq
      apply ih
      revert heq
      cases Diag210 (bg L) (↑e - 2) s <;> cases Diag210 x0 ↑e s <;> cases Diag210 (bg L) ↑e s <;> simp
  apply key e
  rw [diag_clock x0 h.hx e, diag_clock (bg L) (clock_bg L h.hL) e]

/-- The gate: the background's odd diagonal just left of the deviation. -/
def bb (L : Nat → Bool) (e : Nat) (s : Nat) : Bool := Diag210 (bg L) ((e : Int) - 1) s

theorem bb_exists (h : Dev x0 L e) (heven : e % 2 = 0) : ∃ s, bb L e s = true := by
  have he := h.he
  refine ⟨e - 1, ?_⟩
  unfold bb
  rw [show (e : Int) - 1 = ((e - 1 : Nat) : Int) by omega, diag_clock (bg L) (clock_bg L h.hL)]
  simp; omega

/-- The first black time of the gate. -/
noncomputable def tau (h : Dev x0 L e) (heven : e % 2 = 0) : Nat :=
  Classical.choose (exists_least (h.bb_exists heven))

theorem bb_tau (h : Dev x0 L e) (heven : e % 2 = 0) : bb L e (h.tau heven) = true :=
  (Classical.choose_spec (exists_least (h.bb_exists heven))).1

theorem bb_before_tau (h : Dev x0 L e) (heven : e % 2 = 0) (s : Nat) (hs : s < h.tau heven) : bb L e s = false := by
  have := (Classical.choose_spec (exists_least (h.bb_exists heven))).2 s hs
  simpa using this

theorem tau_le (h : Dev x0 L e) (heven : e % 2 = 0) : h.tau heven ≤ e - 1 := by
  have he := h.he
  refine Nat.le_of_not_lt fun hlt => ?_
  apply (Classical.choose_spec (exists_least (h.bb_exists heven))).2 (e - 1) hlt
  unfold bb
  rw [show (e : Int) - 1 = ((e - 1 : Nat) : Int) by omega, diag_clock (bg L) (clock_bg L h.hL)]
  simp; omega

/-- The candidate's pairs: even and odd diagonals right of the deviation. -/
def P (x0 : Int → Bool) (e : Nat) (j s : Nat) : Bool := Diag210 x0 ((e : Int) + 2 * j) s
def Q (x0 : Int → Bool) (e : Nat) (j s : Nat) : Bool := Diag210 x0 ((e : Int) + 2 * j + 1) s
/-- The background's gates. -/
def Ab (L : Nat → Bool) (e : Nat) (j s : Nat) : Bool := Diag210 (bg L) ((e : Int) + 2 * j + 1) s

theorem P_zero (h : Dev x0 L e) (heven : e % 2 = 0) : P x0 e 0 0 = true := by
  unfold P; rw [show (e : Int) + 2 * ((0 : Nat) : Int) = (e : Int) by omega, diag_zero]
  have hb : bg L e = false := by
    have := bg_even_white L h.hL e (by omega); exact this
  have := h.hdev; rw [hb] at this; simpa using this

/-- **F2.** The deviation's even diagonal is black until the gate fires and white afterwards. -/
theorem P0_succ (h : Dev x0 L e) (heven : e % 2 = 0) (s : Nat) : P x0 e 0 (s + 1) = (!(bb L e s) && P x0 e 0 s) := by
  unfold P bb
  rw [show (e : Int) + 2 * ((0 : Nat) : Int) = (e : Int) by omega, diag_succ, h.local_diag (e - 2) (by omega), bg_diag_even L h.hL (e - 2) (by omega)]
  rw [h.local_diag (e - 1) (by omega)]
  simp

theorem P0_before (h : Dev x0 L e) (heven : e % 2 = 0) : ∀ s, s ≤ h.tau heven → P x0 e 0 s = true := by
  intro s
  induction s with
  | zero => intro _; exact h.P_zero heven
  | succ s ih =>
    intro hs
    rw [h.P0_succ heven, h.bb_before_tau heven s (by omega), ih (by omega)]; rfl

theorem P0_after (h : Dev x0 L e) (heven : e % 2 = 0) : ∀ s, h.tau heven + 1 ≤ s → P x0 e 0 s = false := by
  intro s hs
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
  induction m with
  | zero =>
    rw [h.P0_succ heven]
    have ht : h.tau heven = 0 := by omega
    have hb : bb L e 0 = true := by rw [← ht]; exact h.bb_tau heven
    rw [hb]; rfl
  | succ m ih =>
    rw [h.P0_succ heven]
    rcases Nat.lt_or_ge (h.tau heven) (m + 1) with hlt | hge
    · rw [ih (by omega)]; simp
    · have ht : h.tau heven = m + 1 := by omega
      have hb : bb L e (m + 1) = true := by rw [← ht]; exact h.bb_tau heven
      rw [hb]; rfl

/-- The candidate's recursions, from the diagonal recursion. -/
theorem P_succ (x0 : Int → Bool) (e j s : Nat) :
    P x0 e (j + 1) (s + 1) = xor (P x0 e j s) (!(Q x0 e j s) && P x0 e (j + 1) s) := by
  unfold P Q; rw [diag_succ]
  rw [show (e : Int) + 2 * ((j + 1 : Nat) : Int) - 2 = (e : Int) + 2 * j by omega,
    show (e : Int) + 2 * ((j + 1 : Nat) : Int) - 1 = (e : Int) + 2 * j + 1 by omega]

theorem Q_succ (x0 : Int → Bool) (e j s : Nat) :
    Q x0 e j (s + 1) = xor (Diag210 x0 ((e : Int) + 2 * j - 1) s) (!(P x0 e j s) && Q x0 e j s) := by
  unfold P Q; rw [diag_succ]
  rw [show (e : Int) + 2 * (j : Int) + 1 - 2 = (e : Int) + 2 * j - 1 by omega,
    show (e : Int) + 2 * (j : Int) + 1 - 1 = (e : Int) + 2 * j by omega]

theorem Q_succ' (x0 : Int → Bool) (e j s : Nat) :
    Q x0 e (j + 1) (s + 1) = xor (Q x0 e j s) (!(P x0 e (j + 1) s) && Q x0 e (j + 1) s) := by
  rw [Q_succ]; unfold Q
  rw [show (e : Int) + 2 * ((j + 1 : Nat) : Int) - 1 = (e : Int) + 2 * j + 1 by omega]

theorem Q0_succ (h : Dev x0 L e) (s : Nat) :
    Q x0 e 0 (s + 1) = xor (bb L e s) (!(P x0 e 0 s) && Q x0 e 0 s) := by
  have he := h.he
  rw [Q_succ]; unfold bb
  rw [show (e : Int) + 2 * ((0 : Nat) : Int) - 1 = (e : Int) - 1 by omega, h.local_diag (e - 1) (by omega)]

/-- The background gates' recursions (rule 90). -/
theorem Ab_succ (L : Nat → Bool) (hL : Admissible L) (e j s : Nat) :
    Ab L e (j + 1) (s + 1) = xor (Ab L e j s) (Ab L e (j + 1) s) := by
  unfold Ab; rw [bg_diag_succ L hL]
  rw [show (e : Int) + 2 * ((j + 1 : Nat) : Int) + 1 - 2 = (e : Int) + 2 * j + 1 by omega]

theorem Ab0_succ (L : Nat → Bool) (hL : Admissible L) (e s : Nat) :
    Ab L e 0 (s + 1) = xor (bb L e s) (Ab L e 0 s) := by
  unfold Ab bb; rw [bg_diag_succ L hL]
  rw [show (e : Int) + 2 * ((0 : Nat) : Int) + 1 - 2 = (e : Int) - 1 by omega]


/-! ### W1: the gate wave in the background -/

theorem W1_const (h : Dev x0 L e) (heven : e % 2 = 0) (w : Nat) (hw : ∀ j, j < w → Ab L e j 0 = false) :
    ∀ j, j ≤ w → ∀ s, s ≤ h.tau heven + j → Ab L e j s = Ab L e j 0 := by
  intro j
  induction j with
  | zero =>
    intro _ s hs
    induction s with
    | zero => rfl
    | succ s ih =>
      rw [Ab0_succ L h.hL, h.bb_before_tau heven s (by omega), ih (by omega)]; simp
  | succ j ih =>
    intro hj s hs
    induction s with
    | zero => rfl
    | succ s ihs =>
      rw [Ab_succ L h.hL, ih (by omega) s (by omega), hw j (by omega), ihs (by omega)]; simp

theorem W1_flip (h : Dev x0 L e) (heven : e % 2 = 0) (w : Nat) (hw : ∀ j, j < w → Ab L e j 0 = false) :
    ∀ j, j ≤ w → Ab L e j (h.tau heven + j + 1) = !(Ab L e j 0) := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [show h.tau heven + 0 + 1 = h.tau heven + 1 by omega, Ab0_succ L h.hL, h.bb_tau heven,
      h.W1_const heven w hw 0 (by omega) (h.tau heven) (by omega)]
    cases Ab L e 0 0 <;> rfl
  | succ j ih =>
    intro hj
    rw [show h.tau heven + (j + 1) + 1 = (h.tau heven + j + 1) + 1 by omega, Ab_succ L h.hL, ih (by omega),
      hw j (by omega), h.W1_const heven w hw (j + 1) hj (h.tau heven + j + 1) (by omega)]
    cases Ab L e (j + 1) 0 <;> rfl

/-! ### The abstract clearing front -/

/-- **C1.** The marker identity, for any streams obeying the pair update. -/
theorem marker (U B Pp Qq : Nat → Bool) (hP : ∀ s, Pp (s + 1) = xor (U s) (!(B s) && Pp s))
    (hQ : ∀ s, Qq (s + 1) = xor (B s) (!(Pp s) && Qq s)) (s : Nat) :
    (!(Pp (s + 1)) && Qq (s + 1)) = xor (!(U s) && B s) (!(U s) && (!(Pp s) && Qq s)) := by
  rw [hP, hQ]; cases U s <;> cases B s <;> cases Pp s <;> cases Qq s <;> rfl

/-- **C2.** Propagation of a clearing witness and a `01` front from the input pair to the output pair. -/
theorem propagate (U B Pp Qq : Nat → Bool) (hP : ∀ s, Pp (s + 1) = xor (U s) (!(B s) && Pp s))
    (hQ : ∀ s, Qq (s + 1) = xor (B s) (!(Pp s) && Qq s)) (t T : Nat) (htT : t < T) (hUt : U t = true)
    (hM : ∀ s, t ≤ s → s < T → (!(U s) && B s) = false) (hUT : U T = false) (hBT : B T = true) :
    ∃ t', (t' = t ∨ t' = t + 1) ∧ Pp t' = true ∧ (∀ s, t' ≤ s → s ≤ T → (!(Pp s) && Qq s) = false) ∧
      Pp (T + 1) = false ∧ Qq (T + 1) = true := by
  have hM1 : ∀ n, t + 1 + n ≤ T → (!(Pp (t + 1 + n)) && Qq (t + 1 + n)) = false := by
    intro n
    induction n with
    | zero =>
      intro _
      rw [show t + 1 + 0 = t + 1 by omega, marker U B Pp Qq hP hQ t, hM t (by omega) htT, hUt]; rfl
    | succ n ih =>
      intro hn
      rw [show t + 1 + (n + 1) = (t + 1 + n) + 1 by omega, marker U B Pp Qq hP hQ, ih (by omega),
        hM (t + 1 + n) (by omega) (by omega)]
      cases U (t + 1 + n) <;> rfl
  have hMT : (!(Pp T) && Qq T) = false := by
    have := hM1 (T - t - 1) (by omega)
    rwa [show t + 1 + (T - t - 1) = T by omega] at this
  have hPT1 : Pp (T + 1) = false := by rw [hP, hUT, hBT]; cases Pp T <;> rfl
  have hQT1 : Qq (T + 1) = true := by
    rw [hQ, hBT]
    have : (!(Pp T) && Qq T) = false := hMT
    rw [this]; rfl
  by_cases hPt : Pp t = true
  · refine ⟨t, Or.inl rfl, hPt, fun s hs1 hs2 => ?_, hPT1, hQT1⟩
    rcases Nat.eq_or_lt_of_le hs1 with heq | hlt
    · subst heq; rw [hPt]; rfl
    · have := hM1 (s - t - 1) (by omega)
      rwa [show t + 1 + (s - t - 1) = s by omega] at this
  · have hPt' : Pp t = false := by simpa using hPt
    refine ⟨t + 1, Or.inr rfl, ?_, fun s hs1 hs2 => ?_, hPT1, hQT1⟩
    · rw [hP, hUt, hPt']; cases B t <;> rfl
    · have := hM1 (s - t - 1) (by omega)
      rwa [show t + 1 + (s - t - 1) = s by omega] at this

/-- **C3.** Every candidate pair has a clearing witness no later than `τ + j` and the `01` front at `τ + j + 1`. -/
theorem front (h : Dev x0 L e) (heven : e % 2 = 0) : ∀ j, ∃ tj, tj ≤ h.tau heven + j ∧ P x0 e j tj = true ∧
    (∀ s, tj ≤ s → s ≤ h.tau heven + j → (!(P x0 e j s) && Q x0 e j s) = false) ∧
    P x0 e j (h.tau heven + j + 1) = false ∧ Q x0 e j (h.tau heven + j + 1) = true := by
  intro j
  induction j with
  | zero =>
    refine ⟨h.tau heven, by omega, h.P0_before heven _ (by omega), fun s hs1 hs2 => ?_, ?_, ?_⟩
    · have hs : s = h.tau heven := by omega
      subst hs; rw [h.P0_before heven _ (by omega)]; rfl
    · rw [show h.tau heven + 0 + 1 = h.tau heven + 1 by omega]; exact h.P0_after heven _ (by omega)
    · rw [show h.tau heven + 0 + 1 = h.tau heven + 1 by omega, h.Q0_succ, h.bb_tau heven, h.P0_before heven _ (by omega)]; rfl
  | succ j ih =>
    obtain ⟨tj, htj, hPtj, hMj, hPT, hQT⟩ := ih
    obtain ⟨t', ht', hPt', hM', hP1, hQ1⟩ := propagate (P x0 e j) (Q x0 e j) (P x0 e (j + 1)) (Q x0 e (j + 1))
      (P_succ x0 e j) (Q_succ' x0 e j) tj (h.tau heven + j + 1) (by omega) hPtj
      (fun s hs1 hs2 => hMj s hs1 (by omega)) hPT hQT
    refine ⟨t', by omega, hPt', fun s hs1 hs2 => hM' s hs1 (by omega), ?_, ?_⟩
    · rw [show h.tau heven + (j + 1) + 1 = (h.tau heven + j + 1) + 1 by omega]; exact hP1
    · rw [show h.tau heven + (j + 1) + 1 = (h.tau heven + j + 1) + 1 by omega]; exact hQ1

/-! ### C4: identification with the background after the front -/

theorem identify (h : Dev x0 L e) (heven : e % 2 = 0) (w : Nat) (hw : ∀ j, j < w → Ab L e j 0 = false) :
    ∀ j, j ≤ w → ∀ s, h.tau heven + j + 1 ≤ s →
      P x0 e j s = false ∧ xor (Q x0 e j s) (Ab L e j s) = Ab L e j 0 := by
  intro j
  induction j with
  | zero =>
    intro _ s hs
    obtain ⟨n, rfl⟩ : ∃ n, s = h.tau heven + 0 + 1 + n := ⟨s - (h.tau heven + 0 + 1), by omega⟩
    induction n with
    | zero =>
      obtain ⟨_, _, _, _, _, hQT⟩ := h.front heven 0
      refine ⟨h.P0_after heven _ (by omega), ?_⟩
      rw [hQT, h.W1_flip heven w hw 0 (by omega)]
      cases Ab L e 0 0 <;> rfl
    | succ n ihn =>
      obtain ⟨hPn, hQn⟩ := ihn (by omega)
      refine ⟨h.P0_after heven _ (by omega), ?_⟩
      rw [show h.tau heven + 0 + 1 + (n + 1) = (h.tau heven + 0 + 1 + n) + 1 by omega, h.Q0_succ, Ab0_succ L h.hL, hPn]
      rw [← hQn]
      cases bb L e (h.tau heven + 0 + 1 + n) <;> cases Q x0 e 0 (h.tau heven + 0 + 1 + n) <;>
        cases Ab L e 0 (h.tau heven + 0 + 1 + n) <;> rfl
  | succ j ih =>
    intro hj s hs
    obtain ⟨n, rfl⟩ : ∃ n, s = h.tau heven + (j + 1) + 1 + n := ⟨s - (h.tau heven + (j + 1) + 1), by omega⟩
    induction n with
    | zero =>
      obtain ⟨_, _, _, _, hPT, hQT⟩ := h.front heven (j + 1)
      refine ⟨hPT, ?_⟩
      rw [hQT, h.W1_flip heven w hw (j + 1) hj]
      cases Ab L e (j + 1) 0 <;> rfl
    | succ n ihn =>
      obtain ⟨hPn, hQn⟩ := ihn (by omega)
      have hprev := ih (by omega) (h.tau heven + (j + 1) + 1 + n) (by omega)
      obtain ⟨hPj, hQj⟩ := hprev
      have hQjeq : Q x0 e j (h.tau heven + (j + 1) + 1 + n) = Ab L e j (h.tau heven + (j + 1) + 1 + n) := by
        rw [hw j (by omega)] at hQj
        revert hQj; cases Q x0 e j (h.tau heven + (j + 1) + 1 + n) <;> cases Ab L e j (h.tau heven + (j + 1) + 1 + n) <;> simp
      rw [show h.tau heven + (j + 1) + 1 + (n + 1) = (h.tau heven + (j + 1) + 1 + n) + 1 by omega]
      constructor
      · rw [P_succ, hPj, hPn]; cases Q x0 e j (h.tau heven + (j + 1) + 1 + n) <;> rfl
      · rw [Q_succ', Ab_succ L h.hL, hPn, hQjeq, ← hQn]
        cases Ab L e j (h.tau heven + (j + 1) + 1 + n) <;> cases Q x0 e (j + 1) (h.tau heven + (j + 1) + 1 + n) <;>
          cases Ab L e (j + 1) (h.tau heven + (j + 1) + 1 + n) <;> rfl

/-- **C5.** With a black background gate beyond the deviation, the candidate fails the clock at `e + 2w + 1`. -/
theorem even_impossible (h : Dev x0 L e) (heven : e % 2 = 0) (hwex : ∃ j, Ab L e j 0 = true) : False := by
  have he := h.he
  have htau := h.tau_le heven
  obtain ⟨w, hAw, hmin⟩ := exists_least hwex
  have hw : ∀ j, j < w → Ab L e j 0 = false := fun j hj => by
    have := hmin j hj; simpa using this
  obtain ⟨-, hid⟩ := h.identify heven w hw w (by omega) (e + 2 * w + 1) (by omega)
  rw [hAw] at hid
  have hQ : Q x0 e w (e + 2 * w + 1) = true := by
    unfold Q
    rw [show (e : Int) + 2 * (w : Int) + 1 = ((e + 2 * w + 1 : Nat) : Int) by omega, diag_clock x0 h.hx]
    simp; omega
  have hA : Ab L e w (e + 2 * w + 1) = true := by
    unfold Ab
    rw [show (e : Int) + 2 * (w : Int) + 1 = ((e + 2 * w + 1 : Nat) : Int) by omega, diag_clock (bg L) (clock_bg L h.hL)]
    simp; omega
  rw [hQ, hA] at hid
  exact absurd hid (by decide)

end Dev


/-! ## The theorem: no finite configuration keeps the clock -/

theorem run210_zero_config : ∀ t i, run210 (fun _ => false) t i = false
  | 0, _ => rfl
  | t + 1, i => by rw [run210_succ, run210_zero_config t, run210_zero_config t, run210_zero_config t]; rfl

/-- **No finite configuration has the clock `0101…` on its center column under rule 210**, by the clearing-front
argument. -/
theorem no_finite_clock (x0 : Int → Bool) (hfin : Finite210 x0) (hx : Clock210 x0) : False := by
  obtain ⟨R, hR⟩ := hfin
  let L : Nat → Bool := fun k => x0 (-(k : Int))
  have hL_def : L = fun (k : Nat) => x0 (-(k : Int)) := rfl
  have hL : Admissible L := fun k hk => left_row_of_clock x0 hx (-(k : Int)) (by omega) (by omega)
  have hleft : ∀ i : Int, i ≤ 0 → x0 i = bg L i := by
    intro i hi
    rcases Int.lt_or_eq_of_le hi with hlt | heq
    · rw [bg_left L i hlt, hL_def]; simp only; congr 1; omega
    · subst heq; rw [bg_zero]; exact left_row_of_clock x0 hx 0 (by omega) (by decide)
  have hclock90 : ∀ t, run90 (bg L) t 0 = decide (t % 2 = 1) := fun t => by
    rw [← run210_eq_run90 (bg L) (bg_even_white L hL)]; exact clock_bg L hL t
  by_cases hall : ∀ i : Int, x0 i = bg L i
  · exact no_finite_clock90 (bg L) R (fun i hi => by rw [← hall i]; exact hR i hi) hclock90
  · have hall' : ∃ i : Int, x0 i ≠ bg L i :=
      Classical.byContradiction fun hno => hall fun i => Classical.byContradiction fun hne => hno ⟨i, hne⟩
    have hex : ∃ n : Nat, x0 n ≠ bg L n := by
      obtain ⟨i, hi⟩ := hall'
      have hpos : 0 < i := by
        refine Classical.byContradiction fun hle => ?_; exact hi (hleft i (by omega))
      exact ⟨i.toNat, by rw [Int.toNat_of_nonneg (Int.le_of_lt hpos)]; exact hi⟩
    obtain ⟨e, hdev, hmin⟩ := exists_least hex
    have he : 1 ≤ e := by
      refine Classical.byContradiction fun h0 => ?_
      have h00 : e = 0 := by omega
      apply hdev; rw [h00]; exact hleft 0 (by omega)
    have hfirst : ∀ i : Int, i < e → x0 i = bg L i := by
      intro i hi
      rcases Int.lt_or_le 0 i with hpos | hle
      · have hm : x0 (i.toNat : Int) = bg L (i.toNat : Int) := Classical.byContradiction (hmin i.toNat (by omega))
        rwa [Int.toNat_of_nonneg (Int.le_of_lt hpos)] at hm
      · exact hleft i hle
    have hD : Dev x0 L e := ⟨hx, hL, he, hfirst, hdev⟩
    rcases Nat.mod_two_eq_zero_or_one e with hk | hk
    · have heven : e % 2 = 0 := hk
      by_cases hwex : ∃ j, Dev.Ab L e j 0 = true
      · exact hD.even_impossible heven hwex
      · have hwex' : ∀ j, Dev.Ab L e j 0 ≠ true := fun j hj => hwex ⟨j, hj⟩
        have hbgfin : ∀ i : Int, max R e < i.natAbs → bg L i = false := by
          intro i hi
          have hRm := Nat.le_max_left R e
          have hem := Nat.le_max_right R e
          rcases Int.lt_or_le i 0 with hneg | hnn
          · rw [← hleft i (Int.le_of_lt hneg)]
            exact hR i (by omega)
          · rcases (show i % 2 = 0 ∨ i % 2 = 1 by omega) with hev | hod
            · exact bg_even_white L hL i hev
            · have hgt : (e : Int) < i := by omega
              obtain ⟨j, hj⟩ : ∃ j : Nat, i = (e : Int) + 2 * j + 1 := ⟨((i - e - 1) / 2).toNat, by omega⟩
              have := hwex' j
              simp only [Dev.Ab, diag_zero] at this
              rw [hj]; simpa using this
        exact no_finite_clock90 (bg L) (max R e) hbgfin hclock90
    · exact hD.odd_impossible (by omega)

/-- The semigroup property of `run210`. -/
theorem run210_add (x0 : Int → Bool) (a : Nat) : ∀ b i, run210 (run210 x0 a) b i = run210 x0 (a + b) i := by
  intro b
  induction b with
  | zero => intro i; rfl
  | succ b ih => intro i; rw [run210_succ, ih, ih, ih, show a + (b + 1) = (a + b) + 1 by omega, run210_succ]

/-- A finite configuration stays finite: its support at time `T` lies within `R + T`. -/
theorem finite_run210 (x0 : Int → Bool) (R : Nat) (hR : ∀ i : Int, R < i.natAbs → x0 i = false) (T : Nat) :
    ∀ i : Int, R + T < i.natAbs → run210 x0 T i = false := by
  intro i hi
  rw [run210_cone x0 (fun _ => false) T i (fun j h1 h2 => hR j (by omega)), run210_zero_config]

/-- **Phase and eventual clocks.** No finite configuration has a center column that is eventually alternating, in
either phase. -/
theorem no_finite_eventually_alternating (x0 : Int → Bool) (hfin : Finite210 x0) (T φ : Nat)
    (h : ∀ t, T ≤ t → run210 x0 t 0 = decide ((t + φ) % 2 = 1)) : False := by
  obtain ⟨R, hR⟩ := hfin
  let T' := T + (T + φ) % 2
  have hT' : T' = T + (T + φ) % 2 := rfl
  apply no_finite_clock (run210 x0 T') ⟨R + T', finite_run210 x0 R hR T'⟩
  intro t
  rw [run210_add, h (T' + t) (by omega)]
  congr 1
  apply propext
  constructor <;> intro hh <;> omega

/-- For the kit's single seed, the same statement in the kit's `run g210`: its center column is not eventually
alternating (the kit's `center210` already makes it eventually constant; this is the general finite case). -/
theorem seed_not_eventually_alternating (T φ : Nat)
    (h : ∀ t, T ≤ t → run g210 t 0 = decide ((t + φ) % 2 = 1)) : False :=
  no_finite_eventually_alternating (fun p => decide (p = 0)) ⟨0, fun i hi => by
    simp only [decide_eq_false_iff_not]; omega⟩ T φ
    (fun t ht => by rw [run210_seed]; exact h t ht)


end Ruliology.CellularAutomata.Rule30Rule210Clock
