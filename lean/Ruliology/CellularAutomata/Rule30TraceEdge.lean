module

public import Ruliology.CellularAutomata.Rule30LeftAntiPeriod

public import Ruliology.CellularAutomata.Rule30WhiteSpacing

public import Ruliology.CellularAutomata.Rule30FiniteConfigs

/-!
# A global trace question sufficient for the full nonperiodicity problem

`EdgeObservable` is a CONJECTURE, not a theorem. It says that finite nonzero
configurations with the same infinite center trace have the same left edge.
Full trace injectivity is false, as the catalog's stripe seeds demonstrate.

The theorem here checks the implication from this new hypothesis to the full
official Problem 1, and indeed to nonperiodicity for every nonzero finite start.
No proof of `EdgeObservable` is supplied or claimed.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30TraceEdge

open Rule30Jen Rule30Realization Rule30PeriodTwoSideways Rule30FiniteConfigs

def HasLeftEdge (x : Int → Bool) (lo : Int) : Prop :=
  x lo = true ∧ ∀ p, p < lo → x p = false

/-- Open global hypothesis. This declaration does not assert that it holds. -/
def EdgeObservable : Prop :=
  ∀ (x y : Int → Bool), FinConfig x → FinConfig y →
    ∀ a b, HasLeftEdge x a → HasLeftEdge y b →
      (∀ t, evol x t 0 = evol y t 0) → a = b

theorem hasLeftEdge_evol {x : Int → Bool} {lo : Int}
    (hx : HasLeftEdge x lo) (t : Nat) : HasLeftEdge (evol x t) (lo - t) :=
  ⟨evol_left_edge hx.1 hx.2 t, fun p hp => evol_eq_false_of_lt hx.2 t p hp⟩

/-- A genuinely global implication: the hypothesis excludes EVERY positive
period, with no bound on the transient, period, or finite starting support. -/
theorem no_eventuallyPeriodic_of_edgeObservable (h : EdgeObservable)
    {x : Int → Bool} (hfin : FinConfig x) (hne : ∃ p, x p = true) :
    ¬ EventuallyPeriodic (fun t => evol x t 0) := by
  rintro ⟨T, P, hP, hper⟩
  obtain ⟨lo, hlo, hzero⟩ := exists_leftmost hfin hne
  have hedge : HasLeftEdge x lo := ⟨hlo, hzero⟩
  have heq := h (evol x T) (evol x (T + P))
    (evol_finConfig hfin T) (evol_finConfig hfin (T + P))
    (lo - T) (lo - (T + P))
    (hasLeftEdge_evol hedge T) (hasLeftEdge_evol hedge (T + P))
    (fun t => by
      rw [Rule30ZeroBoundaryBarriers.evol_restart, Rule30ZeroBoundaryBarriers.evol_restart]
      rw [show T + P + t = (T + t) + P by omega]
      exact (hper (T + t) (by omega)).symm)
  omega

/-- Conditional implication to the exact official prize statement. -/
theorem problem1_of_edgeObservable (h : EdgeObservable) : Rule30Prize.Problem1 := by
  have hs : FinConfig seed := ⟨0, fun p hp => by
    simp only [seed, decide_eq_false_iff_not]
    omega⟩
  have hn : ∃ p, seed p = true := ⟨0, by decide⟩
  have := no_eventuallyPeriodic_of_edgeObservable h hs hn
  have htrace : (fun t => evol seed t 0) = Rule30Prize.center :=
    funext (fun t => evol_seed t 0)
  unfold Rule30Prize.Problem1
  rw [← htrace]
  exact this

/-- The easy edge case: when both edges are at or right of the observation
column, first arrival already determines their positions. No finiteness or
global conjecture is needed here. The unresolved case has edges to the left. -/
theorem edges_equal_of_nonnegative {x y : Int → Bool} {a b : Int}
    (hx : HasLeftEdge x a) (hy : HasLeftEdge y b) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (heq : ∀ t, evol x t 0 = evol y t 0) : a = b := by
  have no_lt : ∀ (u v : Int → Bool) (i j : Int),
      HasLeftEdge u i → HasLeftEdge v j → 0 ≤ i → i < j →
      (∀ t, evol u t 0 = evol v t 0) → False := by
    intro u v i j hu hv hi hij he
    have black := evol_left_edge hu.1 hu.2 i.toNat
    have white := evol_eq_false_of_lt hv.2 i.toNat 0 (by omega)
    rw [show i - (i.toNat : Int) = 0 by omega] at black
    have := he i.toNat
    rw [black, white] at this
    cases this
  rcases Int.lt_trichotomy a b with hab | hab | hab
  · exact False.elim (no_lt x y a b hx hy ha hab heq)
  · exact hab
  · exact False.elim (no_lt y x b a hy hx hb hab (fun t => (heq t).symm))

/-! ### Left-Edge Uniqueness, First-Arrival Laws, Arbitrary-Column Recovery, and Exact Problem 1 Equivalence -/

/-- **Uniqueness of the Left Edge (`hasLeftEdge_unique`):** a configuration `x : Int → Bool` has at
most one left edge `lo : Int`. -/
theorem hasLeftEdge_unique {x : Int → Bool} {a b : Int}
    (ha : HasLeftEdge x a) (hb : HasLeftEdge x b) : a = b := by
  rcases Int.lt_trichotomy a b with hab | hab | hab
  · have hfa := hb.2 a hab
    rw [ha.1] at hfa
    cases hfa
  · exact hab
  · have hfb := ha.2 b hab
    rw [hb.1] at hfb
    cases hfb

/-- **White Before First Arrival at Column `c` (`evol_eq_false_before_arrival`):** if `HasLeftEdge x a`
and `c ≤ a`, then `evol x t c = false` for every time `t < (a - c).toNat`. -/
theorem evol_eq_false_before_arrival {x : Int → Bool} {a c : Int}
    (hx : HasLeftEdge x a) (hca : c ≤ a) {t : Nat} (ht : t < (a - c).toNat) :
    evol x t c = false :=
  evol_eq_false_of_lt hx.2 t c (by omega)

/-- **Black at First Arrival at Column `c` (`evol_eq_true_at_arrival`):** if `HasLeftEdge x a` and
`c ≤ a`, then `evol x (a - c).toNat c = true`. -/
theorem evol_eq_true_at_arrival {x : Int → Bool} {a c : Int}
    (hx : HasLeftEdge x a) (hca : c ≤ a) :
    evol x (a - c).toNat c = true := by
  have he := evol_left_edge hx.1 hx.2 (a - c).toNat
  rwa [show a - ((a - c).toNat : Int) = c by omega] at he

/-- **General Observation-Column Edge Recovery (`edges_equal_of_ge_col`):** if `HasLeftEdge x a` and
`HasLeftEdge y b` with `c ≤ a` and `c ≤ b`, then equality of their traces at column `c` forces `a = b`. -/
theorem edges_equal_of_ge_col {x y : Int → Bool} {a b c : Int}
    (hx : HasLeftEdge x a) (hy : HasLeftEdge y b) (ha : c ≤ a) (hb : c ≤ b)
    (heq : ∀ t, evol x t c = evol y t c) : a = b := by
  have no_lt : ∀ (u v : Int → Bool) (i j : Int),
      HasLeftEdge u i → HasLeftEdge v j → c ≤ i → i < j →
      (∀ t, evol u t c = evol v t c) → False := by
    intro u v i j hu hv hi hij he
    have hblack := evol_eq_true_at_arrival hu hi
    have hwhite := evol_eq_false_before_arrival (c := c) hv (by omega) (t := (i - c).toNat) (by omega)
    have htr := he (i - c).toNat
    rw [hblack, hwhite] at htr
    cases htr
  rcases Int.lt_trichotomy a b with hab | hab | hab
  · exact False.elim (no_lt x y a b hx hy ha hab heq)
  · exact hab
  · exact False.elim (no_lt y x b a hy hx hb hab (fun t => (heq t).symm))

/-- **Explicit Finite-Time Trace Divergence for Distinct Edges Right of `c`
(`exists_trace_diff_of_ne_edges_ge_col`):** if `HasLeftEdge x a` and `HasLeftEdge y b` with `c ≤ a`,
`c ≤ b`, and `a ≠ b`, then their column-`c` traces disagree at some time
`t ≤ max (a - c).toNat (b - c).toNat`. -/
theorem exists_trace_diff_of_ne_edges_ge_col {x y : Int → Bool} {a b c : Int}
    (hx : HasLeftEdge x a) (hy : HasLeftEdge y b) (ha : c ≤ a) (hb : c ≤ b) (hne : a ≠ b) :
    ∃ t : Nat, t ≤ max (a - c).toNat (b - c).toNat ∧ evol x t c ≠ evol y t c := by
  rcases Int.lt_trichotomy a b with hab | hab | hab
  · refine ⟨(a - c).toNat, Nat.le_max_left _ _, ?_⟩
    have hblack := evol_left_edge hx.1 hx.2 (a - c).toNat
    rw [show a - ((a - c).toNat : Int) = c by omega] at hblack
    have hwhite := evol_eq_false_of_lt hy.2 (a - c).toNat c (by omega)
    rw [hblack, hwhite]
    decide
  · exact False.elim (hne hab)
  · refine ⟨(b - c).toNat, Nat.le_max_right _ _, ?_⟩
    have hblack := evol_left_edge hy.1 hy.2 (b - c).toNat
    rw [show b - ((b - c).toNat : Int) = c by omega] at hblack
    have hwhite := evol_eq_false_of_lt hx.2 (b - c).toNat c (by omega)
    rw [hblack, hwhite]
    decide

/-- **Seed Left Edge at Time `t` (`hasLeftEdge_evol_seed`):** the single-black-cell evolution
`evol seed t` has left edge `-(t : Int)`. -/
theorem hasLeftEdge_evol_seed (t : Nat) : HasLeftEdge (evol seed t) (-(t : Int)) := by
  have h0 : HasLeftEdge seed 0 := ⟨by decide, fun p hp => by
    show decide (p = 0) = false
    simp; omega⟩
  have ht := hasLeftEdge_evol h0 t
  simpa using ht

/-- **Seed Trace Shift-Freedom (`SeedTraceShiftFree`):** no two distinct positive time-shifts
`evol seed T` and `evol seed (T + P)` (`P > 0`) produce identical infinite center traces. -/
def SeedTraceShiftFree : Prop :=
  ∀ T P : Nat, 0 < P → ¬ (∀ t, evol (evol seed T) t 0 = evol (evol seed (T + P)) t 0)

/-- **`EdgeObservable` Implies `SeedTraceShiftFree` (`seedTraceShiftFree_of_edgeObservable`):**
the global `EdgeObservable` hypothesis implies `SeedTraceShiftFree`. -/
theorem seedTraceShiftFree_of_edgeObservable (h : EdgeObservable) : SeedTraceShiftFree := by
  intro T P hP heq
  have hs : FinConfig seed := ⟨0, fun p hp => by simp only [seed, decide_eq_false_iff_not]; omega⟩
  have he := h (evol seed T) (evol seed (T + P))
    (evol_finConfig hs T) (evol_finConfig hs (T + P))
    (-(T : Int)) (-((T + P : Nat) : Int))
    (hasLeftEdge_evol_seed T) (hasLeftEdge_evol_seed (T + P)) heq
  omega

/-- **Exact Equivalence Between `Problem1` and `SeedTraceShiftFree`
(`problem1_iff_seedTraceShiftFree`):** `Rule30Prize.Problem1` holds if and only if
`SeedTraceShiftFree` holds. -/
theorem problem1_iff_seedTraceShiftFree : Rule30Prize.Problem1 ↔ SeedTraceShiftFree := by
  constructor
  · intro hP1 T P hP heq
    apply hP1
    refine ⟨T, P, hP, fun t ht => ?_⟩
    show cell (t + P) 0 = cell t 0
    rw [← evol_seed (t + P) 0, ← evol_seed t 0]
    have h1 := Rule30ZeroBoundaryBarriers.evol_restart seed T (t - T) 0
    have h2 := Rule30ZeroBoundaryBarriers.evol_restart seed (T + P) (t - T) 0
    rw [show T + (t - T) = t by omega] at h1
    rw [show T + P + (t - T) = t + P by omega] at h2
    rw [← h1, ← h2]
    exact (heq (t - T)).symm
  · intro hS ⟨T, P, hP, hper⟩
    refine hS T P hP (fun t => ?_)
    rw [Rule30ZeroBoundaryBarriers.evol_restart, Rule30ZeroBoundaryBarriers.evol_restart]
    rw [evol_seed, evol_seed, show T + P + t = (T + t) + P by omega]
    exact (hper (T + t) (by omega)).symm

/-! ### Unconditional Left-Cone Arrival Divergence, Left-Half Shift-Freedom, and Exact Shift Recovery of `evol seed` -/

/-- **Exact Arrival-Time Divergence of Shifted Seed Traces
(`evol_seed_shift_arrival_true_and_false`):** for any `T P : Nat` with `0 < P` and column
`c ≤ -((T + P : Nat) : Int)`, at time `t₀ = (-((T + P : Nat) : Int) - c).toNat`,
`evol (evol seed (T + P)) t₀ c = true` and `evol (evol seed T) t₀ c = false`. -/
theorem evol_seed_shift_arrival_true_and_false (T : Nat) {P : Nat} (hP : 0 < P)
    {c : Int} (hc : c ≤ -((T + P : Nat) : Int)) :
    evol (evol seed (T + P)) (-((T + P : Nat) : Int) - c).toNat c = true ∧
      evol (evol seed T) (-((T + P : Nat) : Int) - c).toNat c = false := by
  refine ⟨evol_eq_true_at_arrival (hasLeftEdge_evol_seed (T + P)) hc, ?_⟩
  exact evol_eq_false_before_arrival (hasLeftEdge_evol_seed T) (by omega) (by omega)

/-- **Unconditional Left-Cone Trace Shift-Freedom of `seed`
(`seed_shift_trace_ne_of_le_neg_add`):** for any `T P : Nat` with `0 < P` and column
`c ≤ -((T + P : Nat) : Int)`,
`¬ (∀ t : Nat, evol (evol seed T) t c = evol (evol seed (T + P)) t c)`. -/
theorem seed_shift_trace_ne_of_le_neg_add (T : Nat) {P : Nat} (hP : 0 < P)
    {c : Int} (hc : c ≤ -((T + P : Nat) : Int)) :
    ¬ (∀ t : Nat, evol (evol seed T) t c = evol (evol seed (T + P)) t c) := by
  intro heq
  obtain ⟨htrue, hfalse⟩ := evol_seed_shift_arrival_true_and_false T hP hc
  have h := heq (-((T + P : Nat) : Int) - c).toNat
  rw [htrue, hfalse] at h
  cases h

/-- **Unconditional Exclusion of Period `P` from `T` on Columns `c ≤ -(T + P)`
(`not_cell_periodic_at_col_le_neg_add`):** for any `T P : Nat` with `0 < P` and column
`c ≤ -((T + P : Nat) : Int)`, `¬ (∀ t : Nat, T ≤ t → cell (t + P) c = cell t c)`. -/
theorem not_cell_periodic_at_col_le_neg_add (T : Nat) {P : Nat} (hP : 0 < P)
    {c : Int} (hc : c ≤ -((T + P : Nat) : Int)) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + P) c = cell t c) := by
  intro hper
  refine seed_shift_trace_ne_of_le_neg_add T hP hc (fun t => ?_)
  rw [Rule30ZeroBoundaryBarriers.evol_restart, Rule30ZeroBoundaryBarriers.evol_restart,
      evol_seed, evol_seed, show T + P + t = (T + t) + P by omega]
  exact (hper (T + t) (by omega)).symm

/-- **Exact Shift Recovery from Any Left-Bounded Observation Column
(`seed_shift_eq_of_trace_eq_le`):** if `c ≤ -(T₁ : Int)`, `c ≤ -(T₂ : Int)`, and
`∀ t : Nat, evol (evol seed T₁) t c = evol (evol seed T₂) t c`, then `T₁ = T₂`. -/
theorem seed_shift_eq_of_trace_eq_le {T₁ T₂ : Nat} {c : Int}
    (h1 : c ≤ -(T₁ : Int)) (h2 : c ≤ -(T₂ : Int))
    (heq : ∀ t : Nat, evol (evol seed T₁) t c = evol (evol seed T₂) t c) :
    T₁ = T₂ := by
  have hneg := edges_equal_of_ge_col (hasLeftEdge_evol_seed T₁) (hasLeftEdge_evol_seed T₂) h1 h2 heq
  omega

/-- **Exact Bidirectional Equivalence for Left-Cone Seed Shifts
(`seed_shift_trace_eq_iff_eq_of_le`):** when `c ≤ -(T₁ : Int)` and `c ≤ -(T₂ : Int)`,
`(∀ t : Nat, evol (evol seed T₁) t c = evol (evol seed T₂) t c) ↔ T₁ = T₂`. -/
theorem seed_shift_trace_eq_iff_eq_of_le {T₁ T₂ : Nat} {c : Int}
    (h1 : c ≤ -(T₁ : Int)) (h2 : c ≤ -(T₂ : Int)) :
    (∀ t : Nat, evol (evol seed T₁) t c = evol (evol seed T₂) t c) ↔ T₁ = T₂ := by
  constructor
  · exact seed_shift_eq_of_trace_eq_le h1 h2
  · rintro rfl _
    rfl

/-! ### Depth-5 Left-Space Arrival Laws, Three-Column Inward Non-Periodicity, White-Gate Transmission, and Bounded-Horizon `{0, 1}` Divergence -/

/-- **Exact Arrival Triple at Column `-s` (`cell_neg_arrival_triple`):** for every `s : Nat`,
at column `-(s : Int)`, `cell s (-(s : Int)) = true` (`D 0`), `cell (s + 1) (-(s : Int)) = true` (`D 1`),
and `cell (s + 2) (-(s : Int)) = false` (`D 2`). -/
theorem cell_neg_arrival_triple (s : Nat) :
    cell s (-(s : Int)) = true ∧
      cell (s + 1) (-(s : Int)) = true ∧
      cell (s + 2) (-(s : Int)) = false := by
  have h0 : cell s (-(s : Int)) = true := cell_left_edge s
  have h1 : cell (s + 1) (-(s : Int)) = Rule30Diagonals.D 1 (s + 1) := by
    unfold Rule30Diagonals.D
    exact Rule30Diagonals.cell_congr (by omega)
  have h1_true : cell (s + 1) (-(s : Int)) = true := by
    rw [h1]
    exact Rule30Diagonals.D_one s
  have h2 : cell (s + 2) (-(s : Int)) = Rule30Diagonals.D 2 (s + 2) := by
    unfold Rule30Diagonals.D
    exact Rule30Diagonals.cell_congr (by omega)
  have h2_false : cell (s + 2) (-(s : Int)) = false := by
    rw [h2]
    have hstep := Rule30Diagonals.D_step 0 (s + 1)
    rw [show s + 1 + 1 = s + 2 by omega, Rule30Diagonals.D_zero, Rule30Diagonals.D_one s, Bool.true_or] at hstep
    exact hstep
  exact ⟨h0, h1_true, h2_false⟩

/-- **Phase-Locking of the Fifth and Third Left Diagonals (`D_five_eq_D_three`):** for every
`s : Nat`, `D 5 (s + 5) = D 3 (s + 3)`. -/
theorem D_five_eq_D_three (s : Nat) :
    Rule30Diagonals.D 5 (s + 5) = Rule30Diagonals.D 3 (s + 3) := by
  have h2 : ∀ k : Nat, Rule30Diagonals.D 2 (k + 2) = false := fun k => by
    have hs := Rule30Diagonals.D_step 0 (k + 1)
    rw [show k + 1 + 1 = k + 2 by omega, Rule30Diagonals.D_zero, Rule30Diagonals.D_one k, Bool.true_or] at hs
    exact hs
  have h4_all : ∀ k : Nat, Rule30Diagonals.D 4 (k + 4) = true := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      have hs := Rule30Diagonals.D_step 2 (k + 4)
      rw [show k + 4 + 1 = k + 1 + 4 by omega,
          show Rule30Diagonals.D 2 (k + 4) = false from h2 (k + 2),
          ih, Bool.or_true] at hs
      exact hs
  have h3 : Rule30Diagonals.D 3 (s + 4) = !Rule30Diagonals.D 3 (s + 3) := by
    have hs := Rule30Diagonals.D_step 1 (s + 3)
    rw [show s + 3 + 1 = s + 4 by omega,
        show Rule30Diagonals.D 1 (s + 3) = true from Rule30Diagonals.D_one (s + 2),
        show Rule30Diagonals.D 2 (s + 3) = false from h2 (s + 1), Bool.false_or] at hs
    simpa using hs
  have hstep := Rule30Diagonals.D_step 3 (s + 4)
  rw [show s + 4 + 1 = s + 5 by omega, h4_all s, Bool.true_or, h3] at hstep
  revert hstep
  cases Rule30Diagonals.D 3 (s + 3) <;> cases Rule30Diagonals.D 5 (s + 5) <;> decide

/-- **Five-Tick Arrival Profile at Column `-s` (`cell_neg_arrival_five`):** for every `s : Nat`,
at column `-(s : Int)`, `cell s (-s) = true`, `cell (s + 1) (-s) = true`, `cell (s + 2) (-s) = false`,
`cell (s + 4) (-s) = true`, and `cell (s + 5) (-s) = cell (s + 3) (-s)`. -/
theorem cell_neg_arrival_five (s : Nat) :
    cell s (-(s : Int)) = true ∧
      cell (s + 1) (-(s : Int)) = true ∧
      cell (s + 2) (-(s : Int)) = false ∧
      cell (s + 4) (-(s : Int)) = true ∧
      cell (s + 5) (-(s : Int)) = cell (s + 3) (-(s : Int)) := by
  obtain ⟨h0, h1, h2⟩ := cell_neg_arrival_triple s
  have h2_diag : ∀ k : Nat, Rule30Diagonals.D 2 (k + 2) = false := fun k => by
    have hs := Rule30Diagonals.D_step 0 (k + 1)
    rw [show k + 1 + 1 = k + 2 by omega, Rule30Diagonals.D_zero, Rule30Diagonals.D_one k, Bool.true_or] at hs
    exact hs
  have h4_all : ∀ k : Nat, Rule30Diagonals.D 4 (k + 4) = true := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      have hs := Rule30Diagonals.D_step 2 (k + 4)
      rw [show k + 4 + 1 = k + 1 + 4 by omega,
          show Rule30Diagonals.D 2 (k + 4) = false from h2_diag (k + 2),
          ih, Bool.or_true] at hs
      exact hs
  have h4 : cell (s + 4) (-(s : Int)) = Rule30Diagonals.D 4 (s + 4) := by
    unfold Rule30Diagonals.D
    exact Rule30Diagonals.cell_congr (by omega)
  have h4_true : cell (s + 4) (-(s : Int)) = true := by
    rw [h4, h4_all s]
  have h5 : cell (s + 5) (-(s : Int)) = Rule30Diagonals.D 5 (s + 5) := by
    unfold Rule30Diagonals.D
    exact Rule30Diagonals.cell_congr (by omega)
  have h3 : cell (s + 3) (-(s : Int)) = Rule30Diagonals.D 3 (s + 3) := by
    unfold Rule30Diagonals.D
    exact Rule30Diagonals.cell_congr (by omega)
  have h53 : cell (s + 5) (-(s : Int)) = cell (s + 3) (-(s : Int)) := by
    rw [h5, h3, D_five_eq_D_three s]
  exact ⟨h0, h1, h2, h4_true, h53⟩

/-- **Unconditional Non-Periodicity on `c ≤ -(T + P) + 1`
(`not_cell_periodic_at_col_le_neg_add_add_one`):** -/
theorem not_cell_periodic_at_col_le_neg_add_add_one (T : Nat) {P : Nat} (hP : 0 < P)
    {c : Int} (hc : c ≤ -((T + P : Nat) : Int) + 1) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + P) c = cell t c) := by
  intro hper
  by_cases hle : c ≤ -((T + P : Nat) : Int)
  · exact not_cell_periodic_at_col_le_neg_add T hP hle hper
  · let s : Nat := T + P - 1
    have hc_s : c = -(s : Int) := by omega
    by_cases hP1 : P = 1
    · subst hP1
      have hsT : s = T := by omega
      have h := hper (T + 1) (by omega)
      rw [hc_s, hsT, show T + 1 + 1 = T + 2 by omega,
          (cell_neg_arrival_triple T).2.1, (cell_neg_arrival_triple T).2.2] at h
      cases h
    · have h := hper T (Nat.le_refl T)
      have hTP : T + P = s + 1 := by omega
      rw [hc_s, hTP, (cell_neg_arrival_triple s).2.1,
          cell_eq_false_of_lt T (-(s : Int)) (by omega)] at h
      cases h

/-- **Unconditional Non-Periodicity Three Columns Inside the Light Cone
(`not_cell_periodic_at_col_le_neg_add_add_three`):** for every `T P : Nat` with `0 < P` and every
column `c ≤ 0` with `c ≤ -((T + P : Nat) : Int) + 3`, `cell · c` is not `P`-periodic from `T` on. -/
theorem not_cell_periodic_at_col_le_neg_add_add_three (T : Nat) {P : Nat} (hP : 0 < P)
    {c : Int} (hc0 : c ≤ 0) (hc : c ≤ -((T + P : Nat) : Int) + 3) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + P) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  obtain ⟨h0, h1, h2, h4, h53⟩ := cell_neg_arrival_five s
  by_cases hP1 : P = 1
  · subst hP1
    have h_a := hper (s + 2) (by omega)
    have h_b := hper (s + 3) (by omega)
    rw [hc_eq, show s + 2 + 1 = s + 3 by omega, h2] at h_a
    rw [hc_eq, show s + 3 + 1 = s + 4 by omega, h4, h_a] at h_b
    cases h_b
  · by_cases hP2 : P = 2
    · subst hP2
      have h := hper (s + 2) (by omega)
      rw [hc_eq, show s + 2 + 2 = s + 4 by omega, h4, h2] at h
      cases h
    · by_cases hP3 : P = 3
      · subst hP3
        have h_a := hper s (by omega)
        have h_b := hper (s + 2) (by omega)
        rw [hc_eq, h0] at h_a
        rw [hc_eq, show s + 2 + 3 = s + 5 by omega, h53, h_a, h2] at h_b
        cases h_b
      · by_cases hP4 : P = 4
        · subst hP4
          cases h3_val : cell (s + 3) (-(s : Int))
          · have h5_false : cell (s + 5) (-(s : Int)) = false := by rw [h53, h3_val]
            have h := hper (s + 1) (by omega)
            rw [hc_eq, show s + 1 + 4 = s + 5 by omega, h5_false, h1] at h
            cases h
          · have h := hper (s - 1) (by omega)
            rw [hc_eq, show s - 1 + 4 = s + 3 by omega, h3_val,
                cell_eq_false_of_lt (s - 1) (-(s : Int)) (by omega)] at h
            cases h
        · have h := hper (s + 4 - P) (by omega)
          rw [hc_eq, show s + 4 - P + P = s + 4 by omega, h4,
              cell_eq_false_of_lt (s + 4 - P) (-(s : Int)) (by omega)] at h
          cases h

/-- **Unconditional Two-Step Inward Period-2 Exclusion on `c ≤ -T`
(`not_cell_periodic_two_at_col_le_neg`):** -/
theorem not_cell_periodic_two_at_col_le_neg (T : Nat) {c : Int} (hc : c ≤ -(T : Int)) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 2) c = cell t c) :=
  not_cell_periodic_at_col_le_neg_add_add_three T (by decide : 0 < 2) (by omega) (by omega)

/-- **Unconditional Two-Step Inward Period-1 Exclusion on `c ≤ -T + 1` for `1 ≤ T`
(`not_cell_periodic_one_at_col_le_neg_add_one`):** -/
theorem not_cell_periodic_one_at_col_le_neg_add_one {T : Nat} (hT : 1 ≤ T)
    {c : Int} (hc : c ≤ -(T : Int) + 1) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 1) c = cell t c) :=
  not_cell_periodic_at_col_le_neg_add_add_three T (by decide : 0 < 1) (by omega) (by omega)

/-- **Center-Column (`c = 0`) Period-1, Period-2, and Period-3 Exclusion from `T = 0`
(`not_center_periodic_one_two_or_three_from_zero`):** -/
theorem not_center_periodic_one_two_or_three_from_zero :
    ¬ (∀ t : Nat, 0 ≤ t → cell (t + 1) 0 = cell t 0) ∧
      ¬ (∀ t : Nat, 0 ≤ t → cell (t + 2) 0 = cell t 0) ∧
      ¬ (∀ t : Nat, 0 ≤ t → cell (t + 3) 0 = cell t 0) :=
  ⟨not_cell_periodic_at_col_le_neg_add_add_three 0 (by decide : 0 < 1) (by decide) (by decide),
   not_cell_periodic_at_col_le_neg_add_add_three 0 (by decide : 0 < 2) (by decide) (by decide),
   not_cell_periodic_at_col_le_neg_add_add_three 0 (by decide : 0 < 3) (by decide) (by decide)⟩

/-- **Black-Shield Left-Neighbor Locking (`black_shield_locks_left_col`):** -/
theorem black_shield_locks_left_col {t P : Nat} {c : Int}
    (hc0 : cell t c = true) (hcP : cell (t + P) c = true)
    (hc1 : cell (t + 1 + P) c = cell (t + 1) c) :
    cell (t + P) (c - 1) = cell t (c - 1) := by
  rw [cell_left (t + P) c, cell_left t c, show t + P + 1 = t + 1 + P by omega,
      hc1, hc0, hcP, Bool.true_or, Bool.true_or]

/-- **White-Gate Transmission Under Local Column Agreement (`periodic_col_forces_white_gate_and_right_ne`):** -/
theorem periodic_col_forces_white_gate_and_right_ne {t P : Nat} {c : Int}
    (hc0 : cell (t + P) c = cell t c) (hc1 : cell (t + 1 + P) c = cell (t + 1) c)
    (hne : cell (t + P) (c - 1) ≠ cell t (c - 1)) :
    cell t c = false ∧ cell (t + P) c = false ∧ cell (t + P) (c + 1) ≠ cell t (c + 1) := by
  have hfalse : cell t c = false := by
    cases h : cell t c
    · rfl
    · have hP : cell (t + P) c = true := by rw [hc0, h]
      exact False.elim (hne (black_shield_locks_left_col h hP hc1))
  have hPfalse : cell (t + P) c = false := by rw [hc0, hfalse]
  refine ⟨hfalse, hPfalse, fun heq1 => hne ?_⟩
  rw [cell_left (t + P) c, cell_left t c, show t + P + 1 = t + 1 + P by omega,
      hc1, hfalse, hPfalse, heq1]

/-- **One-Step Rightward Disagreement Transfer (`cell_ne_right_step`):** -/
theorem cell_ne_right_step {t P : Nat} {c : Int}
    (hne : cell (t + P) (c - 1) ≠ cell t (c - 1)) :
    cell (t + 1 + P) c ≠ cell (t + 1) c ∨
      cell (t + P) c ≠ cell t c ∨
      cell (t + P) (c + 1) ≠ cell t (c + 1) := by
  refine Classical.byContradiction fun hnor => ?_
  have h1 : cell (t + 1 + P) c = cell (t + 1) c :=
    Classical.byContradiction fun h => hnor (Or.inl h)
  have h2 : cell (t + P) c = cell t c :=
    Classical.byContradiction fun h => hnor (Or.inr (Or.inl h))
  have h3 : cell (t + P) (c + 1) = cell t (c + 1) :=
    Classical.byContradiction fun h => hnor (Or.inr (Or.inr h))
  have eqL := cell_left (t + P) c
  have eqR := cell_left t c
  rw [show t + P + 1 = t + 1 + P by omega, h1, h2, h3, ← eqR] at eqL
  exact hne eqL

/-- **Adjacent Pair Disagreement Step (`pair_disagreement_step`):** -/
theorem pair_disagreement_step {T P B : Nat} {c : Int}
    (h : ∃ t : Nat, T ≤ t ∧ t ≤ T + B ∧
      (cell (t + P) c ≠ cell t c ∨ cell (t + P) (c + 1) ≠ cell t (c + 1))) :
    ∃ t : Nat, T ≤ t ∧ t ≤ T + (B + 1) ∧
      (cell (t + P) (c + 1) ≠ cell t (c + 1) ∨ cell (t + P) (c + 2) ≠ cell t (c + 2)) := by
  obtain ⟨t, ht1, ht2, hc | hc1⟩ := h
  · have hstep := cell_ne_right_step (c := c + 1) (by simpa [Int.add_sub_cancel] using hc)
    rcases hstep with hnext | hcurr | hnextcol
    · exact ⟨t + 1, by omega, by omega, Or.inl hnext⟩
    · exact ⟨t, ht1, by omega, Or.inl hcurr⟩
    · exact ⟨t, ht1, by omega, Or.inr (by simpa [Int.add_assoc] using hnextcol)⟩
  · exact ⟨t, ht1, by omega, Or.inl hc1⟩

/-- **Multi-Column Rightward Pair Transport (`pair_disagreement_shift`):** -/
theorem pair_disagreement_shift {T P B : Nat} {c : Int} (d : Nat)
    (h : ∃ t : Nat, T ≤ t ∧ t ≤ T + B ∧
      (cell (t + P) c ≠ cell t c ∨ cell (t + P) (c + 1) ≠ cell t (c + 1))) :
    ∃ t : Nat, T ≤ t ∧ t ≤ T + (B + d) ∧
      (cell (t + P) (c + d) ≠ cell t (c + d) ∨
       cell (t + P) (c + d + 1) ≠ cell t (c + d + 1)) := by
  induction d with
  | zero => simpa using h
  | succ d ih =>
    have hstep := pair_disagreement_step ih
    obtain ⟨t, ht1, ht2, hdisj⟩ := hstep
    refine ⟨t, ht1, by omega, ?_⟩
    simpa [Int.natCast_add, Int.add_assoc] using hdisj

/-- **Quantitative Bounded-Horizon Two-Column Disagreement (`exists_center_or_col_one_ne_within_horizon`):** -/
theorem exists_center_or_col_one_ne_within_horizon (T : Nat) {P : Nat} (hP : 0 < P) :
    ∃ t : Nat, T ≤ t ∧ t ≤ 2 * T + P ∧
      (Rule30Prize.center (t + P) ≠ Rule30Prize.center t ∨ cell (t + P) 1 ≠ cell t 1) := by
  have hedge : cell (T + P) (-((T + P : Nat) : Int)) ≠ cell T (-((T + P : Nat) : Int)) := by
    rw [cell_left_edge (T + P), cell_eq_false_of_lt T (-((T + P : Nat) : Int)) (by omega)]
    decide
  have h0 : ∃ t : Nat, T ≤ t ∧ t ≤ T + 0 ∧
      (cell (t + P) (-((T + P : Nat) : Int)) ≠ cell t (-((T + P : Nat) : Int)) ∨
       cell (t + P) (-((T + P : Nat) : Int) + 1) ≠ cell t (-((T + P : Nat) : Int) + 1)) :=
    ⟨T, Nat.le_refl T, by omega, Or.inl hedge⟩
  obtain ⟨t, ht1, ht2, hdisj⟩ := pair_disagreement_shift (T + P) h0
  refine ⟨t, ht1, by omega, ?_⟩
  have hcol0 : -((T + P : Nat) : Int) + ((T + P : Nat) : Int) = 0 := by omega
  rw [hcol0] at hdisj
  exact hdisj

/-- **Forced Column-`1` Divergence Within `2 * T + P` Under a Periodic Center Tail
(`periodic_center_forces_col_one_ne_within_horizon`):** -/
theorem periodic_center_forces_col_one_ne_within_horizon {T P : Nat} (hP : 0 < P)
    (hper : ∀ t : Nat, T ≤ t → Rule30Prize.center (t + P) = Rule30Prize.center t) :
    ∃ t : Nat, T ≤ t ∧ t ≤ 2 * T + P ∧ cell (t + P) 1 ≠ cell t 1 := by
  obtain ⟨t, ht1, ht2, hc0 | hc1⟩ := exists_center_or_col_one_ne_within_horizon T hP
  · exact False.elim (hc0 (hper t ht1))
  · exact ⟨t, ht1, ht2, hc1⟩

/-! ### Depth-7 Left-Space Arrival Profile (`D 0 .. D 7`) and Four-to-Seven-Column Inward Non-Periodicity -/

/-- **Sixth Left Diagonal Complements Third Left Diagonal at Lag 3 (`D_six_eq_not_D_three`):**
for every `s : Nat`, `D 6 (s + 6) = !D 3 (s + 3)`. -/
theorem D_six_eq_not_D_three (s : Nat) :
    Rule30Diagonals.D 6 (s + 6) = !Rule30Diagonals.D 3 (s + 3) := by
  have h6 : Rule30Diagonals.D 6 (s + 6) = Rule30Diagonals.D 3 (s + 6) :=
    Rule30WhiteSpacing.D_six_eq_D_three (s + 6) (by omega)
  have h3_1 : Rule30Diagonals.D 3 (s + 4) = !Rule30Diagonals.D 3 (s + 3) :=
    Rule30WhiteSpacing.D_three_succ (s + 3) (by omega)
  have h3_2 : Rule30Diagonals.D 3 (s + 5) = Rule30Diagonals.D 3 (s + 3) := by
    rw [show s + 5 = (s + 4) + 1 by omega, Rule30WhiteSpacing.D_three_succ (s + 4) (by omega), h3_1, Bool.not_not]
  have h3_3 : Rule30Diagonals.D 3 (s + 6) = !Rule30Diagonals.D 3 (s + 3) := by
    rw [show s + 6 = (s + 5) + 1 by omega, Rule30WhiteSpacing.D_three_succ (s + 5) (by omega), h3_2]
  rw [h6, h3_3]

/-- **Exact 7-Tick Arrival Profile at Column `-s` (`cell_neg_arrival_seven`):** for every `s : Nat`,
at column `-(s : Int)`:
- `cell s (-s) = true` (`D 0`),
- `cell (s + 1) (-s) = true` (`D 1`),
- `cell (s + 2) (-s) = false` (`D 2`, first white reset border),
- `cell (s + 4) (-s) = true` (`D 4`, all-black shield),
- `cell (s + 5) (-s) = cell (s + 3) (-s)` (`D 5 = D 3`),
- `cell (s + 6) (-s) = !cell (s + 3) (-s)` (`D 6` complements `D 3` at lag 3), and
- `cell (s + 7) (-s) = false` (`D 7`, second white reset border). -/
theorem cell_neg_arrival_seven (s : Nat) :
    cell s (-(s : Int)) = true ∧
      cell (s + 1) (-(s : Int)) = true ∧
      cell (s + 2) (-(s : Int)) = false ∧
      cell (s + 4) (-(s : Int)) = true ∧
      cell (s + 5) (-(s : Int)) = cell (s + 3) (-(s : Int)) ∧
      cell (s + 6) (-(s : Int)) = !cell (s + 3) (-(s : Int)) ∧
      cell (s + 7) (-(s : Int)) = false := by
  obtain ⟨h0, h1, h2, h4, h53⟩ := cell_neg_arrival_five s
  have h3 : cell (s + 3) (-(s : Int)) = Rule30Diagonals.D 3 (s + 3) := by
    unfold Rule30Diagonals.D; exact Rule30Diagonals.cell_congr (by omega)
  have h6 : cell (s + 6) (-(s : Int)) = Rule30Diagonals.D 6 (s + 6) := by
    unfold Rule30Diagonals.D; exact Rule30Diagonals.cell_congr (by omega)
  have h63 : cell (s + 6) (-(s : Int)) = !cell (s + 3) (-(s : Int)) := by
    rw [h6, h3, D_six_eq_not_D_three s]
  have h7 : cell (s + 7) (-(s : Int)) = Rule30Diagonals.D 7 (s + 7) := by
    unfold Rule30Diagonals.D; exact Rule30Diagonals.cell_congr (by omega)
  have h7_false : cell (s + 7) (-(s : Int)) = false := by
    rw [h7, Rule30WhiteSpacing.D_seven_eq_false (s + 7) (by omega)]
  exact ⟨h0, h1, h2, h4, h53, h63, h7_false⟩

/-- **Universal Flip Between Ticks `s + 5` and `s + 6` at Every Left Column `-s`
(`cell_neg_flip_five_six`):** for every `s : Nat`, `cell (s + 6) (-(s : Int)) = !cell (s + 5) (-(s : Int))`. -/
theorem cell_neg_flip_five_six (s : Nat) :
    cell (s + 6) (-(s : Int)) = !cell (s + 5) (-(s : Int)) := by
  obtain ⟨_, _, _, _, h53, h63, _⟩ := cell_neg_arrival_seven s
  rw [h63, h53]

/-- **Seven-Column Inward Period-3 Exclusion (`not_cell_periodic_three_at_col_le_neg_add_four`):**
for every `T : Nat` and column `c ≤ 0` with `c ≤ -(T : Int) + 4` (i.e. `c ≤ -(T + 3) + 7`),
`¬ (∀ t : Nat, T ≤ t → cell (t + 3) c = cell t c)`. -/
theorem not_cell_periodic_three_at_col_le_neg_add_four (T : Nat) {c : Int}
    (hc0 : c ≤ 0) (hc : c ≤ -(T : Int) + 4) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 3) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  obtain ⟨_, _, _, h4, _, _, h7⟩ := cell_neg_arrival_seven s
  have h := hper (s + 4) (by omega)
  rw [hc_eq, show s + 4 + 3 = s + 7 by omega, h7, h4] at h
  cases h

/-- **Uniform Inward Non-Periodicity for `1 ≤ P ≤ 4` on `c ≤ -T + 2`
(`not_cell_periodic_le_four_at_col_le_neg_add_two`):** for every `T : Nat`, `1 ≤ P ≤ 4`,
and column `c ≤ 0` with `c ≤ -(T : Int) + 2` (which for `P = 4` is `c ≤ -(T + 4) + 6`),
`cell · c` is not `P`-periodic from `T` on. -/
theorem not_cell_periodic_le_four_at_col_le_neg_add_two (T : Nat) {P : Nat}
    (hP1 : 1 ≤ P) (hP4 : P ≤ 4) {c : Int} (hc0 : c ≤ 0)
    (hc : c ≤ -(T : Int) + 2) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + P) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  obtain ⟨_, _, h2, h4, h53, h63, h7⟩ := cell_neg_arrival_seven s
  rcases (by omega : P = 1 ∨ P = 2 ∨ P = 3 ∨ P = 4) with rfl | rfl | rfl | rfl
  · have h := hper (s + 5) (by omega)
    rw [hc_eq, show s + 5 + 1 = s + 6 by omega, h63, h53] at h
    revert h; cases cell (s + 3) (-(s : Int)) <;> decide
  · have h := hper (s + 2) (by omega)
    rw [hc_eq, show s + 2 + 2 = s + 4 by omega, h4, h2] at h
    cases h
  · exact not_cell_periodic_three_at_col_le_neg_add_four T hc0 (by omega) hper
  · cases h3_val : cell (s + 3) (-(s : Int))
    · have h6_true : cell (s + 6) (-(s : Int)) = true := by rw [h63, h3_val]; rfl
      have h := hper (s + 2) (by omega)
      rw [hc_eq, show s + 2 + 4 = s + 6 by omega, h6_true, h2] at h
      cases h
    · have h := hper (s + 3) (by omega)
      rw [hc_eq, show s + 3 + 4 = s + 7 by omega, h7, h3_val] at h
      cases h

/-- **Unconditional Non-Periodicity Four Columns Inside the Light Cone for All `P > 0`
(`not_cell_periodic_at_col_le_neg_add_add_four`):** for every `T P : Nat` with `0 < P` and every
column `c ≤ 0` with `c ≤ -((T + P : Nat) : Int) + 4`, `cell · c` is not `P`-periodic from `T` on. -/
theorem not_cell_periodic_at_col_le_neg_add_add_four (T : Nat) {P : Nat} (hP : 0 < P)
    {c : Int} (hc0 : c ≤ 0) (hc : c ≤ -((T + P : Nat) : Int) + 4) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + P) c = cell t c) := by
  by_cases hle4 : P ≤ 4
  · rcases (by omega : P = 1 ∨ P = 2 ∨ P = 3 ∨ P = 4) with rfl | rfl | rfl | rfl
    · intro hper
      let s : Nat := (-c).toNat
      have hc_eq : c = -(s : Int) := by omega
      obtain ⟨_, _, _, _, h53, h63, _⟩ := cell_neg_arrival_seven s
      have h := hper (s + 5) (by omega)
      rw [hc_eq, show s + 5 + 1 = s + 6 by omega, h63, h53] at h
      revert h; cases cell (s + 3) (-(s : Int)) <;> decide
    · exact not_cell_periodic_le_four_at_col_le_neg_add_two T (by decide) (by decide) hc0 (by omega)
    · exact not_cell_periodic_three_at_col_le_neg_add_four T hc0 (by omega)
    · exact not_cell_periodic_le_four_at_col_le_neg_add_two T (by decide) (by decide) hc0 (by omega)
  · intro hper
    let s : Nat := (-c).toNat
    have hc_eq : c = -(s : Int) := by omega
    obtain ⟨_, _, _, h4, _, _, _⟩ := cell_neg_arrival_seven s
    have h := hper (s + 4 - P) (by omega)
    rw [hc_eq, show s + 4 - P + P = s + 4 by omega, h4,
        cell_eq_false_of_lt (s + 4 - P) (-(s : Int)) (by omega)] at h
    cases h

/-- **Depth-9 Arrival Profile at Column `-s` (`cell_neg_arrival_nine`):** for every `s : Nat`,
at column `-(s : Int)`, `cell s (-s) = true`, `cell (s + 1) (-s) = true`, `cell (s + 2) (-s) = false`,
`cell (s + 4) (-s) = true`, `cell (s + 5) (-s) = cell (s + 3) (-s)`, `cell (s + 6) (-s) = !cell (s + 5) (-s)`,
`cell (s + 7) (-s) = false`, and `cell (s + 9) (-s) = true`. -/
theorem cell_neg_arrival_nine (s : Nat) :
    cell s (-(s : Int)) = true ∧
      cell (s + 1) (-(s : Int)) = true ∧
      cell (s + 2) (-(s : Int)) = false ∧
      cell (s + 4) (-(s : Int)) = true ∧
      cell (s + 5) (-(s : Int)) = cell (s + 3) (-(s : Int)) ∧
      cell (s + 6) (-(s : Int)) = !cell (s + 5) (-(s : Int)) ∧
      cell (s + 7) (-(s : Int)) = false ∧
      cell (s + 9) (-(s : Int)) = true := by
  obtain ⟨h0, h1, h2, h4, h53, h63, h7⟩ := cell_neg_arrival_seven s
  have h65 : cell (s + 6) (-(s : Int)) = !cell (s + 5) (-(s : Int)) := cell_neg_flip_five_six s
  have h9 : cell (s + 9) (-(s : Int)) = Rule30Diagonals.D 9 (s + 9) := by
    unfold Rule30Diagonals.D; exact Rule30Diagonals.cell_congr (by omega)
  have h9_true : cell (s + 9) (-(s : Int)) = true := by
    rw [h9, Rule30LeftAntiPeriod.D_nine_eq_true (s + 9) (by omega)]
  exact ⟨h0, h1, h2, h4, h53, h65, h7, h9_true⟩

/-- **Nine-Column Inward Period-1 and Period-2 Exclusion (`not_cell_periodic_one_or_two_at_col_le_neg_add_seven`):**
for every `T : Nat`, `P ∈ {1, 2}`, and column `c ≤ 0` with `c ≤ -(T : Int) + 7`,
`cell · c` is not `P`-periodic from `T` on. -/
theorem not_cell_periodic_one_or_two_at_col_le_neg_add_seven (T : Nat) {P : Nat}
    (hP1 : 1 ≤ P) (hP2 : P ≤ 2) {c : Int} (hc0 : c ≤ 0) (hc : c ≤ -(T : Int) + 7) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + P) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  obtain ⟨_, _, _, _, _, _, h7, h9⟩ := cell_neg_arrival_nine s
  rcases (by omega : P = 1 ∨ P = 2) with rfl | rfl
  · have ha := hper (s + 7) (by omega)
    have hb := hper (s + 8) (by omega)
    rw [hc_eq, show s + 7 + 1 = s + 8 by omega, h7] at ha
    rw [hc_eq, show s + 8 + 1 = s + 9 by omega, h9, ha] at hb
    cases hb
  · have h := hper (s + 7) (by omega)
    rw [hc_eq, show s + 7 + 2 = s + 9 by omega, h9, h7] at h
    cases h

/-- **Nine-Column Inward Non-Periodicity for All `P ≥ 10` (`not_cell_periodic_ge_ten_at_col_le_neg_add_add_nine`):**
for every `T : Nat`, `P ≥ 10`, and column `c ≤ 0` with `c ≤ -((T + P : Nat) : Int) + 9`,
`cell · c` is not `P`-periodic from `T` on. -/
theorem not_cell_periodic_ge_ten_at_col_le_neg_add_add_nine (T : Nat) {P : Nat} (hP : 10 ≤ P)
    {c : Int} (hc0 : c ≤ 0) (hc : c ≤ -((T + P : Nat) : Int) + 9) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + P) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  obtain ⟨_, _, _, _, _, _, _, h9⟩ := cell_neg_arrival_nine s
  have h := hper (s + 9 - P) (by omega)
  rw [hc_eq, show s + 9 - P + P = s + 9 by omega, h9,
      cell_eq_false_of_lt (s + 9 - P) (-(s : Int)) (by omega)] at h
  cases h

/-- **Unconditional Non-Periodicity Five Columns Inside the Light Cone for All `P > 0`
(`not_cell_periodic_at_col_le_neg_add_add_five`):** for every `T P : Nat` with `0 < P` and every
column `c ≤ 0` with `c ≤ -((T + P : Nat) : Int) + 5`, `cell · c` is not `P`-periodic from `T` on. -/
theorem not_cell_periodic_at_col_le_neg_add_add_five (T : Nat) {P : Nat} (hP : 0 < P)
    {c : Int} (hc0 : c ≤ 0) (hc : c ≤ -((T + P : Nat) : Int) + 5) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + P) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  obtain ⟨h0, h1, h2, h4, h53, h65, h7, h9⟩ := cell_neg_arrival_nine s
  by_cases hle6 : P ≤ 6
  · rcases (by omega : P = 1 ∨ P = 2 ∨ P = 3 ∨ P = 4 ∨ P = 5 ∨ P = 6) with rfl | rfl | rfl | rfl | rfl | rfl
    · exact not_cell_periodic_one_or_two_at_col_le_neg_add_seven T (by decide) (by decide) hc0 (by omega) hper
    · exact not_cell_periodic_one_or_two_at_col_le_neg_add_seven T (by decide) (by decide) hc0 (by omega) hper
    · have h := hper (s + 4) (by omega)
      rw [hc_eq, show s + 4 + 3 = s + 7 by omega, h7, h4] at h
      cases h
    · cases h5_val : cell (s + 5) (-(s : Int))
      · have h := hper (s + 1) (by omega)
        rw [hc_eq, show s + 1 + 4 = s + 5 by omega, h5_val, h1] at h
        cases h
      · have h3_true : cell (s + 3) (-(s : Int)) = true := by rw [← h53, h5_val]
        have h := hper (s + 3) (by omega)
        rw [hc_eq, show s + 3 + 4 = s + 7 by omega, h7, h3_true] at h
        cases h
    · cases h5_val : cell (s + 5) (-(s : Int))
      · have h := hper s (by omega)
        rw [hc_eq, h5_val, h0] at h
        cases h
      · have h6_false : cell (s + 6) (-(s : Int)) = false := by rw [h65, h5_val]; rfl
        have h := hper (s + 1) (by omega)
        rw [hc_eq, show s + 1 + 5 = s + 6 by omega, h6_false, h1] at h
        cases h
    · have h := hper (s + 1) (by omega)
      rw [hc_eq, show s + 1 + 6 = s + 7 by omega, h7, h1] at h
      cases h
  · cases h5_val : cell (s + 5) (-(s : Int))
    · have h6_true : cell (s + 6) (-(s : Int)) = true := by rw [h65, h5_val]; rfl
      have h := hper (s + 6 - P) (by omega)
      rw [hc_eq, show s + 6 - P + P = s + 6 by omega, h6_true,
          cell_eq_false_of_lt (s + 6 - P) (-(s : Int)) (by omega)] at h
      cases h
    · have h := hper (s + 5 - P) (by omega)
      rw [hc_eq, show s + 5 - P + P = s + 5 by omega, h5_val,
          cell_eq_false_of_lt (s + 5 - P) (-(s : Int)) (by omega)] at h
      cases h

/-- **Universal Lag-6 Flip Between Ticks `s + 8` and `s + 14` at Every Left Column `-s`
(`cell_neg_flip_eight_fourteen`):** for every `s : Nat`,
`cell (s + 14) (-(s : Int)) = !cell (s + 8) (-(s : Int))`. -/
theorem cell_neg_flip_eight_fourteen (s : Nat) :
    cell (s + 14) (-(s : Int)) = !cell (s + 8) (-(s : Int)) := by
  have h8 : cell (s + 8) (-(s : Int)) = Rule30Diagonals.D 8 (s + 8) := by
    unfold Rule30Diagonals.D; exact Rule30Diagonals.cell_congr (by omega)
  have h14 : cell (s + 14) (-(s : Int)) = Rule30Diagonals.D 14 (s + 14) := by
    unfold Rule30Diagonals.D; exact Rule30Diagonals.cell_congr (by omega)
  have h14_8 : Rule30Diagonals.D 14 (s + 14) = Rule30Diagonals.D 8 (s + 14) :=
    Rule30LeftAntiPeriod.D_fourteen_eq_D_eight (s + 14) (by omega)
  have ha1 : Rule30Diagonals.D 8 (s + 10) = !Rule30Diagonals.D 8 (s + 8) := by
    simpa [Nat.add_assoc] using Rule30LeftAntiPeriod.D_eight_antiperiodic_two (s + 8) (by omega)
  have ha2 : Rule30Diagonals.D 8 (s + 12) = Rule30Diagonals.D 8 (s + 8) := by
    have h := Rule30LeftAntiPeriod.D_eight_antiperiodic_two (s + 10) (by omega)
    rw [show s + 10 + 2 = s + 12 by omega, ha1, Bool.not_not] at h
    exact h
  have ha3 : Rule30Diagonals.D 8 (s + 14) = !Rule30Diagonals.D 8 (s + 8) := by
    have h := Rule30LeftAntiPeriod.D_eight_antiperiodic_two (s + 12) (by omega)
    rw [show s + 12 + 2 = s + 14 by omega, ha2] at h
    exact h
  rw [h14, h8, h14_8, ha3]

/-- **Fourteen-Column Inward Period-6 Exclusion (`not_cell_periodic_six_at_col_le_neg_add_eight`):**
for every `T : Nat` and column `c ≤ 0` with `c ≤ -(T : Int) + 8` (i.e. `c ≤ -(T + 6) + 14`,
14 columns inside the light cone), `¬ (∀ t : Nat, T ≤ t → cell (t + 6) c = cell t c)`. -/
theorem not_cell_periodic_six_at_col_le_neg_add_eight (T : Nat) {c : Int}
    (hc0 : c ≤ 0) (hc : c ≤ -(T : Int) + 8) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 6) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h := hper (s + 8) (by omega)
  have hflip := cell_neg_flip_eight_fourteen s
  rw [hc_eq, show s + 8 + 6 = s + 14 by omega, hflip] at h
  revert h; cases cell (s + 8) (-(s : Int)) <;> decide

/-- **Thirty-Column Inward Period-1 and Period-2 Exclusion
(`not_cell_periodic_one_or_two_at_col_le_neg_add_twenty_eight`):**
for every `T : Nat`, `P ∈ {1, 2}`, and column `c ≤ -3` with `c ≤ -(T : Int) + 28`
(for `P = 2`, 30 columns inside the light cone: `c ≤ -(T + 2) + 30`),
`cell · c` is not `P`-periodic from `T` on. -/
theorem not_cell_periodic_one_or_two_at_col_le_neg_add_twenty_eight (T : Nat) {P : Nat}
    (hP1 : 1 ≤ P) (hP2 : P ≤ 2) {c : Int} (hc0 : c ≤ -3) (hc : c ≤ -(T : Int) + 28) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + P) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h28_d : cell (s + 28) (-(s : Int)) = Rule30Diagonals.D 28 (s + 28) := by
    unfold Rule30Diagonals.D; exact Rule30Diagonals.cell_congr (by omega)
  have h28 : cell (s + 28) (-(s : Int)) = false := by
    rw [h28_d, Rule30LeftAntiPeriod.D_twenty_eight_eq_false (s + 28) (by omega)]
  have h30_d : cell (s + 30) (-(s : Int)) = Rule30Diagonals.D 30 (s + 30) := by
    unfold Rule30Diagonals.D; exact Rule30Diagonals.cell_congr (by omega)
  have h30 : cell (s + 30) (-(s : Int)) = true := by
    rw [h30_d, Rule30LeftAntiPeriod.D_thirty_eq_true (s + 30) (by omega)]
  rcases (by omega : P = 1 ∨ P = 2) with rfl | rfl
  · have ha := hper (s + 28) (by omega)
    have hb := hper (s + 29) (by omega)
    rw [hc_eq, show s + 28 + 1 = s + 29 by omega, h28] at ha
    rw [hc_eq, show s + 29 + 1 = s + 30 by omega, h30, ha] at hb
    cases hb
  · have h := hper (s + 28) (by omega)
    rw [hc_eq, show s + 28 + 2 = s + 30 by omega, h30, h28] at h
    cases h

/-- **Thirty-Column Inward Non-Periodicity for All `P ≥ 31`
(`not_cell_periodic_ge_thirty_one_at_col_le_neg_add_add_thirty`):**
for every `T : Nat`, `P ≥ 31`, and column `c ≤ -3` with `c ≤ -((T + P : Nat) : Int) + 30`,
`cell · c` is not `P`-periodic from `T` on. -/
theorem not_cell_periodic_ge_thirty_one_at_col_le_neg_add_add_thirty (T : Nat) {P : Nat}
    (hP : 31 ≤ P) {c : Int} (hc0 : c ≤ -3) (hc : c ≤ -((T + P : Nat) : Int) + 30) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + P) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h30_d : cell (s + 30) (-(s : Int)) = Rule30Diagonals.D 30 (s + 30) := by
    unfold Rule30Diagonals.D; exact Rule30Diagonals.cell_congr (by omega)
  have h30 : cell (s + 30) (-(s : Int)) = true := by
    rw [h30_d, Rule30LeftAntiPeriod.D_thirty_eq_true (s + 30) (by omega)]
  have h := hper (s + 30 - P) (by omega)
  rw [hc_eq, show s + 30 - P + P = s + 30 by omega, h30,
      cell_eq_false_of_lt (s + 30 - P) (-(s : Int)) (by omega)] at h
  cases h

/-- **Universal Adjacent Column Flip at Ticks `s + 14` and `s + 15` (`cell_neg_flip_fourteen_fifteen`):**
for every `s : Nat`, `cell (s + 15) (-(s : Int)) = !cell (s + 14) (-(s : Int))`. -/
theorem cell_neg_flip_fourteen_fifteen (s : Nat) :
    cell (s + 15) (-(s : Int)) = !cell (s + 14) (-(s : Int)) := by
  have h14 : cell (s + 14) (-(s : Int)) = Rule30Diagonals.D 14 (s + 14) := by
    unfold Rule30Diagonals.D; exact Rule30Diagonals.cell_congr (by omega)
  have h15 : cell (s + 15) (-(s : Int)) = Rule30Diagonals.D 15 (s + 15) := by
    unfold Rule30Diagonals.D; exact Rule30Diagonals.cell_congr (by omega)
  rw [h14, h15, Rule30LeftAntiPeriod.D_fourteen_eq_D_eight (s + 14) (by omega),
      Rule30LeftAntiPeriod.D_fifteen_eq_D_ten (s + 15) (by omega),
      show s + 15 = (s + 14) + 1 by omega,
      Rule30LeftAntiPeriod.D_ten_succ_eq_not_D_eight (s + 14) (by omega)]

/-- **Fifteen-Column Inward Period-1 Exclusion (`not_cell_periodic_one_at_col_le_neg_add_fourteen`):**
for every `T : Nat` and column `c ≤ 0` with `c ≤ -(T : Int) + 14`,
`¬ (∀ t : Nat, T ≤ t → cell (t + 1) c = cell t c)`. -/
theorem not_cell_periodic_one_at_col_le_neg_add_fourteen (T : Nat) {c : Int}
    (hc0 : c ≤ 0) (hc : c ≤ -(T : Int) + 14) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 1) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h := hper (s + 14) (by omega)
  have hflip := cell_neg_flip_fourteen_fifteen s
  rw [hc_eq, show s + 14 + 1 = s + 15 by omega, hflip] at h
  revert h; cases cell (s + 14) (-(s : Int)) <;> decide

/-- **Universal Lag-8 Column Flip at Ticks `s + 10` and `s + 18` (`cell_neg_flip_ten_eighteen`):**
for every `s ≥ 2`, `cell (s + 18) (-(s : Int)) = !cell (s + 10) (-(s : Int))`. -/
theorem cell_neg_flip_ten_eighteen (s : Nat) (hs : 2 ≤ s) :
    cell (s + 18) (-(s : Int)) = !cell (s + 10) (-(s : Int)) := by
  have h10 : cell (s + 10) (-(s : Int)) = Rule30Diagonals.D 10 (s + 10) := by
    unfold Rule30Diagonals.D; exact Rule30Diagonals.cell_congr (by omega)
  have h18 : cell (s + 18) (-(s : Int)) = Rule30Diagonals.D 18 (s + 18) := by
    unfold Rule30Diagonals.D; exact Rule30Diagonals.cell_congr (by omega)
  have p1 : Rule30Diagonals.D 10 (s + 12) = !Rule30Diagonals.D 10 (s + 10) :=
    Rule30LeftAntiPeriod.D_ten_antiperiodic_two (s + 10) (by omega)
  have p2 : Rule30Diagonals.D 10 (s + 14) = Rule30Diagonals.D 10 (s + 10) := by
    have h := Rule30LeftAntiPeriod.D_ten_antiperiodic_two (s + 12) (by omega)
    rw [show s + 12 + 2 = s + 14 by omega, p1, Bool.not_not] at h; exact h
  have p3 : Rule30Diagonals.D 10 (s + 16) = !Rule30Diagonals.D 10 (s + 10) := by
    have h := Rule30LeftAntiPeriod.D_ten_antiperiodic_two (s + 14) (by omega)
    rw [show s + 14 + 2 = s + 16 by omega, p2] at h; exact h
  have p4 : Rule30Diagonals.D 10 (s + 18) = Rule30Diagonals.D 10 (s + 10) := by
    have h := Rule30LeftAntiPeriod.D_ten_antiperiodic_two (s + 16) (by omega)
    rw [show s + 16 + 2 = s + 18 by omega, p3, Bool.not_not] at h; exact h
  rw [h10, h18, Rule30LeftAntiPeriod.D_eighteen_eq_not_D_ten (s + 18) (by omega), p4]

/-- **Eighteen-Column Inward Period-8 Exclusion (`not_cell_periodic_eight_at_col_le_neg_add_ten`):**
for every `T : Nat` and column `c ≤ -2` with `c ≤ -(T : Int) + 10` (i.e. `c ≤ -(T + 8) + 18`),
`¬ (∀ t : Nat, T ≤ t → cell (t + 8) c = cell t c)`. -/
theorem not_cell_periodic_eight_at_col_le_neg_add_ten (T : Nat) {c : Int}
    (hc0 : c ≤ -2) (hc : c ≤ -(T : Int) + 10) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 8) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h := hper (s + 10) (by omega)
  have hflip := cell_neg_flip_ten_eighteen s (by omega)
  rw [hc_eq, show s + 10 + 8 = s + 18 by omega, hflip] at h
  revert h; cases cell (s + 10) (-(s : Int)) <;> decide

/-- **Universal Lag-3 Column Flip at Ticks `s + 19` and `s + 22` (`cell_neg_flip_nineteen_twenty_two`):**
for every `s ≥ 3`, `cell (s + 22) (-(s : Int)) = !cell (s + 19) (-(s : Int))`. -/
theorem cell_neg_flip_nineteen_twenty_two (s : Nat) (hs : 3 ≤ s) :
    cell (s + 22) (-(s : Int)) = !cell (s + 19) (-(s : Int)) := by
  have h19 : cell (s + 19) (-(s : Int)) = Rule30Diagonals.D 19 (s + 19) := by
    unfold Rule30Diagonals.D; exact Rule30Diagonals.cell_congr (by omega)
  have h22 : cell (s + 22) (-(s : Int)) = Rule30Diagonals.D 22 (s + 22) := by
    unfold Rule30Diagonals.D; exact Rule30Diagonals.cell_congr (by omega)
  have p1 : Rule30Diagonals.D 10 (s + 22) = !Rule30Diagonals.D 10 (s + 20) :=
    Rule30LeftAntiPeriod.D_ten_antiperiodic_two (s + 20) (by omega)
  have p2 : Rule30Diagonals.D 10 (s + 20) = !Rule30Diagonals.D 8 (s + 19) :=
    Rule30LeftAntiPeriod.D_ten_succ_eq_not_D_eight (s + 19) (by omega)
  rw [h19, h22, Rule30LeftAntiPeriod.D_nineteen_eq_not_D_eight (s + 19) (by omega),
      Rule30LeftAntiPeriod.D_twenty_two_eq_D_ten (s + 22) (by omega), p1, p2, Bool.not_not]

/-- **Twenty-Two-Column Inward Period-3 Exclusion (`not_cell_periodic_three_at_col_le_neg_add_nineteen`):**
for every `T : Nat` and column `c ≤ -3` with `c ≤ -(T : Int) + 19` (i.e. `c ≤ -(T + 3) + 22`),
`¬ (∀ t : Nat, T ≤ t → cell (t + 3) c = cell t c)`. -/
theorem not_cell_periodic_three_at_col_le_neg_add_nineteen (T : Nat) {c : Int}
    (hc0 : c ≤ -3) (hc : c ≤ -(T : Int) + 19) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 3) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h := hper (s + 19) (by omega)
  have hflip := cell_neg_flip_nineteen_twenty_two s (by omega)
  rw [hc_eq, show s + 19 + 3 = s + 22 by omega, hflip] at h
  revert h; cases cell (s + 19) (-(s : Int)) <;> decide

/-- **Universal Lag-4 Column Flip at Ticks `s + 18` and `s + 22` (`cell_neg_flip_eighteen_twenty_two`):**
for every `s ≥ 3`, `cell (s + 22) (-(s : Int)) = !cell (s + 18) (-(s : Int))`. -/
theorem cell_neg_flip_eighteen_twenty_two (s : Nat) (hs : 3 ≤ s) :
    cell (s + 22) (-(s : Int)) = !cell (s + 18) (-(s : Int)) := by
  have h18 : cell (s + 18) (-(s : Int)) = Rule30Diagonals.D 18 (s + 18) := by
    unfold Rule30Diagonals.D; exact Rule30Diagonals.cell_congr (by omega)
  have h22 : cell (s + 22) (-(s : Int)) = Rule30Diagonals.D 22 (s + 22) := by
    unfold Rule30Diagonals.D; exact Rule30Diagonals.cell_congr (by omega)
  have p1 : Rule30Diagonals.D 10 (s + 20) = !Rule30Diagonals.D 10 (s + 18) :=
    Rule30LeftAntiPeriod.D_ten_antiperiodic_two (s + 18) (by omega)
  have p2 : Rule30Diagonals.D 10 (s + 22) = Rule30Diagonals.D 10 (s + 18) := by
    have h := Rule30LeftAntiPeriod.D_ten_antiperiodic_two (s + 20) (by omega)
    rw [show s + 20 + 2 = s + 22 by omega, p1, Bool.not_not] at h; exact h
  rw [h18, h22, Rule30LeftAntiPeriod.D_eighteen_eq_not_D_ten (s + 18) (by omega),
      Rule30LeftAntiPeriod.D_twenty_two_eq_D_ten (s + 22) (by omega), p2, Bool.not_not]

/-- **Twenty-Two-Column Inward Period-4 Exclusion (`not_cell_periodic_four_at_col_le_neg_add_eighteen`):**
for every `T : Nat` and column `c ≤ -3` with `c ≤ -(T : Int) + 18` (i.e. `c ≤ -(T + 4) + 22`),
`¬ (∀ t : Nat, T ≤ t → cell (t + 4) c = cell t c)`. -/
theorem not_cell_periodic_four_at_col_le_neg_add_eighteen (T : Nat) {c : Int}
    (hc0 : c ≤ -3) (hc : c ≤ -(T : Int) + 18) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 4) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h := hper (s + 18) (by omega)
  have hflip := cell_neg_flip_eighteen_twenty_two s (by omega)
  rw [hc_eq, show s + 18 + 4 = s + 22 by omega, hflip] at h
  revert h; cases cell (s + 18) (-(s : Int)) <;> decide

/-- **Universal Lag-5 Column Flip at Ticks `s + 20` and `s + 25` (`cell_neg_flip_twenty_twenty_five`):**
for every `s ≥ 3`, `cell (s + 25) (-(s : Int)) = !cell (s + 20) (-(s : Int))`. -/
theorem cell_neg_flip_twenty_twenty_five (s : Nat) (hs : 3 ≤ s) :
    cell (s + 25) (-(s : Int)) = !cell (s + 20) (-(s : Int)) := by
  have h20 : cell (s + 20) (-(s : Int)) = Rule30Diagonals.D 20 (s + 20) := by
    unfold Rule30Diagonals.D; exact Rule30Diagonals.cell_congr (by omega)
  have h25 : cell (s + 25) (-(s : Int)) = Rule30Diagonals.D 25 (s + 25) := by
    unfold Rule30Diagonals.D; exact Rule30Diagonals.cell_congr (by omega)
  have p1 : Rule30Diagonals.D 10 (s + 23) = !Rule30Diagonals.D 10 (s + 21) :=
    Rule30LeftAntiPeriod.D_ten_antiperiodic_two (s + 21) (by omega)
  have p2 : Rule30Diagonals.D 10 (s + 25) = Rule30Diagonals.D 10 (s + 21) := by
    have h := Rule30LeftAntiPeriod.D_ten_antiperiodic_two (s + 23) (by omega)
    rw [show s + 23 + 2 = s + 25 by omega, p1, Bool.not_not] at h; exact h
  have p3 : Rule30Diagonals.D 10 (s + 21) = !Rule30Diagonals.D 8 (s + 20) :=
    Rule30LeftAntiPeriod.D_ten_succ_eq_not_D_eight (s + 20) (by omega)
  rw [h20, h25, Rule30LeftAntiPeriod.D_twenty_eq_D_eight (s + 20) (by omega),
      Rule30LeftAntiPeriod.D_twenty_five_eq_D_ten (s + 25) (by omega), p2, p3]

/-- **Twenty-Five-Column Inward Period-5 Exclusion (`not_cell_periodic_five_at_col_le_neg_add_twenty`):**
for every `T : Nat` and column `c ≤ -3` with `c ≤ -(T : Int) + 20` (i.e. `c ≤ -(T + 5) + 25`),
`¬ (∀ t : Nat, T ≤ t → cell (t + 5) c = cell t c)`. -/
theorem not_cell_periodic_five_at_col_le_neg_add_twenty (T : Nat) {c : Int}
    (hc0 : c ≤ -3) (hc : c ≤ -(T : Int) + 20) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 5) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h := hper (s + 20) (by omega)
  have hflip := cell_neg_flip_twenty_twenty_five s (by omega)
  rw [hc_eq, show s + 20 + 5 = s + 25 by omega, hflip] at h
  revert h; cases cell (s + 20) (-(s : Int)) <;> decide

private theorem D_eight_periodic_four_local (t : Nat) (ht : 7 ≤ t) :
    Rule30Diagonals.D 8 (t + 4) = Rule30Diagonals.D 8 t := by
  have h1 := Rule30LeftAntiPeriod.D_eight_antiperiodic_two t ht
  have h2 := Rule30LeftAntiPeriod.D_eight_antiperiodic_two (t + 2) (by omega)
  rw [show t + 2 + 2 = t + 4 by omega, h1, Bool.not_not] at h2
  exact h2

private theorem D_ten_periodic_four_local (t : Nat) (ht : 9 ≤ t) :
    Rule30Diagonals.D 10 (t + 4) = Rule30Diagonals.D 10 t := by
  have h1 := Rule30LeftAntiPeriod.D_ten_antiperiodic_two t ht
  have h2 := Rule30LeftAntiPeriod.D_ten_antiperiodic_two (t + 2) (by omega)
  rw [show t + 2 + 2 = t + 4 by omega, h1, Bool.not_not] at h2
  exact h2

private theorem D_three_periodic_two_local (t : Nat) (ht : 2 ≤ t) :
    Rule30Diagonals.D 3 (t + 2) = Rule30Diagonals.D 3 t := by
  have h1 := Rule30WhiteSpacing.D_three_succ t ht
  have h2 := Rule30WhiteSpacing.D_three_succ (t + 1) (by omega)
  rw [show t + 1 + 1 = t + 2 by omega, h1, Bool.not_not] at h2
  exact h2

/-- **Universal Lag-9 Column Flip at Ticks `s + 17` and `s + 26` (`cell_neg_flip_seventeen_twenty_six`):**
for every `s ≥ 3`, `cell (s + 26) (-(s : Int)) = !cell (s + 17) (-(s : Int))`. -/
theorem cell_neg_flip_seventeen_twenty_six (s : Nat) (hs : 3 ≤ s) :
    cell (s + 26) (-(s : Int)) = !cell (s + 17) (-(s : Int)) := by
  have h17 : cell (s + 17) (-(s : Int)) = Rule30Diagonals.D 17 (s + 17) := by
    unfold Rule30Diagonals.D; exact Rule30Diagonals.cell_congr (by omega)
  have h26 : cell (s + 26) (-(s : Int)) = Rule30Diagonals.D 26 (s + 26) := by
    unfold Rule30Diagonals.D; exact Rule30Diagonals.cell_congr (by omega)
  have p8 : Rule30Diagonals.D 8 (s + 26) = Rule30Diagonals.D 10 (s + 17) := by
    calc Rule30Diagonals.D 8 (s + 26) = Rule30Diagonals.D 8 ((s + 22) + 4) := by rfl
      _ = Rule30Diagonals.D 8 (s + 22) := D_eight_periodic_four_local (s + 22) (by omega)
      _ = Rule30Diagonals.D 8 ((s + 18) + 4) := by rfl
      _ = Rule30Diagonals.D 8 (s + 18) := D_eight_periodic_four_local (s + 18) (by omega)
      _ = Rule30Diagonals.D 8 ((s + 17) + 1) := by rfl
      _ = Rule30Diagonals.D 10 (s + 17) := Rule30LeftAntiPeriod.D_eight_succ_eq_D_ten (s + 17) (by omega)
  have p10 : Rule30Diagonals.D 10 (s + 26) = !Rule30Diagonals.D 8 (s + 17) := by
    calc Rule30Diagonals.D 10 (s + 26) = Rule30Diagonals.D 10 ((s + 22) + 4) := by rfl
      _ = Rule30Diagonals.D 10 (s + 22) := D_ten_periodic_four_local (s + 22) (by omega)
      _ = Rule30Diagonals.D 10 ((s + 18) + 4) := by rfl
      _ = Rule30Diagonals.D 10 (s + 18) := D_ten_periodic_four_local (s + 18) (by omega)
      _ = Rule30Diagonals.D 10 ((s + 17) + 1) := by rfl
      _ = !Rule30Diagonals.D 8 (s + 17) := Rule30LeftAntiPeriod.D_ten_succ_eq_not_D_eight (s + 17) (by omega)
  rw [h17, h26, Rule30LeftAntiPeriod.D_seventeen_eq_not_D_eight_and_D_ten (s + 17) (by omega),
      Rule30LeftAntiPeriod.D_twenty_six_eq_nand_D_eight_D_ten (s + 26) (by omega), p8, p10]
  cases Rule30Diagonals.D 8 (s + 17) <;> cases Rule30Diagonals.D 10 (s + 17) <;> decide

/-- **Twenty-Six-Column Inward Period-9 Exclusion (`not_cell_periodic_nine_at_col_le_neg_add_seventeen`):**
for every `T : Nat` and column `c ≤ -3` with `c ≤ -(T : Int) + 17` (i.e. `c ≤ -(T + 9) + 26`),
`¬ (∀ t : Nat, T ≤ t → cell (t + 9) c = cell t c)`. -/
theorem not_cell_periodic_nine_at_col_le_neg_add_seventeen (T : Nat) {c : Int}
    (hc0 : c ≤ -3) (hc : c ≤ -(T : Int) + 17) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 9) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h := hper (s + 17) (by omega)
  have hflip := cell_neg_flip_seventeen_twenty_six s (by omega)
  rw [hc_eq, show s + 17 + 9 = s + 26 by omega, hflip] at h
  revert h; cases cell (s + 17) (-(s : Int)) <;> decide

/-- **Universal Lag-10 Column Flip at Ticks `s + 15` and `s + 25` (`cell_neg_flip_fifteen_twenty_five`):**
for every `s ≥ 3`, `cell (s + 25) (-(s : Int)) = !cell (s + 15) (-(s : Int))`. -/
theorem cell_neg_flip_fifteen_twenty_five (s : Nat) (hs : 3 ≤ s) :
    cell (s + 25) (-(s : Int)) = !cell (s + 15) (-(s : Int)) := by
  have h15 : cell (s + 15) (-(s : Int)) = Rule30Diagonals.D 15 (s + 15) := by
    unfold Rule30Diagonals.D; exact Rule30Diagonals.cell_congr (by omega)
  have h25 : cell (s + 25) (-(s : Int)) = Rule30Diagonals.D 25 (s + 25) := by
    unfold Rule30Diagonals.D; exact Rule30Diagonals.cell_congr (by omega)
  have p10 : Rule30Diagonals.D 10 (s + 25) = !Rule30Diagonals.D 10 (s + 15) := by
    calc Rule30Diagonals.D 10 (s + 25) = Rule30Diagonals.D 10 ((s + 21) + 4) := by rfl
      _ = Rule30Diagonals.D 10 (s + 21) := D_ten_periodic_four_local (s + 21) (by omega)
      _ = Rule30Diagonals.D 10 ((s + 17) + 4) := by rfl
      _ = Rule30Diagonals.D 10 (s + 17) := D_ten_periodic_four_local (s + 17) (by omega)
      _ = Rule30Diagonals.D 10 ((s + 15) + 2) := by rfl
      _ = !Rule30Diagonals.D 10 (s + 15) := Rule30LeftAntiPeriod.D_ten_antiperiodic_two (s + 15) (by omega)
  rw [h15, h25, Rule30LeftAntiPeriod.D_fifteen_eq_D_ten (s + 15) (by omega),
      Rule30LeftAntiPeriod.D_twenty_five_eq_D_ten (s + 25) (by omega), p10]

/-- **Twenty-Five-Column Inward Period-10 Exclusion (`not_cell_periodic_ten_at_col_le_neg_add_fifteen`):**
for every `T : Nat` and column `c ≤ -3` with `c ≤ -(T : Int) + 15` (i.e. `c ≤ -(T + 10) + 25`),
`¬ (∀ t : Nat, T ≤ t → cell (t + 10) c = cell t c)`. -/
theorem not_cell_periodic_ten_at_col_le_neg_add_fifteen (T : Nat) {c : Int}
    (hc0 : c ≤ -3) (hc : c ≤ -(T : Int) + 15) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 10) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h := hper (s + 15) (by omega)
  have hflip := cell_neg_flip_fifteen_twenty_five s (by omega)
  rw [hc_eq, show s + 15 + 10 = s + 25 by omega, hflip] at h
  revert h; cases cell (s + 15) (-(s : Int)) <;> decide

/-- **Universal Lag-17 Column Flip at Ticks `s + 8` and `s + 25` (`cell_neg_flip_eight_twenty_five`):**
for every `s ≥ 3`, `cell (s + 25) (-(s : Int)) = !cell (s + 8) (-(s : Int))`. -/
theorem cell_neg_flip_eight_twenty_five (s : Nat) (hs : 3 ≤ s) :
    cell (s + 25) (-(s : Int)) = !cell (s + 8) (-(s : Int)) := by
  have h8 : cell (s + 8) (-(s : Int)) = Rule30Diagonals.D 8 (s + 8) := by
    unfold Rule30Diagonals.D; exact Rule30Diagonals.cell_congr (by omega)
  have h25 : cell (s + 25) (-(s : Int)) = Rule30Diagonals.D 25 (s + 25) := by
    unfold Rule30Diagonals.D; exact Rule30Diagonals.cell_congr (by omega)
  have p10 : Rule30Diagonals.D 10 (s + 25) = !Rule30Diagonals.D 8 (s + 8) := by
    calc Rule30Diagonals.D 10 (s + 25) = Rule30Diagonals.D 10 ((s + 21) + 4) := by rfl
      _ = Rule30Diagonals.D 10 (s + 21) := D_ten_periodic_four_local (s + 21) (by omega)
      _ = Rule30Diagonals.D 10 ((s + 17) + 4) := by rfl
      _ = Rule30Diagonals.D 10 (s + 17) := D_ten_periodic_four_local (s + 17) (by omega)
      _ = Rule30Diagonals.D 10 ((s + 13) + 4) := by rfl
      _ = Rule30Diagonals.D 10 (s + 13) := D_ten_periodic_four_local (s + 13) (by omega)
      _ = Rule30Diagonals.D 10 ((s + 9) + 4) := by rfl
      _ = Rule30Diagonals.D 10 (s + 9) := D_ten_periodic_four_local (s + 9) (by omega)
      _ = Rule30Diagonals.D 10 ((s + 8) + 1) := by rfl
      _ = !Rule30Diagonals.D 8 (s + 8) := Rule30LeftAntiPeriod.D_ten_succ_eq_not_D_eight (s + 8) (by omega)
  rw [h8, h25, Rule30LeftAntiPeriod.D_twenty_five_eq_D_ten (s + 25) (by omega), p10]

/-- **Twenty-Five-Column Inward Period-17 Exclusion (`not_cell_periodic_seventeen_at_col_le_neg_add_eight`):**
for every `T : Nat` and column `c ≤ -3` with `c ≤ -(T : Int) + 8` (i.e. `c ≤ -(T + 17) + 25`),
`¬ (∀ t : Nat, T ≤ t → cell (t + 17) c = cell t c)`. -/
theorem not_cell_periodic_seventeen_at_col_le_neg_add_eight (T : Nat) {c : Int}
    (hc0 : c ≤ -3) (hc : c ≤ -(T : Int) + 8) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 17) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h := hper (s + 8) (by omega)
  have hflip := cell_neg_flip_eight_twenty_five s (by omega)
  rw [hc_eq, show s + 8 + 17 = s + 25 by omega, hflip] at h
  revert h; cases cell (s + 8) (-(s : Int)) <;> decide

/-- **Universal Lag-18 Column Flip at Ticks `s + 5` and `s + 23` (`cell_neg_flip_five_twenty_three`):**
for every `s ≥ 2`, `cell (s + 23) (-(s : Int)) = !cell (s + 5) (-(s : Int))`. -/
theorem cell_neg_flip_five_twenty_three (s : Nat) (hs : 2 ≤ s) :
    cell (s + 23) (-(s : Int)) = !cell (s + 5) (-(s : Int)) := by
  have h5 : cell (s + 5) (-(s : Int)) = Rule30Diagonals.D 5 (s + 5) := by
    unfold Rule30Diagonals.D; exact Rule30Diagonals.cell_congr (by omega)
  have h23 : cell (s + 23) (-(s : Int)) = Rule30Diagonals.D 23 (s + 23) := by
    unfold Rule30Diagonals.D; exact Rule30Diagonals.cell_congr (by omega)
  have p3 : Rule30Diagonals.D 3 (s + 23) = Rule30Diagonals.D 3 (s + 5) := by
    calc Rule30Diagonals.D 3 (s + 23) = Rule30Diagonals.D 3 ((s + 21) + 2) := by rfl
      _ = Rule30Diagonals.D 3 (s + 21) := D_three_periodic_two_local (s + 21) (by omega)
      _ = Rule30Diagonals.D 3 ((s + 19) + 2) := by rfl
      _ = Rule30Diagonals.D 3 (s + 19) := D_three_periodic_two_local (s + 19) (by omega)
      _ = Rule30Diagonals.D 3 ((s + 17) + 2) := by rfl
      _ = Rule30Diagonals.D 3 (s + 17) := D_three_periodic_two_local (s + 17) (by omega)
      _ = Rule30Diagonals.D 3 ((s + 15) + 2) := by rfl
      _ = Rule30Diagonals.D 3 (s + 15) := D_three_periodic_two_local (s + 15) (by omega)
      _ = Rule30Diagonals.D 3 ((s + 13) + 2) := by rfl
      _ = Rule30Diagonals.D 3 (s + 13) := D_three_periodic_two_local (s + 13) (by omega)
      _ = Rule30Diagonals.D 3 ((s + 11) + 2) := by rfl
      _ = Rule30Diagonals.D 3 (s + 11) := D_three_periodic_two_local (s + 11) (by omega)
      _ = Rule30Diagonals.D 3 ((s + 9) + 2) := by rfl
      _ = Rule30Diagonals.D 3 (s + 9) := D_three_periodic_two_local (s + 9) (by omega)
      _ = Rule30Diagonals.D 3 ((s + 7) + 2) := by rfl
      _ = Rule30Diagonals.D 3 (s + 7) := D_three_periodic_two_local (s + 7) (by omega)
      _ = Rule30Diagonals.D 3 ((s + 5) + 2) := by rfl
      _ = Rule30Diagonals.D 3 (s + 5) := D_three_periodic_two_local (s + 5) (by omega)
  rw [h5, h23, Rule30WhiteSpacing.D_five_eq_D_three (s + 5) (by omega),
      Rule30LeftAntiPeriod.D_twenty_three_eq_not_D_three (s + 23) (by omega), p3]

/-- **Twenty-Three-Column Inward Period-18 Exclusion (`not_cell_periodic_eighteen_at_col_le_neg_add_five`):**
for every `T : Nat` and column `c ≤ -2` with `c ≤ -(T : Int) + 5` (i.e. `c ≤ -(T + 18) + 23`),
`¬ (∀ t : Nat, T ≤ t → cell (t + 18) c = cell t c)`. -/
theorem not_cell_periodic_eighteen_at_col_le_neg_add_five (T : Nat) {c : Int}
    (hc0 : c ≤ -2) (hc : c ≤ -(T : Int) + 5) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 18) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h := hper (s + 5) (by omega)
  have hflip := cell_neg_flip_five_twenty_three s (by omega)
  rw [hc_eq, show s + 5 + 18 = s + 23 by omega, hflip] at h
  revert h; cases cell (s + 5) (-(s : Int)) <;> decide

/-- **Universal Lag-20 Column Flip at Ticks `s + 3` and `s + 23` (`cell_neg_flip_three_twenty_three`):**
for every `s ≥ 2`, `cell (s + 23) (-(s : Int)) = !cell (s + 3) (-(s : Int))`. -/
theorem cell_neg_flip_three_twenty_three (s : Nat) (hs : 2 ≤ s) :
    cell (s + 23) (-(s : Int)) = !cell (s + 3) (-(s : Int)) := by
  have h3 : cell (s + 3) (-(s : Int)) = Rule30Diagonals.D 3 (s + 3) := by
    unfold Rule30Diagonals.D; exact Rule30Diagonals.cell_congr (by omega)
  have h5 : cell (s + 5) (-(s : Int)) = Rule30Diagonals.D 5 (s + 5) := by
    unfold Rule30Diagonals.D; exact Rule30Diagonals.cell_congr (by omega)
  have h53 : cell (s + 5) (-(s : Int)) = cell (s + 3) (-(s : Int)) := by
    rw [h5, h3, Rule30WhiteSpacing.D_five_eq_D_three (s + 5) (by omega)]
    exact D_three_periodic_two_local (s + 3) (by omega)
  rw [← h53]
  exact cell_neg_flip_five_twenty_three s hs

/-- **Twenty-Three-Column Inward Period-20 Exclusion (`not_cell_periodic_twenty_at_col_le_neg_add_three`):**
for every `T : Nat` and column `c ≤ -2` with `c ≤ -(T : Int) + 3` (i.e. `c ≤ -(T + 20) + 23`),
`¬ (∀ t : Nat, T ≤ t → cell (t + 20) c = cell t c)`. -/
theorem not_cell_periodic_twenty_at_col_le_neg_add_three (T : Nat) {c : Int}
    (hc0 : c ≤ -2) (hc : c ≤ -(T : Int) + 3) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 20) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h := hper (s + 3) (by omega)
  have hflip := cell_neg_flip_three_twenty_three s (by omega)
  rw [hc_eq, show s + 3 + 20 = s + 23 by omega, hflip] at h
  revert h; cases cell (s + 3) (-(s : Int)) <;> decide

/-- **Twenty-Eight-Column Inward Period-19 Exclusion (`not_cell_periodic_nineteen_at_col_le_neg_add_nine`):**
for every `T : Nat` and column `c ≤ -3` with `c ≤ -(T : Int) + 9` (i.e. `c ≤ -(T + 19) + 28`),
`¬ (∀ t : Nat, T ≤ t → cell (t + 19) c = cell t c)`. -/
theorem not_cell_periodic_nineteen_at_col_le_neg_add_nine (T : Nat) {c : Int}
    (hc0 : c ≤ -3) (hc : c ≤ -(T : Int) + 9) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 19) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h9 : cell (s + 9) (-(s : Int)) = true := by
    have hd : cell (s + 9) (-(s : Int)) = Rule30Diagonals.D 9 (s + 9) := by
      unfold Rule30Diagonals.D; exact Rule30Diagonals.cell_congr (by omega)
    rw [hd, Rule30LeftAntiPeriod.D_nine_eq_true (s + 9) (by omega)]
  have h28 : cell (s + 28) (-(s : Int)) = false := by
    have hd : cell (s + 28) (-(s : Int)) = Rule30Diagonals.D 28 (s + 28) := by
      unfold Rule30Diagonals.D; exact Rule30Diagonals.cell_congr (by omega)
    rw [hd, Rule30LeftAntiPeriod.D_twenty_eight_eq_false (s + 28) (by omega)]
  have h := hper (s + 9) (by omega)
  rw [hc_eq, show s + 9 + 19 = s + 28 by omega, h28, h9] at h
  cases h

/-- **Thirty-Column Inward Period-23 Exclusion (`not_cell_periodic_twenty_three_at_col_le_neg_add_seven`):**
for every `T : Nat` and column `c ≤ -3` with `c ≤ -(T : Int) + 7` (i.e. `c ≤ -(T + 23) + 30`),
`¬ (∀ t : Nat, T ≤ t → cell (t + 23) c = cell t c)`. -/
theorem not_cell_periodic_twenty_three_at_col_le_neg_add_seven (T : Nat) {c : Int}
    (hc0 : c ≤ -3) (hc : c ≤ -(T : Int) + 7) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 23) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h7 : cell (s + 7) (-(s : Int)) = false := by
    have hd : cell (s + 7) (-(s : Int)) = Rule30Diagonals.D 7 (s + 7) := by
      unfold Rule30Diagonals.D; exact Rule30Diagonals.cell_congr (by omega)
    rw [hd, Rule30WhiteSpacing.D_seven_eq_false (s + 7) (by omega)]
  have h30 : cell (s + 30) (-(s : Int)) = true := by
    have hd : cell (s + 30) (-(s : Int)) = Rule30Diagonals.D 30 (s + 30) := by
      unfold Rule30Diagonals.D; exact Rule30Diagonals.cell_congr (by omega)
    rw [hd, Rule30LeftAntiPeriod.D_thirty_eq_true (s + 30) (by omega)]
  have h := hper (s + 7) (by omega)
  rw [hc_eq, show s + 7 + 23 = s + 30 by omega, h30, h7] at h
  cases h

/-- **Twenty-Eight-Column Inward Period-24 Exclusion (`not_cell_periodic_twenty_four_at_col_le_neg_add_four`):**
for every `T : Nat` and column `c ≤ -3` with `c ≤ -(T : Int) + 4` (i.e. `c ≤ -(T + 24) + 28`),
`¬ (∀ t : Nat, T ≤ t → cell (t + 24) c = cell t c)`. -/
theorem not_cell_periodic_twenty_four_at_col_le_neg_add_four (T : Nat) {c : Int}
    (hc0 : c ≤ -3) (hc : c ≤ -(T : Int) + 4) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 24) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h4 : cell (s + 4) (-(s : Int)) = true := by
    have hd : cell (s + 4) (-(s : Int)) = Rule30Diagonals.D 4 (s + 4) := by
      unfold Rule30Diagonals.D; exact Rule30Diagonals.cell_congr (by omega)
    rw [hd, Rule30WhiteSpacing.D_four_eq_true (s + 4) (by omega)]
  have h28 : cell (s + 28) (-(s : Int)) = false := by
    have hd : cell (s + 28) (-(s : Int)) = Rule30Diagonals.D 28 (s + 28) := by
      unfold Rule30Diagonals.D; exact Rule30Diagonals.cell_congr (by omega)
    rw [hd, Rule30LeftAntiPeriod.D_twenty_eight_eq_false (s + 28) (by omega)]
  have h := hper (s + 4) (by omega)
  rw [hc_eq, show s + 4 + 24 = s + 28 by omega, h28, h4] at h
  cases h

/-- **Twenty-Eight-Column Inward Period-27 Exclusion (`not_cell_periodic_twenty_seven_at_col_le_neg_add_one`):**
for every `T : Nat` and column `c ≤ -3` with `c ≤ -(T : Int) + 1` (i.e. `c ≤ -(T + 27) + 28`),
`¬ (∀ t : Nat, T ≤ t → cell (t + 27) c = cell t c)`. -/
theorem not_cell_periodic_twenty_seven_at_col_le_neg_add_one (T : Nat) {c : Int}
    (hc0 : c ≤ -3) (hc : c ≤ -(T : Int) + 1) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 27) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h1 : cell (s + 1) (-(s : Int)) = true := by
    have hd : cell (s + 1) (-(s : Int)) = Rule30Diagonals.D 1 (s + 1) := by
      unfold Rule30Diagonals.D; exact Rule30Diagonals.cell_congr (by omega)
    rw [hd, Rule30Diagonals.D_one s]
  have h28 : cell (s + 28) (-(s : Int)) = false := by
    have hd : cell (s + 28) (-(s : Int)) = Rule30Diagonals.D 28 (s + 28) := by
      unfold Rule30Diagonals.D; exact Rule30Diagonals.cell_congr (by omega)
    rw [hd, Rule30LeftAntiPeriod.D_twenty_eight_eq_false (s + 28) (by omega)]
  have h := hper (s + 1) (by omega)
  rw [hc_eq, show s + 1 + 27 = s + 28 by omega, h28, h1] at h
  cases h

/-- **Thirty-Column Inward Period-28 Exclusion (`not_cell_periodic_twenty_eight_at_col_le_neg_add_two`):**
for every `T : Nat` and column `c ≤ -3` with `c ≤ -(T : Int) + 2` (i.e. `c ≤ -(T + 28) + 30`),
`¬ (∀ t : Nat, T ≤ t → cell (t + 28) c = cell t c)`. -/
theorem not_cell_periodic_twenty_eight_at_col_le_neg_add_two (T : Nat) {c : Int}
    (hc0 : c ≤ -3) (hc : c ≤ -(T : Int) + 2) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 28) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h2 : cell (s + 2) (-(s : Int)) = false := by
    have hd : cell (s + 2) (-(s : Int)) = Rule30Diagonals.D 2 (s + 2) := by
      unfold Rule30Diagonals.D; exact Rule30Diagonals.cell_congr (by omega)
    rw [hd, Rule30WhiteSpacing.D_two_eq_false (s + 2) (by omega)]
  have h30 : cell (s + 30) (-(s : Int)) = true := by
    have hd : cell (s + 30) (-(s : Int)) = Rule30Diagonals.D 30 (s + 30) := by
      unfold Rule30Diagonals.D; exact Rule30Diagonals.cell_congr (by omega)
    rw [hd, Rule30LeftAntiPeriod.D_thirty_eq_true (s + 30) (by omega)]
  have h := hper (s + 2) (by omega)
  rw [hc_eq, show s + 2 + 28 = s + 30 by omega, h30, h2] at h
  cases h

section Inward18Closure
open Rule30Diagonals Rule30WhiteSpacing Rule30LeftAntiPeriod

/-! ### 5. Column Arrival Table in Terms of `(D 8 (s + 8), D 10 (s + 8))` and All-Period 18-Column Closure -/

private theorem D_three_eq_xor_D_eight_D_ten (t : Nat) (ht : 9 ≤ t) : D 3 t = xor (D 8 t) (D 10 t) := by
  have h1 := D_eight_step_eq_xor_D_three t (by omega)
  have h2 := D_eight_succ_eq_D_ten t ht
  rw [h2] at h1; revert h1; cases D 3 t <;> cases D 8 t <;> cases D 10 t <;> decide

private theorem d3_s_3 (s : Nat) (hs : 1 ≤ s) : D 3 (s + 3) = !xor (D 8 (s + 8)) (D 10 (s + 8)) := by
  have h8 : D 3 (s + 8) = xor (D 8 (s + 8)) (D 10 (s + 8)) := D_three_eq_xor_D_eight_D_ten (s + 8) (by omega)
  have p1 : D 3 (s + 8) = D 3 (s + 6) := D_three_periodic_two_local (s + 6) (by omega)
  have p2 : D 3 (s + 6) = D 3 (s + 4) := D_three_periodic_two_local (s + 4) (by omega)
  have p3 : D 3 (s + 4) = !D 3 (s + 3) := D_three_succ (s + 3) (by omega)
  rw [p1, p2, p3] at h8; revert h8; cases D 3 (s + 3) <;> cases xor (D 8 (s + 8)) (D 10 (s + 8)) <;> decide

private theorem d3_s_5 (s : Nat) (hs : 1 ≤ s) : D 3 (s + 5) = !xor (D 8 (s + 8)) (D 10 (s + 8)) := by
  rw [show s + 5 = (s + 3) + 2 by omega, D_three_periodic_two_local (s + 3) (by omega), d3_s_3 s hs]
private theorem d3_s_6 (s : Nat) (hs : 1 ≤ s) : D 3 (s + 6) = xor (D 8 (s + 8)) (D 10 (s + 8)) := by
  rw [show s + 6 = (s + 5) + 1 by omega, D_three_succ (s + 5) (by omega), d3_s_5 s hs, Bool.not_not]

private theorem d8_s_8 (s : Nat) : D 8 (s + 8) = D 8 (s + 8) := rfl
private theorem d10_s_8 (s : Nat) : D 10 (s + 8) = D 10 (s + 8) := rfl
private theorem d8_s_9 (s : Nat) (hs : 1 ≤ s) : D 8 (s + 9) = D 10 (s + 8) := by
  rw [show s + 9 = (s + 8) + 1 by omega, D_eight_succ_eq_D_ten (s + 8) (by omega), d10_s_8 s]
private theorem d10_s_9 (s : Nat) (hs : 1 ≤ s) : D 10 (s + 9) = !D 8 (s + 8) := by
  rw [show s + 9 = (s + 8) + 1 by omega, D_ten_succ_eq_not_D_eight (s + 8) (by omega), d8_s_8 s]
private theorem d8_s_10 (s : Nat) (hs : 1 ≤ s) : D 8 (s + 10) = !D 8 (s + 8) := by
  rw [show s + 10 = (s + 9) + 1 by omega, D_eight_succ_eq_D_ten (s + 9) (by omega), d10_s_9 s hs]
private theorem d10_s_10 (s : Nat) (hs : 1 ≤ s) : D 10 (s + 10) = !D 10 (s + 8) := by
  rw [show s + 10 = (s + 9) + 1 by omega, D_ten_succ_eq_not_D_eight (s + 9) (by omega), d8_s_9 s hs]
private theorem d8_s_11 (s : Nat) (hs : 1 ≤ s) : D 8 (s + 11) = !D 10 (s + 8) := by
  rw [show s + 11 = (s + 10) + 1 by omega, D_eight_succ_eq_D_ten (s + 10) (by omega), d10_s_10 s hs]
private theorem d10_s_11 (s : Nat) (hs : 1 ≤ s) : D 10 (s + 11) = D 8 (s + 8) := by
  rw [show s + 11 = (s + 10) + 1 by omega, D_ten_succ_eq_not_D_eight (s + 10) (by omega), d8_s_10 s hs, Bool.not_not]
private theorem d8_s_12 (s : Nat) (hs : 1 ≤ s) : D 8 (s + 12) = D 8 (s + 8) := by
  rw [show s + 12 = (s + 11) + 1 by omega, D_eight_succ_eq_D_ten (s + 11) (by omega), d10_s_11 s hs]
private theorem d10_s_12 (s : Nat) (hs : 1 ≤ s) : D 10 (s + 12) = D 10 (s + 8) := by
  rw [show s + 12 = (s + 11) + 1 by omega, D_ten_succ_eq_not_D_eight (s + 11) (by omega), d8_s_11 s hs, Bool.not_not]
private theorem d8_s_13 (s : Nat) (hs : 1 ≤ s) : D 8 (s + 13) = D 10 (s + 8) := by
  rw [show s + 13 = (s + 12) + 1 by omega, D_eight_succ_eq_D_ten (s + 12) (by omega), d10_s_12 s hs]
private theorem d10_s_13 (s : Nat) (hs : 1 ≤ s) : D 10 (s + 13) = !D 8 (s + 8) := by
  rw [show s + 13 = (s + 12) + 1 by omega, D_ten_succ_eq_not_D_eight (s + 12) (by omega), d8_s_12 s hs]
private theorem d8_s_14 (s : Nat) (hs : 1 ≤ s) : D 8 (s + 14) = !D 8 (s + 8) := by
  rw [show s + 14 = (s + 13) + 1 by omega, D_eight_succ_eq_D_ten (s + 13) (by omega), d10_s_13 s hs]
private theorem d10_s_14 (s : Nat) (hs : 1 ≤ s) : D 10 (s + 14) = !D 10 (s + 8) := by
  rw [show s + 14 = (s + 13) + 1 by omega, D_ten_succ_eq_not_D_eight (s + 13) (by omega), d8_s_13 s hs]
private theorem d8_s_15 (s : Nat) (hs : 1 ≤ s) : D 8 (s + 15) = !D 10 (s + 8) := by
  rw [show s + 15 = (s + 14) + 1 by omega, D_eight_succ_eq_D_ten (s + 14) (by omega), d10_s_14 s hs]
private theorem d10_s_15 (s : Nat) (hs : 1 ≤ s) : D 10 (s + 15) = D 8 (s + 8) := by
  rw [show s + 15 = (s + 14) + 1 by omega, D_ten_succ_eq_not_D_eight (s + 14) (by omega), d8_s_14 s hs, Bool.not_not]
private theorem d8_s_16 (s : Nat) (hs : 1 ≤ s) : D 8 (s + 16) = D 8 (s + 8) := by
  rw [show s + 16 = (s + 15) + 1 by omega, D_eight_succ_eq_D_ten (s + 15) (by omega), d10_s_15 s hs]
private theorem d10_s_16 (s : Nat) (hs : 1 ≤ s) : D 10 (s + 16) = D 10 (s + 8) := by
  rw [show s + 16 = (s + 15) + 1 by omega, D_ten_succ_eq_not_D_eight (s + 15) (by omega), d8_s_15 s hs, Bool.not_not]
private theorem d8_s_17 (s : Nat) (hs : 1 ≤ s) : D 8 (s + 17) = D 10 (s + 8) := by
  rw [show s + 17 = (s + 16) + 1 by omega, D_eight_succ_eq_D_ten (s + 16) (by omega), d10_s_16 s hs]
private theorem d10_s_17 (s : Nat) (hs : 1 ≤ s) : D 10 (s + 17) = !D 8 (s + 8) := by
  rw [show s + 17 = (s + 16) + 1 by omega, D_ten_succ_eq_not_D_eight (s + 16) (by omega), d8_s_16 s hs]
private theorem d8_s_18 (s : Nat) (hs : 1 ≤ s) : D 8 (s + 18) = !D 8 (s + 8) := by
  rw [show s + 18 = (s + 17) + 1 by omega, D_eight_succ_eq_D_ten (s + 17) (by omega), d10_s_17 s hs]
private theorem d10_s_18 (s : Nat) (hs : 1 ≤ s) : D 10 (s + 18) = !D 10 (s + 8) := by
  rw [show s + 18 = (s + 17) + 1 by omega, D_ten_succ_eq_not_D_eight (s + 17) (by omega), d8_s_17 s hs]
private theorem d8_s_19 (s : Nat) (hs : 1 ≤ s) : D 8 (s + 19) = !D 10 (s + 8) := by
  rw [show s + 19 = (s + 18) + 1 by omega, D_eight_succ_eq_D_ten (s + 18) (by omega), d10_s_18 s hs]
private theorem d10_s_19 (s : Nat) (hs : 1 ≤ s) : D 10 (s + 19) = D 8 (s + 8) := by
  rw [show s + 19 = (s + 18) + 1 by omega, D_ten_succ_eq_not_D_eight (s + 18) (by omega), d8_s_18 s hs, Bool.not_not]
private theorem d8_s_20 (s : Nat) (hs : 1 ≤ s) : D 8 (s + 20) = D 8 (s + 8) := by
  rw [show s + 20 = (s + 19) + 1 by omega, D_eight_succ_eq_D_ten (s + 19) (by omega), d10_s_19 s hs]
private theorem d10_s_20 (s : Nat) (hs : 1 ≤ s) : D 10 (s + 20) = D 10 (s + 8) := by
  rw [show s + 20 = (s + 19) + 1 by omega, D_ten_succ_eq_not_D_eight (s + 19) (by omega), d8_s_19 s hs, Bool.not_not]
private theorem d8_s_21 (s : Nat) (hs : 1 ≤ s) : D 8 (s + 21) = D 10 (s + 8) := by
  rw [show s + 21 = (s + 20) + 1 by omega, D_eight_succ_eq_D_ten (s + 20) (by omega), d10_s_20 s hs]
private theorem d10_s_21 (s : Nat) (hs : 1 ≤ s) : D 10 (s + 21) = !D 8 (s + 8) := by
  rw [show s + 21 = (s + 20) + 1 by omega, D_ten_succ_eq_not_D_eight (s + 20) (by omega), d8_s_20 s hs]
private theorem d8_s_22 (s : Nat) (hs : 1 ≤ s) : D 8 (s + 22) = !D 8 (s + 8) := by
  rw [show s + 22 = (s + 21) + 1 by omega, D_eight_succ_eq_D_ten (s + 21) (by omega), d10_s_21 s hs]
private theorem d10_s_22 (s : Nat) (hs : 1 ≤ s) : D 10 (s + 22) = !D 10 (s + 8) := by
  rw [show s + 22 = (s + 21) + 1 by omega, D_ten_succ_eq_not_D_eight (s + 21) (by omega), d8_s_21 s hs]
private theorem d8_s_23 (s : Nat) (hs : 1 ≤ s) : D 8 (s + 23) = !D 10 (s + 8) := by
  rw [show s + 23 = (s + 22) + 1 by omega, D_eight_succ_eq_D_ten (s + 22) (by omega), d10_s_22 s hs]
private theorem d10_s_23 (s : Nat) (hs : 1 ≤ s) : D 10 (s + 23) = D 8 (s + 8) := by
  rw [show s + 23 = (s + 22) + 1 by omega, D_ten_succ_eq_not_D_eight (s + 22) (by omega), d8_s_22 s hs, Bool.not_not]
private theorem d8_s_24 (s : Nat) (hs : 1 ≤ s) : D 8 (s + 24) = D 8 (s + 8) := by
  rw [show s + 24 = (s + 23) + 1 by omega, D_eight_succ_eq_D_ten (s + 23) (by omega), d10_s_23 s hs]
private theorem d10_s_24 (s : Nat) (hs : 1 ≤ s) : D 10 (s + 24) = D 10 (s + 8) := by
  rw [show s + 24 = (s + 23) + 1 by omega, D_ten_succ_eq_not_D_eight (s + 23) (by omega), d8_s_23 s hs, Bool.not_not]
private theorem d8_s_25 (s : Nat) (hs : 1 ≤ s) : D 8 (s + 25) = D 10 (s + 8) := by
  rw [show s + 25 = (s + 24) + 1 by omega, D_eight_succ_eq_D_ten (s + 24) (by omega), d10_s_24 s hs]
private theorem d10_s_25 (s : Nat) (hs : 1 ≤ s) : D 10 (s + 25) = !D 8 (s + 8) := by
  rw [show s + 25 = (s + 24) + 1 by omega, D_ten_succ_eq_not_D_eight (s + 24) (by omega), d8_s_24 s hs]
private theorem d8_s_26 (s : Nat) (hs : 1 ≤ s) : D 8 (s + 26) = !D 8 (s + 8) := by
  rw [show s + 26 = (s + 25) + 1 by omega, D_eight_succ_eq_D_ten (s + 25) (by omega), d10_s_25 s hs]
private theorem d10_s_26 (s : Nat) (hs : 1 ≤ s) : D 10 (s + 26) = !D 10 (s + 8) := by
  rw [show s + 26 = (s + 25) + 1 by omega, D_ten_succ_eq_not_D_eight (s + 25) (by omega), d8_s_25 s hs]
private theorem d8_s_27 (s : Nat) (hs : 1 ≤ s) : D 8 (s + 27) = !D 10 (s + 8) := by
  rw [show s + 27 = (s + 26) + 1 by omega, D_eight_succ_eq_D_ten (s + 26) (by omega), d10_s_26 s hs]
private theorem d10_s_27 (s : Nat) (hs : 1 ≤ s) : D 10 (s + 27) = D 8 (s + 8) := by
  rw [show s + 27 = (s + 26) + 1 by omega, D_ten_succ_eq_not_D_eight (s + 26) (by omega), d8_s_26 s hs, Bool.not_not]
private theorem col_at_0 (s : Nat) (_hs : 3 ≤ s) : cell (s + 0) (-(s : Int)) = true := by
  have hd : cell (s + 0) (-(s : Int)) = D 0 (s + 0) := by unfold D; exact cell_congr (by omega)
  rw [hd, D_zero (s + 0)]
private theorem col_at_1 (s : Nat) (_hs : 3 ≤ s) : cell (s + 1) (-(s : Int)) = true := by
  have hd : cell (s + 1) (-(s : Int)) = D 1 (s + 1) := by unfold D; exact cell_congr (by omega)
  rw [hd, D_one s]
private theorem col_at_2 (s : Nat) (_hs : 3 ≤ s) : cell (s + 2) (-(s : Int)) = false := by
  have hd : cell (s + 2) (-(s : Int)) = D 2 (s + 2) := by unfold D; exact cell_congr (by omega)
  rw [hd, D_two_eq_false (s + 2) (by omega)]
private theorem col_at_3 (s : Nat) (_hs : 3 ≤ s) : cell (s + 3) (-(s : Int)) = !xor (D 8 (s + 8)) (D 10 (s + 8)) := by
  have hd : cell (s + 3) (-(s : Int)) = D 3 (s + 3) := by unfold D; exact cell_congr (by omega)
  rw [hd, d3_s_3 s (by omega)]
private theorem col_at_4 (s : Nat) (_hs : 3 ≤ s) : cell (s + 4) (-(s : Int)) = true := by
  have hd : cell (s + 4) (-(s : Int)) = D 4 (s + 4) := by unfold D; exact cell_congr (by omega)
  rw [hd, D_four_eq_true (s + 4) (by omega)]
private theorem col_at_5 (s : Nat) (_hs : 3 ≤ s) : cell (s + 5) (-(s : Int)) = !xor (D 8 (s + 8)) (D 10 (s + 8)) := by
  have hd : cell (s + 5) (-(s : Int)) = D 5 (s + 5) := by unfold D; exact cell_congr (by omega)
  rw [hd, Rule30WhiteSpacing.D_five_eq_D_three (s + 5) (by omega), d3_s_5 s (by omega)]
private theorem col_at_6 (s : Nat) (_hs : 3 ≤ s) : cell (s + 6) (-(s : Int)) = xor (D 8 (s + 8)) (D 10 (s + 8)) := by
  have hd : cell (s + 6) (-(s : Int)) = D 6 (s + 6) := by unfold D; exact cell_congr (by omega)
  rw [hd, D_six_eq_D_three (s + 6) (by omega), d3_s_6 s (by omega)]
private theorem col_at_7 (s : Nat) (_hs : 3 ≤ s) : cell (s + 7) (-(s : Int)) = false := by
  have hd : cell (s + 7) (-(s : Int)) = D 7 (s + 7) := by unfold D; exact cell_congr (by omega)
  rw [hd, D_seven_eq_false (s + 7) (by omega)]
private theorem col_at_8 (s : Nat) (_hs : 3 ≤ s) : cell (s + 8) (-(s : Int)) = D 8 (s + 8) := by
  have hd : cell (s + 8) (-(s : Int)) = D 8 (s + 8) := by unfold D; exact cell_congr (by omega)
  rw [hd]
private theorem col_at_9 (s : Nat) (_hs : 3 ≤ s) : cell (s + 9) (-(s : Int)) = true := by
  have hd : cell (s + 9) (-(s : Int)) = D 9 (s + 9) := by unfold D; exact cell_congr (by omega)
  rw [hd, D_nine_eq_true (s + 9) (by omega)]
private theorem col_at_10 (s : Nat) (_hs : 3 ≤ s) : cell (s + 10) (-(s : Int)) = !D 10 (s + 8) := by
  have hd : cell (s + 10) (-(s : Int)) = D 10 (s + 10) := by unfold D; exact cell_congr (by omega)
  rw [hd, d10_s_10 s (by omega)]
private theorem col_at_11 (s : Nat) (_hs : 3 ≤ s) : cell (s + 11) (-(s : Int)) = !(!D 10 (s + 8) || D 8 (s + 8)) := by
  have hd : cell (s + 11) (-(s : Int)) = D 11 (s + 11) := by unfold D; exact cell_congr (by omega)
  rw [hd, D_eleven_eq_nor_D_eight_D_ten (s + 11) (by omega), d8_s_11 s (by omega), d10_s_11 s (by omega)]
private theorem col_at_12 (s : Nat) (_hs : 3 ≤ s) : cell (s + 12) (-(s : Int)) = !(D 8 (s + 8) && D 10 (s + 8)) := by
  have hd : cell (s + 12) (-(s : Int)) = D 12 (s + 12) := by unfold D; exact cell_congr (by omega)
  rw [hd, D_twelve_eq_nand_D_eight_D_ten (s + 12) (by omega), d8_s_12 s (by omega), d10_s_12 s (by omega)]
private theorem col_at_13 (s : Nat) (_hs : 3 ≤ s) : cell (s + 13) (-(s : Int)) = (D 10 (s + 8) || !!D 8 (s + 8)) := by
  have hd : cell (s + 13) (-(s : Int)) = D 13 (s + 13) := by unfold D; exact cell_congr (by omega)
  rw [hd, D_thirteen_eq_or_not_D_eight_D_ten (s + 13) (by omega), d8_s_13 s (by omega), d10_s_13 s (by omega)]
private theorem col_at_14 (s : Nat) (_hs : 3 ≤ s) : cell (s + 14) (-(s : Int)) = !D 8 (s + 8) := by
  have hd : cell (s + 14) (-(s : Int)) = D 14 (s + 14) := by unfold D; exact cell_congr (by omega)
  rw [hd, D_fourteen_eq_D_eight (s + 14) (by omega), d8_s_14 s (by omega)]
private theorem col_at_15 (s : Nat) (_hs : 3 ≤ s) : cell (s + 15) (-(s : Int)) = D 8 (s + 8) := by
  have hd : cell (s + 15) (-(s : Int)) = D 15 (s + 15) := by unfold D; exact cell_congr (by omega)
  rw [hd, D_fifteen_eq_D_ten (s + 15) (by omega), d10_s_15 s (by omega)]
private theorem col_at_16 (s : Nat) (_hs : 3 ≤ s) : cell (s + 16) (-(s : Int)) = (!D 8 (s + 8) || D 10 (s + 8)) := by
  have hd : cell (s + 16) (-(s : Int)) = D 16 (s + 16) := by unfold D; exact cell_congr (by omega)
  rw [hd, D_sixteen_eq_not_D_eight_or_D_ten (s + 16) (by omega), d8_s_16 s (by omega), d10_s_16 s (by omega)]
private theorem col_at_17 (s : Nat) (_hs : 3 ≤ s) : cell (s + 17) (-(s : Int)) = (!D 10 (s + 8) && !D 8 (s + 8)) := by
  have hd : cell (s + 17) (-(s : Int)) = D 17 (s + 17) := by unfold D; exact cell_congr (by omega)
  rw [hd, D_seventeen_eq_not_D_eight_and_D_ten (s + 17) (by omega), d8_s_17 s (by omega), d10_s_17 s (by omega)]
private theorem col_at_18 (s : Nat) (_hs : 3 ≤ s) : cell (s + 18) (-(s : Int)) = !!D 10 (s + 8) := by
  have hd : cell (s + 18) (-(s : Int)) = D 18 (s + 18) := by unfold D; exact cell_congr (by omega)
  rw [hd, D_eighteen_eq_not_D_ten (s + 18) (by omega), d10_s_18 s (by omega)]
private theorem col_at_19 (s : Nat) (_hs : 3 ≤ s) : cell (s + 19) (-(s : Int)) = !!D 10 (s + 8) := by
  have hd : cell (s + 19) (-(s : Int)) = D 19 (s + 19) := by unfold D; exact cell_congr (by omega)
  rw [hd, D_nineteen_eq_not_D_eight (s + 19) (by omega), d8_s_19 s (by omega)]
private theorem col_at_20 (s : Nat) (_hs : 3 ≤ s) : cell (s + 20) (-(s : Int)) = D 8 (s + 8) := by
  have hd : cell (s + 20) (-(s : Int)) = D 20 (s + 20) := by unfold D; exact cell_congr (by omega)
  rw [hd, D_twenty_eq_D_eight (s + 20) (by omega), d8_s_20 s (by omega)]
private theorem col_at_21 (s : Nat) (_hs : 3 ≤ s) : cell (s + 21) (-(s : Int)) = (D 10 (s + 8) || !!D 8 (s + 8)) := by
  have hd : cell (s + 21) (-(s : Int)) = D 21 (s + 21) := by unfold D; exact cell_congr (by omega)
  rw [hd, D_twenty_one_eq_D_eight_or_not_D_ten (s + 21) (by omega), d8_s_21 s (by omega), d10_s_21 s (by omega)]
private theorem col_at_22 (s : Nat) (_hs : 3 ≤ s) : cell (s + 22) (-(s : Int)) = !D 10 (s + 8) := by
  have hd : cell (s + 22) (-(s : Int)) = D 22 (s + 22) := by unfold D; exact cell_congr (by omega)
  rw [hd, D_twenty_two_eq_D_ten (s + 22) (by omega), d10_s_22 s (by omega)]
private theorem col_at_23 (s : Nat) (_hs : 3 ≤ s) : cell (s + 23) (-(s : Int)) = !xor (!D 10 (s + 8)) (D 8 (s + 8)) := by
  have hd : cell (s + 23) (-(s : Int)) = D 23 (s + 23) := by unfold D; exact cell_congr (by omega)
  rw [hd, D_twenty_three_eq_not_xor_D_eight_D_ten (s + 23) (by omega), d8_s_23 s (by omega), d10_s_23 s (by omega)]
private theorem col_at_24 (s : Nat) (_hs : 3 ≤ s) : cell (s + 24) (-(s : Int)) = (!D 8 (s + 8) && D 10 (s + 8)) := by
  have hd : cell (s + 24) (-(s : Int)) = D 24 (s + 24) := by unfold D; exact cell_congr (by omega)
  rw [hd, D_twenty_four_eq_not_D_eight_and_D_ten (s + 24) (by omega), d8_s_24 s (by omega), d10_s_24 s (by omega)]
private theorem col_at_25 (s : Nat) (_hs : 3 ≤ s) : cell (s + 25) (-(s : Int)) = !D 8 (s + 8) := by
  have hd : cell (s + 25) (-(s : Int)) = D 25 (s + 25) := by unfold D; exact cell_congr (by omega)
  rw [hd, D_twenty_five_eq_D_ten (s + 25) (by omega), d10_s_25 s (by omega)]
private theorem col_at_26 (s : Nat) (_hs : 3 ≤ s) : cell (s + 26) (-(s : Int)) = !(!D 8 (s + 8) && !D 10 (s + 8)) := by
  have hd : cell (s + 26) (-(s : Int)) = D 26 (s + 26) := by unfold D; exact cell_congr (by omega)
  rw [hd, D_twenty_six_eq_nand_D_eight_D_ten (s + 26) (by omega), d8_s_26 s (by omega), d10_s_26 s (by omega)]
private theorem col_at_27 (s : Nat) (_hs : 3 ≤ s) : cell (s + 27) (-(s : Int)) = !(!D 10 (s + 8) && D 8 (s + 8)) := by
  have hd : cell (s + 27) (-(s : Int)) = D 27 (s + 27) := by unfold D; exact cell_congr (by omega)
  rw [hd, D_twenty_seven_eq_nand_D_eight_D_ten (s + 27) (by omega), d8_s_27 s (by omega), d10_s_27 s (by omega)]
private theorem col_at_28 (s : Nat) (_hs : 3 ≤ s) : cell (s + 28) (-(s : Int)) = false := by
  have hd : cell (s + 28) (-(s : Int)) = D 28 (s + 28) := by unfold D; exact cell_congr (by omega)
  rw [hd, D_twenty_eight_eq_false (s + 28) (by omega)]
private theorem col_at_30 (s : Nat) (_hs : 3 ≤ s) : cell (s + 30) (-(s : Int)) = true := by
  have hd : cell (s + 30) (-(s : Int)) = D 30 (s + 30) := by unfold D; exact cell_congr (by omega)
  rw [hd, D_thirty_eq_true (s + 30) (by omega)]

/-- **Universal Lag-6 Column Flip at Ticks `s + 14` and `s + 20` (`cell_neg_flip_fourteen_twenty`):**
for every `s ≥ 3`, `cell (s + 20) (-(s : Int)) = !cell (s + 14) (-(s : Int))`. -/
theorem cell_neg_flip_fourteen_twenty (s : Nat) (hs : 3 ≤ s) :
    cell (s + 20) (-(s : Int)) = !cell (s + 14) (-(s : Int)) := by
  rw [col_at_20 s hs, col_at_14 s hs]
  cases D 8 (s + 8) <;> decide


theorem not_cell_periodic_six_at_col_le_neg_add_fourteen (T : Nat) {c : Int}
    (hc0 : c ≤ -3) (hc : c ≤ -(T : Int) + 14) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 6) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 14) (by omega)
  rw [hc_eq, show (s + 14) + 6 = s + 20 by omega, col_at_14 s (by omega), col_at_20 s (by omega)] at h0
  revert h0
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> decide

theorem not_cell_periodic_seven_at_col_le_neg_add_twenty_one (T : Nat) {c : Int}
    (hc0 : c ≤ -3) (hc : c ≤ -(T : Int) + 21) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 7) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 21) (by omega)
  rw [hc_eq, show (s + 21) + 7 = s + 28 by omega, col_at_21 s (by omega), col_at_28 s (by omega)] at h0
  have h1 := hper (s + 23) (by omega)
  rw [hc_eq, show (s + 23) + 7 = s + 30 by omega, col_at_23 s (by omega), col_at_30 s (by omega)] at h1
  revert h0 h1
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> decide

theorem not_cell_periodic_eleven_at_col_le_neg_add_thirteen (T : Nat) {c : Int}
    (hc0 : c ≤ -3) (hc : c ≤ -(T : Int) + 13) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 11) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 13) (by omega)
  rw [hc_eq, show (s + 13) + 11 = s + 24 by omega, col_at_13 s (by omega), col_at_24 s (by omega)] at h0
  have h1 := hper (s + 15) (by omega)
  rw [hc_eq, show (s + 15) + 11 = s + 26 by omega, col_at_15 s (by omega), col_at_26 s (by omega)] at h1
  have h2 := hper (s + 17) (by omega)
  rw [hc_eq, show (s + 17) + 11 = s + 28 by omega, col_at_17 s (by omega), col_at_28 s (by omega)] at h2
  revert h0 h1 h2
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> decide

theorem not_cell_periodic_twelve_at_col_le_neg_add_sixteen (T : Nat) {c : Int}
    (hc0 : c ≤ -3) (hc : c ≤ -(T : Int) + 16) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 12) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 16) (by omega)
  rw [hc_eq, show (s + 16) + 12 = s + 28 by omega, col_at_16 s (by omega), col_at_28 s (by omega)] at h0
  have h1 := hper (s + 18) (by omega)
  rw [hc_eq, show (s + 18) + 12 = s + 30 by omega, col_at_18 s (by omega), col_at_30 s (by omega)] at h1
  revert h0 h1
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> decide

theorem not_cell_periodic_thirteen_at_col_le_neg_add_ten (T : Nat) {c : Int}
    (hc0 : c ≤ -3) (hc : c ≤ -(T : Int) + 10) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 13) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 10) (by omega)
  rw [hc_eq, show (s + 10) + 13 = s + 23 by omega, col_at_10 s (by omega), col_at_23 s (by omega)] at h0
  have h1 := hper (s + 12) (by omega)
  rw [hc_eq, show (s + 12) + 13 = s + 25 by omega, col_at_12 s (by omega), col_at_25 s (by omega)] at h1
  have h2 := hper (s + 14) (by omega)
  rw [hc_eq, show (s + 14) + 13 = s + 27 by omega, col_at_14 s (by omega), col_at_27 s (by omega)] at h2
  revert h0 h1 h2
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> decide

theorem not_cell_periodic_fourteen_at_col_le_neg_add_twelve (T : Nat) {c : Int}
    (hc0 : c ≤ -3) (hc : c ≤ -(T : Int) + 12) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 14) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 12) (by omega)
  rw [hc_eq, show (s + 12) + 14 = s + 26 by omega, col_at_12 s (by omega), col_at_26 s (by omega)] at h0
  have h1 := hper (s + 13) (by omega)
  rw [hc_eq, show (s + 13) + 14 = s + 27 by omega, col_at_13 s (by omega), col_at_27 s (by omega)] at h1
  have h2 := hper (s + 14) (by omega)
  rw [hc_eq, show (s + 14) + 14 = s + 28 by omega, col_at_14 s (by omega), col_at_28 s (by omega)] at h2
  revert h0 h1 h2
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> decide

theorem not_cell_periodic_fifteen_at_col_le_neg_add_thirteen (T : Nat) {c : Int}
    (hc0 : c ≤ -3) (hc : c ≤ -(T : Int) + 13) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 15) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 13) (by omega)
  rw [hc_eq, show (s + 13) + 15 = s + 28 by omega, col_at_13 s (by omega), col_at_28 s (by omega)] at h0
  have h1 := hper (s + 15) (by omega)
  rw [hc_eq, show (s + 15) + 15 = s + 30 by omega, col_at_15 s (by omega), col_at_30 s (by omega)] at h1
  revert h0 h1
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> decide

theorem not_cell_periodic_sixteen_at_col_le_neg_add_twelve (T : Nat) {c : Int}
    (hc0 : c ≤ -3) (hc : c ≤ -(T : Int) + 12) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 16) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 12) (by omega)
  rw [hc_eq, show (s + 12) + 16 = s + 28 by omega, col_at_12 s (by omega), col_at_28 s (by omega)] at h0
  have h1 := hper (s + 14) (by omega)
  rw [hc_eq, show (s + 14) + 16 = s + 30 by omega, col_at_14 s (by omega), col_at_30 s (by omega)] at h1
  revert h0 h1
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> decide

theorem not_cell_periodic_twenty_one_at_col_le_neg_add_five (T : Nat) {c : Int}
    (hc0 : c ≤ -3) (hc : c ≤ -(T : Int) + 5) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 21) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 5) (by omega)
  rw [hc_eq, show (s + 5) + 21 = s + 26 by omega, col_at_5 s (by omega), col_at_26 s (by omega)] at h0
  have h1 := hper (s + 6) (by omega)
  rw [hc_eq, show (s + 6) + 21 = s + 27 by omega, col_at_6 s (by omega), col_at_27 s (by omega)] at h1
  revert h0 h1
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> decide

theorem not_cell_periodic_twenty_two_at_col_le_neg_add_three (T : Nat) {c : Int}
    (hc0 : c ≤ -3) (hc : c ≤ -(T : Int) + 3) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 22) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 3) (by omega)
  rw [hc_eq, show (s + 3) + 22 = s + 25 by omega, col_at_3 s (by omega), col_at_25 s (by omega)] at h0
  have h1 := hper (s + 4) (by omega)
  rw [hc_eq, show (s + 4) + 22 = s + 26 by omega, col_at_4 s (by omega), col_at_26 s (by omega)] at h1
  have h2 := hper (s + 6) (by omega)
  rw [hc_eq, show (s + 6) + 22 = s + 28 by omega, col_at_6 s (by omega), col_at_28 s (by omega)] at h2
  revert h0 h1 h2
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> decide

theorem not_cell_periodic_twenty_five_at_col_le_neg_add_three (T : Nat) {c : Int}
    (hc0 : c ≤ -3) (hc : c ≤ -(T : Int) + 3) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 25) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 3) (by omega)
  rw [hc_eq, show (s + 3) + 25 = s + 28 by omega, col_at_3 s (by omega), col_at_28 s (by omega)] at h0
  have h1 := hper (s + 5) (by omega)
  rw [hc_eq, show (s + 5) + 25 = s + 30 by omega, col_at_5 s (by omega), col_at_30 s (by omega)] at h1
  revert h0 h1
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> decide

theorem not_cell_periodic_twenty_six_at_col_le_neg_sub_five (T : Nat) {c : Int}
    (hc0 : c ≤ -5) (hc : c ≤ -(T : Int) - 5) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 26) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s - 5) (by omega)
  rw [hc_eq, show (s - 5) + 26 = s + 21 by omega, cell_eq_false_of_lt (s - 5) (-(s : Int)) (by omega), col_at_21 s (by omega)] at h0
  have h1 := hper (s - 4) (by omega)
  rw [hc_eq, show (s - 4) + 26 = s + 22 by omega, cell_eq_false_of_lt (s - 4) (-(s : Int)) (by omega), col_at_22 s (by omega)] at h1
  revert h0 h1
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> decide

theorem not_cell_periodic_twenty_nine_at_col_le_neg_sub_three (T : Nat) {c : Int}
    (hc0 : c ≤ -3) (hc : c ≤ -(T : Int) - 3) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 29) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s - 3) (by omega)
  rw [hc_eq, show (s - 3) + 29 = s + 26 by omega, cell_eq_false_of_lt (s - 3) (-(s : Int)) (by omega), col_at_26 s (by omega)] at h0
  have h1 := hper (s - 2) (by omega)
  rw [hc_eq, show (s - 2) + 29 = s + 27 by omega, cell_eq_false_of_lt (s - 2) (-(s : Int)) (by omega), col_at_27 s (by omega)] at h1
  revert h0 h1
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> decide

theorem not_cell_periodic_thirty_at_col_le_neg_sub_four (T : Nat) {c : Int}
    (hc0 : c ≤ -4) (hc : c ≤ -(T : Int) - 4) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 30) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s - 4) (by omega)
  rw [hc_eq, show (s - 4) + 30 = s + 26 by omega, cell_eq_false_of_lt (s - 4) (-(s : Int)) (by omega), col_at_26 s (by omega)] at h0
  have h1 := hper (s - 3) (by omega)
  rw [hc_eq, show (s - 3) + 30 = s + 27 by omega, cell_eq_false_of_lt (s - 3) (-(s : Int)) (by omega), col_at_27 s (by omega)] at h1
  revert h0 h1
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> decide

/-- **All-Period Unconditional 18-Column Inward Non-Periodicity
(`not_cell_periodic_at_col_le_neg_add_add_eighteen`):**
for every `T : Nat`, every positive period `P > 0`, and every column `c ≤ -5` with
`c ≤ -((T + P : Nat) : Int) + 18`, `cell · c` is not `P`-periodic from `T` on. -/
theorem not_cell_periodic_at_col_le_neg_add_add_eighteen (T : Nat) {P : Nat} (hP : 0 < P)
    {c : Int} (hc0 : c ≤ -5) (hc : c ≤ -((T + P : Nat) : Int) + 18) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + P) c = cell t c) := by
  rcases (by omega : P = 1 ∨ P = 2 ∨ P = 3 ∨ P = 4 ∨ P = 5 ∨ P = 6 ∨ P = 7 ∨ P = 8 ∨
      P = 9 ∨ P = 10 ∨ P = 11 ∨ P = 12 ∨ P = 13 ∨ P = 14 ∨ P = 15 ∨ P = 16 ∨ P = 17 ∨
      P = 18 ∨ P = 19 ∨ P = 20 ∨ P = 21 ∨ P = 22 ∨ P = 23 ∨ P = 24 ∨ P = 25 ∨ P = 26 ∨
      P = 27 ∨ P = 28 ∨ P = 29 ∨ P = 30 ∨ 31 ≤ P) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h31
  · exact not_cell_periodic_one_or_two_at_col_le_neg_add_twenty_eight T (by omega) (by omega) (by omega) (by omega)
  · exact not_cell_periodic_one_or_two_at_col_le_neg_add_twenty_eight T (by omega) (by omega) (by omega) (by omega)
  · exact not_cell_periodic_three_at_col_le_neg_add_nineteen T (by omega) (by omega)
  · exact not_cell_periodic_four_at_col_le_neg_add_eighteen T (by omega) (by omega)
  · exact not_cell_periodic_five_at_col_le_neg_add_twenty T (by omega) (by omega)
  · exact not_cell_periodic_six_at_col_le_neg_add_fourteen T (by omega) (by omega)
  · exact not_cell_periodic_seven_at_col_le_neg_add_twenty_one T (by omega) (by omega)
  · exact not_cell_periodic_eight_at_col_le_neg_add_ten T (by omega) (by omega)
  · exact not_cell_periodic_nine_at_col_le_neg_add_seventeen T (by omega) (by omega)
  · exact not_cell_periodic_ten_at_col_le_neg_add_fifteen T (by omega) (by omega)
  · exact not_cell_periodic_eleven_at_col_le_neg_add_thirteen T (by omega) (by omega)
  · exact not_cell_periodic_twelve_at_col_le_neg_add_sixteen T (by omega) (by omega)
  · exact not_cell_periodic_thirteen_at_col_le_neg_add_ten T (by omega) (by omega)
  · exact not_cell_periodic_fourteen_at_col_le_neg_add_twelve T (by omega) (by omega)
  · exact not_cell_periodic_fifteen_at_col_le_neg_add_thirteen T (by omega) (by omega)
  · exact not_cell_periodic_sixteen_at_col_le_neg_add_twelve T (by omega) (by omega)
  · exact not_cell_periodic_seventeen_at_col_le_neg_add_eight T (by omega) (by omega)
  · exact not_cell_periodic_eighteen_at_col_le_neg_add_five T (by omega) (by omega)
  · exact not_cell_periodic_nineteen_at_col_le_neg_add_nine T (by omega) (by omega)
  · exact not_cell_periodic_twenty_at_col_le_neg_add_three T (by omega) (by omega)
  · exact not_cell_periodic_twenty_one_at_col_le_neg_add_five T (by omega) (by omega)
  · exact not_cell_periodic_twenty_two_at_col_le_neg_add_three T (by omega) (by omega)
  · exact not_cell_periodic_twenty_three_at_col_le_neg_add_seven T (by omega) (by omega)
  · exact not_cell_periodic_twenty_four_at_col_le_neg_add_four T (by omega) (by omega)
  · exact not_cell_periodic_twenty_five_at_col_le_neg_add_three T (by omega) (by omega)
  · exact not_cell_periodic_twenty_six_at_col_le_neg_sub_five T (by omega) (by omega)
  · exact not_cell_periodic_twenty_seven_at_col_le_neg_add_one T (by omega) (by omega)
  · exact not_cell_periodic_twenty_eight_at_col_le_neg_add_two T (by omega) (by omega)
  · exact not_cell_periodic_twenty_nine_at_col_le_neg_sub_three T (by omega) (by omega)
  · exact not_cell_periodic_thirty_at_col_le_neg_sub_four T (by omega) (by omega)
  · exact not_cell_periodic_ge_thirty_one_at_col_le_neg_add_add_thirty T h31 (by omega) (by omega)




private theorem col_at_29 (s : Nat) (_hs : 3 ≤ s) :
    cell (s + 29) (-(s : Int)) = D 29 (s + 29) := by
  unfold D; exact cell_congr (by omega)

/-- **Three-Bit Arrival Formula at Diagonal `D 31` (`col_at_thirty_one_eq_not_xor`):**
for every `s ≥ 3`, `cell (s + 31) (-(s : Int)) = !xor (!(D 10 (s + 8) && !D 8 (s + 8))) (D 29 (s + 29))`. -/
theorem col_at_thirty_one_eq_not_xor (s : Nat) (hs : 3 ≤ s) :
    cell (s + 31) (-(s : Int)) = !xor (!(D 10 (s + 8) && !D 8 (s + 8))) (D 29 (s + 29)) := by
  have hd : cell (s + 31) (-(s : Int)) = D 31 (s + 31) := by unfold D; exact cell_congr (by omega)
  have h31 := D_thirty_one_succ_eq_not_D_twenty_nine (s + 30) (by omega)
  have h29 := D_twenty_nine_step_eq_xor_D_twenty_seven (s + 29) (by omega)
  have h27 : D 27 (s + 29) = !(D 10 (s + 8) && !D 8 (s + 8)) := by
    have p8 : D 8 (s + 29) = D 8 (s + 25) := D_eight_periodic_four_local (s + 25) (by omega)
    have p10 : D 10 (s + 29) = D 10 (s + 25) := D_ten_periodic_four_local (s + 25) (by omega)
    rw [D_twenty_seven_eq_nand_D_eight_D_ten (s + 29) (by omega), p8, p10,
        d8_s_25 s (by omega), d10_s_25 s (by omega)]
  rw [show s + 30 + 1 = s + 31 by omega] at h31
  rw [show s + 29 + 1 = s + 30 by omega] at h29
  rw [hd, h31, h29, h27]

private theorem col_at_31 (s : Nat) (hs : 3 ≤ s) :
    cell (s + 31) (-(s : Int)) = !xor (!(D 10 (s + 8) && !D 8 (s + 8))) (D 29 (s + 29)) :=
  col_at_thirty_one_eq_not_xor s hs


theorem not_cell_periodic_three_at_col_le_neg_add_twenty_five (T : Nat) {c : Int}
    (hc0 : c ≤ -3) (hc : c ≤ -(T : Int) + 25) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 3) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 25) (by omega)
  rw [hc_eq, show (s + 25) + 3 = s + 28 by omega, col_at_25 s (by omega), col_at_28 s (by omega)] at h0
  have h1 := hper (s + 26) (by omega)
  rw [hc_eq, show (s + 26) + 3 = s + 29 by omega, col_at_26 s (by omega), col_at_29 s (by omega)] at h1
  have h2 := hper (s + 27) (by omega)
  rw [hc_eq, show (s + 27) + 3 = s + 30 by omega, col_at_27 s (by omega), col_at_30 s (by omega)] at h2
  have h3 := hper (s + 28) (by omega)
  rw [hc_eq, show (s + 28) + 3 = s + 31 by omega, col_at_28 s (by omega), col_at_31 s (by omega)] at h3
  revert h0 h1 h2 h3
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_four_at_col_le_neg_add_twenty_three (T : Nat) {c : Int}
    (hc0 : c ≤ -3) (hc : c ≤ -(T : Int) + 23) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 4) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 23) (by omega)
  rw [hc_eq, show (s + 23) + 4 = s + 27 by omega, col_at_23 s (by omega), col_at_27 s (by omega)] at h0
  have h1 := hper (s + 24) (by omega)
  rw [hc_eq, show (s + 24) + 4 = s + 28 by omega, col_at_24 s (by omega), col_at_28 s (by omega)] at h1
  revert h0 h1
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_six_at_col_le_neg_add_twenty_three (T : Nat) {c : Int}
    (hc0 : c ≤ -3) (hc : c ≤ -(T : Int) + 23) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 6) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 23) (by omega)
  rw [hc_eq, show (s + 23) + 6 = s + 29 by omega, col_at_23 s (by omega), col_at_29 s (by omega)] at h0
  have h1 := hper (s + 24) (by omega)
  rw [hc_eq, show (s + 24) + 6 = s + 30 by omega, col_at_24 s (by omega), col_at_30 s (by omega)] at h1
  have h2 := hper (s + 25) (by omega)
  rw [hc_eq, show (s + 25) + 6 = s + 31 by omega, col_at_25 s (by omega), col_at_31 s (by omega)] at h2
  revert h0 h1 h2
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_eight_at_col_le_neg_add_nineteen (T : Nat) {c : Int}
    (hc0 : c ≤ -3) (hc : c ≤ -(T : Int) + 19) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 8) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 19) (by omega)
  rw [hc_eq, show (s + 19) + 8 = s + 27 by omega, col_at_19 s (by omega), col_at_27 s (by omega)] at h0
  have h1 := hper (s + 20) (by omega)
  rw [hc_eq, show (s + 20) + 8 = s + 28 by omega, col_at_20 s (by omega), col_at_28 s (by omega)] at h1
  have h2 := hper (s + 21) (by omega)
  rw [hc_eq, show (s + 21) + 8 = s + 29 by omega, col_at_21 s (by omega), col_at_29 s (by omega)] at h2
  have h3 := hper (s + 22) (by omega)
  rw [hc_eq, show (s + 22) + 8 = s + 30 by omega, col_at_22 s (by omega), col_at_30 s (by omega)] at h3
  revert h0 h1 h2 h3
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_thirteen_at_col_le_neg_add_sixteen (T : Nat) {c : Int}
    (hc0 : c ≤ -3) (hc : c ≤ -(T : Int) + 16) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 13) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 16) (by omega)
  rw [hc_eq, show (s + 16) + 13 = s + 29 by omega, col_at_16 s (by omega), col_at_29 s (by omega)] at h0
  have h1 := hper (s + 17) (by omega)
  rw [hc_eq, show (s + 17) + 13 = s + 30 by omega, col_at_17 s (by omega), col_at_30 s (by omega)] at h1
  have h2 := hper (s + 18) (by omega)
  rw [hc_eq, show (s + 18) + 13 = s + 31 by omega, col_at_18 s (by omega), col_at_31 s (by omega)] at h2
  revert h0 h1 h2
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_eighteen_at_col_le_neg_add_ten (T : Nat) {c : Int}
    (hc0 : c ≤ -3) (hc : c ≤ -(T : Int) + 10) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 18) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 10) (by omega)
  rw [hc_eq, show (s + 10) + 18 = s + 28 by omega, col_at_10 s (by omega), col_at_28 s (by omega)] at h0
  have h1 := hper (s + 11) (by omega)
  rw [hc_eq, show (s + 11) + 18 = s + 29 by omega, col_at_11 s (by omega), col_at_29 s (by omega)] at h1
  have h2 := hper (s + 12) (by omega)
  rw [hc_eq, show (s + 12) + 18 = s + 30 by omega, col_at_12 s (by omega), col_at_30 s (by omega)] at h2
  have h3 := hper (s + 13) (by omega)
  rw [hc_eq, show (s + 13) + 18 = s + 31 by omega, col_at_13 s (by omega), col_at_31 s (by omega)] at h3
  revert h0 h1 h2 h3
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_twenty_at_col_le_neg_add_nine (T : Nat) {c : Int}
    (hc0 : c ≤ -3) (hc : c ≤ -(T : Int) + 9) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 20) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 9) (by omega)
  rw [hc_eq, show (s + 9) + 20 = s + 29 by omega, col_at_9 s (by omega), col_at_29 s (by omega)] at h0
  have h1 := hper (s + 10) (by omega)
  rw [hc_eq, show (s + 10) + 20 = s + 30 by omega, col_at_10 s (by omega), col_at_30 s (by omega)] at h1
  have h2 := hper (s + 11) (by omega)
  rw [hc_eq, show (s + 11) + 20 = s + 31 by omega, col_at_11 s (by omega), col_at_31 s (by omega)] at h2
  revert h0 h1 h2
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

/-- **All-Period Unconditional 21-Column Inward Non-Periodicity
(`not_cell_periodic_at_col_le_neg_add_add_twenty_one`):**
for every `T : Nat`, every positive period `P > 0`, and every column `c ≤ -5` with
`c ≤ -((T + P : Nat) : Int) + 21`, `cell · c` is not `P`-periodic from `T` on. -/
theorem not_cell_periodic_at_col_le_neg_add_add_twenty_one (T : Nat) {P : Nat} (hP : 0 < P)
    {c : Int} (hc0 : c ≤ -5) (hc : c ≤ -((T + P : Nat) : Int) + 21) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + P) c = cell t c) := by
  rcases (by omega : P = 1 ∨ P = 2 ∨ P = 3 ∨ P = 4 ∨ P = 5 ∨ P = 6 ∨ P = 7 ∨ P = 8 ∨
      P = 9 ∨ P = 10 ∨ P = 11 ∨ P = 12 ∨ P = 13 ∨ P = 14 ∨ P = 15 ∨ P = 16 ∨ P = 17 ∨
      P = 18 ∨ P = 19 ∨ P = 20 ∨ P = 21 ∨ P = 22 ∨ P = 23 ∨ P = 24 ∨ P = 25 ∨ P = 26 ∨
      P = 27 ∨ P = 28 ∨ P = 29 ∨ P = 30 ∨ 31 ≤ P) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h31
  · exact not_cell_periodic_one_or_two_at_col_le_neg_add_twenty_eight T (by omega) (by omega) (by omega) (by omega)
  · exact not_cell_periodic_one_or_two_at_col_le_neg_add_twenty_eight T (by omega) (by omega) (by omega) (by omega)
  · exact not_cell_periodic_three_at_col_le_neg_add_twenty_five T (by omega) (by omega)
  · exact not_cell_periodic_four_at_col_le_neg_add_twenty_three T (by omega) (by omega)
  · exact not_cell_periodic_five_at_col_le_neg_add_twenty T (by omega) (by omega)
  · exact not_cell_periodic_six_at_col_le_neg_add_twenty_three T (by omega) (by omega)
  · exact not_cell_periodic_seven_at_col_le_neg_add_twenty_one T (by omega) (by omega)
  · exact not_cell_periodic_eight_at_col_le_neg_add_nineteen T (by omega) (by omega)
  · exact not_cell_periodic_nine_at_col_le_neg_add_seventeen T (by omega) (by omega)
  · exact not_cell_periodic_ten_at_col_le_neg_add_fifteen T (by omega) (by omega)
  · exact not_cell_periodic_eleven_at_col_le_neg_add_thirteen T (by omega) (by omega)
  · exact not_cell_periodic_twelve_at_col_le_neg_add_sixteen T (by omega) (by omega)
  · exact not_cell_periodic_thirteen_at_col_le_neg_add_sixteen T (by omega) (by omega)
  · exact not_cell_periodic_fourteen_at_col_le_neg_add_twelve T (by omega) (by omega)
  · exact not_cell_periodic_fifteen_at_col_le_neg_add_thirteen T (by omega) (by omega)
  · exact not_cell_periodic_sixteen_at_col_le_neg_add_twelve T (by omega) (by omega)
  · exact not_cell_periodic_seventeen_at_col_le_neg_add_eight T (by omega) (by omega)
  · exact not_cell_periodic_eighteen_at_col_le_neg_add_ten T (by omega) (by omega)
  · exact not_cell_periodic_nineteen_at_col_le_neg_add_nine T (by omega) (by omega)
  · exact not_cell_periodic_twenty_at_col_le_neg_add_nine T (by omega) (by omega)
  · exact not_cell_periodic_twenty_one_at_col_le_neg_add_five T (by omega) (by omega)
  · exact not_cell_periodic_twenty_two_at_col_le_neg_add_three T (by omega) (by omega)
  · exact not_cell_periodic_twenty_three_at_col_le_neg_add_seven T (by omega) (by omega)
  · exact not_cell_periodic_twenty_four_at_col_le_neg_add_four T (by omega) (by omega)
  · exact not_cell_periodic_twenty_five_at_col_le_neg_add_three T (by omega) (by omega)
  · exact not_cell_periodic_twenty_six_at_col_le_neg_sub_five T (by omega) (by omega)
  · exact not_cell_periodic_twenty_seven_at_col_le_neg_add_one T (by omega) (by omega)
  · exact not_cell_periodic_twenty_eight_at_col_le_neg_add_two T (by omega) (by omega)
  · exact not_cell_periodic_twenty_nine_at_col_le_neg_sub_three T (by omega) (by omega)
  · exact not_cell_periodic_thirty_at_col_le_neg_sub_four T (by omega) (by omega)
  · exact not_cell_periodic_ge_thirty_one_at_col_le_neg_add_add_thirty T h31 (by omega) (by omega)

/-- **Twenty-Four-Column Inward Non-Periodicity for All `P ≠ 26`
(`not_cell_periodic_ne_twenty_six_at_col_le_neg_add_add_twenty_four`):**
for every `T : Nat`, every positive period `P > 0` with `P ≠ 26`, and every column `c ≤ -4` with
`c ≤ -((T + P : Nat) : Int) + 24`, `cell · c` is not `P`-periodic from `T` on. -/
theorem not_cell_periodic_ne_twenty_six_at_col_le_neg_add_add_twenty_four (T : Nat) {P : Nat}
    (hP : 0 < P) (hne : P ≠ 26) {c : Int} (hc0 : c ≤ -4) (hc : c ≤ -((T + P : Nat) : Int) + 24) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + P) c = cell t c) := by
  rcases (by omega : P = 1 ∨ P = 2 ∨ P = 3 ∨ P = 4 ∨ P = 5 ∨ P = 6 ∨ P = 7 ∨ P = 8 ∨
      P = 9 ∨ P = 10 ∨ P = 11 ∨ P = 12 ∨ P = 13 ∨ P = 14 ∨ P = 15 ∨ P = 16 ∨ P = 17 ∨
      P = 18 ∨ P = 19 ∨ P = 20 ∨ P = 21 ∨ P = 22 ∨ P = 23 ∨ P = 24 ∨ P = 25 ∨
      P = 27 ∨ P = 28 ∨ P = 29 ∨ P = 30 ∨ 31 ≤ P) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h31
  · exact not_cell_periodic_one_or_two_at_col_le_neg_add_twenty_eight T (by omega) (by omega) (by omega) (by omega)
  · exact not_cell_periodic_one_or_two_at_col_le_neg_add_twenty_eight T (by omega) (by omega) (by omega) (by omega)
  · exact not_cell_periodic_three_at_col_le_neg_add_twenty_five T (by omega) (by omega)
  · exact not_cell_periodic_four_at_col_le_neg_add_twenty_three T (by omega) (by omega)
  · exact not_cell_periodic_five_at_col_le_neg_add_twenty T (by omega) (by omega)
  · exact not_cell_periodic_six_at_col_le_neg_add_twenty_three T (by omega) (by omega)
  · exact not_cell_periodic_seven_at_col_le_neg_add_twenty_one T (by omega) (by omega)
  · exact not_cell_periodic_eight_at_col_le_neg_add_nineteen T (by omega) (by omega)
  · exact not_cell_periodic_nine_at_col_le_neg_add_seventeen T (by omega) (by omega)
  · exact not_cell_periodic_ten_at_col_le_neg_add_fifteen T (by omega) (by omega)
  · exact not_cell_periodic_eleven_at_col_le_neg_add_thirteen T (by omega) (by omega)
  · exact not_cell_periodic_twelve_at_col_le_neg_add_sixteen T (by omega) (by omega)
  · exact not_cell_periodic_thirteen_at_col_le_neg_add_sixteen T (by omega) (by omega)
  · exact not_cell_periodic_fourteen_at_col_le_neg_add_twelve T (by omega) (by omega)
  · exact not_cell_periodic_fifteen_at_col_le_neg_add_thirteen T (by omega) (by omega)
  · exact not_cell_periodic_sixteen_at_col_le_neg_add_twelve T (by omega) (by omega)
  · exact not_cell_periodic_seventeen_at_col_le_neg_add_eight T (by omega) (by omega)
  · exact not_cell_periodic_eighteen_at_col_le_neg_add_ten T (by omega) (by omega)
  · exact not_cell_periodic_nineteen_at_col_le_neg_add_nine T (by omega) (by omega)
  · exact not_cell_periodic_twenty_at_col_le_neg_add_nine T (by omega) (by omega)
  · exact not_cell_periodic_twenty_one_at_col_le_neg_add_five T (by omega) (by omega)
  · exact not_cell_periodic_twenty_two_at_col_le_neg_add_three T (by omega) (by omega)
  · exact not_cell_periodic_twenty_three_at_col_le_neg_add_seven T (by omega) (by omega)
  · exact not_cell_periodic_twenty_four_at_col_le_neg_add_four T (by omega) (by omega)
  · exact not_cell_periodic_twenty_five_at_col_le_neg_add_three T (by omega) (by omega)
  · exact not_cell_periodic_twenty_seven_at_col_le_neg_add_one T (by omega) (by omega)
  · exact not_cell_periodic_twenty_eight_at_col_le_neg_add_two T (by omega) (by omega)
  · exact not_cell_periodic_twenty_nine_at_col_le_neg_sub_three T (by omega) (by omega)
  · exact not_cell_periodic_thirty_at_col_le_neg_sub_four T (by omega) (by omega)
  · exact not_cell_periodic_ge_thirty_one_at_col_le_neg_add_add_thirty T h31 (by omega) (by omega)


private theorem d8_s_28 (s : Nat) (hs : 1 ≤ s) : D 8 (s + 28) = D 8 (s + 8) := by
  rw [show s + 28 = (s + 27) + 1 by omega, D_eight_succ_eq_D_ten (s + 27) (by omega), d10_s_27 s hs]
private theorem d10_s_28 (s : Nat) (hs : 1 ≤ s) : D 10 (s + 28) = D 10 (s + 8) := by
  rw [show s + 28 = (s + 27) + 1 by omega, D_ten_succ_eq_not_D_eight (s + 27) (by omega), d8_s_27 s hs, Bool.not_not]
private theorem d8_s_29 (s : Nat) (hs : 1 ≤ s) : D 8 (s + 29) = D 10 (s + 8) := by
  rw [show s + 29 = (s + 28) + 1 by omega, D_eight_succ_eq_D_ten (s + 28) (by omega), d10_s_28 s hs]
private theorem d10_s_29 (s : Nat) (hs : 1 ≤ s) : D 10 (s + 29) = !D 8 (s + 8) := by
  rw [show s + 29 = (s + 28) + 1 by omega, D_ten_succ_eq_not_D_eight (s + 28) (by omega), d8_s_28 s hs]
private theorem d8_s_30 (s : Nat) (hs : 1 ≤ s) : D 8 (s + 30) = !D 8 (s + 8) := by
  rw [show s + 30 = (s + 29) + 1 by omega, D_eight_succ_eq_D_ten (s + 29) (by omega), d10_s_29 s hs]
private theorem d10_s_30 (s : Nat) (hs : 1 ≤ s) : D 10 (s + 30) = !D 10 (s + 8) := by
  rw [show s + 30 = (s + 29) + 1 by omega, D_ten_succ_eq_not_D_eight (s + 29) (by omega), d8_s_29 s hs]
private theorem d8_s_31 (s : Nat) (hs : 1 ≤ s) : D 8 (s + 31) = !D 10 (s + 8) := by
  rw [show s + 31 = (s + 30) + 1 by omega, D_eight_succ_eq_D_ten (s + 30) (by omega), d10_s_30 s hs]
private theorem d10_s_31 (s : Nat) (hs : 1 ≤ s) : D 10 (s + 31) = D 8 (s + 8) := by
  rw [show s + 31 = (s + 30) + 1 by omega, D_ten_succ_eq_not_D_eight (s + 30) (by omega), d8_s_30 s hs, Bool.not_not]
private theorem d8_s_32 (s : Nat) (hs : 1 ≤ s) : D 8 (s + 32) = D 8 (s + 8) := by
  rw [show s + 32 = (s + 31) + 1 by omega, D_eight_succ_eq_D_ten (s + 31) (by omega), d10_s_31 s hs]
private theorem d10_s_32 (s : Nat) (hs : 1 ≤ s) : D 10 (s + 32) = D 10 (s + 8) := by
  rw [show s + 32 = (s + 31) + 1 by omega, D_ten_succ_eq_not_D_eight (s + 31) (by omega), d8_s_31 s hs, Bool.not_not]
private theorem d8_s_33 (s : Nat) (hs : 1 ≤ s) : D 8 (s + 33) = D 10 (s + 8) := by
  rw [show s + 33 = (s + 32) + 1 by omega, D_eight_succ_eq_D_ten (s + 32) (by omega), d10_s_32 s hs]
private theorem d10_s_33 (s : Nat) (hs : 1 ≤ s) : D 10 (s + 33) = !D 8 (s + 8) := by
  rw [show s + 33 = (s + 32) + 1 by omega, D_ten_succ_eq_not_D_eight (s + 32) (by omega), d8_s_32 s hs]
private theorem d8_s_34 (s : Nat) (hs : 1 ≤ s) : D 8 (s + 34) = !D 8 (s + 8) := by
  rw [show s + 34 = (s + 33) + 1 by omega, D_eight_succ_eq_D_ten (s + 33) (by omega), d10_s_33 s hs]
private theorem d10_s_34 (s : Nat) (hs : 1 ≤ s) : D 10 (s + 34) = !D 10 (s + 8) := by
  rw [show s + 34 = (s + 33) + 1 by omega, D_ten_succ_eq_not_D_eight (s + 33) (by omega), d8_s_33 s hs]
private theorem d29_s_29 (s : Nat) (_hs : 2 ≤ s) : D 29 (s + 29) = D 29 (s + 29) := rfl
private theorem d29_s_30 (s : Nat) (hs : 2 ≤ s) : D 29 (s + 30) = xor (!(D 10 (s + 8) && !D 8 (s + 8))) (D 29 (s + 29)) := by
  rw [show s + 30 = (s + 29) + 1 by omega, D_twenty_nine_step_eq_xor_D_twenty_seven (s + 29) (by omega), D_twenty_seven_eq_nand_D_eight_D_ten (s + 29) (by omega), d8_s_29 s (by omega), d10_s_29 s (by omega), d29_s_29 s hs]
private theorem d29_s_31 (s : Nat) (hs : 2 ≤ s) : D 29 (s + 31) = xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (D 29 (s + 29))) := by
  rw [show s + 31 = (s + 30) + 1 by omega, D_twenty_nine_step_eq_xor_D_twenty_seven (s + 30) (by omega), D_twenty_seven_eq_nand_D_eight_D_ten (s + 30) (by omega), d8_s_30 s (by omega), d10_s_30 s (by omega), d29_s_30 s hs]
private theorem d29_s_32 (s : Nat) (hs : 2 ≤ s) : D 29 (s + 32) = xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (D 29 (s + 29)))) := by
  rw [show s + 32 = (s + 31) + 1 by omega, D_twenty_nine_step_eq_xor_D_twenty_seven (s + 31) (by omega), D_twenty_seven_eq_nand_D_eight_D_ten (s + 31) (by omega), d8_s_31 s (by omega), d10_s_31 s (by omega), d29_s_31 s hs]
private theorem d29_s_33 (s : Nat) (hs : 2 ≤ s) : D 29 (s + 33) = xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (D 29 (s + 29))))) := by
  rw [show s + 33 = (s + 32) + 1 by omega, D_twenty_nine_step_eq_xor_D_twenty_seven (s + 32) (by omega), D_twenty_seven_eq_nand_D_eight_D_ten (s + 32) (by omega), d8_s_32 s (by omega), d10_s_32 s (by omega), d29_s_32 s hs]
private theorem d29_s_34 (s : Nat) (hs : 2 ≤ s) : D 29 (s + 34) = xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (D 29 (s + 29)))))) := by
  rw [show s + 34 = (s + 33) + 1 by omega, D_twenty_nine_step_eq_xor_D_twenty_seven (s + 33) (by omega), D_twenty_seven_eq_nand_D_eight_D_ten (s + 33) (by omega), d8_s_33 s (by omega), d10_s_33 s (by omega), d29_s_33 s hs]

private theorem col_at_32 (s : Nat) (hs : 4 ≤ s) :
    cell (s + 32) (-(s : Int)) = (( !(D 10 (s + 8)) && !(xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (D 29 (s + 29))))) ) || ( (D 8 (s + 8)) && (D 10 (s + 8)) && (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (D 29 (s + 29))))) )) := by
  have hd : cell (s + 32) (-(s : Int)) = D 32 (s + 32) := by unfold D; exact cell_congr (by omega)
  rw [hd, D_thirty_two_eq_gate (s + 32) (by omega), d8_s_32 s (by omega), d10_s_32 s (by omega), d29_s_32 s (by omega)]

private theorem col_at_33 (s : Nat) (hs : 3 ≤ s) :
    cell (s + 33) (-(s : Int)) = ( (!D 8 (s + 8)) && ( !(D 10 (s + 8)) || (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (D 29 (s + 29)))))) ) ) := by
  have hd : cell (s + 33) (-(s : Int)) = D 33 (s + 33) := by unfold D; exact cell_congr (by omega)
  rw [hd, D_thirty_three_eq_gate (s + 33) (by omega), d8_s_33 s (by omega), d10_s_33 s (by omega), d29_s_33 s (by omega)]

private theorem col_at_34 (s : Nat) (hs : 6 ≤ s) :
    cell (s + 34) (-(s : Int)) = ( ( (!D 8 (s + 8)) && !(xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (D 29 (s + 29))))))) ) || ( (!D 10 (s + 8)) && (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (D 29 (s + 29))))))) ) ) := by
  have hd : cell (s + 34) (-(s : Int)) = D 34 (s + 34) := by unfold D; exact cell_congr (by omega)
  rw [hd, D_thirty_four_eq_mux (s + 34) (by omega), d8_s_34 s (by omega), d10_s_34 s (by omega), d29_s_34 s (by omega)]


theorem not_cell_periodic_five_at_col_le_neg_add_twenty_five (T : Nat) {c : Int}
    (hc0 : c ≤ -4) (hc : c ≤ -(T : Int) + 25) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 5) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 25) (by omega)
  rw [hc_eq, show (s + 25) + 5 = s + 30 by omega, col_at_25 s (by omega), col_at_30 s (by omega)] at h0
  have h1 := hper (s + 26) (by omega)
  rw [hc_eq, show (s + 26) + 5 = s + 31 by omega, col_at_26 s (by omega), col_at_31 s (by omega)] at h1
  have h2 := hper (s + 27) (by omega)
  rw [hc_eq, show (s + 27) + 5 = s + 32 by omega, col_at_27 s (by omega), col_at_32 s (by omega)] at h2
  have h3 := hper (s + 28) (by omega)
  rw [hc_eq, show (s + 28) + 5 = s + 33 by omega, col_at_28 s (by omega), col_at_33 s (by omega)] at h3
  revert h0 h1 h2 h3
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_nine_at_col_le_neg_add_twenty_two (T : Nat) {c : Int}
    (hc0 : c ≤ -4) (hc : c ≤ -(T : Int) + 22) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 9) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 22) (by omega)
  rw [hc_eq, show (s + 22) + 9 = s + 31 by omega, col_at_22 s (by omega), col_at_31 s (by omega)] at h0
  have h1 := hper (s + 23) (by omega)
  rw [hc_eq, show (s + 23) + 9 = s + 32 by omega, col_at_23 s (by omega), col_at_32 s (by omega)] at h1
  have h2 := hper (s + 24) (by omega)
  rw [hc_eq, show (s + 24) + 9 = s + 33 by omega, col_at_24 s (by omega), col_at_33 s (by omega)] at h2
  revert h0 h1 h2
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_ten_at_col_le_neg_add_eighteen (T : Nat) {c : Int}
    (hc0 : c ≤ -3) (hc : c ≤ -(T : Int) + 18) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 10) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 18) (by omega)
  rw [hc_eq, show (s + 18) + 10 = s + 28 by omega, col_at_18 s (by omega), col_at_28 s (by omega)] at h0
  have h1 := hper (s + 19) (by omega)
  rw [hc_eq, show (s + 19) + 10 = s + 29 by omega, col_at_19 s (by omega), col_at_29 s (by omega)] at h1
  have h2 := hper (s + 20) (by omega)
  rw [hc_eq, show (s + 20) + 10 = s + 30 by omega, col_at_20 s (by omega), col_at_30 s (by omega)] at h2
  have h3 := hper (s + 21) (by omega)
  rw [hc_eq, show (s + 21) + 10 = s + 31 by omega, col_at_21 s (by omega), col_at_31 s (by omega)] at h3
  revert h0 h1 h2 h3
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_eleven_at_col_le_neg_add_twenty (T : Nat) {c : Int}
    (hc0 : c ≤ -4) (hc : c ≤ -(T : Int) + 20) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 11) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 20) (by omega)
  rw [hc_eq, show (s + 20) + 11 = s + 31 by omega, col_at_20 s (by omega), col_at_31 s (by omega)] at h0
  have h1 := hper (s + 21) (by omega)
  rw [hc_eq, show (s + 21) + 11 = s + 32 by omega, col_at_21 s (by omega), col_at_32 s (by omega)] at h1
  revert h0 h1
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_fourteen_at_col_le_neg_add_seventeen (T : Nat) {c : Int}
    (hc0 : c ≤ -4) (hc : c ≤ -(T : Int) + 17) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 14) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 17) (by omega)
  rw [hc_eq, show (s + 17) + 14 = s + 31 by omega, col_at_17 s (by omega), col_at_31 s (by omega)] at h0
  have h1 := hper (s + 18) (by omega)
  rw [hc_eq, show (s + 18) + 14 = s + 32 by omega, col_at_18 s (by omega), col_at_32 s (by omega)] at h1
  have h2 := hper (s + 19) (by omega)
  rw [hc_eq, show (s + 19) + 14 = s + 33 by omega, col_at_19 s (by omega), col_at_33 s (by omega)] at h2
  revert h0 h1 h2
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_seventeen_at_col_le_neg_add_twelve (T : Nat) {c : Int}
    (hc0 : c ≤ -3) (hc : c ≤ -(T : Int) + 12) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 17) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 12) (by omega)
  rw [hc_eq, show (s + 12) + 17 = s + 29 by omega, col_at_12 s (by omega), col_at_29 s (by omega)] at h0
  have h1 := hper (s + 13) (by omega)
  rw [hc_eq, show (s + 13) + 17 = s + 30 by omega, col_at_13 s (by omega), col_at_30 s (by omega)] at h1
  have h2 := hper (s + 14) (by omega)
  rw [hc_eq, show (s + 14) + 17 = s + 31 by omega, col_at_14 s (by omega), col_at_31 s (by omega)] at h2
  have h3 := hper (s + 16) (by omega)
  rw [hc_eq, show (s + 16) + 17 = s + 33 by omega, col_at_16 s (by omega), col_at_33 s (by omega)] at h3
  revert h0 h1 h2 h3
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_twenty_one_at_col_le_neg_add_twelve (T : Nat) {c : Int}
    (hc0 : c ≤ -6) (hc : c ≤ -(T : Int) + 12) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 21) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 12) (by omega)
  rw [hc_eq, show (s + 12) + 21 = s + 33 by omega, col_at_12 s (by omega), col_at_33 s (by omega)] at h0
  have h1 := hper (s + 13) (by omega)
  rw [hc_eq, show (s + 13) + 21 = s + 34 by omega, col_at_13 s (by omega), col_at_34 s (by omega)] at h1
  revert h0 h1
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_twenty_two_at_col_le_neg_add_seven (T : Nat) {c : Int}
    (hc0 : c ≤ -3) (hc : c ≤ -(T : Int) + 7) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 22) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 7) (by omega)
  rw [hc_eq, show (s + 7) + 22 = s + 29 by omega, col_at_7 s (by omega), col_at_29 s (by omega)] at h0
  have h1 := hper (s + 8) (by omega)
  rw [hc_eq, show (s + 8) + 22 = s + 30 by omega, col_at_8 s (by omega), col_at_30 s (by omega)] at h1
  have h2 := hper (s + 9) (by omega)
  rw [hc_eq, show (s + 9) + 22 = s + 31 by omega, col_at_9 s (by omega), col_at_31 s (by omega)] at h2
  revert h0 h1 h2
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_twenty_six_at_col_le_neg_add_six (T : Nat) {c : Int}
    (hc0 : c ≤ -6) (hc : c ≤ -(T : Int) + 6) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 26) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 6) (by omega)
  rw [hc_eq, show (s + 6) + 26 = s + 32 by omega, col_at_6 s (by omega), col_at_32 s (by omega)] at h0
  have h1 := hper (s + 7) (by omega)
  rw [hc_eq, show (s + 7) + 26 = s + 33 by omega, col_at_7 s (by omega), col_at_33 s (by omega)] at h1
  have h2 := hper (s + 8) (by omega)
  rw [hc_eq, show (s + 8) + 26 = s + 34 by omega, col_at_8 s (by omega), col_at_34 s (by omega)] at h2
  revert h0 h1 h2
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_twenty_nine_at_col_le_neg_zero (T : Nat) {c : Int}
    (hc0 : c ≤ -3) (hc : c ≤ -(T : Int)) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 29) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 0) (by omega)
  rw [hc_eq, show (s + 0) + 29 = s + 29 by omega, col_at_0 s (by omega), col_at_29 s (by omega)] at h0
  have h1 := hper (s + 2) (by omega)
  rw [hc_eq, show (s + 2) + 29 = s + 31 by omega, col_at_2 s (by omega), col_at_31 s (by omega)] at h1
  have h2 := hper (s + 4) (by omega)
  rw [hc_eq, show (s + 4) + 29 = s + 33 by omega, col_at_4 s (by omega), col_at_33 s (by omega)] at h2
  revert h0 h1 h2
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_thirty_at_col_le_neg_sub_one (T : Nat) {c : Int}
    (hc0 : c ≤ -3) (hc : c ≤ -(T : Int) - 1) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 30) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s - 1) (by omega)
  rw [hc_eq, show (s - 1) + 30 = s + 29 by omega, cell_eq_false_of_lt (s - 1) (-(s : Int)) (by omega), col_at_29 s (by omega)] at h0
  have h1 := hper (s + 1) (by omega)
  rw [hc_eq, show (s + 1) + 30 = s + 31 by omega, col_at_1 s (by omega), col_at_31 s (by omega)] at h1
  have h2 := hper (s + 3) (by omega)
  rw [hc_eq, show (s + 3) + 30 = s + 33 by omega, col_at_3 s (by omega), col_at_33 s (by omega)] at h2
  revert h0 h1 h2
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

/-- **All-Period Unconditional 27-Column Inward Non-Periodicity
(`not_cell_periodic_at_col_le_neg_add_add_twenty_seven`):**
for every `T : Nat`, every positive period `P > 0`, and every column `c ≤ -6` with
`c ≤ -((T + P : Nat) : Int) + 27`, `cell · c` is not `P`-periodic from `T` on. -/
theorem not_cell_periodic_at_col_le_neg_add_add_twenty_seven (T : Nat) {P : Nat} (hP : 0 < P)
    {c : Int} (hc0 : c ≤ -6) (hc : c ≤ -((T + P : Nat) : Int) + 27) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + P) c = cell t c) := by
  rcases (by omega : P = 1 ∨ P = 2 ∨ P = 3 ∨ P = 4 ∨ P = 5 ∨ P = 6 ∨ P = 7 ∨ P = 8 ∨
      P = 9 ∨ P = 10 ∨ P = 11 ∨ P = 12 ∨ P = 13 ∨ P = 14 ∨ P = 15 ∨ P = 16 ∨ P = 17 ∨
      P = 18 ∨ P = 19 ∨ P = 20 ∨ P = 21 ∨ P = 22 ∨ P = 23 ∨ P = 24 ∨ P = 25 ∨ P = 26 ∨
      P = 27 ∨ P = 28 ∨ P = 29 ∨ P = 30 ∨ 31 ≤ P) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h31
  · exact not_cell_periodic_one_or_two_at_col_le_neg_add_twenty_eight T (by omega) (by omega) (by omega) (by omega)
  · exact not_cell_periodic_one_or_two_at_col_le_neg_add_twenty_eight T (by omega) (by omega) (by omega) (by omega)
  · exact not_cell_periodic_three_at_col_le_neg_add_twenty_five T (by omega) (by omega)
  · exact not_cell_periodic_four_at_col_le_neg_add_twenty_three T (by omega) (by omega)
  · exact not_cell_periodic_five_at_col_le_neg_add_twenty_five T (by omega) (by omega)
  · exact not_cell_periodic_six_at_col_le_neg_add_twenty_three T (by omega) (by omega)
  · exact not_cell_periodic_seven_at_col_le_neg_add_twenty_one T (by omega) (by omega)
  · exact not_cell_periodic_eight_at_col_le_neg_add_nineteen T (by omega) (by omega)
  · exact not_cell_periodic_nine_at_col_le_neg_add_twenty_two T (by omega) (by omega)
  · exact not_cell_periodic_ten_at_col_le_neg_add_eighteen T (by omega) (by omega)
  · exact not_cell_periodic_eleven_at_col_le_neg_add_twenty T (by omega) (by omega)
  · exact not_cell_periodic_twelve_at_col_le_neg_add_sixteen T (by omega) (by omega)
  · exact not_cell_periodic_thirteen_at_col_le_neg_add_sixteen T (by omega) (by omega)
  · exact not_cell_periodic_fourteen_at_col_le_neg_add_seventeen T (by omega) (by omega)
  · exact not_cell_periodic_fifteen_at_col_le_neg_add_thirteen T (by omega) (by omega)
  · exact not_cell_periodic_sixteen_at_col_le_neg_add_twelve T (by omega) (by omega)
  · exact not_cell_periodic_seventeen_at_col_le_neg_add_twelve T (by omega) (by omega)
  · exact not_cell_periodic_eighteen_at_col_le_neg_add_ten T (by omega) (by omega)
  · exact not_cell_periodic_nineteen_at_col_le_neg_add_nine T (by omega) (by omega)
  · exact not_cell_periodic_twenty_at_col_le_neg_add_nine T (by omega) (by omega)
  · exact not_cell_periodic_twenty_one_at_col_le_neg_add_twelve T (by omega) (by omega)
  · exact not_cell_periodic_twenty_two_at_col_le_neg_add_seven T (by omega) (by omega)
  · exact not_cell_periodic_twenty_three_at_col_le_neg_add_seven T (by omega) (by omega)
  · exact not_cell_periodic_twenty_four_at_col_le_neg_add_four T (by omega) (by omega)
  · exact not_cell_periodic_twenty_five_at_col_le_neg_add_three T (by omega) (by omega)
  · exact not_cell_periodic_twenty_six_at_col_le_neg_add_six T (by omega) (by omega)
  · exact not_cell_periodic_twenty_seven_at_col_le_neg_add_one T (by omega) (by omega)
  · exact not_cell_periodic_twenty_eight_at_col_le_neg_add_two T (by omega) (by omega)
  · exact not_cell_periodic_twenty_nine_at_col_le_neg_zero T (by omega) (by omega)
  · exact not_cell_periodic_thirty_at_col_le_neg_sub_one T (by omega) (by omega)
  · exact not_cell_periodic_ge_thirty_one_at_col_le_neg_add_add_thirty T h31 (by omega) (by omega)





/-- **Thirty-Column Inward Period-4 Exclusion (`not_cell_periodic_four_at_col_le_neg_add_twenty_six`):**
for every `T : Nat` and column `c ≤ -4` with `c ≤ -(T : Int) + 26` (i.e. `c ≤ -(T + 4) + 30`),
`¬ (∀ t : Nat, T ≤ t → cell (t + 4) c = cell t c)`. -/
theorem not_cell_periodic_four_at_col_le_neg_add_twenty_six (T : Nat) {c : Int}
    (hc0 : c ≤ -4) (hc : c ≤ -(T : Int) + 26) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 4) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 26) (by omega)
  rw [hc_eq, show (s + 26) + 4 = s + 30 by omega, col_at_26 s (by omega), col_at_30 s (by omega)] at h0
  have h1 := hper (s + 27) (by omega)
  rw [hc_eq, show (s + 27) + 4 = s + 31 by omega, col_at_27 s (by omega), col_at_31 s (by omega)] at h1
  have h2 := hper (s + 28) (by omega)
  rw [hc_eq, show (s + 28) + 4 = s + 32 by omega, col_at_28 s (by omega), col_at_32 s (by omega)] at h2
  have h3 := hper (s + 29) (by omega)
  rw [hc_eq, show (s + 29) + 4 = s + 33 by omega, col_at_29 s (by omega), col_at_33 s (by omega)] at h3
  revert h0 h1 h2 h3
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

/-- **Thirty-Three-Column Inward Period-7 Exclusion (`not_cell_periodic_seven_at_col_le_neg_add_twenty_six`):**
for every `T : Nat` and column `c ≤ -6` with `c ≤ -(T : Int) + 26` (i.e. `c ≤ -(T + 7) + 33`),
`¬ (∀ t : Nat, T ≤ t → cell (t + 7) c = cell t c)`. -/
theorem not_cell_periodic_seven_at_col_le_neg_add_twenty_six (T : Nat) {c : Int}
    (hc0 : c ≤ -6) (hc : c ≤ -(T : Int) + 26) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 7) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 26) (by omega)
  rw [hc_eq, show (s + 26) + 7 = s + 33 by omega, col_at_26 s (by omega), col_at_33 s (by omega)] at h0
  have h1 := hper (s + 27) (by omega)
  rw [hc_eq, show (s + 27) + 7 = s + 34 by omega, col_at_27 s (by omega), col_at_34 s (by omega)] at h1
  revert h0 h1
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

/-- **Twenty-Eight-Column Inward Period-8 Exclusion (`not_cell_periodic_eight_at_col_le_neg_add_twenty`):**
for every `T : Nat` and column `c ≤ -4` with `c ≤ -(T : Int) + 20` (i.e. `c ≤ -(T + 8) + 28`),
`¬ (∀ t : Nat, T ≤ t → cell (t + 8) c = cell t c)`. -/
theorem not_cell_periodic_eight_at_col_le_neg_add_twenty (T : Nat) {c : Int}
    (hc0 : c ≤ -4) (hc : c ≤ -(T : Int) + 20) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 8) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 20) (by omega)
  rw [hc_eq, show (s + 20) + 8 = s + 28 by omega, col_at_20 s (by omega), col_at_28 s (by omega)] at h0
  have h1 := hper (s + 21) (by omega)
  rw [hc_eq, show (s + 21) + 8 = s + 29 by omega, col_at_21 s (by omega), col_at_29 s (by omega)] at h1
  have h2 := hper (s + 22) (by omega)
  rw [hc_eq, show (s + 22) + 8 = s + 30 by omega, col_at_22 s (by omega), col_at_30 s (by omega)] at h2
  have h3 := hper (s + 24) (by omega)
  rw [hc_eq, show (s + 24) + 8 = s + 32 by omega, col_at_24 s (by omega), col_at_32 s (by omega)] at h3
  revert h0 h1 h2 h3
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

/-- **Thirty-Two-Column Inward Period-15 Exclusion (`not_cell_periodic_fifteen_at_col_le_neg_add_seventeen`):**
for every `T : Nat` and column `c ≤ -6` with `c ≤ -(T : Int) + 17` (i.e. `c ≤ -(T + 15) + 32`),
`¬ (∀ t : Nat, T ≤ t → cell (t + 15) c = cell t c)`. -/
theorem not_cell_periodic_fifteen_at_col_le_neg_add_seventeen (T : Nat) {c : Int}
    (hc0 : c ≤ -6) (hc : c ≤ -(T : Int) + 17) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 15) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 17) (by omega)
  rw [hc_eq, show (s + 17) + 15 = s + 32 by omega, col_at_17 s (by omega), col_at_32 s (by omega)] at h0
  have h1 := hper (s + 18) (by omega)
  rw [hc_eq, show (s + 18) + 15 = s + 33 by omega, col_at_18 s (by omega), col_at_33 s (by omega)] at h1
  have h2 := hper (s + 19) (by omega)
  rw [hc_eq, show (s + 19) + 15 = s + 34 by omega, col_at_19 s (by omega), col_at_34 s (by omega)] at h2
  revert h0 h1 h2
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

/-- **Thirty-Two-Column Inward Period-16 Exclusion (`not_cell_periodic_sixteen_at_col_le_neg_add_sixteen`):**
for every `T : Nat` and column `c ≤ -6` with `c ≤ -(T : Int) + 16` (i.e. `c ≤ -(T + 16) + 32`),
`¬ (∀ t : Nat, T ≤ t → cell (t + 16) c = cell t c)`. -/
theorem not_cell_periodic_sixteen_at_col_le_neg_add_sixteen (T : Nat) {c : Int}
    (hc0 : c ≤ -6) (hc : c ≤ -(T : Int) + 16) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 16) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 16) (by omega)
  rw [hc_eq, show (s + 16) + 16 = s + 32 by omega, col_at_16 s (by omega), col_at_32 s (by omega)] at h0
  have h1 := hper (s + 18) (by omega)
  rw [hc_eq, show (s + 18) + 16 = s + 34 by omega, col_at_18 s (by omega), col_at_34 s (by omega)] at h1
  revert h0 h1
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

/-- **All-Period Unconditional 28-Column Inward Non-Periodicity
(`not_cell_periodic_at_col_le_neg_add_add_twenty_eight`):**
for every `T : Nat`, every positive period `P > 0`, and every column `c ≤ -6` with
`c ≤ -((T + P : Nat) : Int) + 28`, `cell · c` is not `P`-periodic from `T` on. -/
theorem not_cell_periodic_at_col_le_neg_add_add_twenty_eight (T : Nat) {P : Nat} (hP : 0 < P)
    {c : Int} (hc0 : c ≤ -6) (hc : c ≤ -((T + P : Nat) : Int) + 28) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + P) c = cell t c) := by
  rcases (by omega : P = 1 ∨ P = 2 ∨ P = 3 ∨ P = 4 ∨ P = 5 ∨ P = 6 ∨ P = 7 ∨ P = 8 ∨
      P = 9 ∨ P = 10 ∨ P = 11 ∨ P = 12 ∨ P = 13 ∨ P = 14 ∨ P = 15 ∨ P = 16 ∨ P = 17 ∨
      P = 18 ∨ P = 19 ∨ P = 20 ∨ P = 21 ∨ P = 22 ∨ P = 23 ∨ P = 24 ∨ P = 25 ∨ P = 26 ∨
      P = 27 ∨ P = 28 ∨ P = 29 ∨ P = 30 ∨ 31 ≤ P) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h31
  · exact not_cell_periodic_one_or_two_at_col_le_neg_add_twenty_eight T (by omega) (by omega) (by omega) (by omega)
  · exact not_cell_periodic_one_or_two_at_col_le_neg_add_twenty_eight T (by omega) (by omega) (by omega) (by omega)
  · exact not_cell_periodic_three_at_col_le_neg_add_twenty_five T (by omega) (by omega)
  · exact not_cell_periodic_four_at_col_le_neg_add_twenty_six T (by omega) (by omega)
  · exact not_cell_periodic_five_at_col_le_neg_add_twenty_five T (by omega) (by omega)
  · exact not_cell_periodic_six_at_col_le_neg_add_twenty_three T (by omega) (by omega)
  · exact not_cell_periodic_seven_at_col_le_neg_add_twenty_one T (by omega) (by omega)
  · exact not_cell_periodic_eight_at_col_le_neg_add_twenty T (by omega) (by omega)
  · exact not_cell_periodic_nine_at_col_le_neg_add_twenty_two T (by omega) (by omega)
  · exact not_cell_periodic_ten_at_col_le_neg_add_eighteen T (by omega) (by omega)
  · exact not_cell_periodic_eleven_at_col_le_neg_add_twenty T (by omega) (by omega)
  · exact not_cell_periodic_twelve_at_col_le_neg_add_sixteen T (by omega) (by omega)
  · exact not_cell_periodic_thirteen_at_col_le_neg_add_sixteen T (by omega) (by omega)
  · exact not_cell_periodic_fourteen_at_col_le_neg_add_seventeen T (by omega) (by omega)
  · exact not_cell_periodic_fifteen_at_col_le_neg_add_thirteen T (by omega) (by omega)
  · exact not_cell_periodic_sixteen_at_col_le_neg_add_twelve T (by omega) (by omega)
  · exact not_cell_periodic_seventeen_at_col_le_neg_add_twelve T (by omega) (by omega)
  · exact not_cell_periodic_eighteen_at_col_le_neg_add_ten T (by omega) (by omega)
  · exact not_cell_periodic_nineteen_at_col_le_neg_add_nine T (by omega) (by omega)
  · exact not_cell_periodic_twenty_at_col_le_neg_add_nine T (by omega) (by omega)
  · exact not_cell_periodic_twenty_one_at_col_le_neg_add_twelve T (by omega) (by omega)
  · exact not_cell_periodic_twenty_two_at_col_le_neg_add_seven T (by omega) (by omega)
  · exact not_cell_periodic_twenty_three_at_col_le_neg_add_seven T (by omega) (by omega)
  · exact not_cell_periodic_twenty_four_at_col_le_neg_add_four T (by omega) (by omega)
  · exact not_cell_periodic_twenty_five_at_col_le_neg_add_three T (by omega) (by omega)
  · exact not_cell_periodic_twenty_six_at_col_le_neg_add_six T (by omega) (by omega)
  · exact not_cell_periodic_twenty_seven_at_col_le_neg_add_one T (by omega) (by omega)
  · exact not_cell_periodic_twenty_eight_at_col_le_neg_add_two T (by omega) (by omega)
  · exact not_cell_periodic_twenty_nine_at_col_le_neg_zero T (by omega) (by omega)
  · exact not_cell_periodic_thirty_at_col_le_neg_sub_one T (by omega) (by omega)
  · exact not_cell_periodic_ge_thirty_one_at_col_le_neg_add_add_thirty T h31 (by omega) (by omega)




private theorem d8_s_35 (s : Nat) (hs : 1 ≤ s) : D 8 (s + 35) = !D 10 (s + 8) := by
  rw [show s + 35 = (s + 34) + 1 by omega, D_eight_succ_eq_D_ten (s + 34) (by omega), d10_s_34 s hs]
private theorem d10_s_35 (s : Nat) (hs : 1 ≤ s) : D 10 (s + 35) = D 8 (s + 8) := by
  rw [show s + 35 = (s + 34) + 1 by omega, D_ten_succ_eq_not_D_eight (s + 34) (by omega), d8_s_34 s hs, Bool.not_not]
private theorem d29_s_35 (s : Nat) (hs : 2 ≤ s) : D 29 (s + 35) = xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (D 29 (s + 29))))))) := by
  rw [show s + 35 = (s + 34) + 1 by omega, D_twenty_nine_step_eq_xor_D_twenty_seven (s + 34) (by omega), D_twenty_seven_eq_nand_D_eight_D_ten (s + 34) (by omega), d8_s_34 s (by omega), d10_s_34 s (by omega), d29_s_34 s hs]
private theorem d8_s_36 (s : Nat) (hs : 1 ≤ s) : D 8 (s + 36) = D 8 (s + 8) := by
  rw [show s + 36 = (s + 35) + 1 by omega, D_eight_succ_eq_D_ten (s + 35) (by omega), d10_s_35 s hs]
private theorem d10_s_36 (s : Nat) (hs : 1 ≤ s) : D 10 (s + 36) = D 10 (s + 8) := by
  rw [show s + 36 = (s + 35) + 1 by omega, D_ten_succ_eq_not_D_eight (s + 35) (by omega), d8_s_35 s hs, Bool.not_not]
private theorem d29_s_36 (s : Nat) (hs : 2 ≤ s) : D 29 (s + 36) = xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (D 29 (s + 29)))))))) := by
  rw [show s + 36 = (s + 35) + 1 by omega, D_twenty_nine_step_eq_xor_D_twenty_seven (s + 35) (by omega), D_twenty_seven_eq_nand_D_eight_D_ten (s + 35) (by omega), d8_s_35 s (by omega), d10_s_35 s (by omega), d29_s_35 s hs]

private theorem col_at_35 (s : Nat) (hs : 5 ≤ s) :
    cell (s + 35) (-(s : Int)) = (( !(!D 10 (s + 8)) && xor (D 8 (s + 8)) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (D 29 (s + 29)))))))) ) || ( (!D 10 (s + 8)) && !(D 8 (s + 8)) && !(xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (D 29 (s + 29)))))))) )) := by
  have hd : cell (s + 35) (-(s : Int)) = D 35 (s + 35) := by unfold D; exact cell_congr (by omega)
  rw [hd, D_thirty_five_eq_gate (s + 35) (by omega), d8_s_35 s (by omega), d10_s_35 s (by omega), d29_s_35 s (by omega)]

private theorem col_at_36 (s : Nat) (hs : 10 ≤ s) :
    cell (s + 36) (-(s : Int)) = ( (D 10 (s + 8)) && ( (D 8 (s + 8)) || !(xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (D 29 (s + 29))))))))) ) ) := by
  have hd : cell (s + 36) (-(s : Int)) = D 36 (s + 36) := by unfold D; exact cell_congr (by omega)
  rw [hd, D_thirty_six_eq_gate (s + 36) (by omega), d8_s_36 s (by omega), d10_s_36 s (by omega), d29_s_36 s (by omega)]



theorem not_cell_periodic_three_at_col_le_neg_add_thirty (T : Nat) {c : Int}
    (hc0 : c ≤ -10) (hc : c ≤ -(T : Int) + 30) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 3) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 30) (by omega)
  rw [hc_eq, show (s + 30) + 3 = s + 33 by omega, col_at_30 s (by omega), col_at_33 s (by omega)] at h0
  have h1 := hper (s + 31) (by omega)
  rw [hc_eq, show (s + 31) + 3 = s + 34 by omega, col_at_31 s (by omega), col_at_34 s (by omega)] at h1
  have h2 := hper (s + 33) (by omega)
  rw [hc_eq, show (s + 33) + 3 = s + 36 by omega, col_at_33 s (by omega), col_at_36 s (by omega)] at h2
  revert h0 h1 h2
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_four_at_col_le_neg_add_thirty (T : Nat) {c : Int}
    (hc0 : c ≤ -6) (hc : c ≤ -(T : Int) + 30) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 4) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 30) (by omega)
  rw [hc_eq, show (s + 30) + 4 = s + 34 by omega, col_at_30 s (by omega), col_at_34 s (by omega)] at h0
  have h1 := hper (s + 31) (by omega)
  rw [hc_eq, show (s + 31) + 4 = s + 35 by omega, col_at_31 s (by omega), col_at_35 s (by omega)] at h1
  revert h0 h1
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_ten_at_col_le_neg_add_twenty_two (T : Nat) {c : Int}
    (hc0 : c ≤ -6) (hc : c ≤ -(T : Int) + 22) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 10) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 22) (by omega)
  rw [hc_eq, show (s + 22) + 10 = s + 32 by omega, col_at_22 s (by omega), col_at_32 s (by omega)] at h0
  have h1 := hper (s + 23) (by omega)
  rw [hc_eq, show (s + 23) + 10 = s + 33 by omega, col_at_23 s (by omega), col_at_33 s (by omega)] at h1
  have h2 := hper (s + 24) (by omega)
  rw [hc_eq, show (s + 24) + 10 = s + 34 by omega, col_at_24 s (by omega), col_at_34 s (by omega)] at h2
  have h3 := hper (s + 25) (by omega)
  rw [hc_eq, show (s + 25) + 10 = s + 35 by omega, col_at_25 s (by omega), col_at_35 s (by omega)] at h3
  revert h0 h1 h2 h3
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_twelve_at_col_le_neg_add_twenty_one (T : Nat) {c : Int}
    (hc0 : c ≤ -5) (hc : c ≤ -(T : Int) + 21) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 12) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 21) (by omega)
  rw [hc_eq, show (s + 21) + 12 = s + 33 by omega, col_at_21 s (by omega), col_at_33 s (by omega)] at h0
  have h1 := hper (s + 23) (by omega)
  rw [hc_eq, show (s + 23) + 12 = s + 35 by omega, col_at_23 s (by omega), col_at_35 s (by omega)] at h1
  revert h0 h1
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_thirteen_at_col_le_neg_add_twenty_one (T : Nat) {c : Int}
    (hc0 : c ≤ -6) (hc : c ≤ -(T : Int) + 21) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 13) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 21) (by omega)
  rw [hc_eq, show (s + 21) + 13 = s + 34 by omega, col_at_21 s (by omega), col_at_34 s (by omega)] at h0
  have h1 := hper (s + 22) (by omega)
  rw [hc_eq, show (s + 22) + 13 = s + 35 by omega, col_at_22 s (by omega), col_at_35 s (by omega)] at h1
  revert h0 h1
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_eighteen_at_col_le_neg_add_fifteen (T : Nat) {c : Int}
    (hc0 : c ≤ -5) (hc : c ≤ -(T : Int) + 15) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 18) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 15) (by omega)
  rw [hc_eq, show (s + 15) + 18 = s + 33 by omega, col_at_15 s (by omega), col_at_33 s (by omega)] at h0
  have h1 := hper (s + 17) (by omega)
  rw [hc_eq, show (s + 17) + 18 = s + 35 by omega, col_at_17 s (by omega), col_at_35 s (by omega)] at h1
  revert h0 h1
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_nineteen_at_col_le_neg_add_thirteen (T : Nat) {c : Int}
    (hc0 : c ≤ -6) (hc : c ≤ -(T : Int) + 13) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 19) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 13) (by omega)
  rw [hc_eq, show (s + 13) + 19 = s + 32 by omega, col_at_13 s (by omega), col_at_32 s (by omega)] at h0
  have h1 := hper (s + 15) (by omega)
  rw [hc_eq, show (s + 15) + 19 = s + 34 by omega, col_at_15 s (by omega), col_at_34 s (by omega)] at h1
  revert h0 h1
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_twenty_at_col_le_neg_add_thirteen (T : Nat) {c : Int}
    (hc0 : c ≤ -6) (hc : c ≤ -(T : Int) + 13) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 20) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 13) (by omega)
  rw [hc_eq, show (s + 13) + 20 = s + 33 by omega, col_at_13 s (by omega), col_at_33 s (by omega)] at h0
  have h1 := hper (s + 14) (by omega)
  rw [hc_eq, show (s + 14) + 20 = s + 34 by omega, col_at_14 s (by omega), col_at_34 s (by omega)] at h1
  revert h0 h1
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_twenty_four_at_col_le_neg_add_ten (T : Nat) {c : Int}
    (hc0 : c ≤ -10) (hc : c ≤ -(T : Int) + 10) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 24) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 10) (by omega)
  rw [hc_eq, show (s + 10) + 24 = s + 34 by omega, col_at_10 s (by omega), col_at_34 s (by omega)] at h0
  have h1 := hper (s + 11) (by omega)
  rw [hc_eq, show (s + 11) + 24 = s + 35 by omega, col_at_11 s (by omega), col_at_35 s (by omega)] at h1
  have h2 := hper (s + 12) (by omega)
  rw [hc_eq, show (s + 12) + 24 = s + 36 by omega, col_at_12 s (by omega), col_at_36 s (by omega)] at h2
  revert h0 h1 h2
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_twenty_five_at_col_le_neg_add_eight (T : Nat) {c : Int}
    (hc0 : c ≤ -5) (hc : c ≤ -(T : Int) + 8) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 25) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 8) (by omega)
  rw [hc_eq, show (s + 8) + 25 = s + 33 by omega, col_at_8 s (by omega), col_at_33 s (by omega)] at h0
  have h1 := hper (s + 10) (by omega)
  rw [hc_eq, show (s + 10) + 25 = s + 35 by omega, col_at_10 s (by omega), col_at_35 s (by omega)] at h1
  revert h0 h1
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_twenty_seven_at_col_le_neg_add_five (T : Nat) {c : Int}
    (hc0 : c ≤ -10) (hc : c ≤ -(T : Int) + 5) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 27) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 5) (by omega)
  rw [hc_eq, show (s + 5) + 27 = s + 32 by omega, col_at_5 s (by omega), col_at_32 s (by omega)] at h0
  have h1 := hper (s + 6) (by omega)
  rw [hc_eq, show (s + 6) + 27 = s + 33 by omega, col_at_6 s (by omega), col_at_33 s (by omega)] at h1
  have h2 := hper (s + 8) (by omega)
  rw [hc_eq, show (s + 8) + 27 = s + 35 by omega, col_at_8 s (by omega), col_at_35 s (by omega)] at h2
  have h3 := hper (s + 9) (by omega)
  rw [hc_eq, show (s + 9) + 27 = s + 36 by omega, col_at_9 s (by omega), col_at_36 s (by omega)] at h3
  revert h0 h1 h2 h3
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

/-- **Twenty-Nine-Column Inward Non-Periodicity for All `P ≠ 8`
(`not_cell_periodic_ne_eight_at_col_le_neg_add_add_twenty_nine`):**
for every `T : Nat`, every positive period `P > 0` with `P ≠ 8`, and every column `c ≤ -10` with
`c ≤ -((T + P : Nat) : Int) + 29`, `cell · c` is not `P`-periodic from `T` on. -/
theorem not_cell_periodic_ne_eight_at_col_le_neg_add_add_twenty_nine (T : Nat) {P : Nat}
    (hP : 0 < P) (hne8 : P ≠ 8) {c : Int} (hc0 : c ≤ -10) (hc : c ≤ -((T + P : Nat) : Int) + 29) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + P) c = cell t c) := by
  rcases (by omega : P = 1 ∨ P = 2 ∨ P = 3 ∨ P = 4 ∨ P = 5 ∨ P = 6 ∨ P = 7 ∨
      P = 9 ∨ P = 10 ∨ P = 11 ∨ P = 12 ∨ P = 13 ∨ P = 14 ∨ P = 15 ∨ P = 16 ∨ P = 17 ∨
      P = 18 ∨ P = 19 ∨ P = 20 ∨ P = 21 ∨ P = 22 ∨ P = 23 ∨ P = 24 ∨ P = 25 ∨ P = 26 ∨
      P = 27 ∨ P = 28 ∨ P = 29 ∨ P = 30 ∨ 31 ≤ P) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h31
  · exact not_cell_periodic_one_or_two_at_col_le_neg_add_twenty_eight T (by omega) (by omega) (by omega) (by omega)
  · exact not_cell_periodic_one_or_two_at_col_le_neg_add_twenty_eight T (by omega) (by omega) (by omega) (by omega)
  · exact not_cell_periodic_three_at_col_le_neg_add_thirty T (by omega) (by omega)
  · exact not_cell_periodic_four_at_col_le_neg_add_thirty T (by omega) (by omega)
  · exact not_cell_periodic_five_at_col_le_neg_add_twenty_five T (by omega) (by omega)
  · exact not_cell_periodic_six_at_col_le_neg_add_twenty_three T (by omega) (by omega)
  · exact not_cell_periodic_seven_at_col_le_neg_add_twenty_six T (by omega) (by omega)
  · exact not_cell_periodic_nine_at_col_le_neg_add_twenty_two T (by omega) (by omega)
  · exact not_cell_periodic_ten_at_col_le_neg_add_twenty_two T (by omega) (by omega)
  · exact not_cell_periodic_eleven_at_col_le_neg_add_twenty T (by omega) (by omega)
  · exact not_cell_periodic_twelve_at_col_le_neg_add_twenty_one T (by omega) (by omega)
  · exact not_cell_periodic_thirteen_at_col_le_neg_add_twenty_one T (by omega) (by omega)
  · exact not_cell_periodic_fourteen_at_col_le_neg_add_seventeen T (by omega) (by omega)
  · exact not_cell_periodic_fifteen_at_col_le_neg_add_seventeen T (by omega) (by omega)
  · exact not_cell_periodic_sixteen_at_col_le_neg_add_sixteen T (by omega) (by omega)
  · exact not_cell_periodic_seventeen_at_col_le_neg_add_twelve T (by omega) (by omega)
  · exact not_cell_periodic_eighteen_at_col_le_neg_add_fifteen T (by omega) (by omega)
  · exact not_cell_periodic_nineteen_at_col_le_neg_add_thirteen T (by omega) (by omega)
  · exact not_cell_periodic_twenty_at_col_le_neg_add_thirteen T (by omega) (by omega)
  · exact not_cell_periodic_twenty_one_at_col_le_neg_add_twelve T (by omega) (by omega)
  · exact not_cell_periodic_twenty_two_at_col_le_neg_add_seven T (by omega) (by omega)
  · exact not_cell_periodic_twenty_three_at_col_le_neg_add_seven T (by omega) (by omega)
  · exact not_cell_periodic_twenty_four_at_col_le_neg_add_ten T (by omega) (by omega)
  · exact not_cell_periodic_twenty_five_at_col_le_neg_add_eight T (by omega) (by omega)
  · exact not_cell_periodic_twenty_six_at_col_le_neg_add_six T (by omega) (by omega)
  · exact not_cell_periodic_twenty_seven_at_col_le_neg_add_five T (by omega) (by omega)
  · exact not_cell_periodic_twenty_eight_at_col_le_neg_add_two T (by omega) (by omega)
  · exact not_cell_periodic_twenty_nine_at_col_le_neg_zero T (by omega) (by omega)
  · exact not_cell_periodic_thirty_at_col_le_neg_sub_one T (by omega) (by omega)
  · exact not_cell_periodic_ge_thirty_one_at_col_le_neg_add_add_thirty T h31 (by omega) (by omega)

/-- **Thirty-One-Column Inward Non-Periodicity for Intermediate Periods `P ∈ {4, 5, 7, 9, 10, 11, 12, 13, 14, 15, 16, 18, 19, 20, 21, 24, 25, 26, 27}`
(`not_cell_periodic_thirty_one_inward_of_four_to_twenty_seven`):**
for every `T : Nat`, every `P ∈ {4, 7, 9, 10, 11, 12, 13, 14, 15, 16, 18, 19, 20, 21, 24, 25, 26, 27}`,
and every column `c ≤ -10` with `c ≤ -((T + P : Nat) : Int) + 31`, `cell · c` is not `P`-periodic from `T` on. -/
theorem not_cell_periodic_thirty_one_inward_of_four_to_twenty_seven (T : Nat) {P : Nat}
    (hP : P = 4 ∨ P = 7 ∨ P = 9 ∨ P = 10 ∨ P = 11 ∨ P = 12 ∨ P = 13 ∨ P = 14 ∨ P = 15 ∨
          P = 16 ∨ P = 18 ∨ P = 19 ∨ P = 20 ∨ P = 21 ∨ P = 24 ∨ P = 25 ∨ P = 26 ∨ P = 27)
    {c : Int} (hc0 : c ≤ -10) (hc : c ≤ -((T + P : Nat) : Int) + 31) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + P) c = cell t c) := by
  rcases hP with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_cell_periodic_four_at_col_le_neg_add_thirty T (by omega) (by omega)
  · exact not_cell_periodic_seven_at_col_le_neg_add_twenty_six T (by omega) (by omega)
  · exact not_cell_periodic_nine_at_col_le_neg_add_twenty_two T (by omega) (by omega)
  · exact not_cell_periodic_ten_at_col_le_neg_add_twenty_two T (by omega) (by omega)
  · exact not_cell_periodic_eleven_at_col_le_neg_add_twenty T (by omega) (by omega)
  · exact not_cell_periodic_twelve_at_col_le_neg_add_twenty_one T (by omega) (by omega)
  · exact not_cell_periodic_thirteen_at_col_le_neg_add_twenty_one T (by omega) (by omega)
  · exact not_cell_periodic_fourteen_at_col_le_neg_add_seventeen T (by omega) (by omega)
  · exact not_cell_periodic_fifteen_at_col_le_neg_add_seventeen T (by omega) (by omega)
  · exact not_cell_periodic_sixteen_at_col_le_neg_add_sixteen T (by omega) (by omega)
  · exact not_cell_periodic_eighteen_at_col_le_neg_add_fifteen T (by omega) (by omega)
  · exact not_cell_periodic_nineteen_at_col_le_neg_add_thirteen T (by omega) (by omega)
  · exact not_cell_periodic_twenty_at_col_le_neg_add_thirteen T (by omega) (by omega)
  · exact not_cell_periodic_twenty_one_at_col_le_neg_add_twelve T (by omega) (by omega)
  · exact not_cell_periodic_twenty_four_at_col_le_neg_add_ten T (by omega) (by omega)
  · exact not_cell_periodic_twenty_five_at_col_le_neg_add_eight T (by omega) (by omega)
  · exact not_cell_periodic_twenty_six_at_col_le_neg_add_six T (by omega) (by omega)
  · exact not_cell_periodic_twenty_seven_at_col_le_neg_add_five T (by omega) (by omega)




private theorem d8_s_37 (s : Nat) (hs : 1 ≤ s) : D 8 (s + 37) = D 10 (s + 8) := by
  rw [show s + 37 = (s + 36) + 1 by omega, D_eight_succ_eq_D_ten (s + 36) (by omega), d10_s_36 s hs]
private theorem d10_s_37 (s : Nat) (hs : 1 ≤ s) : D 10 (s + 37) = !D 8 (s + 8) := by
  rw [show s + 37 = (s + 36) + 1 by omega, D_ten_succ_eq_not_D_eight (s + 36) (by omega), d8_s_36 s hs]
private theorem d29_s_37 (s : Nat) (hs : 2 ≤ s) : D 29 (s + 37) = xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (D 29 (s + 29))))))))) := by
  rw [show s + 37 = (s + 36) + 1 by omega, D_twenty_nine_step_eq_xor_D_twenty_seven (s + 36) (by omega), D_twenty_seven_eq_nand_D_eight_D_ten (s + 36) (by omega), d8_s_36 s (by omega), d10_s_36 s (by omega), d29_s_36 s hs]
private theorem d8_s_38 (s : Nat) (hs : 1 ≤ s) : D 8 (s + 38) = !D 8 (s + 8) := by
  rw [show s + 38 = (s + 37) + 1 by omega, D_eight_succ_eq_D_ten (s + 37) (by omega), d10_s_37 s hs]
private theorem d10_s_38 (s : Nat) (hs : 1 ≤ s) : D 10 (s + 38) = !D 10 (s + 8) := by
  rw [show s + 38 = (s + 37) + 1 by omega, D_ten_succ_eq_not_D_eight (s + 37) (by omega), d8_s_37 s hs]
private theorem d29_s_38 (s : Nat) (hs : 2 ≤ s) : D 29 (s + 38) = xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (D 29 (s + 29)))))))))) := by
  rw [show s + 38 = (s + 37) + 1 by omega, D_twenty_nine_step_eq_xor_D_twenty_seven (s + 37) (by omega), D_twenty_seven_eq_nand_D_eight_D_ten (s + 37) (by omega), d8_s_37 s (by omega), d10_s_37 s (by omega), d29_s_37 s hs]
private theorem d8_s_39 (s : Nat) (hs : 1 ≤ s) : D 8 (s + 39) = !D 10 (s + 8) := by
  rw [show s + 39 = (s + 38) + 1 by omega, D_eight_succ_eq_D_ten (s + 38) (by omega), d10_s_38 s hs]
private theorem d10_s_39 (s : Nat) (hs : 1 ≤ s) : D 10 (s + 39) = D 8 (s + 8) := by
  rw [show s + 39 = (s + 38) + 1 by omega, D_ten_succ_eq_not_D_eight (s + 38) (by omega), d8_s_38 s hs, Bool.not_not]
private theorem d29_s_39 (s : Nat) (hs : 2 ≤ s) : D 29 (s + 39) = xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (D 29 (s + 29))))))))))) := by
  rw [show s + 39 = (s + 38) + 1 by omega, D_twenty_nine_step_eq_xor_D_twenty_seven (s + 38) (by omega), D_twenty_seven_eq_nand_D_eight_D_ten (s + 38) (by omega), d8_s_38 s (by omega), d10_s_38 s (by omega), d29_s_38 s hs]
private theorem d8_s_40 (s : Nat) (hs : 1 ≤ s) : D 8 (s + 40) = D 8 (s + 8) := by
  rw [show s + 40 = (s + 39) + 1 by omega, D_eight_succ_eq_D_ten (s + 39) (by omega), d10_s_39 s hs]
private theorem d10_s_40 (s : Nat) (hs : 1 ≤ s) : D 10 (s + 40) = D 10 (s + 8) := by
  rw [show s + 40 = (s + 39) + 1 by omega, D_ten_succ_eq_not_D_eight (s + 39) (by omega), d8_s_39 s hs, Bool.not_not]
private theorem d29_s_40 (s : Nat) (hs : 2 ≤ s) : D 29 (s + 40) = xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (D 29 (s + 29)))))))))))) := by
  rw [show s + 40 = (s + 39) + 1 by omega, D_twenty_nine_step_eq_xor_D_twenty_seven (s + 39) (by omega), D_twenty_seven_eq_nand_D_eight_D_ten (s + 39) (by omega), d8_s_39 s (by omega), d10_s_39 s (by omega), d29_s_39 s hs]
private theorem d8_s_41 (s : Nat) (hs : 1 ≤ s) : D 8 (s + 41) = D 10 (s + 8) := by
  rw [show s + 41 = (s + 40) + 1 by omega, D_eight_succ_eq_D_ten (s + 40) (by omega), d10_s_40 s hs]
private theorem d10_s_41 (s : Nat) (hs : 1 ≤ s) : D 10 (s + 41) = !D 8 (s + 8) := by
  rw [show s + 41 = (s + 40) + 1 by omega, D_ten_succ_eq_not_D_eight (s + 40) (by omega), d8_s_40 s hs]
private theorem d29_s_41 (s : Nat) (hs : 2 ≤ s) : D 29 (s + 41) = xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (D 29 (s + 29))))))))))))) := by
  rw [show s + 41 = (s + 40) + 1 by omega, D_twenty_nine_step_eq_xor_D_twenty_seven (s + 40) (by omega), D_twenty_seven_eq_nand_D_eight_D_ten (s + 40) (by omega), d8_s_40 s (by omega), d10_s_40 s (by omega), d29_s_40 s hs]

private theorem col_at_38 (s : Nat) (hs : 10 ≤ s) :
    cell (s + 38) (-(s : Int)) = ( !(!D 8 (s + 8)) || xor (!D 10 (s + 8)) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (D 29 (s + 29))))))))))) ) := by
  have hd : cell (s + 38) (-(s : Int)) = D 38 (s + 38) := by unfold D; exact cell_congr (by omega)
  rw [hd, D_thirty_eight_eq_gate (s + 38) (by omega), d8_s_38 s (by omega), d10_s_38 s (by omega), d29_s_38 s (by omega)]

private theorem col_at_39 (s : Nat) (hs : 11 ≤ s) :
    cell (s + 39) (-(s : Int)) = ( !(!D 10 (s + 8)) && xor (D 8 (s + 8)) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (D 29 (s + 29)))))))))))) ) := by
  have hd : cell (s + 39) (-(s : Int)) = D 39 (s + 39) := by unfold D; exact cell_congr (by omega)
  rw [hd, D_thirty_nine_eq_gate (s + 39) (by omega), d8_s_39 s (by omega), d10_s_39 s (by omega), d29_s_39 s (by omega)]

private theorem col_at_40 (s : Nat) (hs : 15 ≤ s) :
    cell (s + 40) (-(s : Int)) = ( !(xor (D 8 (s + 8)) (D 10 (s + 8))) && !(xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (D 29 (s + 29))))))))))))) ) := by
  have hd : cell (s + 40) (-(s : Int)) = D 40 (s + 40) := by unfold D; exact cell_congr (by omega)
  rw [hd, D_forty_eq_gate (s + 40) (by omega), d8_s_40 s (by omega), d10_s_40 s (by omega), d29_s_40 s (by omega)]

private theorem col_at_41 (s : Nat) (hs : 14 ≤ s) :
    cell (s + 41) (-(s : Int)) = ( (D 10 (s + 8)) || !(!D 8 (s + 8)) || (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (D 29 (s + 29)))))))))))))) ) := by
  have hd : cell (s + 41) (-(s : Int)) = D 41 (s + 41) := by unfold D; exact cell_congr (by omega)
  rw [hd, D_forty_one_eq_gate (s + 41) (by omega), d8_s_41 s (by omega), d10_s_41 s (by omega), d29_s_41 s (by omega)]


/-- **Thirty-Eight-Column Inward Period-8 Exclusion (`not_cell_periodic_eight_at_col_le_neg_add_thirty`):**
for every `T : Nat` and column `c ≤ -15` with `c ≤ -(T : Int) + 30` (i.e. `c ≤ -(T + 8) + 38`),
`¬ (∀ t : Nat, T ≤ t → cell (t + 8) c = cell t c)`. -/
theorem not_cell_periodic_eight_at_col_le_neg_add_thirty (T : Nat) {c : Int}
    (hc0 : c ≤ -15) (hc : c ≤ -(T : Int) + 30) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 8) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 30) (by omega)
  rw [hc_eq, show (s + 30) + 8 = s + 38 by omega, col_at_30 s (by omega), col_at_38 s (by omega)] at h0
  have h1 := hper (s + 31) (by omega)
  rw [hc_eq, show (s + 31) + 8 = s + 39 by omega, col_at_31 s (by omega), col_at_39 s (by omega)] at h1
  have h2 := hper (s + 32) (by omega)
  rw [hc_eq, show (s + 32) + 8 = s + 40 by omega, col_at_32 s (by omega), col_at_40 s (by omega)] at h2
  have h3 := hper (s + 33) (by omega)
  rw [hc_eq, show (s + 33) + 8 = s + 41 by omega, col_at_33 s (by omega), col_at_41 s (by omega)] at h3
  revert h0 h1 h2 h3
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

/-- **Thirty-Nine-Column Inward Period-17 Exclusion (`not_cell_periodic_seventeen_at_col_le_neg_add_twenty_two`):**
for every `T : Nat` and column `c ≤ -15` with `c ≤ -(T : Int) + 22` (i.e. `c ≤ -(T + 17) + 39`),
`¬ (∀ t : Nat, T ≤ t → cell (t + 17) c = cell t c)`. -/
theorem not_cell_periodic_seventeen_at_col_le_neg_add_twenty_two (T : Nat) {c : Int}
    (hc0 : c ≤ -15) (hc : c ≤ -(T : Int) + 22) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 17) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 22) (by omega)
  rw [hc_eq, show (s + 22) + 17 = s + 39 by omega, col_at_22 s (by omega), col_at_39 s (by omega)] at h0
  have h1 := hper (s + 23) (by omega)
  rw [hc_eq, show (s + 23) + 17 = s + 40 by omega, col_at_23 s (by omega), col_at_40 s (by omega)] at h1
  revert h0 h1
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

/-- **All-Period Unconditional 29-Column Inward Non-Periodicity
(`not_cell_periodic_at_col_le_neg_add_add_twenty_nine`):**
for every `T : Nat`, every positive period `P > 0`, and every column `c ≤ -15` with
`c ≤ -((T + P : Nat) : Int) + 29`, `cell · c` is not `P`-periodic from `T` on. -/
theorem not_cell_periodic_at_col_le_neg_add_add_twenty_nine (T : Nat) {P : Nat}
    (hP : 0 < P) {c : Int} (hc0 : c ≤ -15) (hc : c ≤ -((T + P : Nat) : Int) + 29) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + P) c = cell t c) := by
  by_cases h8 : P = 8
  · subst h8
    exact not_cell_periodic_eight_at_col_le_neg_add_thirty T (by omega) (by omega)
  · exact not_cell_periodic_ne_eight_at_col_le_neg_add_add_twenty_nine T hP h8 (by omega) hc

/-- **Thirty-One-Column Inward Non-Periodicity Across 21 Periods `P ∈ {3, 4, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 24, 25, 26, 27}`
(`not_cell_periodic_thirty_one_inward_of_three_to_twenty_seven`):**
for every `T : Nat`, every `P` in the 21-period set, and every column `c ≤ -15` with
`c ≤ -((T + P : Nat) : Int) + 31`, `cell · c` is not `P`-periodic from `T` on. -/
theorem not_cell_periodic_thirty_one_inward_of_three_to_twenty_seven (T : Nat) {P : Nat}
    (hP : P = 3 ∨ P = 4 ∨ P = 7 ∨ P = 8 ∨ P = 9 ∨ P = 10 ∨ P = 11 ∨ P = 12 ∨ P = 13 ∨
          P = 14 ∨ P = 15 ∨ P = 16 ∨ P = 17 ∨ P = 18 ∨ P = 19 ∨ P = 20 ∨ P = 21 ∨ P = 24 ∨
          P = 25 ∨ P = 26 ∨ P = 27)
    {c : Int} (hc0 : c ≤ -15) (hc : c ≤ -((T + P : Nat) : Int) + 31) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + P) c = cell t c) := by
  rcases hP with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_cell_periodic_three_at_col_le_neg_add_thirty T (by omega) (by omega)
  · exact not_cell_periodic_four_at_col_le_neg_add_thirty T (by omega) (by omega)
  · exact not_cell_periodic_seven_at_col_le_neg_add_twenty_six T (by omega) (by omega)
  · exact not_cell_periodic_eight_at_col_le_neg_add_thirty T (by omega) (by omega)
  · exact not_cell_periodic_nine_at_col_le_neg_add_twenty_two T (by omega) (by omega)
  · exact not_cell_periodic_ten_at_col_le_neg_add_twenty_two T (by omega) (by omega)
  · exact not_cell_periodic_eleven_at_col_le_neg_add_twenty T (by omega) (by omega)
  · exact not_cell_periodic_twelve_at_col_le_neg_add_twenty_one T (by omega) (by omega)
  · exact not_cell_periodic_thirteen_at_col_le_neg_add_twenty_one T (by omega) (by omega)
  · exact not_cell_periodic_fourteen_at_col_le_neg_add_seventeen T (by omega) (by omega)
  · exact not_cell_periodic_fifteen_at_col_le_neg_add_seventeen T (by omega) (by omega)
  · exact not_cell_periodic_sixteen_at_col_le_neg_add_sixteen T (by omega) (by omega)
  · exact not_cell_periodic_seventeen_at_col_le_neg_add_twenty_two T (by omega) (by omega)
  · exact not_cell_periodic_eighteen_at_col_le_neg_add_fifteen T (by omega) (by omega)
  · exact not_cell_periodic_nineteen_at_col_le_neg_add_thirteen T (by omega) (by omega)
  · exact not_cell_periodic_twenty_at_col_le_neg_add_thirteen T (by omega) (by omega)
  · exact not_cell_periodic_twenty_one_at_col_le_neg_add_twelve T (by omega) (by omega)
  · exact not_cell_periodic_twenty_four_at_col_le_neg_add_ten T (by omega) (by omega)
  · exact not_cell_periodic_twenty_five_at_col_le_neg_add_eight T (by omega) (by omega)
  · exact not_cell_periodic_twenty_six_at_col_le_neg_add_six T (by omega) (by omega)
  · exact not_cell_periodic_twenty_seven_at_col_le_neg_add_five T (by omega) (by omega)


/-! ### 15. Complete All-Period Unconditional 31-Column Inward Non-Periodicity Closure -/

theorem not_cell_periodic_one_at_col_le_neg_add_thirty (T : Nat) {c : Int}
    (hc0 : c ≤ -6) (hc : c ≤ -(T : Int) + 30) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 1) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 30) (by omega)
  rw [hc_eq, show (s + 30) + 1 = s + 31 by omega, col_at_30 s (by omega), col_at_31 s (by omega)] at h0
  have h1 := hper (s + 31) (by omega)
  rw [hc_eq, show (s + 31) + 1 = s + 32 by omega, col_at_31 s (by omega), col_at_32 s (by omega)] at h1
  have h2 := hper (s + 32) (by omega)
  rw [hc_eq, show (s + 32) + 1 = s + 33 by omega, col_at_32 s (by omega), col_at_33 s (by omega)] at h2
  have h3 := hper (s + 33) (by omega)
  rw [hc_eq, show (s + 33) + 1 = s + 34 by omega, col_at_33 s (by omega), col_at_34 s (by omega)] at h3
  revert h0 h1 h2 h3
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_two_at_col_le_neg_add_thirty (T : Nat) {c : Int}
    (hc0 : c ≤ -6) (hc : c ≤ -(T : Int) + 30) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 2) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 30) (by omega)
  rw [hc_eq, show (s + 30) + 2 = s + 32 by omega, col_at_30 s (by omega), col_at_32 s (by omega)] at h0
  have h1 := hper (s + 31) (by omega)
  rw [hc_eq, show (s + 31) + 2 = s + 33 by omega, col_at_31 s (by omega), col_at_33 s (by omega)] at h1
  have h2 := hper (s + 32) (by omega)
  rw [hc_eq, show (s + 32) + 2 = s + 34 by omega, col_at_32 s (by omega), col_at_34 s (by omega)] at h2
  revert h0 h1 h2
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_five_at_col_le_neg_add_twenty_nine (T : Nat) {c : Int}
    (hc0 : c ≤ -10) (hc : c ≤ -(T : Int) + 29) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 5) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 29) (by omega)
  rw [hc_eq, show (s + 29) + 5 = s + 34 by omega, col_at_29 s (by omega), col_at_34 s (by omega)] at h0
  have h1 := hper (s + 30) (by omega)
  rw [hc_eq, show (s + 30) + 5 = s + 35 by omega, col_at_30 s (by omega), col_at_35 s (by omega)] at h1
  have h2 := hper (s + 31) (by omega)
  rw [hc_eq, show (s + 31) + 5 = s + 36 by omega, col_at_31 s (by omega), col_at_36 s (by omega)] at h2
  revert h0 h1 h2
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_six_at_col_le_neg_add_twenty_seven (T : Nat) {c : Int}
    (hc0 : c ≤ -10) (hc : c ≤ -(T : Int) + 27) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 6) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 27) (by omega)
  rw [hc_eq, show (s + 27) + 6 = s + 33 by omega, col_at_27 s (by omega), col_at_33 s (by omega)] at h0
  have h1 := hper (s + 28) (by omega)
  rw [hc_eq, show (s + 28) + 6 = s + 34 by omega, col_at_28 s (by omega), col_at_34 s (by omega)] at h1
  have h2 := hper (s + 30) (by omega)
  rw [hc_eq, show (s + 30) + 6 = s + 36 by omega, col_at_30 s (by omega), col_at_36 s (by omega)] at h2
  revert h0 h1 h2
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_twenty_two_at_col_le_neg_add_eleven (T : Nat) {c : Int}
    (hc0 : c ≤ -10) (hc : c ≤ -(T : Int) + 11) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 22) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 11) (by omega)
  rw [hc_eq, show (s + 11) + 22 = s + 33 by omega, col_at_11 s (by omega), col_at_33 s (by omega)] at h0
  have h1 := hper (s + 12) (by omega)
  rw [hc_eq, show (s + 12) + 22 = s + 34 by omega, col_at_12 s (by omega), col_at_34 s (by omega)] at h1
  have h2 := hper (s + 13) (by omega)
  rw [hc_eq, show (s + 13) + 22 = s + 35 by omega, col_at_13 s (by omega), col_at_35 s (by omega)] at h2
  have h3 := hper (s + 14) (by omega)
  rw [hc_eq, show (s + 14) + 22 = s + 36 by omega, col_at_14 s (by omega), col_at_36 s (by omega)] at h3
  revert h0 h1 h2 h3
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_twenty_three_at_col_le_neg_add_eight (T : Nat) {c : Int}
    (hc0 : c ≤ -6) (hc : c ≤ -(T : Int) + 8) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 23) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 8) (by omega)
  rw [hc_eq, show (s + 8) + 23 = s + 31 by omega, col_at_8 s (by omega), col_at_31 s (by omega)] at h0
  have h1 := hper (s + 9) (by omega)
  rw [hc_eq, show (s + 9) + 23 = s + 32 by omega, col_at_9 s (by omega), col_at_32 s (by omega)] at h1
  have h2 := hper (s + 11) (by omega)
  rw [hc_eq, show (s + 11) + 23 = s + 34 by omega, col_at_11 s (by omega), col_at_34 s (by omega)] at h2
  revert h0 h1 h2
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_twenty_eight_at_col_le_neg_add_five (T : Nat) {c : Int}
    (hc0 : c ≤ -10) (hc : c ≤ -(T : Int) + 5) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 28) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 5) (by omega)
  rw [hc_eq, show (s + 5) + 28 = s + 33 by omega, col_at_5 s (by omega), col_at_33 s (by omega)] at h0
  have h1 := hper (s + 6) (by omega)
  rw [hc_eq, show (s + 6) + 28 = s + 34 by omega, col_at_6 s (by omega), col_at_34 s (by omega)] at h1
  have h2 := hper (s + 7) (by omega)
  rw [hc_eq, show (s + 7) + 28 = s + 35 by omega, col_at_7 s (by omega), col_at_35 s (by omega)] at h2
  have h3 := hper (s + 8) (by omega)
  rw [hc_eq, show (s + 8) + 28 = s + 36 by omega, col_at_8 s (by omega), col_at_36 s (by omega)] at h3
  revert h0 h1 h2 h3
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_twenty_nine_at_col_le_neg_add_three (T : Nat) {c : Int}
    (hc0 : c ≤ -5) (hc : c ≤ -(T : Int) + 3) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 29) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 3) (by omega)
  rw [hc_eq, show (s + 3) + 29 = s + 32 by omega, col_at_3 s (by omega), col_at_32 s (by omega)] at h0
  have h1 := hper (s + 4) (by omega)
  rw [hc_eq, show (s + 4) + 29 = s + 33 by omega, col_at_4 s (by omega), col_at_33 s (by omega)] at h1
  have h2 := hper (s + 6) (by omega)
  rw [hc_eq, show (s + 6) + 29 = s + 35 by omega, col_at_6 s (by omega), col_at_35 s (by omega)] at h2
  revert h0 h1 h2
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_thirty_at_col_le_neg_add_two (T : Nat) {c : Int}
    (hc0 : c ≤ -10) (hc : c ≤ -(T : Int) + 2) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 30) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 2) (by omega)
  rw [hc_eq, show (s + 2) + 30 = s + 32 by omega, col_at_2 s (by omega), col_at_32 s (by omega)] at h0
  have h1 := hper (s + 3) (by omega)
  rw [hc_eq, show (s + 3) + 30 = s + 33 by omega, col_at_3 s (by omega), col_at_33 s (by omega)] at h1
  have h2 := hper (s + 5) (by omega)
  rw [hc_eq, show (s + 5) + 30 = s + 35 by omega, col_at_5 s (by omega), col_at_35 s (by omega)] at h2
  have h3 := hper (s + 6) (by omega)
  rw [hc_eq, show (s + 6) + 30 = s + 36 by omega, col_at_6 s (by omega), col_at_36 s (by omega)] at h3
  revert h0 h1 h2 h3
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_thirty_one_at_col_le_neg_zero (T : Nat) {c : Int}
    (hc0 : c ≤ -4) (hc : c ≤ -(T : Int)) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 31) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 0) (by omega)
  rw [hc_eq, show (s + 0) + 31 = s + 31 by omega, col_at_0 s (by omega), col_at_31 s (by omega)] at h0
  have h1 := hper (s + 1) (by omega)
  rw [hc_eq, show (s + 1) + 31 = s + 32 by omega, col_at_1 s (by omega), col_at_32 s (by omega)] at h1
  revert h0 h1
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_thirty_two_at_col_le_neg_zero (T : Nat) {c : Int}
    (hc0 : c ≤ -6) (hc : c ≤ -(T : Int)) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 32) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 0) (by omega)
  rw [hc_eq, show (s + 0) + 32 = s + 32 by omega, col_at_0 s (by omega), col_at_32 s (by omega)] at h0
  have h1 := hper (s + 1) (by omega)
  rw [hc_eq, show (s + 1) + 32 = s + 33 by omega, col_at_1 s (by omega), col_at_33 s (by omega)] at h1
  have h2 := hper (s + 2) (by omega)
  rw [hc_eq, show (s + 2) + 32 = s + 34 by omega, col_at_2 s (by omega), col_at_34 s (by omega)] at h2
  revert h0 h1 h2
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_thirty_three_at_col_le_neg_sub_two (T : Nat) {c : Int}
    (hc0 : c ≤ -4) (hc : c ≤ -(T : Int) - 2) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 33) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s - 2) (by omega)
  rw [hc_eq, show (s - 2) + 33 = s + 31 by omega, cell_eq_false_of_lt (s - 2) (-(s : Int)) (by omega), col_at_31 s (by omega)] at h0
  have h1 := hper (s - 1) (by omega)
  rw [hc_eq, show (s - 1) + 33 = s + 32 by omega, cell_eq_false_of_lt (s - 1) (-(s : Int)) (by omega), col_at_32 s (by omega)] at h1
  have h2 := hper (s + 0) (by omega)
  rw [hc_eq, show (s + 0) + 33 = s + 33 by omega, col_at_0 s (by omega), col_at_33 s (by omega)] at h2
  revert h0 h1 h2
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_thirty_four_at_col_le_neg_sub_one (T : Nat) {c : Int}
    (hc0 : c ≤ -10) (hc : c ≤ -(T : Int) - 1) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + 34) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s - 1) (by omega)
  rw [hc_eq, show (s - 1) + 34 = s + 33 by omega, cell_eq_false_of_lt (s - 1) (-(s : Int)) (by omega), col_at_33 s (by omega)] at h0
  have h1 := hper (s + 0) (by omega)
  rw [hc_eq, show (s + 0) + 34 = s + 34 by omega, col_at_0 s (by omega), col_at_34 s (by omega)] at h1
  have h2 := hper (s + 1) (by omega)
  rw [hc_eq, show (s + 1) + 34 = s + 35 by omega, col_at_1 s (by omega), col_at_35 s (by omega)] at h2
  have h3 := hper (s + 2) (by omega)
  rw [hc_eq, show (s + 2) + 34 = s + 36 by omega, col_at_2 s (by omega), col_at_36 s (by omega)] at h3
  revert h0 h1 h2 h3
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

/-- **Thirty-One-Column Inward Non-Periodicity for All Large Periods `P ≥ 35`
(`not_cell_periodic_ge_thirty_five_at_col_le_neg_add_add_thirty_one`):**
for every `T : Nat`, every period `P ≥ 35`, and every column `c ≤ -6` with
`c ≤ -((T + P : Nat) : Int) + 31`, `¬ (∀ t : Nat, T ≤ t → cell (t + P) c = cell t c)`. -/
theorem not_cell_periodic_ge_thirty_five_at_col_le_neg_add_add_thirty_one (T : Nat) {P : Nat}
    (hP : 35 ≤ P) {c : Int} (hc0 : c ≤ -6) (hc : c ≤ -((T + P : Nat) : Int) + 31) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + P) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 31 - P) (by omega)
  rw [hc_eq, show (s + 31 - P) + P = s + 31 by omega,
      cell_eq_false_of_lt (s + 31 - P) (-(s : Int)) (by omega), col_at_31 s (by omega)] at h0
  have h1 := hper (s + 32 - P) (by omega)
  rw [hc_eq, show (s + 32 - P) + P = s + 32 by omega,
      cell_eq_false_of_lt (s + 32 - P) (-(s : Int)) (by omega), col_at_32 s (by omega)] at h1
  have h2 := hper (s + 34 - P) (by omega)
  rw [hc_eq, show (s + 34 - P) + P = s + 34 by omega,
      cell_eq_false_of_lt (s + 34 - P) (-(s : Int)) (by omega), col_at_34 s (by omega)] at h2
  revert h0 h1 h2
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

/-- **All-Period Unconditional 31-Column Inward Non-Periodicity
(`not_cell_periodic_at_col_le_neg_add_add_thirty_one`):**
for every `T : Nat`, every positive period `P > 0`, and every column `c ≤ -15` with
`c ≤ -((T + P : Nat) : Int) + 31`, `cell · c` is not `P`-periodic from `T` on. -/
theorem not_cell_periodic_at_col_le_neg_add_add_thirty_one (T : Nat) {P : Nat}
    (hP : 0 < P) {c : Int} (hc0 : c ≤ -15) (hc : c ≤ -((T + P : Nat) : Int) + 31) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + P) c = cell t c) := by
  rcases (by omega : P = 1 ∨ P = 2 ∨ P = 3 ∨ P = 4 ∨ P = 5 ∨ P = 6 ∨ P = 7 ∨ P = 8 ∨
      P = 9 ∨ P = 10 ∨ P = 11 ∨ P = 12 ∨ P = 13 ∨ P = 14 ∨ P = 15 ∨ P = 16 ∨ P = 17 ∨
      P = 18 ∨ P = 19 ∨ P = 20 ∨ P = 21 ∨ P = 22 ∨ P = 23 ∨ P = 24 ∨ P = 25 ∨ P = 26 ∨
      P = 27 ∨ P = 28 ∨ P = 29 ∨ P = 30 ∨ P = 31 ∨ P = 32 ∨ P = 33 ∨ P = 34 ∨ 35 ≤ P) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | h35
  · exact not_cell_periodic_one_at_col_le_neg_add_thirty T (by omega) (by omega)
  · exact not_cell_periodic_two_at_col_le_neg_add_thirty T (by omega) (by omega)
  · exact not_cell_periodic_three_at_col_le_neg_add_thirty T (by omega) (by omega)
  · exact not_cell_periodic_four_at_col_le_neg_add_thirty T (by omega) (by omega)
  · exact not_cell_periodic_five_at_col_le_neg_add_twenty_nine T (by omega) (by omega)
  · exact not_cell_periodic_six_at_col_le_neg_add_twenty_seven T (by omega) (by omega)
  · exact not_cell_periodic_seven_at_col_le_neg_add_twenty_six T (by omega) (by omega)
  · exact not_cell_periodic_eight_at_col_le_neg_add_thirty T (by omega) (by omega)
  · exact not_cell_periodic_nine_at_col_le_neg_add_twenty_two T (by omega) (by omega)
  · exact not_cell_periodic_ten_at_col_le_neg_add_twenty_two T (by omega) (by omega)
  · exact not_cell_periodic_eleven_at_col_le_neg_add_twenty T (by omega) (by omega)
  · exact not_cell_periodic_twelve_at_col_le_neg_add_twenty_one T (by omega) (by omega)
  · exact not_cell_periodic_thirteen_at_col_le_neg_add_twenty_one T (by omega) (by omega)
  · exact not_cell_periodic_fourteen_at_col_le_neg_add_seventeen T (by omega) (by omega)
  · exact not_cell_periodic_fifteen_at_col_le_neg_add_seventeen T (by omega) (by omega)
  · exact not_cell_periodic_sixteen_at_col_le_neg_add_sixteen T (by omega) (by omega)
  · exact not_cell_periodic_seventeen_at_col_le_neg_add_twenty_two T (by omega) (by omega)
  · exact not_cell_periodic_eighteen_at_col_le_neg_add_fifteen T (by omega) (by omega)
  · exact not_cell_periodic_nineteen_at_col_le_neg_add_thirteen T (by omega) (by omega)
  · exact not_cell_periodic_twenty_at_col_le_neg_add_thirteen T (by omega) (by omega)
  · exact not_cell_periodic_twenty_one_at_col_le_neg_add_twelve T (by omega) (by omega)
  · exact not_cell_periodic_twenty_two_at_col_le_neg_add_eleven T (by omega) (by omega)
  · exact not_cell_periodic_twenty_three_at_col_le_neg_add_eight T (by omega) (by omega)
  · exact not_cell_periodic_twenty_four_at_col_le_neg_add_ten T (by omega) (by omega)
  · exact not_cell_periodic_twenty_five_at_col_le_neg_add_eight T (by omega) (by omega)
  · exact not_cell_periodic_twenty_six_at_col_le_neg_add_six T (by omega) (by omega)
  · exact not_cell_periodic_twenty_seven_at_col_le_neg_add_five T (by omega) (by omega)
  · exact not_cell_periodic_twenty_eight_at_col_le_neg_add_five T (by omega) (by omega)
  · exact not_cell_periodic_twenty_nine_at_col_le_neg_add_three T (by omega) (by omega)
  · exact not_cell_periodic_thirty_at_col_le_neg_add_two T (by omega) (by omega)
  · exact not_cell_periodic_thirty_one_at_col_le_neg_zero T (by omega) (by omega)
  · exact not_cell_periodic_thirty_two_at_col_le_neg_zero T (by omega) (by omega)
  · exact not_cell_periodic_thirty_three_at_col_le_neg_sub_two T (by omega) (by omega)
  · exact not_cell_periodic_thirty_four_at_col_le_neg_sub_one T (by omega) (by omega)
  · exact not_cell_periodic_ge_thirty_five_at_col_le_neg_add_add_thirty_one T h35 (by omega) (by omega)


/-! ### 16. Arrival Entries `col_at_37` and `col_at_42 .. col_at_45` and All-Period 39-Column Inward Non-Periodicity -/
private theorem d8_s_42 (s : Nat) (hs : 1 ≤ s) : D 8 (s + 42) = !D 8 (s + 8) := by
  rw [show s + 42 = (s + 41) + 1 by omega, D_eight_succ_eq_D_ten (s + 41) (by omega), d10_s_41 s hs]
private theorem d10_s_42 (s : Nat) (hs : 1 ≤ s) : D 10 (s + 42) = !D 10 (s + 8) := by
  rw [show s + 42 = (s + 41) + 1 by omega, D_ten_succ_eq_not_D_eight (s + 41) (by omega), d8_s_41 s hs]
private theorem d29_s_42 (s : Nat) (hs : 2 ≤ s) : D 29 (s + 42) = xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (D 29 (s + 29)))))))))))))) := by
  rw [show s + 42 = (s + 41) + 1 by omega, D_twenty_nine_step_eq_xor_D_twenty_seven (s + 41) (by omega), D_twenty_seven_eq_nand_D_eight_D_ten (s + 41) (by omega), d8_s_41 s (by omega), d10_s_41 s (by omega), d29_s_41 s hs]
private theorem d8_s_43 (s : Nat) (hs : 1 ≤ s) : D 8 (s + 43) = !D 10 (s + 8) := by
  rw [show s + 43 = (s + 42) + 1 by omega, D_eight_succ_eq_D_ten (s + 42) (by omega), d10_s_42 s hs]
private theorem d10_s_43 (s : Nat) (hs : 1 ≤ s) : D 10 (s + 43) = D 8 (s + 8) := by
  rw [show s + 43 = (s + 42) + 1 by omega, D_ten_succ_eq_not_D_eight (s + 42) (by omega), d8_s_42 s hs, Bool.not_not]
private theorem d29_s_43 (s : Nat) (hs : 2 ≤ s) : D 29 (s + 43) = xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (D 29 (s + 29))))))))))))))) := by
  rw [show s + 43 = (s + 42) + 1 by omega, D_twenty_nine_step_eq_xor_D_twenty_seven (s + 42) (by omega), D_twenty_seven_eq_nand_D_eight_D_ten (s + 42) (by omega), d8_s_42 s (by omega), d10_s_42 s (by omega), d29_s_42 s hs]
private theorem d8_s_44 (s : Nat) (hs : 1 ≤ s) : D 8 (s + 44) = D 8 (s + 8) := by
  rw [show s + 44 = (s + 43) + 1 by omega, D_eight_succ_eq_D_ten (s + 43) (by omega), d10_s_43 s hs]
private theorem d10_s_44 (s : Nat) (hs : 1 ≤ s) : D 10 (s + 44) = D 10 (s + 8) := by
  rw [show s + 44 = (s + 43) + 1 by omega, D_ten_succ_eq_not_D_eight (s + 43) (by omega), d8_s_43 s hs, Bool.not_not]
private theorem d29_s_44 (s : Nat) (hs : 2 ≤ s) : D 29 (s + 44) = xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (D 29 (s + 29)))))))))))))))) := by
  rw [show s + 44 = (s + 43) + 1 by omega, D_twenty_nine_step_eq_xor_D_twenty_seven (s + 43) (by omega), D_twenty_seven_eq_nand_D_eight_D_ten (s + 43) (by omega), d8_s_43 s (by omega), d10_s_43 s (by omega), d29_s_43 s hs]
private theorem d8_s_45 (s : Nat) (hs : 1 ≤ s) : D 8 (s + 45) = D 10 (s + 8) := by
  rw [show s + 45 = (s + 44) + 1 by omega, D_eight_succ_eq_D_ten (s + 44) (by omega), d10_s_44 s hs]
private theorem d10_s_45 (s : Nat) (hs : 1 ≤ s) : D 10 (s + 45) = !D 8 (s + 8) := by
  rw [show s + 45 = (s + 44) + 1 by omega, D_ten_succ_eq_not_D_eight (s + 44) (by omega), d8_s_44 s hs]
private theorem d29_s_45 (s : Nat) (hs : 2 ≤ s) : D 29 (s + 45) = xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (D 29 (s + 29))))))))))))))))) := by
  rw [show s + 45 = (s + 44) + 1 by omega, D_twenty_nine_step_eq_xor_D_twenty_seven (s + 44) (by omega), D_twenty_seven_eq_nand_D_eight_D_ten (s + 44) (by omega), d8_s_44 s (by omega), d10_s_44 s (by omega), d29_s_44 s hs]

private theorem col_at_37 (s : Nat) (hs : 9 ≤ s) :
    cell (s + 37) (-(s : Int)) = ( xor (D 10 (s + 8)) (!D 8 (s + 8)) || !(xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (D 29 (s + 29)))))))))) ) := by
  have hd : cell (s + 37) (-(s : Int)) = D 37 (s + 37) := by unfold D; exact cell_congr (by omega)
  rw [hd, D_thirty_seven_eq_gate (s + 37) (by omega), d8_s_37 s (by omega), d10_s_37 s (by omega), d29_s_37 s (by omega)]

private theorem col_at_42 (s : Nat) (hs : 15 ≤ s) :
    cell (s + 42) (-(s : Int)) = ( !(xor (!D 8 (s + 8)) (!D 10 (s + 8))) || !(xor (!D 8 (s + 8)) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (D 29 (s + 29)))))))))))))))) ) := by
  have hd : cell (s + 42) (-(s : Int)) = D 42 (s + 42) := by unfold D; exact cell_congr (by omega)
  rw [hd, D_forty_two_eq_gate (s + 42) (by omega), d8_s_42 s (by omega), d10_s_42 s (by omega), d29_s_42 s (by omega)]

private theorem col_at_43 (s : Nat) (hs : 14 ≤ s) :
    cell (s + 43) (-(s : Int)) = ( ((!D 10 (s + 8)) && (D 8 (s + 8))) || (!(!D 10 (s + 8)) && !(D 8 (s + 8)) && (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (D 29 (s + 29))))))))))))))))) ) := by
  have hd : cell (s + 43) (-(s : Int)) = D 43 (s + 43) := by unfold D; exact cell_congr (by omega)
  rw [hd, D_forty_three_eq_gate (s + 43) (by omega), d8_s_43 s (by omega), d10_s_43 s (by omega), d29_s_43 s (by omega)]

private theorem col_at_44 (s : Nat) (hs : 17 ≤ s) :
    cell (s + 44) (-(s : Int)) = ( !(xor (D 8 (s + 8)) (D 10 (s + 8))) && !(xor (D 10 (s + 8)) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (xor (!(D 8 (s + 8) && D 10 (s + 8))) (xor (!(!D 10 (s + 8) && D 8 (s + 8))) (xor (!(!D 8 (s + 8) && !D 10 (s + 8))) (xor (!(D 10 (s + 8) && !D 8 (s + 8))) (D 29 (s + 29)))))))))))))))))) ) := by
  have hd : cell (s + 44) (-(s : Int)) = D 44 (s + 44) := by unfold D; exact cell_congr (by omega)
  rw [hd, D_forty_four_eq_gate (s + 44) (by omega), d8_s_44 s (by omega), d10_s_44 s (by omega), d29_s_44 s (by omega)]

private theorem col_at_45 (s : Nat) (hs : 16 ≤ s) :
    cell (s + 45) (-(s : Int)) = (!D 8 (s + 8)) := by
  have hd : cell (s + 45) (-(s : Int)) = D 45 (s + 45) := by unfold D; exact cell_congr (by omega)
  rw [hd, D_forty_five_eq_D_ten (s + 45) (by omega), d10_s_45 s (by omega)]


theorem not_cell_periodic_one_to_three_at_col_le_neg_add_add_forty_one (T : Nat) {P : Nat}
    (hP : P = 1 ∨ P = 2 ∨ P = 3) {c : Int} (hc0 : c ≤ -17) (hc : c ≤ -((T + P : Nat) : Int) + 41) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + P) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  rcases hP with rfl | rfl | rfl
  ·
    have h0 := hper (s + 42) (by omega)
    rw [hc_eq, show (s + 42) + 1 = s + 43 by omega, col_at_42 s (by omega), col_at_43 s (by omega)] at h0
    have h1 := hper (s + 43) (by omega)
    rw [hc_eq, show (s + 43) + 1 = s + 44 by omega, col_at_43 s (by omega), col_at_44 s (by omega)] at h1
    revert h0 h1
    cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide
  ·
    have h0 := hper (s + 39) (by omega)
    rw [hc_eq, show (s + 39) + 2 = s + 41 by omega, col_at_39 s (by omega), col_at_41 s (by omega)] at h0
    have h1 := hper (s + 40) (by omega)
    rw [hc_eq, show (s + 40) + 2 = s + 42 by omega, col_at_40 s (by omega), col_at_42 s (by omega)] at h1
    revert h0 h1
    cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide
  ·
    have h0 := hper (s + 41) (by omega)
    rw [hc_eq, show (s + 41) + 3 = s + 44 by omega, col_at_41 s (by omega), col_at_44 s (by omega)] at h0
    have h1 := hper (s + 42) (by omega)
    rw [hc_eq, show (s + 42) + 3 = s + 45 by omega, col_at_42 s (by omega), col_at_45 s (by omega)] at h1
    revert h0 h1
    cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_four_to_six_at_col_le_neg_add_add_forty_one (T : Nat) {P : Nat}
    (hP : P = 4 ∨ P = 5 ∨ P = 6) {c : Int} (hc0 : c ≤ -17) (hc : c ≤ -((T + P : Nat) : Int) + 41) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + P) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  rcases hP with rfl | rfl | rfl
  ·
    have h0 := hper (s + 39) (by omega)
    rw [hc_eq, show (s + 39) + 4 = s + 43 by omega, col_at_39 s (by omega), col_at_43 s (by omega)] at h0
    have h1 := hper (s + 40) (by omega)
    rw [hc_eq, show (s + 40) + 4 = s + 44 by omega, col_at_40 s (by omega), col_at_44 s (by omega)] at h1
    have h2 := hper (s + 41) (by omega)
    rw [hc_eq, show (s + 41) + 4 = s + 45 by omega, col_at_41 s (by omega), col_at_45 s (by omega)] at h2
    revert h0 h1 h2
    cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide
  ·
    have h0 := hper (s + 36) (by omega)
    rw [hc_eq, show (s + 36) + 5 = s + 41 by omega, col_at_36 s (by omega), col_at_41 s (by omega)] at h0
    have h1 := hper (s + 40) (by omega)
    rw [hc_eq, show (s + 40) + 5 = s + 45 by omega, col_at_40 s (by omega), col_at_45 s (by omega)] at h1
    have h2 := hper (s + 38) (by omega)
    rw [hc_eq, show (s + 38) + 5 = s + 43 by omega, col_at_38 s (by omega), col_at_43 s (by omega)] at h2
    revert h0 h1 h2
    cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide
  ·
    have h0 := hper (s + 37) (by omega)
    rw [hc_eq, show (s + 37) + 6 = s + 43 by omega, col_at_37 s (by omega), col_at_43 s (by omega)] at h0
    have h1 := hper (s + 38) (by omega)
    rw [hc_eq, show (s + 38) + 6 = s + 44 by omega, col_at_38 s (by omega), col_at_44 s (by omega)] at h1
    revert h0 h1
    cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_seven_to_nine_at_col_le_neg_add_add_forty_one (T : Nat) {P : Nat}
    (hP : P = 7 ∨ P = 8 ∨ P = 9) {c : Int} (hc0 : c ≤ -17) (hc : c ≤ -((T + P : Nat) : Int) + 41) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + P) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  rcases hP with rfl | rfl | rfl
  ·
    have h0 := hper (s + 36) (by omega)
    rw [hc_eq, show (s + 36) + 7 = s + 43 by omega, col_at_36 s (by omega), col_at_43 s (by omega)] at h0
    have h1 := hper (s + 37) (by omega)
    rw [hc_eq, show (s + 37) + 7 = s + 44 by omega, col_at_37 s (by omega), col_at_44 s (by omega)] at h1
    have h2 := hper (s + 35) (by omega)
    rw [hc_eq, show (s + 35) + 7 = s + 42 by omega, col_at_35 s (by omega), col_at_42 s (by omega)] at h2
    revert h0 h1 h2
    cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide
  ·
    have h0 := hper (s + 34) (by omega)
    rw [hc_eq, show (s + 34) + 8 = s + 42 by omega, col_at_34 s (by omega), col_at_42 s (by omega)] at h0
    have h1 := hper (s + 35) (by omega)
    rw [hc_eq, show (s + 35) + 8 = s + 43 by omega, col_at_35 s (by omega), col_at_43 s (by omega)] at h1
    have h2 := hper (s + 36) (by omega)
    rw [hc_eq, show (s + 36) + 8 = s + 44 by omega, col_at_36 s (by omega), col_at_44 s (by omega)] at h2
    revert h0 h1 h2
    cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide
  ·
    have h0 := hper (s + 32) (by omega)
    rw [hc_eq, show (s + 32) + 9 = s + 41 by omega, col_at_32 s (by omega), col_at_41 s (by omega)] at h0
    have h1 := hper (s + 34) (by omega)
    rw [hc_eq, show (s + 34) + 9 = s + 43 by omega, col_at_34 s (by omega), col_at_43 s (by omega)] at h1
    have h2 := hper (s + 33) (by omega)
    rw [hc_eq, show (s + 33) + 9 = s + 42 by omega, col_at_33 s (by omega), col_at_42 s (by omega)] at h2
    revert h0 h1 h2
    cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_ten_to_twelve_at_col_le_neg_add_add_forty_one (T : Nat) {P : Nat}
    (hP : P = 10 ∨ P = 11 ∨ P = 12) {c : Int} (hc0 : c ≤ -17) (hc : c ≤ -((T + P : Nat) : Int) + 41) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + P) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  rcases hP with rfl | rfl | rfl
  ·
    have h0 := hper (s + 33) (by omega)
    rw [hc_eq, show (s + 33) + 10 = s + 43 by omega, col_at_33 s (by omega), col_at_43 s (by omega)] at h0
    have h1 := hper (s + 31) (by omega)
    rw [hc_eq, show (s + 31) + 10 = s + 41 by omega, col_at_31 s (by omega), col_at_41 s (by omega)] at h1
    have h2 := hper (s + 32) (by omega)
    rw [hc_eq, show (s + 32) + 10 = s + 42 by omega, col_at_32 s (by omega), col_at_42 s (by omega)] at h2
    revert h0 h1 h2
    cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide
  ·
    have h0 := hper (s + 31) (by omega)
    rw [hc_eq, show (s + 31) + 11 = s + 42 by omega, col_at_31 s (by omega), col_at_42 s (by omega)] at h0
    have h1 := hper (s + 32) (by omega)
    rw [hc_eq, show (s + 32) + 11 = s + 43 by omega, col_at_32 s (by omega), col_at_43 s (by omega)] at h1
    have h2 := hper (s + 33) (by omega)
    rw [hc_eq, show (s + 33) + 11 = s + 44 by omega, col_at_33 s (by omega), col_at_44 s (by omega)] at h2
    have h3 := hper (s + 30) (by omega)
    rw [hc_eq, show (s + 30) + 11 = s + 41 by omega, col_at_30 s (by omega), col_at_41 s (by omega)] at h3
    revert h0 h1 h2 h3
    cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide
  ·
    have h0 := hper (s + 30) (by omega)
    rw [hc_eq, show (s + 30) + 12 = s + 42 by omega, col_at_30 s (by omega), col_at_42 s (by omega)] at h0
    have h1 := hper (s + 32) (by omega)
    rw [hc_eq, show (s + 32) + 12 = s + 44 by omega, col_at_32 s (by omega), col_at_44 s (by omega)] at h1
    have h2 := hper (s + 31) (by omega)
    rw [hc_eq, show (s + 31) + 12 = s + 43 by omega, col_at_31 s (by omega), col_at_43 s (by omega)] at h2
    revert h0 h1 h2
    cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_thirteen_to_fifteen_at_col_le_neg_add_add_forty (T : Nat) {P : Nat}
    (hP : P = 13 ∨ P = 14 ∨ P = 15) {c : Int} (hc0 : c ≤ -17) (hc : c ≤ -((T + P : Nat) : Int) + 40) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + P) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  rcases hP with rfl | rfl | rfl
  ·
    have h0 := hper (s + 31) (by omega)
    rw [hc_eq, show (s + 31) + 13 = s + 44 by omega, col_at_31 s (by omega), col_at_44 s (by omega)] at h0
    have h1 := hper (s + 30) (by omega)
    rw [hc_eq, show (s + 30) + 13 = s + 43 by omega, col_at_30 s (by omega), col_at_43 s (by omega)] at h1
    have h2 := hper (s + 32) (by omega)
    rw [hc_eq, show (s + 32) + 13 = s + 45 by omega, col_at_32 s (by omega), col_at_45 s (by omega)] at h2
    revert h0 h1 h2
    cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide
  ·
    have h0 := hper (s + 30) (by omega)
    rw [hc_eq, show (s + 30) + 14 = s + 44 by omega, col_at_30 s (by omega), col_at_44 s (by omega)] at h0
    have h1 := hper (s + 29) (by omega)
    rw [hc_eq, show (s + 29) + 14 = s + 43 by omega, col_at_29 s (by omega), col_at_43 s (by omega)] at h1
    revert h0 h1
    cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide
  ·
    have h0 := hper (s + 28) (by omega)
    rw [hc_eq, show (s + 28) + 15 = s + 43 by omega, col_at_28 s (by omega), col_at_43 s (by omega)] at h0
    have h1 := hper (s + 26) (by omega)
    rw [hc_eq, show (s + 26) + 15 = s + 41 by omega, col_at_26 s (by omega), col_at_41 s (by omega)] at h1
    have h2 := hper (s + 25) (by omega)
    rw [hc_eq, show (s + 25) + 15 = s + 40 by omega, col_at_25 s (by omega), col_at_40 s (by omega)] at h2
    have h3 := hper (s + 27) (by omega)
    rw [hc_eq, show (s + 27) + 15 = s + 42 by omega, col_at_27 s (by omega), col_at_42 s (by omega)] at h3
    have h4 := hper (s + 30) (by omega)
    rw [hc_eq, show (s + 30) + 15 = s + 45 by omega, col_at_30 s (by omega), col_at_45 s (by omega)] at h4
    revert h0 h1 h2 h3 h4
    cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_sixteen_to_eighteen_at_col_le_neg_add_add_forty_one (T : Nat) {P : Nat}
    (hP : P = 16 ∨ P = 17 ∨ P = 18) {c : Int} (hc0 : c ≤ -17) (hc : c ≤ -((T + P : Nat) : Int) + 41) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + P) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  rcases hP with rfl | rfl | rfl
  ·
    have h0 := hper (s + 26) (by omega)
    rw [hc_eq, show (s + 26) + 16 = s + 42 by omega, col_at_26 s (by omega), col_at_42 s (by omega)] at h0
    have h1 := hper (s + 27) (by omega)
    rw [hc_eq, show (s + 27) + 16 = s + 43 by omega, col_at_27 s (by omega), col_at_43 s (by omega)] at h1
    revert h0 h1
    cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide
  ·
    have h0 := hper (s + 24) (by omega)
    rw [hc_eq, show (s + 24) + 17 = s + 41 by omega, col_at_24 s (by omega), col_at_41 s (by omega)] at h0
    have h1 := hper (s + 25) (by omega)
    rw [hc_eq, show (s + 25) + 17 = s + 42 by omega, col_at_25 s (by omega), col_at_42 s (by omega)] at h1
    have h2 := hper (s + 28) (by omega)
    rw [hc_eq, show (s + 28) + 17 = s + 45 by omega, col_at_28 s (by omega), col_at_45 s (by omega)] at h2
    have h3 := hper (s + 26) (by omega)
    rw [hc_eq, show (s + 26) + 17 = s + 43 by omega, col_at_26 s (by omega), col_at_43 s (by omega)] at h3
    revert h0 h1 h2 h3
    cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide
  ·
    have h0 := hper (s + 25) (by omega)
    rw [hc_eq, show (s + 25) + 18 = s + 43 by omega, col_at_25 s (by omega), col_at_43 s (by omega)] at h0
    have h1 := hper (s + 26) (by omega)
    rw [hc_eq, show (s + 26) + 18 = s + 44 by omega, col_at_26 s (by omega), col_at_44 s (by omega)] at h1
    have h2 := hper (s + 27) (by omega)
    rw [hc_eq, show (s + 27) + 18 = s + 45 by omega, col_at_27 s (by omega), col_at_45 s (by omega)] at h2
    revert h0 h1 h2
    cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_nineteen_to_twenty_one_at_col_le_neg_add_add_forty (T : Nat) {P : Nat}
    (hP : P = 19 ∨ P = 20 ∨ P = 21) {c : Int} (hc0 : c ≤ -17) (hc : c ≤ -((T + P : Nat) : Int) + 40) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + P) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  rcases hP with rfl | rfl | rfl
  ·
    have h0 := hper (s + 26) (by omega)
    rw [hc_eq, show (s + 26) + 19 = s + 45 by omega, col_at_26 s (by omega), col_at_45 s (by omega)] at h0
    have h1 := hper (s + 25) (by omega)
    rw [hc_eq, show (s + 25) + 19 = s + 44 by omega, col_at_25 s (by omega), col_at_44 s (by omega)] at h1
    revert h0 h1
    cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide
  ·
    have h0 := hper (s + 20) (by omega)
    rw [hc_eq, show (s + 20) + 20 = s + 40 by omega, col_at_20 s (by omega), col_at_40 s (by omega)] at h0
    have h1 := hper (s + 24) (by omega)
    rw [hc_eq, show (s + 24) + 20 = s + 44 by omega, col_at_24 s (by omega), col_at_44 s (by omega)] at h1
    have h2 := hper (s + 22) (by omega)
    rw [hc_eq, show (s + 22) + 20 = s + 42 by omega, col_at_22 s (by omega), col_at_42 s (by omega)] at h2
    revert h0 h1 h2
    cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide
  ·
    have h0 := hper (s + 21) (by omega)
    rw [hc_eq, show (s + 21) + 21 = s + 42 by omega, col_at_21 s (by omega), col_at_42 s (by omega)] at h0
    have h1 := hper (s + 19) (by omega)
    rw [hc_eq, show (s + 19) + 21 = s + 40 by omega, col_at_19 s (by omega), col_at_40 s (by omega)] at h1
    have h2 := hper (s + 23) (by omega)
    rw [hc_eq, show (s + 23) + 21 = s + 44 by omega, col_at_23 s (by omega), col_at_44 s (by omega)] at h2
    revert h0 h1 h2
    cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_twenty_two_to_twenty_four_at_col_le_neg_add_add_forty (T : Nat) {P : Nat}
    (hP : P = 22 ∨ P = 23 ∨ P = 24) {c : Int} (hc0 : c ≤ -17) (hc : c ≤ -((T + P : Nat) : Int) + 40) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + P) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  rcases hP with rfl | rfl | rfl
  ·
    have h0 := hper (s + 19) (by omega)
    rw [hc_eq, show (s + 19) + 22 = s + 41 by omega, col_at_19 s (by omega), col_at_41 s (by omega)] at h0
    have h1 := hper (s + 18) (by omega)
    rw [hc_eq, show (s + 18) + 22 = s + 40 by omega, col_at_18 s (by omega), col_at_40 s (by omega)] at h1
    have h2 := hper (s + 21) (by omega)
    rw [hc_eq, show (s + 21) + 22 = s + 43 by omega, col_at_21 s (by omega), col_at_43 s (by omega)] at h2
    have h3 := hper (s + 20) (by omega)
    rw [hc_eq, show (s + 20) + 22 = s + 42 by omega, col_at_20 s (by omega), col_at_42 s (by omega)] at h3
    revert h0 h1 h2 h3
    cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide
  ·
    have h0 := hper (s + 21) (by omega)
    rw [hc_eq, show (s + 21) + 23 = s + 44 by omega, col_at_21 s (by omega), col_at_44 s (by omega)] at h0
    have h1 := hper (s + 19) (by omega)
    rw [hc_eq, show (s + 19) + 23 = s + 42 by omega, col_at_19 s (by omega), col_at_42 s (by omega)] at h1
    have h2 := hper (s + 20) (by omega)
    rw [hc_eq, show (s + 20) + 23 = s + 43 by omega, col_at_20 s (by omega), col_at_43 s (by omega)] at h2
    revert h0 h1 h2
    cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide
  ·
    have h0 := hper (s + 19) (by omega)
    rw [hc_eq, show (s + 19) + 24 = s + 43 by omega, col_at_19 s (by omega), col_at_43 s (by omega)] at h0
    have h1 := hper (s + 18) (by omega)
    rw [hc_eq, show (s + 18) + 24 = s + 42 by omega, col_at_18 s (by omega), col_at_42 s (by omega)] at h1
    revert h0 h1
    cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_twenty_five_to_twenty_seven_at_col_le_neg_add_add_forty (T : Nat) {P : Nat}
    (hP : P = 25 ∨ P = 26 ∨ P = 27) {c : Int} (hc0 : c ≤ -17) (hc : c ≤ -((T + P : Nat) : Int) + 40) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + P) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  rcases hP with rfl | rfl | rfl
  ·
    have h0 := hper (s + 20) (by omega)
    rw [hc_eq, show (s + 20) + 25 = s + 45 by omega, col_at_20 s (by omega), col_at_45 s (by omega)] at h0
    revert h0
    cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide
  ·
    have h0 := hper (s + 17) (by omega)
    rw [hc_eq, show (s + 17) + 26 = s + 43 by omega, col_at_17 s (by omega), col_at_43 s (by omega)] at h0
    have h1 := hper (s + 19) (by omega)
    rw [hc_eq, show (s + 19) + 26 = s + 45 by omega, col_at_19 s (by omega), col_at_45 s (by omega)] at h1
    have h2 := hper (s + 18) (by omega)
    rw [hc_eq, show (s + 18) + 26 = s + 44 by omega, col_at_18 s (by omega), col_at_44 s (by omega)] at h2
    revert h0 h1 h2
    cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide
  ·
    have h0 := hper (s + 13) (by omega)
    rw [hc_eq, show (s + 13) + 27 = s + 40 by omega, col_at_13 s (by omega), col_at_40 s (by omega)] at h0
    have h1 := hper (s + 14) (by omega)
    rw [hc_eq, show (s + 14) + 27 = s + 41 by omega, col_at_14 s (by omega), col_at_41 s (by omega)] at h1
    revert h0 h1
    cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_twenty_eight_to_thirty_at_col_le_neg_add_add_forty (T : Nat) {P : Nat}
    (hP : P = 28 ∨ P = 29 ∨ P = 30) {c : Int} (hc0 : c ≤ -17) (hc : c ≤ -((T + P : Nat) : Int) + 40) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + P) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  rcases hP with rfl | rfl | rfl
  ·
    have h0 := hper (s + 12) (by omega)
    rw [hc_eq, show (s + 12) + 28 = s + 40 by omega, col_at_12 s (by omega), col_at_40 s (by omega)] at h0
    have h1 := hper (s + 13) (by omega)
    rw [hc_eq, show (s + 13) + 28 = s + 41 by omega, col_at_13 s (by omega), col_at_41 s (by omega)] at h1
    have h2 := hper (s + 14) (by omega)
    rw [hc_eq, show (s + 14) + 28 = s + 42 by omega, col_at_14 s (by omega), col_at_42 s (by omega)] at h2
    revert h0 h1 h2
    cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide
  ·
    have h0 := hper (s + 13) (by omega)
    rw [hc_eq, show (s + 13) + 29 = s + 42 by omega, col_at_13 s (by omega), col_at_42 s (by omega)] at h0
    have h1 := hper (s + 16) (by omega)
    rw [hc_eq, show (s + 16) + 29 = s + 45 by omega, col_at_16 s (by omega), col_at_45 s (by omega)] at h1
    have h2 := hper (s + 14) (by omega)
    rw [hc_eq, show (s + 14) + 29 = s + 43 by omega, col_at_14 s (by omega), col_at_43 s (by omega)] at h2
    have h3 := hper (s + 15) (by omega)
    rw [hc_eq, show (s + 15) + 29 = s + 44 by omega, col_at_15 s (by omega), col_at_44 s (by omega)] at h3
    revert h0 h1 h2 h3
    cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide
  ·
    have h0 := hper (s + 15) (by omega)
    rw [hc_eq, show (s + 15) + 30 = s + 45 by omega, col_at_15 s (by omega), col_at_45 s (by omega)] at h0
    revert h0
    cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_thirty_one_to_thirty_three_at_col_le_neg_add_add_forty_two (T : Nat) {P : Nat}
    (hP : P = 31 ∨ P = 32 ∨ P = 33) {c : Int} (hc0 : c ≤ -17) (hc : c ≤ -((T + P : Nat) : Int) + 39) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + P) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  rcases hP with rfl | rfl | rfl
  ·
    have h0 := hper (s + 13) (by omega)
    rw [hc_eq, show (s + 13) + 31 = s + 44 by omega, col_at_13 s (by omega), col_at_44 s (by omega)] at h0
    have h1 := hper (s + 11) (by omega)
    rw [hc_eq, show (s + 11) + 31 = s + 42 by omega, col_at_11 s (by omega), col_at_42 s (by omega)] at h1
    have h2 := hper (s + 12) (by omega)
    rw [hc_eq, show (s + 12) + 31 = s + 43 by omega, col_at_12 s (by omega), col_at_43 s (by omega)] at h2
    revert h0 h1 h2
    cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide
  ·
    have h0 := hper (s + 12) (by omega)
    rw [hc_eq, show (s + 12) + 32 = s + 44 by omega, col_at_12 s (by omega), col_at_44 s (by omega)] at h0
    have h1 := hper (s + 13) (by omega)
    rw [hc_eq, show (s + 13) + 32 = s + 45 by omega, col_at_13 s (by omega), col_at_45 s (by omega)] at h1
    revert h0 h1
    cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide
  ·
    have h0 := hper (s + 6) (by omega)
    rw [hc_eq, show (s + 6) + 33 = s + 39 by omega, col_at_6 s (by omega), col_at_39 s (by omega)] at h0
    have h1 := hper (s + 7) (by omega)
    rw [hc_eq, show (s + 7) + 33 = s + 40 by omega, col_at_7 s (by omega), col_at_40 s (by omega)] at h1
    have h2 := hper (s + 10) (by omega)
    rw [hc_eq, show (s + 10) + 33 = s + 43 by omega, col_at_10 s (by omega), col_at_43 s (by omega)] at h2
    have h3 := hper (s + 8) (by omega)
    rw [hc_eq, show (s + 8) + 33 = s + 41 by omega, col_at_8 s (by omega), col_at_41 s (by omega)] at h3
    revert h0 h1 h2 h3
    cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_thirty_four_to_thirty_six_at_col_le_neg_add_add_forty_one (T : Nat) {P : Nat}
    (hP : P = 34 ∨ P = 35 ∨ P = 36) {c : Int} (hc0 : c ≤ -17) (hc : c ≤ -((T + P : Nat) : Int) + 41) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + P) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  rcases hP with rfl | rfl | rfl
  ·
    have h0 := hper (s + 7) (by omega)
    rw [hc_eq, show (s + 7) + 34 = s + 41 by omega, col_at_7 s (by omega), col_at_41 s (by omega)] at h0
    have h1 := hper (s + 8) (by omega)
    rw [hc_eq, show (s + 8) + 34 = s + 42 by omega, col_at_8 s (by omega), col_at_42 s (by omega)] at h1
    revert h0 h1
    cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide
  ·
    have h0 := hper (s + 9) (by omega)
    rw [hc_eq, show (s + 9) + 35 = s + 44 by omega, col_at_9 s (by omega), col_at_44 s (by omega)] at h0
    have h1 := hper (s + 7) (by omega)
    rw [hc_eq, show (s + 7) + 35 = s + 42 by omega, col_at_7 s (by omega), col_at_42 s (by omega)] at h1
    have h2 := hper (s + 8) (by omega)
    rw [hc_eq, show (s + 8) + 35 = s + 43 by omega, col_at_8 s (by omega), col_at_43 s (by omega)] at h2
    revert h0 h1 h2
    cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide
  ·
    have h0 := hper (s + 5) (by omega)
    rw [hc_eq, show (s + 5) + 36 = s + 41 by omega, col_at_5 s (by omega), col_at_41 s (by omega)] at h0
    have h1 := hper (s + 6) (by omega)
    rw [hc_eq, show (s + 6) + 36 = s + 42 by omega, col_at_6 s (by omega), col_at_42 s (by omega)] at h1
    revert h0 h1
    cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_thirty_seven_to_thirty_nine_at_col_le_neg_add_add_forty_one (T : Nat) {P : Nat}
    (hP : P = 37 ∨ P = 38 ∨ P = 39) {c : Int} (hc0 : c ≤ -17) (hc : c ≤ -((T + P : Nat) : Int) + 41) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + P) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  rcases hP with rfl | rfl | rfl
  ·
    have h0 := hper (s + 8) (by omega)
    rw [hc_eq, show (s + 8) + 37 = s + 45 by omega, col_at_8 s (by omega), col_at_45 s (by omega)] at h0
    revert h0
    cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide
  ·
    have h0 := hper (s + 5) (by omega)
    rw [hc_eq, show (s + 5) + 38 = s + 43 by omega, col_at_5 s (by omega), col_at_43 s (by omega)] at h0
    have h1 := hper (s + 6) (by omega)
    rw [hc_eq, show (s + 6) + 38 = s + 44 by omega, col_at_6 s (by omega), col_at_44 s (by omega)] at h1
    revert h0 h1
    cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide
  ·
    have h0 := hper (s + 2) (by omega)
    rw [hc_eq, show (s + 2) + 39 = s + 41 by omega, col_at_2 s (by omega), col_at_41 s (by omega)] at h0
    have h1 := hper (s + 4) (by omega)
    rw [hc_eq, show (s + 4) + 39 = s + 43 by omega, col_at_4 s (by omega), col_at_43 s (by omega)] at h1
    revert h0 h1
    cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

theorem not_cell_periodic_forty_to_forty_two_at_col_le_neg_add_add_thirty_nine (T : Nat) {P : Nat}
    (hP : P = 40 ∨ P = 41 ∨ P = 42) {c : Int} (hc0 : c ≤ -17) (hc : c ≤ -((T + P : Nat) : Int) + 39) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + P) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  rcases hP with rfl | rfl | rfl
  ·
    have h0 := hper (s + 3) (by omega)
    rw [hc_eq, show (s + 3) + 40 = s + 43 by omega, col_at_3 s (by omega), col_at_43 s (by omega)] at h0
    have h1 := hper (s + 4) (by omega)
    rw [hc_eq, show (s + 4) + 40 = s + 44 by omega, col_at_4 s (by omega), col_at_44 s (by omega)] at h1
    revert h0 h1
    cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide
  ·
    have h0 := hper (s + 1) (by omega)
    rw [hc_eq, show (s + 1) + 41 = s + 42 by omega, col_at_1 s (by omega), col_at_42 s (by omega)] at h0
    have h1 := hper (s - 1) (by omega)
    rw [hc_eq, show (s - 1) + 41 = s + 40 by omega, cell_eq_false_of_lt (s - 1) (-(s : Int)) (by omega), col_at_40 s (by omega)] at h1
    have h2 := hper (s + 2) (by omega)
    rw [hc_eq, show (s + 2) + 41 = s + 43 by omega, col_at_2 s (by omega), col_at_43 s (by omega)] at h2
    have h3 := hper (s) (by omega)
    rw [hc_eq, show (s) + 41 = s + 41 by omega, show cell s (-(s : Int)) = cell (s + 0) (-(s : Int)) by rfl, col_at_0 s (by omega), col_at_41 s (by omega)] at h3
    have h4 := hper (s - 2) (by omega)
    rw [hc_eq, show (s - 2) + 41 = s + 39 by omega, cell_eq_false_of_lt (s - 2) (-(s : Int)) (by omega), col_at_39 s (by omega)] at h4
    revert h0 h1 h2 h3 h4
    cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide
  ·
    have h0 := hper (s - 1) (by omega)
    rw [hc_eq, show (s - 1) + 42 = s + 41 by omega, cell_eq_false_of_lt (s - 1) (-(s : Int)) (by omega), col_at_41 s (by omega)] at h0
    have h1 := hper (s + 1) (by omega)
    rw [hc_eq, show (s + 1) + 42 = s + 43 by omega, col_at_1 s (by omega), col_at_43 s (by omega)] at h1
    revert h0 h1
    cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

/-- **Forty-One-Column Inward Non-Periodicity for All Large Periods `P ≥ 43`
(`not_cell_periodic_ge_forty_three_at_col_le_neg_add_add_forty_one`):**
for every `T : Nat`, every period `P ≥ 43`, and every column `c ≤ -15` with
`c ≤ -((T + P : Nat) : Int) + 41`, `¬ (∀ t : Nat, T ≤ t → cell (t + P) c = cell t c)`. -/
theorem not_cell_periodic_ge_forty_three_at_col_le_neg_add_add_forty_one (T : Nat) {P : Nat}
    (hP : 43 ≤ P) {c : Int} (hc0 : c ≤ -15) (hc : c ≤ -((T + P : Nat) : Int) + 41) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + P) c = cell t c) := by
  intro hper
  let s : Nat := (-c).toNat
  have hc_eq : c = -(s : Int) := by omega
  have h0 := hper (s + 41 - P) (by omega)
  rw [hc_eq, show (s + 41 - P) + P = s + 41 by omega,
      cell_eq_false_of_lt (s + 41 - P) (-(s : Int)) (by omega), col_at_41 s (by omega)] at h0
  have h1 := hper (s + 42 - P) (by omega)
  rw [hc_eq, show (s + 42 - P) + P = s + 42 by omega,
      cell_eq_false_of_lt (s + 42 - P) (-(s : Int)) (by omega), col_at_42 s (by omega)] at h1
  revert h0 h1
  cases D 8 (s + 8) <;> cases D 10 (s + 8) <;> cases D 29 (s + 29) <;> decide

/-- **All-Period Unconditional 39-Column Inward Non-Periodicity
(`not_cell_periodic_at_col_le_neg_add_add_thirty_nine`):**
for every `T : Nat`, every positive period `P > 0`, and every column `c ≤ -17` with
`c ≤ -((T + P : Nat) : Int) + 39`, `cell · c` is not `P`-periodic from `T` on. -/
theorem not_cell_periodic_at_col_le_neg_add_add_thirty_nine (T : Nat) {P : Nat}
    (hP : 0 < P) {c : Int} (hc0 : c ≤ -17) (hc : c ≤ -((T + P : Nat) : Int) + 39) :
    ¬ (∀ t : Nat, T ≤ t → cell (t + P) c = cell t c) := by
  rcases (by omega :
      (P = 1 ∨ P = 2 ∨ P = 3) ∨ (P = 4 ∨ P = 5 ∨ P = 6) ∨ (P = 7 ∨ P = 8 ∨ P = 9) ∨
      (P = 10 ∨ P = 11 ∨ P = 12) ∨ (P = 13 ∨ P = 14 ∨ P = 15) ∨ (P = 16 ∨ P = 17 ∨ P = 18) ∨
      (P = 19 ∨ P = 20 ∨ P = 21) ∨ (P = 22 ∨ P = 23 ∨ P = 24) ∨ (P = 25 ∨ P = 26 ∨ P = 27) ∨
      (P = 28 ∨ P = 29 ∨ P = 30) ∨ (P = 31 ∨ P = 32 ∨ P = 33) ∨ (P = 34 ∨ P = 35 ∨ P = 36) ∨
      (P = 37 ∨ P = 38 ∨ P = 39) ∨ (P = 40 ∨ P = 41 ∨ P = 42) ∨ 43 ≤ P) with
    h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h43
  · exact not_cell_periodic_one_to_three_at_col_le_neg_add_add_forty_one T h1 hc0 (by omega)
  · exact not_cell_periodic_four_to_six_at_col_le_neg_add_add_forty_one T h2 hc0 (by omega)
  · exact not_cell_periodic_seven_to_nine_at_col_le_neg_add_add_forty_one T h3 hc0 (by omega)
  · exact not_cell_periodic_ten_to_twelve_at_col_le_neg_add_add_forty_one T h4 hc0 (by omega)
  · exact not_cell_periodic_thirteen_to_fifteen_at_col_le_neg_add_add_forty T h5 hc0 (by omega)
  · exact not_cell_periodic_sixteen_to_eighteen_at_col_le_neg_add_add_forty_one T h6 hc0 (by omega)
  · exact not_cell_periodic_nineteen_to_twenty_one_at_col_le_neg_add_add_forty T h7 hc0 (by omega)
  · exact not_cell_periodic_twenty_two_to_twenty_four_at_col_le_neg_add_add_forty T h8 hc0 (by omega)
  · exact not_cell_periodic_twenty_five_to_twenty_seven_at_col_le_neg_add_add_forty T h9 hc0 (by omega)
  · exact not_cell_periodic_twenty_eight_to_thirty_at_col_le_neg_add_add_forty T h10 hc0 (by omega)
  · exact not_cell_periodic_thirty_one_to_thirty_three_at_col_le_neg_add_add_forty_two T h11 hc0 (by omega)
  · exact not_cell_periodic_thirty_four_to_thirty_six_at_col_le_neg_add_add_forty_one T h12 hc0 (by omega)
  · exact not_cell_periodic_thirty_seven_to_thirty_nine_at_col_le_neg_add_add_forty_one T h13 hc0 (by omega)
  · exact not_cell_periodic_forty_to_forty_two_at_col_le_neg_add_add_thirty_nine T h14 hc0 (by omega)
  · exact not_cell_periodic_ge_forty_three_at_col_le_neg_add_add_forty_one T h43 (by omega) (by omega)


end Inward18Closure

end Ruliology.CellularAutomata.Rule30TraceEdge
