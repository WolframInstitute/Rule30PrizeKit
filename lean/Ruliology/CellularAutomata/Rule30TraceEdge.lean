module

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

end Ruliology.CellularAutomata.Rule30TraceEdge
