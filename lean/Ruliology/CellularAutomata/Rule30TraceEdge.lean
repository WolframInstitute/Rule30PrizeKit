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

end Ruliology.CellularAutomata.Rule30TraceEdge
