module

public import Ruliology.CellularAutomata.Rule30TraceMerge

/-!
# Arbitrarily long ambiguity among finite initial configurations

For EVERY finite observation horizon, two finite rows with left edge -3 have
equal center observations up to that horizon but different initial cells at
-1. Truncating the explicit right-infinite merge example proves the result
by causality. This rules out a uniform finite horizon for recovering the
initial left half from only its left depth, even among finite initial rows.

It does not refute recovery from the entire infinite trace of a finite row.
The two edges agree, so it does not refute EdgeObservable either.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30TraceAmbiguity

open Rule30Realization Rule30PeriodTwoSideways Rule30TraceEdge
open Rule30TraceMerge

def cutoff (N : Nat) (x : Int → Bool) (p : Int) : Bool :=
  if p ≤ (N:Int) then x p else false

theorem cutoff_finite {x : Int → Bool} (hx : ∀ p, p < -3 → x p = false) (N : Nat) :
    FinConfig (cutoff N x) := by
  refine ⟨N+3,fun p hp => ?_⟩
  by_cases h : p ≤ (N:Int)
  · rw [cutoff,ite_eq_left h]
    exact hx p (by omega)
  · simp [cutoff,h]

theorem cutoff_edge {x : Int → Bool} (hx : HasLeftEdge x (-3)) (N : Nat) :
    HasLeftEdge (cutoff N x) (-3) := by
  constructor
  · simpa [cutoff] using hx.1
  · intro p hp
    simp [cutoff,show p ≤ (N:Int) by omega,hx.2 p hp]

theorem cutoff_trace (x : Int → Bool) (N t : Nat) (ht : t ≤ N) :
    evol (cutoff N x) t 0 = evol x t 0 := by
  have h := Rule30ZeroBoundaryBarriers.evol_local_le
    (x:=x) (x':=cutoff N x) (d:=0) (b:=(N:Int))
    (fun p hp => by simp [cutoff,hp]) t 0 (by omega)
  simpa using h

/-- An all-horizons theorem with FINITE initial witnesses and fixed left
depth. The right support is allowed to increase with the requested horizon. -/
theorem arbitrarily_long_finite_left_ambiguity (H : Nat) :
    ∃ x y : Int → Bool, FinConfig x ∧ FinConfig y ∧
      HasLeftEdge x (-3) ∧ HasLeftEdge y (-3) ∧ x (-1) ≠ y (-1) ∧
      (∀ t, t < H → evol x t 0 = evol y t 0) := by
  refine ⟨cutoff H leftExample,cutoff H rightExample,
    cutoff_finite (fun _ h => left_white h) H,
    cutoff_finite (fun _ h => right_white h) H,
    cutoff_edge left_edge H,cutoff_edge right_edge H,?_,?_⟩
  · simpa [cutoff] using different_left_neighbor
  · intro t ht
    rw [cutoff_trace _ _ _ (by omega),cutoff_trace _ _ _ (by omega)]
    exact same_center_trace t

theorem no_uniform_finite_left_recovery :
    ¬ ∃ H : Nat, ∀ x y : Int → Bool, FinConfig x → FinConfig y →
      HasLeftEdge x (-3) → HasLeftEdge y (-3) →
      (∀ t, t < H → evol x t 0 = evol y t 0) → x (-1) = y (-1) := by
  rintro ⟨H,hH⟩
  obtain ⟨x,y,hx,hy,hex,hey,hne,heq⟩ := arbitrarily_long_finite_left_ambiguity H
  exact hne (hH x y hx hy hex hey heq)

/-- Four center observations recover the initial left neighbor at depth two. -/
def decodeDepthTwo (c0 c1 c2 c3 : Bool) : Bool :=
  if c0 then !c1 else if c1 then c2 else c2 && !c3

theorem recover_left_neighbor_at_depth_two {x : Int → Bool}
    (hx : HasLeftEdge x (-2)) :
    x (-1) = decodeDepthTwo (evol x 0 0) (evol x 1 0) (evol x 2 0) (evol x 3 0) := by
  have h2 : x (-2) = true := hx.1
  have h3 : x (-3) = false := hx.2 (-3) (by decide)
  simp only [evol,Rule30Jen.rule,Int.reduceSub,Int.reduceAdd]
  rw [h2,h3]
  cases x (-1) <;> cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> decide

/-- In contrast to depth three, four observations suffice at depth two,
uniformly over every right half. No finiteness hypothesis is required. -/
theorem left_neighbor_rigid_at_depth_two {x y : Int → Bool}
    (hx : HasLeftEdge x (-2)) (hy : HasLeftEdge y (-2))
    (htrace : ∀ t, t < 4 → evol x t 0 = evol y t 0) : x (-1) = y (-1) := by
  rw [recover_left_neighbor_at_depth_two hx,recover_left_neighbor_at_depth_two hy,
      htrace 0 (by decide),htrace 1 (by decide),htrace 2 (by decide),htrace 3 (by decide)]

/-! ## Complete non-positive half-line rigidity (`p ≤ 0`) at depth two -/

/-- **Complete Non-Positive Half-Line Rigidity from Four Center Observations at Depth Two (`nonpositive_half_rigid_at_depth_two`).** -/
theorem nonpositive_half_rigid_at_depth_two {x y : Int → Bool}
    (hx : HasLeftEdge x (-2)) (hy : HasLeftEdge y (-2))
    (htrace : ∀ t, t < 4 → evol x t 0 = evol y t 0) :
    ∀ p : Int, p ≤ 0 → x p = y p := by
  intro p hp
  by_cases hlt : p < -2
  · rw [hx.2 p hlt, hy.2 p hlt]
  · have hcases : p = -2 ∨ p = -1 ∨ p = 0 := by omega
    rcases hcases with rfl | rfl | rfl
    · rw [hx.1, hy.1]
    · exact left_neighbor_rigid_at_depth_two hx hy htrace
    · exact htrace 0 (by decide)

end Ruliology.CellularAutomata.Rule30TraceAmbiguity
