module
public import Ruliology.CellularAutomata.Rule30DensitySharpness

/-! The converse of `polygon_necessary`, and the classification as an equivalence.

`polygon_necessary` says that a linear inequality `α*C + β*A ≤ γ*T + K` which holds for every
nonzero finite seed, with one constant `K`, holds without the constant at the five corners
`(T, C, A) = (1,0,0), (3,1,0), (4,3,1), (10,9,4), (1,1,1)`. This module proves the converse, for every
ordinary evolution, every site and every interval: the five corner inequalities give the bound, with
the explicit constant `9|α| + 4|β|`. The proof writes `(α, β)` in the normal cone of one corner as
a nonnegative combination of the two faces that meet there: `A ≥ 0`, Condrey's `3C ≤ T + 5A + 3`,
`middle_face`, `high_face` and `A ≤ C`.

So the linear inequalities between the duration, the black count and the run-end count that hold
uniformly are exactly those that hold at the five corners, and it makes no difference whether
the bound is asked of all evolutions or only of nonzero finite seeds. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30SourceDensityRegion
open Rule30Jen Rule30Realization
open Rule30SourceObservables (count source bit)

/-- The linear inequality holds, with the additive constant `K`, on every interval at every site
of every ordinary evolution. -/
def UniformBound (α β γ K : Int) : Prop := ∀ u : History, Evolution u → ∀ (j : Int) (s n : Nat),
    α*black u j s n+β*ends u j s n≤γ*(n:Int)+K

/-- The linear inequality holds, with no constant, at the five corners of the polygon. -/
def AtCorners (α β γ : Int) : Prop :=
    0≤γ ∧ α≤3*γ ∧ 3*α+β≤4*γ ∧ 9*α+4*β≤10*γ ∧ α+β≤γ

private theorem count_nonneg (f : Nat → Bool) (n : Nat) : 0≤count f n := by
  induction n with
  | zero => simp [count]
  | succ n ih =>
    have b := (Rule30SourceObservables.bit_bounds (f n)).1
    simp only [count];omega

private theorem count_mono {f g : Nat → Bool} (h : ∀ t, f t=true → g t=true) (n : Nat) :
    count f n≤count g n := by
  induction n with
  | zero => simp [count]
  | succ n ih =>
    have step : bit (f n)≤bit (g n) := by
      cases hf : f n with
      | false => exact (Rule30SourceObservables.bit_bounds (g n)).1
      | true => rw [h n hf];exact Int.le_refl _
    simp only [count];omega

theorem ends_nonneg (u : History) (j : Int) (s n : Nat) : 0≤ends u j s n := count_nonneg _ n

/-- A run end is a black cell. -/
theorem ends_le_black (u : History) (j : Int) (s n : Nat) : ends u j s n≤black u j s n :=
  count_mono (fun t h => by
    cases hb : u (s+t) j with
    | false => simp [source,hb] at h
    | true => rfl) n

/-- The five faces give every inequality that holds at the five corners. The cases are the normal
cones of the corners, in the order `(9/10,2/5)`, `(1,1)`, `(3/4,1/4)`, `(1/3,0)`, `(0,0)`. -/
private theorem arithmetic {α β γ C A T : Int} (corners : AtCorners α β γ)
    (hT : 0≤T) (hA : 0≤A) (hAC : A≤C)
    (f1 : 3*C≤T+5*A+3) (f2 : 2*C≤T+2*A+1) (f3 : 6*C≤5*T+A+5) :
    α*C+β*A≤γ*T+((9*α.natAbs+4*β.natAbs : Nat) : Int) := by
  obtain ⟨g0,v1,v2,v3,v4⟩ := corners
  have a1 : α≤(α.natAbs : Int) := by omega
  have a2 : -α≤(α.natAbs : Int) := by omega
  have b1 : β≤(β.natAbs : Int) := by omega
  have b2 : -β≤(β.natAbs : Int) := by omega
  have k : ((9*α.natAbs+4*β.natAbs : Nat) : Int)=9*(α.natAbs : Int)+4*(β.natAbs : Int) := by omega
  rw [k]
  by_cases p : 0≤α+β
  · by_cases q : α+6*β≤0
    · have h1 : 0≤(-α-6*β)*(T+2*A+1-2*C) := Int.mul_nonneg (by omega) (by omega)
      have h2 : 0≤(2*(α+β))*(5*T+A+5-6*C) := Int.mul_nonneg (by omega) (by omega)
      have h3 : 0≤(10*γ-(9*α+4*β))*T := Int.mul_nonneg (by omega) hT
      grind
    · have h1 : 0≤(α+β)*(5*T+A+5-6*C) := Int.mul_nonneg p (by omega)
      have h2 : 0≤(α+6*β)*(C-A) := Int.mul_nonneg (by omega) (by omega)
      have h3 : 0≤(γ-(α+β))*T := Int.mul_nonneg (by omega) hT
      grind
  · by_cases q : 0≤5*α+3*β
    · have h1 : 0≤(-2*(α+β))*(T+5*A+3-3*C) := Int.mul_nonneg (by omega) (by omega)
      have h2 : 0≤(5*α+3*β)*(T+2*A+1-2*C) := Int.mul_nonneg q (by omega)
      have h3 : 0≤(4*γ-(3*α+β))*T := Int.mul_nonneg (by omega) hT
      grind
    · by_cases r : 0≤α
      · have h1 : 0≤(-5*α-3*β)*A := Int.mul_nonneg (by omega) hA
        have h2 : 0≤α*(T+5*A+3-3*C) := Int.mul_nonneg r (by omega)
        have h3 : 0≤(3*γ-α)*T := Int.mul_nonneg (by omega) hT
        grind
      · have h1 : 0≤(-α)*(C-A) := Int.mul_nonneg (by omega) (by omega)
        have h2 : 0≤(-α-β)*A := Int.mul_nonneg (by omega) hA
        have h3 : 0≤γ*T := Int.mul_nonneg g0 hT
        grind

/-- **Sufficiency.** A linear inequality that holds at the five corners holds on every interval
at every site of every ordinary evolution, with the additive constant `9|α| + 4|β|`. -/
theorem polygon_sufficient {α β γ : Int} (corners : AtCorners α β γ) :
    UniformBound α β γ ((9*α.natAbs+4*β.natAbs : Nat) : Int) := by
  intro u hu j s n
  obtain ⟨f1,f2,f3⟩ := region hu j s n
  exact arithmetic corners (Int.natCast_nonneg n) (ends_nonneg u j s n) (ends_le_black u j s n)
    f1 f2 f3

/-- A bound for every evolution is in particular a bound for every nonzero finite seed. -/
theorem finite_of_uniform {α β γ K : Int} (h : UniformBound α β γ K) : FiniteBound α β γ K :=
  fun x _ _ n => h (evol x) (fun _ _ => rfl) 0 0 n

/-- **The classification, over all evolutions.** Some constant makes the linear inequality hold
uniformly exactly when it holds at the five corners. -/
theorem uniform_bound_iff (α β γ : Int) : (∃ K, UniformBound α β γ K) ↔ AtCorners α β γ :=
  ⟨fun ⟨_,h⟩ => polygon_necessary (finite_of_uniform h),fun c => ⟨_,polygon_sufficient c⟩⟩

/-- **The classification, over nonzero finite seeds.** The same five inequalities decide it. -/
theorem finite_bound_iff (α β γ : Int) : (∃ K, FiniteBound α β γ K) ↔ AtCorners α β γ :=
  ⟨fun ⟨_,h⟩ => polygon_necessary h,fun c => ⟨_,finite_of_uniform (polygon_sufficient c)⟩⟩

/-- The two notions of a uniform linear bound agree. -/
theorem finite_bound_iff_uniform (α β γ : Int) :
    (∃ K, FiniteBound α β γ K) ↔ (∃ K, UniformBound α β γ K) :=
  (finite_bound_iff α β γ).trans (uniform_bound_iff α β γ).symm

end Ruliology.CellularAutomata.Rule30SourceDensityRegion
