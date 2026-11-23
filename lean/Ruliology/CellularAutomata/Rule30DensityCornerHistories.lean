module
public import Ruliology.CellularAutomata.Rule30DensityPolygon
public import Ruliology.CellularAutomata.Rule30DensityOneHistory

/-! Each corner of the polygon, from an arbitrary right half.

`Rule30DensityControl.physical_mode` and its five certified controllers are restated here in the counts
`black` and `ends` of `Rule30SourceDensityRegion`, with their numbers written out. `Tracks W D c a cap`
says: every prescribed row on the sites `j ≥ 0` is the right half of an ordinary full-line configuration
whose counts at sites `0` and `1`, on every interval starting at tick `W`, stay within `cap` of the corner:
`|D*C - c*T| ≤ cap` and `|D*A - a*T| ≤ cap`. The five instances are the five corners. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30SourceDensityRegion
open Rule30Jen Rule30Realization
open Rule30SourceObservables (count source bit)
open Rule30DensityControl

private theorem total_count (f : Nat → Bool) (n : Nat) :
    total (fun t => ((f t).toNat : Int)) n=count f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have step : ((f n).toNat : Int)=bit (f n) := by cases f n <;> rfl
    simp only [total,count,ih,step]

/-- From tick `W` on, both counts stay within `cap` of the corner `(c/D, a/D)`, whatever the right half. -/
def Tracks (W D c a cap : Nat) : Prop := ∀ r : Nat → Bool, ∃ x : Int → Bool,
    (∀ j : Nat, evol x 0 j=r j) ∧ ∀ n : Nat,
      -(cap : Int)≤(D : Int)*black (evol x) 0 W n-(c : Int)*(n : Int) ∧
      (D : Int)*black (evol x) 0 W n-(c : Int)*(n : Int)≤(cap : Int) ∧
      -(cap : Int)≤(D : Int)*ends (evol x) 0 W n-(a : Int)*(n : Int) ∧
      (D : Int)*ends (evol x) 0 W n-(a : Int)*(n : Int)≤(cap : Int)

/-- Every certified controller tracks its corner from any right half. -/
theorem tracks_of_mode {m : Mode} (good : GoodMode m) :
    Tracks m.width m.denominator m.black m.source m.cap := by
  intro r
  obtain ⟨x,start,bounds⟩ := physical_mode good r
  refine ⟨x,start,fun n => ?_⟩
  have h := bounds n
  have hb : total (fun t => ((evol x (m.width+t) 0).toNat : Int)) n=black (evol x) 0 m.width n :=
    total_count (fun t => evol x (m.width+t) 0) n
  have he : total (fun t => (((evol x (m.width+t) 0 && !(evol x (m.width+t) 1)).toNat) : Int)) n=
      ends (evol x) 0 m.width n := by
    have e := total_count (fun t => (evol x (m.width+t) 0 && !(evol x (m.width+t) 1))) n
    simpa only [ends,source,Int.zero_add] using e
  simp only [hb,he] at h
  exact h

/-- **The five corners, each from an arbitrary right half.** The widths, denominators,
target numerators and error caps of the five controllers. -/
theorem corners_from_any_right_half :
    Tracks 2 1 0 0 0 ∧ Tracks 6 3 1 0 3 ∧ Tracks 21 4 3 1 3 ∧ Tracks 37 10 9 4 12 ∧ Tracks 3 1 1 1 0 :=
  ⟨tracks_of_mode zero_policy,tracks_of_mode oneThird_policy,tracks_of_mode threeQuarters_policy,
    tracks_of_mode nineTenths_policy,tracks_of_mode one_policy⟩

end Ruliology.CellularAutomata.Rule30SourceDensityRegion
