module
public import Ruliology.CellularAutomata.Rule30DensityVertices

/-! Every prescribed initial right half extends to a full-line orbit which tracks the black
and run-end counts of a certified controller. The proof steers to its initial state in
exactly its width in ticks, joins the controller run to the steering segment, then realizes
that entire stream of half-rows by one full-line initial condition. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30DensityControl
open Rule30Realization

/-- A physical orbit with any preassigned nonnegative initial half-row enters the chosen finite controller after its width ticks. -/
theorem physical_mode {m : Mode} (good : GoodMode m) (r : Row) :
    ∃ x : Int → Bool, (∀ j : Nat,evol x 0 j=r j) ∧ ∀ n,
      let X := (m.denominator:Int)*total (fun t => ((evol x (m.width+t) 0).toNat:Int)) n-m.black*(n:Int)
      let A := (m.denominator:Int)*total (fun t => (((evol x (m.width+t) 0 && !(evol x (m.width+t) 1)).toNat):Int)) n-m.source*(n:Int)
      (-(m.cap:Int)≤X ∧ X≤m.cap ∧ -(m.cap:Int)≤A ∧ A≤m.cap) := by
  obtain ⟨v,path,fit⟩ := install m r
  obtain ⟨z,z0,zEnd,zStep⟩ := realize_segment path
  let s (t : Nat) := if t<m.width then z t else (run m v (t-m.width)).2
  have early (t : Nat) (h : t≤m.width) : s t=z t := by
    by_cases e : t=m.width
    · subst t;simp [s,run,zEnd]
    · simp [s,show t<m.width by omega]
  have late (t : Nat) : s (m.width+t)=(run m v t).2 := by
    simp [s,show ¬m.width+t<m.width by omega]
  have phys (t : Nat) : OpenStep (s t) (s (t+1)) := by
    by_cases old : t<m.width
    · rw [early t (by omega),early (t+1) (by omega)];exact zStep t old
    · obtain ⟨n,rfl⟩ : ∃ n,t=m.width+n := ⟨t-m.width,by omega⟩
      rw [late,show m.width+n+1=m.width+(n+1) by omega,late];exact run_open m v n
  obtain ⟨x,actual⟩ := realize_stream s phys
  refine ⟨x,fun j => (actual 0 j).trans (by rw [early 0 (Nat.zero_le _),z0]),?_⟩
  intro n
  have black (t : Nat) : evol x (m.width+t) 0=(run m v t).2 0 := by
    simpa [late] using actual (m.width+t) 0
  have right (t : Nat) : evol x (m.width+t) 1=(run m v t).2 1 := by
    simpa [late] using actual (m.width+t) 1
  simpa only [black,right,blackWeight,sourceWeight] using block_bounds good v fit n

end Ruliology.CellularAutomata.Rule30DensityControl
