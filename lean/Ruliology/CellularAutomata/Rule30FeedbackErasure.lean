module

public import Ruliology.CellularAutomata.Rule30ControlledResponse
public import Ruliology.CellularAutomata.Rule30FiniteConfigs

/-!
# Finite feedback can erase a distinction between controlled responses

The right halves `1` and `11` are not universally response equivalent.
When the initial center is white, one actual Rule 30 step sends them to
`11` and `101`, which are universally response equivalent. Consequently
they give the same entire left space-time diagram under any common initial
left half whose center is white. Specializing that left half to white gives
two finite, nonzero configurations with identical, non-eventually-constant
center traces. This does not decide eventual periodicity or distinguish
configurations with different left edges.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30FeedbackErasure

open Rule30Jen Rule30Realization Rule30ControlledResponse
open Rule30PeriodTwoSideways Rule30ZeroBoundaryBarriers

theorem step_white_one : step false (word [true]) = word [true,true] := by
  funext k
  cases k with
  | zero => rfl
  | succ k => cases k <;> rfl

theorem step_white_two : step false (word [true,true]) = word [true,false,true] := by
  funext k
  cases k with
  | zero => rfl
  | succ k =>
      cases k with
      | zero => rfl
      | succ k => cases k <;> rfl

theorem white_step_erases_distinction :
    SameResponse (step false (word [true])) (step false (word [true,true])) := by
  rw [step_white_one,step_white_two]
  exact sameResponse_symm (tail_101_response [])

theorem initial_responses_differ : ¬ SameResponse (word [true]) (word [true,true]) :=
  fixed_driver_counterexample.2

theorem first_left_equal (left : Int → Bool) :
    ∀ p, p≤0 → evol (splice left (word [true])) 1 p =
      evol (splice left (word [true,true])) 1 p := by
  intro p hp
  change rule (splice left (word [true]) (p-1)) (splice left (word [true]) p)
      (splice left (word [true]) (p+1)) =
    rule (splice left (word [true,true]) (p-1)) (splice left (word [true,true]) p)
      (splice left (word [true,true]) (p+1))
  rw [show splice left (word [true]) (p-1)=left (p-1) by simp [splice,show p-1≤0 by omega],
      show splice left (word [true,true]) (p-1)=left (p-1) by simp [splice,show p-1≤0 by omega]]
  simp only [splice,hp,ite_true]
  by_cases hz : p=0
  · subst p; rfl
  · simp [show p+1≤0 by omega]

theorem first_right_sameResponse (left : Int → Bool) (hwhite : left 0=false) :
    SameResponse (rightPart (evol (splice left (word [true])) 1))
      (rightPart (evol (splice left (word [true,true])) 1)) := by
  rw [show 1=0+1 from rfl,rightPart_next,rightPart_next]
  simp only [evol,splice,Int.le_refl,ite_true,hwhite]
  exact white_step_erases_distinction

/-- All actual left columns agree, despite initially inequivalent right responses. -/
theorem same_left_forever (left : Int → Bool) (hwhite : left 0=false) :
    ∀ t p, p≤0 → evol (splice left (word [true])) t p =
      evol (splice left (word [true,true])) t p := by
  intro t p hp
  cases t with
  | zero => simp [evol,splice,hp]
  | succ t =>
      have h := (feedback_left_equal (first_left_equal left)
        (first_right_sameResponse left hwhite) t).1 p hp
      simpa only [evol_restart,Nat.add_comm 1 t] using h

def single : Int → Bool := splice (fun _ => false) (word [true])
def double : Int → Bool := splice (fun _ => false) (word [true,true])

theorem single_support (p : Int) : single p = decide (p=1) := by
  by_cases hp : p≤0
  · simp [single,splice,hp,show p≠1 by omega]
  · by_cases h1 : p=1
    · subst p; rfl
    · have hn : 1≤p.toNat-1 := by omega
      obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le hn
      simp [single,splice,hp,word,hk,List.getD,h1]

theorem double_support (p : Int) : double p = decide (p=1 ∨ p=2) := by
  by_cases hp : p≤0
  · simp [double,splice,hp,show p≠1 by omega,show p≠2 by omega]
  · by_cases h1 : p=1
    · subst p; rfl
    · by_cases h2 : p=2
      · subst p; rfl
      · have hn : 2≤p.toNat-1 := by omega
        obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le hn
        simp [double,splice,hp,word,hk,List.getD,h1,h2]

theorem single_finite : FinConfig single := by
  refine ⟨1,?_⟩
  intro p hp
  rw [single_support]
  simp [show p≠1 by intro h; subst p; simp at hp]

theorem double_finite : FinConfig double := by
  refine ⟨2,?_⟩
  intro p hp
  rw [double_support]
  simp [show p≠1 by intro h; subst p; simp at hp,
    show p≠2 by intro h; subst p; simp at hp]

theorem single_nonzero : ∃ p, single p=true := ⟨1,rfl⟩
theorem double_nonzero : ∃ p, double p=true := ⟨1,rfl⟩

theorem configurations_differ : single≠double := by
  intro h
  have he := congrFun h 2
  change false=true at he
  cases he

theorem same_actual_left : ∀ t p, p≤0 → evol single t p=evol double t p :=
  same_left_forever (fun _ => false) rfl

theorem same_actual_center (t : Nat) : evol single t 0=evol double t 0 :=
  same_actual_left t 0 (by omega)

theorem same_actual_right_head (t : Nat) : evol single t 1=evol double t 1 := by
  cases t with
  | zero => rfl
  | succ t =>
      have h := (feedback_left_equal (first_left_equal (fun _ => false))
        (first_right_sameResponse (fun _ => false) rfl) t).2
      have he := (sameResponse_observe h).1
      change evol (evol single 1) t 1=evol (evol double 1) t 1 at he
      simpa only [evol_restart,Nat.add_comm 1 t] using he

theorem initial_rights_not_sameResponse : ¬ SameResponse (rightPart single) (rightPart double) := by
  simpa only [single,double,rightPart_splice] using initial_responses_differ

theorem center_not_eventually_constant : ¬ ∃ T b, ∀ t, T≤t → evol single t 0=b :=
  Rule30FiniteConfigs.no_column_eventually_constant_finite single_finite single_nonzero 0

theorem right_head_not_eventually_constant : ¬ ∃ T b, ∀ t, T≤t → evol single t 1=b :=
  Rule30FiniteConfigs.no_column_eventually_constant_finite single_finite single_nonzero 1

/-- A genuine finite feedback counterexample, without an eventually constant trace. -/
theorem finite_feedback_counterexample :
    FinConfig single ∧ FinConfig double ∧ single≠double ∧
    (∀ t, evol single t 0=evol double t 0) ∧
    (∀ t, evol single t 1=evol double t 1) ∧
    (¬ ∃ T b, ∀ t, T≤t → evol single t 0=b) ∧
    (¬ ∃ T b, ∀ t, T≤t → evol single t 1=b) ∧
    ¬ SameResponse (rightPart single) (rightPart double) :=
  ⟨single_finite,double_finite,configurations_differ,same_actual_center,
    same_actual_right_head,center_not_eventually_constant,right_head_not_eventually_constant,
    initial_rights_not_sameResponse⟩

/-! ## Unified all-time agreement on `p ≤ 1`, sharpness at `p = 2`, and `p ≤ 1` agreement for `tail_011` splices -/

/-- **Unified All-Time Agreement on `p ≤ 1` and Sharpness at `p = 2` (`same_actual_up_to_col_one_and_sharp_at_two`).** -/
theorem same_actual_up_to_col_one_and_sharp_at_two (left : Int → Bool) (bs : List Bool) (t : Nat) :
    (∀ p : Int, p ≤ 1 → evol single t p = evol double t p) ∧
    evol single 0 2 ≠ evol double 0 2 ∧
    (∀ p : Int, p ≤ 1 →
      evol (splice left (word (bs ++ [false, true, true]))) t p =
      evol (splice left (word (bs ++ [false, true]))) t p) := by
  refine ⟨fun p hp => ?_, by decide, fun p hp => ?_⟩
  · by_cases hp0 : p ≤ 0
    · exact same_actual_left t p hp0
    · have hp1 : p = 1 := by omega
      subst hp1
      exact same_actual_right_head t
  · have hfb := feedback_left_equal
      (x := splice left (word (bs ++ [false, true, true])))
      (y := splice left (word (bs ++ [false, true])))
      (fun q hq => by simp [splice, hq])
      (by rw [rightPart_splice, rightPart_splice]; exact tail_011_response bs) t
    by_cases hp0 : p ≤ 0
    · exact hfb.1 p hp0
    · have hp1 : p = 1 := by omega
      subst hp1
      exact (sameResponse_observe hfb.2).1

end Ruliology.CellularAutomata.Rule30FeedbackErasure
