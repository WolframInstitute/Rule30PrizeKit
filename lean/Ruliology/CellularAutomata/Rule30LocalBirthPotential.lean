module

public import Ruliology.CellularAutomata.Rule30PeriodicBirthCounterexample
public import Ruliology.CellularAutomata.Rule30ZeroBoundaryBarriers

/-! No fixed finite-window Int-valued potential pays every backward-four birth
on all finite actual configurations with the stated local alternating center.
This is a finite-time obstruction, not a single-seed or all-time-periodic claim. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30LocalBirthPotential
open Ruliology.CellularAutomata
open Rule30Realization
namespace Cycle
abbrev orbit := Rule30PeriodicBirthCounterexample.orbit
end Cycle

def cut (R : Nat) (p : Int) : Bool :=
  if -(R+20 : Int) ≤ p ∧ p ≤ (R+20 : Int) then Cycle.orbit 0 p else false

def FiniteNonzero (z : Int → Bool) : Prop :=
  (∃ M : Nat, ∀ p : Int, p < -(M:Int) ∨ (M:Int) < p → z p=false) ∧
  (∃ p : Int, z p=true)

theorem cut_finite_nonzero (R : Nat) : FiniteNonzero (cut R) := by
  constructor
  · refine ⟨R+20, ?_⟩
    intro p hp
    simp only [cut]
    rw [ite_eq_right (by omega)]
  · refine ⟨-1, ?_⟩
    have h : -(R+20 : Int) ≤ -1 ∧ (-1:Int) ≤ R+20 := by omega
    rw [cut, ite_eq_left h]
    decide

theorem evol_orbit (t : Nat) (p : Int) :
    evol (Cycle.orbit 0) t p=Cycle.orbit t p := by
  induction t generalizing p with
  | zero => rfl
  | succ t ih =>
    simp only [evol, ih]
    simpa using (Rule30PeriodicBirthCounterexample.physical_recurrence (t:Int) p).symm

theorem cut_agrees (R s : Nat) (hs : s≤16) (p : Int)
    (hp0 : -(R+1 : Int) ≤ p) (hp1 : p ≤ R+1) :
    evol (cut R) s p=Cycle.orbit s p := by
  have h := Rule30ZeroBoundaryBarriers.evol_local
    (x := Cycle.orbit 0) (x' := cut R)
    (a := -(R+20 : Int)) (b := R+20)
    (fun j h0 h1 => by simp only [cut]; exact ite_eq_left (And.intro h0 h1))
    s p (by omega) (by omega)
  exact h.trans (evol_orbit s p)

theorem cycle_center (s : Nat) :
    Cycle.orbit s 0=decide (s%2=1) := by
  have h : ∀ r : Fin 6,
      Rule30PeriodicBirthCounterexample.bit r.val 0=decide (r.val%2=1) := by decide
  have hr : Rule30PeriodicBirthCounterexample.residue (s:Int) 6=s%6 := by
    unfold Rule30PeriodicBirthCounterexample.residue
    omega
  change Rule30PeriodicBirthCounterexample.bit
    (Rule30PeriodicBirthCounterexample.residue (s:Int) 6) 0=_
  rw [hr]
  have e := h ⟨s%6,Nat.mod_lt _ (by decide)⟩
  have hm : (s%6)%2=s%2 := by omega
  simpa only [hm] using e

def LocalAlt (z : Int → Bool) (t : Nat) : Prop :=
  ∀ s : Nat, t-4≤s → s≤t+1 → evol z s 0=decide (s%2=1)

theorem cut_local_alt (R t : Nat) (ht : 4≤t) (ht' : t≤15) :
    LocalAlt (cut R) t := by
  intro s _ hs
  rw [cut_agrees R s (by omega) 0 (by omega) (by omega),cycle_center]

def coordinate (R : Nat) (i : Fin (2*R+1)) : Int := (i.val:Int)-R
abbrev Observation (R : Nat) :=
  (Fin (2*R+1) → Bool) × (Fin (2*R+1) → Bool) × Nat
def observe (R : Nat) (z : Int → Bool) (t : Nat) : Observation R :=
  (fun i => evol z t (coordinate R i),
   fun i => evol z (t-4) (coordinate R i),t%4)

theorem coordinate_bounds (R : Nat) (i : Fin (2*R+1)) :
    -(R:Int) ≤ coordinate R i ∧ coordinate R i ≤ R := by
  have hi := i.isLt
  unfold coordinate
  omega

theorem cut_observation_loop (R : Nat) : observe R (cut R) 16=observe R (cut R) 4 := by
  apply Prod.ext
  · funext i
    have hi := coordinate_bounds R i
    change evol (cut R) 16 (coordinate R i)=evol (cut R) 4 (coordinate R i)
    rw [cut_agrees R 16 (by decide) _ (by omega) (by omega),
      cut_agrees R 4 (by decide) _ (by omega) (by omega)]
    exact (Rule30PeriodicBirthCounterexample.temporal_period6 10 _).trans
      (Rule30PeriodicBirthCounterexample.temporal_period6 4 _)
  · apply Prod.ext
    · funext i
      have hi := coordinate_bounds R i
      change evol (cut R) 12 (coordinate R i)=evol (cut R) 0 (coordinate R i)
      rw [cut_agrees R 12 (by decide) _ (by omega) (by omega),
        cut_agrees R 0 (by decide) _ (by omega) (by omega)]
      exact (Rule30PeriodicBirthCounterexample.temporal_period6 6 _).trans
        (Rule30PeriodicBirthCounterexample.temporal_period6 0 _)
    · rfl

def mismatch (z : Int → Bool) (t : Nat) : Bool :=
  xor (evol z t 1) (evol z (t-4) 1)
def TrueBirth (z : Int → Bool) (t : Nat) : Prop :=
  mismatch z t=false ∧ mismatch z (t+1)=true
instance (z : Int → Bool) (t : Nat) : Decidable (TrueBirth z t) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem cut_mismatch (R t : Nat) (ht : t≤16) :
    mismatch (cut R) t=Rule30PeriodicBirthCounterexample.backwardMismatch t := by
  unfold mismatch Rule30PeriodicBirthCounterexample.backwardMismatch
  rw [cut_agrees R t ht 1 (by omega) (by omega),
    cut_agrees R (t-4) (by omega) 1 (by omega) (by omega)]

theorem cut_true_births (R : Nat) : TrueBirth (cut R) 4 ∧ TrueBirth (cut R) 10 := by
  constructor
  · change mismatch (cut R) 4=false ∧ mismatch (cut R) 5=true
    rw [cut_mismatch R 4 (by decide),cut_mismatch R 5 (by decide)]
    exact Rule30PeriodicBirthCounterexample.true_birth_every_six 0
  · change mismatch (cut R) 10=false ∧ mismatch (cut R) 11=true
    rw [cut_mismatch R 10 (by decide),cut_mismatch R 11 (by decide)]
    exact Rule30PeriodicBirthCounterexample.true_birth_every_six 1

/-- There is no such local birth-consuming Int-valued potential, for any radius.
Only the finite local alternating-center premise is used; no all-time periodic
premise is silently imposed on the finite cutoff witnesses. -/
theorem no_local_birth_potential (R : Nat) :
    ¬ ∃ E : Observation R → Int,
      ∀ z : Int → Bool, FiniteNonzero z → ∀ t : Nat, 4≤t → LocalAlt z t →
        E (observe R z (t+1)) + (if TrueBirth z t then 1 else 0) ≤ E (observe R z t) := by
  rintro ⟨E,hE⟩
  have step (t : Nat) (ht : 4≤t) (ht' : t≤15) :=
    hE (cut R) (cut_finite_nonzero R) t ht (cut_local_alt R t ht ht')
  have weak (t : Nat) (ht : 4≤t) (ht' : t≤15) :
      E (observe R (cut R) (t+1)) ≤ E (observe R (cut R) t) := by
    have h := step t ht ht'
    split at h <;> omega
  have tail (n : Nat) (hn : n≤11) :
      E (observe R (cut R) (5+n)) ≤ E (observe R (cut R) 5) := by
    induction n with
    | zero => exact Int.le_refl _
    | succ n ih =>
      have h := weak (5+n) (by omega) (by omega)
      have h' := ih (by omega)
      have he : 5+(n+1)=5+n+1 := by omega
      rw [he]
      omega
  have htail := tail 11 (by decide)
  have hfirst := step 4 (by decide) (by decide)
  rw [ite_eq_left (cut_true_births R).1] at hfirst
  have hloop := congrArg E (cut_observation_loop R)
  change E (observe R (cut R) 16) ≤ E (observe R (cut R) 5) at htail
  change E (observe R (cut R) 5)+1 ≤ E (observe R (cut R) 4) at hfirst
  omega

end Ruliology.CellularAutomata.Rule30LocalBirthPotential
