module

public import Ruliology.CellularAutomata.Rule30RestartVisibility

/-!
# Periodic controls for the white-left restart test

Repeat the 37 readings at singleton age 61476. The gap between the physical
exit at 3 and the black-only failure at 35 recurs at every phase-zero launch
in a full-line Rule 30 history. Any fixed number of cycles also has a finite
seed. In the infinite statement only the positive half is prescribed. The
finite seed can depend on the requested horizon.

The Rule 210 singleton supplies a separate control for the proposed XOR
observer. All forward center shifts miss its adjoining column on the first
white tick. The two rules have identical right-input visibility and opposite
right-neighbor behavior immediately after a white/black adjacent pair.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30PeriodicGapControl
open Rule30Jen Rule30Realization Rule30DrivenLeft Rule30MarkedGaps Rule30RestartVisibility

/-- Repeat the 37 actual readings needed to determine the two exit times. -/
def clock (t : Nat) : Bool := cell (61476 + t%37) 0

private theorem wall_prefix {c d : Nat → Bool} (t : Nat)
    (same : ∀ i, i≤t → c i=d i) (p : Int) :
    L c (fun _ => false) t p = L d (fun _ => false) t p := by
  induction t generalizing p with
  | zero => simp [L,same 0 (by omega)]
  | succ t ih =>
    simp only [L]
    split
    · rw [ih (fun i hi => same i (by omega)), ih (fun i hi => same i (by omega)),
        ih (fun i hi => same i (by omega))]
    · exact same _ (by omega)

private theorem fails_iff {c d : Nat → Bool} {t : Nat}
    (h : ∀ i, i≤t+1 → c i=d i) : Failed c t ↔ Failed d t := by
  unfold Failed
  rw [wall_prefix t (fun i hi => h i (by omega)),h t (by omega),h (t+1) (by omega)]

private theorem feasible_iff {c d : Nat → Bool} {t : Nat}
    (h : ∀ i, i≤t → c i=d i) : Feasible c t ↔ Feasible d t := by
  constructor <;> rintro ⟨x,white,eq⟩
  · exact ⟨x,white,fun i hi => (eq i hi).trans (h i hi)⟩
  · exact ⟨x,white,fun i hi => (eq i hi).trans (h i hi).symm⟩

private theorem same_gap {c : Nat → Bool} (copy : ∀ i, i≤36 → c i=cell (61476+i) 0) :
    PhysicalExit c 3 ∧ FirstFailure c 35 := by
  obtain ⟨_,feas,no⟩ := singleton_physical_exits
  obtain ⟨⟨bad,early⟩,_⟩ := singleton_delayed_but_impossible
  refine ⟨⟨(feasible_iff (fun i hi => copy i (by omega))).mpr feas,
    fun h => no ((feasible_iff (fun i hi => copy i (by omega))).mp h)⟩,
    (fails_iff (fun i hi => copy i (by omega))).mpr bad,?_⟩
  exact fun t ht h => early t ht ((fails_iff (fun i hi => copy i (by omega))).mp h)

private theorem phase_prefix (k t : Nat) (ht : t≤36) :
    clock (k*37+t) = cell (61476+t) 0 := by
  simp [clock,Nat.add_mod,Nat.mod_eq_of_lt (show t<37 by omega)]

/-- One full-line Rule 30 history has a strictly white initial positive half,
period 37 at the center, and the same physical/black-only exit gap on every
cycle. No left-finiteness assumption is made. -/
theorem repeated_gap : ∃ x : Int → Bool, (∀ p, 1≤p → x p=false) ∧
    (∀ t, trace x (t+37)=trace x t) ∧
    ∀ k, PhysicalExit (fun t => trace x (k*37+t)) 3 ∧
      FirstFailure (fun t => trace x (k*37+t)) 35 := by
  let x := conf (fun _ => false) clock
  obtain ⟨right,hit⟩ := realize (fun _ => false) clock
  have eq (t : Nat) : trace x t=clock t := hit t
  exact ⟨x,right,fun t => by rw [eq,eq]; simp [clock],fun k =>
    same_gap (fun i hi => (eq _).trans (phase_prefix k i hi))⟩

/-- Every prescribed finite number of cycles is also achieved by a single
finite launch supported on [-(37*K+36),0]. The launch may depend on K. -/
theorem finite_repetitions (K : Nat) : ∃ y : Int → Bool,
    (∀ p : Int, p < -((37*K+36:Nat):Int) ∨ 0<p → y p=false) ∧
    (∀ t, t≤37*K+36 → trace y t=clock t) ∧
    ∀ k, k≤K → PhysicalExit (fun t => trace y (k*37+t)) 3 ∧
      FirstFailure (fun t => trace y (k*37+t)) 35 := by
  let x := conf (fun _ => false) clock
  let y := fun p : Int => if -((37*K+36:Nat):Int)≤p then x p else false
  obtain ⟨right,hit⟩ := realize (fun _ => false) clock
  have eq (t : Nat) (ht : t≤37*K+36) : trace y t=clock t := by
    apply Eq.trans _ (hit t)
    apply Rule30LightCone.evol_window
    intro p lo _
    exact ite_eq_left (show -((37*K+36:Nat):Int)≤p by omega)
  refine ⟨y,?_,eq,fun k hk => same_gap (fun t ht => (eq _ (by omega)).trans (phase_prefix k t ht))⟩
  intro p h
  rcases h with h|h
  · exact ite_eq_right (show ¬-((37*K+36:Nat):Int)≤p by omega)
  · simp [y,x,right p (by omega)]

/-- With a fixed positive half, the center through H uniquely determines
each initial cell from -H to zero. The statement is finite in both time
and the amount of right-half agreement used. -/
theorem forced_prefix {x y : Int → Bool} (H : Nat)
    (right : ∀ p : Int, 0<p → p≤H → y p=x p)
    (hit : ∀ t, t≤H → trace y t=trace x t) :
    ∀ d, d≤H → y (-(d:Int))=x (-(d:Int)) := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro hd
    apply Classical.byContradiction
    intro bad
    have flip : y (-(d:Int))= !x (-(d:Int)) := by
      cases a : y (-(d:Int)) <;> cases b : x (-(d:Int)) <;> simp_all
    have diff := Rule30LightCone.center_flip_leftmost d (x:=x) (x':=y) (by
      intro p lo hi
      by_cases pos : 0<p
      · exact right p pos (by omega)
      · have inner := ih (-p).toNat (by omega) (by omega)
        simpa only [show -(((-p).toNat:Nat):Int)=p by omega] using inner) flip
    change trace y d= !trace x d at diff
    rw [hit d hd] at diff
    cases e : trace x d <;> simp [e] at diff

/-- Any prescribed seed prefix, in both space and time, can precede the
periodic gap. Only the initial sites strictly left of -N may change. -/
theorem after_singleton_prefix (N : Nat) : ∃ x : Int → Bool,
    (∀ p : Int, -(N:Int)≤p → x p=seed p) ∧
    (∀ t, t≤N → trace x t=cell t 0) ∧
    (∀ t, trace x (N+1+t)=clock t) ∧
    ∀ k, PhysicalExit (fun t => trace x (N+1+(k*37+t))) 3 ∧
      FirstFailure (fun t => trace x (N+1+(k*37+t))) 35 := by
  let c := fun t => if t≤N then cell t 0 else clock (t-(N+1))
  let x := conf seed c
  obtain ⟨right,hit⟩ := realize seed c
  have early (t : Nat) (ht : t≤N) : trace x t=cell t 0 := (hit t).trans (ite_eq_left ht)
  have late (t : Nat) : trace x (N+1+t)=clock t := by
    change evol (conf seed c) (N+1+t) 0=clock t
    rw [hit]; simp [c,show ¬N+1+t≤N by omega]
  refine ⟨x,?_,early,late,fun k => same_gap (fun t ht => (late _).trans (phase_prefix k t ht))⟩
  intro p hp
  by_cases pos : 0<p
  · exact right p (by omega)
  · have eq := forced_prefix (x:=seed) (y:=x) N (fun q hq _ => right q (by omega))
      (fun t ht => (early t ht).trans (evol_seed t 0).symm) (-p).toNat (by omega)
    simpa only [show -(((-p).toNat:Nat):Int)=p by omega] using eq

/-- The exact radius obstruction. All finite prefixes can be reproduced
with a uniform radius iff the unique infinite reconstruction has that radius. -/
theorem uniform_radius_iff (c : Nat → Bool) (R : Nat) :
    (∀ H, ∃ y : Int → Bool, (∀ p : Int, p < -(R:Int) ∨ 0<p → y p=false) ∧
      ∀ t, t≤H → trace y t=c t) ↔
    (∀ d, R<d → conf (fun _ => false) c (-(d:Int))=false) := by
  let x := conf (fun _ => false) c
  obtain ⟨blank,clocked⟩ := realize (fun _ => false) c
  constructor
  · intro allH d hd
    obtain ⟨y,support,matchH⟩ := allH d
    have eq := forced_prefix (x:=x) (y:=y) d (fun p hp _ =>
      (support p (Or.inr hp)).trans (blank p (by omega)).symm)
      (fun t ht => (matchH t ht).trans (clocked t).symm) d (by omega)
    exact eq.symm.trans (support _ (Or.inl (by omega)))
  · intro left H
    refine ⟨x,?_,fun t _ => clocked t⟩
    intro p hp
    rcases hp with hp|hp
    · have e := left (-p).toNat (by omega)
      simpa only [show -(((-p).toNat:Nat):Int)=p by omega] using e
    · exact blank p (by omega)

/-- Both rules expose their right input on exactly the white center ticks.
Rule 30 differs by a single XOR with the current center. -/
theorem same_mask (l c r : Bool) : rule l c r = xor c (xor l (g210 c r)) := by
  cases l <;> cases c <;> cases r <;> decide

/-- If the center is white and its right neighbor black, the *next*
right neighbor is forced in both rules, with opposite colors. -/
theorem white_neighbor (far : Bool) : rule false true far=true ∧
    xor false (g210 true far)=false := by cases far <;> decide

/-- All forward center shifts vanish on the first visible tick of Rule 210;
the actual right neighbor is black there. Includes the empty XOR. -/
theorem forward_xor_fails (offsets : List Nat) :
    run g210 1 0=false ∧ run g210 1 1=true ∧
    offsets.foldr (fun s b => xor (run g210 (s+1) 0) b) false=false := by
  refine ⟨center210 0,rfl,?_⟩
  induction offsets with
  | nil => rfl
  | cons s _ ih => rw [List.foldr_cons,ih,center210]; rfl

end Ruliology.CellularAutomata.Rule30PeriodicGapControl
