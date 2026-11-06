module

public import Ruliology.CellularAutomata.Rule30TraceEdge

/-!
# Divided-difference observers: gauges, a frontier, and a physicality barrier

For fixed actual Rule30 backgrounds A,B, their XOR satisfies the linear rule
`h' = left XOR ((NOT B_right) AND center) XOR ((NOT A_center) AND right)`.
Redistributing the quadratic term gives a local Boolean gauge. The universal
`Front.actual_difference` theorem verifies this for every pair, gauge and time.
The universal
`curvature` identity records the error in treating A XOR h as a new physical
configuration; the error is `h_center AND (delta_right XOR h_right)`.

The counterexample uses A(p)=[p mod3=1] and B(p)=[p mod3=2]. They merge to all
black after one step and vacuum after two. For every k>=1, the auxiliary
initial mode has four black cells at -3k-2,-3k-1,3k+1,3k+2. It is initially
supported inside A XOR B, but its observation at column1 is white for EVERY
time and EVERY local gauge (`unobservable`, `initial_subset`, `H_any_gauge`).
After two steps this is an additive Rule150 reflection mode. Actual nonlinear
recombination disagrees: the k=1 recombined center is black at time7 while
the linear mode stays white (`actual_center_diverges`).

`ObserverCriterion` states the open auxiliary-field route precisely: for
finite backgrounds, a finite initially supported common mode with its left
edge at the common lower bound must be seen at every observation column.
`edgeObservable_of_observerCriterion` proves that this criterion implies
the kit's `Rule30TraceEdge.EdgeObservable`; the actual pair difference is
an admissible common mode whenever the two finite backgrounds have unequal
left edges. `problem1_of_observerCriterion` supplies the prize implication.

The barrier backgrounds have NO left bound (`backgrounds_no_left_bound`).
Their finite initial modes satisfy the subset and common-field conditions
but fail `ModeObservable` (`barrier_mode_not_observable`). Thus removing the
background restrictions admits the existing all-gauge barrier.
`Front.mode_left_edge` retains a hypothesis the counterexample lacks: if
both actual backgrounds vanish below lo and the initial mode has left edge
lo, that mode keeps its left edge lo-t for every time and every local gauge.
It does not assert that this edge must affect the observation column.

All proofs are core Lean; no Mathlib or finite-horizon premise. The Boolean
identities and two concrete divergence controls use `decide +kernel`.
-/

@[expose] public section
namespace Ruliology.CellularAutomata.Rule30DividedDifference
open Ruliology.CellularAutomata Rule30Jen Rule30Realization

def A (p : Int) : Bool := decide (p % 3 = 1)
def B (p : Int) : Bool := decide (p % 3 = 2)

def mix (c r l x y : Bool) : Bool := xor (xor l (c && x)) (r && y)

theorem mix_add : ∀ c r l x y l' x' y' : Bool,
    mix c r (xor l l') (xor x x') (xor y y') =
      xor (mix c r l x y) (mix c r l' x' y') := by decide +kernel

theorem pair_difference_gauged : ∀ g a b c d e f : Bool,
    mix (xor (!f) (g && xor c f)) (xor (!b) (g && xor b e))
      (xor a d) (xor b e) (xor c f)=xor (rule a b c) (rule d e f) := by decide +kernel

theorem curvature : ∀ a b c f l x y : Bool,
    xor (xor (rule (xor a l) (xor b x) (xor c y)) (rule a b c))
      (mix (!f) (!b) l x y) = (x && xor (xor c f) y) := by decide +kernel

theorem phase_periodic (n p : Int) : A (p-3*n)=A p ∧ B (p-3*n)=B p := by
  have hm : (p-3*n)%3=p%3 := by omega
  simp [A,B,hm]

theorem backgrounds_one (p : Int) : evol A 1 p=true ∧ evol B 1 p=true := by
  have hm : p%3=0 ∨ p%3=1 ∨ p%3=2 := by omega
  rcases hm with hm|hm|hm <;>
    simp [evol,A,B,rule,show (p-1)%3=(p%3+2)%3 by omega,
      show (p+1)%3=(p%3+1)%3 by omega,hm]

theorem backgrounds_vacuum : ∀ (t : Nat) (p : Int),
    evol A (t+2) p=false ∧ evol B (t+2) p=false
  | 0,p => by
      change rule (evol A 1 (p-1)) (evol A 1 p) (evol A 1 (p+1))=false ∧
        rule (evol B 1 (p-1)) (evol B 1 p) (evol B 1 (p+1))=false
      rw [(backgrounds_one _).1,(backgrounds_one _).1,(backgrounds_one _).1,
        (backgrounds_one _).2,(backgrounds_one _).2,(backgrounds_one _).2]
      exact ⟨rfl,rfl⟩
  | t+1,p => by
      change rule (evol A (t+2) (p-1)) (evol A (t+2) p) (evol A (t+2) (p+1))=false ∧
        rule (evol B (t+2) (p-1)) (evol B (t+2) p) (evol B (t+2) (p+1))=false
      rw [(backgrounds_vacuum t _).1,(backgrounds_vacuum t _).1,(backgrounds_vacuum t _).1,
        (backgrounds_vacuum t _).2,(backgrounds_vacuum t _).2,(backgrounds_vacuum t _).2]
      exact ⟨rfl,rfl⟩

def lin (t : Nat) (h : Int → Bool) (p : Int) : Bool :=
  mix (!(evol B t (p+1))) (!(evol A t p)) (h (p-1)) (h p) (h (p+1))

theorem lin_add (t : Nat) (h g : Int → Bool) (p : Int) :
    lin t (fun q => xor (h q) (g q)) p=xor (lin t h p) (lin t g p) :=
  mix_add _ _ _ _ _ _ _ _

def shifted (d : Int) (h : Int → Bool) (p : Int) : Bool := h (p-d)
def run0 (p : Int) : Bool := decide (p=1 ∨ p=2)
def image0 (p : Int) : Bool := decide (p=0 ∨ p=3)
def run (n : Int) := shifted (3*n) run0
def image (n : Int) := shifted (3*n) image0

theorem run0_step (p : Int) : lin 0 run0 p=image0 p := by
  by_cases hp : 0≤p ∧ p≤3
  · obtain rfl|rfl|rfl|rfl : p=0 ∨ p=1 ∨ p=2 ∨ p=3 := by omega
    all_goals decide +kernel
  · have h0 : p≠0 := by omega
    have h3 : p≠3 := by omega
    have hleft : p-1≠1 ∧ p-1≠2 := by omega
    have hcenter : p≠1 ∧ p≠2 := by omega
    have hright : p+1≠1 ∧ p+1≠2 := by omega
    simp [lin,mix,run0,image0,h0,h3,hleft,hcenter,hright]

theorem lin_shift (n : Int) (h : Int → Bool) (p : Int) :
    lin 0 (shifted (3*n) h) p=shifted (3*n) (lin 0 h) p := by
  simp only [lin,shifted,evol]
  rw [show p-3*n+1=(p+1)-3*n by omega,
      show p-1-3*n=p-3*n-1 by omega]
  rw [(phase_periodic n (p+1)).2,(phase_periodic n p).1]

theorem run_step (n p : Int) : lin 0 (run n) p=image n p := by
  rw [run,lin_shift]
  exact run0_step (p-3*n)

theorem run0_wedge (p : Int) :
    xor (xor (A (p+1)) (B (p+1)) && run0 p)
      (xor (A p) (B p) && run0 (p+1))=false := by
  by_cases hp : 0≤p ∧ p≤2
  · obtain rfl|rfl|rfl : p=0 ∨ p=1 ∨ p=2 := by omega
    all_goals decide +kernel
  · have hp0 : p≠1 ∧ p≠2 := by omega
    have hp1 : p+1≠1 ∧ p+1≠2 := by omega
    simp [run0,hp0,hp1]

theorem run_wedge (n p : Int) :
    xor (xor (A (p+1)) (B (p+1)) && run n p)
      (xor (A p) (B p) && run n (p+1))=false := by
  have hh:=run0_wedge (p-3*n)
  rw [show p-3*n+1=(p+1)-3*n by omega] at hh
  rw [(phase_periodic n (p+1)).1,(phase_periodic n (p+1)).2,
    (phase_periodic n p).1,(phase_periodic n p).2] at hh
  exact hh

def h0 (k : Int) (p : Int) := xor (run (-k-1) p) (run k p)
def h1 (k : Int) (p : Int) := xor (image (-k-1) p) (image k p)
def h2 (k : Int) (p : Int) := h1 k (p-1)

def addEvol (x : Int → Bool) : Nat → Int → Bool
  | 0,p => x p
  | t+1,p => xor (xor (addEvol x t (p-1)) (addEvol x t p)) (addEvol x t (p+1))

theorem add_reflect {x : Int → Bool} (hx : ∀ p, x (2-p)=x p) :
    ∀ (t : Nat) (p : Int), addEvol x t (2-p)=addEvol x t p
  | 0,p => hx p
  | t+1,p => by
      simp only [addEvol,show 2-p-1=2-(p+1) by omega,
        show 2-p+1=2-(p-1) by omega,add_reflect hx t]
      cases addEvol x t (p-1) <;> cases addEvol x t p <;>
        cases addEvol x t (p+1) <;> rfl

theorem add_center {x : Int → Bool} (hx : ∀ p, x (2-p)=x p) (hcenter : x 1=false) :
    ∀ t, addEvol x t 1=false
  | 0 => hcenter
  | t+1 => by
      have hs := add_reflect hx t 0
      change addEvol x t 2=addEvol x t 0 at hs
      simp only [addEvol,show (1:Int)-1=0 by omega,show (1:Int)+1=2 by omega,
        add_center hx hcenter t,hs]
      cases addEvol x t 0 <;> rfl

theorem image_reflect (n p : Int) : image (-n-1) (-p)=image n p := by
  have h0 : -p-3*(-n-1)=0 ↔ p-3*n=3 := by omega
  have h3 : -p-3*(-n-1)=3 ↔ p-3*n=0 := by omega
  simp only [image,shifted,image0,h0,h3,or_comm]

theorem h1_reflect (k p : Int) : h1 k (-p)=h1 k p := by
  have hl := image_reflect k p
  have hr := image_reflect (-k-1) p
  rw [show -(-k-1)-1=k by omega] at hr
  simp only [h1,hl,hr,Bool.xor_comm]

theorem h2_reflect (k p : Int) : h2 k (2-p)=h2 k p := by
  unfold h2
  rw [show 2-p-1=-(p-1) by omega,h1_reflect]

theorem h2_center (k : Int) (hk : 1≤k) : h2 k 1=false := by
  have hl : image (-k-1) 0=false := by
    change decide (0-3*(-k-1)=0 ∨ 0-3*(-k-1)=3)=false
    apply decide_eq_false_iff_not.mpr
    omega
  have hr : image k 0=false := by
    change decide (0-3*k=0 ∨ 0-3*k=3)=false
    apply decide_eq_false_iff_not.mpr
    omega
  change xor (image (-k-1) 0) (image k 0)=false
  rw [hl,hr]
  rfl

def H (k : Int) : Nat → Int → Bool
  | 0 => h0 k
  | 1 => h1 k
  | t+2 => addEvol (h2 k) t

theorem H_step (k : Int) : ∀ (t : Nat) (p : Int), H k (t+1) p=lin t (H k t) p
  | 0,p => by
      change xor (image (-k-1) p) (image k p)=
        lin 0 (fun q => xor (run (-k-1) q) (run k q)) p
      rw [lin_add,run_step,run_step]
  | 1,p => by
      simp only [H,lin,(backgrounds_one _).1,(backgrounds_one _).2,
        Bool.not_true,Bool.false_and,mix,Bool.xor_false,addEvol,h2]
  | t+2,p => by
      simp only [H,lin,(backgrounds_vacuum t _).1,(backgrounds_vacuum t _).2,
        Bool.not_false,Bool.true_and,mix,addEvol]

theorem H_center (k : Int) (hk : 1≤k) : ∀ t, H k t 1=false
  | 0 => by
      have hl : 1-3*(-k-1)≠1 ∧ 1-3*(-k-1)≠2 := by omega
      have hr : 1-3*k≠1 ∧ 1-3*k≠2 := by omega
      simp [H,h0,run,shifted,run0,hl,hr]
  | 1 => by
      have hl : 1-3*(-k-1)≠0 ∧ 1-3*(-k-1)≠3 := by omega
      have hr : 1-3*k≠0 ∧ 1-3*k≠3 := by omega
      simp [H,h1,image,shifted,image0,hl,hr]
  | t+2 => add_center (h2_reflect k) (h2_center k hk) t

def delta (t : Nat) (p : Int) := xor (evol A t p) (evol B t p)
def wedge (t : Nat) (h : Int → Bool) (p : Int) :=
  xor (delta t (p+1) && h p) (delta t p && h (p+1))

theorem wedge_add : ∀ a b x y x' y' : Bool,
    xor (a && xor x x') (b && xor y y') =
      xor (xor (a && x) (b && y)) (xor (a && x') (b && y')) := by decide +kernel

theorem H_wedge (k : Int) : ∀ (t : Nat) (p : Int), wedge t (H k t) p=false
  | 0,p => by
      simp only [wedge,delta,evol,H,h0,wedge_add,run_wedge,Bool.false_xor]
  | 1,p => by
      simp [wedge,delta,(backgrounds_one _).1,(backgrounds_one _).2]
  | t+2,p => by
      simp [wedge,delta,(backgrounds_vacuum t _).1,(backgrounds_vacuum t _).2]

def gauged (g : Nat → Int → Bool) (t : Nat) (h : Int → Bool) (p : Int) :=
  mix (xor (!(evol B t (p+1))) (g t p && delta t (p+1)))
      (xor (!(evol A t p)) (g t p && delta t p)) (h (p-1)) (h p) (h (p+1))

theorem gauge_identity : ∀ c r g a b l x y : Bool,
    mix (xor c (g && a)) (xor r (g && b)) l x y =
      xor (mix c r l x y) (g && xor (a && x) (b && y)) := by decide +kernel

theorem H_any_gauge (g : Nat → Int → Bool) (k : Int) (t : Nat) (p : Int) :
    gauged g t (H k t) p=H k (t+1) p := by
  rw [gauged,gauge_identity]
  change xor (lin t (H k t) p) (g t p && wedge t (H k t) p)=_
  rw [H_wedge,Bool.and_false,Bool.xor_false,H_step]

def gaugeEvol (g : Nat → Int → Bool) (x : Int → Bool) : Nat → Int → Bool
  | 0,p => x p
  | t+1,p => gauged g t (gaugeEvol g x t) p

theorem gaugeEvol_eq (g : Nat → Int → Bool) (k : Int) :
    ∀ t, gaugeEvol g (h0 k) t=H k t
  | 0 => rfl
  | t+1 => by
      funext p
      simp only [gaugeEvol,gaugeEvol_eq g k t,H_any_gauge]

theorem finite_mode (k : Int) (hk : 1≤k) : Rule30PeriodTwoSideways.FinConfig (h0 k) := by
  refine ⟨(3*k+2).toNat,?_⟩
  intro p hp
  have hl : p-3*(-k-1)≠1 ∧ p-3*(-k-1)≠2 := by omega
  have hr : p-3*k≠1 ∧ p-3*k≠2 := by omega
  simp [h0,run,shifted,run0,hl,hr]

theorem source_bit (k : Int) (hk : 1≤k) :
    h0 k (-3*k-2)=true ∧ A (-3*k-2)=true ∧ B (-3*k-2)=false := by
  have hm : (-3*k-2)%3=1 := by omega
  have hl : -3*k-2-3*(-k-1)=1 := by omega
  have hr : -3*k-2-3*k≠1 ∧ -3*k-2-3*k≠2 := by omega
  simp [h0,run,shifted,run0,A,B,hm,hl,hr]

theorem run_subset (n p : Int) (hp : run n p=true) : xor (A p) (B p)=true := by
  change decide (p-3*n=1 ∨ p-3*n=2)=true at hp
  simp only [decide_eq_true_eq] at hp
  rcases hp with hp|hp
  · have hm : p%3=1 := by omega
    simp [A,B,hm]
  · have hm : p%3=2 := by omega
    simp [A,B,hm]

theorem initial_subset (k p : Int) (hp : h0 k p=true) : delta 0 p=true := by
  by_cases hl : run (-k-1) p=true
  · exact run_subset (-k-1) p hl
  · have hr : run k p=true := by
      cases hleft : run (-k-1) p <;> cases hright : run k p <;> simp_all [h0]
    exact run_subset k p hr

theorem source_left (k : Int) (hk : 1≤k) (p : Int) (hp : p < -3*k-2) : h0 k p=false := by
  have hl : p-3*(-k-1)≠1 ∧ p-3*(-k-1)≠2 := by omega
  have hr : p-3*k≠1 ∧ p-3*k≠2 := by omega
  simp [h0,run,shifted,run0,hl,hr]

theorem backgrounds_no_left_bound (lo : Int) :
    (∃ p, p<lo ∧ A p=true) ∧ (∃ p, p<lo ∧ B p=true) := by
  constructor
  · refine ⟨lo-lo%3-2,by omega,?_⟩
    have hm : (lo-lo%3-2)%3=1 := by omega
    simp [A,hm]
  · refine ⟨lo-lo%3-1,by omega,?_⟩
    have hm : (lo-lo%3-1)%3=2 := by omega
    simp [B,hm]

/-- Uniform in the source separation, all times and every local gauge.
The backgrounds are infinite initially. -/
theorem unobservable (g : Nat → Int → Bool) (k : Int) (hk : 1≤k) :
    Rule30PeriodTwoSideways.FinConfig (h0 k) ∧ h0 k (-3*k-2)=true ∧
      ∀ t, gaugeEvol g (h0 k) t 1=false := by
  refine ⟨finite_mode k hk,(source_bit k hk).1,?_⟩
  intro t
  rw [gaugeEvol_eq]
  exact H_center k hk t

theorem recombination_is_not_physical :
    evol (fun p => xor (A p) (h0 1 p)) 4 (-5) ≠ xor (evol A 4 (-5)) (H 1 4 (-5)) := by
  decide +kernel

theorem actual_center_diverges :
    evol (fun p => xor (A p) (h0 1 p)) 7 1=true ∧ H 1 7 1=false := by
  decide +kernel

/-! The finite/left-bounded problem has an additional frontier that the
periodic-background examples above lack. Preserve this in future arguments.
The coefficients and gauges here use arbitrary actual Rule30 backgrounds. -/
namespace Front

def step (a b : Int → Bool) (g : Nat → Int → Bool) (t : Nat) (x : Int → Bool) (p : Int) :=
  mix (xor (!(evol b t (p+1))) (g t p && xor (evol a t (p+1)) (evol b t (p+1))))
      (xor (!(evol a t p)) (g t p && xor (evol a t p) (evol b t p)))
      (x (p-1)) (x p) (x (p+1))

def mode (a b : Int → Bool) (g : Nat → Int → Bool) (x : Int → Bool) : Nat → Int → Bool
  | 0,p => x p
  | t+1,p => step a b g t (mode a b g x t) p

/-- Every gauge still represents the actual nonlinear pair difference. -/
theorem actual_difference (a b : Int → Bool) (g : Nat → Int → Bool) :
    ∀ (t : Nat) (p : Int), mode a b g (fun q => xor (a q) (b q)) t p=
      xor (evol a t p) (evol b t p)
  | 0,p => rfl
  | t+1,p => by
      simp only [mode,step,actual_difference a b g t]
      exact pair_difference_gauged _ _ _ _ _ _ _

/-- The mode keeps the actual farther-left edge, for EVERY local gauge.
Only left bounds of the actual backgrounds are needed for this assertion;
it does not assert that this frontier must reach the observation column. -/
theorem mode_left_edge (a b x : Int → Bool) (g : Nat → Int → Bool) (lo : Int)
    (ha : ∀ p, p<lo → a p=false) (hb : ∀ p, p<lo → b p=false)
    (hx : x lo=true) (hzero : ∀ p, p<lo → x p=false) :
    ∀ t : Nat, mode a b g x t (lo-t)=true ∧
      ∀ p, p<lo-t → mode a b g x t p=false
  | 0 => by simpa [mode] using (And.intro hx hzero)
  | t+1 => by
      have ih := mode_left_edge a b x g lo ha hb hx hzero t
      constructor
      · let q : Int := lo-(t+1 : Nat)
        have hleft : mode a b g x t (q-1)=false := ih.2 _ (by dsimp [q]; omega)
        have hcenter : mode a b g x t q=false := ih.2 _ (by dsimp [q]; omega)
        have hright : mode a b g x t (q+1)=true := by
          rw [show q+1=lo-(t:Int) by dsimp [q]; omega]
          exact ih.1
        have haw : evol a t q=false :=
          Rule30FiniteConfigs.evol_eq_false_of_lt ha t q (by dsimp [q]; omega)
        have hbw : evol b t q=false :=
          Rule30FiniteConfigs.evol_eq_false_of_lt hb t q (by dsimp [q]; omega)
        change step a b g t (mode a b g x t) q=true
        simp [step,mix,hleft,hcenter,hright,haw,hbw]
      · intro p hp
        change step a b g t (mode a b g x t) p=false
        have hleft := ih.2 (p-1) (by omega)
        have hcenter := ih.2 p (by omega)
        have hright := ih.2 (p+1) (by omega)
        simp [step,mix,hleft,hcenter,hright]

end Front

open Ruliology.CellularAutomata.Rule30PeriodTwoSideways (FinConfig)
open Ruliology.CellularAutomata.Rule30TraceEdge (HasLeftEdge EdgeObservable)
set_option autoImplicit false

/-- The fixed zero gauge; a common field is independent of the gauge choice. -/
def zeroGauge (_ : Nat) (_ : Int) : Bool := false

/-- Vanishing gauge curvature along the complete auxiliary history. -/
def CommonField (a b : Int → Bool) (h : Nat → Int → Bool) : Prop :=
  ∀ t p, xor
    (xor (evol a t (p+1)) (evol b t (p+1)) && h t p)
    (xor (evol a t p) (evol b t p) && h t (p+1))=false

/-- Observation at every fixed physical column, not at a moving edge. -/
def ModeObservable (a b x : Int → Bool) : Prop :=
  ∀ p, ∃ t, Front.mode a b zeroGauge x t p=true

/-- Open sufficient criterion. The auxiliary mode is not assumed physical.
Only initial subset is required; CommonField is required for all time.
Both backgrounds vanish below the initial mode's left edge. -/
def ObserverCriterion : Prop :=
  ∀ (a b x : Int → Bool), FinConfig a → FinConfig b → FinConfig x →
    ∀ lo, HasLeftEdge x lo →
      (∀ p, p<lo → a p=false) → (∀ p, p<lo → b p=false) →
      (∀ p, x p=true → xor (a p) (b p)=true) →
      CommonField a b (Front.mode a b zeroGauge x) → ModeObservable a b x

theorem actual_difference_common (a b : Int → Bool) :
    CommonField a b (Front.mode a b zeroGauge (fun p => xor (a p) (b p))) := by
  intro t p
  rw [Front.actual_difference,Front.actual_difference]
  simp only [Bool.and_comm,Bool.xor_self]

/-- The criterion gives the precise existing global observer target. -/
theorem edgeObservable_of_observerCriterion (hc : ObserverCriterion) : EdgeObservable := by
  have no_lt : ∀ (a b : Int → Bool) (u v : Int),
      FinConfig a → FinConfig b → HasLeftEdge a u → HasLeftEdge b v → u<v →
      (∀ t, evol a t 0=evol b t 0) → False := by
    intro a b u v hfa hfb ha hb huv heq
    let x : Int → Bool := fun p => xor (a p) (b p)
    have hfx : FinConfig x := by
      obtain ⟨M,hM⟩ := hfa
      obtain ⟨N,hN⟩ := hfb
      refine ⟨M+N,?_⟩
      intro p hp
      simp only [x,hM p (by omega),hN p (by omega),Bool.xor_self]
    have hleft : HasLeftEdge x u := by
      constructor
      · simp only [x,ha.1,hb.2 u huv,Bool.true_xor,Bool.not_false]
      · intro p hp
        simp only [x,ha.2 p hp,hb.2 p (by omega),Bool.xor_self]
    have hobs := hc a b x hfa hfb hfx u hleft ha.2
      (fun p hp => hb.2 p (by omega)) (fun _ hp => hp)
      (actual_difference_common a b) 0
    obtain ⟨t,ht⟩ := hobs
    change Front.mode a b zeroGauge (fun p => xor (a p) (b p)) t 0=true at ht
    rw [Front.actual_difference,heq t,Bool.xor_self] at ht
    cases ht
  intro a b hfa hfb u v ha hb heq
  rcases Int.lt_trichotomy u v with huv|huv|huv
  · exact False.elim (no_lt a b u v hfa hfb ha hb huv heq)
  · exact huv
  · exact False.elim (no_lt b a v u hfb hfa hb ha huv (fun t => (heq t).symm))

/-- Conditional implication to the exact official Problem 1. -/
theorem problem1_of_observerCriterion (hc : ObserverCriterion) : Rule30Prize.Problem1 :=
  Rule30TraceEdge.problem1_of_edgeObservable (edgeObservable_of_observerCriterion hc)

theorem barrier_front_mode_eq (g : Nat → Int → Bool) (k : Int) :
    ∀ t p, Front.mode A B g (h0 k) t p=gaugeEvol g (h0 k) t p := by
  intro t
  induction t with
  | zero => intro p;rfl
  | succ t ih =>
    intro p
    simp only [Front.mode,Front.step,gaugeEvol,gauged,delta,ih]

theorem barrier_common_field (k : Int) :
    CommonField A B (Front.mode A B zeroGauge (h0 k)) := by
  intro t p
  simp only [barrier_front_mode_eq,gaugeEvol_eq]
  exact H_wedge k t p

/-- The finite mode meets the initial subset and all-time common-field
conditions, but the unbounded backgrounds prevent using ObserverCriterion. -/
theorem barrier_mode_not_observable (k : Int) (hk : 1≤k) :
    FinConfig (h0 k) ∧ HasLeftEdge (h0 k) (-3*k-2) ∧
    (∀ p, h0 k p=true → xor (A p) (B p)=true) ∧
    CommonField A B (Front.mode A B zeroGauge (h0 k)) ∧
    ¬ModeObservable A B (h0 k) := by
  refine ⟨finite_mode k hk,⟨(source_bit k hk).1,source_left k hk⟩,
    (fun p hp => initial_subset k p hp),barrier_common_field k,?_⟩
  intro hobs
  obtain ⟨t,ht⟩ := hobs 1
  rw [barrier_front_mode_eq,gaugeEvol_eq,H_center k hk] at ht
  cases ht

/-! ### Universal Gauge Invariance of Common Modes, Left-of-Edge Observability, and Column-0 Observer Reduction -/

/-- One-step gauge independence when the wedge term vanishes (`Front.step_eq_zeroGauge_of_wedge_false`):
if the wedge term between `a, b` and `h` vanishes at `(t, p)`, then `Front.step a b g t h p`
equals `Front.step a b zeroGauge t h p` for every gauge `g`. -/
theorem Front.step_eq_zeroGauge_of_wedge_false (a b : Int → Bool) (g : Nat → Int → Bool)
    (t : Nat) (h : Int → Bool) (p : Int)
    (hw : xor (xor (evol a t (p + 1)) (evol b t (p + 1)) && h p)
              (xor (evol a t p) (evol b t p) && h (p + 1)) = false) :
    Front.step a b g t h p = Front.step a b zeroGauge t h p := by
  unfold Front.step zeroGauge
  rw [gauge_identity]
  simp [hw]

/-- **Universal Gauge Invariance of Common Modes (`Front.mode_eq_zeroGauge_of_commonField`):**
for any backgrounds `a, b`, initial mode `x`, and local gauge `g`, if `Front.mode a b zeroGauge x`
satisfies `CommonField a b`, then `Front.mode a b g x t p = Front.mode a b zeroGauge x t p` at
every time `t` and column `p`. -/
theorem Front.mode_eq_zeroGauge_of_commonField {a b x : Int → Bool} (g : Nat → Int → Bool)
    (hc : CommonField a b (Front.mode a b zeroGauge x)) :
    ∀ (t : Nat) (p : Int), Front.mode a b g x t p = Front.mode a b zeroGauge x t p
  | 0, p => rfl
  | t + 1, p => by
    show Front.step a b g t (Front.mode a b g x t) p =
      Front.step a b zeroGauge t (Front.mode a b zeroGauge x t) p
    have heq : Front.mode a b g x t = Front.mode a b zeroGauge x t :=
      funext (Front.mode_eq_zeroGauge_of_commonField g hc t)
    rw [heq]
    exact Front.step_eq_zeroGauge_of_wedge_false a b g t (Front.mode a b zeroGauge x t) p (hc t p)

/-- **Gauge Invariance of `CommonField` (`commonField_any_gauge_iff`):** if `Front.mode a b zeroGauge x`
satisfies `CommonField a b`, then `Front.mode a b g x` also satisfies `CommonField a b` for every
local gauge `g`. -/
theorem commonField_of_zeroGauge {a b x : Int → Bool} (g : Nat → Int → Bool)
    (hc : CommonField a b (Front.mode a b zeroGauge x)) :
    CommonField a b (Front.mode a b g x) := by
  intro t p
  rw [Front.mode_eq_zeroGauge_of_commonField g hc t p,
      Front.mode_eq_zeroGauge_of_commonField g hc t (p + 1)]
  exact hc t p

/-- **Unconditional Observability at All Columns on or Left of the Initial Edge
(`Front.mode_observable_of_le_edge`):** if `a` and `b` vanish below `lo` and `HasLeftEdge x lo`,
then for every gauge `g` and every column `p ≤ lo`, `Front.mode a b g x (lo - p).toNat p = true`. -/
theorem Front.mode_observable_of_le_edge {a b x : Int → Bool} (g : Nat → Int → Bool) {lo p : Int}
    (ha : ∀ q, q < lo → a q = false) (hb : ∀ q, q < lo → b q = false)
    (hx : HasLeftEdge x lo) (hp : p ≤ lo) :
    Front.mode a b g x (lo - p).toNat p = true := by
  have he := (Front.mode_left_edge a b x g lo ha hb hx.1 hx.2 (lo - p).toNat).1
  rwa [show lo - ((lo - p).toNat : Int) = p by omega] at he

/-- **Reduction of `ModeObservable` to Columns Strictly Right of the Left Edge
(`modeObservable_of_gt_edge`):** if `a` and `b` vanish below `lo` and `HasLeftEdge x lo`, then
`ModeObservable a b x` holds as soon as every column `p > lo` is reached at some time `t`. -/
theorem modeObservable_of_gt_edge {a b x : Int → Bool} {lo : Int}
    (ha : ∀ q, q < lo → a q = false) (hb : ∀ q, q < lo → b q = false)
    (hx : HasLeftEdge x lo)
    (hgt : ∀ p, lo < p → ∃ t, Front.mode a b zeroGauge x t p = true) :
    ModeObservable a b x := by
  intro p
  by_cases hp : p ≤ lo
  · exact ⟨(lo - p).toNat, Front.mode_observable_of_le_edge zeroGauge ha hb hx hp⟩
  · exact hgt p (by omega)

/-- **Left Edge of the Actual Pair Difference (`hasLeftEdge_xor_of_lt`):** if `HasLeftEdge a u`
and `HasLeftEdge b v` with `u < v`, then `fun p => xor (a p) (b p)` has left edge `u`. -/
theorem hasLeftEdge_xor_of_lt {a b : Int → Bool} {u v : Int}
    (ha : HasLeftEdge a u) (hb : HasLeftEdge b v) (huv : u < v) :
    HasLeftEdge (fun p => xor (a p) (b p)) u := by
  refine ⟨?_, fun p hp => ?_⟩
  · simp only [ha.1, hb.2 u huv, Bool.true_xor, Bool.not_false]
  · simp only [ha.2 p hp, hb.2 p (by omega), Bool.xor_self]

/-! ### Canonical Seed Shift-Difference Modes and Bidirectional Divided-Difference Characterizations of `EdgeObservable` and `Problem1` -/

open Ruliology.CellularAutomata.Rule30TraceEdge
  (hasLeftEdge_evol_seed SeedTraceShiftFree problem1_iff_seedTraceShiftFree)

/-- **Canonical Seed Shift-Difference Mode (`seedDiffMode`):** initial XOR difference between
`evol seed (T + P)` and `evol seed T`. -/
def seedDiffMode (T P : Nat) (p : Int) : Bool :=
  xor (evol seed (T + P) p) (evol seed T p)

/-- **Exact Left Edge of `seedDiffMode` (`hasLeftEdge_seedDiffMode`):** for any `T P : Nat`
with `0 < P`, `HasLeftEdge (seedDiffMode T P) (-((T + P : Nat) : Int))`. -/
theorem hasLeftEdge_seedDiffMode (T : Nat) {P : Nat} (hP : 0 < P) :
    HasLeftEdge (seedDiffMode T P) (-((T + P : Nat) : Int)) :=
  hasLeftEdge_xor_of_lt (hasLeftEdge_evol_seed (T + P)) (hasLeftEdge_evol_seed T) (by omega)

/-- **All-Gauge Common-Field Property of `seedDiffMode` (`commonField_seedDiffMode`):** for any
`T P : Nat` and local gauge `g`, `Front.mode (evol seed (T + P)) (evol seed T) g (seedDiffMode T P)`
satisfies `CommonField (evol seed (T + P)) (evol seed T)`. -/
theorem commonField_seedDiffMode (T P : Nat) (g : Nat → Int → Bool) :
    CommonField (evol seed (T + P)) (evol seed T)
      (Front.mode (evol seed (T + P)) (evol seed T) g (seedDiffMode T P)) :=
  commonField_of_zeroGauge g (actual_difference_common (evol seed (T + P)) (evol seed T))

/-- **Unconditional Left-of-Edge Observability of `seedDiffMode`
(`seedDiffMode_observable_le_edge`):** for any `T P : Nat` with `0 < P`, local gauge `g`, and
column `p ≤ -((T + P : Nat) : Int)`,
`Front.mode (evol seed (T + P)) (evol seed T) g (seedDiffMode T P) (-((T + P : Nat) : Int) - p).toNat p = true`. -/
theorem seedDiffMode_observable_le_edge (T : Nat) {P : Nat} (hP : 0 < P)
    (g : Nat → Int → Bool) {p : Int} (hp : p ≤ -((T + P : Nat) : Int)) :
    Front.mode (evol seed (T + P)) (evol seed T) g (seedDiffMode T P)
      (-((T + P : Nat) : Int) - p).toNat p = true :=
  Front.mode_observable_of_le_edge g
    (hasLeftEdge_evol_seed (T + P)).2
    (fun q hq => (hasLeftEdge_evol_seed T).2 q (by omega))
    (hasLeftEdge_seedDiffMode T hP)
    hp

/-- **Exact Bidirectional Divided-Difference Characterization of `EdgeObservable`
(`edgeObservable_iff_pairDiff_center_observable`):** `EdgeObservable` holds if and only if for
every pair of finite configurations `a, b` with left edges `u < v`, their pair-difference mode
`Front.mode a b zeroGauge (fun p => xor (a p) (b p))` reaches `true` at column `0`. -/
theorem edgeObservable_iff_pairDiff_center_observable :
    EdgeObservable ↔
      (∀ (a b : Int → Bool) (u v : Int),
        FinConfig a → FinConfig b → HasLeftEdge a u → HasLeftEdge b v → u < v →
        ∃ t : Nat, Front.mode a b zeroGauge (fun p => xor (a p) (b p)) t 0 = true) := by
  constructor
  · intro hEO a b u v hfa hfb ha hb huv
    refine Classical.byContradiction fun hno => ?_
    have heq : ∀ t : Nat, evol a t 0 = evol b t 0 := by
      intro t
      have ht : Front.mode a b zeroGauge (fun p => xor (a p) (b p)) t 0 = false := by
        cases hbit : Front.mode a b zeroGauge (fun p => xor (a p) (b p)) t 0
        · rfl
        · exact False.elim (hno ⟨t, hbit⟩)
      rw [Front.actual_difference] at ht
      revert ht; cases evol a t 0 <;> cases evol b t 0 <;> decide
    have huv_eq := hEO a b hfa hfb u v ha hb heq
    omega
  · intro hpair a b hfa hfb u v ha hb heq
    rcases Int.lt_trichotomy u v with huv | huv | huv
    · obtain ⟨t, ht⟩ := hpair a b u v hfa hfb ha hb huv
      rw [Front.actual_difference, heq t, Bool.xor_self] at ht
      cases ht
    · exact huv
    · obtain ⟨t, ht⟩ := hpair b a v u hfb hfa hb ha huv
      rw [Front.actual_difference, (heq t).symm, Bool.xor_self] at ht
      cases ht

/-- **Exact Bidirectional Divided-Difference Characterization of `Problem1`
(`problem1_iff_seedDiffMode_center_observable`):** `Rule30Prize.Problem1` (**open**) holds if
and only if for every `T P : Nat` with `0 < P`, the canonical shift-difference mode
`seedDiffMode T P` reaches `true` at column `0` at some time `t : Nat`. -/
theorem problem1_iff_seedDiffMode_center_observable :
    Rule30Prize.Problem1 ↔
      (∀ T P : Nat, 0 < P →
        ∃ t : Nat,
          Front.mode (evol seed (T + P)) (evol seed T) zeroGauge (seedDiffMode T P) t 0 = true) := by
  rw [problem1_iff_seedTraceShiftFree]
  constructor
  · intro hS T P hP
    refine Classical.byContradiction fun hno => hS T P hP (fun t => ?_)
    have ht : Front.mode (evol seed (T + P)) (evol seed T) zeroGauge (seedDiffMode T P) t 0 = false := by
      cases hbit : Front.mode (evol seed (T + P)) (evol seed T) zeroGauge (seedDiffMode T P) t 0
      · rfl
      · exact False.elim (hno ⟨t, hbit⟩)
    unfold seedDiffMode at ht
    rw [Front.actual_difference] at ht
    revert ht
    cases evol (evol seed T) t 0 <;> cases evol (evol seed (T + P)) t 0 <;> decide
  · intro hobs T P hP heq
    obtain ⟨t, ht⟩ := hobs T P hP
    unfold seedDiffMode at ht
    rw [Front.actual_difference, (heq t).symm, Bool.xor_self] at ht
    cases ht

/-- **All-Gauge Divided-Difference Equivalence for `Problem1`
(`problem1_iff_seedDiffMode_any_gauge_center_observable`):** `Rule30Prize.Problem1` (**open**)
holds if and only if for every local gauge `g` and every `T P : Nat` with `0 < P`,
`Front.mode (evol seed (T + P)) (evol seed T) g (seedDiffMode T P)` reaches `true` at column `0`. -/
theorem problem1_iff_seedDiffMode_any_gauge_center_observable :
    Rule30Prize.Problem1 ↔
      (∀ (g : Nat → Int → Bool) (T P : Nat), 0 < P →
        ∃ t : Nat,
          Front.mode (evol seed (T + P)) (evol seed T) g (seedDiffMode T P) t 0 = true) := by
  rw [problem1_iff_seedDiffMode_center_observable]
  constructor
  · intro h0 g T P hP
    obtain ⟨t, ht⟩ := h0 T P hP
    refine ⟨t, ?_⟩
    unfold seedDiffMode at ht ⊢
    rw [Front.actual_difference] at ht ⊢
    exact ht
  · intro hg T P hP
    exact hg zeroGauge T P hP

end Ruliology.CellularAutomata.Rule30DividedDifference
