module
public import Ruliology.CellularAutomata.Rule30EdgeClock

/-!
# A black-clock budget forces four-layer defect escape

For arbitrary infinite codes with a common black edge and first difference
at j+1, a difference reaches j+5 or j+6 within7*(ceil(j/2)+1) ticks, from
every starting time. The bound is not claimed optimal.

An explicit Boolean rank on the six-digit relative window and its lower
clock is at most6, never increases during confinement, and drops whenever
that clock is black. Its transition inequality is kernel checked over all
Boolean assignments. The separate all-j quiet-clock theorem forces a
black tick in every ceil(j/2)+1 window. Seven such windows are impossible.

This is uniform in the absolute first-difference depth and all upper tails,
not an enumeration of larger absolute bands or temporal periods. It does
not prove escape for arbitrary band width or center nonperiodicity. The
rank is not an additive local charge and may stall on white clock ticks.
-/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30DefectClockBudget
open Rule30FrozenRuler Rule30EdgeClock

def rank (x0 x1 x2 x3 x4 _x5 d1 d2 d3 c h : Bool) : Nat :=
  (if c then (if h then (if d3 then (if d2 then (if d1 then (if x4 then (if x3 then (if x2 then 0 else (if x1 then 1 else (if x0 then 1 else 6))) else (if x2 then (if x1 then (if x0 then 6 else 1) else 1) else 0)) else 0) else (if x4 then (if x3 then (if x2 then 0 else (if x1 then 1 else (if x0 then 3 else 5))) else (if x2 then (if x1 then 1 else (if x0 then 5 else 3)) else 0)) else 0)) else (if x4 then (if x2 then 1 else 0) else 0)) else (if d2 then (if d1 then (if x4 then (if x3 then (if x2 then (if x1 then 1 else (if x0 then 1 else 2)) else (if x1 then (if x0 then 2 else 1) else 1)) else 0) else (if x3 then (if x2 then (if x1 then 1 else (if x0 then 1 else 3)) else (if x1 then (if x0 then 3 else 1) else 1)) else 0)) else (if x3 then 1 else 0)) else (if d1 then (if x4 then (if x3 then 1 else (if x2 then (if x1 then (if x0 then 1 else 2) else (if x0 then 2 else 1)) else 1)) else (if x3 then (if x2 then (if x1 then (if x0 then 1 else 2) else (if x0 then 2 else 1)) else 1) else 1)) else (if x3 then (if x2 then 1 else (if x1 then 4 else 1)) else (if x2 then (if x1 then 2 else 1) else 1))))) else (if d3 then (if d2 then (if d1 then (if x4 then (if x3 then (if x2 then 0 else (if x1 then 1 else (if x0 then 2 else 6))) else (if x2 then (if x1 then (if x0 then 6 else 2) else 1) else 0)) else 0) else (if x4 then (if x3 then (if x2 then 0 else (if x1 then 1 else (if x0 then 3 else 5))) else (if x2 then (if x1 then 1 else (if x0 then 5 else 3)) else 0)) else 0)) else (if x4 then (if x2 then 1 else 0) else 0)) else (if d2 then (if d1 then (if x3 then (if x2 then (if x1 then 1 else (if x0 then 1 else 3)) else (if x1 then (if x0 then 3 else 1) else 1)) else 0) else (if x4 then (if x3 then 1 else 0) else (if x3 then (if x2 then (if x1 then 1 else (if x0 then 1 else 2)) else (if x1 then 1 else (if x0 then 2 else 1))) else 0))) else (if d1 then (if x4 then (if x3 then (if x2 then (if x1 then (if x0 then 1 else 2) else (if x0 then 2 else 1)) else 1) else (if x2 then (if x1 then (if x0 then 2 else 3) else (if x0 then 3 else 2)) else (if x1 then (if x0 then 1 else 2) else (if x0 then 2 else 1)))) else (if x3 then (if x2 then (if x1 then (if x0 then 1 else 3) else (if x0 then 3 else 1)) else 2) else (if x2 then 2 else 1))) else (if x3 then (if x2 then (if x1 then 2 else 1) else (if x1 then 4 else 2)) else (if x2 then (if x1 then 3 else 2) else (if x1 then 2 else 1))))))) else (if h then (if d3 then (if d2 then (if d1 then (if x4 then (if x3 then (if x2 then 0 else (if x1 then 0 else (if x0 then 1 else 2))) else (if x2 then (if x1 then (if x0 then 2 else 1) else 0) else 0)) else 0) else (if x4 then (if x3 then (if x2 then 0 else (if x1 then 0 else (if x0 then 3 else 2))) else (if x2 then (if x1 then 0 else (if x0 then 2 else 3)) else 0)) else 0)) else 0) else (if d2 then (if d1 then (if x3 then (if x2 then (if x1 then 0 else (if x0 then 0 else 2)) else (if x1 then (if x0 then 2 else 0) else 0)) else 0) else (if x4 then 0 else (if x3 then (if x2 then (if x1 then 0 else (if x0 then 0 else 1)) else (if x1 then 0 else (if x0 then 1 else 0))) else 0))) else (if d1 then (if x4 then (if x3 then (if x2 then (if x1 then (if x0 then 0 else 2) else (if x0 then 2 else 0)) else 0) else (if x2 then (if x1 then (if x0 then 1 else 4) else (if x0 then 4 else 1)) else (if x1 then (if x0 then 0 else 1) else (if x0 then 1 else 0)))) else (if x3 then (if x2 then (if x1 then (if x0 then 0 else 2) else (if x0 then 2 else 0)) else (if x1 then (if x0 then 3 else 1) else (if x0 then 1 else 3))) else (if x2 then (if x1 then (if x0 then 1 else 4) else (if x0 then 4 else 1)) else 0))) else (if x4 then (if x3 then (if x2 then (if x1 then 1 else 0) else (if x1 then 2 else 1)) else (if x2 then (if x1 then 2 else 1) else (if x1 then 1 else 0))) else (if x3 then (if x2 then (if x1 then 1 else 0) else (if x1 then 2 else 1)) else (if x2 then 1 else (if x1 then 1 else 0))))))) else (if d3 then (if d2 then (if d1 then (if x4 then (if x3 then (if x2 then 0 else (if x1 then 0 else (if x0 then 1 else 2))) else (if x2 then (if x1 then (if x0 then 2 else 1) else 0) else 0)) else 0) else (if x4 then (if x3 then (if x2 then 0 else (if x1 then 0 else (if x0 then 1 else 5))) else (if x2 then (if x1 then 0 else (if x0 then 5 else 1)) else 0)) else 0)) else 0) else (if d2 then (if d1 then (if x3 then (if x2 then (if x1 then 0 else (if x0 then 0 else 3)) else (if x1 then (if x0 then 3 else 0) else 0)) else 0) else (if x4 then 0 else (if x3 then (if x2 then (if x1 then 0 else (if x0 then 0 else 1)) else (if x1 then 0 else (if x0 then 1 else 0))) else 0))) else (if d1 then (if x4 then (if x3 then (if x2 then (if x1 then (if x0 then 0 else 3) else (if x0 then 3 else 0)) else 0) else (if x2 then (if x1 then (if x0 then 2 else 4) else (if x0 then 4 else 2)) else (if x1 then (if x0 then 0 else 1) else (if x0 then 1 else 0)))) else (if x3 then (if x2 then (if x1 then (if x0 then 0 else 3) else (if x0 then 3 else 0)) else (if x1 then (if x0 then 5 else 1) else (if x0 then 1 else 5))) else (if x2 then (if x1 then (if x0 then 1 else 4) else (if x0 then 4 else 1)) else 0))) else (if x4 then (if x3 then (if x2 then (if x1 then 1 else 0) else (if x1 then 4 else 1)) else (if x2 then (if x1 then 2 else 3) else (if x1 then 3 else 0))) else (if x3 then (if x2 then (if x1 then 2 else 0) else (if x1 then 4 else 1)) else (if x2 then (if x1 then 1 else 3) else (if x1 then 3 else 0)))))))))

set_option maxRecDepth 20000
set_option maxHeartbeats 20000000

theorem rank_bound : ∀ x0 x1 x2 x3 x4 x5 d1 d2 d3 c h : Bool,
    rank x0 x1 x2 x3 x4 x5 d1 d2 d3 c h≤6 := by decide

theorem rank_certificate : ∀ x0 x1 x2 x3 x4 x5 d1 d2 d3 c h cp hp : Bool,
    (h=true → cp≠c) →
    xor x4 (x3||x2)=xor x4 (xor x3 d3||xor x2 d2) →
    xor x5 (x4||x3)=xor x5 (x4||xor x3 d3) →
    rank
      (xor x0 (c||h)) (xor x1 (x0||c)) (xor x2 (x1||x0))
      (xor x3 (x2||x1)) (xor x4 (x3||x2)) (xor x5 (x4||x3))
      (xor (xor x1 (x0||c)) (xor (xor x1 d1) (!x0||c)))
      (xor (xor x2 (x1||x0)) (xor (xor x2 d2) (xor x1 d1||!x0)))
      (xor (xor x3 (x2||x1)) (xor (xor x3 d3) (xor x2 d2||xor x1 d1))) cp hp
      +(if c then 1 else 0)≤rank x0 x1 x2 x3 x4 x5 d1 d2 d3 c h := by decide


def older (x : Code) : Nat → Bool
  | 0 => false
  | j+1 => x j

theorem lower_drive (x : Code) (j : Nat) :
    T x (j+1)=xor (x (j+1)) (x j||older x j) := by
  cases j with
  | zero => simp only [T,older,Bool.or_false]
  | succ j => rfl

theorem compatible (x : Code) (j : Nat) (black : older x j=true) : T x j≠x j := by
  cases j with
  | zero => cases black
  | succ j =>
    change x j=true at black
    rw [lower_drive,black]
    simp only [Bool.true_or]
    cases x (j+1) <;> decide

theorem older_agree (x y : Code) (j : Nat) (low : AgreeBelow (j+1) x y) :
    older x j=older y j := by
  cases j with
  | zero => rfl
  | succ j => exact low j (by omega)

theorem unxor (a b : Bool) : xor a (xor a b)=b := by cases a <;> cases b <;> rfl
theorem neq_neg (a b : Bool) (h : a≠b) : b= !a := by cases a <;> cases b <;> simp_all

def measure (j : Nat) (x y : Code) : Nat :=
  rank (x (j+1)) (x (j+2)) (x (j+3)) (x (j+4)) (x (j+5)) (x (j+6))
    (xor (x (j+2)) (y (j+2))) (xor (x (j+3)) (y (j+3)))
    (xor (x (j+4)) (y (j+4))) (x j) (older x j)

theorem measure_bound (j : Nat) (x y : Code) : measure j x y≤6 := rank_bound _ _ _ _ _ _ _ _ _ _ _

/-- At most six black ticks of the common lower clock can be paid before
escape. The rank can stall on white ticks; it is not a strict local rank. -/
theorem measure_step (j : Nat) (x y : Code)
    (low : AgreeBelow (j+1) x y) (different : x (j+1)≠y (j+1))
    (a : x (j+5)=y (j+5)) (b : x (j+6)=y (j+6))
    (a1 : T x (j+5)=T y (j+5)) (b1 : T x (j+6)=T y (j+6)) :
    measure j (T x) (T y)+(if x j then 1 else 0)≤measure j x y := by
  have neg:=neq_neg _ _ different
  have lowj:=low j (by omega)
  have oldeq:=older_agree x y j low
  have e4 : xor (x (j+5)) (x (j+4)||x (j+3))=
      xor (x (j+5)) (y (j+4)||y (j+3)) := by
    simpa only [T,←a] using a1
  have e5 : xor (x (j+6)) (x (j+5)||x (j+4))=
      xor (x (j+6)) (x (j+5)||y (j+4)) := by
    simpa only [T,←a,←b] using b1
  have cert:=rank_certificate
    (x (j+1)) (x (j+2)) (x (j+3)) (x (j+4)) (x (j+5)) (x (j+6))
    (xor (x (j+2)) (y (j+2))) (xor (x (j+3)) (y (j+3)))
    (xor (x (j+4)) (y (j+4))) (x j) (older x j) (T x j) (older (T x) j)
    (compatible x j) (by simpa only [unxor] using e4) (by simpa only [unxor] using e5)
  have tx0:=lower_drive x j
  simp only [measure]
  rw [tx0]
  simpa only [T,←lowj,←oldeq,unxor,neg] using cert

theorem black_within (j s : Nat) (x : Code) (hx : x 0=true) :
    ∃ t,t≤(j+1)/2 ∧ iter (s+t) x j=true := by
  by_cases black : iter s x j=true
  · exact ⟨0,by omega,black⟩
  · by_cases zero : j=0
    · subst j
      have e : iter s x 0=true := by simpa only [iter_zero] using hx
      exact False.elim (black e)
    · obtain ⟨t,ht,ne⟩:=flip_bound_from j s (by omega) x hx
      have white : iter s x j=false := by cases h:iter s x j <;> simp_all
      refine ⟨t,ht,?_⟩
      rw [white] at ne
      cases h:iter (s+t) x j <;> simp_all

theorem rank_chain (r : Nat → Nat) (N : Nat)
    (step : ∀ t,t<N → r (t+1)≤r t) :
    ∀ d a,a+d≤N → r (a+d)≤r a := by
  intro d
  induction d with
  | zero => intro a ha;exact Nat.le_refl _
  | succ d ih =>
    intro a ha
    have prior:=ih a (by omega)
    have next:=step (a+d) (by omega)
    exact Nat.le_trans next prior

theorem clock_rank_contradiction (r : Nat → Nat) (c : Nat → Bool) (B : Nat)
    (initial : r 0≤6)
    (step : ∀ t,t<7*(B+1) → r (t+1)+(if c t then 1 else 0)≤r t)
    (black : ∀ s,s≤6*(B+1) → ∃ u,u≤B ∧ c (s+u)=true) : False := by
  have weak : ∀ t,t<7*(B+1) → r (t+1)≤r t := by
    intro t ht;have h:=step t ht;omega
  have mono (a b : Nat) (hab : a≤b) (hb : b≤7*(B+1)) : r b≤r a := by
    have h:=rank_chain r _ weak (b-a) a (by omega)
    have idx : a+(b-a)=b := by omega
    simpa only [idx] using h
  have blocks (k : Nat) (hk : k<7) : r ((k+1)*(B+1))+1≤r (k*(B+1)) := by
    have startbound : k*(B+1)≤6*(B+1) := Nat.mul_le_mul_right _ (by omega)
    have endbound : (k+1)*(B+1)≤7*(B+1) := Nat.mul_le_mul_right _ (by omega)
    have endpoint : (k+1)*(B+1)=k*(B+1)+(B+1) := by rw [Nat.add_mul,Nat.one_mul]
    obtain ⟨u,hu,bc⟩:=black (k*(B+1)) startbound
    have before:=mono (k*(B+1)) (k*(B+1)+u) (by omega) (by omega)
    have after:=mono (k*(B+1)+u+1) ((k+1)*(B+1)) (by omega) endbound
    have strict:=step (k*(B+1)+u) (by omega)
    rw [bc] at strict
    change r (k*(B+1)+u+1)+1≤r (k*(B+1)+u) at strict
    omega
  have h0:=blocks 0 (by decide)
  have h1:=blocks 1 (by decide)
  have h2:=blocks 2 (by decide)
  have h3:=blocks 3 (by decide)
  have h4:=blocks 4 (by decide)
  have h5:=blocks 5 (by decide)
  have h6:=blocks 6 (by decide)
  simp only [Nat.zero_mul,Nat.one_mul,Nat.reduceAdd] at h0 h1 h2 h3 h4 h5 h6
  omega

/-- A uniform arbitrary-depth escape theorem for a four-digit band.
No finite support, temporal period or upper-tail condition is assumed. -/
theorem four_layer_escape (j : Nat) (x y : Code) (hx : x 0=true)
    (low : AgreeBelow (j+1) x y) (different : x (j+1)≠y (j+1)) :
    ∃ t,t≤7*((j+1)/2+1) ∧
      (iter t x (j+5)≠iter t y (j+5) ∨ iter t x (j+6)≠iter t y (j+6)) := by
  apply Classical.byContradiction
  intro none
  have same : ∀ t,t≤7*((j+1)/2+1) →
      iter t x (j+5)=iter t y (j+5) ∧ iter t x (j+6)=iter t y (j+6) := by
    intro t ht
    constructor
    · by_cases eq : iter t x (j+5)=iter t y (j+5)
      · exact eq
      · exact False.elim (none ⟨t,ht,Or.inl eq⟩)
    · by_cases eq : iter t x (j+6)=iter t y (j+6)
      · exact eq
      · exact False.elim (none ⟨t,ht,Or.inr eq⟩)
  apply clock_rank_contradiction (fun t => measure j (iter t x) (iter t y))
    (fun t => iter t x j) ((j+1)/2) (measure_bound j x y)
  · intro t ht
    exact measure_step j (iter t x) (iter t y) (iter_agree low t) (iter_diff low different t)
      (same t (by omega)).1 (same t (by omega)).2
      (same (t+1) (by omega)).1 (same (t+1) (by omega)).2
  · intro s hs
    exact black_within j s x hx

theorem recurrent_four_layer_escape (j s : Nat) (x y : Code) (hx : x 0=true)
    (low : AgreeBelow (j+1) x y) (different : x (j+1)≠y (j+1)) :
    ∃ t,t≤7*((j+1)/2+1) ∧
      (iter (s+t) x (j+5)≠iter (s+t) y (j+5) ∨
       iter (s+t) x (j+6)≠iter (s+t) y (j+6)) := by
  obtain ⟨t,ht,ne⟩:=four_layer_escape j (iter s x) (iter s y)
    (by simpa only [iter_zero] using hx) (iter_agree low s) (iter_diff low different s)
  exact ⟨t,ht,by simpa only [iter_add] using ne⟩


end Ruliology.CellularAutomata.Rule30DefectClockBudget
