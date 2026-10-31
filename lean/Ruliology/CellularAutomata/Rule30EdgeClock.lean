module
public import Ruliology.CellularAutomata.Rule30FrozenRuler

/-!
# Quiet-time bounds and two-layer defect escape

In the official `Rule30FrozenRuler.T` edge frame, any code with black digit0
changes each positive digit j within ceil(j/2) updates, from every starting
time (`flip_bound_from`). The bound is attained by the single seed at its
first change of digit j (`seed_at_bound`). No finite-support or periodicity
assumption is required.

For two codes first differing at j+1, agreement of interface digits j+3 and
j+4 over three consecutive rows forces their shared digit j white. The
clock bound therefore forces a defect outside that two-digit band within
ceil(j/2)+2 updates (`two_layer_escape`), recurrently from every starting
time. This includes j=0, where immediate-next-digit excitation has a genuine
exception. It does not establish escape from arbitrary-width bands.

If two codes agree below digit j+1>=2 and differ at that digit, their next
digit is excited in every interval of ceil(j/2)+1 updates
(`recurrent_excitation`). The lowest difference persists by the existing
triangular-map theorem. This is one-layer excitation; it does not establish
escape from an arbitrary damage band. Digit1 is excluded from this
excitation statement: the black edge masks its influence on digit2.

The mechanism uses the OR gate: an unchanged digit forces both lower
drivers white. Iterating this constraint reaches the permanently black
edge. These are bounds at a fixed edge digit; the center reads a moving
digit and its eventual periodicity remains open.
-/

@[expose] public section
set_option autoImplicit false
namespace Ruliology.CellularAutomata.Rule30EdgeClock
open Ruliology.CellularAutomata.Rule30FrozenRuler
abbrev Code := Nat → Bool

theorem freeze_below (x : Code) (j : Nat) (same : T x (j+2)=x (j+2)) :
    x (j+1)=false ∧ x j=false := by
  simp only [T] at same
  cases a:x (j+2) <;> cases b:x (j+1) <;> cases c:x j <;> simp_all

/-- Every non-edge digit changes within ceil(j/2) ticks. The autonomous
prefix period can be much longer; its consecutive quiet stretches cannot. -/
theorem flip_bound (j : Nat) (hj : 0<j) (x : Code) (hx : x 0=true) :
    ∃ t,t≤(j+1)/2 ∧ iter t x j≠x j := by
  induction j using Nat.strongRecOn generalizing x with
  | ind j ih =>
    by_cases one : j=1
    · subst j
      refine ⟨1,by omega,?_⟩
      change xor (x 1) (x 0)≠x 1
      rw [hx];cases x 1 <;> decide
    obtain ⟨k,rfl⟩ : ∃ k,j=k+2 := ⟨j-2,by omega⟩
    apply Classical.byContradiction
    intro none
    have constant : ∀ t,t≤(k+3)/2 → iter t x (k+2)=x (k+2) := by
      intro t ht
      by_cases eq : iter t x (k+2)=x (k+2)
      · exact eq
      · exact False.elim (none ⟨t,ht,eq⟩)
    have lower : ∀ t,t≤(k+1)/2 → iter t x k=false := by
      intro t ht
      have a:=constant t (by omega)
      have b:=constant (t+1) (by omega)
      have eq : T (iter t x) (k+2)=iter t x (k+2) := b.trans a.symm
      exact (freeze_below _ k eq).2
    by_cases zero : k=0
    · subst k
      have wrong:=lower 0 (by omega)
      change x 0=false at wrong
      rw [hx] at wrong
      cases wrong
    obtain ⟨t,ht,ne⟩:=ih k (by omega) (by omega) x hx
    have a:=lower 0 (by omega)
    have b:=lower t ht
    exact ne (b.trans a.symm)

theorem flip_bound_from (j s : Nat) (hj : 0<j) (x : Code) (hx : x 0=true) :
    ∃ t,t≤(j+1)/2 ∧ iter (s+t) x j≠iter s x j := by
  obtain ⟨t,ht,ne⟩:=flip_bound j hj (iter s x) (by simpa only [iter_zero] using hx)
  refine ⟨t,ht,?_⟩
  rw [iter_add]
  exact ne

private theorem seed_before (j t : Nat) (before : 2*t<j) : iter t one j=false := by
  induction t generalizing j with
  | zero => simp only [iter,one,show j≠0 by omega,decide_false]
  | succ t ih =>
    obtain ⟨k,rfl⟩ : ∃ k,j=k+2 := ⟨j-2,by omega⟩
    change T (iter t one) (k+2)=false
    simp only [T,ih (k+2) (by omega),ih (k+1) (by omega),ih k (by omega)]
    rfl

/-- The change bound is sharp: the single seed first changes digit j at
exactly ceil(j/2), for every positive j. -/
theorem seed_at_bound (j : Nat) (hj : 0<j) : iter ((j+1)/2) one j=true := by
  obtain ⟨t,ht,ne⟩:=flip_bound j hj one rfl
  have white : one j=false := by simp only [one,show j≠0 by omega,decide_false]
  have equal : t=(j+1)/2 := by
    by_cases eq : t=(j+1)/2
    · exact eq
    · have past:=seed_before j t (by omega)
      exact False.elim (ne (past.trans white.symm))
  subst t
  rw [white] at ne
  cases a:iter ((j+1)/2) one j <;> simp_all

theorem mask_forces_black (a b c u : Bool) (different : a≠b)
    (same : xor u (a||c)=xor u (b||c)) : c=true := by
  cases a <;> cases b <;> cases c <;> cases u <;> simp_all

/-- A persistent lowest difference at digit j+1 excites its next digit
within ceil(j/2)+1 ticks. This is a one-layer result, not full band escape. -/
theorem higher_excitation (j : Nat) (hj : 0<j) (x y : Code) (hx : x 0=true)
    (below : AgreeBelow (j+1) x y) (different : x (j+1)≠y (j+1)) :
    ∃ t,t≤(j+1)/2+1 ∧ iter t x (j+2)≠iter t y (j+2) := by
  apply Classical.byContradiction
  intro none
  have same : ∀ t,t≤(j+1)/2+1 → iter t x (j+2)=iter t y (j+2) := by
    intro t ht
    by_cases eq : iter t x (j+2)=iter t y (j+2)
    · exact eq
    · exact False.elim (none ⟨t,ht,eq⟩)
  have lower : ∀ t,t≤(j+1)/2 → iter t x j=true := by
    intro t ht
    have currentEq:=same t (by omega)
    have after:=same (t+1) (by omega)
    have low:=iter_agree below t j (by omega)
    have ne:=iter_diff below different t
    have e : xor (iter t y (j+2)) (iter t x (j+1)||iter t y j)=
        xor (iter t y (j+2)) (iter t y (j+1)||iter t y j) := by
      change T (iter t x) (j+2)=T (iter t y) (j+2) at after
      simpa only [T,currentEq,low] using after
    exact low.trans (mask_forces_black _ _ _ _ ne e)
  obtain ⟨t,ht,ne⟩:=flip_bound j hj x hx
  exact ne ((lower t ht).trans (lower 0 (by omega)).symm)

theorem recurrent_excitation (j s : Nat) (hj : 0<j) (x y : Code) (hx : x 0=true)
    (below : AgreeBelow (j+1) x y) (different : x (j+1)≠y (j+1)) :
    ∃ t,t≤(j+1)/2+1 ∧ iter (s+t) x (j+2)≠iter (s+t) y (j+2) := by
  obtain ⟨t,ht,ne⟩:=higher_excitation j hj (iter s x) (iter s y)
    (by simpa only [iter_zero] using hx) (iter_agree below s) (iter_diff below different s)
  exact ⟨t,ht,by simpa only [iter_add] using ne⟩

theorem cancel_xor (u a b : Bool) (h : xor u a=xor u b) : a=b := by
  cases u <;> cases a <;> cases b <;> simp_all

theorem bool_two_stalls (a b p q u c a1 b1 : Bool)
    (ne : a≠b) (ne1 : a1≠b1)
    (h0 : (p||a)=(q||b)) (m0 : (u||p)=(u||q))
    (h1 : (xor p (a||c)||a1)=(xor q (b||c)||b1))
    (m1 : (xor u (p||a)||xor p (a||c))=
          (xor u (p||a)||xor q (b||c))) : c=false := by
  cases a <;> cases b <;> cases p <;> cases q <;> cases u <;>
    cases c <;> cases a1 <;> cases b1 <;> simp_all

/-- If both interface digits agree for three consecutive rows, the common
digit below the persistent lowest difference must currently be white. -/
theorem three_rows_force_white (x y : Code) (j : Nat)
    (below : AgreeBelow (j+1) x y) (different : x (j+1)≠y (j+1))
    (a0 : x (j+3)=y (j+3)) (b0 : x (j+4)=y (j+4))
    (a1 : T x (j+3)=T y (j+3)) (b1 : T x (j+4)=T y (j+4))
    (a2 : T (T x) (j+3)=T (T y) (j+3))
    (b2 : T (T x) (j+4)=T (T y) (j+4)) : x j=false := by
  have low:=below j (by omega)
  have next_ne : T x (j+1)≠T y (j+1) := iter_diff below different 1
  have h0 : (x (j+2)||x (j+1))=(y (j+2)||y (j+1)) := by
    apply cancel_xor (y (j+3))
    simpa only [T,a0] using a1
  have m0 : (x (j+3)||x (j+2))=(x (j+3)||y (j+2)) := by
    apply cancel_xor (y (j+4))
    simpa only [T,b0,←a0] using b1
  have h1 : (T x (j+2)||T x (j+1))=(T y (j+2)||T y (j+1)) := by
    apply cancel_xor (T y (j+3))
    change xor (T x (j+3)) (T x (j+2)||T x (j+1))=
      xor (T y (j+3)) (T y (j+2)||T y (j+1)) at a2
    rw [a1] at a2
    exact a2
  have m1 : (T x (j+3)||T x (j+2))=(T x (j+3)||T y (j+2)) := by
    apply cancel_xor (T y (j+4))
    change xor (T x (j+4)) (T x (j+3)||T x (j+2))=
      xor (T y (j+4)) (T y (j+3)||T y (j+2)) at b2
    rw [b1,←a1] at b2
    exact b2
  apply bool_two_stalls (x (j+1)) (y (j+1)) (x (j+2)) (y (j+2))
    (x (j+3)) (x j) (T x (j+1)) (T y (j+1)) different next_ne h0 m0
  · simpa only [T,low] using h1
  · simpa only [T,low] using m1

/-- Every persistent first difference escapes a band of two digits within
ceil(j/2)+2 ticks, including the exceptional first-difference digit 1. -/
theorem two_layer_escape (j : Nat) (x y : Code) (hx : x 0=true)
    (below : AgreeBelow (j+1) x y) (different : x (j+1)≠y (j+1)) :
    ∃ t,t≤(j+1)/2+2 ∧
      (iter t x (j+3)≠iter t y (j+3) ∨ iter t x (j+4)≠iter t y (j+4)) := by
  apply Classical.byContradiction
  intro none
  have same : ∀ t,t≤(j+1)/2+2 →
      iter t x (j+3)=iter t y (j+3) ∧ iter t x (j+4)=iter t y (j+4) := by
    intro t ht
    constructor
    · by_cases eq : iter t x (j+3)=iter t y (j+3)
      · exact eq
      · exact False.elim (none ⟨t,ht,Or.inl eq⟩)
    · by_cases eq : iter t x (j+4)=iter t y (j+4)
      · exact eq
      · exact False.elim (none ⟨t,ht,Or.inr eq⟩)
  have white : ∀ t,t≤(j+1)/2 → iter t x j=false := by
    intro t ht
    exact three_rows_force_white (iter t x) (iter t y) j
      (iter_agree below t) (iter_diff below different t)
      (same t (by omega)).1 (same t (by omega)).2
      (same (t+1) (by omega)).1 (same (t+1) (by omega)).2
      (same (t+2) (by omega)).1 (same (t+2) (by omega)).2
  by_cases zero : j=0
  · subst j
    have wrong:=white 0 (by omega)
    change x 0=false at wrong
    rw [hx] at wrong;cases wrong
  · obtain ⟨t,ht,ne⟩:=flip_bound j (by omega) x hx
    exact ne ((white t ht).trans (white 0 (by omega)).symm)


/-- The two-layer escape recurs from every starting time; no seed or finite
support hypothesis is imposed. -/
theorem recurrent_two_layer_escape (j s : Nat) (x y : Code) (hx : x 0=true)
    (below : AgreeBelow (j+1) x y) (different : x (j+1)≠y (j+1)) :
    ∃ t,t≤(j+1)/2+2 ∧
      (iter (s+t) x (j+3)≠iter (s+t) y (j+3) ∨
       iter (s+t) x (j+4)≠iter (s+t) y (j+4)) := by
  obtain ⟨t,ht,ne⟩:=two_layer_escape j (iter s x) (iter s y)
    (by simpa only [iter_zero] using hx) (iter_agree below s) (iter_diff below different s)
  exact ⟨t,ht,by simpa only [iter_add] using ne⟩

end Ruliology.CellularAutomata.Rule30EdgeClock
