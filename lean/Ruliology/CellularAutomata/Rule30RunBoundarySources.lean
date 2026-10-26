module
public import Ruliology.CellularAutomata.Rule30Prize
public import Ruliology.CellularAutomata.Rule30Diagonals

/-!
# Actual Rule30 run-boundary sources on a dyadic binary support

The source `source d s` is exactly the black-to-white run boundary
`cell s (s-d) AND NOT cell s (s-d+1)` (`source_physical`). The local update
is Rule90 plus this source (`rule90_source_identity`).

Put H=2^e. Among depths d<=e and times s<2H-1, `SelectedEvent` requires d
even, `(H-1-d/2) AND (2H-2-s)=H-1-d/2`, and a nonzero actual source.
`selected_event_iff_outer` proves, for all e,d,s in that growing strip,
that exactly one event meets these requirements: d=0 and s=H-1.

The proof uses right-diagonal periodicity and the finite seed cone. At
phase H-1 every diagonal bit up to e is black; just after H the prefix
agrees with the early seed orbit. A positive-depth run-boundary source
vanishes at every phase selected by the binary support condition.

This core module states the mask explicitly. Its interpretation through
Lucas coefficients and the complete Rule90 Duhamel sum is supplied by
separate research proofs using Mathlib. No source deeper than e is
restricted here, no full source-sum noncancellation is asserted, and no
prize problem is solved. The standard diagonal periodicity and local
Boolean decomposition are not claimed as new historical results.

Contributed by Troy Lowry with OpenAI Codex, 2026-10-25.
-/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30RunBoundarySources
open Ruliology.CellularAutomata
open Rule30Diagonals

def source (d t : Nat) : Bool :=
  if d = 0 then R 0 t else R d t && !R (d-1) t

theorem rule90_source_identity (a b c : Bool) :
    Rule30Jen.rule a b c = xor (xor a c) (b && !c) := by
  cases a <;> cases b <;> cases c <;> decide

theorem source_physical (d t : Nat) : source d t =
    (Rule30Jen.cell t ((t:Int)-d) && !Rule30Jen.cell t ((t:Int)-d+1)) := by
  by_cases h : d=0
  · subst d
    have hx : Rule30Jen.cell t ((t:Int)+1)=false :=
      Rule30Diagonals.cell_eq_false_of_gt t ((t:Int)+1) (by omega)
    have hr : Rule30Jen.cell t (t:Int)=true := by simpa [R] using R_zero t
    simp [source,R,hr,hx]
  · have hc : (t:Int)-(d-1:Nat) = (t:Int)-d+1 := by omega
    simp [source,h,R,hc]

theorem source_outer (t : Nat) : source 0 t = true := by simp [source,R_zero]

theorem R_period_pow (j e : Nat) (hj : j ≤ e) :
    ∀ t, R j (t+2^e) = R j t := by
  induction e with
  | zero =>
    have hzero : j=0 := by omega
    subst j
    intro t
    rw [R_zero, R_zero]
  | succ e ih =>
    by_cases h : j ≤ e
    · have hper := ih h
      have hd := periodic_double hper
      simpa [Nat.pow_succ, Nat.mul_comm] using hd
    · have : j=e+1 := by omega
      subst j
      exact R_periodic (e+1)

theorem R_at_zero (j : Nat) (hj : 0<j) : R j 0 = false := by
  simp [R, Rule30Jen.cell]
  omega

theorem R_at_period (j e : Nat) (hj : 0<j) (he : j≤e) :
    R j (2^e) = false := by
  have h := R_period_pow j e he 0
  simpa [R_at_zero j hj] using h

theorem R_last_phase (e j : Nat) (hj : j≤e) : R j (2^e-1) = true := by
  have hp : 0<2^e := Nat.two_pow_pos e
  induction j using Nat.strongRecOn with
  | ind j ih =>
    cases j with
    | zero => exact R_zero _
    | succ j =>
      cases j with
      | zero =>
        have h := R_one_succ (2^e-1)
        rw [show 2^e-1+1=2^e by omega, R_at_period 1 e (by omega) hj] at h
        cases hx : R 1 (2^e-1) <;> simp_all
      | succ j =>
        have low := ih (j+1) (by omega) (by omega)
        have h := R_step j (2^e-1)
        rw [show 2^e-1+1=2^e by omega, R_at_period (j+2) e (by omega) hj, low] at h
        cases hx : R (j+2) (2^e-1) <;> simp_all

theorem source_zero_before_cone (d t : Nat) (hd : 2*t<d) : source d t=false := by
  have hp : 0<d := by omega
  have h : R d t=false := Rule30Jen.cell_eq_false_of_lt t _ (by omega)
  simp [source, Nat.ne_of_gt hp, h]

theorem source_period_pow (d e t : Nat) (hd : d≤e) :
    source d (t+2^e)=source d t := by
  by_cases h : d=0
  · simp [source,h,R_zero]
  · simp [source,h,R_period_pow d e hd t,R_period_pow (d-1) e (by omega) t]

theorem source_last_phase (d e : Nat) (hd : 0<d) (he : d≤e) :
    source d (2^e-1)=false := by
  simp [source,Nat.ne_of_gt hd,R_last_phase e d he,
    R_last_phase e (d-1) (by omega)]

theorem source_zero_window (d e v : Nat) (_hd : 0<d) (he : d≤e) (hv : 2*v<d) :
    source d (2^e+v)=false := by
  rw [Nat.add_comm,source_period_pow d e v he]
  exact source_zero_before_cone d v hv

/-- The bit-support condition for the even-depth channel at time 2^(e+1)-1.
Every actual source at a positive even depth d<=e is zero on this support.
This proves no conclusion about depths greater than e. -/
theorem source_dyadic_kernel_zero (e r s : Nat) (hr : 0<r) (he : 2*r≤e)
    (hs : s<2*(2^e)-1)
    (hk : ((2^e-1-r) &&& (2*(2^e)-2-s)) = (2^e-1-r)) :
    source (2*r) s=false := by
  let H := 2^e
  have hH : 0<H := Nat.two_pow_pos e
  have hrH : r<H := by
    have : e<2^e := Nat.lt_two_pow_self
    dsimp [H]
    omega
  have hK : H-1-r<H := by omega
  have hmod := congrArg (fun x => x%H) hk
  change ((H-1-r) &&& (2*H-2-s))%H = (H-1-r)%H at hmod
  rw [Nat.and_mod_two_pow, Nat.mod_eq_of_lt hK] at hmod
  have hbound : H-1-r ≤ (2*H-2-s)%H := by
    rw [←hmod]
    exact Nat.and_le_right
  by_cases hsmall : s<r
  · exact source_zero_before_cone _ _ (by omega)
  have hleft : H-1≤s := by
    by_cases h : H-1≤s
    · exact h
    · have hhi : H≤2*H-2-s := by omega
      have hlo : 2*H-2-s<2*H := by omega
      have hm : (2*H-2-s)%H = (2*H-2-s)-H := by
        rw [Nat.mod_eq_sub_mod hhi, Nat.mod_eq_of_lt (by omega)]
      rw [hm] at hbound
      omega
  have hright : s≤H-1+r := by
    have hh : 2*H-2-s<H := by omega
    rw [Nat.mod_eq_of_lt hh] at hbound
    omega
  by_cases hlast : s=H-1
  · rw [hlast]
    exact source_last_phase _ e (by omega) he
  · have hpos : H≤s := by omega
    have htime : s=H+(s-H) := by omega
    rw [htime]
    exact source_zero_window _ e (s-H) (by omega) he (by omega)

theorem outer_kernel_iff (e s : Nat) (hs : s<2*(2^e)-1) :
    (((2^e-1) &&& (2*(2^e)-2-s)) = (2^e-1)) ↔ s=2^e-1 := by
  let H := 2^e
  have hp : 0<H := Nat.two_pow_pos e
  constructor
  · intro hk
    have hm := congrArg (fun x => x%H) hk
    change ((H-1) &&& (2*H-2-s))%H = (H-1)%H at hm
    rw [Nat.and_mod_two_pow,Nat.mod_eq_of_lt (show H-1<H by omega)] at hm
    have hb : H-1≤(2*H-2-s)%H := by rw [←hm]; exact Nat.and_le_right
    by_cases hx : H≤2*H-2-s
    · have hm' : (2*H-2-s)%H=(2*H-2-s)-H := by
        rw [Nat.mod_eq_sub_mod hx,Nat.mod_eq_of_lt (by omega)]
      rw [hm'] at hb
      omega
    · rw [Nat.mod_eq_of_lt (by omega)] at hb
      change s=H-1
      omega
  · intro hk
    rw [hk,show 2*(2^e)-2-(2^e-1)=2^e-1 by have := Nat.two_pow_pos e; omega]
    exact Nat.and_self _

/-- A source selected by the explicit binary support mask. The relation of
this mask to a full Rule90 Duhamel sum is not asserted here. -/
def SelectedEvent (e d s : Nat) : Prop :=
  s<2*(2^e)-1 ∧ d%2=0 ∧
  ((2^e-1-d/2) &&& (2*(2^e)-2-s)) = (2^e-1-d/2) ∧ source d s=true

/-- At every dyadic scale, within the growing strip d<=e, exactly one actual
nonlinear source passes the mask: the outer wall at time 2^e-1. -/
theorem selected_event_iff_outer (e d s : Nat) (hd : d≤e) :
    SelectedEvent e d s ↔ d=0 ∧ s=2^e-1 := by
  constructor
  · rintro ⟨hs,heven,hmask,hsource⟩
    by_cases hzero : d=0
    · refine ⟨hzero,?_⟩
      subst d
      simp only [Nat.zero_div,Nat.sub_zero] at hmask
      exact (outer_kernel_iff e s hs).mp hmask
    · have hdform : d=2*(d/2) := by omega
      have hz := source_dyadic_kernel_zero e (d/2) s (by omega) (by omega) hs hmask
      rw [←hdform,hsource] at hz
      contradiction
  · rintro ⟨rfl,rfl⟩
    have hp := Nat.two_pow_pos e
    refine ⟨by omega,by omega,?_,source_outer _⟩
    simp only [Nat.zero_div,Nat.sub_zero]
    exact (outer_kernel_iff e (2^e-1) (by omega)).mpr rfl

end Ruliology.CellularAutomata.Rule30RunBoundarySources
