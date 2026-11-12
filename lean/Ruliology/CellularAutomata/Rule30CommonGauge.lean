module

public import Ruliology.CellularAutomata.Rule30Prize
public import Ruliology.CellularAutomata.Rule30Diagonals
public import Ruliology.CellularAutomata.Rule30DividedDifference

/-!
# Common-field exterior rigidity and unbounded depth escape

All-time common-gauge rigidity with a zero background. The auxiliary field
is not assumed to be a physical Rule30 history. This adapts the catalog's
XOR-rigidity gap argument, keeping an asymmetric black right endpoint.
The right-wedge section applies it uniformly to every actual canonical age
pair U>V. Beyond the younger row's right front, any supported common field
equals its initial older-right-edge bit times the older canonical row.
The finite-horizon version has a distance-dependent bound. The overlap
containing the center and the left edge remains unresolved.
The BandEscape section proves that every nonzero field over a canonical
older background visits arbitrarily large right-edge depths after every
time. It uses dyadic returns and a backward peeling argument, without W
or an evolution hypothesis for the second coefficient background. This
does not force a visit to the moving center depth.
`ObserverConnection` identifies the canonical instances of the exact mode
and CommonField used by `Rule30DividedDifference.ObserverCriterion`, whose
implication to `Rule30TraceEdge.EdgeObservable` is proved in that module.
Thus the exterior and escape results apply to that auxiliary observer route.
The remaining observation statement concerns a fixed physical column.
-/

@[expose] public section
namespace Ruliology.CellularAutomata.Rule30CommonGauge
open Ruliology.CellularAutomata.Rule30Jen (rule)

def lin (a l c r : Bool) : Bool := xor (xor l c) ((!a) && r)

def Good (a b c d : Bool) : Prop := (a && d)=(c && b)

theorem good_self (a b : Bool) : Good a b a b := rfl
theorem good_symm : ∀ a b c d : Bool, Good a b c d → Good c d a b := by
  unfold Good; decide +kernel
theorem middle_zero : ∀ a b c d e f : Bool,
    ¬ Good a b e f → Good a b c d → Good c d e f → c=false ∧ d=false := by
  unfold Good; decide +kernel

theorem gap_two : ∀ a b d e f : Bool,
    Good (rule a false true) (lin false b false d)
      (rule false true e) (lin true false d f) → Good a b true d := by
  unfold Good; decide +kernel

namespace HalfLine
def Actual (A : Nat → Nat → Bool) : Prop :=
  ∀ t i, A (t+1) i=rule (A t i) (A t (i+1)) (A t (i+2))
def Driven (A h : Nat → Nat → Bool) : Prop :=
  ∀ t i, h (t+1) i=lin (A t (i+1)) (h t i) (h t (i+1)) (h t (i+2))
def Common (A h : Nat → Nat → Bool) : Prop :=
  ∀ t i, Good (A t i) (h t i) (A t (i+1)) (h t (i+1))
def CommonThrough (A h : Nat → Nat → Bool) (N : Nat) : Prop :=
  ∀ t, t ≤ N → ∀ i, Good (A t i) (h t i) (A t (i+1)) (h t (i+1))

/-- No physical-history premise on h. The right endpoint must be black in A. -/
theorem distant_good_right_black_through (A h : Nat → Nat → Bool)
    (ha : Actual A) (hh : Driven A h) (N : Nat) (hw : CommonThrough A h N) (d : Nat) :
    ∀ t p, t+d/2 ≤ N → A t (p+d)=true →
      Good (A t p) (h t p) (A t (p+d)) (h t (p+d)) := by
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro t p ht hblack
    by_cases hd0 : d=0
    · subst d; exact good_self _ _
    by_cases hd1 : d=1
    · subst d; exact hw t (by omega) p
    apply Classical.byContradiction
    intro bad
    have mid : ∀ k, p<k → k<p+d → A t k=false ∧ h t k=false := by
      intro k hpk hkq
      have hr := ih (p+d-k) (by omega) t k (by omega)
        (by simpa [show k+(p+d-k)=p+d by omega] using hblack)
      rw [show k+(p+d-k)=p+d by omega] at hr
      by_cases hak : A t k=true
      · have hl := ih (k-p) (by omega) t p (by omega)
          (by simpa [show p+(k-p)=k by omega] using hak)
        rw [show p+(k-p)=k by omega] at hl
        have hz := middle_zero _ _ _ _ _ _ bad hl hr
        rw [hak] at hz
        cases hz.1
      · have hak0 : A t k=false := by cases he : A t k <;> simp_all
        refine ⟨hak0, ?_⟩
        simpa [Good, hak0, hblack] using hr.symm
    by_cases hd2 : d=2
    · subst d
      obtain ⟨az,hz⟩ := mid (p+1) (by omega) (by omega)
      have hn := hw (t+1) (by omega) p
      rw [ha t p, hh t p, ha t (p+1), hh t (p+1), az,hz,
        show p+1+1=p+2 by omega, show p+1+2=p+3 by omega, hblack] at hn
      apply bad
      rw [hblack]
      exact gap_two (A t p) (h t p) (h t (p+2)) (A t (p+3)) (h t (p+3)) hn
    · obtain ⟨a1,h1⟩ := mid (p+1) (by omega) (by omega)
      obtain ⟨a2,h2⟩ := mid (p+2) (by omega) (by omega)
      obtain ⟨az,hz⟩ := mid (p+d-2) (by omega) (by omega)
      obtain ⟨az1,hz1⟩ := mid (p+d-1) (by omega) (by omega)
      have hnextblack : A (t+1) (p+(d-2))=true := by
        rw [show p+(d-2)=p+d-2 by omega, ha, az,
          show p+d-2+1=p+d-1 by omega, show p+d-2+2=p+d by omega, az1,hblack]
        rfl
      have hn := ih (d-2) (by omega) (t+1) p (by omega) hnextblack
      rw [show p+(d-2)=p+d-2 by omega, ha t p,hh t p,
        ha t (p+d-2),hh t (p+d-2), a1,h1,a2,h2,az,hz,
        show p+d-2+1=p+d-1 by omega, show p+d-2+2=p+d by omega,
        az1,hz1,hblack] at hn
      exact bad (by simpa [rule,lin,hblack] using hn)

theorem distant_good_right_black (A h : Nat → Nat → Bool)
    (ha : Actual A) (hh : Driven A h) (hw : Common A h) (d t p : Nat)
    (hblack : A t (p+d)=true) :
    Good (A t p) (h t p) (A t (p+d)) (h t (p+d)) :=
  distant_good_right_black_through A h ha hh (t+d/2) (fun s _ i => hw s i)
    d t p (by omega) hblack

theorem initial_phase (A h : Nat → Nat → Bool)
    (ha : Actual A) (hh : Driven A h) (hw : Common A h)
    (hs : ∀ i, (h 0 i && A 0 i)=h 0 i) :
    ∃ b : Bool, ∀ i, h 0 i=(b && A 0 i) := by
  by_cases hex : ∃ q, A 0 q=true
  · obtain ⟨q,hq⟩ := hex
    refine ⟨h 0 q, ?_⟩
    intro p
    cases hp : A 0 p with
    | false => simpa [hp] using (hs p).symm
    | true =>
      have hg : Good (A 0 p) (h 0 p) (A 0 q) (h 0 q) := by
        by_cases hle : p ≤ q
        · have hg := distant_good_right_black A h ha hh hw (q-p) 0 p
            (by simpa [Nat.add_sub_of_le hle] using hq)
          simpa [Nat.add_sub_of_le hle] using hg
        · have hg := distant_good_right_black A h ha hh hw (p-q) 0 q
            (by simpa [Nat.add_sub_of_le (by omega : q ≤ p)] using hp)
          apply good_symm
          simpa [Nat.add_sub_of_le (by omega : q ≤ p)] using hg
      simpa [Good,hp,hq] using hg.symm
  · refine ⟨false, ?_⟩
    intro p
    have hp : A 0 p=false := by
      cases he : A 0 p with
      | false => rfl
      | true => exact False.elim (hex ⟨p,he⟩)
    simpa [hp] using (hs p).symm

theorem lin_self : ∀ a b c : Bool, lin b a b c=rule a b c := by decide +kernel

theorem common_mode_classification (A h : Nat → Nat → Bool)
    (ha : Actual A) (hh : Driven A h) (hw : Common A h)
    (hs : ∀ i, (h 0 i && A 0 i)=h 0 i) :
    ∃ b : Bool, ∀ t i, h t i=(b && A t i) := by
  obtain ⟨b,hb⟩ := initial_phase A h ha hh hw hs
  refine ⟨b, ?_⟩
  intro t
  induction t with
  | zero => exact hb
  | succ t ih =>
    intro i
    rw [hh t i, ih i,ih (i+1),ih (i+2),ha t i]
    cases b
    · simp [lin]
    · simpa using lin_self (A t i) (A t (i+1)) (A t (i+2))

end HalfLine

namespace RightWedge
open _root_.Ruliology.CellularAutomata.Rule30Jen (cell)

def delta (U V t : Nat) (p : Int) := xor (cell (U+t) p) (cell (V+t) p)
def dStep (U V : Nat) (h : Nat → Int → Bool) (t : Nat) (p : Int) :=
  xor (xor (h t (p-1)) ((!cell (V+t) (p+1)) && h t p))
    ((!cell (U+t) p) && h t (p+1))
def Mode (U V : Nat) (h : Nat → Int → Bool) : Prop :=
  ∀ t p, h (t+1) p=dStep U V h t p
def Common (U V : Nat) (h : Nat → Int → Bool) : Prop :=
  ∀ t p, Good (delta U V t p) (h t p) (delta U V t (p+1)) (h t (p+1))
def CommonThrough (U V : Nat) (h : Nat → Int → Bool) (N : Nat) : Prop :=
  ∀ t, t ≤ N → ∀ p, Good (delta U V t p) (h t p) (delta U V t (p+1)) (h t (p+1))

def site (V t i : Nat) : Int := (V : Int)+1+t+i
def rightA (U V : Nat) (t i : Nat) := cell (U+t) (site V t i)
def rightH (V : Nat) (h : Nat → Int → Bool) (t i : Nat) := h t (site V t i)

theorem site_left (V t i : Nat) : site V (t+1) i-1=site V t i := by
  simp only [site]; omega
theorem site_center (V t i : Nat) : site V (t+1) i=site V t (i+1) := by
  simp only [site]; omega
theorem site_right (V t i : Nat) : site V (t+1) i+1=site V t (i+2) := by
  simp only [site]; omega
theorem site_neighbor (V t i : Nat) : site V t i+1=site V t (i+1) := by
  simp only [site]; omega
theorem younger_white (V t i : Nat) : cell (V+t) (site V t i)=false := by
  apply Rule30Diagonals.cell_eq_false_of_gt
  simp only [site]; omega

theorem right_cut_actual (U V : Nat) : HalfLine.Actual (rightA U V) := by
  intro t i
  change cell (U+(t+1)) (site V (t+1) i)=_
  rw [show U+(t+1)=(U+t)+1 by omega]
  change rule (cell (U+t) (site V (t+1) i-1)) (cell (U+t) (site V (t+1) i))
    (cell (U+t) (site V (t+1) i+1)) = _
  rw [site_left, site_right, site_center]
  rfl

theorem right_cut_driven (U V : Nat) (h : Nat → Int → Bool) (hh : Mode U V h) :
    HalfLine.Driven (rightA U V) (rightH V h) := by
  intro t i
  have hm := hh t (site V (t+1) i)
  unfold dStep at hm
  rw [site_left,site_right,site_center,younger_white] at hm
  simpa only [rightA,rightH,lin,site_center,Bool.not_false,Bool.true_and] using hm

theorem right_cut_common (U V : Nat) (h : Nat → Int → Bool) (hw : Common U V h) :
    HalfLine.Common (rightA U V) (rightH V h) := by
  intro t i
  have hm := hw t (site V t i)
  unfold delta at hm
  rw [site_neighbor,younger_white,younger_white] at hm
  simpa only [rightA,rightH,Bool.xor_false] using hm

theorem right_cut_common_through (U V : Nat) (h : Nat → Int → Bool) (N : Nat)
    (hw : CommonThrough U V h N) :
    HalfLine.CommonThrough (rightA U V) (rightH V h) N := by
  intro t ht i
  have hm := hw t ht (site V t i)
  unfold delta at hm
  rw [site_neighbor,younger_white,younger_white] at hm
  simpa only [rightA,rightH,Bool.xor_false] using hm

theorem mode_right_white (U V : Nat) (h : Nat → Int → Bool) (hh : Mode U V h)
    (hi : ∀ p, (U : Int) < p → h 0 p=false) :
    ∀ (t : Nat) (p : Int), (U : Int)+t < p → h t p=false := by
  intro t
  induction t with
  | zero => intro p hp; exact hi p (by omega)
  | succ t ih =>
    intro p hp
    rw [hh t p]
    simp only [dStep,ih (p-1) (by omega),ih p (by omega),ih (p+1) (by omega)]
    simp

theorem mode_right_edge (U V : Nat) (h : Nat → Int → Bool) (hh : Mode U V h)
    (hi : ∀ p, (U : Int) < p → h 0 p=false) :
    ∀ t, h t ((U : Int)+t)=h 0 U := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
    rw [hh]
    have e : (U : Int)+(t+1 : Nat)-1=(U : Int)+t := by omega
    have hw0 := mode_right_white U V h hh hi t ((U : Int)+(t+1 : Nat)) (by omega)
    have hw1 := mode_right_white U V h hh hi t ((U : Int)+(t+1 : Nat)+1) (by omega)
    rw [dStep,e,hw0,hw1]
    simpa using ih

/-- A finite, distance-dependent common-gauge horizon suffices in the right
exterior. It does not give a fixed horizon independent of the ages. -/
theorem right_wedge_phase_through (U V : Nat) (hUV : V<U) (h : Nat → Int → Bool)
    (hh : Mode U V h) (N : Nat) (hw : CommonThrough U V h N)
    (hi : ∀ p, (U : Int) < p → h 0 p=false)
    (t : Nat) (p : Int) (hp : (V : Int)+t < p)
    (ht : t+((U : Int)+t-p).toNat/2 ≤ N) :
    h t p=(h 0 U && cell (U+t) p) := by
  by_cases hout : (U : Int)+t < p
  · rw [mode_right_white U V h hh hi t p hout,
      Rule30Diagonals.cell_eq_false_of_gt (U+t) p (by omega)]
    simp
  · let i := (p-((V : Int)+1+t)).toNat
    let q := U-V-1
    have hiq : i ≤ q := by dsimp [i,q]; omega
    have hsi : site V t i=p := by dsimp [site,i]; omega
    have hsq : site V t q=(U : Int)+t := by dsimp [site,q]; omega
    have heq : i+(q-i)=q := Nat.add_sub_of_le hiq
    have hd : q-i=((U : Int)+t-p).toNat := by dsimp [q,i]; omega
    have hblack : rightA U V t (i+(q-i))=true := by
      rw [heq]
      change cell (U+t) (site V t q)=true
      rw [hsq]
      simpa only [Rule30Diagonals.R,Int.natCast_zero,Int.sub_zero,Int.natCast_add] using
        Rule30Diagonals.R_zero (U+t)
    have hg := HalfLine.distant_good_right_black_through (rightA U V) (rightH V h)
      (right_cut_actual U V) (right_cut_driven U V h hh) N
      (right_cut_common_through U V h N hw) (q-i) t i (by omega) hblack
    rw [heq] at hg
    have haedge : cell (U+t) ((U : Int)+t)=true := by
      simpa only [Rule30Diagonals.R,Int.natCast_zero,Int.sub_zero,Int.natCast_add] using
        Rule30Diagonals.R_zero (U+t)
    simpa [rightA,rightH,hsi,hsq,Good,haedge,mode_right_edge U V h hh hi t,
      Bool.and_comm] using hg.symm

/-- All-time consequence for every actual canonical age pair U>V. -/
theorem right_wedge_phase (U V : Nat) (hUV : V<U) (h : Nat → Int → Bool)
    (hh : Mode U V h) (hw : Common U V h)
    (hi : ∀ p, (U : Int) < p → h 0 p=false) :
    ∀ (t : Nat) (p : Int), (V : Int)+t < p → h t p=(h 0 U && cell (U+t) p) := by
  intro t p hp
  exact right_wedge_phase_through U V hUV h hh (t+((U : Int)+t-p).toNat/2)
    (fun s _ x => hw s x) hi t p hp (by omega)

theorem subset_right_white (U V : Nat) (hUV : V<U) (h : Nat → Int → Bool)
    (hs : ∀ p, (h 0 p && delta U V 0 p)=h 0 p) :
    ∀ p, (U : Int) < p → h 0 p=false := by
  intro p hp
  have ha := Rule30Diagonals.cell_eq_false_of_gt U p hp
  have hb := Rule30Diagonals.cell_eq_false_of_gt V p (by omega)
  have h := hs p
  simpa [delta,ha,hb] using h.symm

theorem right_wedge_phase_subset (U V : Nat) (hUV : V<U) (h : Nat → Int → Bool)
    (hh : Mode U V h) (hw : Common U V h)
    (hs : ∀ p, (h 0 p && delta U V 0 p)=h 0 p) :
    ∀ (t : Nat) (p : Int), (V : Int)+t < p → h t p=(h 0 U && cell (U+t) p) :=
  right_wedge_phase U V hUV h hh hw (subset_right_white U V hUV h hs)

end RightWedge

namespace BandEscape
open _root_.Ruliology.CellularAutomata.Rule30Diagonals (R R_periodic)

def step (a b h : Nat → Bool) : Nat → Bool
  | 0 => h 0
  | 1 => xor (h 1) (h 0)
  | j+2 => xor (xor (h (j+2)) ((!b j) && h (j+1))) ((!a (j+1)) && h j)

def Evolution (a b h : Nat → Nat → Bool) : Prop :=
  ∀ t j, h (t+1) j=step (a t) (b t) (h t) j

def canonical (U t j : Nat) : Bool := R j (U+t)

theorem R_periodic_mul (j q t : Nat) : R j (t+q*2^j)=R j t := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul,show t+(q*2^j+2^j)=(t+q*2^j)+2^j by omega,R_periodic,ih]

theorem R_dyadic_return (E j k : Nat) (hj : j ≤ E) : R j (2^E+k)=R j k := by
  have hp : 2^E=2^(E-j)*2^j := by
    rw [← Nat.pow_add,Nat.sub_add_cancel hj]
  rw [show 2^E+k=k+2^(E-j)*2^j by omega,R_periodic_mul]

theorem R_white (k j : Nat) (hj : 2*k < j) : R j k=false := by
  apply Rule30Jen.cell_eq_false_of_lt
  omega

theorem step_zero (a b h : Nat → Bool) (hz : ∀ j, step a b h j=false) :
    ∀ j, h j=false := by
  intro j
  induction j using Nat.strongRecOn with
  | ind j ih =>
    cases j with
    | zero => exact hz 0
    | succ j =>
      cases j with
      | zero => simpa [step,ih 0 (by omega)] using hz 1
      | succ j => simpa [step,ih j (by omega),ih (j+1) (by omega)] using hz (j+2)

theorem zero_of_later_zero (a b h : Nat → Nat → Bool) (hh : Evolution a b h) (t : Nat) :
    (∀ j, h t j=false) → ∀ j, h 0 j=false := by
  induction t with
  | zero => exact fun hz => hz
  | succ t ih =>
    intro hz
    apply ih
    apply step_zero (a t) (b t) (h t)
    intro j
    rw [← hh t j]
    exact hz j

/-- Peel two cells backward through a white part of the older background. -/
theorem peel (a b h : Nat → Nat → Bool) (hh : Evolution a b h) (k L : Nat)
    (ha : ∀ j, 2*k < j → j ≤ L → a k j=false)
    (hb : ∀ j, L ≤ j → h k j=false)
    (hn : ∀ j, 2*(k+1) ≤ j → h (k+1) j=false) :
    ∀ j, 2*k ≤ j → h k j=false := by
  have key : ∀ n : Nat, ∀ j, L-j=n → 2*k ≤ j → h k j=false := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro j hj hk
      by_cases hlarge : L ≤ j
      · exact hb j hlarge
      · have h1 := ih (L-(j+1)) (by omega) (j+1) rfl (by omega)
        have h2 := ih (L-(j+2)) (by omega) (j+2) rfl (by omega)
        have hm := hh k (j+2)
        rw [hn (j+2) (by omega)] at hm
        simpa [step,h1,h2,ha (j+1) (by omega) (by omega)] using hm.symm
  intro j hj
  exact key (L-j) j rfl hj

/-- At a dyadic return, a finite window of band confinement forces h=0. -/
theorem window_forces_zero (U E L K tau : Nat) (he : L ≤ E) (ht : U+tau=2^E)
    (hk : L ≤ 2*K)
    (b h : Nat → Nat → Bool) (hh : Evolution (canonical U) b h)
    (hb : ∀ k, k ≤ K → ∀ j, L ≤ j → h (tau+k) j=false) :
    ∀ j, h 0 j=false := by
  let A : Nat → Nat → Bool := fun k j => R j (2^E+k)
  let B : Nat → Nat → Bool := fun k j => b (tau+k) j
  let H : Nat → Nat → Bool := fun k j => h (tau+k) j
  have hH : Evolution A B H := by
    intro k j
    have hm := hh (tau+k) j
    have ht' : U+(tau+k)=2^E+k := by omega
    change h ((tau+k)+1) j=step (fun j => R j (U+(tau+k))) (b (tau+k)) (h (tau+k)) j at hm
    rw [ht'] at hm
    simpa only [H,A,B,Nat.add_assoc] using hm
  have white : ∀ k j, 2*k < j → j ≤ L → A k j=false := by
    intro k j hj hjL
    change R j (2^E+k)=false
    rw [R_dyadic_return E j k (by omega)]
    exact R_white k j hj
  have back : ∀ n : Nat, n ≤ K → ∀ j, 2*(K-n) ≤ j → H (K-n) j=false := by
    intro n
    induction n with
    | zero =>
      intro _ j hj
      exact hb K (by omega) j (by omega)
    | succ n ih =>
      intro hn
      apply peel A B H hH (K-(n+1)) L
      · exact white (K-(n+1))
      · intro j hj
        exact hb (K-(n+1)) (by omega) j hj
      · intro j hj
        have heq : K-n=(K-(n+1))+1 := by omega
        simpa only [heq] using ih (by omega) j (by omega)
  have hz : ∀ j, h tau j=false := by
    intro j
    simpa [H] using back K (by omega) j (by omega)
  exact zero_of_later_zero (canonical U) b h hh tau hz

theorem small_pow (n : Nat) : n < 2^n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

/-- No W, no second-background recurrence and no initial subset premise. -/
theorem no_eventually_bounded_band (U : Nat) (b h : Nat → Nat → Bool)
    (hh : Evolution (canonical U) b h) (hne : ∃ j, h 0 j=true) :
    ¬ ∃ T L : Nat, ∀ t, T ≤ t → ∀ j, L ≤ j → h t j=false := by
  rintro ⟨T,L,hb⟩
  let E := U+T+L+1
  let tau := 2^E-U
  have hp := small_pow E
  have hreset : U+tau=2^E := by dsimp [E,tau] at *; omega
  have htau : T ≤ tau := by dsimp [E,tau] at *; omega
  have hz := window_forces_zero U E L L tau (by dsimp [E]; omega) hreset (by omega) b h hh
    (fun k _ j hj => hb (tau+k) (by omega) j hj)
  obtain ⟨j,hj⟩ := hne
  rw [hz j] at hj
  cases hj

/-- An explicit finite escape window after any chosen dyadic return. -/
theorem escapes_near_reset (U E L tau : Nat) (he : L ≤ E) (ht : U+tau=2^E)
    (b h : Nat → Nat → Bool) (hh : Evolution (canonical U) b h)
    (hne : ∃ j, h 0 j=true) :
    ∃ k, k ≤ (L+1)/2 ∧ ∃ j, L ≤ j ∧ h (tau+k) j=true := by
  apply Classical.byContradiction
  intro hn
  have hb : ∀ k, k ≤ (L+1)/2 → ∀ j, L ≤ j → h (tau+k) j=false := by
    intro k hk j hj
    cases hc : h (tau+k) j with
    | false => rfl
    | true => exact False.elim (hn ⟨k,hk,j,hj,hc⟩)
  have hz := window_forces_zero U E L ((L+1)/2) tau he ht (by omega) b h hh hb
  obtain ⟨j,hj⟩ := hne
  rw [hz j] at hj
  cases hj

theorem arbitrarily_deep_after_any_time (U : Nat) (b h : Nat → Nat → Bool)
    (hh : Evolution (canonical U) b h) (hne : ∃ j, h 0 j=true) (T L : Nat) :
    ∃ t, T ≤ t ∧ ∃ j, L ≤ j ∧ h t j=true := by
  apply Classical.byContradiction
  intro hn
  apply no_eventually_bounded_band U b h hh hne
  refine ⟨T,L,?_⟩
  intro t ht j hj
  cases hc : h t j with
  | false => rfl
  | true => exact False.elim (hn ⟨t,ht,j,hj,hc⟩)


namespace Ordinary
open _root_.Ruliology.CellularAutomata.Rule30Jen (cell)

def read (U : Nat) (h : Nat → Int → Bool) (t j : Nat) : Bool :=
  h t ((U : Int)+t-j)
def readB (U V t j : Nat) : Bool := cell (V+t) ((U : Int)+t-j)

theorem read_evolution (U V : Nat) (hUV : V ≤ U) (h : Nat → Int → Bool)
    (hh : RightWedge.Mode U V h) (hi : ∀ p, (U : Int) < p → h 0 p=false) :
    Evolution (canonical U) (readB U V) (read U h) := by
  intro t j
  cases j with
  | zero =>
    change h (t+1) ((U : Int)+(t+1)-0)=h t ((U : Int)+t-0)
    simp only [Int.sub_zero]
    have h1 := RightWedge.mode_right_edge U V h hh hi (t+1)
    have h0 := RightWedge.mode_right_edge U V h hh hi t
    simpa only [Int.natCast_add,Int.natCast_one] using h1.trans h0.symm
  | succ j =>
    cases j with
    | zero =>
      have hm := hh t ((U : Int)+t)
      unfold RightWedge.dStep at hm
      have hb := Rule30Diagonals.cell_eq_false_of_gt (V+t) ((U : Int)+t+1) (by omega)
      have hz := RightWedge.mode_right_white U V h hh hi t ((U : Int)+t+1) (by omega)
      rw [hb,hz] at hm
      change h (t+1) ((U : Int)+(t+1)-1)=_
      rw [show (U : Int)+(t+1)-1=(U : Int)+t by omega]
      simpa [read,step] using hm
    | succ j =>
      let p : Int := (U : Int)+(t+1)-(j+2)
      have hl : p-1=(U : Int)+t-(j+2) := by dsimp [p]; omega
      have hc : p=(U : Int)+t-(j+1) := by dsimp [p]; omega
      have hr : p+1=(U : Int)+t-j := by dsimp [p]; omega
      have hm := hh t p
      unfold RightWedge.dStep at hm
      rw [hl,hr,hc] at hm
      change h (t+1) p=step (canonical U t) (readB U V t) (read U h t) (j+2)
      rw [hc]
      simpa [read,readB,step,canonical,R,Int.natCast_add] using hm

theorem read_nonzero (U : Nat) (h : Nat → Int → Bool)
    (hi : ∀ p, (U : Int) < p → h 0 p=false) (hne : ∃ p, h 0 p=true) :
    ∃ j, read U h 0 j=true := by
  obtain ⟨p,hp⟩ := hne
  have hpU : p ≤ U := by
    apply Classical.byContradiction
    intro hn
    rw [hi p (by omega)] at hp
    cases hp
  refine ⟨((U : Int)-p).toNat,?_⟩
  have he : (U : Int)+0-(((U : Int)-p).toNat : Int)=p := by omega
  simpa only [read,Int.natCast_zero,he] using hp

/-- Ordinary coordinates: every nonzero initially upper-bounded D field
visits arbitrarily far behind the older moving right front, after every time.
No common-gauge or initial subset hypothesis is used. -/
theorem arbitrarily_far_behind_front (U V : Nat) (hUV : V ≤ U)
    (h : Nat → Int → Bool) (hh : RightWedge.Mode U V h)
    (hi : ∀ p, (U : Int) < p → h 0 p=false) (hne : ∃ p, h 0 p=true)
    (T L : Nat) :
    ∃ t, T ≤ t ∧ ∃ p : Int, p ≤ (U : Int)+t-L ∧ h t p=true := by
  obtain ⟨t,ht,j,hj,hblack⟩ := arbitrarily_deep_after_any_time U (readB U V) (read U h)
    (read_evolution U V hUV h hh hi) (read_nonzero U h hi hne) T L
  exact ⟨t,ht,(U : Int)+t-j,by omega,hblack⟩

end Ordinary

end BandEscape

namespace ObserverConnection
open _root_.Ruliology.CellularAutomata.Rule30Jen (cell)
open _root_.Ruliology.CellularAutomata.Rule30Realization (evol)
open _root_.Ruliology.CellularAutomata.Rule30DividedDifference
set_option autoImplicit false

theorem canonical_evol (U : Nat) : ∀ (t : Nat) (p : Int),
    evol (cell U) t p=cell (U+t) p
  | 0,p => rfl
  | t+1,p => by
      change rule (evol (cell U) t (p-1)) (evol (cell U) t p)
        (evol (cell U) t (p+1)) =
        rule (cell (U+t) (p-1)) (cell (U+t) p) (cell (U+t) (p+1))
      rw [canonical_evol,canonical_evol,canonical_evol]

def canonicalMode (U V : Nat) (x : Int → Bool) : Nat → Int → Bool :=
  Front.mode (cell U) (cell V) zeroGauge x

/-- The observer criterion's exact zero-gauge field obeys the D equation
used by the exterior and band-escape theorems. -/
theorem canonical_mode_equation (U V : Nat) (x : Int → Bool) :
    RightWedge.Mode U V (canonicalMode U V x) := by
  intro t p
  change Front.step (cell U) (cell V) zeroGauge t (canonicalMode U V x t) p =
    RightWedge.dStep U V (canonicalMode U V x) t p
  simp only [Front.step,zeroGauge,Bool.false_and,Bool.xor_false,mix,
    canonical_evol,RightWedge.dStep]

theorem wedge_eq_iff : ∀ a b c d : Bool,
    xor (c && b) (a && d)=false ↔ Good a b c d := by
  unfold Good
  decide +kernel

/-- Literal equality of the two common-field predicates in canonical coordinates. -/
theorem canonical_common_iff (U V : Nat) (h : Nat → Int → Bool) :
    CommonField (cell U) (cell V) h ↔ RightWedge.Common U V h := by
  constructor
  · intro hw t p
    apply (wedge_eq_iff _ _ _ _).mp
    simpa only [canonical_evol,RightWedge.delta] using hw t p
  · intro hw t p
    have hh := (wedge_eq_iff _ _ _ _).mpr (hw t p)
    simpa only [canonical_evol,RightWedge.delta] using hh

/-- Exterior coherence applied directly to a mode of ObserverCriterion. -/
theorem observer_mode_right_wedge (U V : Nat) (hUV : V<U) (x : Int → Bool)
    (hw : CommonField (cell U) (cell V) (canonicalMode U V x))
    (hs : ∀ p, x p=true → xor (cell U p) (cell V p)=true) :
    ∀ (t : Nat) (p : Int), (V : Int)+t<p →
      canonicalMode U V x t p=(x U && cell (U+t) p) := by
  apply RightWedge.right_wedge_phase_subset U V hUV (canonicalMode U V x)
    (canonical_mode_equation U V x) ((canonical_common_iff U V _).mp hw)
  intro p
  change (x p && RightWedge.delta U V 0 p)=x p
  simp only [RightWedge.delta,Nat.add_zero]
  cases hx : x p with
  | false => simp only [Bool.false_and]
  | true => rw [hs p hx];rfl

end ObserverConnection
/-! ## Right-wedge dichotomy, explicit dyadic escape in ordinary coordinates, and observer-mode front escape -/

/-- **Right-Wedge Dichotomy (`right_wedge_dichotomy`):**
under `RightWedge.Mode U V h` and `RightWedge.Common U V h` with `V < U` and `h 0 p = false` for `p > U`,
if `h 0 U = false` then `h t p = false` throughout `(V : Int) + t < p`, whereas if `h 0 U = true`
then `h t p = Rule30Jen.cell (U + t) p` throughout `(V : Int) + t < p`. -/
theorem right_wedge_dichotomy (U V : Nat) (hUV : V < U) (h : Nat → Int → Bool)
    (hh : RightWedge.Mode U V h) (hw : RightWedge.Common U V h)
    (hi : ∀ p : Int, (U : Int) < p → h 0 p = false) :
    (h 0 U = false → ∀ (t : Nat) (p : Int), (V : Int) + t < p → h t p = false) ∧
    (h 0 U = true → ∀ (t : Nat) (p : Int), (V : Int) + t < p → h t p = Rule30Jen.cell (U + t) p) := by
  have hph := RightWedge.right_wedge_phase U V hUV h hh hw hi
  refine ⟨fun h0 t p hp => by rw [hph t p hp, h0, Bool.false_and],
          fun h1 t p hp => by rw [hph t p hp, h1, Bool.true_and]⟩

/-- **Observer-Mode Right-Wedge Dichotomy (`observer_mode_right_wedge_dichotomy`).** -/
theorem observer_mode_right_wedge_dichotomy (U V : Nat) (hUV : V < U) (x : Int → Bool)
    (hw : Rule30DividedDifference.CommonField (Rule30Jen.cell U) (Rule30Jen.cell V)
      (ObserverConnection.canonicalMode U V x))
    (hs : ∀ p : Int, x p = true → xor (Rule30Jen.cell U p) (Rule30Jen.cell V p) = true) :
    (x U = false → ∀ (t : Nat) (p : Int), (V : Int) + t < p →
      ObserverConnection.canonicalMode U V x t p = false) ∧
    (x U = true → ∀ (t : Nat) (p : Int), (V : Int) + t < p →
      ObserverConnection.canonicalMode U V x t p = Rule30Jen.cell (U + t) p) := by
  have hobs := ObserverConnection.observer_mode_right_wedge U V hUV x hw hs
  refine ⟨fun hx0 t p hp => by rw [hobs t p hp, hx0, Bool.false_and],
          fun hx1 t p hp => by rw [hobs t p hp, hx1, Bool.true_and]⟩

/-- **Explicit Dyadic Escape Window in Ordinary Coordinates (`ordinary_escapes_near_dyadic_reset`):**
at any dyadic return `U + tau = 2^E` with `L ≤ E` and `V ≤ U`, every non-zero upper-bounded
`RightWedge.Mode U V h` visits `p ≤ (U : Int) + (tau + k) - L` at some step `k ≤ (L + 1) / 2`. -/
theorem ordinary_escapes_near_dyadic_reset (U V E L tau : Nat) (hUV : V ≤ U)
    (he : L ≤ E) (ht : U + tau = 2 ^ E) (h : Nat → Int → Bool)
    (hh : RightWedge.Mode U V h) (hi : ∀ p : Int, (U : Int) < p → h 0 p = false)
    (hne : ∃ p : Int, h 0 p = true) :
    ∃ k, k ≤ (L + 1) / 2 ∧ ∃ p : Int, p ≤ (U : Int) + (tau + k) - L ∧ h (tau + k) p = true := by
  obtain ⟨k, hk, j, hj, hblack⟩ := BandEscape.escapes_near_reset U E L tau he ht
    (BandEscape.Ordinary.readB U V) (BandEscape.Ordinary.read U h)
    (BandEscape.Ordinary.read_evolution U V hUV h hh hi)
    (BandEscape.Ordinary.read_nonzero U h hi hne)
  exact ⟨k, hk, (U : Int) + (tau + k) - j, by omega, hblack⟩

/-- **Unbounded Escape Behind the Front for `ObserverConnection.canonicalMode` (`canonical_mode_arbitrarily_far_behind_front`).** -/
theorem canonical_mode_arbitrarily_far_behind_front (U V : Nat) (hUV : V ≤ U) (x : Int → Bool)
    (hi : ∀ p : Int, (U : Int) < p → x p = false) (hne : ∃ p : Int, x p = true)
    (T L : Nat) :
    ∃ t, T ≤ t ∧ ∃ p : Int, p ≤ (U : Int) + t - L ∧
      ObserverConnection.canonicalMode U V x t p = true :=
  BandEscape.Ordinary.arbitrarily_far_behind_front U V hUV
    (ObserverConnection.canonicalMode U V x)
    (ObserverConnection.canonical_mode_equation U V x) hi hne T L

end Ruliology.CellularAutomata.Rule30CommonGauge
