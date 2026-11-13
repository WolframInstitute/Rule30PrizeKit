module

public import Ruliology.CellularAutomata.Rule30Prize
public import Ruliology.CellularAutomata.Rule30Realization

/-!
# Exact XOR superposition rigidity for ordinary Rule 30

For arbitrary histories on natural times and all integer sites, their pointwise XOR
is another Rule 30 history if and only if one is zero or they are identical.
`xor_history_iff` states the ordinary left/center/right recurrence explicitly.
`standard_two_partners` gives the corresponding nonzero-history partner statement.
There are no support, boundary or periodicity hypotheses.

The elementary local quadratic defect is an adjacent determinant on paired Boolean
colors. Strong induction on the distance between incompatible colors rules out a
persistent zero gap. Half-line restrictions transfer this collision argument to
all integer sites; a proved shear returns to ordinary coordinates.
Only the general argument and its proof dependencies are included.

-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30XorRigidity

namespace HalfLine

def rule (a b c : Bool) : Bool := Ruliology.CellularAutomata.Rule30Jen.rule a b c

def Actual (X : Nat → Nat → Bool) : Prop :=
 ∀ t i, X (t+1) i = rule (X t i) (X t (i+1)) (X t (i+2))

def add (A B : Nat → Nat → Bool) : Nat → Nat → Bool := fun t i => A t i ^^ B t i

set_option maxHeartbeats 4000000 in
/-- The exact nonlinear cross defect; all 64 local assignments are kernel checked. -/
theorem local_cross : ∀ a b c d e f : Bool,
 rule (a ^^ d) (b ^^ e) (c ^^ f) = (rule a b c ^^ rule d e f) ↔
 (b && f)=(c && e) := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem actual_add_iff (A B : Nat → Nat → Bool) (ha : Actual A) (hb : Actual B) :
 Actual (add A B) ↔ ∀ t i, (A t (i+1) && B t (i+2))=(A t (i+2) && B t (i+1)) := by
 constructor
 · intro hc t i
   have he := hc t i
   change (A (t+1) i ^^ B (t+1) i) = _ at he
   rw [ha t i, hb t i] at he
   exact (local_cross _ _ _ _ _ _).mp he.symm
 · intro hd t i
   change (A (t+1) i ^^ B (t+1) i) = _
   rw [ha t i, hb t i]
   exact ((local_cross _ _ _ _ _ _).mpr (hd t i)).symm

def Good (a b c d : Bool) : Prop := (a && d)=(c && b)

set_option maxHeartbeats 4000000 in
theorem good_self (a b : Bool) : Good a b a b := rfl
set_option maxHeartbeats 4000000 in
theorem good_symm (a b c d : Bool) : Good a b c d → Good c d a b := by
 unfold Good
 intro h
 simpa [Bool.and_comm] using h.symm

set_option maxHeartbeats 4000000 in
theorem middle_zero : ∀ a b c d e f : Bool,
 ¬ Good a b e f → Good a b c d → Good c d e f → c=false ∧ d=false := by
 unfold Good; decide +kernel

set_option maxHeartbeats 4000000 in
theorem gap_two : ∀ a b c d e f : Bool,
 Good c d e f → Good (rule a false c) (rule b false d)
 (rule false c e) (rule false d f) → Good a b c d := by unfold Good; decide +kernel

set_option maxHeartbeats 4000000 in
theorem gap_large : ∀ a b c d : Bool,
 Good (rule a false false) (rule b false false)
 (rule false false c) (rule false false d) → Good a b c d := by unfold Good; decide +kernel

set_option maxHeartbeats 4000000 in
/-- Any two sites at positive indices are projectively compatible at every time. -/
theorem distant_good (A B : Nat → Nat → Bool) (ha : Actual A) (hb : Actual B)
 (hc : Actual (add A B)) (d : Nat) :
 ∀ t p, 1≤p → Good (A t p) (B t p) (A t (p+d)) (B t (p+d)) := by
 have adj := (actual_add_iff A B ha hb).mp hc
 induction d using Nat.strongRecOn with
 | ind d ih =>
   intro t p hp
   by_cases hd0 : d=0
   · subst d
     exact good_self _ _
   by_cases hd1 : d=1
   · subst d
     have h := adj t (p-1)
     simpa [Good, show p-1+1=p by omega, show p-1+2=p+1 by omega] using h
   apply Classical.byContradiction
   intro bad
   have mid : ∀ k, p<k → k<p+d → A t k=false ∧ B t k=false := by
     intro k hpk hkd
     have l := ih (k-p) (by omega) t p hp
     have r := ih (p+d-k) (by omega) t k (by omega)
     rw [show p+(k-p)=k by omega] at l
     rw [show k+(p+d-k)=p+d by omega] at r
     exact middle_zero _ _ _ _ _ _ bad l r
   by_cases hd2 : d=2
   · subst d
     obtain ⟨az,bz⟩ := mid (p+1) (by omega) (by omega)
     have next := ih 1 (by omega) (t+1) p hp
     have right := adj t (p+1)
     change Good (A t (p+2)) (B t (p+2)) (A t (p+3)) (B t (p+3)) at right
     rw [ha t p, hb t p, ha t (p+1), hb t (p+1), az,bz,
       show p+1+1=p+2 by omega, show p+1+2=p+3 by omega] at next
     exact bad (gap_two _ _ _ _ _ _ right next)
   · obtain ⟨a1,b1⟩ := mid (p+1) (by omega) (by omega)
     obtain ⟨a2,b2⟩ := mid (p+2) (by omega) (by omega)
     obtain ⟨az,bz⟩ := mid (p+d-2) (by omega) (by omega)
     obtain ⟨az1,bz1⟩ := mid (p+d-1) (by omega) (by omega)
     have next := ih (d-2) (by omega) (t+1) p hp
     rw [show p+(d-2)=p+d-2 by omega, ha t p, hb t p,
       ha t (p+d-2), hb t (p+d-2),
       show p+d-2+1=p+d-1 by omega, show p+d-2+2=p+d by omega,
       a1,b1,a2,b2,az,bz,az1,bz1] at next
     exact bad (gap_large _ _ _ _ next)

set_option maxHeartbeats 4000000 in
theorem all_good (A B : Nat → Nat → Bool) (ha : Actual A) (hb : Actual B)
 (hc : Actual (add A B)) (t p q : Nat) (hp : 1≤p) (hq : 1≤q) :
 Good (A t p) (B t p) (A t q) (B t q) := by
 by_cases h : p≤q
 · have he := distant_good A B ha hb hc (q-p) t p hp
   simpa [show p+(q-p)=q by omega] using he
 · apply good_symm
   have he := distant_good A B ha hb hc (p-q) t q hq
   simpa [show q+(p-q)=p by omega] using he

end HalfLine

open HalfLine (rule)

def Actual (A : Nat → Int → Bool) : Prop :=
 ∀ t i, A (t+1) i = rule (A t i) (A t (i+1)) (A t (i+2))
def add (A B : Nat → Int → Bool) : Nat → Int → Bool := fun t i => A t i ^^ B t i
def zero : Nat → Int → Bool := fun _ _ => false
def cut (A : Nat → Int → Bool) (k : Int) : Nat → Nat → Bool := fun t j => A t (k+j)

set_option maxHeartbeats 4000000 in
theorem cut_actual (A : Nat → Int → Bool) (ha : Actual A) (k : Int) :
 HalfLine.Actual (cut A k) := by
 intro t j
 change A (t+1) (k+j)=rule (A t (k+j)) (A t (k+((j+1:Nat):Int))) (A t (k+((j+2:Nat):Int)))
 rw [show k+((j+1:Nat):Int)=k+(j:Int)+1 by omega,
   show k+((j+2:Nat):Int)=k+(j:Int)+2 by omega]
 exact ha t (k+j)

set_option maxHeartbeats 4000000 in
theorem all_good (A B : Nat → Int → Bool) (ha : Actual A) (hb : Actual B)
 (hc : Actual (add A B)) (t : Nat) (p q : Int) :
 HalfLine.Good (A t p) (B t p) (A t q) (B t q) := by
 let k := min p q - 1
 let u := (p-k).toNat
 let v := (q-k).toNat
 have kp : k < p := by dsimp [k]; omega
 have kq : k < q := by dsimp [k]; omega
 have hu : (u : Int)=p-k := Int.toNat_of_nonneg (by omega)
 have hv : (v : Int)=q-k := Int.toNat_of_nonneg (by omega)
 have up : 1≤u := by omega
 have vp : 1≤v := by omega
 have hh : HalfLine.Actual (HalfLine.add (cut A k) (cut B k)) :=
   cut_actual (add A B) hc k
 have h := HalfLine.all_good (cut A k) (cut B k)
   (cut_actual A ha k) (cut_actual B hb k) hh t u v up vp
 simpa only [cut,hu,hv,show k+(p-k)=p by omega,show k+(q-k)=q by omega] using h

set_option maxHeartbeats 4000000 in
theorem unique (A B : Nat → Int → Bool) (ha : Actual A) (hb : Actual B)
 (h0 : ∀ i, A 0 i=B 0 i) : A=B := by
 funext t i
 have ht : ∀ t i, A t i=B t i := by
   intro t
   induction t with
   | zero => exact h0
   | succ t ih => intro i; rw [ha t i,hb t i,ih i,ih (i+1),ih (i+2)]
 exact ht t i

set_option maxHeartbeats 4000000 in
theorem zero_actual : Actual zero := by intro t i; rfl

set_option maxHeartbeats 4000000 in
theorem add_zero (A : Nat → Int → Bool) : add A zero=A := by
 funext t i; simp [add,zero]
set_option maxHeartbeats 4000000 in
theorem zero_add (A : Nat → Int → Bool) : add zero A=A := by
 funext t i; simp [add,zero]
set_option maxHeartbeats 4000000 in
theorem add_self (A : Nat → Int → Bool) : add A A=zero := by
 funext t i; simp [add,zero]

set_option maxHeartbeats 4000000 in
/-- No boundary or finiteness premise: only a zero input or identical initial rows. -/
theorem actual_add_classification (A B : Nat → Int → Bool) (ha : Actual A) (hb : Actual B) :
 Actual (add A B) ↔
 (∀ i, A 0 i=false) ∨ (∀ i, B 0 i=false) ∨ (∀ i, A 0 i=B 0 i) := by
 constructor
 · intro hc
   by_cases hz : ∀ i, A 0 i=false
   · exact Or.inl hz
   · have ex : ∃ p, A 0 p=true := by
       apply Classical.byContradiction
       intro hn
       apply hz
       intro p
       cases hp : A 0 p with
       | false => rfl
       | true => exact False.elim (hn ⟨p,hp⟩)
     obtain ⟨p,hp⟩ := ex
     cases bp : B 0 p with
     | false =>
       right; left; intro q
       have h := all_good A B ha hb hc 0 p q
       simpa [HalfLine.Good,hp,bp] using h.symm
     | true =>
       right; right; intro q
       have h := all_good A B ha hb hc 0 p q
       simpa [HalfLine.Good,hp,bp] using h.symm
 · intro h
   rcases h with h|h|h
   · have he := unique A zero ha zero_actual h
     simpa [he,zero_add] using hb
   · have he := unique B zero hb zero_actual h
     simpa [he,add_zero] using ha
   · have he := unique A B ha hb h
     simpa [he,add_self] using zero_actual

set_option maxHeartbeats 4000000 in
/-- Classical left/center/right orientation of Rule 30. -/
def Standard (R : Nat → Int → Bool) : Prop :=
 ∀ t x, R (t+1) x = rule (R t (x-1)) (R t x) (R t (x+1))
def shear (R : Nat → Int → Bool) : Nat → Int → Bool := fun t i => R t ((t : Int)+i)

set_option maxHeartbeats 4000000 in
theorem shear_actual_iff (R : Nat → Int → Bool) : Actual (shear R) ↔ Standard R := by
 constructor
 · intro h t x
   have hh := h t (x-(t+1))
   simpa [shear, show (t : Int)+1+(x-((t : Int)+1))=x by omega,
     show (t : Int)+(x-((t : Int)+1))=x-1 by omega,
     show (t : Int)+(x-((t : Int)+1)+1)=x by omega,
     show (t : Int)+(x-((t : Int)+1)+2)=x+1 by omega] using hh
 · intro h t i
   change R (t+1) (((t+1:Nat):Int)+i) = rule (R t ((t:Int)+i))
     (R t ((t:Int)+(i+1))) (R t ((t:Int)+(i+2)))
   rw [show (((t+1:Nat):Int)+i)=(t:Int)+1+i by omega]
   have hh := h t ((t : Int)+1+i)
   rw [show (t:Int)+1+i-1=(t:Int)+i by omega,
     show (t:Int)+1+i+1=(t:Int)+(i+2) by omega,
     show (t:Int)+1+i=(t:Int)+(i+1) by omega] at hh
   simpa only [show (t:Int)+1+i=(t:Int)+(i+1) by omega] using hh

set_option maxHeartbeats 4000000 in
theorem standard_add_classification (A B : Nat → Int → Bool) (ha : Standard A) (hb : Standard B) :
 Standard (add A B) ↔
 (∀ i, A 0 i=false) ∨ (∀ i, B 0 i=false) ∨ (∀ i, A 0 i=B 0 i) := by
 have hc := actual_add_classification (shear A) (shear B)
   ((shear_actual_iff A).mpr ha) ((shear_actual_iff B).mpr hb)
 change Actual (shear (add A B)) ↔ _ at hc
 simpa [shear_actual_iff,shear] using hc

set_option maxHeartbeats 4000000 in
theorem standard_unique (A B : Nat → Int → Bool) (ha : Standard A) (hb : Standard B)
 (h0 : ∀ i, A 0 i=B 0 i) : A=B := by
 funext t i
 have ht : ∀ t i, A t i=B t i := by
   intro t
   induction t with
   | zero => exact h0
   | succ t ih => intro i; rw [ha t i,hb t i,ih (i-1),ih i,ih (i+1)]
 exact ht t i

set_option maxHeartbeats 4000000 in
theorem zero_standard : Standard zero := by intro t i; rfl

set_option maxHeartbeats 4000000 in
theorem standard_full_classification (A B : Nat → Int → Bool)
 (ha : Standard A) (hb : Standard B) :
 Standard (add A B) ↔ A=zero ∨ B=zero ∨ A=B := by
 rw [standard_add_classification A B ha hb]
 constructor
 · intro h
   rcases h with h|h|h
   · exact Or.inl (standard_unique A zero ha zero_standard h)
   · exact Or.inr (Or.inl (standard_unique B zero hb zero_standard h))
   · exact Or.inr (Or.inr (standard_unique A B ha hb h))
 · intro h
   rcases h with h|h|h
   · left; rw [h]; intro i; rfl
   · right; left; rw [h]; intro i; rfl
   · right; right; rw [h]; intro i; rfl

/-- Every nonzero ordinary whole-line orbit has precisely two XOR partners. -/
theorem standard_two_partners (A B : Nat → Int → Bool) (ha : Standard A) (hb : Standard B)
 (hn : A≠zero) : Standard (add A B) ↔ B=zero ∨ B=A := by
 rw [standard_full_classification A B ha hb]
 constructor
 · intro h
   rcases h with h|h|h
   · exact False.elim (hn h)
   · exact Or.inl h
   · exact Or.inr h.symm
 · intro h
   rcases h with h|h
   · exact Or.inr (Or.inl h)
   · exact Or.inr (Or.inr h.symm)

set_option maxHeartbeats 4000000 in
/-- Explicit ordinary whole-line Rule 30 statement: only zero or identical histories. -/
theorem xor_history_iff (A B : Nat → Int → Bool)
 (ha : ∀ t x, A (t+1) x = Ruliology.CellularAutomata.Rule30Jen.rule
   (A t (x-1)) (A t x) (A t (x+1)))
 (hb : ∀ t x, B (t+1) x = Ruliology.CellularAutomata.Rule30Jen.rule
   (B t (x-1)) (B t x) (B t (x+1))) :
 (∀ t x, (A (t+1) x ^^ B (t+1) x) = Ruliology.CellularAutomata.Rule30Jen.rule
   (A t (x-1) ^^ B t (x-1)) (A t x ^^ B t x) (A t (x+1) ^^ B t (x+1))) ↔
 A = (fun _ _ => false) ∨ B = (fun _ _ => false) ∨ A = B :=
 standard_full_classification A B ha hb

/-! ## F_2 vector-space laws of `add`, self-cancellation, and official `evol` XOR rigidity -/

/-- **F_2 Vector-Space Laws of `add`, Self-Cancellation `add A B = zero ↔ A = B`, and `evol` XOR Rigidity (`add_f2_laws_and_evol_xor_iff`).** -/
theorem add_f2_laws_and_evol_xor_iff (A B C : Nat → Int → Bool) (x y : Int → Bool) :
    add A B = add B A ∧
    add (add A B) C = add A (add B C) ∧
    (add A B = zero ↔ A = B) ∧
    (Standard (add (Rule30Realization.evol x) (Rule30Realization.evol y)) ↔
      (∀ p, x p = false) ∨ (∀ p, y p = false) ∨ x = y) := by
  have hcomm : add A B = add B A := by
    funext t i; unfold add; exact Bool.xor_comm (A t i) (B t i)
  have hassoc : add (add A B) C = add A (add B C) := by
    funext t i; unfold add; exact Bool.xor_assoc (A t i) (B t i) (C t i)
  have hcancel : add A B = zero ↔ A = B := by
    constructor
    · intro h
      funext t i
      have hti : xor (A t i) (B t i) = false := congrFun (congrFun h t) i
      revert hti; cases A t i <;> cases B t i <;> decide
    · rintro rfl
      funext t i; unfold add zero; cases A t i <;> rfl
  have hstd_x : Standard (Rule30Realization.evol x) := fun _ _ => rfl
  have hstd_y : Standard (Rule30Realization.evol y) := fun _ _ => rfl
  refine ⟨hcomm, hassoc, hcancel, ?_⟩
  rw [standard_add_classification (Rule30Realization.evol x) (Rule30Realization.evol y) hstd_x hstd_y]
  constructor
  · rintro (hx | hy | hxy)
    · exact Or.inl hx
    · exact Or.inr (Or.inl hy)
    · exact Or.inr (Or.inr (funext hxy))
  · rintro (hx | hy | rfl)
    · exact Or.inl hx
    · exact Or.inr (Or.inl hy)
    · exact Or.inr (Or.inr (fun _ => rfl))

end Ruliology.CellularAutomata.Rule30XorRigidity
