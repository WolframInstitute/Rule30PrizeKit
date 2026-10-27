module

public import Ruliology.CellularAutomata.Rule30Ether
public import Ruliology.CellularAutomata.Rule30Prize

/-!
# Ordered birth inheritance between actual physical mismatch episodes

Under common center forcing, a column-one mismatch death terminates a
surviving column-two episode at the following tick. Thus an interval of
continuous column-two mismatch supports at most two column-one births;
any second birth is terminal. The literal single-seed age-pair corollaries
retain actual ancestry. No upper birth budget or prize result is claimed.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30BirthEpisodeInheritance

open Rule30Jen Rule30Ether

def difference (F G : Nat → Nat → Bool) (i t : Nat) : Bool := xor (F t i) (G t i)
def Birth (f : Nat → Bool) (t : Nat) : Prop := f t=false ∧ f (t+1)=true

theorem death_boolean (c r z w v rb zb wb vb : Bool)
    (hr : xor r rb=true) (hz : xor z zb=true)
    (hd : xor (rule c r z) (rule c rb zb)=false)
    (hz1 : xor (rule r z w) (rule rb zb wb)=true) :
    xor (rule (rule c r z) (rule r z w) (rule z w v))
      (rule (rule c rb zb) (rule rb zb wb) (rule zb wb vb)) = false := by
  revert hr hz hd hz1
  cases c <;> cases r <;> cases z <;> cases w <;> cases v <;>
    cases rb <;> cases zb <;> cases wb <;> cases vb <;> decide

/-- The common center is needed only at the death source tick. -/
theorem death_termination {F G : Nat → Nat → Bool}
    (hF : IsR30 F) (hG : IsR30 G) (d : Nat)
    (hc : F d 0=G d 0) (h1 : difference F G 1 d=true)
    (hdeath : difference F G 1 (d+1)=false)
    (h2 : difference F G 2 d=true) (h2next : difference F G 2 (d+1)=true) :
    difference F G 2 (d+2)=false := by
  have hd : xor (rule (F d 0) (F d 1) (F d 2))
      (rule (F d 0) (G d 1) (G d 2))=false := by
    simpa only [difference,hF d 0,hG d 0,←hc] using hdeath
  have hp : xor (rule (F d 1) (F d 2) (F d 3))
      (rule (G d 1) (G d 2) (G d 3))=true := by
    simpa only [difference,hF d 1,hG d 1] using h2next
  have h := death_boolean (F d 0) (F d 1) (F d 2) (F d 3) (F d 4)
    (G d 1) (G d 2) (G d 3) (G d 4) h1 h2 hd hp
  simpa only [difference,show d+2=(d+1)+1 by omega,
    hF (d+1) 1,hG (d+1) 1,hF d 0,hG d 0,hF d 1,hG d 1,hF d 2,hG d 2,←hc] using h

theorem exists_death (f : Nat → Bool) (a : Nat) : ∀ n,
    f a=true → f (a+n)=false →
    ∃ d, a≤d ∧ d<a+n ∧ f d=true ∧ f (d+1)=false := by
  intro n
  induction n with
  | zero => intro ha hn; simp only [Nat.add_zero,ha] at hn; contradiction
  | succ n ih =>
      intro ha hn
      cases hm : f (a+n) with
      | false =>
          obtain ⟨d,hda,hdb,hd,hd1⟩ := ih ha hm
          exact ⟨d,hda,by omega,hd,hd1⟩
      | true =>
          exact ⟨a+n,by omega,by omega,hm,by simpa only [Nat.add_assoc] using hn⟩

/-- Two births in a common-driver parent interval force the second to be its last tick. -/
theorem terminal_second_birth {F G : Nat → Nat → Bool}
    (hF : IsR30 F) (hG : IsR30 G) (A Z a b : Nat)
    (ha : A≤a) (hab : a<b) (hb : b≤Z)
    (hc : ∀ t, A≤t → t≤Z → F t 0=G t 0)
    (hp : ∀ t, A≤t → t≤Z → difference F G 2 t=true)
    (ba : Birth (difference F G 1) a) (bb : Birth (difference F G 1) b) :
    b=Z ∧ difference F G 2 (b+1)=false := by
  have hend : (a+1)+(b-(a+1))=b := by omega
  obtain ⟨d,hda,hdb,hd,hd1⟩ := exists_death (difference F G 1) (a+1)
    (b-(a+1)) ba.2 (by simpa only [hend] using bb.1)
  rw [hend] at hdb
  have hk := death_termination hF hG d (hc d (by omega) (by omega)) hd hd1
    (hp d (by omega) (by omega)) (hp (d+1) (by omega) (by omega))
  have hz : Z<d+2 := by
    by_cases hn : Z<d+2
    · exact hn
    · have htrue := hp (d+2) (by omega) (by omega)
      rw [htrue] at hk
      contradiction
  refine ⟨by omega,?_⟩
  simpa only [show d+2=b+1 by omega] using hk

/-- This is the cardinality-at-most-two statement without introducing a finite-set library. -/
theorem no_ordered_three_births {F G : Nat → Nat → Bool}
    (hF : IsR30 F) (hG : IsR30 G) (A Z a b c : Nat)
    (ha : A≤a) (hab : a<b) (hbc : b<c) (hcZ : c≤Z)
    (hc : ∀ t, A≤t → t≤Z → F t 0=G t 0)
    (hp : ∀ t, A≤t → t≤Z → difference F G 2 t=true)
    (ba : Birth (difference F G 1) a) (bb : Birth (difference F G 1) b)
    (_bc : Birth (difference F G 1) c) : False := by
  have h := (terminal_second_birth hF hG A Z a b ha hab (by omega) hc hp ba bb).1
  omega

def seedHistory (age : Nat) (t i : Nat) : Bool := cell (age+t) (i:Int)

theorem seedHistory_actual (age : Nat) : IsR30 (seedHistory age) := by
  intro t p
  change cell ((age+t)+1) ((p+1:Nat):Int) =
    rule (cell (age+t) (p:Int)) (cell (age+t) ((p+1:Nat):Int))
      (cell (age+t) ((p+2:Nat):Int))
  have hl : ((p+1:Nat):Int)-1=(p:Int) := by omega
  have hr : ((p+1:Nat):Int)+1=((p+2:Nat):Int) := by omega
  rw [cell,hl,hr]

def lagDifference (Q i t : Nat) : Bool := xor (cell (Q+t) (i:Int)) (cell t (i:Int))

theorem lagDifference_eq (Q i t : Nat) :
    lagDifference Q i t=difference (seedHistory Q) (seedHistory 0) i t := by
  simp only [lagDifference,difference,seedHistory,Nat.zero_add]

/-- The two histories are ages Q+t and t of the SAME literal single-seed orbit. -/
theorem actual_lag_death (Q d : Nat)
    (hc : cell (Q+d) 0=cell d 0)
    (h1 : lagDifference Q 1 d=true) (hd : lagDifference Q 1 (d+1)=false)
    (h2 : lagDifference Q 2 d=true) (h2n : lagDifference Q 2 (d+1)=true) :
    lagDifference Q 2 (d+2)=false := by
  simp only [lagDifference_eq] at h1 hd h2 h2n ⊢
  apply death_termination (seedHistory_actual Q) (seedHistory_actual 0) d
    (by simpa only [seedHistory,Nat.zero_add,Int.natCast_zero] using hc) h1 hd h2 h2n

theorem actual_terminal_second_birth (Q A Z a b : Nat)
    (ha : A≤a) (hab : a<b) (hb : b≤Z)
    (hc : ∀ t, A≤t → t≤Z → cell (Q+t) 0=cell t 0)
    (hp : ∀ t, A≤t → t≤Z → lagDifference Q 2 t=true)
    (ba : Birth (lagDifference Q 1) a) (bb : Birth (lagDifference Q 1) b) :
    b=Z ∧ lagDifference Q 2 (b+1)=false := by
  have h := terminal_second_birth (seedHistory_actual Q) (seedHistory_actual 0) A Z a b
    ha hab hb (by simpa only [seedHistory,Nat.zero_add,Int.natCast_zero] using hc)
    (by simpa only [lagDifference_eq] using hp)
    (by simpa only [Birth,lagDifference_eq] using ba)
    (by simpa only [Birth,lagDifference_eq] using bb)
  simpa only [lagDifference_eq] using h

theorem actual_no_ordered_three_births (Q A Z a b c : Nat)
    (ha : A≤a) (hab : a<b) (hbc : b<c) (hcZ : c≤Z)
    (hc : ∀ t, A≤t → t≤Z → cell (Q+t) 0=cell t 0)
    (hp : ∀ t, A≤t → t≤Z → lagDifference Q 2 t=true)
    (ba : Birth (lagDifference Q 1) a) (bb : Birth (lagDifference Q 1) b)
    (_bc : Birth (lagDifference Q 1) c) : False := by
  have h := (actual_terminal_second_birth Q A Z a b ha hab (by omega) hc hp ba bb).1
  omega

end Ruliology.CellularAutomata.Rule30BirthEpisodeInheritance
