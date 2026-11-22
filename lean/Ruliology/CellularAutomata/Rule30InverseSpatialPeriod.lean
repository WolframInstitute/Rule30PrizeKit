module

public import Ruliology.CellularAutomata.Rule30Realization
public import Ruliology.CellularAutomata.Rule30Prize

/-!
# Spatial periods of Rule 30 ancestors

When a whole-line image has white cells arbitrarily far to the right, any
three predecessors include an equal pair. At a white image cell the next
inverse step to its left remembers just one bit. A periodic image containing
a white cell therefore has only predecessors of period dividing twice the
given period. This bound iterates over every ancestor of a nonconstant
periodic image, even if no periodicity of the ancestor was assumed.

The kit's mathlib companion `Rule30Equivalents.Preimages` already proves a
global bound of three, attained on every eventually black right tail, and
uniqueness under frequent synchronizing windows. The two-predecessor bound
below needs only frequent individual white cells. These are spatial results.

Contributed by Troy Lowry with OpenAI Codex.
-/

@[expose] public section
namespace Ruliology.CellularAutomata.Rule30InverseSpatialPeriod

open Rule30Jen Rule30Realization

abbrev Row := Int → Bool

def Period (x : Row) (p : Nat) : Prop := ∀ j, x (j + p) = x j
def WhiteCofinal (y : Row) : Prop := ∀ b : Int, ∃ j, b ≤ j ∧ y j = false
def Nonconstant (y : Row) : Prop := ∃ i j, y i ≠ y j

private theorem recover (x : Row) (j : Int) :
    x (j-1) = xor (evol x 1 j) (x j || x (j+1)) :=
  rule_left _ _ _

private theorem agree_left {x z : Row} {lo k : Int}
    (h : ∀ i, lo<i → i≤k → evol x 1 i = evol z 1 i)
    (h0 : x k = z k) (h1 : x (k+1) = z (k+1)) :
    ∀ j, lo≤j → j ≤ k+1 → x j = z j := by
  have H : ∀ n : Nat, lo≤k-n → x (k-n) = z (k-n) ∧ x (k-n+1) = z (k-n+1) := by
    intro n
    induction n with
    | zero => intro _; simpa using And.intro h0 h1
    | succ n ih =>
      intro hl
      obtain ⟨he,he'⟩ := ih (by omega)
      have hh := recover x (k-n)
      rw [h _ (by omega) (by omega), he, he', ← recover z] at hh
      rw [show k-((n+1:Nat):Int) = k-n-1 by omega,
          show k-(n:Int)-1+1=k-n by omega]
      exact ⟨hh, he⟩
  intro j hl hj
  by_cases htop : j=k+1
  · simpa [htop] using h1
  · have hj' : k - ((k-j).toNat : Int) = j := by omega
    simpa only [hj'] using (H (k-j).toNat (by omega)).1

private theorem compress (a b c d : Bool) (h : rule b c d = false) :
    a = xor (rule a b c) b := by
  revert a b c d
  decide

private theorem white_window {x z : Row} {lo j : Int} (hl : lo<j-1)
    (h : ∀ i, lo<i → i≤j → evol x 1 i = evol z 1 i)
    (hw : evol x 1 j = false) (hb : x (j-1) = z (j-1)) :
    ∀ i, lo≤i → i ≤ j-1 → x i = z i := by
  have pair (v : Row) (hv : evol v 1 j = false) :
      v (j-2) = xor (evol v 1 (j-1)) (v (j-1)) := by
    simp only [evol, show j-1-1=j-2 by omega, show j-1+1=j by omega]
    exact compress _ _ _ _ hv
  have hz : evol z 1 j = false := (h j (by omega) (by omega)).symm.trans hw
  have hx := pair x hw
  rw [h _ (by omega) (by omega),hb,← pair z hz] at hx
  have hk : j-2+1=j-1 := by omega
  simpa only [hk] using agree_left (lo:=lo) (fun i hi hu => h i hi (by omega)) hx (hk.symm ▸ hb)

/-- A white image cell and one predecessor bit determine the entire ray to its left. -/
theorem white_determines_left {x z : Row} (h : evol x 1 = evol z 1) {j : Int}
    (hw : evol x 1 j = false) (hb : x (j-1) = z (j-1)) :
    ∀ i, i ≤ j-1 → x i = z i := by
  intro i hi
  exact white_window (lo:=i-1) (by omega) (fun k _ _ => congrFun h k) hw hb i (by omega) hi

/-- On an image with cofinally many white cells at most two distinct
whole-line predecessors are possible. -/
theorem two_predecessors {x y z : Row} (hw : WhiteCofinal (evol x 1))
    (hxy : evol x 1 = evol y 1) (hxz : evol x 1 = evol z 1) :
    x = y ∨ x = z ∨ y = z := by
  classical
  by_cases h₁ : x=y
  · exact Or.inl h₁
  by_cases h₂ : x=z
  · exact Or.inr (Or.inl h₂)
  by_cases h₃ : y=z
  · exact Or.inr (Or.inr h₃)
  have witness {a b : Row} (hab : a ≠ b) : ∃ i, a i ≠ b i := by
    exact Classical.byContradiction fun hn => hab (funext fun i =>
      Classical.byContradiction fun hi => hn ⟨i,hi⟩)
  obtain ⟨a,ha⟩ := witness h₁
  obtain ⟨b,hb⟩ := witness h₂
  obtain ⟨c,hc⟩ := witness h₃
  obtain ⟨j,hj,hj0⟩ := hw (max a (max b c)+1)
  have pigeon (v w u : Bool) : v=w ∨ v=u ∨ w=u := by
    cases v <;> cases w <;> cases u <;> decide
  rcases pigeon (x (j-1)) (y (j-1)) (z (j-1)) with e | e | e
  · exact False.elim (ha (white_determines_left hxy hj0 e a (by omega)))
  · exact False.elim (hb (white_determines_left hxz hj0 e b (by omega)))
  · exact False.elim (hc (white_determines_left (hxy.symm.trans hxz) (hxy ▸ hj0) e c (by omega)))

theorem frequent_of_period {y : Row} {p : Nat} (hp : 0<p) (hy : Period y p)
    {a : Int} {bit : Bool} (ha : y a=bit) : ∀ b : Int, ∃ j, b≤j ∧ y j=bit := by
  intro b
  have H : ∀ n : Nat, y (a+(n*p:Nat))=bit := by
    intro n
    induction n with
    | zero => simpa using ha
    | succ n ih =>
      simpa [Nat.succ_mul, Int.add_assoc] using (hy (a+(n*p:Nat))).trans ih
  let n := (b-a).toNat
  have hn : n ≤ n*p := by simpa using Nat.mul_le_mul_left n hp
  have hb : b-a ≤ (n:Int) := by dsimp [n]; omega
  exact ⟨a+((n*p:Nat):Int),by omega,H n⟩

theorem translated (x : Row) (d j : Int) :
    evol (fun i => x (i+d)) 1 j = evol x 1 (j+d) := by
  simp only [evol, show j-1+d=j+d-1 by omega, show j+1+d=j+d+1 by omega]

private theorem carry {x : Row} {a j d : Int} (hl : a<j-1)
    (rep : ∀ k, a<k → k≤j → evol x 1 (k+d)=evol x 1 k)
    (white : evol x 1 j=false) (seed : x (j-1)=x (j+d-1)) :
    ∀ i, a≤i → i<j → x i=x (i+d) := by
  have r := white_window (x:=x) (z:=fun k => x (k+d)) hl
    (fun k hk ht => (rep k hk ht).symm.trans (translated x d k).symm) white
    (by simpa only [show j-1+d=j+d-1 by omega] using seed)
  exact fun i hi hu => r i hi (by omega)

/-- Finite-window version on any physical row. The image repeats at shift
`p` on the indicated interval, with a white marker at `r`. Its predecessor
repeats at shift `2*p` throughout the interior down to the left endpoint
`a`. No agreement outside the given output window is used. -/
theorem period_predecessor_window {x : Row} {a r : Int} {p : Nat} (hp : 0<p)
    (rep : ∀ k, a<k → k≤r+p → evol x 1 (k+p)=evol x 1 k)
    (white : evol x 1 r=false) :
    ∀ i, a≤i → i+p<r → x (i+2*(p:Int))=x i := by
  intro i hi hu
  let A := x (r-1)
  let B := x (r+p-1)
  let C := x (r+2*(p:Int)-1)
  have tri (v w u : Bool) : v=w ∨ v=u ∨ w=u := by cases v <;> cases w <;> cases u <;> decide
  rcases tri A B C with hab|hac|hbc
  · have H := carry (a:=a) (j:=r) (d:=p) (by omega) (fun k h g => rep k h (by omega)) white hab
    have v := (H i hi (by omega)).trans (H (i+p) (by omega) hu)
    simpa only [show i+p+p=i+2*(p:Int) by omega] using v.symm
  · apply Eq.symm
    apply carry (a:=a) (j:=r) (d:=2*(p:Int)) (by omega) _ white hac i hi (by omega)
    intro k hk hg
    rw [show k+2*(p:Int)=k+p+p by omega, rep (k+p) (by omega) (by omega), rep k hk (by omega)]
  · have hw := (rep r (by omega) (by omega)).trans white
    have H := carry (a:=a) (j:=r+p) (d:=p) (by omega) rep hw
      (by simpa only [show r+p+p=r+2*(p:Int) by omega] using hbc)
    have v := (H i hi (by omega)).trans (H (i+p) (by omega) (by omega))
    simpa only [show i+p+p=i+2*(p:Int) by omega] using v.symm

/-- Every predecessor of a spatially p-periodic image containing white
is spatially 2p-periodic. -/
theorem period_predecessor {x : Row} {p : Nat} (hp : 0<p)
    (h : Period (evol x 1) p) (white : ∃ j, evol x 1 j=false) : Period x (2*p) := by
  obtain ⟨j,hj⟩ := white
  let y : Row := fun i => x (i+p)
  let z : Row := fun i => y (i+p)
  have E : evol y 1=evol x 1 := funext fun i => (translated x p i).trans (h i)
  have D : evol z 1=evol x 1 := funext fun i =>
    (translated y p i).trans ((congrFun E _).trans (h i))
  rcases two_predecessors (frequent_of_period hp h hj) E.symm D.symm with H|H|H
  · intro i
    have h₁ := congrFun H i
    have h₂ := congrFun H (i+p)
    dsimp [y] at h₁ h₂
    simpa [Nat.two_mul, ← Int.add_assoc] using h₂.symm.trans h₁.symm
  · intro i
    simpa [z,y,Nat.two_mul,← Int.add_assoc] using (congrFun H i).symm
  · have H' (i : Int) : x i = x (i+p) := by
      simpa [z,y] using congrFun H (i-p)
    intro i
    simpa [Nat.two_mul,← Int.add_assoc] using (H' (i+p)).symm.trans (H' i).symm

theorem nonconstant_before {x : Row} (h : Nonconstant (evol x 1)) : Nonconstant x := by
  obtain ⟨i,j,hij⟩ := h
  apply Classical.byContradiction
  intro hn
  have same (a b : Int) : x a=x b := Classical.byContradiction fun e => hn ⟨a,b,e⟩
  exact hij (by simp only [evol]; rw [same (i-1) (j-1),same i j,same (i+1) (j+1)])

/-- All ancestors of a nonconstant periodic image, however many ticks
back, are periodic with the same odd part as an upper bound. -/
theorem period_ancestor (x : Row) (t : Nat) {p : Nat} (hp : 0<p)
    (h : Period (evol x t) p) (hn : Nonconstant (evol x t)) : Period x (2^t*p) := by
  induction t generalizing p with
  | zero => simpa [evol] using h
  | succ t ih =>
    change Nonconstant (evol (evol x t) 1) at hn
    change Period (evol (evol x t) 1) p at h
    obtain ⟨i,j,hij⟩ := hn
    have hw : ∃ k, evol (evol x t) 1 k = false := by
      cases hi : evol (evol x t) 1 i <;> cases hj : evol (evol x t) 1 j
      · exact ⟨i,hi⟩
      · exact ⟨i,hi⟩
      · exact ⟨j,hj⟩
      · exact False.elim (hij (hi.trans hj.symm))
    have H := ih (p := 2*p) (by omega) (period_predecessor hp h hw)
      (nonconstant_before ⟨i,j,hij⟩)
    simpa [Nat.pow_succ,Nat.mul_assoc] using H

end Ruliology.CellularAutomata.Rule30InverseSpatialPeriod
