module
public import Ruliology.CellularAutomata.Rule30SourceObservables
public import Ruliology.CellularAutomata.Rule30Realization

/-! Three upper bounds on the black count `C` in terms of the run-end count `A` over any
interval of `n` ticks at any site. Condrey's bound gives `3C ≤ n + 5A + 3`. Summing
one-step potential differences on two and six cells gives `2C ≤ n + 2A + 1` and
`6C ≤ 5n + A + 5`, respectively. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30SourceDensityRegion

open Rule30Jen (cell rule)
open Rule30SourceObservables (source bit count)

abbrev History := Nat → Int → Bool
def Evolution (u : History) : Prop := ∀ t i, u (t+1) i =
  rule (u t (i-1)) (u t i) (u t (i+1))
def black (u : History) (j : Int) (s n : Nat) := count (fun t => u (s+t) j) n
def ends (u : History) (j : Int) (s n : Nat) :=
  count (fun t => source (u (s+t) j) (u (s+t) (j+1))) n

private def credit (a b c d e f : Bool) : Int :=
  (#[0,1,0,1,0,0,0,3,0,2,0,5,0,0,0,4,0,3,0,1,0,0,0,4,0,4,0,3,0,0,0,2,0,1,0,1,0,0,0,5,0,2,0,3,0,0,0,2,0,3,0,1,0,0,0,4,0,4,0,3,0,0,0,2] : Array Nat).getD
    (a.toNat+2*b.toNat+4*c.toNat+8*d.toNat+16*e.toNat+32*f.toNat) 0
private theorem credit_range : ∀ a b c d e f, 0 ≤ credit a b c d e f ∧
    credit a b c d e f ≤ 5 := by decide +kernel
private theorem credit_step : ∀ a b c d e f g h : Bool,
  6*bit a-bit (source a b)-5 ≤ credit a b c d e f -
    credit h (rule a b c) (rule b c d) (rule c d e) (rule d e f) (rule e f g) := by decide +kernel

private def twin (a b : Bool) : Int := bit (a && b)
private theorem twin_range : ∀ a b, 0 ≤ twin a b ∧ twin a b ≤ 1 := by decide
private theorem twin_step : ∀ a b c h : Bool,
  2*bit a-2*bit (source a b)-1 ≤ twin a b - twin h (rule a b c) := by decide

private theorem telescope (c r : Nat → Bool) (p : Nat → Int) (k m z : Int)
    (localBound : ∀ t, k*bit (c t)-m*bit (source (c t) (r t))-z ≤ p t-p (t+1)) (n : Nat) :
    k*count c n-m*count (fun t => source (c t) (r t)) n-z*(n:Int) ≤ p 0-p n := by
  induction n with
  | zero => simp [count]
  | succ n ih =>
    have h := localBound n
    simp only [count,Int.natCast_succ,Int.mul_add,Int.mul_one]
    omega

private theorem low {u : History} (hu : Evolution u) (j : Int) (s n : Nat) :
    3*black u j s n ≤ n+5*ends u j s n+3 := by
  apply Rule30SourceObservables.density_bound (fun t=>u (s+t) j) (fun t=>u (s+t) (j+1))
    (fun t=>u (s+t) (j+2)) (fun t=>u (s+t) (j+3))
  · intro t
    simpa only [show j+1-1=j by omega,show j+1+1=j+2 by omega,Nat.add_assoc] using hu (s+t) (j+1)
  · intro t
    simpa only [show j+2-1=j+1 by omega,show j+2+1=j+3 by omega,Nat.add_assoc] using hu (s+t) (j+2)

theorem middle_face {u : History} (hu : Evolution u) (j : Int) (s n : Nat) :
    2*black u j s n ≤ n+2*ends u j s n+1 := by
  let x (t : Nat) (i : Int) := u (s+t) (j+i)
  let p (t : Nat) := twin (x t 0) (x t 1)
  have step (t : Nat) : 2*bit (x t 0)-2*bit (source (x t 0) (x t 1))-1 ≤ p t-p (t+1) := by
    have update : x (t+1) 1 = rule (x t 0) (x t 1) (x t 2) := by
      simpa only [x,show j+1-1=j+0 by omega,show j+1+1=j+2 by omega,Nat.add_assoc] using hu (s+t) (j+1)
    dsimp only [p]; rw [update];exact twin_step _ _ _ _
  have h:=telescope (fun t=>x t 0) (fun t=>x t 1) p 2 2 1 step n
  have h0: p 0 ≤ 1 := (twin_range _ _).2
  have hn: 0 ≤ p n := (twin_range _ _).1
  simp only [x,Int.add_zero,Int.one_mul] at h
  unfold black ends;omega

theorem high_face {u : History} (hu : Evolution u) (j : Int) (s n : Nat) :
    6*black u j s n ≤ 5*(n:Int)+ends u j s n+5 := by
  let x (t : Nat) (i : Int) := u (s+t) (j+i)
  let p (t : Nat) := credit (x t 0) (x t 1) (x t 2) (x t 3) (x t 4) (x t 5)
  have up (t : Nat) (i : Int) : x (t+1) i = rule (x t (i-1)) (x t i) (x t (i+1)) := by
    simpa only [x,Nat.add_assoc,Int.add_sub_assoc,Int.add_assoc] using hu (s+t) (j+i)
  have step (t : Nat) : 6*bit (x t 0)-1*bit (source (x t 0) (x t 1))-5 ≤ p t-p (t+1) := by
    dsimp only [p]
    rw [up t 1,up t 2,up t 3,up t 4,up t 5]
    simpa only [Int.one_mul,show (1:Int)+1=2 by decide,show (1:Int)-1=0 by decide,show (2:Int)+1=3 by decide,show (2:Int)-1=1 by decide,show (3:Int)+1=4 by decide,show (3:Int)-1=2 by decide,show (4:Int)+1=5 by decide,show (4:Int)-1=3 by decide,show (5:Int)+1=6 by decide,show (5:Int)-1=4 by decide] using credit_step (x t 0) (x t 1) (x t 2) (x t 3) (x t 4) (x t 5) (x t 6) (x (t+1) 0)
  have h:=telescope (fun t=>x t 0) (fun t=>x t 1) p 6 1 5 step n
  have h0: p 0 ≤ 5 := (credit_range _ _ _ _ _ _).2
  have hn: 0 ≤ p n := (credit_range _ _ _ _ _ _).1
  simp only [x,Int.add_zero,Int.one_mul] at h
  unfold black ends;omega

theorem region {u : History} (hu : Evolution u) (j : Int) (s n : Nat) :
    3*black u j s n ≤ n+5*ends u j s n+3 ∧
    2*black u j s n ≤ n+2*ends u j s n+1 ∧
    6*black u j s n ≤ 5*(n:Int)+ends u j s n+5 :=
  ⟨low hu j s n,middle_face hu j s n,high_face hu j s n⟩

theorem singleton_region (j : Int) (s n : Nat) :
    3*black cell j s n ≤ n+5*ends cell j s n+3 ∧
    2*black cell j s n ≤ n+2*ends cell j s n+1 ∧
    6*black cell j s n ≤ 5*(n:Int)+ends cell j s n+5 := region (fun _ _ => rfl) j s n
end Ruliology.CellularAutomata.Rule30SourceDensityRegion
