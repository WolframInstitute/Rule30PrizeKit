module
public import Ruliology.CellularAutomata.Rule30Prize
public import Ruliology.CellularAutomata.Rule30Realization

/-! Finite steering of a half-strip by its observed leftmost column. Every infinite controlled evolution is a restriction of a genuine full-line Rule 30 evolution. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30DensityControl
open Rule30Jen
abbrev Row := Nat → Bool

def next (r : Row) (b : Bool) : Row
  | 0 => b
  | j+1 => rule (r j) (r (j+1)) (r (j+2))

def defaultRow (r : Row) : Nat → Row
  | 0 => r
  | t+1 => next (defaultRow r t) false

def OpenStep (r s : Row) := ∀ j,s (j+1)=rule (r j) (r (j+1)) (r (j+2))

inductive Reach : Nat → Row → Row → Prop
  | zero (r : Row) : Reach 0 r r
  | succ {t r s z} : Reach t r s → OpenStep s z → Reach (t+1) r z

private theorem fill (k : Nat) (r y : Row)
    (already : ∀ j,k≤j → y (j+1)=rule (r j) (r (j+1)) (r (j+2))) :
    ∃ q, (∀ j,k≤j → q j=r j) ∧ OpenStep q y := by
  induction k generalizing r with
  | zero => exact ⟨r,fun _ _ => rfl,fun j => already j (Nat.zero_le _)⟩
  | succ k ih =>
    let q (i : Nat) := if i=k then xor (y (k+1)) (r (k+1) || r (k+2)) else r i
    have same (i : Nat) (hi : k<i) : q i=r i := by simp [q,show i≠k by omega]
    have extended (j : Nat) (hj : k≤j) : y (j+1)=rule (q j) (q (j+1)) (q (j+2)) := by
      rw [same (j+1) (by omega),same (j+2) (by omega)]
      by_cases e : j=k
      · subst j; simp [q,rule]
      · rw [same _ (by omega)]; exact already j (by omega)
    obtain ⟨z,hz,phys⟩ := ih q extended
    exact ⟨z,fun j h => (hz j (by omega)).trans (same j (by omega)),phys⟩

private theorem reach_tail (r : Row) (n : Nat) (v : Row) (far : ∀ j,n≤j → v j=defaultRow r n j) :
    Reach n r v := by
  induction n generalizing v with
  | zero =>
    have eq : v=r := funext (fun j => far j (Nat.zero_le _))
    rw [eq];exact .zero _
  | succ n ih =>
    obtain ⟨q,tail,phys⟩ := fill n (defaultRow r n) v (fun j h => far (j+1) (by omega))
    exact .succ (ih q tail) phys

/-- A prescribed W-bit prefix, including the freely varied site zero, can be installed in W transitions from every complete current row. -/
theorem steer_prefix (r target : Row) (W : Nat) :
    ∃ v, Reach W r v ∧ ∀ j,j<W → v j=target j := by
  let v j := if j<W then target j else defaultRow r W j
  exact ⟨v,reach_tail r W v (fun j h => by simp [v,show ¬j<W by omega]),fun j h => by simp [v,h]⟩

/-- Every finite steering certificate yields actual intermediate rows with the stated duration. -/
theorem realize_segment {n : Nat} {r v : Row} (path : Reach n r v) :
    ∃ s : Nat → Row, s 0=r ∧ s n=v ∧ ∀ t,t<n → OpenStep (s t) (s (t+1)) := by
  induction path with
  | zero r => exact ⟨fun _ => r,rfl,rfl,fun t ht => by omega⟩
  | @succ n r u v path last ih =>
    obtain ⟨s,beginAt,endAt,physical⟩ := ih
    let z (t : Nat) := if t=n+1 then v else s t
    refine ⟨z,by simp [z,beginAt],by simp [z],?_⟩
    intro t ht
    by_cases eq : t=n
    · subst t; simpa [z,endAt] using last
    · simpa [z,eq,show t≠n+1 by omega] using physical t (by omega)

/-- A prescribed stream of rows obeying the interior rule is realized at every nonnegative site of one full-line initial condition. -/
theorem realize_stream (s : Nat → Row) (phys : ∀ t,OpenStep (s t) (s (t+1))) :
    ∃ x : Int → Bool,∀ (t j : Nat),Rule30Realization.evol x t (j : Int)=s t j := by
  let R (i : Int) := s 0 i.toNat
  let c t := s t 0
  let x := Rule30Realization.conf R c
  have c0 := (Rule30Realization.realize R c).2
  have initial := (Rule30Realization.realize R c).1
  refine ⟨x,?_⟩
  intro t
  induction t with
  | zero =>
    intro j
    cases j with
    | zero => exact c0 0
    | succ j => simpa [x,R,Rule30Realization.evol] using initial ((j+1:Nat):Int) (by omega)
  | succ t ih =>
    intro j
    cases j with
    | zero => exact c0 _
    | succ j =>
      rw [Rule30Realization.evol,show ((j+1:Nat):Int)-1=(j:Int) by omega,
        show ((j+1:Nat):Int)+1=((j+2:Nat):Int) by omega,ih,ih,ih]
      exact (phys t j).symm

end Ruliology.CellularAutomata.Rule30DensityControl
