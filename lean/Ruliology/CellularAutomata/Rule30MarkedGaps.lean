module

public import Ruliology.CellularAutomata.Rule30Prize
public import Ruliology.CellularAutomata.Rule30DrivenLeft

/-!
# White intervals and their black arrival times

Two singleton ages with the same center future cannot have distinct marked
lengths. The nearer spatial disagreement advances a cell each tick and
arrives at site -1 on a black center tick, when it determines the next center.
Unbounded marked lengths would settle Problem 1. Their existence is open.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30MarkedGaps
open Ruliology.CellularAutomata Rule30Jen

def Mark (s l : Nat) : Prop :=
  (∀ q : Int, -(l : Int) ≤ q → q < 0 → cell s q = false) ∧
  cell s (-(l : Int)-1) = true ∧ cell (s+l) 0 = true

open Rule30DrivenLeft

/-- Run just the left half from a white start using the observed center
as its boundary. At a black tick its predicted left bit must equal the
complement of the next center bit to be consistent. -/
def Failed (c : Nat → Bool) (t : Nat) : Prop :=
  c t=true ∧ L c (fun _ => false) t (-1) ≠ !(c (t+1))

def FirstFailure (c : Nat → Bool) (l : Nat) : Prop :=
  Failed c l ∧ ∀ k, k<l → ¬Failed c k

private theorem black_reading (s k : Nat) (on : cell (s+k) 0=true) :
    L (fun u => cell (s+u) 0) (cell s) k (-1) = !(cell (s+(k+1)) 0) := by
  rw [cell_eq_L s k _ (by decide)]
  have e := cell_left (s+k) 0
  rw [on,Bool.true_or] at e
  rw [← Nat.add_assoc]
  cases bit : cell (s+k+1) 0 <;> simpa [bit] using e

/-- A marked gap identifies exactly the first failed check, from the
center bits alone. An unmarked gap may also produce a finite delay. -/
theorem first_failure_of_mark {s l : Nat} (hm : Mark s l) :
    FirstFailure (fun u => cell (s+u) 0) l := by
  let c := fun u => cell (s+u) 0
  have h := permutive_aux (c:=c) (s:=cell s) (s':=fun _ => false) (k:=l) hm.1
    (by rw [show -((l+1:Nat):Int) = -(l:Int)-1 by omega]; exact hm.2.1)
  constructor
  · refine ⟨hm.2.2,?_⟩
    have ne := (h l (Nat.le_refl _)).2
    rw [show -((l+1-l:Nat):Int) = -1 by omega,black_reading s l hm.2.2] at ne
    intro eq
    rw [eq] at ne
    cases bit : cell (s+(l+1)) 0 <;> simp [bit] at ne
  · intro k hk fail
    have eq := (h k (by omega)).1 (-1) (by omega) (by decide)
    exact fail.2 (eq.symm.trans (black_reading s k fail.1))

/-- Unbounded *finite* first failures suffice, even without information
about the lengths of the physical gaps. A restart that never fails does
not supply a witness. -/
theorem problem1_of_first_failures
    (unbounded : ∀ B, ∃ s l, B<l ∧ FirstFailure (fun u => cell (s+u) 0) l) :
    Rule30Prize.Problem1 := by
  rintro ⟨T,P,hp,hper⟩
  have finite (n : Nat) : ∃ B, ∀ s, s<n → ∀ l, FirstFailure (fun u => cell (s+u) 0) l → l≤B := by
    induction n with
    | zero => exact ⟨0,by omega⟩
    | succ n ih =>
      obtain ⟨B,old⟩ := ih
      by_cases ex : ∃ j, FirstFailure (fun u => cell (n+u) 0) j
      · obtain ⟨j,fst⟩ := ex
        refine ⟨B+j,fun s hs l h => ?_⟩
        by_cases prev : s<n
        · have := old s prev l h; omega
        · have e : s=n := by omega
          subst s
          by_cases lt : j<l
          · exact (h.2 j lt fst.1).elim
          · omega
      · refine ⟨B,fun s hs l h => old s ?_ l h⟩
        apply Classical.byContradiction
        intro hn
        have e : s=n := by omega
        exact ex ⟨l,e ▸ h⟩
  obtain ⟨B,bound⟩ := finite (T+P)
  obtain ⟨s,l,large,first⟩ := unbounded B
  by_cases before : s<T
  · have := bound s (by omega) l first; omega
  let r := T+(s-T)%P
  have rem := Nat.mod_lt (s-T) hp
  have div := Nat.mod_add_div (s-T) P
  have same : (fun u => cell (s+u) 0) = (fun u => cell (r+u) 0) := by
    funext u
    have step := periodic_mul (f:=fun u => cell u 0) hper ((s-T)/P) (r+u) (by dsimp [r]; omega)
    rw [Nat.mul_comm ((s-T)/P) P] at step
    have e : s+u=r+u+P*((s-T)/P) := by dsimp [r]; omega
    simpa only [e] using step
  rw [same] at first
  have := bound r (by dsimp [r]; omega) l first
  omega

/-- A fixed center future has at most one marked length. -/
theorem unique_length {s t l m : Nat}
    (clock : ∀ k, cell (s+k) 0 = cell (t+k) 0) (a : Mark s l) (b : Mark t m) :
    l=m := by
  have left := first_failure_of_mark a
  have right := first_failure_of_mark b
  rw [funext clock] at left
  rcases Nat.lt_trichotomy l m with h | h | h
  · exact (right.2 l h left.1).elim
  · exact h
  · exact (left.2 m h right.1).elim

theorem problem1_of_marks (many : ∀ B, ∃ s l, B<l ∧ Mark s l) : Rule30Prize.Problem1 := by
  apply problem1_of_first_failures
  intro B
  obtain ⟨s,l,h,mark⟩ := many B
  exact ⟨s,l,h,first_failure_of_mark mark⟩

/-- Arbitrarily late, arbitrarily wide all-white left intervals suffice
to produce an indefinitely accepted phase of any proposed center period.
There is no condition on the color at the far edge or at arrival. -/
theorem accepting_phase_of_late_gaps {T P : Nat} (pos : 0<P)
    (per : ∀ t, T≤t → cell (t+P) 0=cell t 0)
    (gaps : ∀ w : Nat, ∃ s≥w, ∀ q : Int, -(w:Int)≤q → q<0 → cell s q=false) :
    ∃ r, T≤r ∧ r<T+P ∧ ∀ t, ¬ Failed (fun u => cell (r+u) 0) t := by
  apply Classical.byContradiction
  intro no
  have hits (r : Nat) (lo : T≤r) (hi : r<T+P) :
      ∃ t, Failed (fun u => cell (r+u) 0) t := by
    apply Classical.byContradiction
    intro none
    exact no ⟨r,lo,hi,fun t h => none ⟨t,h⟩⟩
  have bounded (n : Nat) : ∃ B, ∀ r, T≤r → r<T+P → r<n →
      ∃ t≤B, Failed (fun u => cell (r+u) 0) t := by
    induction n with
    | zero => exact ⟨0,by omega⟩
    | succ n ih =>
      obtain ⟨B,old⟩ := ih
      by_cases valid : T≤n ∧ n<T+P
      · obtain ⟨v,f⟩ := hits n valid.1 valid.2
        refine ⟨B+v,fun r lo hi lt => ?_⟩
        by_cases e : r=n
        · exact ⟨v,by omega,e ▸ f⟩
        · obtain ⟨t,b,h⟩ := old r lo hi (by omega)
          exact ⟨t,by omega,h⟩
      · exact ⟨B,fun r lo hi lt => old r lo hi (by omega)⟩
  obtain ⟨B,bound⟩ := bounded (T+P)
  obtain ⟨s,late,white⟩ := gaps (B+T+1)
  let r := T+(s-T)%P
  have rem := Nat.mod_lt (s-T) pos
  have div := Nat.mod_add_div (s-T) P
  obtain ⟨t,small,bad⟩ := bound r (by dsimp [r]; omega) (by dsimp [r]; omega) (by dsimp [r]; omega)
  have same : (fun u => cell (s+u) 0) = (fun u => cell (r+u) 0) := by
    funext u
    have step := periodic_mul (f:=fun u => cell u 0) per ((s-T)/P) (r+u) (by dsimp [r]; omega)
    rw [Nat.mul_comm ((s-T)/P) P] at step
    have e : s+u=r+u+P*((s-T)/P) := by dsimp [r]; omega
    simpa only [e] using step
  rw [← same] at bad
  have eq := light_cone (c:=fun u => cell (s+u) 0) (s:=cell s) (s':=fun _ => false) (k:=t)
    (fun p lo neg => white p (by omega) neg) t (by omega) (-1) (by omega) (by decide)
  exact bad.2 (eq.symm.trans (black_reading s t bad.1))

private instance (c : Nat → Bool) (t : Nat) : Decidable (Failed c t) := by
  unfold Failed
  infer_instance

/-- The first failure can occur after the end of the physical gap. -/
theorem two_white_four_delay :
    cell 4 (-1)=false ∧ cell 4 (-2)=false ∧ cell 4 (-3)=true ∧
    cell 6 0=false ∧ FirstFailure (fun u => cell (4+u) 0) 4 := by
  have early : ∀ i : Fin 4, ¬ Failed (fun u => cell (4+u) 0) i.val := by decide +kernel
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    by decide +kernel,fun k hk => early ⟨k,hk⟩⟩
end Ruliology.CellularAutomata.Rule30MarkedGaps
