module

public import Ruliology.CellularAutomata.Rule30EtherThreeSkeleton

/-!
# Period-three readings six cells west

With an eventual center clock 001 or 011, the column six sites west eventually
avoids 10101, for every choice of the free phase. Thus arbitrarily late 10101 at
this particular singleton column would exclude period three. Its recurrence is open.

Twelve readings of the center and its western neighbor determine seven readings
six cells west by five applications of left inversion. With the kit's short
forbidden gate factors, the table also identifies every monochrome four-start in
the first three phases of this window. The recurrent 001 skeleton is used only
to fix the first white phase. The alternating-word exclusion needs no gate-word
restrictions once the two columns have their phase shapes.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30WestSixReading
open Ruliology.CellularAutomata.Rule30Jen
open Ruliology.CellularAutomata.Rule30EtherThree
open Ruliology.CellularAutomata.Rule30Prize

def back (r a : Nat → Bool) : Nat → Nat → Bool
  | 0, n => a n
  | d+1, n => back a (fun j => rule (a (j+1)) (a j) (r j)) d n
termination_by structural d _ => d

theorem physical (t : Nat) (i : Int) (d n : Nat) :
    back (fun j => cell (t+j) (i+1)) (fun j => cell (t+j) i) d n =
      cell (t+n) (i-d) := by
  induction d generalizing i with
  | zero => simp [back]
  | succ d ih =>
    change back (fun j => cell (t+j) i)
      (fun j => rule (cell (t+(j+1)) i) (cell (t+j) i) (cell (t+j) (i+1))) d n = _
    have h (j : Nat) : rule (cell (t+(j+1)) i) (cell (t+j) i) (cell (t+j) (i+1)) =
        cell (t+j) (i-1) := (cell_left (t+j) i).symm
    simp only [h]
    rw [show i-(↑(d+1) : Int) = i-1-d by omega]
    simpa using ih (i-1)

theorem local_back {r a R A : Nat → Bool} (d n : Nat)
    (h : ∀ j, n ≤ j → j ≤ n+d → r j = R j ∧ a j = A j) :
    back r a d n = back R A d n := by
  induction d generalizing r a R A with
  | zero => exact (h n (by omega) (by omega)).2
  | succ d ih =>
    apply ih
    intro j hj hk
    obtain ⟨hr, ha⟩ := h j hj (by omega)
    exact ⟨ha, by simp only [hr, ha, (h (j+1) (by omega) (by omega)).2]⟩

def centerWord (hi : Bool) (j : Nat) : Bool :=
  decide (j%3=2) || (hi && decide (j%3=1))
def westWord (hi : Bool) (w : Fin 16) (j : Nat) : Bool :=
  decide (j%3=2) || (decide (j%3 = (if hi then 0 else 1)) && w.val.testBit (j/3))
/-- At 001 discard isolated bits; at 011 discard adjacent or once-separated ones.
These are the complements of a subset of the kit's forbidden right-gate words. -/
def legal (hi : Bool) (w : Fin 16) : Bool :=
  let letters := (List.range 4).map (fun j => w.val.testBit j)
  let bad := if hi then [[true,true],[true,false,true]]
             else [[true,false,true],[false,true,false]]
  !(bad.any (fun v => (List.range 4).any (fun j => v.isPrefixOf (letters.drop j))))
def obs (hi : Bool) (w : Fin 16) := back (centerWord hi) (westWord hi w) 5
def starts (f : Nat → Bool) (j : Nat) (b : Bool) : Prop :=
  ∀ k : Fin 4, f (j+k.val) = b
instance (f : Nat → Bool) (j : Nat) (b : Bool) : Decidable (starts f j b) :=
  inferInstanceAs (Decidable (∀ k : Fin 4, f (j+k.val) = b))

-- Earliest gate bit is the low bit: 0011 has code 12 and 0010 has code 4.
theorem table : ∀ (hi : Bool) (w : Fin 16) (j : Fin 3) (b : Bool), legal hi w = true →
    (starts (obs hi w) j.val b ↔ b = hi ∧
      (if hi then w.val=4 ∧ j.val=0 else w.val=12 ∧ 1≤j.val)) := by decide +kernel

/-- Twelve physical readings at each of two adjacent columns suffice. -/
theorem physical_table (t : Nat) (i : Int) (hi : Bool) (w : Fin 16)
    (windows : ∀ n, n < 12 →
      cell (t+n) (i+1) = centerWord hi n ∧ cell (t+n) i = westWord hi w n)
    (ok : legal hi w = true) (j : Fin 3) (b : Bool) :
    (starts (fun n => cell (t+n) (i-5)) j.val b ↔ b = hi ∧
      (if hi then w.val=4 ∧ j.val=0 else w.val=12 ∧ 1≤j.val)) := by
  have eqn (k : Fin 4) : cell (t+(j.val+k.val)) (i-5) = obs hi w (j.val+k.val) := by
    calc
      _ = back (fun n => cell (t+n) (i+1)) (fun n => cell (t+n) i) 5 (j.val+k.val) :=
        (physical t i 5 (j.val+k.val)).symm
      _ = _ := by
        apply local_back
        intro n _ hh
        exact windows n (by have := j.isLt; have := k.isLt; omega)
  simpa only [starts, ← eqn] using table hi w j b ok

private theorem bits_exist : ∀ a b c d : Bool, ∃ w : Fin 16,
    w.val.testBit 0 = a ∧ w.val.testBit 1 = b ∧
    w.val.testBit 2 = c ∧ w.val.testBit 3 = d := by decide

private theorem choose_bits (f : Nat → Bool) : ∃ w : Fin 16, ∀ j, j<4 → w.val.testBit j = f j := by
  obtain ⟨w,h0,h1,h2,h3⟩ := bits_exist (f 0) (f 1) (f 2) (f 3)
  exact ⟨w, fun j hj => by
    have h : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    rcases h with h|h|h|h <;> subst j <;> assumption⟩

def alternatingFive (f : Nat → Bool) (j : Nat) : Prop :=
  ∀ k : Fin 5, f (j+k.val) = decide (k.val%2=0)

private theorem misses : ∀ (hi : Bool) (w : Fin 16) (j : Fin 3),
    ¬ alternatingFive (obs hi w) j.val := by
  unfold alternatingFive
  decide +kernel

private def free (hi : Bool) := if hi then 0 else 1

private theorem shape (hi : Bool) (T : Nat)
    (clock : ∀ t, T ≤ t → cell t 0 = wordAt3 (if hi then w011 else w001) (t-T)) :
    ∃ U, T ≤ U ∧ ∀ t, U ≤ t → cell t 0 = centerWord hi (t-T) ∧
      ((t-T)%3 ≠ free hi → cell t (-1) = decide ((t-T)%3=2)) := by
  cases hi with
  | false =>
    obtain ⟨U,ht,sk⟩ := skeleton_001 T clock
    refine ⟨U,ht,fun t hu => ⟨?_,?_⟩⟩
    · simpa [wordAt3_001, centerWord] using clock t (by omega)
    · intro ne
      obtain ⟨a,_,c⟩ := col_m1_001 T clock t (by omega)
      change (t-T)%3 ≠ 1 at ne
      by_cases z : (t-T)%3=0
      · simp [a z,sk t hu z,z]
      · have v : (t-T)%3=2 := by omega
        simp [v,c v]
  | true =>
    refine ⟨T,by omega,fun t ht => ⟨?_,?_⟩⟩
    · rw [clock t ht]
      change wordAt3 w011 (t-T) = _
      rw [wordAt3_011]
      unfold centerWord
      have h : (t-T)%3=0 ∨ (t-T)%3=1 ∨ (t-T)%3=2 := by omega
      rcases h with h|h|h <;> simp [h]
    · intro ne
      obtain ⟨_,b,c⟩ := col_m1_011 T clock t ht
      change (t-T)%3 ≠ 0 at ne
      by_cases o : (t-T)%3=1
      · simp [o,b o]
      · have v : (t-T)%3=2 := by omega
        simp [v,c v]

/-- Both center clocks exclude 10101 six cells west, allowing an arbitrary free stream. -/
theorem avoids_alternating_five (hi : Bool) (T : Nat)
    (clock : ∀ t, T ≤ t → cell t 0 = wordAt3 (if hi then w011 else w001) (t-T)) :
    ∃ U, ∀ t, U ≤ t → ¬ alternatingFive (fun n => cell n (-6)) t := by
  obtain ⟨U,hU,sh⟩ := shape hi T clock
  refine ⟨U+2,?_⟩
  intro t ht alt
  let j : Fin 3 := ⟨(t-T)%3, by omega⟩
  let s := t-j.val
  have jt : j.val=(t-T)%3 := rfl
  have js : s+j.val=t := by dsimp [s]; omega
  have su : U ≤ s := by omega
  obtain ⟨w,hw⟩ := choose_bits (fun k => cell (s+3*k+free hi) (-1))
  have windows (n : Nat) (hn : n < 12) :
      cell (s+n) 0 = centerWord hi n ∧ cell (s+n) (-1) = westWord hi w n := by
    have ph : (s+n-T)%3=n%3 := by omega
    obtain ⟨a,b⟩ := sh (s+n) (by omega)
    constructor
    · simpa [centerWord,ph] using a
    · rw [ph] at b
      by_cases h : n%3 = free hi
      · have g := hw (n/3) (by omega)
        have eq : s+3*(n/3)+free hi=s+n := by omega
        rw [eq] at g
        have nf : free hi ≠ 2 := by cases hi <;> decide
        change cell (s+n) (-1) = (decide (n%3=2) || decide (n%3=free hi) && _)
        simp only [nf, h, decide_false, decide_true, Bool.true_and, Bool.false_or]
        exact g.symm
      · change cell (s+n) (-1) = (decide (n%3=2) || decide (n%3=free hi) && _)
        simpa only [h, decide_false, Bool.false_and, Bool.or_false] using b h
  apply misses hi w j
  intro k
  have eqn := local_back (r := fun n => cell (s+n) 0) (a := fun n => cell (s+n) (-1))
    (R := centerWord hi) (A := westWord hi w) 5 (j.val+k.val)
    (fun n _ h => windows n (by have := j.isLt; have := k.isLt; omega))
  have eqp := physical s (-1) 5 (j.val+k.val)
  change back (fun n => cell (s+n) 0) (fun n => cell (s+n) (-1)) 5 (j.val+k.val) =
    cell (s+(j.val+k.val)) (-6) at eqp
  rw [eqp] at eqn
  unfold obs
  rw [← eqn, ← Nat.add_assoc,js]
  exact alt k

theorem no_period_three_of_alternating_five
    (hits : ∀ U, ∃ t, U ≤ t ∧ alternatingFive (fun n => cell n (-6)) t) :
    ¬ ∃ T, ∀ t, T ≤ t → center (t+3) = center t := by
  rintro ⟨T,h⟩
  have kill (hi : Bool) (s : Nat)
      (clock : ∀ t, s ≤ t → cell t 0 = wordAt3 (if hi then w011 else w001) (t-s)) : False := by
    obtain ⟨U,avoid⟩ := avoids_alternating_five hi s clock
    obtain ⟨t,ht,found⟩ := hits U
    exact avoid t ht found
  rcases normalize_period_three h with ⟨s,_,w⟩ | ⟨s,_,w⟩
  · exact kill false s w
  · exact kill true s w

end Ruliology.CellularAutomata.Rule30WestSixReading
