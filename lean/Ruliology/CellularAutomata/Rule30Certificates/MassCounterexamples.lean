module

public import Ruliology.CellularAutomata.Rule30PeriodTwoMass

@[expose] public section

/-!
# Finite witnesses for the period-two mass conjectures

The row with 77 ones has a G trace through 541 readings, including the even
prefix of length 540. A forward scan checks a 2638-one row through 18475
readings. `Rule30MassCounterexamples` propagates the latter witness to
arbitrarily large horizons using a finite moving strip.
-/

namespace Ruliology.CellularAutomata.Rule30MassCounterexamples.Certificates

open Ruliology.CellularAutomata.Rule30ZeroBoundary.IntegerForm (F iter)
open Rule30PeriodTwoMass (tr wt gstep GWord ConjS ConjSEven MassFloor)

/-- Bits 2 and 4, together with bits 1, 8, ..., 519. -/
def seed75 : Nat := 20 + 2 * ((128 ^ 75 - 1) / 127)

set_option exponentiation.threshold 1024
set_option maxRecDepth 8192
set_option maxHeartbeats 0

/-- The trace passes exactly 541 checks and fails at time 541. -/
theorem counterexample_trace :
    GWord (tr seed75) 541 ∧ gstep (tr seed75) 541 = false := by
  constructor
  · intro t ht
    revert t
    decide +kernel
  · decide +kernel

/-- The same witness refutes the general and even sharp mass conjectures. In
fact the weaker floor with coefficient seven and additive constant one fails. -/
theorem sharp_mass_conjectures_false :
    ¬ ConjS ∧ ¬ ConjSEven ∧ ¬ MassFloor 7 1 := by
  have theWord := counterexample_trace.1
  have evenWord : GWord (tr seed75) 540 := fun t ht => theWord t (by omega)
  have bits : seed75 < 2 ^ 540 := by decide +kernel
  have wt540 : wt 540 seed75 = 77 := by decide +kernel
  have wt541 : wt 541 seed75 = 77 := by decide +kernel
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have bad := h 540 seed75 (by decide) bits evenWord
    rw [wt540] at bad
    omega
  · intro h
    have bad := h 270 seed75 (by decide) bits evenWord
    change 540 + 5 ≤ 7 * wt 540 seed75 at bad
    rw [wt540] at bad
    omega
  · intro h
    have bad := h 541 seed75 (by decide +kernel) theWord
    rw [wt541] at bad
    omega


private def prev (t : Nat) := if t % 2 = 1 then t - 1 else t - 2

private def checkHead (t : Nat) (old bit : Bool) :=
  if t = 0 then !bit else if t % 2 = 1 then bit else old || bit

private def scan : Nat → Nat → Nat → Bool → Bool
  | 0, _, _, _ => true
  | n + 1, t, x, old =>
    let bit := x.testBit 0
    checkHead t old bit && scan n (t + 1) (F x) (if t % 2 = 1 then old else bit)

private theorem head_eq (Y t : Nat) :
    checkHead t (tr Y (prev t)) (tr Y t) = gstep (tr Y) t := by
  by_cases h : t = 0
  · subst t; rfl
  · by_cases p : t % 2 = 1 <;> simp [checkHead, gstep, prev, h, p]

private theorem prev_next (Y t : Nat) :
    (if t % 2 = 1 then tr Y (prev t) else tr Y t) = tr Y (prev (t + 1)) := by
  rcases Nat.mod_two_eq_zero_or_one t with h | h
  · have e : (t + 1) % 2 = 1 := by omega
    simp [h, e, prev]
  · have e : (t + 1) % 2 = 0 := by omega
    simp [h, e, prev]

private theorem scan_sound (Y : Nat) (n t : Nat)
    (ok : scan n t (iter F t Y) (tr Y (prev t)) = true) :
    ∀ i, i < n → gstep (tr Y) (t + i) = true := by
  induction n generalizing t with
  | zero => intro i hi; omega
  | succ n ih =>
    change (checkHead t (tr Y (prev t)) (tr Y t) &&
      scan n (t + 1) (iter F (t + 1) Y)
        (if t % 2 = 1 then tr Y (prev t) else tr Y t)) = true at ok
    simp only [Bool.and_eq_true, head_eq, prev_next] at ok
    intro i hi
    cases i with
    | zero => simpa using ok.1
    | succ i =>
      have good := ih (t + 1) ok.2 i (by omega)
      rw [show t + (i + 1) = (t + 1) + i by omega]
      exact good

/-- The clean, seven-spaced prefix ends before position 18446. A single
additional black site is placed seventeen cells farther out. -/
def seed2635 : Nat := 20 + 2 * ((128 ^ 2635 - 1) / 127) + 2 ^ 18463

set_option exponentiation.threshold 20000
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem counterexample2635 : GWord (tr seed2635) 18475 ∧ wt 18475 seed2635 = 2638 := by
  constructor
  · have checks : scan 18475 0 seed2635 (tr seed2635 (prev 0)) = true := by decide +kernel
    intro i hi
    simpa only [Nat.zero_add] using scan_sound seed2635 18475 0 checks i hi
  · decide +kernel

theorem mass_floor_eight_false : ¬ MassFloor 7 8 := by
  intro h
  have bad := h 18475 seed2635 (by decide +kernel) counterexample2635.1
  rw [counterexample2635.2] at bad
  omega


end Ruliology.CellularAutomata.Rule30MassCounterexamples.Certificates
