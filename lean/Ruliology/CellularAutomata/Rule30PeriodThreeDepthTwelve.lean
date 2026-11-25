module

public import Ruliology.CellularAutomata.Rule30ZeroBoundary

/-!
# A five-sample decoder for the free phase beside 001

Under the zero-wall reduction for 001, depth one has triples (white, free, black).
The complements of the first five forbidden gate words in Rule30PeriodThreeEntry.words001
already suffice. In a window of nine free bits, five readings of depth 12 (one per
triple at phase two) recover the middle free bit. The reconstruction holds for
the actual zero-boundary evolution, with arbitrary window start and initial row.

The paper interpretation of the local code is that a complete run pair of free
bits 1^h 0^l emits 0^3 1^(h-3) 0 1^(l-1) when the output is aligned with the
last input of its five-bit window. Thus there are four white readings per pair.
Their signed contributions along an inward diagonal telescope to the endpoint
difference. Repeated loss at this one depth does not give a spatial induction.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30PeriodThreeDepthTwelve

open Rule30ZeroBoundary (zrow zrow_inv zrow_wall)

/-- Pack a time word with the first reading in the low bit. -/
def pack (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n+1 => (pack (fun i => f (i+1)) n <<< 1) ||| (f 0).toNat

private theorem pack_bit (f : Nat → Bool) (n i : Nat) (h : i < n) :
    (pack f n).testBit i = f i := by
  induction n generalizing f i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => cases e : f 0 <;> simp [pack, e]
    | succ i =>
      have hi := ih (fun j => f (j+1)) i (by omega)
      have one : Nat.testBit 1 (i+1) = false := by
        cases e : Nat.testBit 1 (i+1) with
        | false => rfl
        | true => have := Nat.testBit_one_eq_true_iff_self_eq_zero.mp e; omega
      cases e : f 0 <;> simpa [pack, e, Nat.testBit_shiftLeft, one] using hi

/-- The five forbidden factors on the left free stream, in chronological order. -/
def allowed (w : Nat) : Bool :=
  let avoids (pat width : Nat) := (List.range (10-width)).all fun j =>
    ((w >>> j) % 2^width) != pat
  -- The low-bit-first factors are 101, 010, 0110, 00000, 111111.
  avoids 5 3 && avoids 2 3 && avoids 6 4 && avoids 0 5 && avoids 63 6

/-- Phase pattern of depth one from a packed window of free bits. -/
def tripleBit (w j : Nat) : Bool :=
  if j % 3 = 1 then w.testBit (j / 3) else decide (j % 3 = 2)

private def pair (trace : Nat) : Nat → Nat × Nat
  | 0 => (0, trace)
  | n+1 =>
    let (r,s) := pair trace n
    (s, (s >>> 1) ^^^ (s ||| r))

private theorem pair_sound (L : Nat → Bool) (t w n : Nat)
    (h : ∀ j, j < n → zrow L (t+j) 1 = w.testBit j) (d : Nat) :
    ∀ j, d+j < n →
      (pair w d).1.testBit j = zrow L (t+j) d ∧
      (pair w d).2.testBit j = zrow L (t+j) (d+1) := by
  induction d with
  | zero =>
    intro j hj
    exact ⟨by simp [pair, zrow_wall], (h j (by omega)).symm⟩
  | succ d ih =>
    intro j hj
    obtain ⟨r,s⟩ := ih j (by omega)
    have next := (ih (j+1) (by omega)).2
    refine ⟨s, ?_⟩
    simp only [pair, Nat.testBit_xor, Nat.testBit_shiftRight, Nat.testBit_or]
    rw [Nat.add_comm 1 j, next, s, r, zrow_inv L (t+j) d]
    rfl

/-- Five depth-12 readings, ordered earliest first. -/
def decode (b c d e f : Bool) : Bool :=
  let code := 16*b.toNat + 8*c.toNat + 4*d.toNat + 2*e.toNat + f.toNat
  ![8,12,14,16,17,24,28].contains code

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem table : ∀ w : Fin 512, allowed w.val = true →
    let q := (pair (pack (tripleBit w.val) 27) 11).2
    decode (q.testBit 2) (q.testBit 5) (q.testBit 8) (q.testBit 11) (q.testBit 14) =
      w.val.testBit 4 := by decide

/-- Recover the middle free bit of nine legal triples from the five
phase-two readings at depth 12 in the same physical history. -/
theorem recover_middle (L : Nat → Bool) (t : Nat) (w : Fin 512)
    (hw : allowed w.val = true)
    (trace : ∀ j, j < 27 → zrow L (t+j) 1 = tripleBit w.val j) :
    let q := fun j => zrow L (t+j) 12
    decode (q 2) (q 5) (q 8) (q 11) (q 14) = zrow L (t+13) 1 := by
  have h j (hj : j < 27) : zrow L (t+j) 1 = (pack (tripleBit w.val) 27).testBit j :=
    (trace j hj).trans (pack_bit _ _ _ hj).symm
  have eqn := table w hw
  dsimp only at eqn ⊢
  have read (j : Nat) (hj : 11+j < 27) := (pair_sound L t _ 27 h 11 j hj).2
  rw [read 2 (by decide), read 5 (by decide), read 8 (by decide),
      read 11 (by decide), read 14 (by decide)] at eqn
  exact eqn.trans (trace 13 (by decide)).symm

/-- A period in the late depth-12 observations transfers with the same period
to the free bits four triples later. The window start may have any offset. -/
theorem transfer_period (L : Nat → Bool) (start K P : Nat)
    (legalTail : ∀ k, K ≤ k → ∃ w : Fin 512, allowed w.val = true ∧
      ∀ j, j < 27 → zrow L (start+3*k+j) 1 = tripleBit w.val j)
    (period : ∀ k, K ≤ k →
      zrow L (start+3*(k+P)+2) 12 = zrow L (start+3*k+2) 12)
    (k : Nat) (hk : K ≤ k) :
    zrow L (start+3*(k+4+P)+1) 1 = zrow L (start+3*(k+4)+1) 1 := by
  let q := fun m j => zrow L (start+3*m+j) 12
  have observed (m : Nat) (hm : K ≤ m) :
      decode (q m 2) (q m 5) (q m 8) (q m 11) (q m 14) = zrow L (start+3*m+13) 1 := by
    obtain ⟨w, hw, ht⟩ := legalTail m hm
    exact recover_middle L (start+3*m) w hw ht
  have left := observed (k+P) (by omega)
  have right := observed k hk
  have eqRead (j : Nat) : q (k+P) (3*j+2) = q k (3*j+2) := by
    dsimp only [q]
    rw [show start+3*(k+P)+(3*j+2) = start+3*(k+j+P)+2 by omega,
        show start+3*k+(3*j+2) = start+3*(k+j)+2 by omega]
    exact period (k+j) (by omega)
  rw [eqRead 0, eqRead 1, eqRead 2, eqRead 3, eqRead 4] at left
  rw [show start+3*(k+4+P)+1 = start+3*(k+P)+13 by omega,
      show start+3*(k+4)+1 = start+3*k+13 by omega]
  exact left.symm.trans right

end Ruliology.CellularAutomata.Rule30PeriodThreeDepthTwelve
