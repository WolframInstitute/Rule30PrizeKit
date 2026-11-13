module

public import Ruliology.CellularAutomata.Rule30PackedReconstruction

/-!
# A spacing-three/five gate with seventeen white initial cells

The gate is globally periodic of period 31, with gaps 3,3,3,3,3,3,3,5,5.
Its reconstructed initial row is white at depths 528 through 544. A finite
packed cone is proved equal to the kit's scalar reconstruction. There is no
claim that this gate is realized by a finite driven right half.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30SpacingGapCounterexample

open Rule30ZeroBoundary Rule30SpacingRenormalization
open Rule30PackedReconstruction

def gate31 (r : Nat) : Bool := decide (r%31 ∈ [0,3,6,9,12,15,18,21,26])

def Next35 (G : Nat → Bool) (r : Nat) : Prop :=
  G (r+1) = false ∧ G (r+2) = false ∧
    (G (r+3) = true ∨ (G (r+3) = false ∧ G (r+4) = false ∧ G (r+5) = true))

theorem gate31_periodic (r : Nat) : gate31 (r+31) = gate31 r := by
  simp [gate31]

theorem gate31_residues : ∀ r : Fin 31, gate31 r = true → Next35 gate31 r := by
  unfold Next35
  decide

/-- Every black gate cell is followed by a gap of exactly three or five. -/
theorem gate31_gaps (r : Nat) (hr : gate31 r = true) : Next35 gate31 r := by
  have h := gate31_residues ⟨r%31, Nat.mod_lt r (by decide)⟩
  simp only [Next35, gate31, Nat.add_mod, Nat.mod_mod] at h hr ⊢
  exact h hr

theorem gate31_spaced : Spaced gate31 := by
  intro r
  cases hr : gate31 r with
  | false => simp
  | true =>
      have h := gate31_gaps r hr
      simp only [Next35] at h
      simp [h.1, h.2.1]

-- The finite boundary prefix is generated and cross-checked by the companion
-- Python experiment. Its bits are rechecked below by the ordinary kernel.
def boundaryPrefix : Nat := 114258128115382768325149165979858622949054058922182384017825772718783752107996860734084690853574210578405379476224683606690194761257884644651583470255712858309128126

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem boundary_bits : ∀ t : Fin 545,
    boundaryPrefix.testBit t = boundary gate31 t := by
  decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem window_check : ∀ j : Fin 17,
    (packedRun boundaryPrefix (528+j.val)).1.testBit 0 = false := by
  decide

/-- The seventeen white cells belong to the actual scalar reconstruction. -/
theorem seventeen_white (j : Nat) (hj : j < 17) :
    recon (boundary gate31) (528+j) 0 = false := by
  have h := (packed_sound boundaryPrefix 545 (boundary gate31)
    (fun t ht => boundary_bits ⟨t,ht⟩) (528+j) 0 (by omega)).1
  exact h.symm.trans (window_check ⟨j,hj⟩)

/-- Spacing-three/five gates do not force a black initial cell in every
seventeen-cell interval, even when the gate itself is periodic. -/
theorem no_uniform_gap_bound_sixteen :
    ¬ (∀ G : Nat → Bool, (∀ r, G r = true → Next35 G r) →
      ∀ n, 1 ≤ n → ∃ j, j ≤ 16 ∧ recon (boundary G) (n+j) 0 = true) := by
  intro h
  obtain ⟨j, hj, hb⟩ := h gate31 gate31_gaps 528 (by decide)
  rw [seventeen_white j (by omega)] at hb
  exact Bool.noConfusion hb

/-! ## Multi-period shift invariance of `gate31` and non-spacing of `transform gate31` -/

/-- **Multi-Period Shift Invariance of `gate31` and Non-Spacing of `transform gate31` (`gate31_period_mul_and_not_transform_spaced`).** -/
theorem gate31_period_mul_and_not_transform_spaced (r m : Nat) :
    gate31 (r + m * 31) = gate31 r ∧
    ¬ Spaced (transform gate31) := by
  refine ⟨?_, fun h => ?_⟩
  · induction m with
    | zero => simp
    | succ m ih =>
      rw [show r + (m + 1) * 31 = (r + m * 31) + 31 by rw [Nat.succ_mul]; omega,
          gate31_periodic, ih]
  · have h6 : gate31 (2 + 4) = false :=
      (transform_spaced_iff gate31 gate31_spaced).mp h 2
    have h6_true : gate31 (2 + 4) = true := by decide
    rw [h6_true] at h6
    exact Bool.noConfusion h6

end Ruliology.CellularAutomata.Rule30SpacingGapCounterexample
