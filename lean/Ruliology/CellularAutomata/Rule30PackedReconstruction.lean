module

public import Ruliology.CellularAutomata.Rule30SpacingRenormalization

/-!
# Finite packed checks of the scalar sideways reconstruction

Each natural number holds a column's successive times in its bits. A right
shift reads the next time, so the packed update is the scalar inverse rule.
The soundness bound explicitly excludes the unrepresented future boundary.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30PackedReconstruction

open Rule30ZeroBoundary Rule30SpacingRenormalization

noncomputable def advance : Nat → Nat → Nat → Nat × Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat × Nat)
    (fun a b => (a,b))
    (fun _ ih a b => ih b (Nat.xor (Nat.shiftRight b 1) (Nat.lor b a)))

theorem advance_zero (a b : Nat) : advance 0 a b = (a,b) := rfl

theorem advance_succ (k a b : Nat) :
    advance (k+1) a b = advance k b ((b >>> 1) ^^^ (b ||| a)) := rfl

theorem advance_last : ∀ k a b,
    advance (k+1) a b =
      ((advance k a b).2,
       ((advance k a b).2 >>> 1) ^^^ ((advance k a b).2 ||| (advance k a b).1))
  | 0,a,b => rfl
  | k+1,a,b => by
      rw [advance_succ, advance_succ k a b, advance_last]

noncomputable def packedRun (B k : Nat) : Nat × Nat := advance k 0 B

theorem packedRun_zero (B : Nat) : packedRun B 0 = (0,B) := rfl

theorem packedRun_succ (B k : Nat) :
    packedRun B (k+1) =
      ((packedRun B k).2,
       ((packedRun B k).2 >>> 1) ^^^ ((packedRun B k).2 ||| (packedRun B k).1)) :=
  advance_last k 0 B

/-- Every checked bit agrees with scalar reconstruction inside its finite cone. -/
theorem packed_sound (B H : Nat) (b : Nat → Bool)
    (hb : ∀ t, t < H → B.testBit t = b t) : ∀ k t, t+k < H →
    (packedRun B k).1.testBit t = recon b k t ∧
    (packedRun B k).2.testBit t = recon b (k+1) t := by
  intro k
  induction k with
  | zero =>
      intro t ht
      exact ⟨by simp [packedRun_zero, recon], hb t ht⟩
  | succ k ih =>
      intro t ht
      have h0 := ih t (by omega)
      have h1 := ih (t+1) (by omega)
      rw [packedRun_succ]
      refine ⟨h0.2, ?_⟩
      simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftRight]
      rw [show 1+t=t+1 by omega, h1.2, h0.2, h0.1]
      exact (recon_two b k t).symm

/-! ## Semigroup composition law for `advance` and bit-`0` initial row extraction -/

/-- **Semigroup Composition Law for `advance` and Bit-`0` Initial Row Extraction (`advance_add_and_packedRun_initial_row`).** -/
theorem advance_add_and_packedRun_initial_row (m n a b B H : Nat) (f : Nat → Bool)
    (hf : ∀ t, t < H → B.testBit t = f t) :
    advance (m + n) a b = advance n (advance m a b).1 (advance m a b).2 ∧
    ∀ k, k < H →
      (packedRun B k).1.testBit 0 = recon f k 0 ∧
      (packedRun B k).2.testBit 0 = recon f (k + 1) 0 := by
  refine ⟨?_, fun k hk => ?_⟩
  · induction m generalizing a b with
    | zero => rw [Nat.zero_add]; rfl
    | succ m ih =>
      rw [Nat.succ_add, advance_succ, advance_succ]
      exact ih _ _
  · exact packed_sound B H f hf k 0 (by omega)

end Ruliology.CellularAutomata.Rule30PackedReconstruction
