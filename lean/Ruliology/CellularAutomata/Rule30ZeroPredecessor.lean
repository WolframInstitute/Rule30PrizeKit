module

public import Ruliology.CellularAutomata.Rule30StripCertificates
public import Ruliology.CellularAutomata.Rule30WhitePadding

@[expose] public section

/-!
The all-white strip has a unique predecessor under a white boundary,
uniformly in strip width. Induction from the boundary forces every cell
of a predecessor of the vacuum to be white.
-/
namespace Ruliology.CellularAutomata.Rule30ZeroPredecessor
open Rule30Jen Rule30StripCertificates Rule30WhitePadding

theorem stripStep_zero_predecessor {K r : Nat} {z : Bool}
    (hr : r < 2^K) (hstep : stripStep K false z r = 0) : r = 0 := by
  have hbits : ∀ k, k < K → r.testBit k = false := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro hk
      have hl : (if k = 0 then false else r.testBit (k-1)) = false := by
        split
        · rfl
        · exact ih (k-1) (by omega) (by omega)
      have h := testBit_stripStep K false z r hr k hk
      rw [hstep, Nat.zero_testBit, hl] at h
      cases hc : r.testBit k
      · rfl
      · simp [rule, hc] at h
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.zero_testBit]
  by_cases hk : k < K
  · exact hbits k hk
  · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hr (Nat.pow_le_pow_right (by decide) (by omega)))

theorem stripStep_zero_iff {K r : Nat} {z : Bool} (hK : 1 ≤ K) (hr : r < 2^K) :
    stripStep K false z r = 0 ↔ r = 0 ∧ z = false := by
  constructor
  · intro h
    have hzero := stripStep_zero_predecessor hr h
    subst r
    have hb := testBit_stripStep K false z 0 (by exact Nat.two_pow_pos K) (K-1) (by omega)
    rw [h, Nat.zero_testBit] at hb
    have hz : z = false := by simpa [rule, show K-1+1=K by omega] using hb.symm
    exact ⟨rfl, hz⟩
  · rintro ⟨rfl,rfl⟩
    simp [stripStep]

/-! ## Non-zero image laws under outer/left black boundaries and all-time vacuum retention -/

/-- **Outer-Black and Left-Black Non-Zero Step Laws (`stripStep_outer_or_left_true_ne_zero`).** -/
theorem stripStep_outer_or_left_true_ne_zero {K r : Nat} (hK : 1 ≤ K) (hr : r < 2 ^ K) :
    stripStep K false true r ≠ 0 ∧ stripStep K true false 0 ≠ 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hiff := (stripStep_zero_iff hK hr).mp h
    exact Bool.noConfusion hiff.2
  · have hb := testBit_stripStep K true false 0 (Nat.two_pow_pos K) 0 (by omega)
    rw [h, Nat.zero_testBit] at hb
    simp [rule] at hb

/-- **All-Time Vacuum Retention Under `image K false` and `zeros K n` (`vacuum_retained_under_image_and_zeros`).** -/
theorem vacuum_retained_under_image_and_zeros (K S : Nat) (h0 : S.testBit 0 = true) :
    (image K false S).testBit 0 = true ∧ ∀ n : Nat, (zeros K n S).testBit 0 = true := by
  have himg : ∀ M : Nat, M.testBit 0 = true → (image K false M).testBit 0 = true := by
    intro M hM0
    have hmem := mem_imageAux (K := K) (a := false) hM0 false (2 ^ K) (Nat.two_pow_pos K)
    have hstep0 : stripStep K false false 0 = 0 := by simp [stripStep]
    rwa [hstep0] at hmem
  refine ⟨himg S h0, fun n => ?_⟩
  induction n with
  | zero => exact h0
  | succ n ih =>
    rw [zeros_succ]
    exact himg (zeros K n S) ih

end Ruliology.CellularAutomata.Rule30ZeroPredecessor
