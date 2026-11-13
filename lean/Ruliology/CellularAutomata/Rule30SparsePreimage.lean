module

public import Ruliology.CellularAutomata.Rule30StripCertificates

@[expose] public section

/-!
Sparse checking of strip predecessor implications. Membership is tested
only at listed target states; a proved bitmask completeness condition
recovers the full predecessor implication, without native evaluation.
-/
namespace Ruliology.CellularAutomata.Rule30SparsePreimage
open Rule30StripCertificates

def stateMask : List Nat → Nat
 | [] => 0
 | s :: L => 2^s ||| stateMask L

theorem mem_stateMask (L : List Nat) (s : Nat) :
    (stateMask L).testBit s = true ↔ s ∈ L := by
  induction L with
  | nil => simp [stateMask]
  | cons r L ih =>
    simp only [stateMask, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true_iff,
      decide_eq_true_eq, ih, List.mem_cons]
    exact or_congr eq_comm Iff.rfl

def restrictedPreCheck (K : Nat) (a : Bool) (Z Q R : Nat) : Bool :=
  allBelow (fun s => ! Z.testBit s ||
    ((! R.testBit (stripStep K a false s) || Q.testBit s) &&
     (! R.testBit (stripStep K a true s) || Q.testBit s))) (2^K)

def sparsePreCheck (K : Nat) (a : Bool) (Q R : Nat) (L : List Nat) : Bool :=
  L.all (fun s =>
    (! R.testBit (stripStep K a false s) || Q.testBit s) &&
    (! R.testBit (stripStep K a true s) || Q.testBit s))

theorem allBelow_of {p : Nat → Bool} (n : Nat)
    (h : ∀ s, s < n → p s = true) : allBelow p n = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold allBelow
    rw [ih (fun s hs => h s (by omega)), h n (by omega)]
    rfl

theorem restricted_of_sparse {K Z Q R : Nat} {a : Bool} {L : List Nat}
    (hmask : Z = stateMask L) (hcheck : sparsePreCheck K a Q R L = true) :
    restrictedPreCheck K a Z Q R = true := by
  apply allBelow_of
  intro s hs
  cases hS : Z.testBit s
  · rfl
  · have hmem : s ∈ L := by
      rw [hmask] at hS
      exact (mem_stateMask L s).mp hS
    have h := List.all_eq_true.mp hcheck s hmem
    simpa [hS] using h

def sparseColConst (Q : Nat) (b : Bool) (L : List Nat) : Bool :=
  L.all (fun s => !Q.testBit s || s.testBit 0 == b)

theorem colConst_inter_of_sparse {K Z Q : Nat} {b : Bool} {L : List Nat}
    (hmask : Z = stateMask L) (hcheck : sparseColConst Q b L = true) :
    colConst K (Z &&& Q) b = true := by
  unfold colConst
  apply allBelow_of
  intro s hs
  rw [Nat.testBit_and]
  cases hS : Z.testBit s
  · rfl
  · have hmem : s ∈ L := by
      rw [hmask] at hS
      exact (mem_stateMask L s).mp hS
    have h := List.all_eq_true.mp hcheck s hmem
    simpa [hS] using h

/-! ## Append homomorphism laws and exact `↔` equivalences between sparse and bitmask checks -/

/-- **Append Homomorphism Laws for `stateMask`, `sparsePreCheck`, and `sparseColConst` (`stateMask_and_sparse_append`).** -/
theorem stateMask_and_sparse_append (K : Nat) (a b : Bool) (Q R : Nat) (L1 L2 : List Nat) :
    stateMask (L1 ++ L2) = (stateMask L1 ||| stateMask L2) ∧
    sparsePreCheck K a Q R (L1 ++ L2) = (sparsePreCheck K a Q R L1 && sparsePreCheck K a Q R L2) ∧
    sparseColConst Q b (L1 ++ L2) = (sparseColConst Q b L1 && sparseColConst Q b L2) := by
  refine ⟨?_, List.all_append, List.all_append⟩
  induction L1 with
  | nil => simp [stateMask]
  | cons s L1 ih =>
    simp only [List.cons_append, stateMask, ih]
    exact (Nat.or_assoc _ _ _).symm

/-- **Exact Bidirectional Equivalence Between Sparse and Bitmask Checks (`restrictedPreCheck_and_colConst_iff_sparse`).** -/
theorem restrictedPreCheck_and_colConst_iff_sparse {K Q R : Nat} {a b : Bool} {L : List Nat}
    (hL : ∀ s ∈ L, s < 2 ^ K) :
    (Rule30SparsePreimage.restrictedPreCheck K a (stateMask L) Q R = true ↔
      sparsePreCheck K a Q R L = true) ∧
    (colConst K (stateMask L &&& Q) b = true ↔
      sparseColConst Q b L = true) := by
  refine ⟨⟨fun h => ?_, restricted_of_sparse rfl⟩, ⟨fun h => ?_, colConst_inter_of_sparse rfl⟩⟩
  · apply List.all_eq_true.mpr
    intro s hs
    have hbit : (stateMask L).testBit s = true := (mem_stateMask L s).mpr hs
    have hall := allBelow_spec h s (hL s hs)
    simpa [hbit] using hall
  · apply List.all_eq_true.mpr
    intro s hs
    have hbit : (stateMask L).testBit s = true := (mem_stateMask L s).mpr hs
    have hall := allBelow_spec h s (hL s hs)
    rw [Nat.testBit_and, hbit, Bool.true_and] at hall
    exact hall

end Ruliology.CellularAutomata.Rule30SparsePreimage
