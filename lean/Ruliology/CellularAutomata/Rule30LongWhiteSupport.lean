module
public import Ruliology.CellularAutomata.Rule30RunEnvelopes
/-! Color-independent pumping and subset tools for the joint long-white envelope. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30LongWhiteSupport
open Rule30StripCertificates Rule30RunEnvelopes

theorem repeat_add (K : Nat) (c : Bool) (n m A : Nat) :
    applyWord K (List.replicate (n+m) c) A =
      applyWord K (List.replicate m c) (applyWord K (List.replicate n c) A) := by
  have hrep : List.replicate (n+m) c = List.replicate n c ++ List.replicate m c := by
    induction n with
    | zero => simp
    | succ n ih => simp [Nat.succ_add, List.replicate_succ]
  rw [hrep, apply_append]

theorem repeat_closed {K B : Nat} {c : Bool} (h : Sub (image K c B) B) (n : Nat) :
    Sub (applyWord K (List.replicate n c) B) B := by
  induction n with
  | zero => exact sub_refl B
  | succ n ih =>
    rw [List.replicate_succ, applyWord]
    exact sub_trans (word_mono K h _) ih

theorem repeat_capture {K N A B : Nat} {c : Bool}
    (cap : Sub (applyWord K (List.replicate N c) A) B)
    (closed : Sub (image K c B) B) (r : Nat) (hr : N≤r) :
    Sub (applyWord K (List.replicate r c) A) B := by
  rw [show r=N+(r-N) by omega, repeat_add]
  exact sub_trans (word_mono K cap _) (repeat_closed closed _)

theorem sub_of_and {A B : Nat} (h : A &&& B = A) : Sub A B := by
  intro s hs
  have hbit := congrArg (fun n : Nat => n.testBit s) h
  rw [Nat.testBit_and, hs, Bool.true_and] at hbit
  exact hbit

/-- Arbitrary positive black duration, then arbitrary white duration at least G. -/
theorem joint_capture {K G A U B : Nat}
    (enter : Sub (image K true A) U) (black_closed : Sub (image K true U) U)
    (whites : Sub (applyWord K (List.replicate G false) U) B)
    (white_closed : Sub (image K false B) B) (r q : Nat) (hr : 1≤r) (hq : G≤q) :
    Sub (applyWord K (word r q) A) B := by
  have hb := repeat_capture (N:=1) (by simpa [List.replicate_succ, applyWord] using enter) black_closed r hr
  apply pump_capture (r:=r) (G:=G) _ white_closed q hq
  rw [apply_append]
  exact sub_trans (word_mono K hb _) whites

/-! ## Exact bitwise characterizations `Sub A B ↔ A &&& B = A` and `Sub A B ↔ A ||| B = B` -/

/-- **Exact Bitwise Characterizations of `Sub A B` (`sub_iff_and_eq_left_and_or_eq_right`).** -/
theorem sub_iff_and_eq_left_and_or_eq_right (A B : Nat) :
    (Sub A B ↔ A &&& B = A) ∧
    (Sub A B ↔ A ||| B = B) := by
  refine ⟨⟨fun h => Nat.eq_of_testBit_eq fun i => ?_, sub_of_and⟩,
          ⟨fun h => Nat.eq_of_testBit_eq fun i => ?_, fun h s hs => ?_⟩⟩
  · rw [Nat.testBit_and]
    cases ha : A.testBit i
    · simp
    · simp [h i ha]
  · rw [Nat.testBit_or]
    cases ha : A.testBit i
    · simp
    · simp [h i ha]
  · have hbit := congrArg (fun n : Nat => n.testBit s) h
    rw [Nat.testBit_or, hs, Bool.true_or] at hbit
    exact hbit.symm

end Ruliology.CellularAutomata.Rule30LongWhiteSupport
