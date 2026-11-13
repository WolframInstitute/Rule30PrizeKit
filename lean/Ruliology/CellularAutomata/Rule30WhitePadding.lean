module

public import Ruliology.CellularAutomata.Rule30StripCertificates

@[expose] public section

/-!
# Pumping a white run in a Rule 30 strip certificate

Finite stabilization of three zero-driven reachable sets proves a strip certificate
for every sufficiently long white prefix, rather than just one finite word.
The checks and the pumping argument use the existing sound strip abstraction.
-/

namespace Ruliology.CellularAutomata.Rule30WhitePadding

open Rule30StripCertificates

def zeros (K n S : Nat) : Nat := applyWord K (List.replicate n false) S

def Forces (K S : Nat) : Bool := colConst K S false || colConst K S true

theorem applyWord_append (K : Nat) (u v : List Bool) (S : Nat) :
    applyWord K (u ++ v) S = applyWord K v (applyWord K u S) := by
  induction u generalizing S with
  | nil => rfl
  | cons a u ih => exact ih (image K a S)

theorem zeros_add (K a b S : Nat) : zeros K (a + b) S = zeros K b (zeros K a S) := by
  have hrep : List.replicate (a + b) false = List.replicate a false ++ List.replicate b false := by
    induction a with
    | zero => simp
    | succ a => simp [Nat.succ_add, List.replicate_succ]
  unfold zeros
  rw [hrep, applyWord_append]

theorem zeros_succ (K n S : Nat) : zeros K (n + 1) S = image K false (zeros K n S) := by
  simpa [zeros, applyWord] using zeros_add K n 1 S

theorem zeros_stable (K N S : Nat)
    (h : zeros K (N + 1) S = zeros K N S) :
    ∀ r, N ≤ r → zeros K r S = zeros K N S := by
  intro r hr
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hr
  induction d with
  | zero => simp
  | succ d ih =>
    rw [show N + (d + 1) = (N + d) + 1 by omega, zeros_succ, ih (by omega)]
    exact (zeros_succ K N S).symm.trans h

/-- A finite check for the family `0^r u`, for all `r ≥ N`.
Two periods reach `S2`; the three zero-driven sets stabilize by `N`.
The white-phase forcing checks cover the finite prefix, the stable zero tail,
and the finitely many phases of `u`. -/
theorem padding_strip (u : List Bool) (K N S1 S2 : Nat)
    (hS1 : applyWord K u (zeros K N (fullSet K)) = S1)
    (hS2 : applyWord K u (zeros K N S1) = S2)
    (h0 : zeros K (N + 1) (fullSet K) = zeros K N (fullSet K))
    (h1 : zeros K (N + 1) S1 = zeros K N S1)
    (h2 : zeros K (N + 1) S2 = zeros K N S2)
    (hret : subsetB K (applyWord K u (zeros K N S2)) S2 = true)
    (hpref : (List.range (N + 1)).all (fun j => Forces K (zeros K j S2)) = true)
    (htail : (List.range u.length).all (fun j =>
      u.getD j false || Forces K (applyWord K (u.take j) (zeros K N S2))) = true)
    (r : Nat) (hr : N ≤ r) :
    stripCert (List.replicate r false ++ u) K 2 = true := by
  let w := List.replicate r false ++ u
  have hpump (S : Nat) (hs : zeros K (N + 1) S = zeros K N S) :
      applyWord K w S = applyWord K u (zeros K N S) := by
    rw [show w = List.replicate r false ++ u from rfl, applyWord_append]
    rw [← zeros, zeros_stable K N S hs r hr]
  have hreach : iterW K w 2 (fullSet K) = S2 := by
    simp only [iterW]
    rw [hpump _ h0, hS1, hpump _ h1, hS2]
  change stripCert w K 2 = true
  unfold stripCert
  rw [hreach, Bool.and_eq_true]
  refine ⟨?_, List.all_eq_true.mpr ?_⟩
  · rw [hpump _ h2]
    exact hret
  · intro j hj
    have hjlt : j < r + u.length := by simpa [w] using List.mem_range.mp hj
    by_cases hjr : j < r
    · have hwj : w.getD j false = false := by
        change (List.replicate r false ++ u).getD j false = false
        rw [List.getD_eq_getElem?_getD,
          List.getElem?_append_left (l₁ := List.replicate r false) (l₂ := u) (by simpa using hjr)]
        simp [List.getElem?_replicate_of_lt hjr]
      have htake : w.take j = List.replicate j false := by
        rw [List.take_append_of_le_length (by simpa using Nat.le_of_lt hjr)]
        simp [Nat.min_eq_left (Nat.le_of_lt hjr)]
      rw [hwj, Bool.false_or, htake]
      change Forces K (zeros K j S2) = true
      by_cases hjN : j ≤ N
      · exact List.all_eq_true.mp hpref j (List.mem_range.mpr (by omega))
      · rw [zeros_stable K N S2 h2 j (by omega)]
        exact List.all_eq_true.mp hpref N (List.mem_range.mpr (by omega))
    · have hrj : r ≤ j := by omega
      have hju : j - r < u.length := by omega
      have hwj : w.getD j false = u.getD (j - r) false := by
        change (List.replicate r false ++ u).getD j false = u.getD (j - r) false
        rw [List.getD_eq_getElem?_getD,
          List.getElem?_append_right (l₁ := List.replicate r false) (l₂ := u) (by simpa using hrj)]
        simp [List.getD_eq_getElem?_getD]
      have htake : w.take j = List.replicate r false ++ u.take (j - r) := by
        simpa [w, show r + (j - r) = j by omega] using
          (List.take_length_add_append (l₁ := List.replicate r false) (l₂ := u) (j - r))
      rw [hwj, htake, applyWord_append, ← zeros, zeros_stable K N S2 h2 r hr]
      simpa only [Forces, Bool.or_assoc] using
        List.all_eq_true.mp htail (j - r) (List.mem_range.mpr hju)

/-- Every word in a finitely checked white-padding family is excluded forever. -/
theorem no_padding_word (u : List Bool) (K N S1 S2 : Nat)
    (hS1 : applyWord K u (zeros K N (fullSet K)) = S1)
    (hS2 : applyWord K u (zeros K N S1) = S2)
    (h0 : zeros K (N + 1) (fullSet K) = zeros K N (fullSet K))
    (h1 : zeros K (N + 1) S1 = zeros K N S1)
    (h2 : zeros K (N + 1) S2 = zeros K N S2)
    (hret : subsetB K (applyWord K u (zeros K N S2)) S2 = true)
    (hpref : (List.range (N + 1)).all (fun j => Forces K (zeros K j S2)) = true)
    (htail : (List.range u.length).all (fun j =>
      u.getD j false || Forces K (applyWord K (u.take j) (zeros K N S2))) = true)
    (hK : 1 ≤ K) (hN : 0 < N) (r : Nat) (hr : N ≤ r) :
    ¬ EventuallyWord (List.replicate r false ++ u) := by
  exact not_eventually_word_strip _ K 2 hK (by simp; omega)
    (padding_strip u K N S1 S2 hS1 hS2 h0 h1 h2 hret hpref htail r hr)

/-! ## Fixed-point characterization of `zeros_stable`, vacuity of `Forces K 0`, and bit-0 agreement -/

/-- **Fixed-Point Equivalence and Additive Shift Invariance for `zeros` (`zeros_zero_and_stable_fixed_point`).** -/
theorem zeros_zero_and_stable_fixed_point (K N S : Nat) :
    zeros K 0 S = S ∧
    (zeros K (N + 1) S = zeros K N S ↔ image K false (zeros K N S) = zeros K N S) ∧
    (zeros K (N + 1) S = zeros K N S → ∀ m : Nat, zeros K (N + m) S = zeros K N S) := by
  refine ⟨rfl, ?_, fun h m => zeros_stable K N S h (N + m) (by omega)⟩
  rw [zeros_succ]

/-- **Empty-Set Vacuity of `Forces` and Bit-0 Agreement Across Forced States (`forces_zero_and_bit_agreement`).** -/
theorem forces_zero_and_bit_agreement (K S s1 s2 : Nat) :
    Forces K 0 = true ∧
    (Forces K S = true → s1 < 2 ^ K → s2 < 2 ^ K →
      S.testBit s1 = true → S.testBit s2 = true → s1.testBit 0 = s2.testBit 0) := by
  have hcol0 : ∀ n, allBelow (fun s => !(0 : Nat).testBit s || (s.testBit 0 == false)) n = true := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => unfold allBelow; rw [ih]; simp
  refine ⟨by unfold Forces colConst; rw [hcol0 (2 ^ K), Bool.true_or], ?_⟩
  intro hf hs1 hs2 h1 h2
  unfold Forces at hf
  rcases Bool.or_eq_true_iff.mp hf with hc0 | hc1
  · have a1 := allBelow_spec hc0 s1 hs1
    have a2 := allBelow_spec hc0 s2 hs2
    rw [h1, Bool.not_true, Bool.false_or, beq_iff_eq] at a1
    rw [h2, Bool.not_true, Bool.false_or, beq_iff_eq] at a2
    exact a1.trans a2.symm
  · have a1 := allBelow_spec hc1 s1 hs1
    have a2 := allBelow_spec hc1 s2 hs2
    rw [h1, Bool.not_true, Bool.false_or, beq_iff_eq] at a1
    rw [h2, Bool.not_true, Bool.false_or, beq_iff_eq] at a2
    exact a1.trans a2.symm

end Ruliology.CellularAutomata.Rule30WhitePadding
