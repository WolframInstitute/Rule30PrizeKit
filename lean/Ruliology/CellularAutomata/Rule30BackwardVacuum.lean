module

public import Ruliology.CellularAutomata.Rule30BackwardTube
public import Ruliology.CellularAutomata.Rule30WhitePaddingVacuumCriterion

@[expose] public section

/-!
# Backward vacuum obstructions for white-padding families

A finite chain of predecessor implications, starting with the empty set and
ending at the vacuum, proves that no strip can follow a fixed terminal block
and end white. Placing that block at the end of an arbitrarily long white run
and a fixed pulse gives a padding exclusion, without forward reachable-set
stabilization or enumeration of padding lengths.
-/
namespace Ruliology.CellularAutomata.Rule30BackwardVacuum
open Rule30Jen Rule30Realization Rule30StripCertificates
open Rule30WhitePulse Rule30BackwardTube
open Rule30WhitePaddingVacuumCriterion

/-- Replay predecessor implications along an actual driven strip. -/
theorem enc_backwards {x : Int → Bool} {K : Nat} {i : Int} :
    ∀ (w : List Bool) (t : Nat) (Q : Nat → Nat),
      (∀ j, j < w.length → preCheck K (w.getD j false) (Q j) (Q (j+1)) = true) →
      (∀ j, j < w.length → evol x (t+j) i = w.getD j false) →
      (Q w.length).testBit (Rule30FiniteStrips.encRow x (t+w.length) i K) = true →
      (Q 0).testBit (Rule30FiniteStrips.encRow x t i K) = true
  | [], t, Q, _, _, h => by simpa using h
  | a :: w, t, Q, hpre, hdriver, hend => by
    have hnext := enc_backwards (x := x) (K := K) (i := i) w (t+1) (fun j => Q (j+1))
      (fun j hj => by simpa [List.getD_cons_succ, Nat.add_assoc] using hpre (j+1) (by simp; omega))
      (fun j hj => by
        have h := hdriver (j+1) (by simp; omega)
        simpa only [List.getD_cons_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h)
      (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hend)
    exact enc_backward (by simpa using hpre 0 (by simp))
      (by simpa using hdriver 0 (by simp)) (by simpa using hnext)

/-- Empty initial predecessor set certifies that the block cannot end at the vacuum. -/
theorem no_vacuum_of_backward_certificate {x : Int → Bool} (i : Int)
    (w : List Bool) (K : Nat) (Q : Nat → Nat)
    (hstart : Q 0 = 0) (hend : Q w.length = 1)
    (hpre : ∀ j, j < w.length → preCheck K (w.getD j false) (Q j) (Q (j+1)) = true)
    (t : Nat) (hdriver : ∀ j, j < w.length → evol x (t+j) i = w.getD j false) :
    Rule30FiniteStrips.encRow x (t+w.length) i K ≠ 0 := by
  intro hz
  have hlast : (Q w.length).testBit
      (Rule30FiniteStrips.encRow x (t+w.length) i K) = true := by
    rw [hend, hz]
    decide
  have h := enc_backwards w t Q hpre hdriver hlast
  rw [hstart, Nat.zero_testBit] at h
  contradiction

/-- A finite obstruction for `0^N u` excludes every `0^r u` with sufficiently large r.
No stable forward set is needed; all boundary histories and all initial strips are covered. -/
theorem no_padding_of_backward_certificate {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (u : List Bool) (K N : Nat) (Q : Nat → Nat)
    (hstart : Q 0 = 0) (hend : Q (N+u.length) = 1)
    (hpre : ∀ j, j < N+u.length →
      preCheck K ((List.replicate N false ++ u).getD j false) (Q j) (Q (j+1)) = true)
    (r : Nat) (hrN : N ≤ r) (hrpulse : 10*u.length+11 ≤ r)
    (hrwidth : K+9*(u.length+1) ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ u) := by
  intro hword
  obtain ⟨T, hT, hwhite⟩ := white_padding_forces_early_white hlo hzero i u r hrpulse hword
  let w := List.replicate N false ++ u
  have hlen : w.length = N+u.length := by simp [w]
  have hdriver : ∀ s, s < w.length → evol x (T+(r-N)+s) i = w.getD s false := by
    intro s hs
    rw [hT _ (by omega), show T+(r-N)+s-T = r-N+s by omega,
      Nat.mod_eq_of_lt (by rw [hlen] at hs; omega), padding_getD, padding_getD]
    by_cases hsN : s < N
    · simp [hsN, show r-N+s < r by omega]
    · simp [hsN, show ¬r-N+s < r by omega, show r-N+s-r = s-N by omega]
  have hnz := no_vacuum_of_backward_certificate i w K Q hstart
    (by simpa only [hlen] using hend) (by simpa only [hlen] using hpre) (T+(r-N)) hdriver
  have htime : T+(r-N)+w.length = T+(r+u.length) := by rw [hlen]; omega
  rw [htime] at hnz
  have he := Rule30FiniteStrips.enc_encRow (x := x) K (T+(r+u.length)) i
  obtain ⟨j, hjK, hjblack⟩ := enc_nonzero_has_black he hnz
  have hboundary : ∀ s, s < j → evol x (T+(r+u.length)+s) i = false := by
    intro s hs
    rw [hT _ (by omega), show T+(r+u.length)+s-T = s+1*(r+u.length) by omega,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega), padding_getD]
    simp [show s < r by omega]
  have hb := black_reaches_boundary x j i (T+(r+u.length)) hboundary hjblack
  have hw := hwhite 1 j (by omega)
  simp only [Nat.one_mul] at hw
  rw [hb] at hw
  contradiction

/-! ## Finite-configuration (`FinConfig`) and single-seed backward-certificate exclusions -/

/-- **Finite-Configuration (`FinConfig`) and Single-Seed Backward-Certificate Exclusions (`no_padding_of_backward_certificate_finite_and_seed`).** -/
theorem no_padding_of_backward_certificate_finite_and_seed
    (u : List Bool) (K N : Nat) (Q : Nat → Nat)
    (hstart : Q 0 = 0) (hend : Q (N + u.length) = 1)
    (hpre : ∀ j, j < N + u.length →
      preCheck K ((List.replicate N false ++ u).getD j false) (Q j) (Q (j + 1)) = true)
    (r : Nat) (hrN : N ≤ r) (hrpulse : 10 * u.length + 11 ≤ r)
    (hrwidth : K + 9 * (u.length + 1) ≤ r) :
    (∀ {x : Int → Bool}, Rule30PeriodTwoSideways.FinConfig x → (∃ p, x p = true) → ∀ i : Int,
      ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ u)) ∧
    ¬ Rule30StripCertificates.EventuallyWord (List.replicate r false ++ u) := by
  refine ⟨fun hfin hne i => ?_, ?_⟩
  · obtain ⟨lo, hlo, hzero⟩ := Rule30FiniteConfigs.exists_leftmost hfin hne
    exact no_padding_of_backward_certificate hlo hzero i u K N Q hstart hend hpre r hrN hrpulse hrwidth
  · have hzero : ∀ p : Int, p < 0 → seed p = false := fun p hp => by simp [seed, show p ≠ 0 by omega]
    have h := no_padding_of_backward_certificate (x := seed) (lo := 0) (by decide) hzero 0 u K N Q
      hstart hend hpre r hrN hrpulse hrwidth
    simpa only [Rule30FiniteStrips.EventuallyWord, Rule30StripCertificates.EventuallyWord, evol_seed] using h

end Ruliology.CellularAutomata.Rule30BackwardVacuum
