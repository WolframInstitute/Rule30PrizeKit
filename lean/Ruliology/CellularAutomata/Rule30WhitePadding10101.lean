module

public import Ruliology.CellularAutomata.Rule30RestrictedBackwardTube
public import Ruliology.CellularAutomata.Rule30WordRotation
public import Ruliology.CellularAutomata.Rule30Certificates.FiveTailTube

/-!
Exclude sufficiently white-padded repetition of the five-bit tail
10101. The finite endpoint-conditioned tube certifies the backward
implications, then the analytic white-pulse bound handles all padding lengths.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30WhitePadding10101
open Rule30Jen Rule30Realization Rule30StripCertificates
open Rule30RestrictedBackwardTube

/-- The first five-bit exceptional tail, proved with an endpoint-conditioned tube. -/
theorem no_padding_10101_leftFinite {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (r : Nat) (hr : 69 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i
      (List.replicate r false ++ [true,false,true,false,true]) := by
  apply no_padding_of_endpoint_tube hlo hzero i Rule30Certificates.FiveTailTube.Tube10101.tail
    16 24 Rule30Certificates.FiveTailTube.Tube10101.Z Rule30Certificates.FiveTailTube.Tube10101.Q
    Rule30Certificates.FiveTailTube.Tube10101.P Rule30Certificates.FiveTailTube.Tube10101.S
    (fun d => decide (d ≤ 8)) (fun _ => false) (by decide)
    Rule30Certificates.FiveTailTube.Tube10101.Zzero Rule30Certificates.FiveTailTube.Tube10101.Zfixed
    Rule30Certificates.FiveTailTube.Tube10101.Szero Rule30Certificates.FiveTailTube.Tube10101.Pend
    Rule30Certificates.FiveTailTube.Tube10101.Qstart Rule30Certificates.FiveTailTube.Tube10101.Qend
  · intro d hd
    exact Rule30Certificates.FiveTailTube.Tube10101.Qstep d hd
  · intro j hj
    exact Rule30Certificates.FiveTailTube.Tube10101.Pstep j hj
  · intro j hj
    exact Rule30Certificates.FiveTailTube.Tube10101.Sstep j hj
  · exact Rule30Certificates.FiveTailTube.Tube10101.Qforce
  · exact Rule30Certificates.FiveTailTube.Tube10101.Pforce
  · simpa only [Rule30Certificates.FiveTailTube.Tube10101.tail, List.length_cons, List.length_nil] using
      (show 10*5+11 ≤ r by omega)
  · simpa only [Rule30Certificates.FiveTailTube.Tube10101.tail, List.length_cons, List.length_nil] using
      (show 16-1+9*(5+1) ≤ r by omega)
  · omega

theorem no_padding_10101 (r : Nat) (hr : 69 ≤ r) :
    ¬ Rule30StripCertificates.EventuallyWord
      (List.replicate r false ++ [true,false,true,false,true]) := by
  have hzero : ∀ p : Int, p < 0 → seed p = false := by
    intro p hp
    simp [seed, show p ≠ 0 by omega]
  have h := no_padding_10101_leftFinite (x := seed) (lo := 0) (by decide) hzero 0 r hr
  simpa only [Rule30FiniteStrips.EventuallyWord,
    Rule30StripCertificates.EventuallyWord, evol_seed] using h

theorem no_padding_10101_finite {x : Int → Bool}
    (hfin : Rule30PeriodTwoSideways.FinConfig x) (hne : ∃ p, x p = true)
    (i : Int) (r : Nat) (hr : 69 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i
      (List.replicate r false ++ [true,false,true,false,true]) := by
  obtain ⟨lo,hlo,hzero⟩ := Rule30FiniteConfigs.exists_leftmost hfin hne
  exact no_padding_10101_leftFinite hlo hzero i r hr

/-! ## Two-sided split white-padding and post-padded exclusions for `10101` -/

/-- **Two-Sided Split White-Padding and Post-Padded Exclusions for `10101` (`no_padding_10101_split_and_post`):**
for all `a, b : Nat` with `69 ≤ a + b`, `(List.replicate a false ++ [true, false, true, false, true]) ++ List.replicate b false`
is excluded at every column `i` of every left-bounded or non-zero finite configuration. -/
theorem no_padding_10101_split_and_post (a b : Nat) (hab : 69 ≤ a + b) :
    (∀ {x : Int → Bool} {lo : Int}, x lo = true → (∀ p, p < lo → x p = false) → ∀ i : Int,
      ¬ Rule30FiniteStrips.EventuallyWord x i
        ((List.replicate a false ++ [true, false, true, false, true]) ++ List.replicate b false)) ∧
    (∀ {x : Int → Bool}, Rule30PeriodTwoSideways.FinConfig x → (∃ p, x p = true) → ∀ i : Int,
      ¬ Rule30FiniteStrips.EventuallyWord x i
        ([true, false, true, false, true] ++ List.replicate (a + b) false)) := by
  have hrep : ∀ m n : Nat, List.replicate m false ++ List.replicate n false = List.replicate (m + n) false := by
    intro m n
    induction m with
    | zero => simp
    | succ m ih => simp [List.replicate_succ, Nat.succ_add, ih]
  have hleft : ∀ (a' b' : Nat), 69 ≤ a' + b' →
      ∀ {x : Int → Bool} {lo : Int}, x lo = true → (∀ p, p < lo → x p = false) → ∀ i : Int,
      ¬ Rule30FiniteStrips.EventuallyWord x i
        ((List.replicate a' false ++ [true, false, true, false, true]) ++ List.replicate b' false) := by
    intro a' b' hab' x lo hlo hzero i hword
    have hrot := Rule30WordRotation.eventuallyWord_swap (by simp; omega) hword
    rw [← List.append_assoc, hrep b' a'] at hrot
    exact no_padding_10101_leftFinite hlo hzero i (b' + a') (by omega) hrot
  refine ⟨hleft a b hab, ?_⟩
  intro x hfin hne i hword
  obtain ⟨lo, hlo, hzero⟩ := Rule30FiniteConfigs.exists_leftmost hfin hne
  have hword0 : Rule30FiniteStrips.EventuallyWord x i
      ((List.replicate 0 false ++ [true, false, true, false, true]) ++ List.replicate (a + b) false) := by
    simpa using hword
  exact hleft 0 (a + b) (by omega) hlo hzero i hword0

end Ruliology.CellularAutomata.Rule30WhitePadding10101
