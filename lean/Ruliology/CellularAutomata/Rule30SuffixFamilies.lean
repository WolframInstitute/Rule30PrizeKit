module

public import Ruliology.CellularAutomata.Rule30ForbiddenSuffix
public import Ruliology.CellularAutomata.Rule30Certificates.WhitePaddingFamilies

@[expose] public section

/-!
# White-padding exclusions for tails of unbounded length

For every Boolean word v, no column of a configuration with a leftmost black cell
eventually repeats `0^r v 011` when r ≥ 10|v|+41. Two further suffixes, `001001`
and `111001`, give the sufficient bound r ≥ 10|v|+71. The prefix v and the
transient are unrestricted. Unlike a finite list of fixed tails, each statement
covers infinitely many tails, with arbitrarily many black bits and alternations.
These are partial results; none settles the alternating period or Problem 1.
-/
namespace Ruliology.CellularAutomata.Rule30SuffixFamilies
open Rule30Jen Rule30Realization Rule30StripCertificates
open Rule30ForbiddenSuffix Rule30Certificates.WhitePaddingFamilies.ForbiddenSuffix

/-- An arbitrary prefix before `011`, not merely a bounded-length tail. -/
theorem no_padding_suffix011_leftFinite {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (v : List Bool) (r : Nat) (hr : 10*v.length+41 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i
      (List.replicate r false ++ (v ++ suffix011)) := by
  exact no_padding_of_forbidden_suffix hlo hzero i v suffix011 5 safe011 r
    (by simp [suffix011]; omega) (by simp [suffix011]; omega)

theorem no_padding_suffix001001_leftFinite {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (v : List Bool) (r : Nat) (hr : 10*v.length+71 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i
      (List.replicate r false ++ (v ++ suffix001001)) := by
  exact no_padding_of_forbidden_suffix hlo hzero i v suffix001001 6 safe001001 r
    (by simp [suffix001001]; omega) (by simp [suffix001001]; omega)

theorem no_padding_suffix111001_leftFinite {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (v : List Bool) (r : Nat) (hr : 10*v.length+71 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i
      (List.replicate r false ++ (v ++ suffix111001)) := by
  exact no_padding_of_forbidden_suffix hlo hzero i v suffix111001 6 safe111001 r
    (by simp [suffix111001]; omega) (by simp [suffix111001]; omega)

theorem no_padding_suffix011_finite {x : Int → Bool}
    (hfin : Rule30PeriodTwoSideways.FinConfig x) (hne : ∃ p, x p = true)
    (i : Int) (v : List Bool) (r : Nat) (hr : 10*v.length+41 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i
      (List.replicate r false ++ (v ++ suffix011)) := by
  obtain ⟨lo, hlo, hzero⟩ := Rule30FiniteConfigs.exists_leftmost hfin hne
  exact no_padding_suffix011_leftFinite hlo hzero i v r hr

theorem no_padding_suffix011_seed (v : List Bool) (r : Nat) (hr : 10*v.length+41 ≤ r) :
    ¬ Rule30StripCertificates.EventuallyWord
      (List.replicate r false ++ (v ++ suffix011)) := by
  exact no_padding_of_forbidden_suffix_seed v suffix011 5 safe011 r
    (by simp [suffix011]; omega) (by simp [suffix011]; omega)

theorem no_padding_suffix001001_seed (v : List Bool) (r : Nat) (hr : 10*v.length+71 ≤ r) :
    ¬ Rule30StripCertificates.EventuallyWord
      (List.replicate r false ++ (v ++ suffix001001)) := by
  exact no_padding_of_forbidden_suffix_seed v suffix001001 6 safe001001 r
    (by simp [suffix001001]; omega) (by simp [suffix001001]; omega)

theorem no_padding_suffix111001_seed (v : List Bool) (r : Nat) (hr : 10*v.length+71 ≤ r) :
    ¬ Rule30StripCertificates.EventuallyWord
      (List.replicate r false ++ (v ++ suffix111001)) := by
  exact no_padding_of_forbidden_suffix_seed v suffix111001 6 safe111001 r
    (by simp [suffix111001]; omega) (by simp [suffix111001]; omega)

/-! ## Finite-configuration (`FinConfig`) exclusions for `suffix001001` and `suffix111001`, and simultaneous three-family exclusion -/

/-- **Finite-Configuration (`FinConfig`) Exclusions for `suffix001001` and `suffix111001`, and Simultaneous Exclusion Above `10 * v.length + 71` (`no_padding_suffix_finite_and_all_three`).** -/
theorem no_padding_suffix_finite_and_all_three {x : Int → Bool}
    (hfin : Rule30PeriodTwoSideways.FinConfig x) (hne : ∃ p, x p = true)
    (i : Int) (v : List Bool) (r : Nat) (hr : 10 * v.length + 71 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ (v ++ suffix011)) ∧
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ (v ++ suffix001001)) ∧
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ (v ++ suffix111001)) := by
  obtain ⟨lo, hlo, hzero⟩ := Rule30FiniteConfigs.exists_leftmost hfin hne
  exact ⟨no_padding_suffix011_leftFinite hlo hzero i v r (by omega),
         no_padding_suffix001001_leftFinite hlo hzero i v r hr,
         no_padding_suffix111001_leftFinite hlo hzero i v r hr⟩

end Ruliology.CellularAutomata.Rule30SuffixFamilies
