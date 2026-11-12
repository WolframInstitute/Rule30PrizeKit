module

public import Ruliology.CellularAutomata.Rule30WhitePaddingVacuumCriterion

@[expose] public section

/-!
# Forbidden suffixes give white-padding exclusions with arbitrary prefixes

If a finite driver word cannot send any width-K strip to the all-white strip,
then it cannot be the suffix of a sufficiently white-padded eventual period.
The part of the tail preceding that suffix is arbitrary and has unbounded length.
This strengthens the vacuum-avoidance interface: no stabilized reachable set is
needed, and a single certificate works for infinitely many different tails.

The analytic white-pulse estimate remains essential. These results do not exclude
every periodic word, in particular the alternating period is still open.
-/
namespace Ruliology.CellularAutomata.Rule30ForbiddenSuffix
open Rule30Jen Rule30Realization Rule30StripCertificates
open Rule30WhitePulse Rule30WhitePaddingVacuumCriterion

/-- A vacuum-free image of the full strip set excludes every white-padded tail
ending in the certified suffix, regardless of the preceding tail bits. -/
theorem no_padding_of_forbidden_suffix {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (lead suffix : List Bool) (K : Nat)
    (hsafe : (applyWord K suffix (fullSet K)).testBit 0 = false)
    (r : Nat) (hrpulse : 10*(lead.length+suffix.length)+11 ≤ r)
    (hrwidth : K+9*(lead.length+suffix.length+1) ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i
      (List.replicate r false ++ (lead ++ suffix)) := by
  intro hword
  obtain ⟨T, hT, hwhite⟩ := white_padding_forces_early_white hlo hzero i
    (lead ++ suffix) r (by simpa using hrpulse) hword
  have hdriver : ∀ s, s < suffix.length →
      evol x (T+r+lead.length+s) i = suffix.getD s false := by
    intro s hs
    rw [hT _ (by omega), List.length_append,
      show T+r+lead.length+s-T = r+lead.length+s by omega,
      Nat.mod_eq_of_lt (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (l₁ := List.replicate r false)
      (l₂ := lead ++ suffix) (by simp; omega)]
    simp only [List.length_replicate]
    rw [show r+lead.length+s-r = lead.length+s by omega,
      List.getElem?_append_right (l₁ := lead) (l₂ := suffix) (by omega),
      show lead.length+s-lead.length = s by omega]
  have he0 := Rule30FiniteStrips.enc_encRow (x := x) K (T+r+lead.length) i
  have hfull : (fullSet K).testBit
      (Rule30FiniteStrips.encRow x (T+r+lead.length) i K) = true := by
    unfold fullSet
    rw [Nat.testBit_two_pow_sub_one]
    exact decide_eq_true he0.1
  obtain ⟨v, he, hv⟩ := Rule30FiniteStrips.enc_applyWord suffix
    (T+r+lead.length) _ (fullSet K) he0 hfull hdriver
  have hv0 : v ≠ 0 := by
    intro hz
    subst v
    rw [hsafe] at hv
    contradiction
  obtain ⟨j, hjK, hjblack⟩ := enc_nonzero_has_black he hv0
  have hboundary : ∀ s, s < j →
      evol x (T+r+lead.length+suffix.length+s) i = false := by
    intro s hs
    have hsr : s < r := by omega
    rw [hT _ (by omega), List.length_append,
      show T+r+lead.length+suffix.length+s-T =
        s+1*(r+(lead.length+suffix.length)) by omega,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (l₁ := List.replicate r false)
      (l₂ := lead ++ suffix) (by simpa using hsr),
      List.getElem?_replicate_of_lt hsr]
    rfl
  have hblack := black_reaches_boundary x j i
    (T+r+lead.length+suffix.length) hboundary hjblack
  have hwh := hwhite 1 j (by simp; omega)
  simp only [List.length_append, Nat.one_mul] at hwh
  rw [show T+(r+(lead.length+suffix.length))+j =
    T+r+lead.length+suffix.length+j by omega, hblack] at hwh
  contradiction

/-- The same arbitrary-lead criterion for every nonzero finite initial pattern. -/
theorem no_padding_of_forbidden_suffix_finite {x : Int → Bool}
    (hfin : Rule30PeriodTwoSideways.FinConfig x) (hne : ∃ p, x p = true)
    (i : Int) (lead suffix : List Bool) (K : Nat)
    (hsafe : (applyWord K suffix (fullSet K)).testBit 0 = false)
    (r : Nat) (hrpulse : 10*(lead.length+suffix.length)+11 ≤ r)
    (hrwidth : K+9*(lead.length+suffix.length+1) ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i
      (List.replicate r false ++ (lead ++ suffix)) := by
  obtain ⟨lo, hlo, hzero⟩ := Rule30FiniteConfigs.exists_leftmost hfin hne
  exact no_padding_of_forbidden_suffix hlo hzero i lead suffix K hsafe r hrpulse hrwidth

/-- Single-seed version, with arbitrary transient and arbitrary lead length. -/
theorem no_padding_of_forbidden_suffix_seed
    (lead suffix : List Bool) (K : Nat)
    (hsafe : (applyWord K suffix (fullSet K)).testBit 0 = false)
    (r : Nat) (hrpulse : 10*(lead.length+suffix.length)+11 ≤ r)
    (hrwidth : K+9*(lead.length+suffix.length+1) ≤ r) :
    ¬ Rule30StripCertificates.EventuallyWord
      (List.replicate r false ++ (lead ++ suffix)) := by
  have hzero : ∀ p : Int, p < 0 → seed p = false := by
    intro p hp
    simp [seed, show p ≠ 0 by omega]
  have h := no_padding_of_forbidden_suffix (x := seed) (lo := 0) (by decide) hzero
    0 lead suffix K hsafe r hrpulse hrwidth
  simpa only [Rule30FiniteStrips.EventuallyWord,
    Rule30StripCertificates.EventuallyWord, evol_seed] using h

/-! ### Empty-lead pure white-padding exclusions for forbidden words -/

/-- **Pure White-Padded Forbidden-Word Exclusions Across Left-Bounded, Finite, and Seed Starts (`no_padding_of_forbidden_word_all`).** -/
theorem no_padding_of_forbidden_word_all (suffix : List Bool) (K r : Nat)
    (hsafe : (Rule30StripCertificates.applyWord K suffix (Rule30StripCertificates.fullSet K)).testBit 0 = false)
    (hrpulse : 10 * suffix.length + 11 ≤ r)
    (hrwidth : K + 9 * (suffix.length + 1) ≤ r) :
    (∀ {x : Int → Bool} {lo : Int}, x lo = true → (∀ p, p < lo → x p = false) → ∀ i : Int,
      ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ suffix)) ∧
    (∀ {x : Int → Bool}, Rule30PeriodTwoSideways.FinConfig x → (∃ p, x p = true) → ∀ i : Int,
      ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ suffix)) ∧
    ¬ Rule30StripCertificates.EventuallyWord (List.replicate r false ++ suffix) := by
  refine ⟨fun hlo hzero i => ?_, fun hfin hne i => ?_, ?_⟩
  · simpa using no_padding_of_forbidden_suffix hlo hzero i [] suffix K hsafe r
      (by simpa using hrpulse) (by simpa using hrwidth)
  · simpa using no_padding_of_forbidden_suffix_finite hfin hne i [] suffix K hsafe r
      (by simpa using hrpulse) (by simpa using hrwidth)
  · simpa using no_padding_of_forbidden_suffix_seed [] suffix K hsafe r
      (by simpa using hrpulse) (by simpa using hrwidth)

end Ruliology.CellularAutomata.Rule30ForbiddenSuffix
