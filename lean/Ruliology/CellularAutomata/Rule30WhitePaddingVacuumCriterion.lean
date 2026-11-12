module

public import Ruliology.CellularAutomata.Rule30WhitePulse
public import Ruliology.CellularAutomata.Rule30WhitePadding

@[expose] public section

/-!
# A finite vacuum-avoidance criterion for arbitrary white-padding families

A stable zero-driven reachable set G and the single finite check that a pulse u
cannot send G to the vacuum imply exclusions of 0^r u for all sufficiently large r.
The length and contents of u are unrestricted. This does not establish that such
vacuum-avoidance certificates exist for every pulse.
-/
namespace Ruliology.CellularAutomata.Rule30WhitePaddingVacuumCriterion
open Rule30Jen Rule30Realization Rule30FiniteConfigs Rule30StripCertificates
open Rule30WhitePadding Rule30WhitePulse

/-- A nonzero encoded strip contains a black cell within its width. -/
theorem enc_nonzero_has_black {x : Int → Bool} {K t : Nat} {i : Int} {v : Nat}
    (he : Rule30FiniteStrips.Enc x K t i v) (hv : v ≠ 0) :
    ∃ j, j < K ∧ evol x t (i + (j + 1 : Nat)) = true := by
  obtain ⟨j, hj⟩ := Nat.exists_testBit_of_ne_zero hv
  have hjK : j < K := by
    by_cases h : j < K
    · exact h
    · have hh := Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le he.1 (Nat.pow_le_pow_right (by decide) (show K ≤ j by omega)))
      rw [hj] at hh
      contradiction
  refine ⟨j, hjK, ?_⟩
  have hh := he.2 j hjK
  rw [hj] at hh
  have hpos : i + 1 + (j : Int) = i + ((j + 1 : Nat) : Int) := by omega
  rw [hpos] at hh
  exact hh.symm

/-- **Generic arbitrary-tail criterion.** Once G is the stabilized zero-driven full strip set,
only vacuum avoidance by u needs a finite check. No tail-length bound is imposed. -/
theorem no_padding_of_vacuum_avoidance {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (u : List Bool) (K n G : Nat)
    (hG : zeros K n (fullSet K) = G)
    (hstable : image K false G = G)
    (hsafe : (applyWord K u G).testBit 0 = false)
    (r : Nat) (hrn : n ≤ r)
    (hrpulse : 10*u.length+11 ≤ r)
    (hrwidth : K+9*(u.length+1) ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ u) := by
  intro hword
  obtain ⟨T, hT, hwhite⟩ := white_padding_forces_early_white hlo hzero i u r hrpulse hword
  let w := List.replicate r false ++ u
  have hlen : w.length = r+u.length := by simp [w]
  have hblock : ∀ s, s < w.length → evol x (T+s) i = w.getD s false := by
    intro s hs
    rw [hT _ (by omega), show T+s-T=s by omega,
      Nat.mod_eq_of_lt (by simpa only [hlen] using hs)]
  have hstab : zeros K (n+1) (fullSet K) = zeros K n (fullSet K) := by
    rw [zeros_succ, hG, hstable]
  have hpump : applyWord K w (fullSet K) = applyWord K u G := by
    rw [show w=List.replicate r false++u from rfl, applyWord_append,
      ← zeros, zeros_stable K n (fullSet K) hstab r hrn, hG]
  have he0 := Rule30FiniteStrips.enc_encRow (x := x) K T i
  have hfull : (fullSet K).testBit (Rule30FiniteStrips.encRow x T i K) = true := by
    unfold fullSet
    rw [Nat.testBit_two_pow_sub_one]
    exact decide_eq_true he0.1
  obtain ⟨v, he, hv⟩ := Rule30FiniteStrips.enc_applyWord w T _ (fullSet K) he0 hfull hblock
  rw [hpump] at hv
  have hv0 : v ≠ 0 := by
    intro hz
    subst v
    rw [hsafe] at hv
    contradiction
  rw [hlen] at he
  obtain ⟨j, hjK, hjblack⟩ := enc_nonzero_has_black he hv0
  have hboundary : ∀ s, s < j → evol x (T+(r+u.length)+s) i = false := by
    intro s hs
    have hsr : s < r := by omega
    rw [hT _ (by omega),
      show T+(r+u.length)+s-T=s+1*(r+u.length) by omega,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (l₁ := List.replicate r false) (l₂ := u) (by simpa using hsr),
      List.getElem?_replicate_of_lt hsr]
    rfl
  have hblack := black_reaches_boundary x j i (T+(r+u.length)) hboundary hjblack
  have hwh := hwhite 1 j (by omega)
  simp only [Nat.one_mul] at hwh
  rw [hblack] at hwh
  contradiction

/-- Single-seed version of the same generic finite criterion. -/
theorem no_padding_seed_of_vacuum_avoidance
    (u : List Bool) (K n G : Nat)
    (hG : zeros K n (fullSet K) = G)
    (hstable : image K false G = G)
    (hsafe : (applyWord K u G).testBit 0 = false)
    (r : Nat) (hrn : n ≤ r)
    (hrpulse : 10*u.length+11 ≤ r)
    (hrwidth : K+9*(u.length+1) ≤ r) :
    ¬ Rule30StripCertificates.EventuallyWord (List.replicate r false ++ u) := by
  have hzero : ∀ p : Int, p < 0 → seed p = false := by
    intro p hp
    simp [seed, show p ≠ 0 by omega]
  have h := no_padding_of_vacuum_avoidance (x := seed) (lo := 0) (by decide) hzero
    0 u K n G hG hstable hsafe r hrn hrpulse hrwidth
  simpa only [Rule30FiniteStrips.EventuallyWord, Rule30StripCertificates.EventuallyWord,
    evol_seed] using h

/-! ## Exact all-white characterization of `v = 0` and finite-configuration vacuum-avoidance exclusion -/

/-- **Exact All-White Characterization of the Vacuum Code `v = 0` (`enc_eq_zero_iff_all_white`):**
under `Rule30FiniteStrips.Enc x K t i v`, `v = 0` if and only if every strip cell `j < K` is white. -/
theorem enc_eq_zero_iff_all_white {x : Int → Bool} {K t : Nat} {i : Int} {v : Nat}
    (he : Rule30FiniteStrips.Enc x K t i v) :
    v = 0 ↔ ∀ j, j < K → evol x t (i + (j + 1 : Nat)) = false := by
  constructor
  · rintro rfl j hj
    have hpos : i + ((j + 1 : Nat) : Int) = i + 1 + (j : Int) := by omega
    rw [hpos, ← he.2 j hj, Nat.zero_testBit]
  · intro hall
    by_cases hv0 : v = 0
    · exact hv0
    · obtain ⟨j, hjK, hblack⟩ := enc_nonzero_has_black he hv0
      rw [hall j hjK] at hblack
      cases hblack

/-- **Finite-Configuration Version of the Generic Vacuum-Avoidance Criterion (`no_padding_finite_of_vacuum_avoidance`).** -/
theorem no_padding_finite_of_vacuum_avoidance {x : Int → Bool}
    (hfin : Rule30PeriodTwoSideways.FinConfig x) (hne : ∃ p, x p = true)
    (i : Int) (u : List Bool) (K n G : Nat)
    (hG : zeros K n (fullSet K) = G)
    (hstable : image K false G = G)
    (hsafe : (applyWord K u G).testBit 0 = false)
    (r : Nat) (hrn : n ≤ r)
    (hrpulse : 10 * u.length + 11 ≤ r)
    (hrwidth : K + 9 * (u.length + 1) ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ u) := by
  obtain ⟨lo, hlo, hzero⟩ := exists_leftmost hfin hne
  exact no_padding_of_vacuum_avoidance hlo hzero i u K n G hG hstable hsafe r hrn hrpulse hrwidth

end Ruliology.CellularAutomata.Rule30WhitePaddingVacuumCriterion
