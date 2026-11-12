module

public import Ruliology.CellularAutomata.Rule30SixTail
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailEndpoints

@[expose] public section

/-! Endpoint refinements reduce the common six-tail padding bound from 77 to 74.
The earlier sharper bounds for shorter tails remain available. No full prize
problem, frequency statement, or computational lower bound is proved. -/
namespace Ruliology.CellularAutomata.Rule30SixTailSharpened
open Rule30Jen Rule30Realization Rule30WordRotation
open Rule30FiveTailReduction Rule30SixTailReduction

theorem no_six_core {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (v : List Bool) (hv : v ∈ sixCores) (r : Nat) (hr : 74 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ v) := by
  simp only [sixCores, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Rule30Certificates.SixTailBackward.C100001.no_padding hlo hzero i r (by omega)
  · exact Rule30Certificates.SixTailBackward.C100011.no_padding hlo hzero i r (by omega)
  · exact Rule30Certificates.SixTailBackward.C100101.no_padding hlo hzero i r (by omega)
  · exact Rule30Certificates.SixTailBackward.C100111.no_padding hlo hzero i r (by omega)
  · exact Rule30Certificates.SixTailBackward.C101001.no_padding hlo hzero i r (by omega)
  · exact Rule30Certificates.SixTailBackward.C101011.no_padding hlo hzero i r (by omega)
  · exact Rule30Certificates.SixTailBackward.C101101.no_padding hlo hzero i r (by omega)
  · exact Rule30Certificates.SixTailBackward.C101111.no_padding hlo hzero i r (by omega)
  · exact Rule30Certificates.SixTailEndpoints.C110001.no_padding hlo hzero i r hr
  · exact Rule30Certificates.SixTailBackward.C110011.no_padding hlo hzero i r (by omega)
  · exact Rule30Certificates.SixTailBackward.C110101.no_padding hlo hzero i r (by omega)
  · exact Rule30Certificates.SixTailBackward.C110111.no_padding hlo hzero i r (by omega)
  · exact Rule30Certificates.SixTailBackward.C111001.no_padding hlo hzero i r (by omega)
  · exact Rule30Certificates.SixTailBackward.C111011.no_padding hlo hzero i r (by omega)
  · exact Rule30Certificates.SixTailEndpoints.C111101.no_padding hlo hzero i r (by omega)
  · exact Rule30Certificates.SixTailBackward.C111111.no_padding hlo hzero i r (by omega)

private theorem replicate_append (a b : Nat) :
    List.replicate a false ++ List.replicate b false = List.replicate (a+b) false := by
  induction a with
  | zero => simp
  | succ a ih => simpa [List.replicate_succ, Nat.succ_add] using congrArg (false :: ·) ih

private theorem replicate_getD (r n : Nat) : (List.replicate r false).getD n false = false := by
  induction r generalizing n with
  | zero => simp
  | succ r ih =>
    cases n with
    | zero => simp [List.replicate_succ]
    | succ n => simpa only [List.replicate_succ, List.getD_cons_succ] using ih n

/-- Every column of every configuration with a leftmost black cell, for every transient. -/
theorem no_six_tail_leftFinite {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (u : List Bool) (hu : u.length ≤ 6) (r : Nat) (hr : 74 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ u) := by
  intro hword
  rcases Rule30SixTailReduction.decomposition u hu with hz | ⟨a,b,v,hv,he⟩
  · obtain ⟨T,hT⟩ := hword
    apply Rule30FiniteConfigs.no_column_eventually_constant hlo hzero i
    refine ⟨T,false,fun t ht => ?_⟩
    rw [hT t ht]
    have hzword : ∀ bit, bit ∈ List.replicate r false ++ u → bit = false := by
      intro bit hb
      rcases List.mem_append.mp hb with hb | hb
      · exact (List.mem_replicate.mp hb).2
      · exact hz bit hb
    rw [List.eq_replicate_of_mem hzword]
    exact replicate_getD _ _
  · rw [he] at hword
    have hw : Rule30FiniteStrips.EventuallyWord x i
        ((List.replicate r false ++ List.replicate a false ++ v) ++ List.replicate b false) := by
      simpa only [List.append_assoc] using hword
    have hrot := eventuallyWord_swap (by simp; omega) hw
    have hlist : List.replicate b false ++ (List.replicate r false ++ List.replicate a false ++ v) =
        List.replicate (b+(r+a)) false ++ v := by
      rw [replicate_append, ← List.append_assoc, replicate_append]
    rw [hlist] at hrot
    rcases List.mem_append.mp hv with hv | hv
    · have hvlen : v.length ≤ 5 := by
        simp only [shortCores, fiveCores, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact Rule30FiveTail.no_five_tail_leftFinite hlo hzero i v hvlen
        (b+(r+a)) (by omega) hrot
    · exact no_six_core hlo hzero i v hv (b+(r+a)) (by omega) hrot

theorem no_six_tail_finite {x : Int → Bool}
    (hfin : Rule30PeriodTwoSideways.FinConfig x) (hne : ∃ p, x p = true)
    (i : Int) (u : List Bool) (hu : u.length ≤ 6) (r : Nat) (hr : 74 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ u) := by
  obtain ⟨lo,hlo,hzero⟩ := Rule30FiniteConfigs.exists_leftmost hfin hne
  exact no_six_tail_leftFinite hlo hzero i u hu r hr

theorem no_six_tail_seed (u : List Bool) (hu : u.length ≤ 6) (r : Nat) (hr : 74 ≤ r) :
    ¬ Rule30StripCertificates.EventuallyWord (List.replicate r false ++ u) := by
  have hzero : ∀ p : Int, p < 0 → seed p = false := by
    intro p hp
    simp [seed, show p ≠ 0 by omega]
  have h := no_six_tail_leftFinite (x := seed) (lo := 0) (by decide) hzero 0 u hu r hr
  simpa only [Rule30FiniteStrips.EventuallyWord,
    Rule30StripCertificates.EventuallyWord, evol_seed] using h

/-! ## Sharpened `P ≥ 75` exclusion of `0^(P-1) 1` and two-sided split six-tail exclusions -/

/-- **Sharpened Unconditional Exclusion of `0^(P-1) 1` for All `P ≥ 75` and Two-Sided Split Six-Tails (`no_oneBlack_ge_75_and_split_six_tail`).** -/
theorem no_oneBlack_ge_75_and_split_six_tail (P a b : Nat) (u : List Bool)
    (hP : 75 ≤ P) (hu : u.length ≤ 6) (hab : 74 ≤ a + b) :
    (∀ {x : Int → Bool} {lo : Int}, x lo = true → (∀ p, p < lo → x p = false) → ∀ i : Int,
      ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate (P - 1) false ++ [true]) ∧
      ¬ Rule30FiniteStrips.EventuallyWord x i ((List.replicate a false ++ u) ++ List.replicate b false)) ∧
    ¬ Rule30StripCertificates.EventuallyWord (List.replicate (P - 1) false ++ [true]) := by
  have hrep : ∀ m n : Nat, List.replicate m false ++ List.replicate n false = List.replicate (m + n) false := by
    intro m n
    induction m with
    | zero => simp
    | succ m ih => simp [List.replicate_succ, Nat.succ_add, ih]
  refine ⟨fun hlo hzero i => ⟨?_, ?_⟩, no_six_tail_seed [true] (by decide) (P - 1) (by omega)⟩
  · exact no_six_tail_leftFinite hlo hzero i [true] (by decide) (P - 1) (by omega)
  · intro hword
    have hrot := Rule30WordRotation.eventuallyWord_swap (by simp; omega) hword
    rw [← List.append_assoc, hrep b a] at hrot
    exact no_six_tail_leftFinite hlo hzero i u hu (b + a) (by omega) hrot

end Ruliology.CellularAutomata.Rule30SixTailSharpened
