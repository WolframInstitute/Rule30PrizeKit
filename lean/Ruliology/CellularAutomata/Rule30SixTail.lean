module
public import Ruliology.CellularAutomata.Rule30SixTailReduction
public import Ruliology.CellularAutomata.Rule30Certificates.SixTailBackward

@[expose] public section
/-! Every Boolean tail of length at most six is excluded after 77 white phases.
The six-bit core proofs use finite backward-vacuum obstructions; shorter cores
use the prior five-tail theorem. This is a partial result, not Problem 1. -/
namespace Ruliology.CellularAutomata.Rule30SixTail
open Rule30Jen Rule30Realization Rule30SixTailReduction

theorem no_six_core {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (v : List Bool) (hv : v ∈ sixCores) (r : Nat) (hr : 77 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ v) := by
  simp only [sixCores, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Rule30Certificates.SixTailBackward.C100001.no_padding hlo hzero i r (by omega)
  · exact Rule30Certificates.SixTailBackward.C100011.no_padding hlo hzero i r (by omega)
  · exact Rule30Certificates.SixTailBackward.C100101.no_padding hlo hzero i r (by omega)
  · exact Rule30Certificates.SixTailBackward.C100111.no_padding hlo hzero i r (by omega)
  · exact Rule30Certificates.SixTailBackward.C101001.no_padding hlo hzero i r (by omega)
  · exact Rule30Certificates.SixTailBackward.C101011.no_padding hlo hzero i r (by omega)
  · exact Rule30Certificates.SixTailBackward.C101101.no_padding hlo hzero i r (by omega)
  · exact Rule30Certificates.SixTailBackward.C101111.no_padding hlo hzero i r (by omega)
  · exact Rule30Certificates.SixTailBackward.C110001.no_padding hlo hzero i r (by omega)
  · exact Rule30Certificates.SixTailBackward.C110011.no_padding hlo hzero i r (by omega)
  · exact Rule30Certificates.SixTailBackward.C110101.no_padding hlo hzero i r (by omega)
  · exact Rule30Certificates.SixTailBackward.C110111.no_padding hlo hzero i r (by omega)
  · exact Rule30Certificates.SixTailBackward.C111001.no_padding hlo hzero i r (by omega)
  · exact Rule30Certificates.SixTailBackward.C111011.no_padding hlo hzero i r (by omega)
  · exact Rule30Certificates.SixTailBackward.C111101.no_padding hlo hzero i r (by omega)
  · exact Rule30Certificates.SixTailBackward.C111111.no_padding hlo hzero i r (by omega)

/-- Every column of every leftmost-black start, with unrestricted transient. -/
theorem no_six_tail_leftFinite {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (u : List Bool) (hu : u.length ≤ 6) (r : Nat) (hr : 77 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ u) :=
  no_six_tail_of_cores hlo hzero i (no_six_core hlo hzero i) u hu r hr

theorem no_six_tail_finite {x : Int → Bool}
    (hfin : Rule30PeriodTwoSideways.FinConfig x) (hne : ∃ p, x p = true)
    (i : Int) (u : List Bool) (hu : u.length ≤ 6) (r : Nat) (hr : 77 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ u) := by
  obtain ⟨lo, hlo, hzero⟩ := Rule30FiniteConfigs.exists_leftmost hfin hne
  exact no_six_tail_leftFinite hlo hzero i u hu r hr

theorem no_six_tail_seed (u : List Bool) (hu : u.length ≤ 6) (r : Nat) (hr : 77 ≤ r) :
    ¬ Rule30StripCertificates.EventuallyWord (List.replicate r false ++ u) := by
  have hzero : ∀ p : Int, p < 0 → seed p = false := by
    intro p hp
    simp [seed, show p ≠ 0 by omega]
  have h := no_six_tail_leftFinite (x := seed) (lo := 0) (by decide) hzero 0 u hu r hr
  simpa only [Rule30FiniteStrips.EventuallyWord,
    Rule30StripCertificates.EventuallyWord, evol_seed] using h
/-! ## Unconditional exclusions of `0^(P-1) 1` for `P ≥ 78` and monochromatic tails of length `≤ 6` -/

/-- **Unconditional Exclusion of `0^(P-1) 1` for Every Period `P ≥ 78` (`no_oneBlack_ge_78_all`):**
for every `P ≥ 78`, the single-black period word `List.replicate (P - 1) false ++ [true]` is excluded
at every column of every left-bounded or non-zero finite configuration and on the single-cell seed. -/
theorem no_oneBlack_ge_78_all (P : Nat) (hP : 78 ≤ P) :
    (∀ {x : Int → Bool} {lo : Int}, x lo = true → (∀ p, p < lo → x p = false) → ∀ i : Int,
      ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate (P - 1) false ++ [true])) ∧
    (∀ {x : Int → Bool}, Rule30PeriodTwoSideways.FinConfig x → (∃ p, x p = true) → ∀ i : Int,
      ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate (P - 1) false ++ [true])) ∧
    ¬ Rule30StripCertificates.EventuallyWord (List.replicate (P - 1) false ++ [true]) :=
  ⟨fun hlo hzero i => no_six_tail_leftFinite hlo hzero i [true] (by decide) (P - 1) (by omega),
   fun hfin hne i => no_six_tail_finite hfin hne i [true] (by decide) (P - 1) (by omega),
   no_six_tail_seed [true] (by decide) (P - 1) (by omega)⟩

/-- **Unconditional Exclusion of Monochromatic Tails `List.replicate k b` of Length `k ≤ 6` After `77` White Cells (`no_replicate_le_six_after_77_white`).** -/
theorem no_replicate_le_six_after_77_white (k r : Nat) (b : Bool) (hk : k ≤ 6) (hr : 77 ≤ r) :
    (∀ {x : Int → Bool} {lo : Int}, x lo = true → (∀ p, p < lo → x p = false) → ∀ i : Int,
      ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ List.replicate k b)) ∧
    (∀ {x : Int → Bool}, Rule30PeriodTwoSideways.FinConfig x → (∃ p, x p = true) → ∀ i : Int,
      ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ List.replicate k b)) ∧
    ¬ Rule30StripCertificates.EventuallyWord (List.replicate r false ++ List.replicate k b) := by
  have hlen : (List.replicate k b).length ≤ 6 := by simp [hk]
  exact ⟨fun hlo hzero i => no_six_tail_leftFinite hlo hzero i (List.replicate k b) hlen r hr,
         fun hfin hne i => no_six_tail_finite hfin hne i (List.replicate k b) hlen r hr,
         no_six_tail_seed (List.replicate k b) hlen r hr⟩

end Ruliology.CellularAutomata.Rule30SixTail
