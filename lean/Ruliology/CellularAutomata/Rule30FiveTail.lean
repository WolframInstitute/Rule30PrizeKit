module

public import Ruliology.CellularAutomata.Rule30FiveTailReduction
public import Ruliology.CellularAutomata.Rule30Certificates.FiveTailTube
public import Ruliology.CellularAutomata.Rule30VacuumExample
public import Ruliology.CellularAutomata.Rule30WhitePadding10101

@[expose] public section

/-!
Exclude sufficiently white-padded repetition of every Boolean tail of
length at most five, in every column of every nonzero left-finite start.
The reduction to black-ended cores combines the shorter-tail theorem,
finite vacuum-avoidance certificates, and the endpoint-conditioned tube.
-/
namespace Ruliology.CellularAutomata.Rule30FiveTail
open Rule30Jen Rule30Realization Rule30FiveTailReduction

theorem no_five_core {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (v : List Bool) (hv : v ∈ fiveCores) (r : Nat) (hr : 69 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ v) := by
  simp only [fiveCores,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Rule30Certificates.FiveTailTube.Vacuum.no_padding10001 hlo hzero i r (by omega)
  · simpa only [Rule30VacuumExample.tailB] using
      Rule30VacuumExample.no_paddingB hlo hzero i r (by omega)
  · exact Rule30WhitePadding10101.no_padding_10101_leftFinite hlo hzero i r hr
  · exact Rule30Certificates.FiveTailTube.Vacuum.no_padding10111 hlo hzero i r (by omega)
  · exact Rule30Certificates.FiveTailTube.Vacuum.no_padding11001 hlo hzero i r (by omega)
  · simpa only [Rule30VacuumExample.tailA] using
      Rule30VacuumExample.no_paddingA hlo hzero i r (by omega)
  · exact Rule30Certificates.FiveTailTube.Vacuum.no_padding11101 hlo hzero i r (by omega)
  · exact Rule30Certificates.FiveTailTube.Vacuum.no_padding11111 hlo hzero i r (by omega)

/-- No column of any configuration with a leftmost black cell eventually repeats
`0^r u` when r≥69 and u has at most five bits. -/
theorem no_five_tail_leftFinite {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (i : Int) (u : List Bool) (hu : u.length ≤ 5) (r : Nat) (hr : 69 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ u) :=
  no_five_tail_of_cores hlo hzero i (no_five_core hlo hzero i) u hu r hr

theorem no_five_tail_finite {x : Int → Bool}
    (hfin : Rule30PeriodTwoSideways.FinConfig x) (hne : ∃ p, x p = true)
    (i : Int) (u : List Bool) (hu : u.length ≤ 5) (r : Nat) (hr : 69 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ u) := by
  obtain ⟨lo,hlo,hzero⟩ := Rule30FiniteConfigs.exists_leftmost hfin hne
  exact no_five_tail_leftFinite hlo hzero i u hu r hr

theorem no_five_tail_seed (u : List Bool) (hu : u.length ≤ 5) (r : Nat) (hr : 69 ≤ r) :
    ¬ Rule30StripCertificates.EventuallyWord (List.replicate r false ++ u) := by
  have hzero : ∀ p : Int, p < 0 → seed p = false := by
    intro p hp
    simp [seed,show p ≠ 0 by omega]
  have h := no_five_tail_leftFinite (x:=seed) (lo:=0) (by decide) hzero 0 u hu r hr
  simpa only [Rule30FiniteStrips.EventuallyWord,Rule30StripCertificates.EventuallyWord,
    evol_seed] using h

/-! ### Periodic Five-Complement Exclusions for Left-Finite, Finite, `cell`, and `Rule30Prize.center` Columns -/

/-- **Periodic Five-Complement Exclusion for Left-Finite Configurations
(`no_period_with_five_complement`):** in every column `i : Int` of any configuration `x` with a
leftmost black cell `lo`, no eventual period `P > 0` can contain a white run of length `r ≥ 69`
(`r ≤ P`) leaving at most five remaining phases (`P - r ≤ 5`). -/
theorem no_period_with_five_complement {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false) (i : Int) {T P a r : Nat}
    (hP : 0 < P) (hper : ∀ t, T ≤ t → evol x (t + P) i = evol x t i)
    (ha : T ≤ a) (hr : 69 ≤ r) (hrP : r ≤ P) (hcomp : P - r ≤ 5)
    (hwhite : ∀ s, s < r → evol x (a + s) i = false) : False := by
  let u := (List.range (P - r)).map (fun j => evol x (a + r + j) i)
  have hu : u.length ≤ 5 := by simpa [u] using hcomp
  have hlen : (List.replicate r false ++ u).length = P := by simp [u]; omega
  apply no_five_tail_leftFinite hlo hzero i u hu r hr
  refine ⟨a, fun t ht => ?_⟩
  rw [hlen]
  let q := (t - a) % P
  have hq : q < P := Nat.mod_lt _ hP
  have hevol : evol x t i = evol x (a + q) i := by
    have hh := Rule30Jen.periodic_mul (f := fun t => evol x t i) (T := T) (P := P)
      hper ((t - a) / P) (a + q) (by omega)
    have heq : a + q + (t - a) / P * P = t := by
      have hd := Nat.div_add_mod (t - a) P
      dsimp [q]
      rw [Nat.mul_comm] at hd
      omega
    rw [heq] at hh
    exact hh
  rw [hevol]
  change evol x (a + q) i = (List.replicate r false ++ u).getD q false
  simp only [List.getD_eq_getElem?_getD]
  by_cases hqr : q < r
  · rw [List.getElem?_append_left (l₁ := List.replicate r false) (l₂ := u) (by simpa using hqr),
      List.getElem?_replicate_of_lt hqr]
    exact hwhite q hqr
  · have hqu : q - r < P - r := by omega
    rw [List.getElem?_append_right (l₁ := List.replicate r false) (l₂ := u) (by simp; omega),
      List.length_replicate]
    change evol x (a + q) i =
      (((List.range (P - r)).map (fun j => evol x (a + r + j) i))[q - r]?).getD false
    rw [List.getElem?_map, List.getElem?_range hqu]
    simp only [Option.map_some, Option.getD_some]
    congr 1
    omega

/-- **Periodic Five-Complement Exclusion for Nonzero Finite Configurations
(`no_period_with_five_complement_finite`):** in every column `i : Int` of every nonzero finite
configuration `x`, no eventual period `P > 0` can contain a white run of length `r ≥ 69` leaving at
most five remaining phases (`P - r ≤ 5`). -/
theorem no_period_with_five_complement_finite {x : Int → Bool}
    (hfin : Rule30PeriodTwoSideways.FinConfig x) (hne : ∃ p, x p = true)
    (i : Int) {T P a r : Nat}
    (hP : 0 < P) (hper : ∀ t, T ≤ t → evol x (t + P) i = evol x t i)
    (ha : T ≤ a) (hr : 69 ≤ r) (hrP : r ≤ P) (hcomp : P - r ≤ 5)
    (hwhite : ∀ s, s < r → evol x (a + s) i = false) : False := by
  obtain ⟨lo, hlo, hzero⟩ := Rule30FiniteConfigs.exists_leftmost hfin hne
  exact no_period_with_five_complement hlo hzero i hP hper ha hr hrP hcomp hwhite

/-- **Periodic Five-Complement Exclusion for Every Column `i` of `cell`
(`no_cell_period_with_five_complement`):** in every column `i : Int` of the standard single-seed
evolution `cell`, no eventual period `P > 0` can contain a white run of length `r ≥ 69` leaving at
most five remaining phases (`P - r ≤ 5`). -/
theorem no_cell_period_with_five_complement (i : Int) {T P a r : Nat}
    (hP : 0 < P) (hper : ∀ t, T ≤ t → cell (t + P) i = cell t i)
    (ha : T ≤ a) (hr : 69 ≤ r) (hrP : r ≤ P) (hcomp : P - r ≤ 5)
    (hwhite : ∀ s, s < r → cell (a + s) i = false) : False := by
  have hlo : seed 0 = true := by decide
  have hzero : ∀ p : Int, p < 0 → seed p = false := by
    intro p hp
    simp [seed, show p ≠ 0 by omega]
  refine no_period_with_five_complement hlo hzero i hP (fun t ht => ?_) ha hr hrP hcomp (fun s hs => ?_)
  · rw [evol_seed, evol_seed]; exact hper t ht
  · rw [evol_seed]; exact hwhite s hs

/-- **Periodic Five-Complement Exclusion for the Official `Rule30Prize.center` Column
(`no_center_period_with_five_complement`):** the center column `Rule30Prize.center` is never
eventually `P`-periodic (`0 < P`) with a white run of length `r ≥ 69` (`r ≤ P`) leaving at most
five remaining phases (`P - r ≤ 5`). -/
theorem no_center_period_with_five_complement {T P a r : Nat}
    (hP : 0 < P) (hper : ∀ t, T ≤ t → Rule30Prize.center (t + P) = Rule30Prize.center t)
    (ha : T ≤ a) (hr : 69 ≤ r) (hrP : r ≤ P) (hcomp : P - r ≤ 5)
    (hwhite : ∀ s, s < r → Rule30Prize.center (a + s) = false) : False :=
  no_cell_period_with_five_complement 0 hP hper ha hr hrP hcomp hwhite

/-- **Direct Additive Form for `Rule30Prize.center` (`no_center_period_white_run_add_le_five`):**
for any white-run length `r ≥ 69` and complement length `k ≤ 5`, `Rule30Prize.center` is never
eventually `(r + k)`-periodic with `r` consecutive white cells in a period window. -/
theorem no_center_period_white_run_add_le_five {T a r k : Nat}
    (hr : 69 ≤ r) (hk : k ≤ 5)
    (hper : ∀ t, T ≤ t → Rule30Prize.center (t + (r + k)) = Rule30Prize.center t)
    (ha : T ≤ a) (hwhite : ∀ s, s < r → Rule30Prize.center (a + s) = false) : False :=
  no_center_period_with_five_complement (P := r + k) (by omega) hper ha hr (by omega) (by omega) hwhite

end Ruliology.CellularAutomata.Rule30FiveTail
