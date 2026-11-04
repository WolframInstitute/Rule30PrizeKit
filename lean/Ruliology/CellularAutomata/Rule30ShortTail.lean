module

public import Ruliology.CellularAutomata.Rule30UniformWhitePadding
public import Ruliology.CellularAutomata.Rule30Certificates.WhitePaddingFamilies
public import Ruliology.CellularAutomata.Rule30WordRotation

@[expose] public section

/-!
# A uniform exclusion for a long white run and a short remaining tail

The certificate families cover the eight black-ended tails of length at most four.
Rotating white prefixes and suffixes gives every binary tail of length at most four.
-/
namespace Ruliology.CellularAutomata.Rule30ShortTail
open Rule30Jen Rule30Realization Rule30StripCertificates Rule30WhitePadding
open Rule30WordRotation
open Rule30Certificates.WhitePaddingFamilies

theorem certificateF (r : Nat) (hr : 21 ≤ r) :
    stripCert (List.replicate r false ++ CheapTails.tailF) 8 2 = true := by
  apply padding_strip CheapTails.tailF 8 21 CheapTails.S1F CheapTails.S2F
  · rw [CheapTails.reachedFullF]; exact CheapTails.firstTailF
  · rw [CheapTails.reachedS1F]; exact CheapTails.secondTailF
  · exact CheapTails.stableFullF
  · exact CheapTails.stableS1F
  · exact CheapTails.stableS2F
  · rw [CheapTails.reachedS2F]; exact CheapTails.returnCheckF
  · exact CheapTails.prefixCheckF
  · rw [CheapTails.reachedS2F]; exact CheapTails.tailCheckF
  · exact hr

theorem certificateG (r : Nat) (hr : 11 ≤ r) :
    stripCert (List.replicate r false ++ CheapTails.tailG) 6 2 = true := by
  apply padding_strip CheapTails.tailG 6 11 CheapTails.S1G CheapTails.S2G
  · rw [CheapTails.reachedFullG]; exact CheapTails.firstTailG
  · rw [CheapTails.reachedS1G]; exact CheapTails.secondTailG
  · exact CheapTails.stableFullG
  · exact CheapTails.stableS1G
  · exact CheapTails.stableS2G
  · rw [CheapTails.reachedS2G]; exact CheapTails.returnCheckG
  · exact CheapTails.prefixCheckG
  · rw [CheapTails.reachedS2G]; exact CheapTails.tailCheckG
  · exact hr

theorem certificateH (r : Nat) (hr : 22 ≤ r) :
    stripCert (List.replicate r false ++ CheapTails.tailH) 8 2 = true := by
  apply padding_strip CheapTails.tailH 8 22 CheapTails.S1H CheapTails.S2H
  · rw [CheapTails.reachedFullH]; exact CheapTails.firstTailH
  · rw [CheapTails.reachedS1H]; exact CheapTails.secondTailH
  · exact CheapTails.stableFullH
  · exact CheapTails.stableS1H
  · exact CheapTails.stableS2H
  · rw [CheapTails.reachedS2H]; exact CheapTails.returnCheckH
  · exact CheapTails.prefixCheckH
  · rw [CheapTails.reachedS2H]; exact CheapTails.tailCheckH
  · exact hr

theorem certificateI (r : Nat) (hr : 13 ≤ r) :
    stripCert (List.replicate r false ++ CheapTails.tailI) 6 2 = true := by
  apply padding_strip CheapTails.tailI 6 13 CheapTails.S1I CheapTails.S2I
  · rw [CheapTails.reachedFullI]; exact CheapTails.firstTailI
  · rw [CheapTails.reachedS1I]; exact CheapTails.secondTailI
  · exact CheapTails.stableFullI
  · exact CheapTails.stableS1I
  · exact CheapTails.stableS2I
  · rw [CheapTails.reachedS2I]; exact CheapTails.returnCheckI
  · exact CheapTails.prefixCheckI
  · rw [CheapTails.reachedS2I]; exact CheapTails.tailCheckI
  · exact hr

private theorem replicate_append (a b : Nat) :
    List.replicate a false ++ List.replicate b false = List.replicate (a + b) false := by
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

/-- The eight core families have a certificate, with the length-three all-black family
supplied as the last independent finite check. -/
theorem short_core_certificate
    (h111 : ∀ r, 49 ≤ r → stripCert (List.replicate r false ++ [true,true,true]) 14 2 = true)
    (u : List Bool) (hu : u ∈ shortCores) (r : Nat) (hr : 49 ≤ r) :
    ∃ K, 1 ≤ K ∧ stripCert (List.replicate r false ++ u) K 2 = true := by
  simp only [shortCores, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨8, by decide, certificateF r (by omega)⟩
  · exact ⟨6, by decide, certificateG r (by omega)⟩
  · exact ⟨9, by decide, Rule30UniformWhitePadding.certificateD r (by omega)⟩
  · exact ⟨14, by decide, h111 r hr⟩
  · exact ⟨8, by decide, certificateH r (by omega)⟩
  · exact ⟨6, by decide, certificateI r (by omega)⟩
  · exact ⟨7, by decide, Rule30UniformWhitePadding.certificateB r (by omega)⟩
  · exact ⟨10, by decide, Rule30UniformWhitePadding.certificateE r (by omega)⟩

/-- Once the last core certificate is supplied, all tails of length at most four are excluded,
in every column of every configuration with a leftmost black cell. -/
theorem no_short_tail_of_111_certificate
    (h111 : ∀ r, 49 ≤ r → stripCert (List.replicate r false ++ [true,true,true]) 14 2 = true)
    {x : Int → Bool} {lo : Int} (hlo : x lo = true)
    (hzero : ∀ p, p < lo → x p = false) (i : Int) (u : List Bool) (hu : u.length ≤ 4)
    (r : Nat) (hr : 49 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ u) := by
  intro hword
  rcases short_decomposition u hu with hz | ⟨a, b, v, hv, he⟩
  · obtain ⟨T, hT⟩ := hword
    apply Rule30FiniteConfigs.no_column_eventually_constant hlo hzero i
    refine ⟨T, false, fun t ht => ?_⟩
    rw [hT t ht]
    have hzword : ∀ b, b ∈ List.replicate r false ++ u → b = false := by
      intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · exact (List.mem_replicate.mp hb).2
      · exact hz b hb
    rw [List.eq_replicate_of_mem hzword]
    exact replicate_getD _ _
  · rw [he] at hword
    have hword' : Rule30FiniteStrips.EventuallyWord x i
        ((List.replicate r false ++ List.replicate a false ++ v) ++ List.replicate b false) := by
      simpa only [List.append_assoc] using hword
    have hrot := eventuallyWord_swap (by simp; omega) hword'
    have hlist : List.replicate b false ++ (List.replicate r false ++ List.replicate a false ++ v) =
        List.replicate (b + (r + a)) false ++ v := by
      rw [replicate_append, ← List.append_assoc, replicate_append]
    rw [hlist] at hrot
    obtain ⟨K, hK, hcert⟩ := short_core_certificate h111 v hv (b + (r + a)) (by omega)
    exact Rule30FiniteStrips.not_eventually_word_strip hlo hzero i _ K 2 hK
      (by simp; omega) hcert hrot

/-- Periodic-column form: a white run of at least 49 cells cannot leave at most four other
phases in the period. The length-three all-black certificate is the only external input. -/
theorem no_short_complement_of_111_certificate
    (h111 : ∀ r, 49 ≤ r → stripCert (List.replicate r false ++ [true,true,true]) 14 2 = true)
    {x : Int → Bool} {lo : Int} (hlo : x lo = true)
    (hzero : ∀ p, p < lo → x p = false) (i : Int) {T P a r : Nat}
    (hP : 0 < P) (hper : ∀ t, T ≤ t → evol x (t + P) i = evol x t i)
    (ha : T ≤ a) (hr : 49 ≤ r) (hrP : r ≤ P) (hcomp : P - r ≤ 4)
    (hwhite : ∀ s, s < r → evol x (a + s) i = false) : False := by
  let u := (List.range (P - r)).map (fun j => evol x (a + r + j) i)
  have hu : u.length ≤ 4 := by simpa [u] using hcomp
  have hlen : (List.replicate r false ++ u).length = P := by simp [u]; omega
  apply no_short_tail_of_111_certificate h111 hlo hzero i u hu r hr
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
      (((List.range (P - r)).map (fun j => evol x (a + r + j) i))[q-r]?).getD false
    rw [List.getElem?_map, List.getElem?_range hqu]
    simp only [Option.map_some, Option.getD_some]
    congr 1
    omega

/-- The final core family, for arbitrary padding r≥49. -/
theorem certificate111 (r : Nat) (hr : 49 ≤ r) :
    stripCert (List.replicate r false ++ [true,true,true]) 14 2 = true := by
  simpa only [Heavy111.tail] using Heavy111.strip_certificate r hr

/-- **Uniform short-tail exclusion.** No column of any configuration with a leftmost black
cell eventually repeats a word consisting of at least 49 white cells and at most four other
cells. The tail may be empty and may itself contain white cells. -/
theorem no_short_tail_leftFinite {x : Int → Bool} {lo : Int} (hlo : x lo = true)
    (hzero : ∀ p, p < lo → x p = false) (i : Int) (u : List Bool) (hu : u.length ≤ 4)
    (r : Nat) (hr : 49 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ u) :=
  no_short_tail_of_111_certificate certificate111 hlo hzero i u hu r hr

/-- Every column of every nonzero finite configuration satisfies the same exclusion. -/
theorem no_short_tail_finite {x : Int → Bool}
    (hfin : Rule30PeriodTwoSideways.FinConfig x) (hne : ∃ p, x p = true)
    (i : Int) (u : List Bool) (hu : u.length ≤ 4) (r : Nat) (hr : 49 ≤ r) :
    ¬ Rule30FiniteStrips.EventuallyWord x i (List.replicate r false ++ u) := by
  obtain ⟨lo, hlo, hzero⟩ := Rule30FiniteConfigs.exists_leftmost hfin hne
  exact no_short_tail_leftFinite hlo hzero i u hu r hr

/-- In particular the center column of the single-seed evolution has no such eventual word. -/
theorem no_short_tail_seed (u : List Bool) (hu : u.length ≤ 4) (r : Nat) (hr : 49 ≤ r) :
    ¬ Rule30StripCertificates.EventuallyWord (List.replicate r false ++ u) := by
  have hzero : ∀ p : Int, p < 0 → seed p = false := by
    intro p hp
    simp [seed, show p ≠ 0 by omega]
  have h := no_short_tail_leftFinite (x := seed) (lo := 0) (by decide) hzero 0 u hu r hr
  simpa only [Rule30FiniteStrips.EventuallyWord, Rule30StripCertificates.EventuallyWord,
    evol_seed] using h

/-- **Periodic-column form.** A period cannot have a white run of length r≥49 and at most four
remaining phases, whatever the transient and in every column of every left-finite nonzero
configuration. The period need not be a least period. -/
theorem no_period_with_short_complement {x : Int → Bool} {lo : Int} (hlo : x lo = true)
    (hzero : ∀ p, p < lo → x p = false) (i : Int) {T P a r : Nat}
    (hP : 0 < P) (hper : ∀ t, T ≤ t → evol x (t + P) i = evol x t i)
    (ha : T ≤ a) (hr : 49 ≤ r) (hrP : r ≤ P) (hcomp : P - r ≤ 4)
    (hwhite : ∀ s, s < r → evol x (a + s) i = false) : False :=
  no_short_complement_of_111_certificate certificate111 hlo hzero i hP hper ha hr hrP hcomp hwhite

/-! ### Finite-Configuration, Single-Seed Column, and Official `center` Periodic Short-Complement Exclusions -/

/-- **Unconditional Short-Core Strip Certificate (`short_core_certificate_unconditional`):**
every core `u ∈ shortCores` has a valid strip certificate `stripCert (List.replicate r false ++ u) K 2 = true`
with `1 ≤ K` for every white-run length `r ≥ 49`. -/
theorem short_core_certificate_unconditional (u : List Bool) (hu : u ∈ shortCores)
    (r : Nat) (hr : 49 ≤ r) :
    ∃ K, 1 ≤ K ∧ stripCert (List.replicate r false ++ u) K 2 = true :=
  short_core_certificate certificate111 u hu r hr

/-- **Periodic Short-Complement Exclusion for Nonzero Finite Configurations
(`no_period_with_short_complement_finite`):** in every column `i : Int` of every nonzero finite
configuration `x`, no eventual period `P > 0` can contain a white run of length `r ≥ 49` leaving at
most four remaining phases (`P - r ≤ 4`). -/
theorem no_period_with_short_complement_finite {x : Int → Bool}
    (hfin : Rule30PeriodTwoSideways.FinConfig x) (hne : ∃ p, x p = true)
    (i : Int) {T P a r : Nat}
    (hP : 0 < P) (hper : ∀ t, T ≤ t → evol x (t + P) i = evol x t i)
    (ha : T ≤ a) (hr : 49 ≤ r) (hrP : r ≤ P) (hcomp : P - r ≤ 4)
    (hwhite : ∀ s, s < r → evol x (a + s) i = false) : False := by
  obtain ⟨lo, hlo, hzero⟩ := Rule30FiniteConfigs.exists_leftmost hfin hne
  exact no_period_with_short_complement hlo hzero i hP hper ha hr hrP hcomp hwhite

/-- **Periodic Short-Complement Exclusion for Every Column `i` of `cell`
(`no_cell_period_with_short_complement`):** in every column `i : Int` of the standard single-seed
evolution `cell`, no eventual period `P > 0` can contain a white run of length `r ≥ 49` leaving at
most four remaining phases (`P - r ≤ 4`). -/
theorem no_cell_period_with_short_complement (i : Int) {T P a r : Nat}
    (hP : 0 < P) (hper : ∀ t, T ≤ t → cell (t + P) i = cell t i)
    (ha : T ≤ a) (hr : 49 ≤ r) (hrP : r ≤ P) (hcomp : P - r ≤ 4)
    (hwhite : ∀ s, s < r → cell (a + s) i = false) : False := by
  have hlo : seed 0 = true := by decide
  have hzero : ∀ p : Int, p < 0 → seed p = false := by
    intro p hp
    simp [seed, show p ≠ 0 by omega]
  refine no_period_with_short_complement hlo hzero i hP (fun t ht => ?_) ha hr hrP hcomp (fun s hs => ?_)
  · rw [evol_seed, evol_seed]; exact hper t ht
  · rw [evol_seed]; exact hwhite s hs

/-- **Periodic Short-Complement Exclusion for the Official `Rule30Prize.center` Column
(`no_center_period_with_short_complement`):** the center column `Rule30Prize.center` is never
eventually `P`-periodic (`0 < P`) with a white run of length `r ≥ 49` (`r ≤ P`) leaving at most
four remaining phases (`P - r ≤ 4`). -/
theorem no_center_period_with_short_complement {T P a r : Nat}
    (hP : 0 < P) (hper : ∀ t, T ≤ t → Rule30Prize.center (t + P) = Rule30Prize.center t)
    (ha : T ≤ a) (hr : 49 ≤ r) (hrP : r ≤ P) (hcomp : P - r ≤ 4)
    (hwhite : ∀ s, s < r → Rule30Prize.center (a + s) = false) : False :=
  no_cell_period_with_short_complement 0 hP hper ha hr hrP hcomp hwhite

/-- **Direct Additive Form for `Rule30Prize.center` (`no_center_period_white_run_add_le_four`):**
for any white-run length `r ≥ 49` and complement length `k ≤ 4` (`0 < r + k`), `Rule30Prize.center`
is never eventually `(r + k)`-periodic with `r` consecutive white cells in a period window. -/
theorem no_center_period_white_run_add_le_four {T a r k : Nat}
    (hr : 49 ≤ r) (hk : k ≤ 4)
    (hper : ∀ t, T ≤ t → Rule30Prize.center (t + (r + k)) = Rule30Prize.center t)
    (ha : T ≤ a) (hwhite : ∀ s, s < r → Rule30Prize.center (a + s) = false) : False :=
  no_center_period_with_short_complement (P := r + k) (by omega) hper ha hr (by omega) (by omega) hwhite

end Ruliology.CellularAutomata.Rule30ShortTail
