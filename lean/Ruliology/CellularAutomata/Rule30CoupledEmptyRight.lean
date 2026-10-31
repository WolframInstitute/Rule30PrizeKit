module

public import Ruliology.CellularAutomata.Rule30Coupled
public import Ruliology.CellularAutomata.Rule30Ether
public import Ruliology.CellularAutomata.Rule30EtherThree
public import Ruliology.CellularAutomata.Rule30EtherThreeTrap
public import Ruliology.CellularAutomata.Rule30EtherThreeReach
public import Ruliology.CellularAutomata.Rule30EtherThreeSkeleton
public import Ruliology.CellularAutomata.Rule30PeriodFourSkeleton
public import Ruliology.CellularAutomata.Rule30PeriodTwoCoupled
public import Ruliology.CellularAutomata.Rule30PeriodTwoSideways
public import Ruliology.CellularAutomata.Rule30ZeroBoundary
public import Ruliology.CellularAutomata.Rule30StripCertificates
public import Ruliology.CellularAutomata.Rule30FiniteMaskedJen
public import Ruliology.CellularAutomata.Rule30FiniteConfigs

/-!
# Coupled Exclusions for the Empty Right Half in Rule 30

This module establishes unconditional non-coupling theorems for the empty right half (R = ∅)
under periodic target center columns.

These results settle unconditionally the empty right half (R = ∅), one case of the coupled
question for period-4 words (0001, 0011, 0111) and period-3 (001); periods 3 and 4 remain
open for general (non-empty) right halves.

## Headline theorems
- `no_empty_right_coupled_0001`: non-coupling for period-4 word 0001 with R = ∅ across all phases.
- `no_empty_right_coupled_0011`: non-coupling for period-4 word 0011 with R = ∅ across all phases.
- `no_empty_right_coupled_0111`: non-coupling for period-4 word 0111 with R = ∅ across all phases.
- `no_empty_right_coupled_001`: non-coupling for period-3 word 001 with R = ∅ across all phases.
- `evol_diff_front`: speed-1 left-permutive difference front propagation.
- `survival_bounded_of_lc_black`: finite survival under bounded left-cone support.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30CoupledEmptyRight

open Rule30Jen Rule30Prize Rule30Realization
open Rule30ZeroBoundary Rule30PeriodTwoCoupled Rule30PeriodTwoSideways
open Rule30Ether
open Rule30PeriodFourSkeleton
open Rule30EtherThree
open Rule30StripCertificates
open Rule30FiniteConfigs Rule30FiniteMaskedJen


theorem exists_first_diff_le (P : Nat → Prop) [DecidablePred P] :
    ∀ n, (¬ ∀ k, 1 ≤ k → k ≤ n → P k) →
      ∃ d, 1 ≤ d ∧ d ≤ n ∧ (∀ k, 1 ≤ k → k < d → P k) ∧ ¬ P d
  | 0, h => absurd (fun _ h1 h2 => by omega) h
  | n + 1, h => by
    by_cases hn : ∀ k, 1 ≤ k → k ≤ n → P k
    · have hnp : ¬ P (n + 1) := fun hp => h fun k hk1 hk2 => by
        rcases Nat.lt_or_eq_of_le hk2 with hlt | rfl
        · exact hn k hk1 (by omega)
        · exact hp
      exact ⟨n + 1, by omega, by omega, fun k hk1 hk2 => hn k hk1 (by omega), hnp⟩
    · obtain ⟨d, hd1, hd2, hag, hne⟩ := exists_first_diff_le P n hn
      exact ⟨d, hd1, by omega, hag, hne⟩

/-- **Universal left-permutive difference front.**
If two configurations `x, x' : Int → Bool` agree strictly to the right of `p₀` and differ at `p₀`,
then at every time `t`, their evolutions `evol x t` and `evol x' t` agree strictly to the right of
`p₀ + t` and differ at `p₀ + t`. -/
theorem evol_diff_front {x x' : Int → Bool} {p₀ : Int}
    (hag : ∀ p, p₀ < p → x p = x' p) (hne : x p₀ ≠ x' p₀) :
    ∀ t : Nat, (∀ p : Int, p₀ + (t : Int) < p → evol x t p = evol x' t p) ∧
      evol x t (p₀ + (t : Int)) ≠ evol x' t (p₀ + (t : Int))
  | 0 => ⟨fun p hp => hag p (by omega), by simpa [evol] using hne⟩
  | t + 1 => by
    obtain ⟨ih_ag, ih_ne⟩ := evol_diff_front hag hne t
    refine ⟨fun p hp => ?_, ?_⟩
    · show rule (evol x t (p - 1)) (evol x t p) (evol x t (p + 1)) =
        rule (evol x' t (p - 1)) (evol x' t p) (evol x' t (p + 1))
      rw [ih_ag (p - 1) (by omega), ih_ag p (by omega), ih_ag (p + 1) (by omega)]
    · show rule (evol x t (p₀ + ((t + 1 : Nat) : Int) - 1))
          (evol x t (p₀ + ((t + 1 : Nat) : Int)))
          (evol x t (p₀ + ((t + 1 : Nat) : Int) + 1)) ≠
        rule (evol x' t (p₀ + ((t + 1 : Nat) : Int) - 1))
          (evol x' t (p₀ + ((t + 1 : Nat) : Int)))
          (evol x' t (p₀ + ((t + 1 : Nat) : Int) + 1))
      have h1 : p₀ + ((t + 1 : Nat) : Int) - 1 = p₀ + (t : Int) := by omega
      rw [h1, ih_ag (p₀ + ((t + 1 : Nat) : Int)) (by omega),
        ih_ag (p₀ + ((t + 1 : Nat) : Int) + 1) (by omega)]
      revert ih_ne
      cases evol x t (p₀ + (t : Int)) <;> cases evol x' t (p₀ + (t : Int)) <;>
        cases evol x' t (p₀ + ((t + 1 : Nat) : Int)) <;>
        cases evol x' t (p₀ + ((t + 1 : Nat) : Int) + 1) <;> decide

/-- **Universal exact death for `Rule30Realization.conf R c`.**
For any right half `R : Int → Bool`, any target column `c : Nat → Bool`, any configuration
`x : Int → Bool` that agrees with `R` on `p ≥ 1`, and any depth `d : Nat`: if `x` agrees with the
sideways-reconstructed left half `lc R c · 0` on `0, …, -(d - 1)` and differs at `-d`, then column
`0` of `evol x` equals `c t` for all `t < d` and differs from `c d` at step `d`. -/
theorem exact_death_conf {x R : Int → Bool} {c : Nat → Bool} {d : Nat}
    (hR : ∀ p : Int, 1 ≤ p → x p = R p)
    (hag : ∀ m : Nat, m < d → x (-(m : Int)) = lc R c m 0)
    (hne : x (-(d : Int)) ≠ lc R c d 0) :
    (∀ t, t < d → evol x t 0 = c t) ∧ evol x d 0 ≠ c d := by
  have hfront := evol_diff_front (x := x) (x' := conf R c) (p₀ := -(d : Int))
    (fun p hp => by
      by_cases h1 : 1 ≤ p
      · rw [hR p h1, (realize R c).1 p h1]
      · have hm : (-p).toNat < d := by omega
        have hxp : x p = lc R c (-p).toNat 0 := by
          have h_p : x p = x (-(((-p).toNat : Nat) : Int)) := by congr 1; omega
          rw [h_p, hag (-p).toNat hm]
        rw [hxp]
        unfold conf
        simp only [h1, ↓reduceIte])
    (by
      unfold conf
      have hpn : ¬ (-(d : Int) ≥ 1) := by omega
      simp only [hpn, ↓reduceIte, show (- -(d : Int)).toNat = d by omega]
      exact hne)
  refine ⟨fun t ht => ?_, ?_⟩
  · rw [(hfront t).1 0 (by omega), (realize R c).2 t]
  · have h := (hfront d).2
    rwa [show -(d : Int) + (d : Int) = 0 by omega, (realize R c).2 d] at h

/-- **Universal survival bound from a single black cell of `lc R c D 0`.**
If `lc R c D 0 = true` for `D ≥ 1`, then every configuration `x` with `x 0 = c 0`, `x p = R p` for
`p ≥ 1`, and `x (-D) = false` has an exact death time `1 ≤ d ≤ D` at which column `0` first
deviates from `c`. -/
theorem survival_bounded_of_lc_black {x R : Int → Bool} {c : Nat → Bool} {D : Nat} (hD : 1 ≤ D)
    (hR : ∀ p : Int, 1 ≤ p → x p = R p) (h0 : x 0 = c 0)
    (hlc : lc R c D 0 = true) (hxD : x (-(D : Int)) = false) :
    ∃ d, 1 ≤ d ∧ d ≤ D ∧ (∀ t, t < d → evol x t 0 = c t) ∧ evol x d 0 ≠ c d := by
  have hnot : ¬ ∀ m, 1 ≤ m → m ≤ D → x (-(m : Int)) = lc R c m 0 := by
    intro hall
    have := hall D hD (Nat.le_refl D)
    rw [hxD, hlc] at this
    exact absurd this (by decide)
  obtain ⟨d, hd1, hdD, hag, hne⟩ :=
    exists_first_diff_le (fun m => x (-(m : Int)) = lc R c m 0) D hnot
  have hag0 : ∀ m, m < d → x (-(m : Int)) = lc R c m 0 := by
    intro m hm
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · simpa [lc] using h0
    · exact hag m hpos hm
  obtain ⟨h1, h2⟩ := exact_death_conf hR hag0 hne
  exact ⟨d, hd1, hdD, h1, h2⟩

/-- Every nonzero left-finite configuration has a leftmost black cell. -/
theorem exists_leftmost_of_left_finite {x : Int → Bool} {W : Nat}
    (hW : ∀ p : Int, p < -(W : Int) → x p = false) (hne : ∃ p, x p = true) :
    ∃ lo, x lo = true ∧ ∀ p, p < lo → x p = false := by
  have key : ∀ n : Nat, (∃ p, x p = true ∧ p ≤ -(W : Int) + n) →
      ∃ lo, x lo = true ∧ ∀ p, p < lo → x p = false := by
    intro n
    induction n with
    | zero =>
      rintro ⟨p, hp, hpW⟩
      refine ⟨p, hp, fun q hq => hW q (by omega)⟩
    | succ n ih =>
      rintro ⟨p, hp, hpW⟩
      by_cases h : ∃ p, x p = true ∧ p ≤ -(W : Int) + n
      · exact ih h
      · refine ⟨p, hp, fun q hq => ?_⟩
        cases hxq : x q
        · rfl
        · exact absurd ⟨q, hxq, by omega⟩ h
  obtain ⟨p, hp⟩ := hne
  have hpW : -(W : Int) ≤ p := by
    rcases Int.lt_or_le p (-(W : Int)) with hlt | hle
    · rw [hW p hlt] at hp; exact absurd hp (by decide)
    · exact hle
  exact key (p + (W : Int)).toNat ⟨p, hp, by omega⟩

/-- **Master Coupled Exclusion Theorem.**
If a driver column `ω : Nat → Bool` has a black cell and is `Q`-periodic from `T₁` (`Q > 0`), and
column `1` of the driven right half `drv ω x` is `Q`-periodic at the white steps of `ω` from `T₁`,
then **no left-finite configuration `s` is coupled with `x` to produce `ω`**. -/
theorem not_coupled_of_right_masked_periodic {ω x : Nat → Bool}
    (hblack : ∃ t₀, ω t₀ = true) {T₁ Q : Nat} (hQ : 0 < Q)
    (hper0 : ∀ t, T₁ ≤ t → ω (t + Q) = ω t)
    (hper1 : ∀ t, T₁ ≤ t → ω t = false → drv ω x (t + Q) 1 = drv ω x t 1)
    (s : Int → Bool) (hs : ∃ W : Nat, ∀ p : Int, p < -(W : Int) → s p = false) :
    ¬ Rule30Coupled.Coupled ω s x := by
  intro hc
  obtain ⟨W, hW⟩ := hs
  let y : Int → Bool := Rule30Coupled.glue s (ω 0) x
  have hy0 : ∀ t, evol y t 0 = ω t := Rule30Coupled.center_glue hc
  have hy1 : ∀ t, evol y t 1 = drv ω x t 1 := by
    intro t
    have e := Rule30Coupled.evol_glue hc t 1
    have hp1 : ¬ (1 : Int) < 0 := by omega
    simp only [hp1, ↓reduceIte, show (1 : Int).toNat = 1 from rfl] at e
    exact e
  have hyW : ∀ p : Int, p < -(W : Int) → y p = false := by
    intro p hp
    show Rule30Coupled.glue s (ω 0) x p = false
    unfold Rule30Coupled.glue
    have hpp : p < 0 := by omega
    simp only [hpp, ↓reduceIte]
    exact hW p hp
  have hne : ∃ p, y p = true := by
    obtain ⟨t₀, ht₀⟩ := hblack
    refine Classical.byContradiction fun hz => ?_
    have hzero : ∀ p, y p = false := fun p => by
      cases hyp : y p
      · rfl
      · exact absurd ⟨p, hyp⟩ hz
    rw [← hy0 t₀, Rule30Coupled.evol_zero hzero] at ht₀
    exact absurd ht₀ (by decide)
  obtain ⟨lo, hlo, hzero⟩ := exists_leftmost_of_left_finite hyW hne
  refine Rule30FiniteMaskedJen.masked_jen hlo hzero 0 hQ (T := T₁) ?_ ?_
  · intro t ht
    rw [hy0 (t + Q), hy0 t]
    exact hper0 t ht
  · intro t ht hw
    rw [hy0 t] at hw
    rw [show (0 : Int) + 1 = 1 from rfl, hy1 (t + Q), hy1 t]
    exact hper1 t ht hw

/-- The realized configuration `conf R ω` is coupled with `fun p => R (p : Int)` to produce `ω`. -/
theorem coupled_conf (R : Int → Bool) (ω : Nat → Bool) :
    Rule30Coupled.Coupled ω (conf R ω) (fun p => R (p : Int)) := by
  have hc := Rule30Coupled.coupled_of_evol (conf R ω)
  have hω : (fun t => evol (conf R ω) t 0) = ω := funext (realize R ω).2
  rw [hω] at hc
  intro t
  rw [hc t]
  congr 1
  exact drv_congr (fun p hp => (realize R ω).1 (p : Int) (by omega)) t 1

/-- **Every sideways-reconstructed left half `lc R ω · 0` is coupled with `R`**, so any theorem
excluding left-finite coupled starts for `(ω, fun p => R (p : Int))` forces `lc R ω · 0` to have
infinite support (`∀ M, ∃ m > M, lc R ω m 0 = true`). -/
theorem lc_infinite_of_no_coupled {R : Int → Bool} {ω : Nat → Bool}
    (hno : ∀ s : Int → Bool, (∃ W : Nat, ∀ p : Int, p < -(W : Int) → s p = false) →
      ¬ Rule30Coupled.Coupled ω s (fun p => R (p : Int)))
    (M : Nat) : ∃ m, M < m ∧ lc R ω m 0 = true := by
  refine Classical.byContradiction fun h => ?_
  have hz : ∀ m, M < m → lc R ω m 0 = false := by
    intro m hm
    cases hlc : lc R ω m 0
    · rfl
    · exact absurd ⟨m, hm, hlc⟩ h
  refine hno (conf R ω) ⟨M, fun p hp => ?_⟩ (coupled_conf R ω)
  unfold conf
  have hpp : ¬ (p ≥ 1) := by omega
  simp only [hpp, ↓reduceIte]
  exact hz (-p).toNat (by omega)

/-- **Master Sideways Support Theorem (`lc_infinite_of_right_masked_periodic`).**
Whenever `ω` has a black cell and is `Q`-periodic from `T₁` (`Q > 0`), and column `1` of
`drv ω (fun p => R (p : Int))` is `Q`-periodic at the white steps of `ω` from `T₁`, the
sideways-reconstructed left half `lc R ω · 0` has infinitely many black cells. -/
theorem lc_infinite_of_right_masked_periodic {R : Int → Bool} {ω : Nat → Bool}
    (hblack : ∃ t₀, ω t₀ = true) {T₁ Q : Nat} (hQ : 0 < Q)
    (hper0 : ∀ t, T₁ ≤ t → ω (t + Q) = ω t)
    (hper1 : ∀ t, T₁ ≤ t → ω t = false →
      drv ω (fun p => R (p : Int)) (t + Q) 1 = drv ω (fun p => R (p : Int)) t 1)
    (M : Nat) : ∃ m, M < m ∧ lc R ω m 0 = true :=
  lc_infinite_of_no_coupled (not_coupled_of_right_masked_periodic hblack hQ hper0 hper1) M

/-! ## 11. Unconditional Solution of the `R = ∅` Coupled Problem (`CQEmpty`) for Period 4 (`0001`, `0011`, `0111`) and Period 3 (`001`) Across All Phases -/

/-- **General Period-4 coupled exclusion from `Rule30Ether.InFamily`.**
If a right half `x : Nat → Bool` driven by `fun t => wordAt w (t + φ)` enters `InFamily` at some
time `t1` for an aligned ether column `(j0, s_off)`, then no left-finite configuration `s` is
coupled with `x` to produce `fun t => wordAt w (t + φ)`. -/
theorem not_coupled_of_inFamily {w : List Bool} {j0 s_off φ t1 : Nat} {x : Nat → Bool}
    (hal : aligned w j0 s_off = true) (hblack : ∃ t₀, wordAt w (t₀ + φ) = true)
    (hF : InFamily (drv (fun t => wordAt w (t + φ)) x) j0 (s_off + φ) t1)
    (s : Int → Bool) (hs : ∃ W : Nat, ∀ p : Int, p < -(W : Int) → s p = false) :
    ¬ Rule30Coupled.Coupled (fun t => wordAt w (t + φ)) s x := by
  obtain ⟨k, hk, hE, hW⟩ := hF
  let ω : Nat → Bool := fun t => wordAt w (t + φ)
  have h0 : ∀ t, t1 ≤ t → drv ω x t 0 = ether j0 (t + (s_off + φ)) := by
    intro t _
    rw [drv_col0]
    show wordAt w (t + φ) = ether j0 (t + (s_off + φ))
    rw [← aligned_spec hal (t + φ)]
    exact ether_congr rfl (by omega)
  have inv := Rule30Ether.trap_invariant (drv_isR30 ω x) j0 (s_off + φ) k t1 hk h0 hE hW
  have key : ∀ t, t1 ≤ t → ω t = false → drv ω x t 1 = ether (j0 + 1) (t + (s_off + φ)) := by
    intro t ht hw
    obtain ⟨hE', hW'⟩ := inv (t - t1)
    rw [show t1 + (t - t1) = t by omega] at hE' hW'
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · have hw2 : ether 2 ((t + (s_off + φ)) % 4) = false := by
        have e : drv ω x t 0 = ether (j0 + 0) (t + (s_off + φ)) := hE' 0 (Nat.le_refl 0)
        rw [drv_col0, hw] at e
        rw [e]; exact ether_congr (by omega) (by omega)
      have hhead := (wall_facts hW').1 hw2
      rw [rowOf_head] at hhead
      have e1 : drv ω x t 1 = ether 3 ((t + (s_off + φ)) % 4) := hhead
      rw [e1]; exact ether_congr (by omega) (by omega)
    · exact hE' 1 hk0
  have hper0 : ∀ t, t1 ≤ t → ω (t + 4) = ω t := by
    intro t _
    show wordAt w (t + 4 + φ) = wordAt w (t + φ)
    unfold wordAt
    congr 1; omega
  refine not_coupled_of_right_masked_periodic hblack (Q := 4) (T₁ := t1) (by decide) hper0 ?_ s hs
  intro t ht hw
  have hw4 : ω (t + 4) = false := by rw [hper0 t ht]; exact hw
  rw [key (t + 4) (by omega) hw4, key t ht hw]
  exact ether_congr rfl (by omega)

/-- **Period-4 `Absorption` implies the full coupled conjecture `Rule30Coupled.CQ` across all phases.** -/
theorem CQ_of_absorption (w : List Bool) (A : List (Nat × Nat))
    (hal : ∀ a ∈ A, aligned w a.1 a.2 = true)
    (hblack : ∀ φ, ∃ t₀, wordAt w (t₀ + φ) = true)
    (hA : Absorption w A) (φ : Nat) :
    Rule30Coupled.CQ (fun t => wordAt w (t + φ)) := by
  rintro ⟨s, x, hs, ⟨WR, hWR⟩, hc⟩
  obtain ⟨⟨j0, s_off⟩, ha, t1, hF⟩ := hA x WR hWR φ
  exact not_coupled_of_inFamily (hal (j0, s_off) ha) (hblack φ) hF s hs hc

/-- Bitmask checker for `InFamily (drv (fun t => wordAt w (t + φ)) (fun _ => false)) j0 (s_off + φ) t1`
using linear-time `Rule30EtherThree.rowN`. -/
def checkEmptyInFamily (w : List Bool) (φ j0 s_off t1 k : Nat) : Bool :=
  let r := rowN (fun t => wordAt w (t + φ)) 0 t1
  decide ((j0 + k) % 7 = 2) &&
  (List.range k).all (fun i => r.testBit i == ether (j0 + (i + 1)) (t1 + (s_off + φ))) &&
  wallStates.contains ((t1 + (s_off + φ)) % 4, seg (fun i => r.testBit (k + i)) 13)

theorem checkEmptyInFamily_sound {w : List Bool} {φ j0 s_off t1 k : Nat}
    (h : checkEmptyInFamily w φ j0 s_off t1 k = true) :
    InFamily (drv (fun t => wordAt w (t + φ)) (fun _ => false)) j0 (s_off + φ) t1 := by
  unfold checkEmptyInFamily at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨⟨hk, hE⟩, hW⟩ := h
  have hx : (fun p : Nat => (0 : Nat).testBit (p - 1)) = (fun _ => false) := by
    funext p; exact Nat.zero_testBit _
  have hbits : ∀ i, (rowN (fun t => wordAt w (t + φ)) 0 t1).testBit i =
      drv (fun t => wordAt w (t + φ)) (fun _ => false) t1 (i + 1) := by
    intro i; rw [rowN_eq_drv, hx]
  refine ⟨k, hk, fun p hp1 hpk => ?_, ?_⟩
  · obtain ⟨i, rfl⟩ : ∃ i, p = i + 1 := ⟨p - 1, by omega⟩
    rw [← hbits i, hE i (by omega)]
  · have hrow : rowOf (drv (fun t => wordAt w (t + φ)) (fun _ => false)) t1 k 13 =
        seg (fun i => (rowN (fun t => wordAt w (t + φ)) 0 t1).testBit (k + i)) 13 := by
      unfold rowOf
      apply seg_congr
      intro i _
      rw [hbits (k + i)]
    rw [hrow]
    exact List.contains_iff_mem.1 hW

theorem wordAt_mod4 (w : List Bool) (t φ : Nat) :
    wordAt w (t + φ) = wordAt w (t + φ % 4) := by
  unfold wordAt
  congr 1; omega

theorem inFamily_mod4 (w : List Bool) (x : Nat → Bool) (j0 s_off φ t1 : Nat)
    (h : InFamily (drv (fun t => wordAt w (t + φ % 4)) x) j0 (s_off + φ % 4) t1) :
    InFamily (drv (fun t => wordAt w (t + φ)) x) j0 (s_off + φ) t1 := by
  have hdrv : (fun t => wordAt w (t + φ)) = (fun t => wordAt w (t + φ % 4)) :=
    funext fun t => wordAt_mod4 w t φ
  obtain ⟨k, hk, hE, hW⟩ := h
  refine ⟨k, hk, fun p hp1 hpk => ?_, ?_⟩
  · rw [hdrv, hE p hp1 hpk]
    exact ether_congr rfl (by omega)
  · rw [hdrv, show (t1 + (s_off + φ)) % 4 = (t1 + (s_off + φ % 4)) % 4 by omega]
    exact hW

/-- **The empty right half driven by `0001^∞` enters `InFamily` across all phases `φ ∈ ℕ` (at `t1 ≤ 14`).** -/
theorem empty_inFamily_0001 (φ : Nat) :
    ∃ t1, InFamily (drv (fun t => wordAt w0001 (t + φ)) (fun _ => false)) 6 (0 + φ) t1 := by
  have hmod : φ % 4 = 0 ∨ φ % 4 = 1 ∨ φ % 4 = 2 ∨ φ % 4 = 3 := by omega
  rcases hmod with h | h | h | h
  · refine ⟨14, inFamily_mod4 w0001 _ 6 0 φ 14 ?_⟩
    rw [h]; exact checkEmptyInFamily_sound (k := 3) (by decide +kernel)
  · refine ⟨13, inFamily_mod4 w0001 _ 6 0 φ 13 ?_⟩
    rw [h]; exact checkEmptyInFamily_sound (k := 3) (by decide +kernel)
  · refine ⟨12, inFamily_mod4 w0001 _ 6 0 φ 12 ?_⟩
    rw [h]; exact checkEmptyInFamily_sound (k := 3) (by decide +kernel)
  · refine ⟨11, inFamily_mod4 w0001 _ 6 0 φ 11 ?_⟩
    rw [h]; exact checkEmptyInFamily_sound (k := 3) (by decide +kernel)

/-- **The empty right half driven by `0011^∞` enters `InFamily` across all phases `φ ∈ ℕ` (at `t1 ≤ 12`).** -/
theorem empty_inFamily_0011 (φ : Nat) :
    ∃ a ∈ A0011, ∃ t1, InFamily (drv (fun t => wordAt w0011 (t + φ)) (fun _ => false)) a.1 (a.2 + φ) t1 := by
  have hmod : φ % 4 = 0 ∨ φ % 4 = 1 ∨ φ % 4 = 2 ∨ φ % 4 = 3 := by omega
  rcases hmod with h | h | h | h
  · refine ⟨(0, 0), by decide, 12, inFamily_mod4 w0011 _ 0 0 φ 12 ?_⟩
    rw [h]; exact checkEmptyInFamily_sound (k := 2) (by decide +kernel)
  · refine ⟨(0, 0), by decide, 11, inFamily_mod4 w0011 _ 0 0 φ 11 ?_⟩
    rw [h]; exact checkEmptyInFamily_sound (k := 2) (by decide +kernel)
  · refine ⟨(0, 0), by decide, 10, inFamily_mod4 w0011 _ 0 0 φ 10 ?_⟩
    rw [h]; exact checkEmptyInFamily_sound (k := 2) (by decide +kernel)
  · refine ⟨(1, 3), by decide, 9, inFamily_mod4 w0011 _ 1 3 φ 9 ?_⟩
    rw [h]; exact checkEmptyInFamily_sound (k := 1) (by decide +kernel)

/-- **The empty right half driven by `0111^∞` enters `InFamily` across all phases `φ ∈ ℕ` (at `t1 ≤ 16`).** -/
theorem empty_inFamily_0111 (φ : Nat) :
    ∃ t1, InFamily (drv (fun t => wordAt w0111 (t + φ)) (fun _ => false)) 2 (2 + φ) t1 := by
  have hmod : φ % 4 = 0 ∨ φ % 4 = 1 ∨ φ % 4 = 2 ∨ φ % 4 = 3 := by omega
  rcases hmod with h | h | h | h
  · refine ⟨9, inFamily_mod4 w0111 _ 2 2 φ 9 ?_⟩
    rw [h]; exact checkEmptyInFamily_sound (k := 0) (by decide +kernel)
  · refine ⟨8, inFamily_mod4 w0111 _ 2 2 φ 8 ?_⟩
    rw [h]; exact checkEmptyInFamily_sound (k := 0) (by decide +kernel)
  · refine ⟨8, inFamily_mod4 w0111 _ 2 2 φ 8 ?_⟩
    rw [h]; exact checkEmptyInFamily_sound (k := 0) (by decide +kernel)
  · refine ⟨16, inFamily_mod4 w0111 _ 2 2 φ 16 ?_⟩
    rw [h]; exact checkEmptyInFamily_sound (k := 0) (by decide +kernel)

theorem wordAt_has_black {w : List Bool} (h3 : wordAt w 3 = true) (φ : Nat) :
    ∃ t₀, wordAt w (t₀ + φ) = true := by
  refine ⟨3 + (4 - φ % 4), ?_⟩
  unfold wordAt at h3 ⊢
  rw [show (3 + (4 - φ % 4) + φ) % 4 = 3 % 4 by omega]
  exact h3

/-- **Unconditional solution of the `R = ∅` coupled conjecture (`CQEmpty`) for `w0001` across all phases.**
No left-finite configuration `s` is coupled with the empty right half to produce `0001^∞` at any phase `φ`. -/
theorem no_empty_right_coupled_0001 (φ : Nat) (s : Int → Bool)
    (hs : ∃ W : Nat, ∀ p : Int, p < -(W : Int) → s p = false) :
    ¬ Rule30Coupled.Coupled (fun t => wordAt w0001 (t + φ)) s (fun _ => false) := by
  obtain ⟨t1, hF⟩ := empty_inFamily_0001 φ
  exact not_coupled_of_inFamily aligned_0001_6 (wordAt_has_black (by decide) φ) hF s hs

/-- **Unconditional solution of the `R = ∅` coupled conjecture (`CQEmpty`) for `w0011` across all phases.**
No left-finite configuration `s` is coupled with the empty right half to produce `0011^∞` at any phase `φ`. -/
theorem no_empty_right_coupled_0011 (φ : Nat) (s : Int → Bool)
    (hs : ∃ W : Nat, ∀ p : Int, p < -(W : Int) → s p = false) :
    ¬ Rule30Coupled.Coupled (fun t => wordAt w0011 (t + φ)) s (fun _ => false) := by
  obtain ⟨⟨j0, s_off⟩, ha, t1, hF⟩ := empty_inFamily_0011 φ
  exact not_coupled_of_inFamily (A0011_ok (j0, s_off) ha) (wordAt_has_black (by decide) φ) hF s hs

/-- **Unconditional solution of the `R = ∅` coupled conjecture (`CQEmpty`) for `w0111` across all phases.**
No left-finite configuration `s` is coupled with the empty right half to produce `0111^∞` at any phase `φ`. -/
theorem no_empty_right_coupled_0111 (φ : Nat) (s : Int → Bool)
    (hs : ∃ W : Nat, ∀ p : Int, p < -(W : Int) → s p = false) :
    ¬ Rule30Coupled.Coupled (fun t => wordAt w0111 (t + φ)) s (fun _ => false) := by
  obtain ⟨t1, hF⟩ := empty_inFamily_0111 φ
  exact not_coupled_of_inFamily aligned_0111_2 (wordAt_has_black (by decide) φ) hF s hs

/-- **Sideways `R = ∅` support theorem for `w0001`:** `lc (fun _ => false) (fun t => wordAt w0001 (t + φ)) · 0`
has infinitely many black cells for every phase `φ ∈ ℕ`. -/
theorem lc_empty_infinite_0001 (φ M : Nat) :
    ∃ m, M < m ∧ lc (fun _ => false) (fun t => wordAt w0001 (t + φ)) m 0 = true :=
  lc_infinite_of_no_coupled (no_empty_right_coupled_0001 φ) M

/-- **Sideways `R = ∅` support theorem for `w0011`:** `lc (fun _ => false) (fun t => wordAt w0011 (t + φ)) · 0`
has infinitely many black cells for every phase `φ ∈ ℕ`. -/
theorem lc_empty_infinite_0011 (φ M : Nat) :
    ∃ m, M < m ∧ lc (fun _ => false) (fun t => wordAt w0011 (t + φ)) m 0 = true :=
  lc_infinite_of_no_coupled (no_empty_right_coupled_0011 φ) M

/-- **Sideways `R = ∅` support theorem for `w0111`:** `lc (fun _ => false) (fun t => wordAt w0111 (t + φ)) · 0`
has infinitely many black cells for every phase `φ ∈ ℕ`. -/
theorem lc_empty_infinite_0111 (φ M : Nat) :
    ∃ m, M < m ∧ lc (fun _ => false) (fun t => wordAt w0111 (t + φ)) m 0 = true :=
  lc_infinite_of_no_coupled (no_empty_right_coupled_0111 φ) M

/-- **General Period-3 `PTrap` invariant for arbitrary phase `φ ∈ ℕ`.** -/
theorem ptrap_invariant_phase (C : PTrap) (hC : C.check = true) {F : Nat → Nat → Bool} (hF : IsR30 F)
    (φ : Nat) (hc : ∀ t, F t 0 = wordAt3 C.w (t + φ))
    (t1 i : Nat) (hi : i < C.n) (hph : (t1 + φ) % 3 = C.lab i % 3)
    (hr : EncF F C.b t1 0 (C.st i)) :
    ∀ n, ∃ j, j < C.n ∧ EncF F C.b (t1 + n) 0 (C.st j) ∧ C.lab j = (C.lab i + n) % C.m := by
  have hli : C.lab i < C.m := (PTrap.step C hC hi false).2.2.2.1
  intro n
  induction n with
  | zero => exact ⟨i, hi, by simpa using hr, by rw [Nat.add_zero, Nat.mod_eq_of_lt hli]⟩
  | succ n ih =>
    obtain ⟨j, hj, hr', hl'⟩ := ih
    have hphase : (t1 + n + φ) % 3 = C.lab j % 3 := by
      rw [hl', show t1 + n + φ = (t1 + φ) + n by omega]
      exact PTrap.phase_lab C hC _ _ hph n
    have hc0 : F (t1 + n) 0 = wordAt3 C.w (C.lab j % 3) := by
      rw [hc (t1 + n)]; unfold wordAt3; rw [Nat.mod_mod, hphase]
    obtain ⟨hnj, hst, hlab, -, -⟩ := PTrap.step C hC hj (F (t1 + n) (0 + 1 + C.b))
    refine ⟨C.nxt j (F (t1 + n) (0 + 1 + C.b)), hnj, ?_, ?_⟩
    · rw [hst, ← hc0, show t1 + (n + 1) = t1 + n + 1 by omega]
      exact encF_step hF hr'
    · rw [hlab, hl', Nat.mod_add_mod]; rfl

/-- **General Period-3 coupled exclusion from `PTrap`.**
If a right half `x` driven by `fun t => wordAt3 C.w (t + φ)` enters a checked trap `C` at time `t1`,
then no left-finite configuration `s` is coupled with `x` to produce `fun t => wordAt3 C.w (t + φ)`. -/
theorem not_coupled_of_ptrap (C : PTrap) (hC : C.check = true) (hb : 0 < C.b)
    (φ : Nat) (hblack : ∃ t₀, wordAt3 C.w (t₀ + φ) = true)
    {x : Nat → Bool} {t1 i : Nat} (hi : i < C.n) (hph : (t1 + φ) % 3 = C.lab i % 3)
    (hr : EncF (drv (fun t => wordAt3 C.w (t + φ)) x) C.b t1 0 (C.st i))
    (s : Int → Bool) (hs : ∃ W : Nat, ∀ p : Int, p < -(W : Int) → s p = false) :
    ¬ Rule30Coupled.Coupled (fun t => wordAt3 C.w (t + φ)) s x := by
  obtain ⟨hm, hm3, -⟩ := PTrap.facts C hC
  let ω : Nat → Bool := fun t => wordAt3 C.w (t + φ)
  have inv := ptrap_invariant_phase C hC (drv_isR30 ω x) φ (drv_col0 ω x) t1 i hi hph hr
  have key : ∀ t, t1 ≤ t → ω t = false →
      drv ω x t 1 = C.u.testBit ((C.lab i + (t - t1)) % C.m) := by
    intro t ht hw
    obtain ⟨j, hj, hr', hl'⟩ := inv (t - t1)
    rw [show t1 + (t - t1) = t by omega] at hr'
    obtain ⟨-, -, -, -, hu⟩ := PTrap.step C hC hj false
    have hphase : (t + φ) % 3 = C.lab j % 3 := by
      rw [hl', show t + φ = (t1 + φ) + (t - t1) by omega]
      exact PTrap.phase_lab C hC _ _ hph _
    have hw' : wordAt3 C.w (C.lab j % 3) = false := by
      rw [← hw]; unfold ω wordAt3; rw [Nat.mod_mod, hphase]
    rw [← hl', ← hu hw', encF_head hr' hb]
  have hper0 : ∀ t, t1 ≤ t → ω (t + C.m) = ω t := by
    intro t _
    unfold ω wordAt3
    congr 1
    obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hm3
    rw [hq, show t + 3 * q + φ = (t + φ) + 3 * q by omega, Nat.add_mul_mod_self_left]
  refine not_coupled_of_right_masked_periodic hblack hm hper0 ?_ s hs
  intro t ht hw
  have hwm : ω (t + C.m) = false := by rw [hper0 t ht]; exact hw
  rw [key (t + C.m) (by omega) hwm, key t ht hw,
    show C.lab i + (t + C.m - t1) = (C.lab i + (t - t1)) + C.m * 1 by omega,
    Nat.add_mul_mod_self_left]

/-- **Period-3 `AbsorptionT C` implies the full coupled conjecture `Rule30Coupled.CQ` across all phases.** -/
theorem CQ_of_absorptionT (C : PTrap) (hC : C.check = true) (hb : 0 < C.b)
    (hblack : ∀ φ, ∃ t₀, wordAt3 C.w (t₀ + φ) = true)
    (hA : AbsorptionT C) (φ : Nat) :
    Rule30Coupled.CQ (fun t => wordAt3 C.w (t + φ)) := by
  rintro ⟨s, x, hs, ⟨WR, hWR⟩, hc⟩
  obtain ⟨t1, i, hi, hph, hr⟩ := hA x WR hWR φ
  exact not_coupled_of_ptrap C hC hb φ (hblack φ) hi hph hr s hs hc

/-- When `c 0 = false`, the empty right half `0` stays `0` at step `1`, shifting `rowN` by one time step. -/
theorem rowN_zero_shift (c : Nat → Bool) (hc0 : c 0 = false) :
    ∀ t, rowN c 0 (t + 1) = rowN (fun s => c (s + 1)) 0 t
  | 0 => by show stepN (c 0) 0 = 0; rw [hc0]; rfl
  | t + 1 => by
    show stepN (c (t + 1)) (rowN c 0 (t + 1)) = stepN (c (t + 1)) (rowN (fun s => c (s + 1)) 0 t)
    rw [rowN_zero_shift c hc0 t]

theorem wordAt3_mod3 (w : List Bool) (t φ : Nat) :
    wordAt3 w (t + φ) = wordAt3 w (t + φ % 3) := by
  unfold wordAt3
  congr 1; omega

/-- **The empty right half driven by `001^∞` enters state `597` of `t001` across all phases `φ ∈ ℕ`**
(at `t1 = 1270` for `φ ≡ 0`, `t1 = 1269` for `φ ≡ 1`, and `t1 = 1268` for `φ ≡ 2` mod `3`). -/
theorem empty_absorbed_t001_all_phases (φ : Nat) :
    ∃ t1 i, i < t001.n ∧ (t1 + φ) % 3 = t001.lab i % 3 ∧
      EncF (drv (fun t => wordAt3 w001 (t + φ)) (fun _ => false)) t001.b t1 0 (t001.st i) := by
  have hx : (fun p : Nat => (0 : Nat).testBit (p - 1)) = (fun _ => false) := by
    funext p; exact Nat.zero_testBit _
  have hb : t001.b = 47 := rfl
  have hlab : t001.lab 597 % 3 = 1 := by decide
  have hdrv : (fun t => wordAt3 w001 (t + φ)) = (fun t => wordAt3 w001 (t + φ % 3)) :=
    funext fun t => wordAt3_mod3 w001 t φ
  have h1 : rowN (fun t => wordAt3 w001 (t + 0)) 0 1270 =
      rowN (fun t => wordAt3 w001 (t + 1)) 0 1269 := by
    have e := rowN_zero_shift (fun t => wordAt3 w001 (t + 0)) rfl 1269
    have hf : (fun s => wordAt3 w001 (s + 1 + 0)) = (fun t => wordAt3 w001 (t + 1)) := rfl
    rw [hf] at e; exact e
  have h2 : rowN (fun t => wordAt3 w001 (t + 1)) 0 1269 =
      rowN (fun t => wordAt3 w001 (t + 2)) 0 1268 := by
    have e := rowN_zero_shift (fun t => wordAt3 w001 (t + 1)) rfl 1268
    have hf : (fun s => wordAt3 w001 (s + 1 + 1)) = (fun t => wordAt3 w001 (t + 2)) := rfl
    rw [hf] at e; exact e
  have hmod : φ % 3 = 0 ∨ φ % 3 = 1 ∨ φ % 3 = 2 := by omega
  rcases hmod with hm | hm | hm
  · refine ⟨1270, 597, by decide, by omega, PTrap.st_lt t001 597, fun k hk => ?_⟩
    rw [hb] at hk
    rw [hdrv, hm, rowN_empty_eq, Nat.testBit_mod_two_pow, decide_eq_true hk, Bool.true_and,
      rowN_eq_drv, hx, show 0 + 1 + k = k + 1 by omega]
  · refine ⟨1269, 597, by decide, by omega, PTrap.st_lt t001 597, fun k hk => ?_⟩
    rw [hb] at hk
    rw [hdrv, hm, rowN_empty_eq, h1, Nat.testBit_mod_two_pow, decide_eq_true hk, Bool.true_and,
      rowN_eq_drv, hx, show 0 + 1 + k = k + 1 by omega]
  · refine ⟨1268, 597, by decide, by omega, PTrap.st_lt t001 597, fun k hk => ?_⟩
    rw [hb] at hk
    rw [hdrv, hm, rowN_empty_eq, h1, h2, Nat.testBit_mod_two_pow, decide_eq_true hk, Bool.true_and,
      rowN_eq_drv, hx, show 0 + 1 + k = k + 1 by omega]

theorem wordAt3_has_black {w : List Bool} (h2 : wordAt3 w 2 = true) (φ : Nat) :
    ∃ t₀, wordAt3 w (t₀ + φ) = true := by
  refine ⟨2 + (3 - φ % 3), ?_⟩
  unfold wordAt3 at h2 ⊢
  rw [show (2 + (3 - φ % 3) + φ) % 3 = 2 % 3 by omega]
  exact h2

/-- **Unconditional solution of the `R = ∅` coupled conjecture (`CQEmpty`) for `w001` across all phases.**
No left-finite configuration `s` is coupled with the empty right half to produce `001^∞` at any phase `φ`. -/
theorem no_empty_right_coupled_001 (φ : Nat) (s : Int → Bool)
    (hs : ∃ W : Nat, ∀ p : Int, p < -(W : Int) → s p = false) :
    ¬ Rule30Coupled.Coupled (fun t => wordAt3 w001 (t + φ)) s (fun _ => false) := by
  obtain ⟨t1, i, hi, hph, hr⟩ := empty_absorbed_t001_all_phases φ
  exact not_coupled_of_ptrap t001 t001_check (by decide) φ (wordAt3_has_black (by decide) φ)
    hi hph hr s hs

/-- **Sideways `R = ∅` support theorem for `w001`:** `lc (fun _ => false) (fun t => wordAt3 w001 (t + φ)) · 0`
has infinitely many black cells for every phase `φ ∈ ℕ`. -/
theorem lc_empty_infinite_001 (φ M : Nat) :
    ∃ m, M < m ∧ lc (fun _ => false) (fun t => wordAt3 w001 (t + φ)) m 0 = true :=
  lc_infinite_of_no_coupled (no_empty_right_coupled_001 φ) M


end Ruliology.CellularAutomata.Rule30CoupledEmptyRight
