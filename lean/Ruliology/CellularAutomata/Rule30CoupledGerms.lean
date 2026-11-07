module

public import Ruliology.CellularAutomata.Rule30Coupled
public import Ruliology.CellularAutomata.Rule30PeriodTwoSideways

/-!
# Recurring RIGHT germs in coupled Rule 30 histories

For the driven RIGHT half, define `gamma(t)` as cell1 AND(cell2 ORcell3).
Suppose that from time T the driver avoids11 and gamma is zero at every fall.
After a black driver cell at some S >= T, the complete nearest-RIGHT trace from
S+2 onward equals the complemented one-tick-delayed driver. This transport uses
neither periodicity, finite support nor LEFT compatibility.

For an eventually periodic driver with arbitrarily late black cells and eventually
no11, literal coupling and Jen rigidity force gamma to be ONE at arbitrarily late
falls whenever the LEFT has a finite positive edge, or both coupled halves are
finite (including an initially empty LEFT).

The method is a two-tick Boolean identity followed by induction on the driver.
The periodicity and contradiction steps reuse the catalog's LEFT reconstruction,
coupling/gluing and driven-LEFT or finite-configuration Jen theorems.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30CoupledGerms

open Ruliology.CellularAutomata
open Rule30Jen Rule30Realization Rule30DrivenLeft Rule30Ether Rule30Coupled

/-- The same three actual RIGHT cells, in the official driven model. -/
def drivenGamma (omega x : Nat → Bool) (t : Nat) : Bool :=
  drv omega x t 1 && (drv omega x t 2 || drv omega x t 3)

/-- No adjacent ONE pair after a specified actual time. -/
def EventuallyNo11 (omega : Nat → Bool) : Prop :=
  ∃ T, ∀ t, T ≤ t → (omega t && omega (t + 1)) = false

/-- The germ is zero at every sufficiently late black-to-white driver transition. -/
def EventuallyZeroGamma (omega x : Nat → Bool) : Prop :=
  ∃ T, ∀ t, T ≤ t → omega t = true → omega (t + 1) = false →
    drivenGamma omega x t = false

/-- ONE occurs arbitrarily late; preperiod-only ONEs do not suffice. -/
def CofinalBlack (omega : Nat → Bool) : Prop :=
  ∀ N, ∃ t, N ≤ t ∧ omega t = true

/-- Established two-tick germ identity, only transported to the official `drv` model. -/
theorem driven_right_two (omega x : Nat → Bool) (S : Nat)
    (hc : omega S = true) (hn : omega (S + 1) = false) :
    drv omega x (S + 2) 1 = !drivenGamma omega x S := by
  change rule (drv omega x (S + 1) 0) (drv omega x (S + 1) 1)
    (drv omega x (S + 1) 2) = _
  rw [drv_col0, hn]
  simp only [rule, Bool.false_xor]
  change (rule (drv omega x S 0) (drv omega x S 1) (drv omega x S 2) ||
    rule (drv omega x S 1) (drv omega x S 2) (drv omega x S 3)) = _
  rw [drv_col0, hc]
  unfold drivenGamma
  cases drv omega x S 1 <;> cases drv omega x S 2 <;> cases drv omega x S 3 <;> rfl

theorem driven_right_step (omega x : Nat → Bool) (t : Nat) :
    drv omega x (t + 1) 1 = xor (omega t)
      (drv omega x t 1 || drv omega x t 2) := by
  change rule (drv omega x t 0) (drv omega x t 1) (drv omega x t 2) = _
  rw [drv_col0]
  rfl

/-- Complete general transport. Periodicity, finite support and LEFT compatibility
are not used: an all-falls zero germ fixes the late RIGHT root one tick behind
the center. This is an exact equality, not a finite-prefix observation. -/
theorem right_root_gamma_transport (omega x : Nat → Bool) (T S : Nat)
    (hS : T ≤ S) (hblack : omega S = true)
    (hno11 : ∀ t, T ≤ t → (omega t && omega (t + 1)) = false)
    (hgamma : ∀ t, T ≤ t → omega t = true → omega (t + 1) = false →
      drivenGamma omega x t = false) :
    ∀ n, drv omega x (S + 2 + n) 1 = !omega (S + 1 + n) := by
  have hn : omega (S + 1) = false := by
    have he := hno11 S hS
    simpa [hblack] using he
  intro n
  induction n with
  | zero =>
    simp only [Nat.add_zero]
    rw [driven_right_two omega x S hblack hn, hgamma S hS hblack hn, hn]
  | succ n ih =>
    have hindex : S + 1 + (n + 1) = S + 2 + n := by omega
    rw [hindex]
    cases hnow : omega (S + 2 + n) with
    | false =>
      cases hprev : omega (S + 1 + n) with
      | false =>
        have hr : drv omega x (S + 2 + n) 1 = true := by simpa [hprev] using ih
        rw [show S + 2 + (n + 1) = (S + 2 + n) + 1 by omega,
          driven_right_step, hnow, hr]
        rfl
      | true =>
        have hn' : omega ((S + 1 + n) + 1) = false := by
          simpa [show S + 1 + n + 1 = S + 2 + n by omega] using hnow
        have he := driven_right_two omega x (S + 1 + n) hprev hn'
        rw [hgamma (S + 1 + n) (by omega) hprev hn'] at he
        simpa [show S + 1 + n + 2 = S + 2 + (n + 1) by omega] using he
    | true =>
      have hprev : omega (S + 1 + n) = false := by
        have he := hno11 (S + 1 + n) (by omega)
        rw [show S + 1 + n + 1 = S + 2 + n by omega, hnow] at he
        simpa using he
      have hr : drv omega x (S + 2 + n) 1 = true := by simpa [hprev] using ih
      rw [show S + 2 + (n + 1) = (S + 2 + n) + 1 by omega,
        driven_right_step, hnow, hr]
      rfl

/-- Periodicity enters only here, after the full transport equality. -/
theorem right_root_periodic_of_zero_gamma (omega x : Nat → Bool)
    (hper : EventuallyPeriodic omega) (hno11 : EventuallyNo11 omega)
    (hgamma : EventuallyZeroGamma omega x) (hblack : CofinalBlack omega) :
    EventuallyPeriodic (fun t => drv omega x t 1) := by
  obtain ⟨Tp, P, hP, hp⟩ := hper
  obtain ⟨Tn, hn⟩ := hno11
  obtain ⟨Tg, hg⟩ := hgamma
  let T := max Tn Tg
  obtain ⟨S, hS, hb⟩ := hblack T
  have htr := right_root_gamma_transport omega x T S hS hb
    (fun t ht => hn t (by omega)) (fun t ht => hg t (by omega))
  refine ⟨max (S + 2) (Tp + 1), P, hP, ?_⟩
  intro t ht
  have he := htr (t - (S + 2))
  have hep := htr (t + P - (S + 2))
  have hi : S + 2 + (t - (S + 2)) = t := by omega
  have hip : S + 2 + (t + P - (S + 2)) = t + P := by omega
  rw [hi] at he
  rw [hip] at hep
  change drv omega x (t + P) 1 = drv omega x t 1
  rw [hep, he]
  have hi' : S + 1 + (t - (S + 2)) = t - 1 := by omega
  have hip' : S + 1 + (t + P - (S + 2)) = (t - 1) + P := by omega
  rw [hi', hip', hp (t - 1) (by omega)]

/-- Both full driven roots are compatible with the same column. Their periods
combine through the exact coupled center equation. -/
theorem coupled_left_periodic_of_right (omega : Nat → Bool)
    (s : Int → Bool) (x : Nat → Bool) (hc : Coupled omega s x)
    (hper : EventuallyPeriodic omega)
    (hr : EventuallyPeriodic (fun t => drv omega x t 1)) :
    EventuallyPeriodic (fun t => L omega s t (-1)) := by
  obtain ⟨T, P, hP, hp, hq⟩ := common_period hper hr
  refine ⟨T, P, hP, ?_⟩
  intro t ht
  have he := hc (t + P)
  have hf := hc t
  rw [show t + P + 1 = (t + 1) + P by omega, hp (t + 1) (by omega),
    hp t ht, hq t ht] at he
  unfold rule at he hf
  cases L omega s (t + P) (-1) <;> cases L omega s t (-1) <;>
    cases omega t <;> cases drv omega x t 1 <;> simp_all

/-- Exact Coupled-model consumer. No boundary-placeholder compatibility assumptions
are needed: `Coupled` already uses the official center `omega` at depth zero. -/
theorem coupled_left_periodic_of_zero_gamma (omega : Nat → Bool)
    (s : Int → Bool) (x : Nat → Bool) (hc : Coupled omega s x)
    (hper : EventuallyPeriodic omega) (hno11 : EventuallyNo11 omega)
    (hgamma : EventuallyZeroGamma omega x) (hblack : CofinalBlack omega) :
    EventuallyPeriodic (fun t => L omega s t (-1)) :=
  coupled_left_periodic_of_right omega s x hc hper
    (right_root_periodic_of_zero_gamma omega x hper hno11 hgamma hblack)

/-- A finite nonzero LEFT source with its true occupied edge cannot satisfy
the additional all-late-falls zero-gamma hypothesis. RIGHT finiteness is unused. -/
theorem coupled_zero_gamma_impossible_of_left_edge (omega : Nat → Bool)
    (s : Int → Bool) (x : Nat → Bool) (hc : Coupled omega s x)
    {m : Nat} (hm : 0 < m)
    (hs0 : ∀ p : Int, p < -(m : Int) → s p = false)
    (hs1 : s (-(m : Int)) = true)
    (hper : EventuallyPeriodic omega) (hno11 : EventuallyNo11 omega)
    (hgamma : EventuallyZeroGamma omega x) (hblack : CofinalBlack omega) : False :=
  col_neg_one_not_periodic hs0 hs1 hm hper
    (coupled_left_periodic_of_zero_gamma omega s x hc hper hno11 hgamma hblack)

/-- Actual finite-configuration version. The center is definitionally the same
initial center `y 0`; no placeholder value is substituted. -/
theorem finite_config_zero_gamma_impossible (y : Int → Bool)
    (hfin : Rule30PeriodTwoSideways.FinConfig y) (hne : ∃ p, y p = true)
    (hper : EventuallyPeriodic (fun t => evol y t 0))
    (hno11 : EventuallyNo11 (fun t => evol y t 0))
    (hgamma : EventuallyZeroGamma (fun t => evol y t 0) (fun p => y (p : Int)))
    (hblack : CofinalBlack (fun t => evol y t 0)) : False := by
  have hp := coupled_left_periodic_of_zero_gamma
    (fun t => evol y t 0) y (fun p => y (p : Int)) (coupled_of_evol y)
    hper hno11 hgamma hblack
  have hl : EventuallyPeriodic (fun t => evol y t (-1)) := by
    obtain ⟨T, P, hP, hp'⟩ := hp
    refine ⟨T, P, hP, ?_⟩
    intro t ht
    change evol y (t + P) (-1) = evol y t (-1)
    rw [left_eq_L y (t + P) (-1) (by omega), left_eq_L y t (-1) (by omega)]
    exact hp' t ht
  exact Rule30FiniteConfigs.jen_finite hfin hne (-1) 0 (by decide) ⟨hl, hper⟩

/-- Full official CQ-model version: finite halves, both coupled to the SAME
column, cannot have gamma zero at all late falls in the covered domain.
The glued full row uses `omega 0` regardless of `s 0` or `x 0`. -/
theorem coupled_finite_zero_gamma_impossible (omega : Nat → Bool)
    (s : Int → Bool) (x : Nat → Bool) (hc : Coupled omega s x)
    (hleft : ∃ W : Nat, ∀ p : Int, p < -(W : Int) → s p = false)
    (hright : ∃ W : Nat, ∀ p, W < p → x p = false)
    (hper : EventuallyPeriodic omega) (hno11 : EventuallyNo11 omega)
    (hgamma : EventuallyZeroGamma omega x) (hblack : CofinalBlack omega) : False := by
  let y := glue s (omega 0) x
  have hfin : Rule30PeriodTwoSideways.FinConfig y := by
    obtain ⟨Wl, hl⟩ := hleft
    obtain ⟨Wr, hr⟩ := hright
    refine ⟨Wl + Wr, ?_⟩
    intro p hp
    dsimp only [y, glue]
    by_cases hn : p < 0
    · rw [ite_eq_left hn]
      exact hl p (by omega)
    · rw [ite_eq_right hn, ite_eq_right (by omega)]
      exact hr _ (by omega)
  have hne : ∃ p, y p = true := by
    refine Classical.byContradiction fun h => ?_
    have hz : ∀ p, y p = false := by
      intro p
      cases he : y p with
      | false => rfl
      | true => exact False.elim (h ⟨p, he⟩)
    obtain ⟨t, _, ht⟩ := hblack 0
    have he := Rule30Coupled.evol_zero hz t 0
    change evol (glue s (omega 0) x) t 0 = false at he
    rw [center_glue hc] at he
    rw [ht] at he
    contradiction
  have hcp : EventuallyPeriodic (fun t => evol y t 0) := by
    obtain ⟨T, P, hP, hp⟩ := hper
    refine ⟨T, P, hP, ?_⟩
    intro t ht
    change evol (glue s (omega 0) x) (t + P) 0 =
      evol (glue s (omega 0) x) t 0
    rw [center_glue hc, center_glue hc]
    exact hp t ht
  have hlp := coupled_left_periodic_of_zero_gamma omega s x hc hper hno11 hgamma hblack
  have hl : EventuallyPeriodic (fun t => evol y t (-1)) := by
    obtain ⟨T, P, hP, hp⟩ := hlp
    refine ⟨T, P, hP, ?_⟩
    intro t ht
    change evol (glue s (omega 0) x) (t + P) (-1) =
      evol (glue s (omega 0) x) t (-1)
    rw [evol_glue hc, evol_glue hc]
    simpa using hp t ht
  exact Rule30FiniteConfigs.jen_finite hfin hne (-1) 0 (by decide) ⟨hl, hcp⟩

/-- Exact Boolean duality, retaining both fall letters. -/
theorem cofinal_gamma_of_not_eventually_zero (omega x : Nat → Bool)
    (h : ¬ EventuallyZeroGamma omega x) :
    ∀ N, ∃ t, N ≤ t ∧ omega t = true ∧ omega (t + 1) = false ∧
      drivenGamma omega x t = true := by
  intro N
  refine Classical.byContradiction fun hn => ?_
  apply h
  refine ⟨N, ?_⟩
  intro t ht hb hf
  cases he : drivenGamma omega x t with
  | false => rfl
  | true => exact False.elim (hn ⟨t, ht, hb, hf, he⟩)

/-- The recurring-germ statement with only a finite positive LEFT edge.
No finite RIGHT assumption or all-gamma-zero premise remains. -/
theorem coupled_gamma_cofinal_of_left_edge (omega : Nat → Bool)
    (s : Int → Bool) (x : Nat → Bool) (hc : Coupled omega s x)
    {m : Nat} (hm : 0 < m)
    (hs0 : ∀ p : Int, p < -(m : Int) → s p = false)
    (hs1 : s (-(m : Int)) = true)
    (hper : EventuallyPeriodic omega) (hno11 : EventuallyNo11 omega)
    (hblack : CofinalBlack omega) :
    ∀ N, ∃ t, N ≤ t ∧ omega t = true ∧ omega (t + 1) = false ∧
      drivenGamma omega x t = true := by
  apply cofinal_gamma_of_not_eventually_zero
  intro hg
  exact coupled_zero_gamma_impossible_of_left_edge omega s x hc hm hs0 hs1
    hper hno11 hg hblack

/-- Recurring gamma for the full official CQ finite-halves model, including
initially empty LEFT halves. Both boundary placeholders remain irrelevant. -/
theorem coupled_finite_gamma_cofinal (omega : Nat → Bool)
    (s : Int → Bool) (x : Nat → Bool) (hc : Coupled omega s x)
    (hleft : ∃ W : Nat, ∀ p : Int, p < -(W : Int) → s p = false)
    (hright : ∃ W : Nat, ∀ p, W < p → x p = false)
    (hper : EventuallyPeriodic omega) (hno11 : EventuallyNo11 omega)
    (hblack : CofinalBlack omega) :
    ∀ N, ∃ t, N ≤ t ∧ omega t = true ∧ omega (t + 1) = false ∧
      drivenGamma omega x t = true := by
  apply cofinal_gamma_of_not_eventually_zero
  intro hg
  exact coupled_finite_zero_gamma_impossible omega s x hc hleft hright
    hper hno11 hg hblack

open Rule30ZeroBoundary Rule30PeriodTwoCoupled Rule30PeriodTwoSideways

/-! ## 1. The 2-Cell White Corridor of an Active Right Germ under `altCol` -/

/-- **Even-Step Formula for `u R s` (`u_eq_not_or_even`):** for every right half `R` and step `s`,
the white-step column-`1` cell `u R s = drv altCol R (2 * s + 1) 1` equals
`!(drv altCol R (2 * s) 1 || drv altCol R (2 * s) 2)`. -/
theorem u_eq_not_or_even (R : Nat → Bool) (s : Nat) :
    u R s = !(drv altCol R (2 * s) 1 || drv altCol R (2 * s) 2) := by
  unfold u
  rw [driven_right_step altCol R (2 * s), altCol_even s]
  cases (drv altCol R (2 * s) 1 || drv altCol R (2 * s) 2) <;> rfl

/-- **Even-Step Column-1 Recovery (`drv_even_succ_col1_eq_not_drivenGamma`):** at every even step
`2 * s + 2`, column `1` of the `altCol`-driven right half is `!drivenGamma altCol R (2 * s)`. -/
theorem drv_even_succ_col1_eq_not_drivenGamma (R : Nat → Bool) (s : Nat) :
    drv altCol R (2 * s + 2) 1 = !drivenGamma altCol R (2 * s) :=
  driven_right_two altCol R (2 * s) (altCol_even s) (altCol_odd s)

/-- **The 2-Cell White Corridor of an Active Germ (`white_corridor_of_drivenGamma_true`):** whenever
`drivenGamma altCol R (2 * s) = true`, both column `1` and column `2` of `drv altCol R` vanish at
the odd step `2 * s + 1` (`u R s = false` and `drv altCol R (2 * s + 1) 2 = false`). -/
theorem white_corridor_of_drivenGamma_true (R : Nat → Bool) (s : Nat)
    (hg : drivenGamma altCol R (2 * s) = true) :
    u R s = false ∧ drv altCol R (2 * s + 1) 2 = false := by
  have h1 : u R s = !(drv altCol R (2 * s) 1 || drv altCol R (2 * s) 2) := u_eq_not_or_even R s
  have h2 : drv altCol R (2 * s + 1) 2 =
      xor (drv altCol R (2 * s) 1) (drv altCol R (2 * s) 2 || drv altCol R (2 * s) 3) := rfl
  unfold drivenGamma at hg
  rw [h1, h2]
  revert hg
  cases drv altCol R (2 * s) 1 <;> cases drv altCol R (2 * s) 2 <;> cases drv altCol R (2 * s) 3 <;> decide

/-- **Transparent Corridor Transmission (`col2_even_succ_of_drivenGamma_true`):** whenever
`drivenGamma altCol R (2 * s) = true`, the 2-cell white corridor at `(2 * s + 1, 1..2)` transmits
column `3` at time `2 * s + 1` directly into column `2` at time `2 * s + 2`. -/
theorem col2_even_succ_of_drivenGamma_true (R : Nat → Bool) (s : Nat)
    (hg : drivenGamma altCol R (2 * s) = true) :
    drv altCol R (2 * s + 2) 2 = drv altCol R (2 * s + 1) 3 := by
  obtain ⟨hc1, hc2⟩ := white_corridor_of_drivenGamma_true R s hg
  unfold u at hc1
  change rule (drv altCol R (2 * s + 1) 1) (drv altCol R (2 * s + 1) 2) (drv altCol R (2 * s + 1) 3) = _
  rw [hc1, hc2]
  cases drv altCol R (2 * s + 1) 3 <;> rfl

/-! ## 2. Exact Germ Factorization of `u R (s + 1)` and Universal `11`-Freeness -/

/-- **Exact 2-Tick Germ Factorization of `u R (s + 1)` (`u_succ_eq_drivenGamma_and_not_col2`):** for
every right half `R` and step `s`, `u R (s + 1)` equals
`drivenGamma altCol R (2 * s) && !drv altCol R (2 * s + 2) 2`. -/
theorem u_succ_eq_drivenGamma_and_not_col2 (R : Nat → Bool) (s : Nat) :
    u R (s + 1) = (drivenGamma altCol R (2 * s) && !drv altCol R (2 * s + 2) 2) := by
  rw [u_eq_not_or_even R (s + 1), show 2 * (s + 1) = 2 * s + 2 by omega,
    drv_even_succ_col1_eq_not_drivenGamma R s]
  cases drivenGamma altCol R (2 * s) <;> cases drv altCol R (2 * s + 2) 2 <;> rfl

/-- **Exact Corridor Factorization of `u R (s + 1)` (`u_succ_eq_drivenGamma_and_not_col3_odd`):** for
every right half `R` and step `s`, `u R (s + 1)` equals
`drivenGamma altCol R (2 * s) && !drv altCol R (2 * s + 1) 3`. -/
theorem u_succ_eq_drivenGamma_and_not_col3_odd (R : Nat → Bool) (s : Nat) :
    u R (s + 1) = (drivenGamma altCol R (2 * s) && !drv altCol R (2 * s + 1) 3) := by
  rw [u_succ_eq_drivenGamma_and_not_col2 R s]
  by_cases hg : drivenGamma altCol R (2 * s) = true
  · rw [col2_even_succ_of_drivenGamma_true R s hg]
  · cases h : drivenGamma altCol R (2 * s)
    · rfl
    · exact absurd h hg

/-- **Universal `11`-Freeness of `u R` (`u_no11`):** for every right half `R : Nat → Bool` (finite or
infinite) and every `s : Nat`, `(u R s && u R (s + 1)) = false`. -/
theorem u_no11 (R : Nat → Bool) (s : Nat) :
    (u R s && u R (s + 1)) = false := by
  rw [u_succ_eq_drivenGamma_and_not_col2 R s]
  by_cases hg : drivenGamma altCol R (2 * s) = true
  · rw [(white_corridor_of_drivenGamma_true R s hg).1]; rfl
  · cases h : drivenGamma altCol R (2 * s)
    · simp
    · exact absurd h hg

/-- **Universal Golden Rule for `Psi R` (`Psi_free_golden`):** for every right half `R : Nat → Bool`
and every `s : Nat`, if the free bit `zrow (Psi R) (2 * s + 1) 1` is `false`, then the next free bit
`zrow (Psi R) (2 * (s + 1) + 1) 1` is `true`. -/
theorem Psi_free_golden (R : Nat → Bool) (s : Nat)
    (h0 : zrow (Psi R) (2 * s + 1) 1 = false) :
    zrow (Psi R) (2 * (s + 1) + 1) 1 = true := by
  rw [Psi_free] at h0 ⊢
  change (!u R s) = false at h0
  change (!u R (s + 1)) = true
  have hno := u_no11 R s
  revert h0 hno
  cases u R s <;> cases u R (s + 1) <;> decide

/-! ## 3. Zero-Germ Exclusion and Quantitative Germ-Drought Clock Bounds for `Psi R` -/

/-- **Unconditional Infinite Support of `Psi R` under `EventuallyZeroGamma` (`not_finSupp_Psi_of_eventuallyZeroGamma`):**
for any right half `R : Nat → Bool`, if `EventuallyZeroGamma altCol R` holds, then `u R` is
eventually `false` and `Psi R` is not finitely supported (`¬ FinSupp (Psi R)`). -/
theorem not_finSupp_Psi_of_eventuallyZeroGamma (R : Nat → Bool)
    (hgamma : EventuallyZeroGamma altCol R) :
    ¬ FinSupp (Psi R) := by
  apply not_finSupp_Psi_of_eventuallyPeriodic R
  obtain ⟨T, hT⟩ := hgamma
  refine ⟨T + 1, 1, by decide, fun s hs => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  have hg1 : drivenGamma altCol R (2 * k) = false :=
    hT (2 * k) (by omega) (altCol_even k) (altCol_odd k)
  have hg2 : drivenGamma altCol R (2 * (k + 1)) = false :=
    hT (2 * (k + 1)) (by omega) (altCol_even (k + 1)) (altCol_odd (k + 1))
  rw [show k + 1 + 1 = (k + 1) + 1 by omega,
    u_succ_eq_drivenGamma_and_not_col2 R (k + 1),
    u_succ_eq_drivenGamma_and_not_col2 R k, hg1, hg2]
  rfl

/-- **Cofinal Active Right Germs from `FinSupp (Psi R)` (`cofinal_drivenGamma_of_finSupp_Psi`):**
if `FinSupp (Psi R)` holds for a right half `R`, then for every `N : Nat` there exists `s ≥ N` such
that `drivenGamma altCol R (2 * s) = true`. -/
theorem cofinal_drivenGamma_of_finSupp_Psi {R : Nat → Bool} (hfin : FinSupp (Psi R)) (N : Nat) :
    ∃ s, N ≤ s ∧ drivenGamma altCol R (2 * s) = true := by
  refine Classical.byContradiction fun hne => ?_
  apply not_finSupp_Psi_of_eventuallyZeroGamma R ⟨2 * N, fun t ht hb hw => ?_⟩ hfin
  obtain ⟨s, rfl | rfl⟩ : ∃ s, t = 2 * s ∨ t = 2 * s + 1 := ⟨t / 2, by omega⟩
  · cases hg : drivenGamma altCol R (2 * s)
    · rfl
    · exact False.elim (hne ⟨s, by omega, hg⟩)
  · rw [altCol_odd s] at hb; contradiction

/-- **Quantitative Germ-Drought Clock Bound (`germ_drought_clock_bound`):** if `Psi R` has its last
black cell at depth `m ≥ 1`, then on any interval `[s₀, s₀ + ℓ)` where `drivenGamma altCol R (2 * s) = false`
for all `s₀ ≤ s < s₀ + ℓ`, the drought length `ℓ` is bounded by `2 * ℓ ≤ 2 * s₀ + m + 6`. -/
theorem germ_drought_clock_bound {R : Nat → Bool} {m : Nat}
    (hm : 1 ≤ m) (hedge : Psi R m = true) (hfin : ∀ k, m < k → Psi R k = false)
    {s₀ ℓ : Nat} (hdrought : ∀ s, s₀ ≤ s → s < s₀ + ℓ → drivenGamma altCol R (2 * s) = false) :
    2 * ℓ ≤ 2 * s₀ + m + 6 := by
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · omega
  · have hconst : ∀ s, s₀ + 1 ≤ s → s + 1 ≤ (s₀ + 1) + (ℓ - 1) →
        zrow (Psi R) (2 * (s + 1) + 1) 1 = zrow (Psi R) (2 * s + 1) 1 := by
      intro s hs1 hs2
      obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
      rw [Psi_free, Psi_free]
      change (!u R (k + 1 + 1)) = (!u R (k + 1))
      rw [u_succ_eq_drivenGamma_and_not_col2 R (k + 1),
        u_succ_eq_drivenGamma_and_not_col2 R k,
        hdrought (k + 1) (by omega) (by omega),
        hdrought k (by omega) (by omega)]
      rfl
    have hclock := free_bits_clock hm hedge hfin (Psi_inX R)
      (s₀ := s₀ + 1) (ℓ := ℓ - 1) (p := 1) (by decide) hconst
    omega

/-! ## 4. Universal `11`-Freeness and 2-Tick Recurrence of Even Right Germs -/

/-- **Exact 2-Tick Recurrence for Even Right Germs (`drivenGamma_succ_eq`):** for every right half
`R` and step `s`, the next even germ `drivenGamma altCol R (2 * (s + 1))` equals
`!drivenGamma altCol R (2 * s) && (drv altCol R (2 * s + 2) 2 || drv altCol R (2 * s + 2) 3)`. -/
theorem drivenGamma_succ_eq (R : Nat → Bool) (s : Nat) :
    drivenGamma altCol R (2 * (s + 1)) =
      (!drivenGamma altCol R (2 * s) &&
        (drv altCol R (2 * s + 2) 2 || drv altCol R (2 * s + 2) 3)) := by
  have hcol1 := drv_even_succ_col1_eq_not_drivenGamma R s
  change (drv altCol R (2 * (s + 1)) 1 &&
    (drv altCol R (2 * (s + 1)) 2 || drv altCol R (2 * (s + 1)) 3)) = _
  rw [show 2 * (s + 1) = 2 * s + 2 by omega, hcol1]

/-- **Universal `11`-Freeness of Even Right Germs (`drivenGamma_even_no11`):** for every right half
`R : Nat → Bool` and step `s : Nat`, two consecutive even steps cannot both have active germs:
`(drivenGamma altCol R (2 * s) && drivenGamma altCol R (2 * (s + 1))) = false`. -/
theorem drivenGamma_even_no11 (R : Nat → Bool) (s : Nat) :
    (drivenGamma altCol R (2 * s) && drivenGamma altCol R (2 * (s + 1))) = false := by
  rw [drivenGamma_succ_eq R s]
  cases drivenGamma altCol R (2 * s) <;> simp

/-- **Immediate Extinction After an Active Germ (`drivenGamma_succ_false_of_true`):** whenever
`drivenGamma altCol R (2 * s) = true`, the next even germ `drivenGamma altCol R (2 * (s + 1))` is
`false`. -/
theorem drivenGamma_succ_false_of_true (R : Nat → Bool) (s : Nat)
    (hg : drivenGamma altCol R (2 * s) = true) :
    drivenGamma altCol R (2 * (s + 1)) = false := by
  rw [drivenGamma_succ_eq R s, hg]; rfl

/-- **Even-Germ Reduction After an Inactive Germ (`drivenGamma_succ_of_false`):** whenever
`drivenGamma altCol R (2 * s) = false`, column `1` at `2 * s + 2` is `true` and the next even germ
reduces to `drv altCol R (2 * s + 2) 2 || drv altCol R (2 * s + 2) 3`. -/
theorem drivenGamma_succ_of_false (R : Nat → Bool) (s : Nat)
    (hg : drivenGamma altCol R (2 * s) = false) :
    drivenGamma altCol R (2 * (s + 1)) =
      (drv altCol R (2 * s + 2) 2 || drv altCol R (2 * s + 2) 3) := by
  rw [drivenGamma_succ_eq R s, hg]; rfl

/-! ## 5. The Dual Even-Step 2-Cell White Corridor and Column-3 Free-Bit Identity -/

/-- **The Even-Step 2-Cell White Corridor of `u R (s + 1) = true` (`even_white_corridor_of_u_succ_true`):**
whenever `u R (s + 1) = true`, both column `1` and column `2` of `drv altCol R` vanish at the even
step `2 * s + 2` (`drv altCol R (2 * s + 2) 1 = false` and `drv altCol R (2 * s + 2) 2 = false`). -/
theorem even_white_corridor_of_u_succ_true (R : Nat → Bool) (s : Nat)
    (hu : u R (s + 1) = true) :
    drv altCol R (2 * s + 2) 1 = false ∧ drv altCol R (2 * s + 2) 2 = false := by
  have h1 := u_succ_eq_drivenGamma_and_not_col2 R s
  rw [hu] at h1
  have h2 := drv_even_succ_col1_eq_not_drivenGamma R s
  revert h1 h2
  cases drivenGamma altCol R (2 * s) <;> cases drv altCol R (2 * s + 2) 2 <;>
    cases drv altCol R (2 * s + 2) 1 <;> decide

/-- **Even-to-Odd Corridor Transmission (`col2_odd_succ_of_u_succ_true`):** whenever
`u R (s + 1) = true`, the even-step 2-cell white corridor at `(2 * s + 2, 1..2)` transmits column
`3` at time `2 * s + 2` directly into column `2` at time `2 * s + 3`. -/
theorem col2_odd_succ_of_u_succ_true (R : Nat → Bool) (s : Nat)
    (hu : u R (s + 1) = true) :
    drv altCol R (2 * s + 3) 2 = drv altCol R (2 * s + 2) 3 := by
  obtain ⟨hc1, hc2⟩ := even_white_corridor_of_u_succ_true R s hu
  change rule (drv altCol R (2 * s + 2) 1) (drv altCol R (2 * s + 2) 2) (drv altCol R (2 * s + 2) 3) = _
  rw [hc1, hc2]
  cases drv altCol R (2 * s + 2) 3 <;> rfl

/-- **Active-Germ Column-3 Determination (`col3_odd_eq_not_u_of_drivenGamma_true`):** whenever
`drivenGamma altCol R (2 * s) = true`, the odd-step column-`3` cell `drv altCol R (2 * s + 1) 3`
equals `!u R (s + 1)`. -/
theorem col3_odd_eq_not_u_of_drivenGamma_true (R : Nat → Bool) (s : Nat)
    (hg : drivenGamma altCol R (2 * s) = true) :
    drv altCol R (2 * s + 1) 3 = !u R (s + 1) := by
  have h := u_succ_eq_drivenGamma_and_not_col3_odd R s
  rw [hg] at h
  revert h
  cases u R (s + 1) <;> cases drv altCol R (2 * s + 1) 3 <;> decide

/-- **Direct Free-Bit Readout from Column 3 (`Psi_free_succ_eq_col3_odd_of_drivenGamma_true`):**
whenever `drivenGamma altCol R (2 * s) = true`, the next free bit `zrow (Psi R) (2 * (s + 1) + 1) 1`
of `Psi R` is identically equal to `drv altCol R (2 * s + 1) 3`. -/
theorem Psi_free_succ_eq_col3_odd_of_drivenGamma_true (R : Nat → Bool) (s : Nat)
    (hg : drivenGamma altCol R (2 * s) = true) :
    zrow (Psi R) (2 * (s + 1) + 1) 1 = drv altCol R (2 * s + 1) 3 := by
  rw [Psi_free R (s + 1), col3_odd_eq_not_u_of_drivenGamma_true R s hg]
  rfl

/-! ## 6. Cofinal Germ Oscillation and `u R` Pulse-Drought Clock Bounds for `Psi R` -/

/-- **Infinite Support of `Psi R` When `u R` is Eventually False (`not_finSupp_Psi_of_eventuallyFalse_u`):**
if `u R s = false` for all `s ≥ T`, then `u R` is eventually periodic of period `1` and `Psi R` is
not finitely supported (`¬ FinSupp (Psi R)`). -/
theorem not_finSupp_Psi_of_eventuallyFalse_u (R : Nat → Bool)
    (hu : ∃ T, ∀ s, T ≤ s → u R s = false) :
    ¬ FinSupp (Psi R) := by
  obtain ⟨T, hT⟩ := hu
  apply not_finSupp_Psi_of_eventuallyPeriodic R
  refine ⟨T, 1, by decide, fun s hs => ?_⟩
  rw [hT (s + 1) (by omega), hT s hs]

/-- **Cofinal Black Pulses of `u R` from `FinSupp (Psi R)` (`cofinal_u_true_of_finSupp_Psi`):** if
`FinSupp (Psi R)` holds for a right half `R`, then for every `N : Nat` there exists `s ≥ N` with
`u R s = true`. -/
theorem cofinal_u_true_of_finSupp_Psi {R : Nat → Bool} (hfin : FinSupp (Psi R)) (N : Nat) :
    ∃ s, N ≤ s ∧ u R s = true := by
  refine Classical.byContradiction fun hne => ?_
  apply not_finSupp_Psi_of_eventuallyFalse_u R ⟨N, fun s hs => ?_⟩ hfin
  cases hu : u R s
  · rfl
  · exact False.elim (hne ⟨s, hs, hu⟩)

/-- **Cofinal Inactive Right Germs from `FinSupp (Psi R)` (`cofinal_drivenGamma_false_of_finSupp_Psi`):**
because `drivenGamma_even_no11` extinguishes the germ after every active step, `FinSupp (Psi R)`
forces `drivenGamma altCol R (2 * s)` to be both `true` cofinally and `false` cofinally. -/
theorem cofinal_drivenGamma_false_of_finSupp_Psi {R : Nat → Bool} (hfin : FinSupp (Psi R)) (N : Nat) :
    ∃ s, N ≤ s ∧ drivenGamma altCol R (2 * s) = false := by
  obtain ⟨s, hs, hg⟩ := cofinal_drivenGamma_of_finSupp_Psi hfin N
  exact ⟨s + 1, by omega, drivenGamma_succ_false_of_true R s hg⟩

/-- **Quantitative `u R` Pulse-Drought Clock Bound (`u_drought_clock_bound`):** if `Psi R` has its
last black cell at depth `m ≥ 1`, then on any interval `[s₀, s₀ + ℓ)` where `u R s = false` for all
`s₀ ≤ s < s₀ + ℓ`, the drought length `ℓ` is bounded by `2 * ℓ ≤ 2 * s₀ + m + 4`. -/
theorem u_drought_clock_bound {R : Nat → Bool} {m : Nat}
    (hm : 1 ≤ m) (hedge : Psi R m = true) (hfin : ∀ k, m < k → Psi R k = false)
    {s₀ ℓ : Nat} (hdrought : ∀ s, s₀ ≤ s → s < s₀ + ℓ → u R s = false) :
    2 * ℓ ≤ 2 * s₀ + m + 4 := by
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · omega
  · have hconst : ∀ s, s₀ ≤ s → s + 1 ≤ s₀ + (ℓ - 1) →
        zrow (Psi R) (2 * (s + 1) + 1) 1 = zrow (Psi R) (2 * s + 1) 1 := by
      intro s hs1 hs2
      rw [Psi_free, Psi_free]
      change (!u R (s + 1)) = (!u R s)
      rw [hdrought (s + 1) (by omega) (by omega), hdrought s hs1 (by omega)]
    have hclock := free_bits_clock hm hedge hfin (Psi_inX R)
      (s₀ := s₀) (ℓ := ℓ - 1) (p := 1) (by decide) hconst
    omega

/-! ## 7. The Double 2-Cell White Corridor, Active-Germ Lockout, and the `101` Free-Bit Sandwich Law -/

/-- **Two-Sided Pulse Isolation of `u R` (`u_eq_false_of_u_succ_true`):** whenever
`u R (s + 1) = true`, both adjacent white-step column-1 cells `u R s` and `u R (s + 2)` are `false`. -/
theorem u_eq_false_of_u_succ_true (R : Nat → Bool) (s : Nat)
    (hu : u R (s + 1) = true) :
    u R s = false ∧ u R (s + 2) = false := by
  have h1 := u_no11 R s
  have h2 := u_no11 R (s + 1)
  rw [hu] at h1 h2
  revert h1 h2
  cases u R s <;> cases u R (s + 2) <;> decide

/-- **Active Preceding Germ Forced by `u R (s + 1) = true` (`drivenGamma_true_of_u_succ_true`):**
whenever `u R (s + 1) = true`, the preceding even right germ `drivenGamma altCol R (2 * s)` is
forced `true`. -/
theorem drivenGamma_true_of_u_succ_true (R : Nat → Bool) (s : Nat)
    (hu : u R (s + 1) = true) :
    drivenGamma altCol R (2 * s) = true := by
  have h := u_succ_eq_drivenGamma_and_not_col2 R s
  rw [hu] at h
  cases h1 : drivenGamma altCol R (2 * s)
  · rw [h1] at h; contradiction
  · rfl

/-- **Immediate Even-Germ Extinction Forced by `u R (s + 1) = true` (`drivenGamma_succ_false_of_u_succ_true`):**
whenever `u R (s + 1) = true`, the even right germ `drivenGamma altCol R (2 * (s + 1))` at step
`2 * s + 2` is forced `false`. -/
theorem drivenGamma_succ_false_of_u_succ_true (R : Nat → Bool) (s : Nat)
    (hu : u R (s + 1) = true) :
    drivenGamma altCol R (2 * (s + 1)) = false :=
  drivenGamma_succ_false_of_true R s (drivenGamma_true_of_u_succ_true R s hu)

/-- **Odd-Step Column-3 Vanishing Forced by `u R (s + 1) = true` (`col3_odd_false_of_u_succ_true`):**
whenever `u R (s + 1) = true`, the odd-step column-`3` cell `drv altCol R (2 * s + 1) 3` is `false`. -/
theorem col3_odd_false_of_u_succ_true (R : Nat → Bool) (s : Nat)
    (hu : u R (s + 1) = true) :
    drv altCol R (2 * s + 1) 3 = false := by
  have hg := drivenGamma_true_of_u_succ_true R s hu
  rw [col3_odd_eq_not_u_of_drivenGamma_true R s hg, hu]
  rfl

/-- **The Double 2-Cell White Corridor of `u R (s + 1) = true` (`double_corridor_of_u_succ_true`):**
whenever `u R (s + 1) = true`, a 2-cell white corridor opens across columns `1` and `2` at BOTH the
odd step `2 * s + 1` and the even step `2 * s + 2`, AND column `3` at the odd step `2 * s + 1`
vanishes (`drv altCol R (2 * s + 1) 3 = false`). -/
theorem double_corridor_of_u_succ_true (R : Nat → Bool) (s : Nat)
    (hu : u R (s + 1) = true) :
    u R s = false ∧
      drv altCol R (2 * s + 1) 2 = false ∧
      drv altCol R (2 * s + 1) 3 = false ∧
      drv altCol R (2 * s + 2) 1 = false ∧
      drv altCol R (2 * s + 2) 2 = false := by
  have hg := drivenGamma_true_of_u_succ_true R s hu
  obtain ⟨ho1, ho2⟩ := white_corridor_of_drivenGamma_true R s hg
  obtain ⟨he1, he2⟩ := even_white_corridor_of_u_succ_true R s hu
  exact ⟨ho1, ho2, col3_odd_false_of_u_succ_true R s hu, he1, he2⟩

/-- **Four-Tick Germ Recovery After `u R (s + 1) = true` (`drivenGamma_add_two_of_u_succ_true`):**
whenever `u R (s + 1) = true`, the even right germ two periods later at `2 * (s + 2)` reduces to
`drv altCol R (2 * s + 4) 2 || drv altCol R (2 * s + 4) 3`. -/
theorem drivenGamma_add_two_of_u_succ_true (R : Nat → Bool) (s : Nat)
    (hu : u R (s + 1) = true) :
    drivenGamma altCol R (2 * (s + 2)) =
      (drv altCol R (2 * s + 4) 2 || drv altCol R (2 * s + 4) 3) := by
  have hg1 := drivenGamma_succ_false_of_u_succ_true R s hu
  have h := drivenGamma_succ_of_false R (s + 1) hg1
  simpa [show 2 * (s + 1) + 2 = 2 * s + 4 by omega] using h

/-- **Inactive Germ Forces Next `u R` Pulse False (`u_succ_false_of_drivenGamma_false`):**
whenever `drivenGamma altCol R (2 * s) = false`, `u R (s + 1) = false`. -/
theorem u_succ_false_of_drivenGamma_false (R : Nat → Bool) (s : Nat)
    (hg : drivenGamma altCol R (2 * s) = false) :
    u R (s + 1) = false := by
  rw [u_succ_eq_drivenGamma_and_not_col2 R s, hg]
  rfl

/-- **Inactive Germ Forces Next Free Bit of `Psi R` True (`Psi_free_true_of_drivenGamma_false`):**
whenever `drivenGamma altCol R (2 * s) = false`, the free bit `zrow (Psi R) (2 * (s + 1) + 1) 1` is `true`. -/
theorem Psi_free_true_of_drivenGamma_false (R : Nat → Bool) (s : Nat)
    (hg : drivenGamma altCol R (2 * s) = false) :
    zrow (Psi R) (2 * (s + 1) + 1) 1 = true := by
  rw [Psi_free R (s + 1)]
  change (!u R (s + 1)) = true
  rw [u_succ_false_of_drivenGamma_false R s hg]
  rfl

/-- **The `101` Free-Bit Sandwich Law (`Psi_free_sandwich_of_u_succ_true`):** whenever
`u R (s + 1) = true`, the free bit `zrow (Psi R) (2 * (s + 1) + 1) 1` is `false` while both
adjacent free bits `zrow (Psi R) (2 * s + 1) 1` and `zrow (Psi R) (2 * (s + 2) + 1) 1` are `true`. -/
theorem Psi_free_sandwich_of_u_succ_true (R : Nat → Bool) (s : Nat)
    (hu : u R (s + 1) = true) :
    zrow (Psi R) (2 * s + 1) 1 = true ∧
      zrow (Psi R) (2 * (s + 1) + 1) 1 = false ∧
      zrow (Psi R) (2 * (s + 2) + 1) 1 = true := by
  obtain ⟨hu0, hu2⟩ := u_eq_false_of_u_succ_true R s hu
  rw [Psi_free R s, Psi_free R (s + 1), Psi_free R (s + 2)]
  change ((!u R s) = true) ∧ ((!u R (s + 1)) = false) ∧ ((!u R (s + 2)) = true)
  rw [hu0, hu, hu2]
  decide

/-- **Cofinal White Steps of `u R` from `FinSupp (Psi R)` (`cofinal_u_false_of_finSupp_Psi`):**
because `u_no11` forbids consecutive `true` values of `u R`, `FinSupp (Psi R)` forces `u R s = false`
cofinally as well as `u R s = true` cofinally. -/
theorem cofinal_u_false_of_finSupp_Psi {R : Nat → Bool} (hfin : FinSupp (Psi R)) (N : Nat) :
    ∃ s, N ≤ s ∧ u R s = false := by
  obtain ⟨s, hs, hu⟩ := cofinal_u_true_of_finSupp_Psi hfin N
  have hno := u_no11 R s
  rw [hu] at hno
  exact ⟨s + 1, by omega, by simpa using hno⟩

/-- **Cofinal Free-Bit Oscillation of `Psi R` (`cofinal_Psi_free_oscillation_of_finSupp_Psi`):**
if `FinSupp (Psi R)` holds, then for every `N : Nat` there exist `s₁ ≥ N` and `s₂ ≥ N` such that
`zrow (Psi R) (2 * s₁ + 1) 1 = false` and `zrow (Psi R) (2 * s₂ + 1) 1 = true`. -/
theorem cofinal_Psi_free_oscillation_of_finSupp_Psi {R : Nat → Bool} (hfin : FinSupp (Psi R)) (N : Nat) :
    (∃ s₁, N ≤ s₁ ∧ zrow (Psi R) (2 * s₁ + 1) 1 = false) ∧
    (∃ s₂, N ≤ s₂ ∧ zrow (Psi R) (2 * s₂ + 1) 1 = true) := by
  obtain ⟨s₁, hs₁, hu₁⟩ := cofinal_u_true_of_finSupp_Psi hfin N
  obtain ⟨s₂, hs₂, hu₂⟩ := cofinal_u_false_of_finSupp_Psi hfin N
  refine ⟨⟨s₁, hs₁, ?_⟩, ⟨s₂, hs₂, ?_⟩⟩
  · rw [Psi_free R s₁]; change (!u R s₁) = false; rw [hu₁]; rfl
  · rw [Psi_free R s₂]; change (!u R s₂) = true; rw [hu₂]; rfl

/-! ### Direct Bridge from `Psi` to `CQ01`, `Psi` Prefix/Injectivity Laws, and the Coupled Ether Witness -/

open Rule30ZeroBoundary Rule30PeriodTwoCoupled

/-- **Definitional Identity of `Psi R` (`Psi_eq_theta_drv`):** `Psi R` is definitionally identical to
`Theta (fun s => !drv altCol R (2 * s + 1) 1)`. -/
theorem Psi_eq_theta_drv (R : Nat → Bool) :
    Psi R = Theta (fun s => !drv altCol R (2 * s + 1) 1) := rfl

/-- **Characterization of `CQ01` via `Psi` (`CQ01_iff_no_finSupp_Psi`):** the coupled period-2 question
`CQ01` holds if and only if `Psi R` is not finitely supported for every finitely supported right half `R`. -/
theorem CQ01_iff_no_finSupp_Psi :
    CQ01 ↔ ∀ R : Nat → Bool, FinSupp R → ¬ FinSupp (Psi R) :=
  CQ01_iff_no_finSupp_theta_drv

/-- **Period-2 Center Exclusion from Infinite Support of `Psi`
(`no_eventual_period_two_of_no_finSupp_Psi`):** if `¬ FinSupp (Psi R)` holds for every finitely
supported right half `R`, then the center column is not eventually 2-periodic. -/
theorem no_eventual_period_two_of_no_finSupp_Psi
    (hPsi : ∀ R : Nat → Bool, FinSupp R → ¬ FinSupp (Psi R)) :
    ¬ ∃ T0, ∀ t, T0 ≤ t → Rule30Prize.center (t + 2) = Rule30Prize.center t :=
  no_eventual_period_two_of_CQ01 (CQ01_iff_no_finSupp_Psi.mpr hPsi)

/-- **Causal Prefix Dependence of `Psi` (`Psi_eq_of_u_eq_le`):** if `u R1 s = u R2 s` for all `s` with
`2 * s + 2 ≤ k`, then `Psi R1 k = Psi R2 k`. -/
theorem Psi_eq_of_u_eq_le (R1 R2 : Nat → Bool) (k : Nat)
    (h : ∀ s, 2 * s + 2 ≤ k → u R1 s = u R2 s) :
    Psi R1 k = Psi R2 k :=
  Theta_dep (fun s => !u R1 s) (fun s => !u R2 s) k (fun s hs => by rw [h s hs])

/-- **Inverse Causal Prefix Dependence of `u` from `Psi` (`u_eq_of_Psi_eq_le`):** if `Psi R1 k = Psi R2 k`
for all `k ≤ 2 * s + 2`, then `u R1 s = u R2 s`. -/
theorem u_eq_of_Psi_eq_le (R1 R2 : Nat → Bool) (s : Nat)
    (h : ∀ k, k ≤ 2 * s + 2 → Psi R1 k = Psi R2 k) :
    u R1 s = u R2 s := by
  have hnot := Theta_inverse_dep (fun j => !u R1 j) (fun j => !u R2 j) s h
  simpa using congrArg Bool.not hnot

/-- **Injectivity of `Psi` on Coupled Traces `u` (`u_eq_of_Psi_eq`):** if `Psi R1 k = Psi R2 k` for all
`k ≥ 1`, then `u R1 = u R2`. -/
theorem u_eq_of_Psi_eq {R1 R2 : Nat → Bool}
    (h : ∀ k, 1 ≤ k → Psi R1 k = Psi R2 k) :
    u R1 = u R2 := by
  have hnot := Theta_inj (f := fun s => !u R1 s) (g := fun s => !u R2 s) h
  funext s
  have hs := congrFun hnot s
  simpa using congrArg Bool.not hs

/-- **Identification of `Psi (etherRight 1)` with `zrow (etherLeft 1) 0`
(`Psi_etherRight_one_eq_zrow_etherLeft_one`):** on the infinite period-4 ether right half `etherRight 1`,
`Psi (etherRight 1)` coincides with `zrow (etherLeft 1) 0`. -/
theorem Psi_etherRight_one_eq_zrow_etherLeft_one :
    Psi (etherRight 1) = zrow (etherLeft 1) 0 :=
  (zrow_zero_eq_theta_of_coupled ether_coupled_witness.1 ether_coupled_witness.2).symm

/-- **Infinite Support of `Psi (etherRight 1)` (`not_finSupp_Psi_etherRight_one`):** `Psi (etherRight 1)`
is not finitely supported. -/
theorem not_finSupp_Psi_etherRight_one :
    ¬ FinSupp (Psi (etherRight 1)) := by
  rw [Psi_etherRight_one_eq_zrow_etherLeft_one]
  rintro ⟨N, hN⟩
  refine not_finSupp_etherLeft_one ⟨N, fun k hk => ?_⟩
  have hk0 : k ≠ 0 := by omega
  have h := hN k hk
  simpa [zrow, hk0] using h

/-! ### Semiflow of `drv`, Stationary Right-Wall Shielding, Universal Right-Edge Twin Invariance, and Non-Injectivity of `Psi` -/

/-- **One-Step Positive-Column Recurrence for `drv` (`drv_succ_of_pos`):** for any column `p ≥ 1`,
`drv c x (t + 1) p = rule (drv c x t (p - 1)) (drv c x t p) (drv c x t (p + 1))`. -/
theorem drv_succ_of_pos (c x : Nat → Bool) (t : Nat) {p : Nat} (hp : 1 ≤ p) :
    drv c x (t + 1) p = rule (drv c x t (p - 1)) (drv c x t p) (drv c x t (p + 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  rfl

/-- **Semiflow (Time-Additivity) Law for `drv` (`drv_add`):** evolving `s + t` steps under `c` from `x`
is identical to evolving `t` steps under `fun k => c (s + k)` from `drv c x s`. -/
theorem drv_add (c x : Nat → Bool) (s : Nat) :
    ∀ t p, drv c x (s + t) p = drv (fun k => c (s + k)) (drv c x s) t p
  | 0, 0 => by simp [drv_col0]
  | 0, p + 1 => by rw [Rule30Ether.drv_init (fun k => c (s + k)) (drv c x s) (p + 1) (by omega)]; rfl
  | t + 1, 0 => by simp [drv_col0]
  | t + 1, p + 1 => by
    rw [show s + (t + 1) = (s + t) + 1 by omega]
    change rule (drv c x (s + t) p) (drv c x (s + t) (p + 1)) (drv c x (s + t) (p + 2)) =
      rule (drv (fun k => c (s + k)) (drv c x s) t p)
        (drv (fun k => c (s + k)) (drv c x s) t (p + 1))
        (drv (fun k => c (s + k)) (drv c x s) t (p + 2))
    rw [drv_add c x s t p, drv_add c x s t (p + 1), drv_add c x s t (p + 2)]

/-- **Depth-2 Even-Step Identity of `Psi` (`zrow_Psi_even_two_eq_u`):** at every even step `2 * s`,
depth `2` of the reconstructed left half `zrow (Psi R) (2 * s) 2` equals `u R s`. -/
theorem zrow_Psi_even_two_eq_u (R : Nat → Bool) (s : Nat) :
    zrow (Psi R) (2 * s) 2 = u R s := by
  have hinv := zrow_inv (Psi R) (2 * s) 0
  have hev : zrow (Psi R) (2 * s) 1 = true := Theta_inX (fun j => !u R j) s
  rw [zrow_wall, Bool.or_false, hev, Psi_free] at hinv
  change zrow (Psi R) (2 * s) 2 = xor (!u R s) true at hinv
  rw [hinv]
  cases u R s <;> rfl

/-- **Initial Depth-2 Formula for `Psi` (`Psi_two_eq_u_zero`):** depth `2` of `Psi R` equals
`u R 0 = !(R 1 || R 2)`. -/
theorem Psi_two_eq_u_zero (R : Nat → Bool) :
    Psi R 2 = !(R 1 || R 2) := by
  have h := zrow_Psi_even_two_eq_u R 0
  rw [zrow_zero_of_pos (Psi R) (by omega : 1 ≤ 2)] at h
  rw [h, u_eq_not_or_even R 0, Rule30Ether.drv_init altCol R 1 (by omega), Rule30Ether.drv_init altCol R 2 (by omega)]

/-- **One-Step Stationary `(false, true)` Right-Wall Shielding (`drv_one_eq_of_zero_one_wall`):**
if `R1` and `R2` agree on columns `≤ M` (`2 ≤ M`) and have `(R1 (M - 1), R1 M) = (false, true)`,
then for any driver `c`, `drv c R1 1` and `drv c R2 1` agree on all columns `≤ M` and both have
`true` at column `M`. -/
theorem drv_one_eq_of_zero_one_wall (c : Nat → Bool) {M : Nat} (hM : 2 ≤ M)
    {R1 R2 : Nat → Bool} (hag : ∀ p, p ≤ M → R1 p = R2 p)
    (hm1 : R1 (M - 1) = false) (hm : R1 M = true) :
    (∀ p, p ≤ M → drv c R1 1 p = drv c R2 1 p) ∧
      drv c R1 1 M = true ∧ drv c R2 1 M = true := by
  have hm1' : R2 (M - 1) = false := by rw [← hag (M - 1) (by omega), hm1]
  have hm' : R2 M = true := by rw [← hag M (by omega), hm]
  have hcolM1 : drv c R1 1 M = true := by
    rw [drv_succ_of_pos c R1 0 (by omega), Rule30Ether.drv_init c R1 (M - 1) (by omega),
      Rule30Ether.drv_init c R1 M (by omega), hm1, hm]
    rfl
  have hcolM2 : drv c R2 1 M = true := by
    rw [drv_succ_of_pos c R2 0 (by omega), Rule30Ether.drv_init c R2 (M - 1) (by omega),
      Rule30Ether.drv_init c R2 M (by omega), hm1', hm']
    rfl
  refine ⟨fun p hp => ?_, hcolM1, hcolM2⟩
  rcases Nat.eq_or_lt_of_le hp with rfl | hlt
  · rw [hcolM1, hcolM2]
  · rcases p with _ | p
    · simp [drv_col0]
    · rw [drv_succ_of_pos c R1 0 (by omega), drv_succ_of_pos c R2 0 (by omega)]
      have h0 : drv c R1 0 p = drv c R2 0 p := by
        rcases p with _ | q
        · simp [drv_col0]
        · rw [Rule30Ether.drv_init c R1 (q + 1) (by omega), Rule30Ether.drv_init c R2 (q + 1) (by omega),
            hag (q + 1) (by omega)]
      rw [show p + 1 - 1 = p by omega, h0,
        Rule30Ether.drv_init c R1 (p + 1) (by omega), Rule30Ether.drv_init c R2 (p + 1) (by omega),
        Rule30Ether.drv_init c R1 (p + 2) (by omega), Rule30Ether.drv_init c R2 (p + 2) (by omega),
        hag (p + 1) (by omega), hag (p + 2) (by omega)]

/-- **Two-Step Stationary `(false, true)` Right-Wall Shielding (`drv_two_eq_of_zero_one_wall`):**
under the hypotheses of `drv_one_eq_of_zero_one_wall`, `drv c R1 2` and `drv c R2 2` still agree
on all columns `≤ M` regardless of how `R1` and `R2` behave above column `M`. -/
theorem drv_two_eq_of_zero_one_wall (c : Nat → Bool) {M : Nat} (hM : 2 ≤ M)
    {R1 R2 : Nat → Bool} (hag : ∀ p, p ≤ M → R1 p = R2 p)
    (hm1 : R1 (M - 1) = false) (hm : R1 M = true) :
    ∀ p, p ≤ M → drv c R1 2 p = drv c R2 2 p := by
  obtain ⟨hag1, hM1, hM2⟩ := drv_one_eq_of_zero_one_wall c hM hag hm1 hm
  intro p hp
  rcases Nat.eq_or_lt_of_le hp with rfl | hlt
  · rw [drv_succ_of_pos c R1 1 (by omega), drv_succ_of_pos c R2 1 (by omega),
      hag1 (p - 1) (by omega), hM1, hM2]
    unfold rule
    simp
  · rcases p with _ | p
    · simp [drv_col0]
    · rw [drv_succ_of_pos c R1 1 (by omega), drv_succ_of_pos c R2 1 (by omega),
        show p + 1 - 1 = p by omega,
        hag1 p (by omega), hag1 (p + 1) (by omega), hag1 (p + 2) (by omega)]

/-- **The Right-Edge Twin Relation (`RightEdgeTwin`):** two right halves `R1` and `R2` form a
right-edge twin pair at column `M ≥ 2` if they agree up to `M`, have `(false, true)` at
`(M - 1, M)`, and beyond `M` have `(false, false, …)` vs `(true, false, …)`. -/
def RightEdgeTwin (M : Nat) (R1 R2 : Nat → Bool) : Prop :=
  2 ≤ M ∧
  (∀ p, p ≤ M → R1 p = R2 p) ∧
  R1 (M - 1) = false ∧
  R1 M = true ∧
  R1 (M + 1) = false ∧
  R2 (M + 1) = true ∧
  (∀ p, M + 2 ≤ p → R1 p = false ∧ R2 p = false)

/-- **Two-Step Outward Shift of `RightEdgeTwin` (`rightEdgeTwin_step_two`):** for any driver `c`,
if `RightEdgeTwin M R1 R2` holds at time `0`, then `RightEdgeTwin (M + 2) (drv c R1 2) (drv c R2 2)`
holds at time `2`. -/
theorem rightEdgeTwin_step_two (c : Nat → Bool) {M : Nat} {R1 R2 : Nat → Bool}
    (htwin : RightEdgeTwin M R1 R2) :
    RightEdgeTwin (M + 2) (drv c R1 2) (drv c R2 2) := by
  rcases htwin with ⟨hM, hag, hm1, hm, h1_M1, h2_M1, htail⟩
  obtain ⟨hag1, hM1_1, hM2_1⟩ := drv_one_eq_of_zero_one_wall c hM hag hm1 hm
  have hm_2 : R2 M = true := by rw [← hag M (by omega), hm]
  have h1_M2 : R1 (M + 2) = false := (htail (M + 2) (by omega)).1
  have h2_M2 : R2 (M + 2) = false := (htail (M + 2) (by omega)).2
  have h1_M3 : R1 (M + 3) = false := (htail (M + 3) (by omega)).1
  have h2_M3 : R2 (M + 3) = false := (htail (M + 3) (by omega)).2
  have hd1_M1 : drv c R1 1 (M + 1) = true := by
    rw [drv_succ_of_pos c R1 0 (by omega), show M + 1 - 1 = M by omega,
      Rule30Ether.drv_init c R1 M (by omega), Rule30Ether.drv_init c R1 (M + 1) (by omega),
      Rule30Ether.drv_init c R1 (M + 2) (by omega), hm, h1_M1, h1_M2]
    rfl
  have hd2_M1 : drv c R2 1 (M + 1) = false := by
    rw [drv_succ_of_pos c R2 0 (by omega), show M + 1 - 1 = M by omega,
      Rule30Ether.drv_init c R2 M (by omega), Rule30Ether.drv_init c R2 (M + 1) (by omega),
      Rule30Ether.drv_init c R2 (M + 2) (by omega), hm_2, h2_M1, h2_M2]
    rfl
  have hd1_M2 : drv c R1 1 (M + 2) = false := by
    rw [drv_succ_of_pos c R1 0 (by omega), show M + 2 - 1 = M + 1 by omega,
      Rule30Ether.drv_init c R1 (M + 1) (by omega), Rule30Ether.drv_init c R1 (M + 2) (by omega),
      Rule30Ether.drv_init c R1 (M + 3) (by omega), h1_M1, h1_M2, h1_M3]
    rfl
  have hd2_M2 : drv c R2 1 (M + 2) = true := by
    rw [drv_succ_of_pos c R2 0 (by omega), show M + 2 - 1 = M + 1 by omega,
      Rule30Ether.drv_init c R2 (M + 1) (by omega), Rule30Ether.drv_init c R2 (M + 2) (by omega),
      Rule30Ether.drv_init c R2 (M + 3) (by omega), h2_M1, h2_M2, h2_M3]
    rfl
  have htail1 : ∀ p, M + 3 ≤ p → drv c R1 1 p = false ∧ drv c R2 1 p = false := by
    intro p hp
    have hk1 := htail (p - 1) (by omega)
    have hk2 := htail p (by omega)
    have hk3 := htail (p + 1) (by omega)
    constructor
    · rw [drv_succ_of_pos c R1 0 (by omega),
        Rule30Ether.drv_init c R1 (p - 1) (by omega), Rule30Ether.drv_init c R1 p (by omega),
        Rule30Ether.drv_init c R1 (p + 1) (by omega), hk1.1, hk2.1, hk3.1]
      rfl
    · rw [drv_succ_of_pos c R2 0 (by omega),
        Rule30Ether.drv_init c R2 (p - 1) (by omega), Rule30Ether.drv_init c R2 p (by omega),
        Rule30Ether.drv_init c R2 (p + 1) (by omega), hk1.2, hk2.2, hk3.2]
      rfl
  have hd1_M3 : drv c R1 1 (M + 3) = false := (htail1 (M + 3) (by omega)).1
  have hd2_M3 : drv c R2 1 (M + 3) = false := (htail1 (M + 3) (by omega)).2
  have hd1_M4 : drv c R1 1 (M + 4) = false := (htail1 (M + 4) (by omega)).1
  have hd2_M4 : drv c R2 1 (M + 4) = false := (htail1 (M + 4) (by omega)).2
  have h2_colM1_1 : drv c R1 2 (M + 1) = false := by
    rw [drv_succ_of_pos c R1 1 (by omega), show M + 1 - 1 = M by omega,
      hM1_1, hd1_M1, hd1_M2]; rfl
  have h2_colM1_2 : drv c R2 2 (M + 1) = false := by
    rw [drv_succ_of_pos c R2 1 (by omega), show M + 1 - 1 = M by omega,
      hM2_1, hd2_M1, hd2_M2]; rfl
  have h2_colM2_1 : drv c R1 2 (M + 2) = true := by
    rw [drv_succ_of_pos c R1 1 (by omega), show M + 2 - 1 = M + 1 by omega,
      hd1_M1, hd1_M2, hd1_M3]; rfl
  have h2_colM2_2 : drv c R2 2 (M + 2) = true := by
    rw [drv_succ_of_pos c R2 1 (by omega), show M + 2 - 1 = M + 1 by omega,
      hd2_M1, hd2_M2, hd2_M3]; rfl
  have h2_colM3_1 : drv c R1 2 (M + 3) = false := by
    rw [drv_succ_of_pos c R1 1 (by omega), show M + 3 - 1 = M + 2 by omega,
      hd1_M2, hd1_M3, hd1_M4]; rfl
  have h2_colM3_2 : drv c R2 2 (M + 3) = true := by
    rw [drv_succ_of_pos c R2 1 (by omega), show M + 3 - 1 = M + 2 by omega,
      hd2_M2, hd2_M3, hd2_M4]; rfl
  have hag2_le_M := drv_two_eq_of_zero_one_wall c hM hag hm1 hm
  refine ⟨by omega, ?_, ?_, h2_colM2_1, h2_colM3_1, h2_colM3_2, ?_⟩
  · intro p hp
    by_cases hpM : p ≤ M
    · exact hag2_le_M p hpM
    · have : p = M + 1 ∨ p = M + 2 := by omega
      rcases this with rfl | rfl
      · rw [h2_colM1_1, h2_colM1_2]
      · rw [h2_colM2_1, h2_colM2_2]
  · rw [show M + 2 - 1 = M + 1 by omega]
    exact h2_colM1_1
  · intro p hp
    have hk1 := htail1 (p - 1) (by omega)
    have hk2 := htail1 p (by omega)
    have hk3 := htail1 (p + 1) (by omega)
    constructor
    · rw [drv_succ_of_pos c R1 1 (by omega), hk1.1, hk2.1, hk3.1]; rfl
    · rw [drv_succ_of_pos c R2 1 (by omega), hk1.2, hk2.2, hk3.2]; rfl

/-- **Iterated Even-Step `RightEdgeTwin` Invariance (`rightEdgeTwin_drv_two_mul`):** for any driver
`c`, `RightEdgeTwin M R1 R2` implies `RightEdgeTwin (M + 2 * s) (drv c R1 (2 * s)) (drv c R2 (2 * s))`
for every `s : Nat`. -/
theorem rightEdgeTwin_drv_two_mul :
    ∀ (s : Nat) (c : Nat → Bool) {M : Nat} {R1 R2 : Nat → Bool},
      RightEdgeTwin M R1 R2 → RightEdgeTwin (M + 2 * s) (drv c R1 (2 * s)) (drv c R2 (2 * s))
  | 0, c, M, R1, R2, htwin => by
    rcases htwin with ⟨hM, hag, hm1, hm, h1_M1, h2_M1, htail⟩
    change RightEdgeTwin M (drv c R1 0) (drv c R2 0)
    refine ⟨hM, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro p hp
      rcases p with _ | p
      · simp [drv_col0]
      · rw [Rule30Ether.drv_init c R1 (p + 1) (by omega), Rule30Ether.drv_init c R2 (p + 1) (by omega), hag (p + 1) hp]
    · rw [Rule30Ether.drv_init c R1 (M - 1) (by omega), hm1]
    · rw [Rule30Ether.drv_init c R1 M (by omega), hm]
    · rw [Rule30Ether.drv_init c R1 (M + 1) (by omega), h1_M1]
    · rw [Rule30Ether.drv_init c R2 (M + 1) (by omega), h2_M1]
    · intro p hp
      rw [Rule30Ether.drv_init c R1 p (by omega), Rule30Ether.drv_init c R2 p (by omega)]
      exact htail p hp
  | s + 1, c, M, R1, R2, htwin => by
    have hstep := rightEdgeTwin_step_two c htwin
    have ih := rightEdgeTwin_drv_two_mul s (fun k => c (2 + k)) hstep
    have hshift1 : drv (fun k => c (2 + k)) (drv c R1 2) (2 * s) = drv c R1 (2 * (s + 1)) := by
      funext p
      rw [← drv_add c R1 2 (2 * s) p, show 2 + 2 * s = 2 * (s + 1) by omega]
    have hshift2 : drv (fun k => c (2 + k)) (drv c R2 2) (2 * s) = drv c R2 (2 * (s + 1)) := by
      funext p
      rw [← drv_add c R2 2 (2 * s) p, show 2 + 2 * s = 2 * (s + 1) by omega]
    rw [hshift1, hshift2, show M + 2 + 2 * s = M + 2 * (s + 1) by omega] at ih
    exact ih

/-- **All-Time Interior Indistinguishability of Right-Edge Twins (`drv_eq_of_rightEdgeTwin`):** if
`RightEdgeTwin M R1 R2` holds, then for any driver `c`, every time `t`, and every column
`p ≤ M + 2 * (t / 2)`, `drv c R1 t p = drv c R2 t p`. -/
theorem drv_eq_of_rightEdgeTwin (c : Nat → Bool) {M : Nat} {R1 R2 : Nat → Bool}
    (htwin : RightEdgeTwin M R1 R2) (t p : Nat) (hp : p ≤ M + 2 * (t / 2)) :
    drv c R1 t p = drv c R2 t p := by
  obtain ⟨s, rfl | rfl⟩ : ∃ s, t = 2 * s ∨ t = 2 * s + 1 := ⟨t / 2, by omega⟩
  · have hp' : p ≤ M + 2 * s := by simpa [Nat.mul_div_right s (by omega : 0 < 2)] using hp
    exact (rightEdgeTwin_drv_two_mul s c htwin).2.1 p hp'
  · have hd : (2 * s + 1) / 2 = s := by omega
    rw [hd] at hp
    rcases rightEdgeTwin_drv_two_mul s c htwin with ⟨hMs, hags, hm1s, hms, _⟩
    have hone := (drv_one_eq_of_zero_one_wall (fun k => c (2 * s + k)) hMs hags hm1s hms).1 p hp
    rw [← drv_add c R1 (2 * s) 1 p, ← drv_add c R2 (2 * s) 1 p] at hone
    exact hone

/-- **Trace Equality `u R1 = u R2` for Right-Edge Twins (`u_eq_of_rightEdgeTwin`):** if
`RightEdgeTwin M R1 R2` holds, then `u R1 = u R2`. -/
theorem u_eq_of_rightEdgeTwin {M : Nat} {R1 R2 : Nat → Bool} (htwin : RightEdgeTwin M R1 R2) :
    u R1 = u R2 := by
  funext s
  have hM : 2 ≤ M := htwin.1
  exact drv_eq_of_rightEdgeTwin altCol htwin (2 * s + 1) 1 (by omega)

/-- **`Psi R1 = Psi R2` for Right-Edge Twins (`Psi_eq_of_rightEdgeTwin`):** if `RightEdgeTwin M R1 R2`
holds, then `Psi R1 = Psi R2`. -/
theorem Psi_eq_of_rightEdgeTwin {M : Nat} {R1 R2 : Nat → Bool} (htwin : RightEdgeTwin M R1 R2) :
    Psi R1 = Psi R2 := by
  unfold Psi
  rw [u_eq_of_rightEdgeTwin htwin]

/-- **Explicit Non-Injectivity of `Psi` on Finitely Supported Right Halves
(`exists_finSupp_ne_and_Psi_eq`):** there exist distinct finitely supported right halves `R1 ≠ R2`
such that `u R1 = u R2` and `Psi R1 = Psi R2` (witnessed by `R1 = {2}` and `R2 = {2, 3}`). -/
theorem exists_finSupp_ne_and_Psi_eq :
    ∃ R1 R2 : Nat → Bool, FinSupp R1 ∧ FinSupp R2 ∧ R1 ≠ R2 ∧ u R1 = u R2 ∧ Psi R1 = Psi R2 := by
  let R1 : Nat → Bool := fun p => p == 2
  let R2 : Nat → Bool := fun p => (p == 2) || (p == 3)
  have htwin : RightEdgeTwin 2 R1 R2 := by
    refine ⟨by omega, ?_, rfl, rfl, rfl, rfl, ?_⟩
    · intro p hp
      have : p = 0 ∨ p = 1 ∨ p = 2 := by omega
      rcases this with rfl | rfl | rfl <;> rfl
    · intro p hp
      have hp2 : (p == 2) = false := beq_false_of_ne (by omega)
      have hp3 : (p == 3) = false := beq_false_of_ne (by omega)
      simp [R1, R2, hp2, hp3]
  refine ⟨R1, R2, ⟨2, fun k hk => beq_false_of_ne (by omega)⟩, ⟨3, fun k hk => ?_⟩, ?_,
    u_eq_of_rightEdgeTwin htwin, Psi_eq_of_rightEdgeTwin htwin⟩
  · have hk2 : (k == 2) = false := beq_false_of_ne (by omega)
    have hk3 : (k == 3) = false := beq_false_of_ne (by omega)
    simp [R2, hk2, hk3]
  · intro h
    have h3 := congrFun h 3
    revert h3
    decide

/-! ### Universal `01 <-> 011` Twin Partner Collapse, Permanent Even-Step Edge Divergence, and Even-Germ Invariance -/

/-- **Universal Right-Edge Twin Partner (`twinPartner`):** adjoins a black cell at `M + 1` to
a right half `R : Nat → Bool`. -/
def twinPartner (M : Nat) (R : Nat → Bool) (p : Nat) : Bool :=
  if p = M + 1 then true else R p

/-- **Universal `RightEdgeTwin` Formation (`rightEdgeTwin_twinPartner`):** for any right half `R`
with `2 ≤ M`, `R (M - 1) = false`, `R M = true`, and `∀ p ≥ M + 1, R p = false`,
`RightEdgeTwin M R (twinPartner M R)` holds. -/
theorem rightEdgeTwin_twinPartner {M : Nat} {R : Nat → Bool} (hM : 2 ≤ M)
    (hm1 : R (M - 1) = false) (hm : R M = true) (htail : ∀ p, M + 1 ≤ p → R p = false) :
    RightEdgeTwin M R (twinPartner M R) := by
  refine ⟨hM, ?_, hm1, hm, htail (M + 1) (Nat.le_refl _), ?_, ?_⟩
  · intro p hp
    have hne : p ≠ M + 1 := by omega
    simp [twinPartner, hne]
  · simp [twinPartner]
  · intro p hp
    have hne : p ≠ M + 1 := by omega
    refine ⟨htail p (by omega), ?_⟩
    simp [twinPartner, hne, htail p (by omega)]

/-- **Distinctness of `twinPartner` (`ne_twinPartner`):** if `R (M + 1) = false`, then
`R ≠ twinPartner M R`. -/
theorem ne_twinPartner {M : Nat} {R : Nat → Bool} (hM1 : R (M + 1) = false) :
    R ≠ twinPartner M R := by
  intro heq
  have h := congrFun heq (M + 1)
  simp [twinPartner, hM1] at h

/-- **Trace Equality `u (twinPartner M R) = u R` (`u_twinPartner_eq`):** for any right half `R`
with `2 ≤ M`, `R (M - 1) = false`, `R M = true`, and `∀ p ≥ M + 1, R p = false`,
`u (twinPartner M R) = u R`. -/
theorem u_twinPartner_eq {M : Nat} {R : Nat → Bool} (hM : 2 ≤ M)
    (hm1 : R (M - 1) = false) (hm : R M = true) (htail : ∀ p, M + 1 ≤ p → R p = false) :
    u (twinPartner M R) = u R :=
  (u_eq_of_rightEdgeTwin (rightEdgeTwin_twinPartner hM hm1 hm htail)).symm

/-- **Sideways Germ Map Equality `Psi (twinPartner M R) = Psi R` (`Psi_twinPartner_eq`):** for
any right half `R` with `2 ≤ M`, `R (M - 1) = false`, `R M = true`, and
`∀ p ≥ M + 1, R p = false`, `Psi (twinPartner M R) = Psi R`. -/
theorem Psi_twinPartner_eq {M : Nat} {R : Nat → Bool} (hM : 2 ≤ M)
    (hm1 : R (M - 1) = false) (hm : R M = true) (htail : ∀ p, M + 1 ≤ p → R p = false) :
    Psi (twinPartner M R) = Psi R :=
  (Psi_eq_of_rightEdgeTwin (rightEdgeTwin_twinPartner hM hm1 hm htail)).symm

/-- **Twin Equivalence of `FinSupp (Psi ·)` (`finSupp_Psi_twinPartner_iff`):** under the
hypotheses of `rightEdgeTwin_twinPartner`, `FinSupp (Psi (twinPartner M R)) ↔ FinSupp (Psi R)`. -/
theorem finSupp_Psi_twinPartner_iff {M : Nat} {R : Nat → Bool} (hM : 2 ≤ M)
    (hm1 : R (M - 1) = false) (hm : R M = true) (htail : ∀ p, M + 1 ≤ p → R p = false) :
    FinSupp (Psi (twinPartner M R)) ↔ FinSupp (Psi R) := by
  rw [Psi_twinPartner_eq hM hm1 hm htail]

/-- **Permanent Even-Step Moving-Edge Divergence of `RightEdgeTwin`
(`drv_even_edge_ne_of_rightEdgeTwin`):** if `RightEdgeTwin M R1 R2` holds, then for every
driver `c` and step `s : Nat`, `drv c R1 (2 * s) (M + 2 * s + 1) = false` and
`drv c R2 (2 * s) (M + 2 * s + 1) = true`. -/
theorem drv_even_edge_ne_of_rightEdgeTwin (c : Nat → Bool) {M : Nat} {R1 R2 : Nat → Bool}
    (htwin : RightEdgeTwin M R1 R2) (s : Nat) :
    drv c R1 (2 * s) (M + 2 * s + 1) = false ∧ drv c R2 (2 * s) (M + 2 * s + 1) = true := by
  rcases rightEdgeTwin_drv_two_mul s c htwin with ⟨_, _, _, _, h1, h2, _⟩
  exact ⟨h1, h2⟩

/-- **Even-Germ Invariance Under `RightEdgeTwin` (`drivenGamma_even_eq_of_rightEdgeTwin`):**
if `RightEdgeTwin M R1 R2` holds, then for every driver `c` and step `s : Nat`,
`drivenGamma c R1 (2 * s) = drivenGamma c R2 (2 * s)`. -/
theorem drivenGamma_even_eq_of_rightEdgeTwin (c : Nat → Bool) {M : Nat} {R1 R2 : Nat → Bool}
    (htwin : RightEdgeTwin M R1 R2) (s : Nat) :
    drivenGamma c R1 (2 * s) = drivenGamma c R2 (2 * s) := by
  have hM : 2 ≤ M := htwin.1
  unfold drivenGamma
  by_cases h3 : 3 ≤ M + 2 * (2 * s / 2)
  · rw [drv_eq_of_rightEdgeTwin c htwin (2 * s) 1 (by omega),
        drv_eq_of_rightEdgeTwin c htwin (2 * s) 2 (by omega),
        drv_eq_of_rightEdgeTwin c htwin (2 * s) 3 h3]
  · have hs0 : s = 0 := by omega
    have hM2 : M = 2 := by omega
    subst hs0; subst hM2
    have h1 := drv_eq_of_rightEdgeTwin c htwin 0 1 (by omega)
    have h2 : drv c R1 0 2 = true := by
      rw [Rule30Ether.drv_init c R1 2 (by omega)]
      exact htwin.2.2.2.1
    have h2' : drv c R2 0 2 = true := by
      rw [← drv_eq_of_rightEdgeTwin c htwin 0 2 (by omega), h2]
    simp [h1, h2, h2']

end Ruliology.CellularAutomata.Rule30CoupledGerms
