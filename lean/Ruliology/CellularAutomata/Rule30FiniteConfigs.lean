module

public import Ruliology.CellularAutomata.Rule30PeriodTwoSideways

/-!
# Rule 30 from any finite configuration: Jen's theorem, period 1 and period 2

`Rule30Jen` and `Rule30Prize` prove Jen's theorem and the period-1 case for the single black cell.
Those proofs use the seed only through its left edge, which moves one cell to the left per step.
So they hold for every configuration with a leftmost black cell. These are the uniform statements
FinConf and NumberLike, at periods 1 and 2.

* `jen`, `periodic_column_unique`: in the evolution of any configuration with a leftmost black cell
  (left-finite and nonzero), no two different columns are both eventually periodic.
* `no_column_eventually_constant`: in the same evolution, no column is eventually constant. For
  finite configurations this is the period-1 case of FinConf (Condrey 2026).
* `exists_leftmost`, `jen_finite`, `no_column_eventually_constant_finite`: the same for every
  nonzero finite configuration.
* `CQ01_iff_no_finite_period_two`: **`CQ01` is exactly FinConf at period 2 for one column**. It holds
  iff no nonzero finite configuration has a center column that is eventually 2-periodic, whatever
  the transient.
* `no_leftFinite_period_two_of_Q01`: `Q01` gives the same for every configuration with a leftmost
  black cell (NumberLike at period 2 for one column).

**Proof.** If two adjacent columns are eventually periodic with a common start and period, the
reconstruction `cell t (i - 1) = cell (t + 1) i ⊕ (cell t i ∨ cell t (i + 1))` makes every column to
their left periodic too; far to the left, the edge reaches a column after the start of
periodicity, a contradiction (`no_left_periodic`). Between two eventually periodic columns the
strip evolves from its own state, so pigeonhole makes the next column eventually periodic. For
period 1: an eventually white column makes the next column monotone, and an eventually black one
makes the previous column white. For period 2, an eventually 2-periodic center that is not
eventually constant alternates; restarting at a black time gives a finite configuration whose
center alternates from time `0`, which is what `CQ01` excludes
(`Rule30PeriodTwoSideways.CQ01_iff_no_finite_alternating`).

Sources: E. Jen, *Global properties of cellular automata*, J. Stat. Phys. 43 (1986) 219–242;
J. Kopra (TCS 2023) for left-finite configurations; Condrey (arXiv 2609.09431, 2026) for period 1.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30FiniteConfigs

open Rule30Jen Rule30Realization Rule30PeriodTwoCoupled Rule30PeriodTwoSideways

/-! ### Left edge -/

section Edge
variable {x : Int → Bool} {lo : Int} (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
include hlo hzero

omit hlo in
theorem evol_eq_false_of_lt : ∀ (t : Nat) (p : Int), p < lo - t → evol x t p = false
  | 0, p, h => hzero p (by omega)
  | t + 1, p, h => by
    show rule (evol x t (p - 1)) (evol x t p) (evol x t (p + 1)) = false
    rw [evol_eq_false_of_lt t (p - 1) (by omega), evol_eq_false_of_lt t p (by omega),
      evol_eq_false_of_lt t (p + 1) (by omega)]
    rfl

/-- The leftmost black cell moves one step to the left at every step. -/
theorem evol_left_edge : ∀ t : Nat, evol x t (lo - t) = true
  | 0 => by simpa [evol] using hlo
  | t + 1 => by
    show rule (evol x t (lo - ((t + 1 : Nat) : Int) - 1)) (evol x t (lo - ((t + 1 : Nat) : Int)))
      (evol x t (lo - ((t + 1 : Nat) : Int) + 1)) = true
    rw [evol_eq_false_of_lt hzero t _ (by omega), evol_eq_false_of_lt hzero t _ (by omega),
      show lo - ((t + 1 : Nat) : Int) + 1 = lo - (t : Int) by omega, evol_left_edge t]
    rfl

end Edge

/-! ### Reconstruction to the left -/

theorem evol_left (x : Int → Bool) (t : Nat) (i : Int) :
    evol x t (i - 1) = xor (evol x (t + 1) i) (evol x t i || evol x t (i + 1)) := by
  show evol x t (i - 1) =
    xor (rule (evol x t (i - 1)) (evol x t i) (evol x t (i + 1))) (evol x t i || evol x t (i + 1))
  cases evol x t (i - 1) <;> cases evol x t i <;> cases evol x t (i + 1) <;> rfl

theorem periodic_left {x : Int → Bool} {T P : Nat} {i : Int}
    (h0 : ∀ t, T ≤ t → evol x (t + P) i = evol x t i)
    (h1 : ∀ t, T ≤ t → evol x (t + P) (i + 1) = evol x t (i + 1)) :
    ∀ t, T ≤ t → evol x (t + P) (i - 1) = evol x t (i - 1) := by
  intro t ht
  rw [evol_left, evol_left x t, show t + P + 1 = (t + 1) + P by omega, h0 (t + 1) (by omega),
    h0 t ht, h1 t ht]

theorem periodic_left_all {x : Int → Bool} {T P : Nat} {i : Int}
    (h0 : ∀ t, T ≤ t → evol x (t + P) i = evol x t i)
    (h1 : ∀ t, T ≤ t → evol x (t + P) (i + 1) = evol x t (i + 1)) :
    ∀ m : Nat, (∀ t, T ≤ t → evol x (t + P) (i - m) = evol x t (i - m)) ∧
      ∀ t, T ≤ t → evol x (t + P) (i - m + 1) = evol x t (i - m + 1) := by
  intro m
  induction m with
  | zero => simpa using ⟨h0, h1⟩
  | succ m ih =>
    refine ⟨?_, ?_⟩
    · have := periodic_left ih.1 ih.2
      rwa [show i - (m : Int) - 1 = i - ((m + 1 : Nat) : Int) by omega] at this
    · rw [show i - ((m + 1 : Nat) : Int) + 1 = i - (m : Int) by omega]
      exact ih.1

/-- No column far enough to the left is periodic: the edge reaches it after the start. -/
theorem no_left_periodic {x : Int → Bool} {lo : Int} (hlo : x lo = true)
    (hzero : ∀ p, p < lo → x p = false) {T P : Nat} (hP : 0 < P) {i : Int}
    (h : ∀ m : Nat, ∀ t, T ≤ t → evol x (t + P) (i - m) = evol x t (i - m)) : False := by
  let q : Int := min i (lo - ((T + P : Nat) : Int) - 1)
  have hq : q ≤ i := Int.min_le_left _ _
  have hq' : q ≤ lo - ((T + P : Nat) : Int) - 1 := Int.min_le_right _ _
  obtain ⟨t₁, ht₁⟩ : ∃ t₁ : Nat, (t₁ : Int) = lo - q := ⟨(lo - q).toNat, by omega⟩
  have hper := h (i - q).toNat (t₁ - P) (by omega)
  rw [show i - (((i - q).toNat : Nat) : Int) = q by omega, show t₁ - P + P = t₁ by omega] at hper
  have hedge : evol x t₁ q = true := by
    have := evol_left_edge hlo hzero t₁
    rwa [show lo - (t₁ : Int) = q by omega] at this
  have hwhite : evol x (t₁ - P) q = false := evol_eq_false_of_lt hzero _ _ (by omega)
  rw [hedge, hwhite] at hper
  exact absurd hper (by decide)

/-! ### The strip between two columns -/

/-- The cells strictly between columns `j` and `k` at step `t`. -/
def strip (x : Int → Bool) (j k : Int) (t : Nat) : List Bool :=
  (List.range (k - j - 1).toNat).map fun (r : Nat) => evol x t (j + 1 + (r : Int))

set_option linter.unusedSimpArgs false in
/-- The strip evolves from its own state and the two boundary columns. -/
theorem strip_agree {x : Int → Bool} {j k : Int} (hjk : j < k) {t₁ t₂ : Nat}
    (hs : strip x j k t₁ = strip x j k t₂)
    (hb : ∀ r, evol x (t₁ + r) j = evol x (t₂ + r) j ∧ evol x (t₁ + r) k = evol x (t₂ + r) k) :
    ∀ r, ∀ i, j ≤ i → i ≤ k → evol x (t₁ + r) i = evol x (t₂ + r) i := by
  intro r
  induction r with
  | zero =>
    intro i hi1 hi2
    by_cases e1 : i = j
    · subst e1; exact (hb 0).1
    by_cases e2 : i = k
    · subst e2; exact (hb 0).2
    have := congrArg (fun l => l.getD (i - j - 1).toNat false) hs
    simp only [strip, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (show (i - j - 1).toNat < (k - j - 1).toNat by omega),
      Option.map_some, Option.getD_some] at this
    rwa [show j + 1 + (((i - j - 1).toNat : Nat) : Int) = i by omega] at this
  | succ r ih =>
    intro i hi1 hi2
    by_cases e1 : i = j
    · subst e1; exact (hb (r + 1)).1
    by_cases e2 : i = k
    · subst e2; exact (hb (r + 1)).2
    show rule (evol x (t₁ + r) (i - 1)) (evol x (t₁ + r) i) (evol x (t₁ + r) (i + 1)) =
      rule (evol x (t₂ + r) (i - 1)) (evol x (t₂ + r) i) (evol x (t₂ + r) (i + 1))
    rw [ih (i - 1) (by omega) (by omega), ih i (by omega) (by omega),
      ih (i + 1) (by omega) (by omega)]

/-- **Between two eventually periodic columns, the next column is eventually periodic.** -/
theorem between_periodic {x : Int → Bool} {j k : Int} (hjk : j + 1 < k)
    (hj : EventuallyPeriodic fun t => evol x t j) (hk : EventuallyPeriodic fun t => evol x t k) :
    EventuallyPeriodic fun t => evol x t (j + 1) := by
  obtain ⟨T, P, hP, hpj, hpk⟩ := common_period hj hk
  obtain ⟨m, n, hmn, -, he⟩ := pigeonhole (k - j - 1).toNat (fun m => strip x j k (T + m * P))
    (fun m => by simp only [strip, List.length_map, List.length_range])
  refine ⟨T + m * P, (n - m) * P, Nat.mul_pos (by omega) hP, fun t ht => ?_⟩
  have hmul : m * P ≤ n * P := Nat.mul_le_mul_right _ (by omega)
  have key := strip_agree (by omega) he (fun r => ⟨?_, ?_⟩) (t - (T + m * P)) (j + 1)
    (by omega) (by omega)
  · rw [show T + m * P + (t - (T + m * P)) = t by omega,
      show T + n * P + (t - (T + m * P)) = t + (n - m) * P by rw [Nat.sub_mul]; omega] at key
    exact key.symm
  · rw [show T + n * P + r = (T + m * P + r) + (n - m) * P by rw [Nat.sub_mul]; omega]
    exact (periodic_mul (f := fun t => evol x t j) hpj (n - m) _ (by omega)).symm
  · rw [show T + n * P + r = (T + m * P + r) + (n - m) * P by rw [Nat.sub_mul]; omega]
    exact (periodic_mul (f := fun t => evol x t k) hpk (n - m) _ (by omega)).symm

/-! ### Jen's theorem for configurations with a leftmost black cell -/

section Jen
variable {x : Int → Bool} {lo : Int} (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
include hlo hzero

/-- Two adjacent columns are never both eventually periodic. -/
theorem not_adjacent (i : Int) (h0 : EventuallyPeriodic fun t => evol x t i)
    (h1 : EventuallyPeriodic fun t => evol x t (i + 1)) : False := by
  obtain ⟨T, P, hP, hp0, hp1⟩ := common_period h0 h1
  exact no_left_periodic hlo hzero hP fun m => (periodic_left_all hp0 hp1 m).1

/-- **Jen's theorem** for every configuration with a leftmost black cell: no two different
columns are both eventually periodic. -/
theorem jen (j k : Int) (hjk : j ≠ k) :
    ¬ (EventuallyPeriodic (fun t => evol x t j) ∧ EventuallyPeriodic (fun t => evol x t k)) := by
  have lt_case : ∀ a b : Int, a < b → (EventuallyPeriodic fun t => evol x t a) →
      (EventuallyPeriodic fun t => evol x t b) → False := by
    intro a b hab ha hb
    by_cases hadj : b = a + 1
    · subst hadj; exact not_adjacent hlo hzero a ha hb
    · exact not_adjacent hlo hzero a ha (between_periodic (by omega) ha hb)
  rintro ⟨hj, hk⟩
  rcases Int.lt_or_gt_of_ne hjk with h | h
  · exact lt_case j k h hj hk
  · exact lt_case k j h hk hj

/-- At most one column is eventually periodic. -/
theorem periodic_column_unique (j k : Int) (hj : EventuallyPeriodic fun t => evol x t j)
    (hk : EventuallyPeriodic fun t => evol x t k) : j = k :=
  Classical.byContradiction fun h => jen hlo hzero j k h ⟨hj, hk⟩

/-- **No column is eventually constant** (period 1), for every configuration with a leftmost
black cell. -/
theorem no_column_eventually_constant (i : Int) :
    ¬ ∃ T b, ∀ t, T ≤ t → evol x t i = b := by
  rintro ⟨T, b, h⟩
  cases b
  · have hmono : ∀ t, T ≤ t → evol x t (i + 1) = true → evol x (t + 1) (i + 1) = true := by
      intro t ht h1
      show rule (evol x t (i + 1 - 1)) (evol x t (i + 1)) (evol x t (i + 1 + 1)) = true
      rw [show i + 1 - 1 = i by omega, h t ht, h1]
      rfl
    obtain ⟨T', b', h'⟩ := Rule30Prize.eventually_const_of_mono hmono
    exact not_adjacent hlo hzero i (Rule30Prize.eventuallyPeriodic_of_const h)
      (Rule30Prize.eventuallyPeriodic_of_const h')
  · have hleft : ∀ t, T ≤ t → evol x t (i - 1) = false := by
      intro t ht
      have e := h (t + 1) (by omega)
      have hc : evol x (t + 1) i = rule (evol x t (i - 1)) (evol x t i) (evol x t (i + 1)) := rfl
      rw [hc, h t ht] at e
      revert e
      cases evol x t (i - 1) <;> simp [rule]
    refine not_adjacent hlo hzero (i - 1) (Rule30Prize.eventuallyPeriodic_of_const hleft) ?_
    rw [show i - 1 + 1 = i by omega]
    exact Rule30Prize.eventuallyPeriodic_of_const h

end Jen

/-! ### Finite configurations -/

/-- A nonzero finite configuration has a leftmost black cell. -/
theorem exists_leftmost {x : Int → Bool} (hfin : FinConfig x) (hne : ∃ p, x p = true) :
    ∃ lo, x lo = true ∧ ∀ p, p < lo → x p = false := by
  obtain ⟨W, hW⟩ := hfin
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
  have hpW : p.natAbs ≤ W := by
    rcases Nat.lt_or_ge W p.natAbs with h | h
    · rw [hW p h] at hp; exact absurd hp (by decide)
    · exact h
  exact key (2 * W) ⟨p, hp, by omega⟩

/-- **Jen's theorem for finite configurations.** -/
theorem jen_finite {x : Int → Bool} (hfin : FinConfig x) (hne : ∃ p, x p = true) (j k : Int)
    (hjk : j ≠ k) :
    ¬ (EventuallyPeriodic (fun t => evol x t j) ∧ EventuallyPeriodic (fun t => evol x t k)) := by
  obtain ⟨lo, hlo, hzero⟩ := exists_leftmost hfin hne
  exact jen hlo hzero j k hjk

/-- **Period 1 for finite configurations**: from a nonzero finite configuration, no column is
eventually constant. -/
theorem no_column_eventually_constant_finite {x : Int → Bool} (hfin : FinConfig x)
    (hne : ∃ p, x p = true) (i : Int) : ¬ ∃ T b, ∀ t, T ≤ t → evol x t i = b := by
  obtain ⟨lo, hlo, hzero⟩ := exists_leftmost hfin hne
  exact no_column_eventually_constant hlo hzero i

/-- The support grows by at most one cell per step on each side. -/
theorem evol_finConfig {x : Int → Bool} (hfin : FinConfig x) (t : Nat) :
    FinConfig fun p => evol x t p := by
  obtain ⟨W, hW⟩ := hfin
  have key : ∀ t (p : Int), W + t < p.natAbs → evol x t p = false := by
    intro t
    induction t with
    | zero => intro p hp; exact hW p hp
    | succ t ih =>
      intro p hp
      show rule (evol x t (p - 1)) (evol x t p) (evol x t (p + 1)) = false
      rw [ih (p - 1) (by omega), ih p (by omega), ih (p + 1) (by omega)]
      rfl
  exact ⟨W + t, key t⟩

/-! ### Period 2 -/

theorem altCol_succ (t : Nat) : altCol (t + 1) = !altCol t := by
  unfold altCol
  by_cases h : t % 2 = 0
  · rw [h, show (t + 1) % 2 = 1 by omega]; rfl
  · rw [show t % 2 = 1 by omega, show (t + 1) % 2 = 0 by omega]; rfl

/-- An eventually 2-periodic sequence that is not eventually constant alternates. -/
theorem alternates_of_period_two {f : Nat → Bool} {T : Nat} (hT : ∀ t, T ≤ t → f (t + 2) = f t)
    (hnc : ¬ ∃ T b, ∀ t, T ≤ t → f t = b) : ∀ t, T ≤ t → f (t + 1) = !f t := by
  intro t ht
  refine Classical.byContradiction fun hne => ?_
  have h1 : f (t + 1) = f t := by revert hne; cases f (t + 1) <;> cases f t <;> simp
  have hconst : ∀ k, f (t + k) = f t ∧ f (t + k + 1) = f t := by
    intro k
    induction k with
    | zero => exact ⟨rfl, h1⟩
    | succ k ih =>
      refine ⟨by rw [← Nat.add_assoc]; exact ih.2, ?_⟩
      rw [show t + (k + 1) + 1 = (t + k) + 2 by omega, hT _ (by omega)]
      exact ih.1
  exact hnc ⟨t, f t, fun s hs => by
    have := (hconst (s - t)).1; rwa [show t + (s - t) = s by omega] at this⟩

/-- An alternating tail can be restarted at a black time. -/
theorem exists_restart {f : Nat → Bool} {T : Nat} (halt : ∀ t, T ≤ t → f (t + 1) = !f t) :
    ∃ T', T ≤ T' ∧ ∀ t, f (T' + t) = altCol t := by
  obtain ⟨T', hT', hblack⟩ : ∃ T', T ≤ T' ∧ f T' = true := by
    cases hc : f T
    · exact ⟨T + 1, by omega, by rw [halt T (Nat.le_refl T), hc]; rfl⟩
    · exact ⟨T, Nat.le_refl T, hc⟩
  refine ⟨T', hT', fun t => ?_⟩
  induction t with
  | zero => rw [Nat.add_zero, hblack]; rfl
  | succ t ih => rw [show T' + (t + 1) = (T' + t) + 1 by omega, halt _ (by omega), ih, altCol_succ]

/-- **`CQ01` is FinConf at period 2 for one column**: it holds iff no nonzero finite configuration
has an eventually 2-periodic center column, whatever the transient. -/
theorem CQ01_iff_no_finite_period_two : CQ01 ↔
    ∀ x : Int → Bool, FinConfig x → (∃ p, x p = true) →
      ¬ ∃ T, ∀ t, T ≤ t → evol x (t + 2) 0 = evol x t 0 := by
  rw [CQ01_iff_no_finite_alternating]
  constructor
  · rintro hC x hfin hne ⟨T, hT⟩
    obtain ⟨T', -, hT'⟩ := exists_restart
      (alternates_of_period_two hT (no_column_eventually_constant_finite hfin hne 0))
    refine hC ⟨fun p => evol x T' p, evol_finConfig hfin T', fun t => ?_⟩
    rw [Rule30ZeroBoundaryBarriers.evol_restart x T' t 0]
    exact hT' t
  · rintro h ⟨x, hfin, hx⟩
    refine h x hfin ⟨0, hx 0⟩ ⟨0, fun t _ => ?_⟩
    rw [hx, hx]
    unfold altCol
    rw [show (t + 2) % 2 = t % 2 by omega]

/-- **`Q01` settles period 2 for every left-finite configuration** (NumberLike at period 2 for one
column): if `Q01` holds, no configuration with a leftmost black cell has an eventually 2-periodic
center column, whatever the transient. -/
theorem no_leftFinite_period_two_of_Q01 (hQ : Rule30ZeroBoundary.Q01) {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false) :
    ¬ ∃ T, ∀ t, T ≤ t → evol x (t + 2) 0 = evol x t 0 := by
  rintro ⟨T, hT⟩
  obtain ⟨T', -, hT'⟩ := exists_restart
    (alternates_of_period_two hT (no_column_eventually_constant hlo hzero 0))
  refine Q01_no_leftfinite_alternating hQ
    ⟨fun p => evol x T' p, ⟨(T' - lo).toNat, fun p hp => evol_eq_false_of_lt hzero T' p (by omega)⟩,
      fun t => ?_⟩
  rw [Rule30ZeroBoundaryBarriers.evol_restart x T' t 0]
  exact hT' t

/-! ### All-column spatial translation equivariance and all-column period-2 reductions for `Q01` and `CQ01` -/

/-- Spatially shift a configuration `x` by `i` cells (`p ↦ x (p + i)`). -/
def shiftConfig (x : Int → Bool) (i : Int) : Int → Bool := fun p => x (p + i)

/-- **Spatial Translation Equivariance of `evol` (`evol_shiftConfig`).** -/
theorem evol_shiftConfig (x : Int → Bool) (i : Int) :
    ∀ (t : Nat) (p : Int), evol (shiftConfig x i) t p = evol x t (p + i)
  | 0, _ => rfl
  | t + 1, p => by
    show rule (evol (shiftConfig x i) t (p - 1)) (evol (shiftConfig x i) t p)
      (evol (shiftConfig x i) t (p + 1)) =
      rule (evol x t (p + i - 1)) (evol x t (p + i)) (evol x t (p + i + 1))
    rw [evol_shiftConfig x i t (p - 1), evol_shiftConfig x i t p, evol_shiftConfig x i t (p + 1),
      evol_congr (show p - 1 + i = p + i - 1 by omega),
      evol_congr (show p + 1 + i = p + i + 1 by omega)]

/-- **`Q01` Settles Period 2 at Every Integer Column `i` of Every Left-Finite Configuration (`no_leftFinite_period_two_any_col_of_Q01`).** -/
theorem no_leftFinite_period_two_any_col_of_Q01 (hQ : Rule30ZeroBoundary.Q01)
    {x : Int → Bool} {lo : Int} (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false) (i : Int) :
    ¬ ∃ T, ∀ t, T ≤ t → evol x (t + 2) i = evol x t i := by
  rintro ⟨T, hT⟩
  have hlo' : shiftConfig x i (lo - i) = true := by
    unfold shiftConfig; rw [show lo - i + i = lo by omega]; exact hlo
  have hzero' : ∀ p, p < lo - i → shiftConfig x i p = false := fun p hp =>
    hzero (p + i) (by omega)
  refine no_leftFinite_period_two_of_Q01 hQ hlo' hzero' ⟨T, fun t ht => ?_⟩
  rw [evol_shiftConfig, evol_shiftConfig, show (0 : Int) + i = i by omega]
  exact hT t ht

/-- **`CQ01` Is Equivalent to Exclusion of Eventual Period 2 at Every Column `i` of Every Non-Zero Finite Configuration (`CQ01_iff_no_finite_period_two_any_col`).** -/
theorem CQ01_iff_no_finite_period_two_any_col : CQ01 ↔
    ∀ (x : Int → Bool), FinConfig x → (∃ p, x p = true) → ∀ (i : Int),
      ¬ ∃ T, ∀ t, T ≤ t → evol x (t + 2) i = evol x t i := by
  rw [CQ01_iff_no_finite_period_two]
  constructor
  · intro hC x ⟨W, hW⟩ ⟨p0, hp0⟩ i ⟨T, hT⟩
    have hfin' : FinConfig (shiftConfig x i) :=
      ⟨W + i.natAbs, fun p hp => hW (p + i) (by omega)⟩
    have hne' : ∃ p, shiftConfig x i p = true :=
      ⟨p0 - i, by unfold shiftConfig; rw [show p0 - i + i = p0 by omega]; exact hp0⟩
    refine hC (shiftConfig x i) hfin' hne' ⟨T, fun t ht => ?_⟩
    rw [evol_shiftConfig, evol_shiftConfig, show (0 : Int) + i = i by omega]
    exact hT t ht
  · intro hall x hfin hne
    exact hall x hfin hne 0

end Rule30FiniteConfigs
end Ruliology.CellularAutomata
