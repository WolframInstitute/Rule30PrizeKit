module

public import Rule30Equivalents.Mixing

/-!
# The law of a driven fair right half

Prescribe the center bits `w 0, …, w (T - 1)` and run rule 30 for `T` ticks from a fair-coin right
half (`after`). The range of the result is a closed set of mass `2⁻ᵀ` (`mass_attainable`), and the
result has the fair law conditioned on it: `2ᵀ μ(after⁻¹ E) = μ(range ∩ E)` for every measurable
`E` (`after_exact`). Distinct words have ranges that meet in a null set (`incompatible_pasts`), and
countably many infinite pasts are null (`countable_long_past_null`). The proof decodes the past from
010 windows far east (`Preimages.eq_of_evol_one_eq_on_of_window`), on one conull set valid against
every comparison row (`ae_read_past`, `Feedback.ae_read_all`), and integrates over the independent
trace (`RandomConfigurations.traceRightHalf`).

The same law holds when a continuous rule chooses the whole boundary from the initial right half
(`Feedback.driven_exact`), in particular for the actual center beside any fixed left half
(`Feedback.later_exact`, `Feedback.mass_later`). So if, beside every finite left half with a black
cell, each purely periodic center word read from tick zero has a null set of right halves, then
beside each such left half the center is almost surely not eventually periodic
(`Feedback.reduction`). That hypothesis is open.

Index zero of a right half denotes spatial site +1.

Contributed by Gareth Herbert with Claude (Anthropic) and GPT (OpenAI).
-/

@[expose] public section

namespace Rule30Equivalents.DrivenRightHalf

open MeasureTheory Ruliology.CellularAutomata Rule30Realization
open Rule30Equivalents Genericity RandomConfigurations

/-- Draw the initial right half and prescribe the entire time trace at site zero.
The kit's unique realization gives its physical right half at time T. -/
noncomputable def after (w : ℕ → Bool) (T : ℕ) (r : ℕ → Bool) : ℕ → Bool :=
  rightHalf (evol (traceRightHalf.symm (w, r)) T)

theorem measurable_after (w : ℕ → Bool) (T : ℕ) : Measurable (after w T) :=
  measurable_rightHalf.comp ((Mixing.measurePreserving_evol T).measurable.comp
    (traceRightHalf.symm.continuous.measurable.comp (measurable_const.prodMk measurable_id)))

/-- Agreement in the right row at time zero and boundary at times 0,…,T−1
determines the entire right row at time T. -/
theorem right_congr {x y : ℤ → Bool} (right : rightHalf x = rightHalf y) (T : ℕ)
    (wall : ∀ i < T, trace x i = trace y i) :
    rightHalf (evol x T) = rightHalf (evol y T) := by
  have h : ∀ t ≤ T, ∀ p : ℤ, 1 ≤ p → evol x t p = evol y t p := by
    intro t
    induction t with
    | zero =>
      intro _ p hp
      have e := congrFun right (p-1).toNat
      simpa only [rightHalf, evol, show ((p-1).toNat : ℤ) + 1 = p by omega] using e
    | succ t ih =>
      intro ht p hp
      have hleft : evol x t (p-1) = evol y t (p-1) := by
        rcases eq_or_lt_of_le hp with eq | lt
        · subst p
          exact wall t (by omega)
        · exact ih (by omega) _ (by omega)
      simp only [evol, hleft, ih (by omega) p hp, ih (by omega) (p+1) (by omega)]
  funext n
  exact h T le_rfl (n+1) (by omega)

/-- Recovering the entire preceding right half and the boundary bit from one output right half,
when that output contains 010 arbitrarily far east. -/
private theorem back_one {x y : ℤ → Bool}
    (same : rightHalf (evol x 1) = rightHalf (evol y 1))
    (win : ∀ n : ℤ, ∃ q ≥ n,
      evol x 1 q = false ∧ evol x 1 (q+1) = true ∧ evol x 1 (q+2) = false) :
    ∀ p : ℤ, 0 ≤ p → x p = y p := by
  intro p hp
  obtain ⟨q, hq, h0, h1, h2⟩ := win (p+1)
  apply Preimages.eq_of_evol_one_eq_on_of_window (by omega : p < q) _ h0 h1 h2
  intro j hj _
  have e := congrFun same (j-1).toNat
  simpa only [rightHalf, show ((j-1).toNat : ℤ) + 1 = j by omega] using e

/-- Almost every full row has enough synchronizers in every image to decode a finite
past wall word, exclusively from the sites strictly east of it at the final time. -/
theorem ae_read_past :
    ∀ᵐ x ∂(coins ℤ), ∀ (T : ℕ) (y : ℤ → Bool),
      rightHalf (evol x T) = rightHalf (evol y T) →
        ∀ t < T, trace x t = trace y t := by
  filter_upwards [Mixing.ae_isNormal_rows] with x hnormal
  have hw (t : ℕ) (n : ℤ) : ∃ q ≥ n, evol x t q = false ∧
      evol x t (q+1) = true ∧ evol x t (q+2) = false := by
    have hd : Disjunctive fun i : ℕ => evol x t i :=
      fun k w => StrongerStatements.disjunctive_of_isNormal (hnormal t) k w
    obtain ⟨i, hi, hword⟩ := Mixing.exists_ge_of_disjunctive hd ![false,true,false] n.toNat
    refine ⟨i, by omega, ?_⟩
    have h0 := hword 0
    have h1 := hword 1
    have h2 := hword 2
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      add_zero] at h0 h1 h2
    push_cast at h0 h1 h2
    exact ⟨h0,h1,h2⟩
  intro T
  induction T with
  | zero => intro y hy t ht; omega
  | succ t ih =>
    intro y final j hj
    have one (z : ℤ → Bool) : evol (evol z t) 1 = evol z (t+1) := by rfl
    have past := back_one (x := evol x t) (y := evol y t)
      (by rw [one, one]; exact final) (by rw [one]; exact hw (t+1))
    by_cases jt : j = t
    · subst j
      exact past 0 le_rfl
    · exact ih y (funext fun n => past (n+1) (by omega)) j (by omega)

private theorem continuous_after (w : ℕ → Bool) (T : ℕ) : Continuous (after w T) :=
  continuous_rightHalf.comp ((continuous_pi (continuous_evol T)).comp
    (traceRightHalf.symm.continuous.comp (continuous_const.prodMk continuous_id)))

/-- The closed set of right rows attainable after the indicated driven history. -/
def attainable (w : ℕ → Bool) (T : ℕ) : Set (ℕ → Bool) := Set.range (after w T)

theorem closed_attainable (w : ℕ → Bool) (T : ℕ) : IsClosed (attainable w T) :=
  (isCompact_range (continuous_after w T)).isClosed

/-- The exact law of a forced right half at a fixed time: it is the fair law restricted
to the closed set of rows with this boundary history, renormalized by 2^T. -/
theorem after_exact (w : ℕ → Bool) (T : ℕ) (E : Set (ℕ → Bool)) (hE : MeasurableSet E) :
    (2⁻¹ : ENNReal)^T * coins ℕ (after w T ⁻¹' E) =
      coins ℕ (attainable w T ∩ E) := by
  let C := Set.pi (Finset.range T : Set ℕ) (fun i => {w i})
  let A := after w T ⁻¹' E
  have hC : MeasurableSet C :=
    MeasurableSet.pi (Finset.range T).countable_toSet (fun _ _ => measurableSet_singleton _)
  have hA : MeasurableSet A := measurable_after w T hE
  have mass : coins ℕ C = (2⁻¹ : ENNReal)^T := by
    dsimp only [C]
    rw [coins_pi, Finset.prod_congr rfl fun i _ => coin_singleton (w i),
      Finset.prod_const, Finset.card_range]
  let F := fun x : ℤ → Bool => rightHalf (evol x T)
  have same : traceRightHalf ⁻¹' (C ×ˢ A) =ᵐ[coins ℤ] F ⁻¹' (attainable w T ∩ E) := by
    filter_upwards [ae_read_past] with x hx
    apply propext
    change (trace x ∈ C ∧ after w T (rightHalf x) ∈ E) ↔
      (F x ∈ attainable w T ∧ F x ∈ E)
    have forward (h : trace x ∈ C) : F x = after w T (rightHalf x) := by
      have repr := traceRightHalf.apply_symm_apply (w, rightHalf x)
      rw [traceRightHalf_apply] at repr
      apply right_congr (congrArg Prod.snd repr).symm
      intro i hi
      exact (h i (Finset.mem_range.mpr hi)).trans ((congrFun (congrArg Prod.fst repr) i).symm)
    constructor
    · rintro ⟨hc,he⟩
      exact ⟨⟨rightHalf x, (forward hc).symm⟩, forward hc ▸ he⟩
    · rintro ⟨⟨r,hr⟩,he⟩
      have rep := traceRightHalf.apply_symm_apply (w,r)
      rw [traceRightHalf_apply] at rep
      have hc : trace x ∈ C := by
        intro i hi
        exact (hx T (traceRightHalf.symm (w,r)) hr.symm i (Finset.mem_range.mp hi)).trans
          (congrFun (congrArg Prod.fst rep) i)
      exact ⟨hc, forward hc ▸ he⟩
  calc
    (2⁻¹ : ENNReal)^T * coins ℕ A = ((coins ℕ).prod (coins ℕ)) (C ×ˢ A) := by
      rw [Measure.prod_prod, mass]
    _ = coins ℤ (traceRightHalf ⁻¹' (C ×ˢ A)) :=
      (measurePreserving_traceRightHalf.measure_preimage (hC.prod hA).nullMeasurableSet).symm
    _ = coins ℤ (F ⁻¹' (attainable w T ∩ E)) := measure_congr same
    _ = coins ℕ (attainable w T ∩ E) := (measurePreserving_rightHalf.comp
      (Mixing.measurePreserving_evol T)).measure_preimage
        (((closed_attainable w T).measurableSet.inter hE).nullMeasurableSet)

/-- A deterministic T-tick drive multiplies the probability of any event by at most 2^T. -/
theorem after_bound (w : ℕ → Bool) (T : ℕ) (E : Set (ℕ → Bool)) (hE : MeasurableSet E) :
    (2⁻¹ : ENNReal)^T * coins ℕ (after w T ⁻¹' E) ≤ coins ℕ E := by
  rw [after_exact w T E hE]
  exact measure_mono Set.inter_subset_right

theorem mass_attainable (w : ℕ → Bool) (T : ℕ) :
    coins ℕ (attainable w T) = (2⁻¹ : ENNReal)^T := by
  simpa using (after_exact w T Set.univ MeasurableSet.univ).symm

/-- Families of successively longer prescribed pasts have null common range. The words
need not be periodic, or even mutually consistent. -/
theorem long_past_null (walls : ℕ → ℕ → Bool) :
    coins ℕ (⋂ T : ℕ, attainable (walls T) T) = 0 := by
  apply le_antisymm _ zero_le
  apply ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num :
    (2⁻¹ : ENNReal) < 1))
  intro T
  rw [← mass_attainable (walls T) T]
  exact measure_mono (Set.iInter_subset _ T)

/-- Two distinct past wall words can label the same present right half only on a null set. -/
theorem incompatible_pasts (w v : ℕ → Bool) (T : ℕ) (hd : ∃ j < T, w j ≠ v j) :
    coins ℕ (attainable w T ∩ attainable v T) = 0 := by
  let F := fun x : ℤ → Bool => rightHalf (evol x T)
  have measurableIntersection := (closed_attainable w T).measurableSet.inter
      (closed_attainable v T).measurableSet
  rw [← (measurePreserving_rightHalf.comp
    (Mixing.measurePreserving_evol T)).measure_preimage measurableIntersection.nullMeasurableSet]
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [ae_read_past] with x hx
  change x ∉ F ⁻¹' (attainable w T ∩ attainable v T)
  rintro ⟨⟨r, hr⟩, ⟨s, hs⟩⟩
  obtain ⟨j,hj,ne⟩ := hd
  have get (w : ℕ → Bool) (r : ℕ → Bool) (h : after w T r = F x) : trace x j = w j := by
    have rep := traceRightHalf.apply_symm_apply (w,r)
    rw [traceRightHalf_apply] at rep
    exact (hx T (traceRightHalf.symm (w,r)) h.symm j hj).trans (congrFun (congrArg Prod.fst rep) j)
  exact ne ((get w r hr).symm.trans (get v s hs))

/-- Countably many proposed backward histories (in particular all eventually periodic
pasts) still make a null set of present right halves. -/
theorem countable_long_past_null {ι : Type} [Countable ι] (walls : ι → ℕ → ℕ → Bool) :
    coins ℕ (⋃ i, ⋂ T, attainable (walls i T) T) = 0 :=
  measure_iUnion_null (fun i => long_past_null (walls i))

/-- Null right-row events stay null after any finite prescribed wall transient. -/
theorem after_null (w : ℕ → Bool) (T : ℕ) {E : Set (ℕ → Bool)} (hE : MeasurableSet E)
    (hzero : coins ℕ E = 0) : coins ℕ (after w T ⁻¹' E) = 0 := by
  have bound := after_bound w T E hE
  rw [hzero, nonpos_iff_eq_zero, mul_eq_zero] at bound
  exact bound.resolve_left (pow_ne_zero _ (ENNReal.inv_ne_zero.mpr (by norm_num)))

end Rule30Equivalents.DrivenRightHalf

/-! The mass law under continuous feedback and the conditional reduction to pure periods. -/

namespace Rule30Equivalents.DrivenRightHalf.Feedback

open MeasureTheory Ruliology.CellularAutomata Rule30Realization
open Rule30Equivalents Genericity RandomConfigurations Rule30Equivalents.DrivenRightHalf

private theorem back_one {x y : ℤ → Bool}
    (same : rightHalf (evol x 1) = rightHalf (evol y 1))
    (win : ∀ n : ℤ, ∃ q ≥ n, evol x 1 q = false ∧ evol x 1 (q+1) = true ∧ evol x 1 (q+2) = false) :
    ∀ p : ℤ, 0 ≤ p → x p = y p := by
  intro p hp
  obtain ⟨q, hq, h0, h1, h2⟩ := win (p+1)
  apply Preimages.eq_of_evol_one_eq_on_of_window (by omega : p < q) _ h0 h1 h2
  intro j hj _
  have e := congrFun same (j-1).toNat
  simpa only [rightHalf, show ((j-1).toNat : ℤ) + 1 = j by omega] using e

/-- The right half at time `T` decodes every earlier cell at and right of the boundary, for almost every row. -/
theorem ae_read_all :
    ∀ᵐ x ∂(coins ℤ), ∀ (T : ℕ) (y : ℤ → Bool), rightHalf (evol x T) = rightHalf (evol y T) →
      ∀ t < T, ∀ p : ℤ, 0 ≤ p → evol x t p = evol y t p := by
  filter_upwards [Mixing.ae_isNormal_rows] with x hnormal
  have hw (t : ℕ) (n : ℤ) : ∃ q ≥ n, evol x t q = false ∧
      evol x t (q+1) = true ∧ evol x t (q+2) = false := by
    have hd : Disjunctive fun i : ℕ => evol x t i :=
      fun k w => StrongerStatements.disjunctive_of_isNormal (hnormal t) k w
    obtain ⟨i, hi, hword⟩ := Mixing.exists_ge_of_disjunctive hd ![false,true,false] n.toNat
    refine ⟨i, by omega, ?_⟩
    have h0 := hword 0
    have h1 := hword 1
    have h2 := hword 2
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      add_zero] at h0 h1 h2
    push_cast at h0 h1 h2
    exact ⟨h0,h1,h2⟩
  intro T
  induction T with
  | zero => intro y hy t ht; omega
  | succ t ih =>
    intro y final j hj
    have one (z : ℤ → Bool) : evol (evol z t) 1 = evol z (t+1) := by rfl
    have past := back_one (x := evol x t) (y := evol y t)
      (by rw [one, one]; exact final) (by rw [one]; exact hw (t+1))
    by_cases jt : j = t
    · subst j
      exact past
    · exact ih y (funext fun n => past (n+1) (by omega)) j (by omega)

/-- The right half at time `T` when the boundary is chosen by a feedback rule `W` from the initial right half. -/
noncomputable def driven (W : (ℕ → Bool) → ℕ → Bool) (T : ℕ) (r : ℕ → Bool) : ℕ → Bool := after (W r) T r

private theorem continuous_driven {W : (ℕ → Bool) → ℕ → Bool} (hW : Continuous W) (T : ℕ) : Continuous (driven W T) :=
  continuous_rightHalf.comp ((continuous_pi (continuous_evol T)).comp
    (traceRightHalf.symm.continuous.comp (hW.prodMk continuous_id)))

/-- **Any continuous feedback.** Whatever continuous rule chooses the boundary from the initial right half, the right half
at time `T` has the fair law restricted to a closed set of measure `2⁻ᵀ`, times `2ᵀ`. -/
theorem driven_exact {W : (ℕ → Bool) → ℕ → Bool} (hW : Continuous W) (T : ℕ) (E : Set (ℕ → Bool))
    (hE : MeasurableSet E) :
    (2⁻¹ : ENNReal)^T * coins ℕ (driven W T ⁻¹' E) = coins ℕ (Set.range (driven W T) ∩ E) := by
  have hc := continuous_driven hW T
  have hrange : MeasurableSet (Set.range (driven W T)) := (isCompact_range hc).isClosed.measurableSet
  have hA : MeasurableSet (driven W T ⁻¹' E) := hc.measurable hE
  let D : Set ((ℕ → Bool) × (ℕ → Bool)) := {p | (∀ i < T, p.1 i = W p.2 i) ∧ driven W T p.2 ∈ E}
  have hD : MeasurableSet D := by
    have h₁ : MeasurableSet {p : (ℕ → Bool) × (ℕ → Bool) | ∀ i < T, p.1 i = W p.2 i} := by
      have : {p : (ℕ → Bool) × (ℕ → Bool) | ∀ i < T, p.1 i = W p.2 i} =
          ⋂ i : ℕ, ⋂ _ : i < T, {p | p.1 i = W p.2 i} := by ext p; simp
      rw [this]
      refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => ?_
      exact (isClosed_eq ((continuous_apply i).comp continuous_fst)
        ((continuous_apply i).comp (hW.comp continuous_snd))).measurableSet
    exact h₁.inter (hA.preimage measurable_snd)
  let F := fun x : ℤ → Bool => rightHalf (evol x T)
  have same : traceRightHalf ⁻¹' D =ᵐ[coins ℤ] F ⁻¹' (Set.range (driven W T) ∩ E) := by
    filter_upwards [ae_read_all] with x hx
    apply propext
    change ((∀ i < T, trace x i = W (rightHalf x) i) ∧ driven W T (rightHalf x) ∈ E) ↔
      (F x ∈ Set.range (driven W T) ∧ F x ∈ E)
    have repr (r : ℕ → Bool) : trace (traceRightHalf.symm (W r, r)) = W r ∧
        rightHalf (traceRightHalf.symm (W r, r)) = r := by
      have h := traceRightHalf.apply_symm_apply (W r, r)
      rw [traceRightHalf_apply] at h
      exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    have forward (h : ∀ i < T, trace x i = W (rightHalf x) i) : F x = driven W T (rightHalf x) := by
      apply right_congr (repr (rightHalf x)).2.symm
      intro i hi
      rw [(repr (rightHalf x)).1]
      exact h i hi
    constructor
    · rintro ⟨hc, he⟩
      exact ⟨⟨rightHalf x, (forward hc).symm⟩, forward hc ▸ he⟩
    · rintro ⟨⟨r, hr⟩, he⟩
      have read := hx T (traceRightHalf.symm (W r, r)) hr.symm
      have hrx : T = 0 ∨ rightHalf x = r := by
        rcases Nat.eq_zero_or_pos T with h0 | hT
        · exact Or.inl h0
        · right
          funext n
          have := read 0 hT (n + 1) (by omega)
          have e := congrFun (repr r).2 n
          exact this.trans e
      rcases hrx with rfl | rfl
      · have : rightHalf x = r := by
          have e : F x = r := by
            rw [← hr]
            exact (repr r).2
          exact e
        subst this
        exact ⟨fun i hi => absurd hi (by omega), hr ▸ he⟩
      · refine ⟨fun i hi => ?_, ?_⟩
        · exact (read i hi 0 le_rfl).trans (congrFun (repr (rightHalf x)).1 i)
        · rw [hr]; exact he
  have mass (r : ℕ → Bool) : coins ℕ {w : ℕ → Bool | ∀ i < T, w i = W r i} = (2⁻¹ : ENNReal)^T := by
    have : {w : ℕ → Bool | ∀ i < T, w i = W r i} = Set.pi (Finset.range T : Set ℕ) (fun i => {W r i}) := by
      ext w; simp [Set.mem_pi]
    rw [this, coins_pi, Finset.prod_congr rfl fun i _ => coin_singleton (W r i), Finset.prod_const, Finset.card_range]
  have prod : ((coins ℕ).prod (coins ℕ)) D = (2⁻¹ : ENNReal)^T * coins ℕ (driven W T ⁻¹' E) := by
    rw [Measure.prod_apply_symm hD]
    have sec : ∀ r, coins ℕ ((fun w => (w, r)) ⁻¹' D) =
        (driven W T ⁻¹' E).indicator (fun _ => (2⁻¹ : ENNReal)^T) r := by
      intro r
      by_cases hr : r ∈ driven W T ⁻¹' E
      · rw [Set.indicator_of_mem hr]
        have : (fun w : ℕ → Bool => (w, r)) ⁻¹' D = {w | ∀ i < T, w i = W r i} := by
          ext w
          exact ⟨fun h => h.1, fun h => ⟨h, hr⟩⟩
        rw [this, mass]
      · rw [Set.indicator_of_notMem hr]
        have : (fun w : ℕ → Bool => (w, r)) ⁻¹' D = ∅ := by
          ext w
          simp only [Set.mem_empty_iff_false, iff_false]
          exact fun h => hr h.2
        rw [this, measure_empty]
    rw [lintegral_congr sec, lintegral_indicator_const hA]
  calc
    (2⁻¹ : ENNReal)^T * coins ℕ (driven W T ⁻¹' E) = ((coins ℕ).prod (coins ℕ)) D := prod.symm
    _ = coins ℤ (traceRightHalf ⁻¹' D) :=
      (measurePreserving_traceRightHalf.measure_preimage hD.nullMeasurableSet).symm
    _ = coins ℤ (F ⁻¹' (Set.range (driven W T) ∩ E)) := measure_congr same
    _ = coins ℕ (Set.range (driven W T) ∩ E) := (measurePreserving_rightHalf.comp
      (Mixing.measurePreserving_evol T)).measure_preimage ((hrange.inter hE).nullMeasurableSet)

theorem driven_null {W : (ℕ → Bool) → ℕ → Bool} (hW : Continuous W) (T : ℕ) {E : Set (ℕ → Bool)}
    (hE : MeasurableSet E) (h0 : coins ℕ E = 0) : coins ℕ (driven W T ⁻¹' E) = 0 := by
  have h := driven_exact hW T E hE
  have hz : coins ℕ (Set.range (driven W T) ∩ E) = 0 := measure_mono_null Set.inter_subset_right h0
  rw [hz, mul_eq_zero] at h
  exact h.resolve_left (pow_ne_zero _ (ENNReal.inv_ne_zero.mpr (by norm_num)))

/-! ### A fixed left half -/

/-- The row with left half `L` (index `n` is site `-n`) and right half `r` (index `n` is site `n + 1`). -/
def row (L r : ℕ → Bool) : ℤ → Bool := fun p => if p ≤ 0 then L (-p).toNat else r (p - 1).toNat

theorem continuous_row (L : ℕ → Bool) : Continuous (row L) := by
  refine continuous_pi fun p => ?_
  unfold row
  split
  · exact continuous_const
  · exact continuous_apply _

theorem rightHalf_row (L r : ℕ → Bool) : rightHalf (row L r) = r := by
  funext n
  simp [rightHalf, row, show ¬ ((n : ℤ) + 1 ≤ 0) by omega]

/-- The right half at time `T` beside the fixed left half `L`. -/
def later (L : ℕ → Bool) (T : ℕ) (r : ℕ → Bool) : ℕ → Bool := rightHalf (evol (row L r) T)

theorem later_eq (L : ℕ → Bool) (T : ℕ) : later L T = driven (fun r => trace (row L r)) T := by
  funext r
  have h := traceRightHalf.apply_symm_apply (trace (row L r), r)
  rw [traceRightHalf_apply] at h
  exact right_congr ((rightHalf_row L r).trans (congrArg Prod.snd h).symm) T
    fun i _ => (congrFun (congrArg Prod.fst h) i).symm

theorem continuous_wall (L : ℕ → Bool) : Continuous fun r => trace (row L r) :=
  continuous_trace.comp (continuous_row L)

/-- **The adaptive corollary.** Beside any fixed left half the right half at time `T` has the fair law restricted to
a closed set of measure `2⁻ᵀ`, times `2ᵀ`. -/
theorem later_exact (L : ℕ → Bool) (T : ℕ) (E : Set (ℕ → Bool)) (hE : MeasurableSet E) :
    (2⁻¹ : ENNReal)^T * coins ℕ (later L T ⁻¹' E) = coins ℕ (Set.range (later L T) ∩ E) := by
  rw [later_eq]
  exact driven_exact (continuous_wall L) T E hE

theorem mass_later (L : ℕ → Bool) (T : ℕ) : coins ℕ (Set.range (later L T)) = (2⁻¹ : ENNReal)^T := by
  simpa using (later_exact L T Set.univ MeasurableSet.univ).symm

/-! ### Reduction to purely periodic words -/

/-- The left half at time `T`. -/
def leftAt (x : ℤ → Bool) (T : ℕ) : ℕ → Bool := fun n => evol x T (-(n : ℤ))

theorem evol_add (x : ℤ → Bool) (T : ℕ) : ∀ t p, evol (evol x T) t p = evol x (T + t) p := by
  intro t
  induction t with
  | zero => intro p; rfl
  | succ t ih =>
    intro p
    show Rule30Jen.rule _ _ _ = Rule30Jen.rule _ _ _
    rw [ih, ih, ih]
    rfl

theorem row_at (x : ℤ → Bool) (T : ℕ) : row (leftAt x T) (rightHalf (evol x T)) = evol x T := by
  funext p
  unfold row leftAt rightHalf
  split
  · rename_i h; rw [show -(((-p).toNat : ℕ) : ℤ) = p by omega]
  · rename_i h; rw [show (((p - 1).toNat : ℕ) : ℤ) + 1 = p by omega]

/-- A finite left half stays finite. -/
theorem left_finite (L r : ℕ → Bool) (B : ℕ) (hB : ∀ n, B ≤ n → L n = false) (T : ℕ) :
    ∀ p : ℤ, p ≤ -((B + T : ℕ) : ℤ) → evol (row L r) T p = false := by
  induction T with
  | zero =>
    intro p hp
    show row L r p = false
    unfold row
    rw [ite_eq_left (by omega)]
    exact hB _ (by omega)
  | succ T ih =>
    intro p hp
    show Rule30Jen.rule (evol (row L r) T (p - 1)) (evol (row L r) T p) (evol (row L r) T (p + 1)) = false
    rw [ih (p - 1) (by omega), ih p (by omega), ih (p + 1) (by omega)]
    rfl

/-- The leftmost black site moves left at speed one. -/
theorem left_black (L r : ℕ → Bool) (m : ℕ) (hm : L m = true) (hB : ∀ n, m + 1 ≤ n → L n = false) (T : ℕ) :
    evol (row L r) T (-((m + T : ℕ) : ℤ)) = true := by
  induction T with
  | zero =>
    show row L r _ = true
    unfold row
    rw [ite_eq_left (by omega), show (-(-((m + 0 : ℕ) : ℤ))).toNat = m by omega]
    exact hm
  | succ T ih =>
    show Rule30Jen.rule (evol (row L r) T _) (evol (row L r) T _) (evol (row L r) T _) = true
    rw [left_finite L r (m + 1) hB T _ (by omega), left_finite L r (m + 1) hB T _ (by omega),
      show -((m + (T + 1) : ℕ) : ℤ) + 1 = -((m + T : ℕ) : ℤ) by omega, ih]
    rfl

/-- The finite left half with black sites `-n`, `n ∈ s`. -/
def fin (s : Finset ℕ) : ℕ → Bool := fun n => decide (n ∈ s)

/-- **Almost-sure aperiodicity reduces to pure periodic targets from time zero.** If beside every finite left half with a black site the set of
right halves whose centre is one given purely periodic word is null, then beside every such left half the centre is
almost surely not eventually periodic. (The converse is immediate.) -/
theorem reduction
    (h : ∀ (s : Finset ℕ), s.Nonempty → ∀ (P : ℕ) (v : Fin (P + 1) → Bool),
      coins ℕ {r | ∀ t, trace (row (fin s) r) t = v ⟨t % (P + 1), Nat.mod_lt _ (by omega)⟩} = 0)
    (s : Finset ℕ) (hs : s.Nonempty) :
    ∀ᵐ r ∂(coins ℕ), ¬ ∃ T P : ℕ, 1 ≤ P ∧ ∀ t, T ≤ t → trace (row (fin s) r) (t + P) = trace (row (fin s) r) t := by
  -- every such right half lies in one of countably many null sets
  let X : {s : Finset ℕ // s.Nonempty} × ℕ × (Σ P : ℕ, Fin (P + 1) → Bool) → Set (ℕ → Bool) := fun q =>
    later (fin s) q.2.1 ⁻¹' {r | ∀ t, trace (row (fin q.1.1) r) t =
      q.2.2.2 ⟨t % (q.2.2.1 + 1), Nat.mod_lt _ (by omega)⟩}
  have hX : ∀ q, coins ℕ (X q) = 0 := by
    rintro ⟨⟨s', hne⟩, T, ⟨P, v⟩⟩
    show coins ℕ (later (fin s) T ⁻¹' _) = 0
    rw [later_eq]
    refine driven_null (continuous_wall _) T ?_ (h s' hne P v)
    have : {r : ℕ → Bool | ∀ t, trace (row (fin s') r) t = v ⟨t % (P + 1), Nat.mod_lt _ (by omega)⟩} =
        ⋂ t, {r | trace (row (fin s') r) t = v ⟨t % (P + 1), Nat.mod_lt _ (by omega)⟩} := by ext r; simp
    rw [this]
    exact MeasurableSet.iInter fun t =>
      (isClosed_eq ((continuous_apply t).comp (continuous_wall (fin s'))) continuous_const).measurableSet
  rw [ae_iff]
  refine measure_mono_null ?_ (measure_iUnion_null hX)
  intro r hr
  simp only [Set.mem_ofPred_eq, not_not] at hr
  obtain ⟨T, P, hP, per⟩ := hr
  obtain ⟨P, rfl⟩ : ∃ P', P = P' + 1 := ⟨P - 1, by omega⟩
  -- the left half at time T is finite and has a black site
  obtain ⟨m, hm, hmax⟩ : ∃ m ∈ s, ∀ n ∈ s, n ≤ m := ⟨s.max' hs, s.max'_mem hs, fun n hn => s.le_max' n hn⟩
  have hB : ∀ n, m + 1 ≤ n → fin s n = false := fun n hn => by
    unfold fin
    rw [decide_eq_false_iff_not]
    intro hin
    have := hmax n hin
    omega
  have hLm : fin s m = true := by unfold fin; exact decide_eq_true hm
  let x := row (fin s) r
  let s' : Finset ℕ := (Finset.range (m + 1 + T)).filter fun n => leftAt x T n = true
  have hs' : fin s' = leftAt x T := by
    funext n
    unfold fin
    by_cases hn : n < m + 1 + T
    · cases e : leftAt x T n <;> simp [s', hn, e]
    · have : leftAt x T n = false := left_finite (fin s) r (m + 1) hB T _ (by omega)
      rw [this]
      simp [s', hn]
  have hne : s'.Nonempty := by
    refine ⟨m + T, ?_⟩
    simp only [s', Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, left_black (fin s) r m hLm hB T⟩
  refine Set.mem_iUnion.mpr ⟨⟨⟨s', hne⟩, T, ⟨P, fun k => trace x (T + k.val)⟩⟩, ?_⟩
  show ∀ t, trace (row (fin s') (later (fin s) T r)) t = trace x (T + t % (P + 1))
  intro t
  have e : row (fin s') (later (fin s) T r) = evol x T := by rw [hs']; exact row_at x T
  rw [e]
  show evol (evol x T) t 0 = _
  rw [evol_add]
  show trace x (T + t) = trace x (T + t % (P + 1))
  induction t using Nat.strongRecOn with
  | ind t ih =>
    rcases Nat.lt_or_ge t (P + 1) with lt | ge
    · rw [Nat.mod_eq_of_lt lt]
    · have e₁ := per (T + (t - (P + 1))) (by omega)
      rw [show T + (t - (P + 1)) + (P + 1) = T + t by omega] at e₁
      rw [e₁, ih (t - (P + 1)) (by omega), Nat.mod_eq_sub_mod ge]

end Rule30Equivalents.DrivenRightHalf.Feedback
