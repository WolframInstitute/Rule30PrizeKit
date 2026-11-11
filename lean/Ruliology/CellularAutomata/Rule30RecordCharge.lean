module

public import Ruliology.CellularAutomata.Rule30Prize

/-!
# Record charges: the bookkeeping behind the half-rate period bound

This module is pure arithmetic on natural numbers. It is the accounting half of
`Rule30RightPeriods.per_upper_half`; the Rule 30 input is supplied there.

A *path* (`Path nu`) is a walk `i = 0, 1, 2, …` whose exponent grows by a weight `0`, `1` or `2`
at each step, together with a resource that must satisfy three laws:

* `reset_before`: the resource is `0` just before a weight-`2` step;
* `reset_after`: just after a weight-`2` step it is `2 ^ (nu + exponent - 1) - 1`;
* `countdown`: a weight-`1` step lowers it by at most `1`.

Weight-`0` steps lower the exponent's excess `exponent i - i`; weight-`2` steps raise it, but each
one needs the resource to have run down to `0`, and after a step that lands at excess `q + 1`
the resource is exponentially large. So the excess can only reach `q + 1` after a time
`threshold nu q`, with `threshold nu 0 = 1` and
`threshold nu (q + 1) = threshold nu q + 2 ^ (nu + threshold nu q + q)`
(`record_potential`, `record_time_lower_bound`). Conversely, before time `threshold nu q` the
exponent is at most `i + q` (`exponent_bound_before_threshold`).

`Q nu d` is the least `q` with `d < threshold nu q` (`Q_spec`, `threshold_le_of_lt_Q`), computed
by counting (`countBelow`), and `B j = ⌈j / 2⌉ + Q 0 ⌊j / 2⌋`. The thresholds grow like a tower of
twos (`threshold_tower_step`): `threshold 0` is `1, 3, 19, 2^21 + 19, …`, so `Q 0 d ≤ 3` for
`d ≤ 2^21 + 18` and `Q 0 d` grows like the iterated logarithm `log* d`.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30RecordCharge

/-! ### Counting an initial run -/

/-- The number of `k < n` with `p k`. -/
def countBelow (p : Nat → Prop) [DecidablePred p] : Nat → Nat
  | 0 => 0
  | n + 1 => countBelow p n + if p n then 1 else 0

theorem countBelow_le (p : Nat → Prop) [DecidablePred p] : ∀ n, countBelow p n ≤ n
  | 0 => Nat.le_refl 0
  | n + 1 => by
    have := countBelow_le p n
    simp only [countBelow]
    split <;> omega

theorem countBelow_all (p : Nat → Prop) [DecidablePred p] :
    ∀ n, (∀ k, k < n → p k) → countBelow p n = n
  | 0, _ => rfl
  | n + 1, h => by
    have hn := h n (Nat.lt_succ_self n)
    simp only [countBelow, hn, ite_true, countBelow_all p n (fun k hk => h k (by omega))]

theorem down_closed {p : Nat → Prop} (hp : ∀ k, p (k + 1) → p k) :
    ∀ n, p n → ∀ k, k ≤ n → p k
  | 0, h, k, hk => by rw [Nat.le_zero.mp hk]; exact h
  | n + 1, h, k, hk => by
    rcases Nat.lt_or_eq_of_le hk with hk | hk
    · exact down_closed hp n (hp n h) k (by omega)
    · rw [hk]; exact h

/-- For a predicate closed downwards, `countBelow p n` is the length of its initial run, cut at
`n`. -/
theorem le_countBelow_iff {p : Nat → Prop} [DecidablePred p] (hp : ∀ k, p (k + 1) → p k) :
    ∀ n r, r ≤ n → (r ≤ countBelow p n ↔ ∀ k, k < r → p k)
  | 0, r, hr => by
    have hr0 : r = 0 := by omega
    subst hr0
    exact ⟨fun _ k hk => absurd hk (Nat.not_lt_zero k), fun _ => Nat.zero_le _⟩
  | n + 1, r, hr => by
    by_cases hn : p n
    · rw [countBelow_all p (n + 1) (fun k hk => down_closed hp n hn k (by omega))]
      exact ⟨fun _ k hk => down_closed hp n hn k (by omega), fun _ => hr⟩
    · have hc : countBelow p (n + 1) = countBelow p n := by
        simp only [countBelow, hn, ite_false, Nat.add_zero]
      rw [hc]
      rcases Nat.lt_or_eq_of_le hr with hr | hr
      · exact le_countBelow_iff hp n r (by omega)
      · subst hr
        have := countBelow_le p n
        exact ⟨fun h => absurd h (by omega), fun h => absurd (h n (by omega)) hn⟩

theorem lt_countBelow_iff {p : Nat → Prop} [DecidablePred p] (hp : ∀ k, p (k + 1) → p k)
    {n r : Nat} (hr : r < n) : r < countBelow p n ↔ p r := by
  rw [← Nat.succ_le_iff, le_countBelow_iff hp n (r + 1) hr]
  exact ⟨fun h => h r (Nat.lt_succ_self r),
    fun h k hk => down_closed hp r h k (by omega)⟩

/-! ### Thresholds and paths -/

/-- `threshold nu q` is the earliest time at which the excess `exponent - time` can exceed `q`. -/
def threshold (nu : Nat) : Nat → Nat
  | 0 => 1
  | q + 1 => threshold nu q + 2 ^ (nu + threshold nu q + q)

theorem threshold_step_le (nu q : Nat) : threshold nu q ≤ threshold nu (q + 1) :=
  Nat.le_add_right _ _

theorem threshold_strict (nu q : Nat) : threshold nu q < threshold nu (q + 1) := by
  have hp := Nat.two_pow_pos (nu + threshold nu q + q)
  simp only [threshold]
  omega

theorem threshold_ge (nu q : Nat) : q + 1 ≤ threshold nu q := by
  induction q with
  | zero => exact Nat.le_refl 1
  | succ q ih => have := threshold_strict nu q; omega

theorem threshold_mono (nu : Nat) {a b : Nat} (h : a ≤ b) : threshold nu a ≤ threshold nu b := by
  induction b with
  | zero => rw [Nat.le_zero.mp h]; exact Nat.le_refl _
  | succ b ih =>
    rcases Nat.lt_or_eq_of_le h with h | h
    · exact Nat.le_trans (ih (by omega)) (threshold_step_le nu b)
    · rw [h]; exact Nat.le_refl _

/-- The thresholds grow at least like a tower of twos. -/
theorem threshold_tower_step (nu q : Nat) : 2 ^ (threshold nu q) ≤ threshold nu (q + 1) := by
  have hp := Nat.pow_le_pow_right (n := 2) (by decide)
    (show threshold nu q ≤ nu + threshold nu q + q by omega)
  simp only [threshold]
  omega

/-- A walk with step weights `0`, `1`, `2` and a resource obeying the reset and countdown laws. -/
structure Path (nu : Nat) where
  weight : Nat → Nat
  exponent : Nat → Nat
  resource : Nat → Nat
  exponent_zero : exponent 0 = 0
  exponent_step : ∀ i, exponent (i + 1) = exponent i + weight i
  weight_le_two : ∀ i, weight i ≤ 2
  reset_before : ∀ i, weight i = 2 → resource i = 0
  reset_after : ∀ i, weight i = 2 → resource (i + 1) + 1 = 2 ^ (nu + exponent (i + 1) - 1)
  countdown : ∀ i, weight i = 1 → resource i ≤ resource (i + 1) + 1

/-- The invariant: an excess of `q + 1` at time `i` has paid the time `threshold nu q`, and time
plus remaining resource has paid `threshold nu (q + 1) - 1`. -/
theorem record_potential {nu : Nat} (p : Path nu) :
    ∀ i q, i + q + 1 ≤ p.exponent i →
      threshold nu q ≤ i ∧ threshold nu (q + 1) ≤ i + p.resource i + 1 := by
  intro i
  induction i with
  | zero =>
    intro q h
    have hz := p.exponent_zero
    omega
  | succ i ih =>
    intro q h
    have he := p.exponent_step i
    have hk := p.weight_le_two i
    have cases : p.weight i = 0 ∨ p.weight i = 1 ∨ p.weight i = 2 := by omega
    rcases cases with h0 | h1 | h2
    · have old := ih (q + 1) (by omega)
      have mono := threshold_step_le nu q
      constructor <;> omega
    · have old := ih q (by omega)
      have drop := p.countdown i h1
      constructor <;> omega
    · have before := p.reset_before i h2
      have after := p.reset_after i h2
      have paid : threshold nu q ≤ i + 1 := by
        cases q with
        | zero => simp only [threshold]; omega
        | succ q =>
          have old := ih q (by omega)
          omega
      refine ⟨paid, ?_⟩
      have exp_le : nu + threshold nu q + q ≤ nu + p.exponent (i + 1) - 1 := by omega
      have pow_le := Nat.pow_le_pow_right (n := 2) (by decide) exp_le
      simp only [threshold]
      omega

/-- An excess of `q + 1` is reached no earlier than `threshold nu q`. -/
theorem record_time_lower_bound {nu : Nat} (p : Path nu) (i q : Nat)
    (h : i + q + 1 ≤ p.exponent i) : threshold nu q ≤ i :=
  (record_potential p i q h).1

/-- Before time `threshold nu q` the exponent is at most `i + q`. -/
theorem exponent_bound_before_threshold {nu : Nat} (p : Path nu) (i q : Nat)
    (h : i < threshold nu q) : p.exponent i ≤ i + q := by
  have hnot : ¬ i + q + 1 ≤ p.exponent i := by
    intro hc
    have := record_time_lower_bound p i q hc
    omega
  omega

/-! ### The inverse of the thresholds -/

/-- The least `q` with `d < threshold nu q`: the number of `q < d` with `threshold nu q ≤ d`. -/
def Q (nu d : Nat) : Nat := countBelow (fun q => threshold nu q ≤ d) d

theorem threshold_down (nu d : Nat) :
    ∀ k, threshold nu (k + 1) ≤ d → threshold nu k ≤ d :=
  fun k h => Nat.le_trans (threshold_step_le nu k) h

theorem Q_le (nu d : Nat) : Q nu d ≤ d := countBelow_le _ d

theorem Q_spec (nu d : Nat) : d < threshold nu (Q nu d) := by
  rcases Nat.lt_or_eq_of_le (Q_le nu d) with h | h
  · have hiff := lt_countBelow_iff (p := fun q => threshold nu q ≤ d) (threshold_down nu d) h
    have hn : ¬ threshold nu (Q nu d) ≤ d := fun hq => Nat.lt_irrefl _ (hiff.mpr hq)
    omega
  · rw [h]; have := threshold_ge nu d; omega

theorem threshold_le_of_lt_Q {nu d q : Nat} (hq : q < Q nu d) : threshold nu q ≤ d :=
  (lt_countBelow_iff (p := fun q => threshold nu q ≤ d) (threshold_down nu d) (Nat.lt_of_lt_of_le hq (Q_le nu d))).mp hq

/-- `Q nu d` is exactly the least `q` with `d < threshold nu q`. -/
theorem Q_le_iff (nu d q : Nat) : Q nu d ≤ q ↔ d < threshold nu q := by
  constructor
  · intro h
    exact Nat.lt_of_lt_of_le (Q_spec nu d) (threshold_mono nu h)
  · intro h
    apply Nat.le_of_not_lt
    intro hq
    have := threshold_le_of_lt_Q hq
    omega

theorem Q_zero (nu : Nat) : Q nu 0 = 0 := rfl

/-- The exponent `⌈j / 2⌉ + Q 0 ⌊j / 2⌋` of `Rule30RightPeriods.per_upper_half`. -/
def B (j : Nat) : Nat := (j + 1) / 2 + Q 0 (j / 2)

theorem B_zero : B 0 = 0 := rfl
theorem B_one : B 1 = 1 := rfl

theorem threshold_zero_two : threshold 0 2 = 19 := by decide
theorem threshold_zero_three : threshold 0 3 = 2 ^ 21 + 19 := by decide

theorem pow_le_threshold (nu : Nat) : ∀ q, 2 ^ q ≤ threshold nu q
  | 0 => Nat.le_refl 1
  | q + 1 => by
    have ht := threshold_ge nu q
    have hp := Nat.pow_le_pow_right (n := 2) (by decide)
      (show q + 1 ≤ nu + threshold nu q + q by omega)
    simp only [threshold]
    omega

theorem twelve_mul_le_two_pow : ∀ n, 7 ≤ n → 12 * (n + 1) ≤ 2 ^ n
  | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h => absurd h (by decide)
  | 7, _ => by decide
  | n + 8, _ => by
    have := twelve_mul_le_two_pow (n + 7) (by omega)
    rw [Nat.pow_succ]
    omega

/-- Past the third record, `Q 0 d` is tiny compared with `d`. -/
theorem twelve_mul_Q_le {d : Nat} (hd : 2 ^ 21 ≤ d) : 12 * Q 0 d ≤ d := by
  have h21 : (2 : Nat) ^ 21 = 2097152 := by decide
  by_cases hQ : Q 0 d ≤ 8
  · omega
  · have ht := threshold_le_of_lt_Q (show Q 0 d - 1 < Q 0 d by omega)
    have hp := pow_le_threshold 0 (Q 0 d - 1)
    have hw := twelve_mul_le_two_pow (Q 0 d - 1) (by omega)
    rw [show Q 0 d - 1 + 1 = Q 0 d by omega] at hw
    omega

/-- For `j / 2 ≤ 2 ^ 21 + 18`, `B j ≤ ⌈j / 2⌉ + 3`. -/
theorem B_le_add_three {j : Nat} (hj : j / 2 ≤ 2 ^ 21 + 18) : B j ≤ (j + 1) / 2 + 3 := by
  have h : Q 0 (j / 2) ≤ 3 := (Q_le_iff 0 (j / 2) 3).mpr (by rw [threshold_zero_three]; omega)
  unfold B
  omega

/-- `B j < (2 j + 1) / 3` for every `j ≥ 18`: `B` beats the exponent of
`Rule30RightPeriods.per_upper` from there on (at `j = 17` both are `11`). -/
theorem B_lt_two_thirds {j : Nat} (hj : 18 ≤ j) : B j < (2 * j + 1) / 3 := by
  have h21 : (2 : Nat) ^ 21 = 2097152 := by decide
  unfold B
  by_cases h2 : j / 2 < 19
  · have : Q 0 (j / 2) ≤ 2 := (Q_le_iff 0 (j / 2) 2).mpr (by rw [threshold_zero_two]; omega)
    omega
  · by_cases h3 : j / 2 < 2 ^ 21 + 19
    · have : Q 0 (j / 2) ≤ 3 :=
        (Q_le_iff 0 (j / 2) 3).mpr (by rw [threshold_zero_three]; omega)
      omega
    · have := twelve_mul_Q_le (d := j / 2) (by omega)
      omega

/-- Along a path with `nu = 0`, the exponent at time `d` is at most `d + Q 0 d`. -/
theorem exponent_le_Q (p : Path 0) (d : Nat) : p.exponent d ≤ d + Q 0 d :=
  exponent_bound_before_threshold p d (Q 0 d) (Q_spec 0 d)

/-! ### Exact threshold inversion, monotonicity, and 1-Lipschitz bounds for `Q` and `B` -/

/-- **Monotonicity of `threshold` in the shift parameter `nu` (`threshold_mono_nu`):**
for all `nu1 ≤ nu2` and `q : Nat`, `threshold nu1 q ≤ threshold nu2 q`. -/
theorem threshold_mono_nu {nu1 nu2 : Nat} (hnu : nu1 ≤ nu2) :
    ∀ q : Nat, threshold nu1 q ≤ threshold nu2 q
  | 0 => Nat.le_refl 1
  | q + 1 => by
    have ih := threshold_mono_nu hnu q
    have hpow := Nat.pow_le_pow_right (n := 2) (by decide)
      (show nu1 + threshold nu1 q + q ≤ nu2 + threshold nu2 q + q by omega)
    simp only [threshold]
    omega

/-- **Monotonicity of `Q nu d` in `d` (`Q_mono`):**
for all `d1 ≤ d2`, `Q nu d1 ≤ Q nu d2`. -/
theorem Q_mono (nu : Nat) {d1 d2 : Nat} (hd : d1 ≤ d2) : Q nu d1 ≤ Q nu d2 :=
  (Q_le_iff nu d1 (Q nu d2)).mpr (Nat.lt_of_le_of_lt hd (Q_spec nu d2))

/-- **Anti-Monotonicity of `Q nu d` in `nu` (`Q_anti_nu`):**
for all `nu1 ≤ nu2` and `d : Nat`, `Q nu2 d ≤ Q nu1 d`. -/
theorem Q_anti_nu {nu1 nu2 : Nat} (hnu : nu1 ≤ nu2) (d : Nat) : Q nu2 d ≤ Q nu1 d :=
  (Q_le_iff nu2 d (Q nu1 d)).mpr
    (Nat.lt_of_lt_of_le (Q_spec nu1 d) (threshold_mono_nu hnu (Q nu1 d)))

/-- **Exact Interval Characterization of `Q nu d = q + 1` (`Q_eq_succ_iff`):**
`Q nu d = q + 1` if and only if `threshold nu q ≤ d` and `d < threshold nu (q + 1)`. -/
theorem Q_eq_succ_iff (nu d q : Nat) :
    Q nu d = q + 1 ↔ threshold nu q ≤ d ∧ d < threshold nu (q + 1) := by
  constructor
  · intro h
    have hlt : q < Q nu d := by omega
    have hle : Q nu d ≤ q + 1 := by omega
    exact ⟨threshold_le_of_lt_Q hlt, (Q_le_iff nu d (q + 1)).mp hle⟩
  · rintro ⟨hle, hlt⟩
    have h1 : Q nu d ≤ q + 1 := (Q_le_iff nu d (q + 1)).mpr hlt
    have h2 : ¬ Q nu d ≤ q := by
      rw [Q_le_iff]
      omega
    omega

/-- **Exact Evaluation of `Q nu` Just Below a Threshold (`Q_threshold_sub_one`):**
for every `nu, q : Nat`, `Q nu (threshold nu q - 1) = q`. -/
theorem Q_threshold_sub_one (nu : Nat) : ∀ q : Nat, Q nu (threshold nu q - 1) = q
  | 0 => rfl
  | q + 1 => by
    rw [Q_eq_succ_iff]
    have hst := threshold_strict nu q
    have hge := threshold_ge nu (q + 1)
    omega

/-- **Exact Evaluation of `Q nu` at a Threshold (`Q_threshold`):**
for every `nu, q : Nat`, `Q nu (threshold nu q) = q + 1`. -/
theorem Q_threshold (nu q : Nat) : Q nu (threshold nu q) = q + 1 := by
  rw [Q_eq_succ_iff]
  exact ⟨Nat.le_refl _, threshold_strict nu q⟩

/-- **1-Lipschitz Step Bound for `Q nu` (`Q_succ_le`):**
advancing `d` by `1` increases `Q nu d` by at most `1`. -/
theorem Q_succ_le (nu d : Nat) : Q nu (d + 1) ≤ Q nu d + 1 := by
  rw [Q_le_iff]
  have h1 := Q_spec nu d
  have h2 := threshold_strict nu (Q nu d)
  omega

/-- **General-`nu` Exponent Bound (`exponent_le_Q_gen`):**
along any path `p : Path nu` (`nu : Nat`), `p.exponent d ≤ d + Q nu d` for all `d : Nat`. -/
theorem exponent_le_Q_gen {nu : Nat} (p : Path nu) (d : Nat) : p.exponent d ≤ d + Q nu d :=
  exponent_bound_before_threshold p d (Q nu d) (Q_spec nu d)

/-- **Exact Odd-Step Increment of `B` (`B_odd_eq_succ`):**
for every `d : Nat`, `B (2 * d + 1) = B (2 * d) + 1`. -/
theorem B_odd_eq_succ (d : Nat) : B (2 * d + 1) = B (2 * d) + 1 := by
  unfold B
  have h1 : (2 * d + 1 + 1) / 2 = d + 1 := by omega
  have h2 : (2 * d + 1) / 2 = d := by omega
  have h3 : (2 * d) / 2 = d := by omega
  rw [h1, h2, h3]
  omega

/-- **1-Lipschitz Step Bounds for `B` (`B_step_bounds`):**
for every `j : Nat`, `B j ≤ B (j + 1) ∧ B (j + 1) ≤ B j + 1`. -/
theorem B_step_bounds (j : Nat) : B j ≤ B (j + 1) ∧ B (j + 1) ≤ B j + 1 := by
  unfold B
  rcases Nat.mod_two_eq_zero_or_one j with he | ho
  · have h1 : (j + 1 + 1) / 2 = (j + 1) / 2 + 1 := by omega
    have h2 : (j + 1) / 2 = j / 2 := by omega
    rw [h1, h2]
    omega
  · have h1 : (j + 1 + 1) / 2 = (j + 1) / 2 := by omega
    have h2 : (j + 1) / 2 = j / 2 + 1 := by omega
    have hmono := Q_mono 0 (show j / 2 ≤ j / 2 + 1 by omega)
    have hsucc := Q_succ_le 0 (j / 2)
    rw [h1, h2]
    omega

/-- **Global Monotonicity of `B` (`B_mono`):**
for all `i ≤ j`, `B i ≤ B j`. -/
theorem B_mono {i j : Nat} (h : i ≤ j) : B i ≤ B j := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    exact Nat.le_trans (ih (by omega)) (B_step_bounds (i + d)).1

end Rule30RecordCharge
end Ruliology.CellularAutomata
