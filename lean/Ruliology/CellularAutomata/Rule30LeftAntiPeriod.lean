module

public import Ruliology.CellularAutomata.Rule30RightPeriods
public import Ruliology.CellularAutomata.Rule30WhiteSpacing

public import Ruliology.CellularAutomata.Rule30LeftUnbounded

/-!
# Left-Diagonal Anti-Periodicity and Infinitely Many Left Diagonals of Asymptotic Density 1/2

In `Rule30LeftReset`, when `D (j + 1)` is eventually white, `D (j + 2)` shifts by `L` via
`D (j + 2) (t + L) = xor (D (j + 2) t) (par (D j) t L)`. Here we prove that whenever `D j` has
eventual period `L`, the `L`-step XOR parity `par (D j) t L` is eventually constant in `t`. This
yields a sharp global dichotomy: when `D j` is `L`-periodic and `D (j + 1)` is eventually white,
`D (j + 2)` is either `L`-periodic or `L`-anti-periodic (`D (j + 2) (t + L) = ! D (j + 2) t`).

Applied to the first diagonal `D m` (`m ≤ 2^(2*L)`) where period `L` fails
(`Rule30LeftUnbounded.D_period_unbounded`), this proves that for every `L > 0` there is an
eventually `L`-anti-periodic left diagonal `D j` (`j ≤ 2^(2*L)`) with `¬ EvPer (D j) L`. We then
prove that every eventually anti-periodic sequence has exact half-black balance (`L` black cells in
every `2*L` window after the transient) and satisfies the exact asymptotic density-`1/2` condition
of `Rule30Prize.Problem2` (`HalfDensity`), yielding infinitely many left diagonals with asymptotic
black-cell density `1/2` (`D_infinitely_many_halfDensity`).
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30LeftAntiPeriod

open Rule30RightPeriods

open Rule30Jen Rule30Prize Rule30Diagonals Rule30LeftReset Rule30LeftUnbounded

/-! ## Constant parity and the period / anti-period dichotomy -/

/-- Associativity of Boolean `xor`. -/
theorem xor_left_assoc (x y z : Bool) : xor x (xor y z) = xor (xor x y) z := by
  cases x <;> cases y <;> cases z <;> rfl

/-- Shifting the starting time of `par a t n` by `1` step:
`xor (a t) (par a (t + 1) n) = xor (par a t n) (a (t + n))`. -/
theorem par_succ_left (a : Nat → Bool) (t : Nat) :
    ∀ n, xor (a t) (par a (t + 1) n) = xor (par a t n) (a (t + n))
  | 0 => by simp [par]
  | n + 1 => by
    simp only [par]
    rw [xor_left_assoc, par_succ_left a t n, show t + 1 + n = t + (n + 1) by omega]

/-- If `a (t + L) = a t`, then `par a (t + 1) L = par a t L`. -/
theorem par_step_of_periodic {a : Nat → Bool} {t L : Nat} (ha : a (t + L) = a t) :
    par a (t + 1) L = par a t L := by
  have h := par_succ_left a t L
  rw [ha] at h
  revert h
  cases a t <;> cases par a (t + 1) L <;> cases par a t L <;> decide

/-- **Eventual constancy of `par a t L`.** If `a` has period `L` from `s` onward, then
`par a t L = par a s L` for all `t ≥ s`. -/
theorem par_const_of_periodic {a : Nat → Bool} {s L : Nat}
    (ha : ∀ t, s ≤ t → a (t + L) = a t) :
    ∀ t, s ≤ t → par a t L = par a s L := by
  intro t ht
  obtain ⟨k, rfl⟩ : ∃ k, t = s + k := ⟨t - s, by omega⟩
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show s + (k + 1) = (s + k) + 1 by omega, par_step_of_periodic (ha (s + k) (by omega)),
      ih (by omega)]

/-- **Generic period / anti-period dichotomy.** If `x (t + 1) = xor (a t) (b t || x t)`, `a` has
period `L` from `s` onward, and `b` is `false` from `s` onward, then either `x` has period `L` from
`s` onward or `x` is `L`-anti-periodic (`x (t + L) = ! x t`) from `s` onward. -/
theorem white_period_or_antiperiodic {x a b : Nat → Bool} {s L : Nat}
    (hx : ∀ t, x (t + 1) = xor (a t) (b t || x t))
    (ha : ∀ t, s ≤ t → a (t + L) = a t) (hb : ∀ t, s ≤ t → b t = false) :
    (∀ t, s ≤ t → x (t + L) = x t) ∨ (∀ t, s ≤ t → x (t + L) = ! x t) := by
  cases hpar : par a s L
  · left
    intro t ht
    rw [white_shift hx hb t ht, par_const_of_periodic ha t ht, hpar]
    cases x t <;> rfl
  · right
    intro t ht
    rw [white_shift hx hb t ht, par_const_of_periodic ha t ht, hpar]
    cases x t <;> rfl

/-- **Left-diagonal period / anti-period dichotomy.** If `D j` has period `L` from `s` onward and
`D (j + 1)` is white from `s` onward, then `D (j + 2)` is either `L`-periodic or `L`-anti-periodic
from `s` onward. -/
theorem D_period_or_antiperiodic {j s L : Nat}
    (ha : ∀ t, s ≤ t → D j (t + L) = D j t) (hb : ∀ t, s ≤ t → D (j + 1) t = false) :
    (∀ t, s ≤ t → D (j + 2) (t + L) = D (j + 2) t) ∨
      (∀ t, s ≤ t → D (j + 2) (t + L) = ! D (j + 2) t) :=
  white_period_or_antiperiodic (D_step j) ha hb

/-- Eventual `L`-anti-periodicity of a sequence `f : Nat → Bool`. -/
def EvAntiPer (f : Nat → Bool) (L : Nat) : Prop := ∃ T, ∀ t, T ≤ t → f (t + L) = ! f t

/-- Every eventually `L`-anti-periodic sequence has eventual period `2 * L`. -/
theorem EvAntiPer.evPer_two {f : Nat → Bool} {L : Nat} (h : EvAntiPer f L) : EvPer f (2 * L) := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T, fun t ht => ?_⟩
  rw [Nat.two_mul, ← Nat.add_assoc, hT (t + L) (by omega), hT t ht, Bool.not_not]

/-- An eventually `L`-anti-periodic sequence cannot be eventually `L`-periodic. -/
theorem EvAntiPer.not_evPer {f : Nat → Bool} {L : Nat} (h : EvAntiPer f L) : ¬ EvPer f L := by
  rintro ⟨T₁, hper⟩
  obtain ⟨T₂, hanti⟩ := h
  let t := max T₁ T₂
  have e1 := hper t (Nat.le_max_left T₁ T₂)
  have e2 := hanti t (Nat.le_max_right T₁ T₂)
  rw [e1] at e2
  revert e2
  cases f t <;> decide

/-- If `D j` and `D (j + 1)` are eventually `L`-periodic while `D (j + 2)` is not, then `D (j + 1)`
is eventually white and `D (j + 2)` is eventually `L`-anti-periodic. -/
theorem D_evAntiPer_of_not_evPer {j L : Nat}
    (h1 : EvPer (D j) L) (h2 : EvPer (D (j + 1)) L) (hnot : ¬ EvPer (D (j + 2)) L) :
    EvWhite (D (j + 1)) ∧ EvAntiPer (D (j + 2)) L := by
  rcases D_evper_or_evwhite h1 h2 with hper | hw
  · exact absurd hper hnot
  · refine ⟨hw, ?_⟩
    obtain ⟨T1, hT1⟩ := h1
    obtain ⟨T2, hT2⟩ := hw
    rcases D_period_or_antiperiodic (s := max T1 T2)
      (fun t ht => hT1 t (by omega)) (fun t ht => hT2 t (by omega)) with hper | hanti
    · exact absurd ⟨max T1 T2, hper⟩ hnot
    · exact ⟨max T1 T2, hanti⟩

/-- Helper: if a predicate `P` holds at `0` and `1` but fails at some `m ≤ B`, there exists `j`
with `j + 2 ≤ B` such that `P j`, `P (j + 1)`, and `¬ P (j + 2)`. -/
theorem exists_step_break {P : Nat → Prop} (h0 : P 0) (h1 : P 1) :
    ∀ {m : Nat}, ¬ P m → ∃ j, j + 2 ≤ m ∧ P j ∧ P (j + 1) ∧ ¬ P (j + 2)
  | 0, hm => absurd h0 hm
  | 1, hm => absurd h1 hm
  | m + 2, hm => by
    by_cases h : P (m + 1)
    · by_cases h' : P m
      · exact ⟨m, Nat.le_refl _, h', h, hm⟩
      · obtain ⟨j, hj, hp0, hp1, hnp2⟩ := exists_step_break h0 h1 h'
        exact ⟨j, by omega, hp0, hp1, hnp2⟩
    · obtain ⟨j, hj, hp0, hp1, hnp2⟩ := exists_step_break h0 h1 h
      exact ⟨j, by omega, hp0, hp1, hnp2⟩

/-- **Unbounded `L`-anti-periodic left diagonals.** For every `L > 0`, there exists a left diagonal
`D j` (`j ≤ 2 ^ (2 * L)`) that is eventually `L`-anti-periodic (`EvAntiPer (D j) L`) and not
eventually `L`-periodic (`¬ EvPer (D j) L`). -/
theorem D_antiperiodic_unbounded (L : Nat) (hL : 0 < L) :
    ∃ j ≤ 2 ^ (2 * L), EvAntiPer (D j) L ∧ ¬ EvPer (D j) L := by
  obtain ⟨m, hm, hnot⟩ := D_period_unbounded L hL
  obtain ⟨j, hj, hp0, hp1, hnp2⟩ :=
    exists_step_break (P := fun i => EvPer (D i) L) (D_zero_evper L) (D_one_evper L) hnot
  obtain ⟨_, hanti⟩ := D_evAntiPer_of_not_evPer hp0 hp1 hnp2
  exact ⟨j + 2, by omega, hanti, hnp2⟩

/-! ## Exact period-`2L` balance and `Problem2` asymptotic density `1/2` -/

/-- The number of black cells (`true` values) of `f` among `0, …, n - 1` (matching
`Rule30Prize.blackCount` when `f = center`). -/
def blackCountFor (f : Nat → Bool) (n : Nat) : Nat := ((List.range n).filter f).length

/-- `blackCountFor center` is definitionally equal to `Rule30Prize.blackCount`. -/
theorem blackCountFor_center (n : Nat) : blackCountFor center n = blackCount n := rfl

/-- The asymptotic density-`1/2` property of `Rule30Prize.Problem2` for a general sequence `f`. -/
def HalfDensity (f : Nat → Bool) : Prop :=
  ∀ k : Nat, 0 < k → ∃ N, ∀ n, N ≤ n → k * (2 * (blackCountFor f n : Int) - n).natAbs ≤ n

/-- `HalfDensity center` is identical to `Rule30Prize.Problem2`. -/
theorem halfDensity_center_iff : HalfDensity center ↔ Problem2 := Iff.rfl

/-- Step equation for `blackCountFor f (n + 1)`. -/
theorem blackCountFor_succ (f : Nat → Bool) (n : Nat) :
    blackCountFor f (n + 1) = blackCountFor f n + (if f n then 1 else 0) := by
  unfold blackCountFor
  rw [List.range_succ, List.filter_append, List.length_append]
  cases hfn : f n <;> simp [List.filter, hfn]

/-- `blackCountFor f (t + d)` is bounded between `blackCountFor f t` and `blackCountFor f t + d`. -/
theorem blackCountFor_add_bounds (f : Nat → Bool) (t : Nat) :
    ∀ d, blackCountFor f t ≤ blackCountFor f (t + d) ∧
      blackCountFor f (t + d) ≤ blackCountFor f t + d
  | 0 => ⟨Nat.le_refl _, Nat.le_refl _⟩
  | d + 1 => by
    obtain ⟨h1, h2⟩ := blackCountFor_add_bounds f t d
    rw [show t + (d + 1) = (t + d) + 1 by omega, blackCountFor_succ]
    cases f (t + d) <;> simp <;> omega

/-- The number of `true` values of `f` on the window `[t, t + n)`. -/
def winCount (f : Nat → Bool) (t : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => winCount f t n + (if f (t + n) then 1 else 0)

/-- `blackCountFor f (t + n) = blackCountFor f t + winCount f t n`. -/
theorem blackCountFor_add_eq_winCount (f : Nat → Bool) (t : Nat) :
    ∀ n, blackCountFor f (t + n) = blackCountFor f t + winCount f t n
  | 0 => by simp [winCount]
  | n + 1 => by
    rw [show t + (n + 1) = (t + n) + 1 by omega, blackCountFor_succ,
      blackCountFor_add_eq_winCount f t n, winCount]
    omega

/-- If `f (t + r + L) = ! f (t + r)` for all `r < n`, then the window counts on `[t, t + n)` and
`[t + L, t + L + n)` sum to `n`. -/
theorem winCount_add_complement {f : Nat → Bool} {t L : Nat} :
    ∀ n, (∀ r, r < n → f (t + L + r) = ! f (t + r)) →
      winCount f t n + winCount f (t + L) n = n
  | 0, _ => rfl
  | n + 1, hcomp => by
    simp only [winCount]
    have ih := winCount_add_complement n (fun r hr => hcomp r (by omega))
    have hn := hcomp n (Nat.lt_succ_self n)
    rw [hn]
    cases f (t + n) <;> simp <;> omega

/-- **Exact period-`2L` balance of an `L`-anti-periodic sequence.** If `f (t + L) = ! f t` for all
`t ≥ T`, then every window of length `2 * L` starting at `t ≥ T` contains *exactly* `L` black
cells: `blackCountFor f (t + 2 * L) = blackCountFor f t + L`. -/
theorem blackCountFor_add_two_mul_of_antiperiodic {f : Nat → Bool} {T L : Nat}
    (hanti : ∀ t, T ≤ t → f (t + L) = ! f t) :
    ∀ t, T ≤ t → blackCountFor f (t + 2 * L) = blackCountFor f t + L := by
  intro t ht
  rw [Nat.two_mul, ← Nat.add_assoc, blackCountFor_add_eq_winCount f (t + L) L,
    blackCountFor_add_eq_winCount f t L, Nat.add_assoc]
  have hsum : winCount f t L + winCount f (t + L) L = L := by
    refine winCount_add_complement L fun r _ => ?_
    rw [show t + L + r = (t + r) + L by omega]
    exact hanti (t + r) (by omega)
  omega

/-- Iterating `q` blocks of length `2 * L` from `T` adds `q * L` black cells. -/
theorem blackCountFor_add_mul_two_mul_of_antiperiodic {f : Nat → Bool} {T L : Nat}
    (hanti : ∀ t, T ≤ t → f (t + L) = ! f t) :
    ∀ q, blackCountFor f (T + q * (2 * L)) = blackCountFor f T + q * L
  | 0 => by simp
  | q + 1 => by
    rw [show T + (q + 1) * (2 * L) = (T + q * (2 * L)) + 2 * L by rw [Nat.succ_mul]; omega,
      blackCountFor_add_two_mul_of_antiperiodic hanti (T + q * (2 * L)) (by omega),
      blackCountFor_add_mul_two_mul_of_antiperiodic hanti q, Nat.succ_mul]
    omega

/-- **Bounded discrepancy of anti-periodic sequences.** If `L > 0` and `f (t + L) = ! f t` for all
`t ≥ T`, then `|2 * blackCountFor f n - n| ≤ T + 2 * L` for all `n ≥ T`. -/
theorem natAbs_discrepancy_le_of_antiperiodic {f : Nat → Bool} {T L : Nat} (hL : 0 < L)
    (hanti : ∀ t, T ≤ t → f (t + L) = ! f t) {n : Nat} (hn : T ≤ n) :
    (2 * (blackCountFor f n : Int) - n).natAbs ≤ T + 2 * L := by
  let q := (n - T) / (2 * L)
  let r := (n - T) % (2 * L)
  have h2L : 0 < 2 * L := by omega
  have hr : r < 2 * L := Nat.mod_lt (n - T) h2L
  have hdiv : q * (2 * L) + r = n - T := by
    have h := Nat.div_add_mod (n - T) (2 * L)
    rw [Nat.mul_comm] at h
    exact h
  have hq2 : q * (2 * L) = 2 * (q * L) := by rw [Nat.mul_left_comm, Nat.mul_comm q L]
  have hn_eq : n = T + q * (2 * L) + r := by omega
  have hbase := blackCountFor_add_mul_two_mul_of_antiperiodic hanti q
  obtain ⟨hb1, hb2⟩ := blackCountFor_add_bounds f (T + q * (2 * L)) r
  rw [← hn_eq] at hb1 hb2
  rw [hbase] at hb1 hb2
  obtain ⟨hT1, hT2⟩ := blackCountFor_add_bounds f 0 T
  have h0 : blackCountFor f 0 = 0 := rfl
  rw [h0, Nat.zero_add] at hT1 hT2
  omega

/-- **Every eventually anti-periodic sequence has asymptotic density `1/2` (`HalfDensity`).** -/
theorem halfDensity_of_antiperiodic {f : Nat → Bool} {L : Nat} (hL : 0 < L)
    (hanti : EvAntiPer f L) : HalfDensity f := by
  obtain ⟨T, hT⟩ := hanti
  intro k hk
  refine ⟨k * (T + 2 * L) + T, fun n hn => ?_⟩
  have hdisc := natAbs_discrepancy_le_of_antiperiodic hL hT (n := n) (by omega)
  have hmul : k * (2 * (blackCountFor f n : Int) - n).natAbs ≤ k * (T + 2 * L) :=
    Nat.mul_le_mul_left k hdisc
  omega

/-- **Unbounded asymptotic density-`1/2` left diagonals (`D_halfDensity_unbounded`).** For every
`L > 0`, there exists a left diagonal `D j` (`j ≤ 2 ^ (2 * L)`) with `¬ EvPer (D j) L` that is
eventually `L`-anti-periodic and satisfies the exact `Problem2` asymptotic density-`1/2` law
`HalfDensity (D j)`. -/
theorem D_halfDensity_unbounded (L : Nat) (hL : 0 < L) :
    ∃ j ≤ 2 ^ (2 * L), EvAntiPer (D j) L ∧ ¬ EvPer (D j) L ∧ HalfDensity (D j) := by
  obtain ⟨j, hj, hanti, hnot⟩ := D_antiperiodic_unbounded L hL
  exact ⟨j, hj, hanti, hnot, halfDensity_of_antiperiodic hL hanti⟩

/-- **Universal `whiteCount` period / anti-period dichotomy.** For every `j : Nat`, either
`D (j + 2)` already has eventual period `2 ^ whiteCount j`, or `D (j + 1)` is eventually white,
`D (j + 2)` is eventually `2 ^ whiteCount j`-anti-periodic, and `HalfDensity (D (j + 2))` holds. -/
theorem D_evPer_or_evAntiPer_pow_whiteCount (j : Nat) :
    EvPer (D (j + 2)) (2 ^ whiteCount j) ∨
      (EvWhite (D (j + 1)) ∧ EvAntiPer (D (j + 2)) (2 ^ whiteCount j) ∧
        HalfDensity (D (j + 2))) := by
  by_cases hper : EvPer (D (j + 2)) (2 ^ whiteCount j)
  · exact Or.inl hper
  · obtain ⟨h1, h2⟩ := D_evper_pow_whiteCount_pair j
    obtain ⟨hw, hanti⟩ := D_evAntiPer_of_not_evPer h1 h2 hper
    exact Or.inr ⟨hw, hanti, halfDensity_of_antiperiodic (Nat.two_pow_pos _) hanti⟩

/-- Monotonicity of `whiteCount`. -/
theorem whiteCount_mono {i k : Nat} (hik : i ≤ k) : whiteCount i ≤ whiteCount k := by
  induction k with
  | zero =>
    have : i = 0 := by omega
    subst this; exact Nat.le_refl _
  | succ k ih =>
    rcases Nat.lt_or_ge i (k + 1) with hlt | hge
    · have := ih (by omega)
      simp only [whiteCount]
      omega
    · have : i = k + 1 := by omega
      subst this; exact Nat.le_refl _

/-- **Infinitely many left diagonals have asymptotic density `1/2` (`D_infinitely_many_halfDensity`).**
Complementing `Rule30LeftUnbounded.D_infinitely_many_white` (density `0`) and
`Rule30LeftUnbounded.D_infinitely_many_black` (density `1`), for every `N : Nat` there exists a
left diagonal `D j` with `j > N` and `k : Nat` such that `D j` is eventually `2^k`-anti-periodic,
not eventually `2^k`-periodic, and satisfies `HalfDensity (D j)`. -/
theorem D_infinitely_many_halfDensity (N : Nat) :
    ∃ j > N, ∃ k : Nat, EvAntiPer (D j) (2 ^ k) ∧ ¬ EvPer (D j) (2 ^ k) ∧ HalfDensity (D j) := by
  let k := whiteCount (N + 1)
  obtain ⟨j, _, hanti, hnot, hhalf⟩ := D_halfDensity_unbounded (2 ^ k) (Nat.two_pow_pos k)
  refine ⟨j, ?_, k, hanti, hnot, hhalf⟩
  refine Classical.byContradiction fun hle => ?_
  have hjN : j ≤ N + 1 := by omega
  have hmono : whiteCount j ≤ k := whiteCount_mono hjN
  have hdvd : 2 ^ whiteCount j ∣ 2 ^ k := Nat.pow_dvd_pow 2 hmono
  exact hnot (EvPer.of_dvd (D_evper_pow_whiteCount j) hdvd)

/-! ## 4. Backward period descent and two-diagonal period bound -/

/-- Left-permutive backward step for left diagonals:
`D j t = xor (D (j + 2) (t + 1)) (D (j + 1) t || D (j + 2) t)`. -/
theorem D_back (j t : Nat) :
    D j t = xor (D (j + 2) (t + 1)) (D (j + 1) t || D (j + 2) t) := by
  rw [D_step j t]
  cases D j t <;> cases (D (j + 1) t || D (j + 2) t) <;> rfl

/-- If `D (j + 1)` and `D (j + 2)` have period `Q` from `s` onward, then `D j` has period `Q` from
`s` onward. -/
theorem D_per_down {j s Q : Nat}
    (h1 : ∀ t, s ≤ t → D (j + 1) (t + Q) = D (j + 1) t)
    (h2 : ∀ t, s ≤ t → D (j + 2) (t + Q) = D (j + 2) t) :
    ∀ t, s ≤ t → D j (t + Q) = D j t := by
  intro t ht
  rw [D_back j (t + Q), D_back j t, show t + Q + 1 = (t + 1) + Q by omega,
    h2 (t + 1) (by omega), h1 t ht, h2 t ht]

/-- If `D m` and `D (m + 1)` have period `Q` from `s` onward, then every `D i` (`i ≤ m + 1`) has
period `Q` from `s` onward. -/
theorem D_per_down_all {s Q : Nat} :
    ∀ {m : Nat}, (∀ t, s ≤ t → D m (t + Q) = D m t) →
      (∀ t, s ≤ t → D (m + 1) (t + Q) = D (m + 1) t) →
      ∀ i, i ≤ m + 1 → ∀ t, s ≤ t → D i (t + Q) = D i t
  | 0, h0, h1, i, hi => by
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · exact h0
    · exact h1
  | m + 1, hm1, hm2, i, hi => by
    rcases (show i ≤ m + 1 ∨ i = m + 2 by omega) with hle | rfl
    · exact D_per_down_all (D_per_down hm1 hm2) hm1 i hle
    · exact hm2

/-- **Two-diagonal eventual periodicity descent (`D_evPer_pair_iff_all`).** `D m` and `D (m + 1)`
both have eventual period `Q` iff every `D i` (`i ≤ m + 1`) has eventual period `Q`. -/
theorem D_evPer_pair_iff_all (m Q : Nat) :
    (EvPer (D m) Q ∧ EvPer (D (m + 1)) Q) ↔ ∀ i, i ≤ m + 1 → EvPer (D i) Q := by
  constructor
  · rintro ⟨⟨T1, h1⟩, ⟨T2, h2⟩⟩ i hi
    refine ⟨max T1 T2, D_per_down_all (s := max T1 T2)
      (fun t ht => h1 t (by omega)) (fun t ht => h2 t (by omega)) i hi⟩
  · intro hall
    exact ⟨hall m (by omega), hall (m + 1) (by omega)⟩

/-- **Two-diagonal period bound (`D_pair_period_bound`).** Strengthening
`Rule30LeftUnbounded.D_common_period_bound`, if `0 < Q` and the two consecutive diagonals `D m` and
`D (m + 1)` have eventual period `Q`, then `m + 3 ≤ 2 ^ (2 * Q)`. -/
theorem D_pair_period_bound {m Q : Nat} (hQ : 0 < Q)
    (hm : EvPer (D m) Q) (hm1 : EvPer (D (m + 1)) Q) : m + 3 ≤ 2 ^ (2 * Q) :=
  D_common_period_bound hQ ((D_evPer_pair_iff_all m Q).mp ⟨hm, hm1⟩)

/-- **White-diagonal period bound (`D_white_period_bound`).** If `D (m + 1)` is eventually white and
`D m` has eventual period `Q` (`0 < Q`), then `m + 3 ≤ 2 ^ (2 * Q)`. -/
theorem D_white_period_bound {m Q : Nat} (hQ : 0 < Q)
    (hw : EvWhite (D (m + 1))) (hm : EvPer (D m) Q) : m + 3 ≤ 2 ^ (2 * Q) := by
  obtain ⟨T, hT⟩ := hw
  refine D_pair_period_bound hQ hm ⟨T, fun t ht => ?_⟩
  rw [hT (t + Q) (by omega), hT t ht]

/-! ## 5. The white-diagonal neighborhood and twin anti-periodic diagonals -/

/-- **Two steps before a white diagonal (`D_white_prev_two`).** If `D (j + 3)` is white from `s`
onward, then `D j t = xor (D (j + 2) t) (D (j + 2) (t + 1))` for all `t ≥ s`. -/
theorem D_white_prev_two {j s : Nat} (hw : ∀ t, s ≤ t → D (j + 3) t = false) :
    ∀ t, s ≤ t → D j t = xor (D (j + 2) t) (D (j + 2) (t + 1)) := by
  intro t ht
  have heq := D_white_of_eq (j := j + 1) hw t ht
  rw [D_back j t, heq]
  cases D (j + 2) t <;> cases D (j + 2) (t + 1) <;> rfl

/-- **Three steps before a white diagonal (`D_white_prev_three`).** If `D (j + 4)` is white from `s`
onward, then `D j t = (D (j + 3) t && ! D (j + 3) (t + 1))` and `D j` is `11`-free from `s` onward. -/
theorem D_white_prev_three {j s : Nat} (hw : ∀ t, s ≤ t → D (j + 4) t = false) :
    ∀ t, s ≤ t →
      D j t = (D (j + 3) t && ! D (j + 3) (t + 1)) ∧ (D j t && D j (t + 1)) = false := by
  intro t ht
  have h1 : ∀ u, s ≤ u → D (j + 2) u = D (j + 3) u := D_white_of_eq (j := j + 2) hw
  have h2 : ∀ u, s ≤ u → D (j + 1) u = xor (D (j + 3) u) (D (j + 3) (u + 1)) :=
    D_white_prev_two (j := j + 1) hw
  have h0 : ∀ u, s ≤ u → D j u = (D (j + 3) u && ! D (j + 3) (u + 1)) := by
    intro u hu
    rw [D_back j u, h1 (u + 1) (by omega), h1 u hu, h2 u hu]
    cases D (j + 3) u <;> cases D (j + 3) (u + 1) <;> rfl
  refine ⟨h0 t ht, ?_⟩
  rw [h0 t ht, h0 (t + 1) (by omega)]
  cases D (j + 3) t <;> cases D (j + 3) (t + 1) <;> cases D (j + 3) (t + 1 + 1) <;> rfl

/-- **Post-white complement law (`D_post_white_complement`).** Whenever `D (j + 1)` is eventually
white, `D (j + 3)` is eventually black and `D (j + 4)` is eventually the 1-step shifted bitwise
complement of `D (j + 2)`: `D (j + 4) (t + 1) = ! D (j + 2) t`. -/
theorem D_post_white_complement {j : Nat} (hw : EvWhite (D (j + 1))) :
    ∃ T, ∀ t, T ≤ t → D (j + 3) t = true ∧ D (j + 4) (t + 1) = ! D (j + 2) t := by
  obtain ⟨T, hT⟩ := D_black_after_white hw
  refine ⟨T, fun t ht => ⟨hT t ht, ?_⟩⟩
  have hstep := D_step (j + 2) t
  rw [show j + 2 + 1 = j + 3 by omega, show j + 2 + 2 = j + 4 by omega, hT t ht] at hstep
  rw [hstep]
  cases D (j + 2) t <;> rfl

/-- **Post-white gated inhibition and `11`-freeness (`D_post_white_no11`).** Whenever `D (j + 1)` is
eventually white, `D (j + 5)` eventually satisfies
`D (j + 5) (t + 1) = (! D (j + 4) t && ! D (j + 5) t)` and is `11`-free
(`(D (j + 5) t && D (j + 5) (t + 1)) = false`). -/
theorem D_post_white_no11 {j : Nat} (hw : EvWhite (D (j + 1))) :
    ∃ T, ∀ t, T ≤ t →
      D (j + 5) (t + 1) = (! D (j + 4) t && ! D (j + 5) t) ∧
      (D (j + 5) t && D (j + 5) (t + 1)) = false := by
  obtain ⟨T, hT⟩ := D_black_after_white hw
  refine ⟨T, fun t ht => ?_⟩
  have hstep := D_step (j + 3) t
  rw [show j + 3 + 1 = j + 4 by omega, show j + 3 + 2 = j + 5 by omega, (hT t ht)] at hstep
  have h1 : D (j + 5) (t + 1) = (! D (j + 4) t && ! D (j + 5) t) := by
    rw [hstep]
    cases D (j + 4) t <;> cases D (j + 5) t <;> rfl
  refine ⟨h1, ?_⟩
  rw [h1]
  cases D (j + 5) t <;> cases D (j + 4) t <;> rfl

/-- If `f` is `L`-anti-periodic and `g (t + 1) = ! f t` from `T` onward, then `g` is also
`L`-anti-periodic. -/
theorem evAntiPer_of_succ_eq_not {f g : Nat → Bool} {L : Nat}
    (hf : EvAntiPer f L) (hfg : ∃ T, ∀ t, T ≤ t → g (t + 1) = ! f t) : EvAntiPer g L := by
  obtain ⟨T1, h1⟩ := hf
  obtain ⟨T2, h2⟩ := hfg
  refine ⟨max T1 T2 + 1, fun t ht => ?_⟩
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  rw [show s + 1 + L = (s + L) + 1 by omega, h2 (s + L) (by omega), h2 s (by omega),
    h1 s (by omega)]

/-- **Twin anti-periodic and density-`1/2` diagonals (`D_twin_antiperiodic_of_not_evPer`).** If
`D j` and `D (j + 1)` have eventual period `L` (`0 < L`) while `D (j + 2)` does not, then both
`D (j + 2)` and `D (j + 4)` are eventually `L`-anti-periodic, fail period `L`, and satisfy
`HalfDensity`. -/
theorem D_twin_antiperiodic_of_not_evPer {j L : Nat} (hL : 0 < L)
    (h1 : EvPer (D j) L) (h2 : EvPer (D (j + 1)) L) (hnot : ¬ EvPer (D (j + 2)) L) :
    EvWhite (D (j + 1)) ∧
      EvAntiPer (D (j + 2)) L ∧ HalfDensity (D (j + 2)) ∧
      EvAntiPer (D (j + 4)) L ∧ ¬ EvPer (D (j + 4)) L ∧ HalfDensity (D (j + 4)) := by
  obtain ⟨hw, hanti2⟩ := D_evAntiPer_of_not_evPer h1 h2 hnot
  obtain ⟨T, hT⟩ := D_post_white_complement hw
  have hanti4 : EvAntiPer (D (j + 4)) L :=
    evAntiPer_of_succ_eq_not hanti2 ⟨T, fun t ht => (hT t ht).2⟩
  exact ⟨hw, hanti2, halfDensity_of_antiperiodic hL hanti2,
    hanti4, hanti4.not_evPer, halfDensity_of_antiperiodic hL hanti4⟩

/-! ## 6. Period bounds via `Rule30WhiteSpacing` and right-diagonal density `1/2` -/

/-- **Universal `(j + 3) / 5` power-of-two period bound for left diagonals (`D_evPer_pow_div_five`).**
By `Rule30WhiteSpacing.whiteCount_bound_five` (`5 * whiteCount j ≤ j + 3`), every left diagonal
`D j` has eventual period `2 ^ ((j + 3) / 5)`. -/
theorem D_evPer_pow_div_five (j : Nat) : EvPer (D j) (2 ^ ((j + 3) / 5)) := by
  have h5 := Rule30WhiteSpacing.whiteCount_bound_five j
  exact EvPer.of_dvd (D_evper_pow_whiteCount j) (Nat.pow_dvd_pow 2 (by omega))

/-- **Universal `(j + 5) / 6` power-of-two period bound for left diagonals (`D_evPer_pow_div_six`).**
By `Rule30WhiteSpacing.whiteCount_bound` (`6 * whiteCount j ≤ j + 5`), every left diagonal `D j`
has eventual period `2 ^ ((j + 5) / 6)`. -/
theorem D_evPer_pow_div_six (j : Nat) : EvPer (D j) (2 ^ ((j + 5) / 6)) := by
  have h6 := Rule30WhiteSpacing.whiteCount_bound j
  exact EvPer.of_dvd (D_evper_pow_whiteCount j) (Nat.pow_dvd_pow 2 (by omega))

/-- **Infinitely many right diagonals have asymptotic density `1/2` (`R_infinitely_many_halfDensity`).**
For every `k : Nat`, there exists a right diagonal `R j` (`k < j ≤ 2 ^ (k + 1) - 1`) that is
`2 ^ k`-anti-periodic from `t = 0` (`∀ t, R j (t + 2 ^ k) = ! R j t`), not `2 ^ k`-periodic, and
satisfies `HalfDensity (R j)`. -/
theorem R_infinitely_many_halfDensity (k : Nat) :
    ∃ j, k < j ∧ j ≤ 2 ^ (k + 1) - 1 ∧
      (∀ t, R j (t + 2 ^ k) = ! R j t) ∧ ¬ Per j (2 ^ k) ∧ HalfDensity (R j) := by
  obtain ⟨J, hJ, hJ1, hkJ⟩ := exists_last k
  have hJb : J ≤ 2 ^ (k + 1) - 2 := per_bound hJ
  have hanti : ∀ t, R (J + 1) (t + 2 ^ k) = ! R (J + 1) t :=
    antiperiod hJ hJ1
  have hpos : 0 < 2 ^ (k + 1) := Nat.two_pow_pos (k + 1)
  exact ⟨J + 1, by omega, by omega, hanti, hJ1,
    halfDensity_of_antiperiodic (Nat.two_pow_pos k) ⟨0, fun t _ => hanti t⟩⟩

/-! ## 7. Twin-Diagonal Conservation, `HalfDensity` Invariance, and Right-Diagonal `leastExp` Balance -/

/-- **Shifted-Complement Window Conservation (`winCount_add_of_succ_eq_not`):** if
`g (t + 1) = !f t` for all `t ≥ T`, then on every window of length `d` starting at `t ≥ T`,
`winCount f t d + winCount g (t + 1) d = d`. -/
theorem winCount_add_of_succ_eq_not {f g : Nat → Bool} {T : Nat}
    (hfg : ∀ t, T ≤ t → g (t + 1) = !f t) {t : Nat} (ht : T ≤ t) :
    ∀ d, winCount f t d + winCount g (t + 1) d = d
  | 0 => rfl
  | d + 1 => by
    simp only [winCount]
    have ih := winCount_add_of_succ_eq_not hfg ht d
    have hstep := hfg (t + d) (by omega)
    rw [show t + 1 + d = (t + d) + 1 by omega, hstep]
    cases f (t + d) <;> simp <;> omega

/-- **Cumulative Twin Discrepancy Cancellation (`blackCountFor_twin_conservation`):** if
`g (t + 1) = !f t` for all `t ≥ T`, then for every `n ≥ T`,
`((2 * (blackCountFor f n : Int) - (n : Int)) + (2 * (blackCountFor g (n + 1) : Int) - ((n + 1 : Nat) : Int))).natAbs ≤ 2 * T + 3`. -/
theorem blackCountFor_twin_conservation {f g : Nat → Bool} {T : Nat}
    (hfg : ∀ t, T ≤ t → g (t + 1) = !f t) {n : Nat} (hn : T ≤ n) :
    ((2 * (blackCountFor f n : Int) - (n : Int)) +
      (2 * (blackCountFor g (n + 1) : Int) - ((n + 1 : Nat) : Int))).natAbs ≤ 2 * T + 3 := by
  let d := n - T
  have hn_eq : n = T + d := by omega
  have hn1_eq : n + 1 = (T + 1) + d := by omega
  have hf := blackCountFor_add_eq_winCount f T d
  have hg := blackCountFor_add_eq_winCount g (T + 1) d
  have hwin := winCount_add_of_succ_eq_not hfg (Nat.le_refl T) d
  rw [← hn_eq] at hf
  rw [← hn1_eq] at hg
  obtain ⟨hf0, hfT⟩ := blackCountFor_add_bounds f 0 T
  obtain ⟨hg0, hgT⟩ := blackCountFor_add_bounds g 0 (T + 1)
  have hbz1 : blackCountFor f 0 = 0 := rfl
  have hbz2 : blackCountFor g 0 = 0 := rfl
  rw [hbz1, Nat.zero_add] at hf0 hfT
  rw [hbz2, Nat.zero_add] at hg0 hgT
  omega

/-- **Forward `HalfDensity` Transfer under Shifted Complementation (`halfDensity_of_succ_eq_not`):**
if `g (t + 1) = !f t` for all `t ≥ T` and `HalfDensity f` holds, then `HalfDensity g` holds. -/
theorem halfDensity_of_succ_eq_not {f g : Nat → Bool} {T : Nat}
    (hfg : ∀ t, T ≤ t → g (t + 1) = !f t) (hf : HalfDensity f) : HalfDensity g := by
  intro k hk
  obtain ⟨N, hN⟩ := hf (2 * k) (by omega)
  refine ⟨max (N + 1) (2 * (k * (2 * T + 3)) + T + 1), fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hmN : N ≤ m := by omega
  have hmT : T ≤ m := by omega
  have h1 := hN m hmN
  have h2 := blackCountFor_twin_conservation hfg hmT
  have htri : (2 * (blackCountFor g (m + 1) : Int) - ((m + 1 : Nat) : Int)).natAbs ≤
      (2 * (blackCountFor f m : Int) - (m : Int)).natAbs + (2 * T + 3) := by omega
  have hmul := Nat.mul_le_mul_left k htri
  rw [Nat.left_distrib] at hmul
  rw [Nat.mul_assoc] at h1
  omega

/-- **Bidirectional `HalfDensity` Invariance under Shifted Complementation (`halfDensity_iff_of_succ_eq_not`):**
if `g (t + 1) = !f t` for all `t ≥ T`, then `HalfDensity f ↔ HalfDensity g`. -/
theorem halfDensity_iff_of_succ_eq_not {f g : Nat → Bool} {T : Nat}
    (hfg : ∀ t, T ≤ t → g (t + 1) = !f t) :
    HalfDensity f ↔ HalfDensity g := by
  constructor
  · exact halfDensity_of_succ_eq_not hfg
  · intro hg k hk
    obtain ⟨N, hN⟩ := hg (2 * k) (by omega)
    refine ⟨max N (2 * (k * (2 * T + 3)) + T + 1), fun n hn => ?_⟩
    have hn1 : N ≤ n + 1 := by omega
    have hnT : T ≤ n := by omega
    have h1 := hN (n + 1) hn1
    have h2 := blackCountFor_twin_conservation hfg hnT
    have htri : (2 * (blackCountFor f n : Int) - (n : Int)).natAbs ≤
        (2 * (blackCountFor g (n + 1) : Int) - ((n + 1 : Nat) : Int)).natAbs + (2 * T + 3) := by omega
    have hmul := Nat.mul_le_mul_left k htri
    rw [Nat.left_distrib] at hmul
    rw [Nat.mul_assoc] at h1
    omega

/-- **Post-White Twin-Diagonal Window Conservation (`D_post_white_twin_winCount_sum`):** around
every eventually white left diagonal `EvWhite (D (j + 1))`, there is a transient `T` such that for
all `t ≥ T` and `d : Nat`, `winCount (D (j + 2)) t d + winCount (D (j + 4)) (t + 1) d = d`. -/
theorem D_post_white_twin_winCount_sum {j : Nat} (hw : EvWhite (D (j + 1))) :
    ∃ T, ∀ t, T ≤ t → ∀ d, winCount (D (j + 2)) t d + winCount (D (j + 4)) (t + 1) d = d := by
  obtain ⟨T, hT⟩ := D_post_white_complement hw
  exact ⟨T, fun t ht d => winCount_add_of_succ_eq_not (fun s hs => (hT s hs).2) ht d⟩

/-- **Post-White Twin-Diagonal `HalfDensity` Equivalence (`D_post_white_halfDensity_iff`):** around
every eventually white left diagonal `EvWhite (D (j + 1))`, `D (j + 2)` has asymptotic density
`1/2` (`HalfDensity (D (j + 2))`) if and only if `D (j + 4)` has asymptotic density `1/2`
(`HalfDensity (D (j + 4))`). -/
theorem D_post_white_halfDensity_iff {j : Nat} (hw : EvWhite (D (j + 1))) :
    HalfDensity (D (j + 2)) ↔ HalfDensity (D (j + 4)) := by
  obtain ⟨T, hT⟩ := D_post_white_complement hw
  exact halfDensity_iff_of_succ_eq_not (fun t ht => (hT t ht).2)

/-- Time-interleaved multiplex of two Boolean trajectories `f` and `g`:
`interleave f g (2 * s) = f s` and `interleave f g (2 * s + 1) = g s`. -/
def interleave (f g : Nat → Bool) (t : Nat) : Bool :=
  if t % 2 = 0 then f (t / 2) else g (t / 2)

/-- **Exact Pairwise Balance of the Interleaved Multiplex (`winCount_interleave_two_mul`):** if
`g (s + 1) = !f s` for all `s ≥ T`, then for all `s ≥ T` and `d : Nat`, the interleaved sequence
`interleave f (fun u => g (u + 1))` contains exactly `d` black cells in `[2 * s, 2 * s + 2 * d)`. -/
theorem winCount_interleave_two_mul {f g : Nat → Bool} {T : Nat}
    (hfg : ∀ s, T ≤ s → g (s + 1) = !f s) {s : Nat} (hs : T ≤ s) :
    ∀ d, winCount (interleave f (fun u => g (u + 1))) (2 * s) (2 * d) = d
  | 0 => rfl
  | d + 1 => by
    rw [show 2 * (d + 1) = 2 * d + 1 + 1 by omega]
    simp only [winCount]
    rw [winCount_interleave_two_mul hfg hs d]
    have hev : interleave f (fun u => g (u + 1)) (2 * s + 2 * d) = f (s + d) := by
      unfold interleave
      rw [ite_eq_left (by omega), show (2 * s + 2 * d) / 2 = s + d by omega]
    have hod : interleave f (fun u => g (u + 1)) (2 * s + (2 * d + 1)) = !f (s + d) := by
      unfold interleave
      rw [ite_eq_right (by omega), show (2 * s + (2 * d + 1)) / 2 = s + d by omega]
      exact hfg (s + d) (by omega)
    rw [hev, hod]
    cases f (s + d) <;> simp <;> omega

/-- **Unconditional `HalfDensity` of the Shifted-Complement Multiplex (`halfDensity_interleave_of_succ_eq_not`):**
if `g (s + 1) = !f s` for all `s ≥ T`, then `interleave f (fun u => g (u + 1))` satisfies
`HalfDensity`. -/
theorem halfDensity_interleave_of_succ_eq_not {f g : Nat → Bool} {T : Nat}
    (hfg : ∀ s, T ≤ s → g (s + 1) = !f s) :
    HalfDensity (interleave f (fun u => g (u + 1))) := by
  let h := interleave f (fun u => g (u + 1))
  intro k hk
  refine ⟨k * (2 * T + 2) + 2 * T, fun n hn => ?_⟩
  let d := (n - 2 * T) / 2
  let r := (n - 2 * T) % 2
  have hn_eq : n = (2 * T + 2 * d) + r := by omega
  have hbase := blackCountFor_add_eq_winCount h (2 * T) (2 * d)
  rw [winCount_interleave_two_mul hfg (Nat.le_refl T) d] at hbase
  obtain ⟨hb1, hb2⟩ := blackCountFor_add_bounds h (2 * T + 2 * d) r
  rw [← hn_eq] at hb1 hb2
  rw [hbase] at hb1 hb2
  obtain ⟨hT1, hT2⟩ := blackCountFor_add_bounds h 0 (2 * T)
  have h0 : blackCountFor h 0 = 0 := rfl
  rw [h0, Nat.zero_add] at hT1 hT2
  have hdisc : (2 * (blackCountFor h n : Int) - (n : Int)).natAbs ≤ 2 * T + 2 := by omega
  have hmul : k * (2 * (blackCountFor h n : Int) - (n : Int)).natAbs ≤ k * (2 * T + 2) :=
    Nat.mul_le_mul_left k hdisc
  dsimp only [h] at hmul
  omega

/-- **Unconditional `HalfDensity` of the Post-White Twin-Diagonal Multiplex (`D_post_white_interleave_halfDensity`):**
around every eventually white left diagonal `EvWhite (D (j + 1))`, the interleaved twin-diagonal
sequence `interleave (D (j + 2)) (fun t => D (j + 4) (t + 1))` unconditionally has asymptotic
density `1/2` (`HalfDensity`). -/
theorem D_post_white_interleave_halfDensity {j : Nat} (hw : EvWhite (D (j + 1))) :
    HalfDensity (interleave (D (j + 2)) (fun t => D (j + 4) (t + 1))) := by
  obtain ⟨T, hT⟩ := D_post_white_complement hw
  exact halfDensity_interleave_of_succ_eq_not (fun s hs => (hT s hs).2)

/-- **Right-Diagonal `leastExp` Step-Up Implies `HalfDensity` (`R_halfDensity_of_leastExp_succ`):**
whenever the least period exponent of a right diagonal increases (`leastExp (j + 1) = leastExp j + 1`),
`R (j + 1)` is `2 ^ leastExp j`-anti-periodic from `t = 0`, is not `2 ^ leastExp j`-periodic, and
satisfies `HalfDensity (R (j + 1))`. -/
theorem R_halfDensity_of_leastExp_succ {j : Nat} (h : leastExp (j + 1) = leastExp j + 1) :
    (∀ t, R (j + 1) (t + 2 ^ leastExp j) = !R (j + 1) t) ∧
      ¬ Per (j + 1) (2 ^ leastExp j) ∧ HalfDensity (R (j + 1)) := by
  have hanti := leastExp_antiperiod h
  have hnot := (leastExp_spec (j + 1)).2 (leastExp j) (by omega)
  exact ⟨hanti, hnot, halfDensity_of_antiperiodic (Nat.two_pow_pos (leastExp j)) ⟨0, fun t _ => hanti t⟩⟩

/-- **Uniform All-`n` Discrepancy Bound for Period-Doubling Right Diagonals (`R_discrepancy_le_of_leastExp_succ`):**
whenever `leastExp (j + 1) = leastExp j + 1`, for every `n : Nat` the discrepancy of `R (j + 1)` is
bounded by a single period: `(2 * (blackCountFor (R (j + 1)) n : Int) - n).natAbs ≤ 2 ^ leastExp (j + 1)`. -/
theorem R_discrepancy_le_of_leastExp_succ {j : Nat} (h : leastExp (j + 1) = leastExp j + 1) (n : Nat) :
    (2 * (blackCountFor (R (j + 1)) n : Int) - n).natAbs ≤ 2 ^ leastExp (j + 1) := by
  have hanti := leastExp_antiperiod h
  have hd := natAbs_discrepancy_le_of_antiperiodic (T := 0) (L := 2 ^ leastExp j)
    (Nat.two_pow_pos (leastExp j)) (fun t _ => hanti t) (Nat.zero_le n)
  rw [Nat.zero_add] at hd
  rw [h, Nat.pow_succ, Nat.mul_comm]
  exact hd

/-! ## 8. Complement Discrepancy Symmetry, Odd-Multiple Antiperiodicity, and Odd-Stride Subsampling -/

/-- **Window Sum Conservation Under Pointwise Negation (`winCount_not_add`):** for every sequence
`f : Nat → Bool`, start `t : Nat`, and window length `d : Nat`, the black counts of `!f` and `f` on
`[t, t + d)` sum to `d`. -/
theorem winCount_not_add (f : Nat → Bool) (t : Nat) :
    ∀ d, winCount (fun s => !f s) t d + winCount f t d = d
  | 0 => rfl
  | d + 1 => by
    simp only [winCount]
    have ih := winCount_not_add f t d
    have hbit : (if (!f (t + d)) = true then 1 else 0) + (if f (t + d) = true then 1 else 0) = 1 := by
      cases f (t + d) <;> rfl
    omega

/-- **Prefix Black-Count Conservation Under Pointwise Negation (`blackCountFor_not_add`):** for
every sequence `f : Nat → Bool` and prefix length `n : Nat`,
`blackCountFor (fun s => !f s) n + blackCountFor f n = n`. -/
theorem blackCountFor_not_add (f : Nat → Bool) (n : Nat) :
    blackCountFor (fun s => !f s) n + blackCountFor f n = n := by
  have h1 := blackCountFor_add_eq_winCount (fun s => !f s) 0 n
  have h2 := blackCountFor_add_eq_winCount f 0 n
  have h0a : blackCountFor (fun s => !f s) 0 = 0 := rfl
  have h0b : blackCountFor f 0 = 0 := rfl
  rw [Nat.zero_add, h0a, Nat.zero_add] at h1
  rw [Nat.zero_add, h0b, Nat.zero_add] at h2
  rw [h1, h2]
  exact winCount_not_add f 0 n

/-- **Exact Discrepancy Invariance Under Pointwise Negation (`natAbs_discrepancy_not`):** for every
sequence `f : Nat → Bool` and `n : Nat`, complementing `f` preserves the absolute discrepancy
`(2 * (blackCountFor · n : Int) - n).natAbs`. -/
theorem natAbs_discrepancy_not (f : Nat → Bool) (n : Nat) :
    (2 * (blackCountFor (fun s => !f s) n : Int) - (n : Int)).natAbs =
      (2 * (blackCountFor f n : Int) - (n : Int)).natAbs := by
  have hsum := blackCountFor_not_add f n
  omega

/-- **`HalfDensity` Equivalence Under Pointwise Negation (`halfDensity_not_iff`):** for every
sequence `f : Nat → Bool`, `HalfDensity (fun s => !f s) ↔ HalfDensity f`. -/
theorem halfDensity_not_iff (f : Nat → Bool) :
    HalfDensity (fun s => !f s) ↔ HalfDensity f := by
  constructor <;> intro hf k hk <;> obtain ⟨N, hN⟩ := hf k hk <;> refine ⟨N, fun n hn => ?_⟩
  · rw [← natAbs_discrepancy_not f n]; exact hN n hn
  · rw [natAbs_discrepancy_not f n]; exact hN n hn

/-- **Even-Multiple Periodicity of Antiperiodic Sequences (`apply_add_two_mul_mul_of_antiperiodic`):**
if `f (t + L) = !f t` for all `t ≥ T`, then `f (t + 2 * m * L) = f t` for all `t ≥ T` and `m : Nat`. -/
theorem apply_add_two_mul_mul_of_antiperiodic {f : Nat → Bool} {T L : Nat}
    (ha : ∀ t, T ≤ t → f (t + L) = !f t) {t : Nat} (ht : T ≤ t) :
    ∀ m, f (t + 2 * m * L) = f t
  | 0 => by simp
  | m + 1 => by
    have hstep : t + 2 * (m + 1) * L = (t + 2 * m * L + L) + L := by
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega, Nat.right_distrib, Nat.right_distrib, Nat.one_mul]
      omega
    rw [hstep, ha (t + 2 * m * L + L) (by omega), ha (t + 2 * m * L) (by omega),
      Bool.not_not, apply_add_two_mul_mul_of_antiperiodic ha ht m]

/-- **Odd-Multiple Antiperiodicity (`apply_add_odd_mul_of_antiperiodic`):** if `f (t + L) = !f t`
for all `t ≥ T`, then `f (t + (2 * m + 1) * L) = !f t` for all `t ≥ T` and `m : Nat`. -/
theorem apply_add_odd_mul_of_antiperiodic {f : Nat → Bool} {T L : Nat}
    (ha : ∀ t, T ≤ t → f (t + L) = !f t) {t : Nat} (ht : T ≤ t) (m : Nat) :
    f (t + (2 * m + 1) * L) = !f t := by
  rw [Nat.right_distrib, Nat.one_mul, ← Nat.add_assoc,
    ha (t + 2 * m * L) (by omega), apply_add_two_mul_mul_of_antiperiodic ha ht m]

/-- **Closure of `EvAntiPer` Under Odd Multiples (`EvAntiPer.odd_mul`):** if `EvAntiPer f L` holds,
then `EvAntiPer f ((2 * m + 1) * L)` holds for every `m : Nat`. -/
theorem EvAntiPer.odd_mul {f : Nat → Bool} {L : Nat} (h : EvAntiPer f L) (m : Nat) :
    EvAntiPer f ((2 * m + 1) * L) := by
  obtain ⟨T, hT⟩ := h
  exact ⟨T, fun t ht => apply_add_odd_mul_of_antiperiodic hT ht m⟩

/-- Arithmetic-progression subsampling of a sequence `f` with stride `d` and phase offset `r`:
`subseq f d r k = f (r + k * d)`. -/
def subseq (f : Nat → Bool) (d r k : Nat) : Bool :=
  f (r + k * d)

/-- **Antiperiodicity of Odd-Stride Subsampled Sequences (`evAntiPer_subseq_odd`):** if
`EvAntiPer f L` holds, then for every `m : Nat` and phase `r : Nat`, the odd-stride subsequence
`subseq f (2 * m + 1) r` satisfies `EvAntiPer (subseq f (2 * m + 1) r) L`. -/
theorem evAntiPer_subseq_odd {f : Nat → Bool} {L : Nat} (h : EvAntiPer f L) (m r : Nat) :
    EvAntiPer (subseq f (2 * m + 1) r) L := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T, fun k hk => ?_⟩
  unfold subseq
  have h1 : T ≤ r + k * (2 * m + 1) := by
    have : k * 1 ≤ k * (2 * m + 1) := Nat.mul_le_mul_left k (by omega)
    omega
  have hrew : r + (k + L) * (2 * m + 1) = (r + k * (2 * m + 1)) + (2 * m + 1) * L := by
    rw [Nat.right_distrib, Nat.mul_comm L (2 * m + 1), Nat.add_assoc]
  rw [hrew]
  exact apply_add_odd_mul_of_antiperiodic hT h1 m

/-- **`HalfDensity` of Odd-Stride Subsampled Antiperiodic Sequences (`halfDensity_subseq_odd`):**
if `EvAntiPer f L` holds with `0 < L`, then for every `m : Nat` and phase `r : Nat`, the odd-stride
subsequence `subseq f (2 * m + 1) r` satisfies `HalfDensity`. -/
theorem halfDensity_subseq_odd {f : Nat → Bool} {L : Nat} (hL : 0 < L)
    (h : EvAntiPer f L) (m r : Nat) :
    HalfDensity (subseq f (2 * m + 1) r) :=
  halfDensity_of_antiperiodic hL (evAntiPer_subseq_odd h m r)

/-- **Infinitely Many Left Diagonals Have `HalfDensity` Along Every Odd-Stride Progression
(`D_subseq_odd_infinitely_many_halfDensity`):** for every odd stride `2 * m + 1`, phase `r : Nat`,
and index bound `N : Nat`, there exists a left diagonal `j > N` such that `subseq (D j) (2 * m + 1) r`
has asymptotic density `1/2` (`HalfDensity`). -/
theorem D_subseq_odd_infinitely_many_halfDensity (m r N : Nat) :
    ∃ j, N < j ∧ HalfDensity (subseq (D j) (2 * m + 1) r) := by
  obtain ⟨j, hj, k, hanti, _, _⟩ := D_infinitely_many_halfDensity N
  exact ⟨j, hj, halfDensity_subseq_odd (Nat.two_pow_pos k) hanti m r⟩

/-- **Infinitely Many Right Diagonals Have `HalfDensity` Along Every Odd-Stride Progression
(`R_subseq_odd_infinitely_many_halfDensity`):** for every odd stride `2 * m + 1`, phase `r : Nat`,
and index bound `k : Nat`, there exists a right diagonal `j` with `k < j ≤ 2 ^ (k + 1) - 1` such
that `subseq (R j) (2 * m + 1) r` has asymptotic density `1/2` (`HalfDensity`). -/
theorem R_subseq_odd_infinitely_many_halfDensity (m r k : Nat) :
    ∃ j, k < j ∧ j ≤ 2 ^ (k + 1) - 1 ∧ HalfDensity (subseq (R j) (2 * m + 1) r) := by
  obtain ⟨j, hj, hjb, hanti, _, _⟩ := R_infinitely_many_halfDensity k
  exact ⟨j, hj, hjb, halfDensity_subseq_odd (Nat.two_pow_pos k) ⟨0, fun t _ => hanti t⟩ m r⟩

/-! ## 9. Periodic Window-Balance Characterization, Odd-Period Exclusion, and Core-Lean-4 Progression Bridge to `Problem1` -/

/-- **Left-Endpoint Shift Identity for `winCount` (`winCount_succ_left`):**
for any sequence `f : Nat → Bool`, start `t : Nat`, and window length `d : Nat`,
`winCount f t d + (if f (t + d) then 1 else 0) = (if f t then 1 else 0) + winCount f (t + 1) d`. -/
theorem winCount_succ_left (f : Nat → Bool) (t : Nat) :
    ∀ d, winCount f t d + (if f (t + d) then 1 else 0) =
      (if f t then 1 else 0) + winCount f (t + 1) d
  | 0 => by simp [winCount]
  | d + 1 => by
    have ih := winCount_succ_left f t d
    simp only [winCount]
    have h1 : t + (d + 1) = t + 1 + d := by omega
    rw [h1]
    omega

/-- **One-Step Invariance of `winCount` Under Periodicity (`winCount_step_of_periodic`):**
if `f (t + L) = f t`, then `winCount f (t + 1) L = winCount f t L`. -/
theorem winCount_step_of_periodic {f : Nat → Bool} {t L : Nat} (hf : f (t + L) = f t) :
    winCount f (t + 1) L = winCount f t L := by
  have h := winCount_succ_left f t L
  rw [hf] at h
  omega

/-- **Global Invariance of `winCount` Across a Periodic Tail (`winCount_const_of_periodic`):**
if `f (s + L) = f s` for all `s ≥ T`, then `winCount f t L = winCount f T L` for all `t ≥ T`. -/
theorem winCount_const_of_periodic {f : Nat → Bool} {T L : Nat}
    (hper : ∀ s, T ≤ s → f (s + L) = f s) :
    ∀ {t : Nat}, T ≤ t → winCount f t L = winCount f T L := by
  intro t ht
  obtain ⟨k, rfl⟩ : ∃ k, t = T + k := ⟨t - T, by omega⟩
  induction k with
  | zero => rfl
  | succ k ih =>
    have hstep : winCount f (T + k + 1) L = winCount f (T + k) L :=
      winCount_step_of_periodic (hper (T + k) (by omega))
    rw [← Nat.add_assoc, hstep, ih (by omega)]

/-- **Multi-Period Linear Accumulation of `blackCountFor` (`blackCountFor_add_mul_of_periodic`):**
if `f (s + L) = f s` for all `s ≥ T`, then for every `m : Nat`,
`blackCountFor f (T + m * L) = blackCountFor f T + m * winCount f T L`. -/
theorem blackCountFor_add_mul_of_periodic {f : Nat → Bool} {T L : Nat}
    (hper : ∀ s, T ≤ s → f (s + L) = f s) (m : Nat) :
    blackCountFor f (T + m * L) = blackCountFor f T + m * winCount f T L := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hrew : T + (m + 1) * L = (T + m * L) + L := by
      rw [Nat.succ_mul, Nat.add_assoc]
    rw [hrew, blackCountFor_add_eq_winCount, ih,
      winCount_const_of_periodic hper (by omega : T ≤ T + m * L), Nat.succ_mul]
    omega

/-- **Necessary Window-Balance Condition for Periodic `HalfDensity`
(`two_mul_winCount_eq_period_of_periodic_of_halfDensity`):**
if `f` has period `L > 0` from `T` on and satisfies `HalfDensity f`, then every length-`L` window
from `T` on contains exactly `L / 2` black cells (`2 * winCount f T L = L`). -/
theorem two_mul_winCount_eq_period_of_periodic_of_halfDensity {f : Nat → Bool} {T L : Nat}
    (hL : 0 < L) (hper : ∀ s, T ≤ s → f (s + L) = f s) (hd : HalfDensity f) :
    2 * winCount f T L = L := by
  by_cases hne : 2 * winCount f T L = L
  · exact hne
  · exfalso
    obtain ⟨N, hN⟩ := hd (L + 1) (by omega)
    let m := N + (L + 1) * T + T + 1
    have hmlt : m * 1 ≤ m * L := Nat.mul_le_mul_left m hL
    have hn_ge : N ≤ T + m * L := by omega
    have hbound := hN (T + m * L) hn_ge
    have hcnt := blackCountFor_add_mul_of_periodic hper m
    have hmul2 : 2 * (m * winCount f T L) = m * (2 * winCount f T L) :=
      Nat.mul_left_comm 2 m (winCount f T L)
    have hbt_le : blackCountFor f T ≤ T := by
      have hb := (blackCountFor_add_bounds f 0 T).2
      simpa [blackCountFor] using hb
    let d := (2 * (blackCountFor f (T + m * L) : Int) - ((T + m * L : Nat) : Int)).natAbs
    have hd_def : d = (2 * (blackCountFor f (T + m * L) : Int) - ((T + m * L : Nat) : Int)).natAbs := rfl
    have hbound' : (L + 1) * d ≤ T + m * L := hbound
    have hm_ge : T ≤ m := by omega
    have hmd_ge : m - T ≤ d := by
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · have hle : m * (2 * winCount f T L + 1) ≤ m * L := Nat.mul_le_mul_left m (by omega)
        rw [Nat.left_distrib, Nat.mul_one] at hle
        omega
      · have hle : m * (L + 1) ≤ m * (2 * winCount f T L) := Nat.mul_le_mul_left m (by omega)
        rw [Nat.left_distrib, Nat.mul_one] at hle
        omega
    have hmul_d : (L + 1) * (m - T) ≤ (L + 1) * d := Nat.mul_le_mul_left (L + 1) hmd_ge
    have h1 : (L + 1) * m = m * L + m := by
      rw [Nat.right_distrib, Nat.one_mul, Nat.mul_comm L m]
    have h2 : (L + 1) * (m - T) + (L + 1) * T = (L + 1) * m := by
      rw [← Nat.left_distrib, Nat.sub_add_cancel hm_ge]
    omega

/-- **Uniform Discrepancy Bound for Balanced Periodic Sequences (`natAbs_discrepancy_le_of_periodic_balanced`):**
if `f (s + L) = f s` for all `s ≥ T` (`0 < L`) and `2 * winCount f T L = L`, then for all `n ≥ T`,
`((2 * (blackCountFor f n : Int) - (n : Int)).natAbs) ≤ T + 2 * L`. -/
theorem natAbs_discrepancy_le_of_periodic_balanced {f : Nat → Bool} {T L : Nat} (hL : 0 < L)
    (hper : ∀ s, T ≤ s → f (s + L) = f s) (hbal : 2 * winCount f T L = L)
    {n : Nat} (hn : T ≤ n) :
    ((2 * (blackCountFor f n : Int) - (n : Int)).natAbs) ≤ T + 2 * L := by
  let m := (n - T) / L
  let r := (n - T) % L
  have hdiv : (n - T) = L * m + r := (Nat.div_add_mod (n - T) L).symm
  have hr_lt : r < L := Nat.mod_lt (n - T) hL
  have hn_eq : n = (T + m * L) + r := by
    have : L * m = m * L := Nat.mul_comm L m
    omega
  have hbase : blackCountFor f (T + m * L) = blackCountFor f T + m * winCount f T L :=
    blackCountFor_add_mul_of_periodic hper m
  have hb_lo : blackCountFor f (T + m * L) ≤ blackCountFor f n := by
    rw [hn_eq]
    exact (blackCountFor_add_bounds f (T + m * L) r).1
  have hb_hi : blackCountFor f n ≤ blackCountFor f (T + m * L) + r := by
    rw [hn_eq]
    exact (blackCountFor_add_bounds f (T + m * L) r).2
  have hT_hi : blackCountFor f T ≤ T := by
    have h0 := (blackCountFor_add_bounds f 0 T).2
    simpa [blackCountFor] using h0
  have hmL : 2 * (m * winCount f T L) = m * L := by
    calc 2 * (m * winCount f T L) = m * (2 * winCount f T L) := Nat.mul_left_comm 2 m (winCount f T L)
    _ = m * L := by rw [hbal]
  omega

/-- **Sufficient Window-Balance Condition for Periodic `HalfDensity`
(`halfDensity_of_periodic_of_two_mul_winCount_eq`):**
if `f` has period `L > 0` from `T` on and `2 * winCount f T L = L`, then `HalfDensity f` holds. -/
theorem halfDensity_of_periodic_of_two_mul_winCount_eq {f : Nat → Bool} {T L : Nat}
    (hL : 0 < L) (hper : ∀ s, T ≤ s → f (s + L) = f s) (hbal : 2 * winCount f T L = L) :
    HalfDensity f := by
  intro k hk
  refine ⟨T + k * (T + 2 * L), fun n hn => ?_⟩
  have hdisc := natAbs_discrepancy_le_of_periodic_balanced hL hper hbal (by omega : T ≤ n)
  have hmul : k * ((2 * (blackCountFor f n : Int) - (n : Int)).natAbs) ≤ k * (T + 2 * L) :=
    Nat.mul_le_mul_left k hdisc
  omega

/-- **Exact Characterization of `HalfDensity` for Periodic Sequences
(`periodic_halfDensity_iff_two_mul_winCount_eq`):**
for any sequence `f` with period `L > 0` from `T` on, `HalfDensity f ↔ 2 * winCount f T L = L`. -/
theorem periodic_halfDensity_iff_two_mul_winCount_eq {f : Nat → Bool} {T L : Nat}
    (hL : 0 < L) (hper : ∀ s, T ≤ s → f (s + L) = f s) :
    HalfDensity f ↔ 2 * winCount f T L = L :=
  ⟨two_mul_winCount_eq_period_of_periodic_of_halfDensity hL hper,
   halfDensity_of_periodic_of_two_mul_winCount_eq hL hper⟩

/-- **Unconditional Odd-Period Exclusion Under `HalfDensity` (`not_evPer_odd_of_halfDensity`):**
no sequence `f : Nat → Bool` satisfying `HalfDensity f` can have an odd eventual period `2 * m + 1`. -/
theorem not_evPer_odd_of_halfDensity {f : Nat → Bool} (hd : HalfDensity f) (m : Nat) :
    ¬ EvPer f (2 * m + 1) := by
  rintro ⟨T, hper⟩
  have hbal := two_mul_winCount_eq_period_of_periodic_of_halfDensity (by omega : 0 < 2 * m + 1) hper hd
  omega

/-- **Antiperiodic Sequences Exclude All Odd Eventual Periods (`not_evPer_odd_of_evAntiPer`):**
any sequence `f : Nat → Bool` that is eventually `L`-antiperiodic (`0 < L`) cannot have any odd
eventual period `2 * m + 1`. -/
theorem not_evPer_odd_of_evAntiPer {f : Nat → Bool} {L : Nat} (hL : 0 < L)
    (hanti : EvAntiPer f L) (m : Nat) :
    ¬ EvPer f (2 * m + 1) :=
  not_evPer_odd_of_halfDensity (halfDensity_of_antiperiodic hL hanti) m

/-- **No Eventually Constant Sequence Has `HalfDensity` (`not_evConstant_of_halfDensity`):**
if `HalfDensity f` holds, then `f` is not eventually constant (`¬ EvPer f 1`) and in particular
not eventually white (`¬ EvWhite f`). -/
theorem not_evConstant_of_halfDensity {f : Nat → Bool} (hd : HalfDensity f) :
    ¬ EvPer f 1 ∧ ¬ EvWhite f := by
  have hnot1 : ¬ EvPer f 1 := by simpa using not_evPer_odd_of_halfDensity hd 0
  refine ⟨hnot1, ?_⟩
  rintro ⟨T, hw⟩
  exact hnot1 ⟨T, fun t ht => by rw [hw (t + 1) (by omega), hw t ht]⟩

/-- **`Problem2` Unconditionally Excludes All Odd Eventual Periods of `center`
(`center_not_evPer_odd_of_problem2`):**
under `Problem2` (`HalfDensity center`), the Rule 30 center column has no odd eventual period
`2 * m + 1` for any `m : Nat`. -/
theorem center_not_evPer_odd_of_problem2 (hP2 : Problem2) (m : Nat) :
    ¬ EvPer center (2 * m + 1) :=
  not_evPer_odd_of_halfDensity (halfDensity_center_iff.mpr hP2) m

/-- **Eventual Periodicity Forces Every Arithmetic Subsequence of Stride `L` to Be Eventually Constant
(`evPer_one_subseq_of_evPer`):**
if `EvPer f L` holds (`0 < L`), then for every phase `r : Nat`, the stride-`L` arithmetic progression
`subseq f L r` has eventual period `1` (`EvPer (subseq f L r) 1`). -/
theorem evPer_one_subseq_of_evPer {f : Nat → Bool} {L : Nat} (hL : 0 < L)
    (hper : EvPer f L) (r : Nat) :
    EvPer (subseq f L r) 1 := by
  obtain ⟨T, hT⟩ := hper
  refine ⟨T, fun k hk => ?_⟩
  simp only [subseq]
  have h1 : r + (k + 1) * L = (r + k * L) + L := by
    rw [Nat.succ_mul, Nat.add_assoc]
  have hge : T ≤ r + k * L := by
    have : k * 1 ≤ k * L := Nat.mul_le_mul_left k hL
    omega
  rw [h1, hT (r + k * L) hge]

/-- **Subsequence `HalfDensity` Excludes Eventual Period `L` (`not_evPer_of_subseq_halfDensity`):**
if `0 < L` and there exists a phase `r : Nat` such that `HalfDensity (subseq f L r)` holds, then
`¬ EvPer f L`. -/
theorem not_evPer_of_subseq_halfDensity {f : Nat → Bool} {L : Nat} (hL : 0 < L)
    {r : Nat} (hd : HalfDensity (subseq f L r)) :
    ¬ EvPer f L := by
  intro hper
  exact (not_evConstant_of_halfDensity hd).1 (evPer_one_subseq_of_evPer hL hper r)

/-- **Core-Lean-4 Progression-Density Bridge to `Problem1` (`problem1_of_subseq_halfDensity`):**
if for every positive stride `L > 0` there is a phase `r : Nat` such that `subseq center L r`
has asymptotic density `1/2` (`HalfDensity`), then `Problem1` (`¬ eventuallyPeriodic center`) holds.
This is the pure core-Lean-4 (Mathlib-free) proof of the progression-density reduction in
`Rule30Equivalents.ProblemTwo.problem1_of_density_on_progressions`. -/
theorem problem1_of_subseq_halfDensity
    (hprog : ∀ L, 0 < L → ∃ r, HalfDensity (subseq center L r)) :
    Problem1 := by
  rintro ⟨T₀, L, hL, hT₀⟩
  obtain ⟨r, hd⟩ := hprog L hL
  exact not_evPer_of_subseq_halfDensity hL hd ⟨T₀, hT₀⟩

/-- **Sharpened Even-Progression Bridge from `Problem2` to `Problem1`
(`problem1_of_problem2_and_even_subseq_halfDensity`):**
because `Problem2` (`HalfDensity center`) already excludes all odd periods `2 * m + 1`, `Problem2`
together with `HalfDensity (subseq center (2 * m) r)` on positive even strides `2 * m` (`m > 0`)
alone implies `Problem1`. This sharpens the core-Lean-4 progression reduction of
`Rule30Equivalents.ProblemTwo.problem1_of_density_on_progressions` from all positive strides to even strides. -/
theorem problem1_of_problem2_and_even_subseq_halfDensity (hP2 : Problem2)
    (heven : ∀ m, 0 < m → ∃ r, HalfDensity (subseq center (2 * m) r)) :
    Problem1 := by
  rintro ⟨T₀, L, hL, hT₀⟩
  have hper : EvPer center L := ⟨T₀, hT₀⟩
  rcases Nat.mod_two_eq_zero_or_one L with hmod0 | hmod1
  · have hm : 0 < L / 2 := by omega
    have hL_eq : L = 2 * (L / 2) := by omega
    rw [hL_eq] at hper
    obtain ⟨r, hd⟩ := heven (L / 2) hm
    exact not_evPer_of_subseq_halfDensity (by omega : 0 < 2 * (L / 2)) hd hper
  · have hL_eq : L = 2 * (L / 2) + 1 := by omega
    rw [hL_eq] at hper
    exact center_not_evPer_odd_of_problem2 hP2 (L / 2) hper

/-- **Prefix-Count Identity for a Shifted Sequence (`blackCountFor_shift_eq`):**
for any sequence `f : Nat → Bool`, shift `s : Nat`, and length `n : Nat`,
`blackCountFor (fun t => f (s + t)) n = winCount f s n`. -/
theorem blackCountFor_shift_eq (f : Nat → Bool) (s : Nat) :
    ∀ n, blackCountFor (fun t => f (s + t)) n = winCount f s n
  | 0 => rfl
  | n + 1 => by
    rw [blackCountFor_succ, blackCountFor_shift_eq f s n]
    rfl

/-- **Shift Invariance of `HalfDensity` (`halfDensity_shift_iff`):**
for any sequence `f : Nat → Bool` and shift `s : Nat`,
`HalfDensity (fun t => f (s + t)) ↔ HalfDensity f`. -/
theorem halfDensity_shift_iff (f : Nat → Bool) (s : Nat) :
    HalfDensity (fun t => f (s + t)) ↔ HalfDensity f := by
  have h_bs : blackCountFor f s ≤ s := by
    have hb := (blackCountFor_add_bounds f 0 s).2
    simpa [blackCountFor] using hb
  constructor
  · intro hshift k hk
    obtain ⟨N, hN⟩ := hshift (2 * k) (by omega)
    refine ⟨s + N + 2 * k * s, fun n hn => ?_⟩
    have h_add := blackCountFor_add_eq_winCount f s (n - s)
    have hn_eq : s + (n - s) = n := by omega
    rw [hn_eq] at h_add
    have h_sh := blackCountFor_shift_eq f s (n - s)
    have hbound := hN (n - s) (by omega)
    let d_sh := (2 * (blackCountFor (fun t => f (s + t)) (n - s) : Int) - ((n - s : Nat) : Int)).natAbs
    let d_f := (2 * (blackCountFor f n : Int) - (n : Int)).natAbs
    have hd_le : d_f ≤ d_sh + s := by omega
    have hmul : 2 * k * d_f ≤ 2 * k * d_sh + 2 * k * s := by
      calc 2 * k * d_f ≤ 2 * k * (d_sh + s) := Nat.mul_le_mul_left (2 * k) hd_le
      _ = 2 * k * d_sh + 2 * k * s := Nat.left_distrib (2 * k) d_sh s
    have hbound' : 2 * k * d_sh ≤ n - s := hbound
    have h2kd : 2 * (k * d_f) = 2 * k * d_f := (Nat.mul_assoc 2 k d_f).symm
    change k * d_f ≤ n
    omega
  · intro hf k hk
    obtain ⟨N, hN⟩ := hf (2 * k) (by omega)
    refine ⟨N + 2 * k * s + s, fun n hn => ?_⟩
    have h_add := blackCountFor_add_eq_winCount f s n
    have h_sh := blackCountFor_shift_eq f s n
    have hbound := hN (s + n) (by omega)
    let d_sh := (2 * (blackCountFor (fun t => f (s + t)) n : Int) - (n : Int)).natAbs
    let d_f := (2 * (blackCountFor f (s + n) : Int) - ((s + n : Nat) : Int)).natAbs
    have hd_le : d_sh ≤ d_f + s := by omega
    have hmul : 2 * k * d_sh ≤ 2 * k * d_f + 2 * k * s := by
      calc 2 * k * d_sh ≤ 2 * k * (d_f + s) := Nat.mul_le_mul_left (2 * k) hd_le
      _ = 2 * k * d_f + 2 * k * s := Nat.left_distrib (2 * k) d_f s
    have hbound' : 2 * k * d_f ≤ s + n := hbound
    have h2kd : 2 * (k * d_sh) = 2 * k * d_sh := (Nat.mul_assoc 2 k d_sh).symm
    change k * d_sh ≤ n
    omega

/-- **Stride-Multiple Phase Translation Invariance for `subseq` (`halfDensity_subseq_add_mul_iff`):**
shifting the phase `r` of an arithmetic subsequence `subseq f L r` by any multiple `q * L` of the
stride `L` shifts the subsequence by `q` indices and therefore preserves `HalfDensity`. -/
theorem halfDensity_subseq_add_mul_iff (f : Nat → Bool) (L r q : Nat) :
    HalfDensity (subseq f L (r + q * L)) ↔ HalfDensity (subseq f L r) := by
  have hfun : subseq f L (r + q * L) = fun k => subseq f L r (q + k) := by
    funext k
    simp only [subseq]
    rw [Nat.right_distrib, ← Nat.add_assoc]
  rw [hfun]
  exact halfDensity_shift_iff (subseq f L r) q

/-- **Modulo-`L` Canonical Residue Reduction for `subseq` (`halfDensity_subseq_mod_iff`):**
for any stride `L` and phase `r : Nat`, `HalfDensity (subseq f L r) ↔ HalfDensity (subseq f L (r % L))`. -/
theorem halfDensity_subseq_mod_iff (f : Nat → Bool) (L r : Nat) :
    HalfDensity (subseq f L r) ↔ HalfDensity (subseq f L (r % L)) := by
  have hdiv : r = r % L + (r / L) * L := by
    have h := (Nat.div_add_mod r L).symm
    rw [Nat.mul_comm L (r / L), Nat.add_comm] at h
    exact h
  conv => lhs; rw [hdiv]
  exact halfDensity_subseq_add_mul_iff f L (r % L) (r / L)

/-- **Canonical Bounded-Residue Progression Bridge to `Problem1` (`problem1_of_subseq_halfDensity_lt`):**
if for every positive stride `L > 0` there is a canonical residue `r < L` such that
`HalfDensity (subseq center L r)` holds, then `Problem1` (`¬ eventuallyPeriodic center`) holds.
This is the bounded-residue core-Lean-4 form of `Rule30Equivalents.ProblemTwo.problem1_of_density_on_progressions`. -/
theorem problem1_of_subseq_halfDensity_lt
    (hprog : ∀ L, 0 < L → ∃ r, r < L ∧ HalfDensity (subseq center L r)) :
    Problem1 :=
  problem1_of_subseq_halfDensity (fun L hL => by
    obtain ⟨r, _, hd⟩ := hprog L hL
    exact ⟨r, hd⟩)

/-- **Canonical Bounded-Residue Even-Progression Bridge from `Problem2` to `Problem1`
(`problem1_of_problem2_and_even_subseq_halfDensity_lt`):**
under `Problem2`, if for every `m > 0` there exists a canonical residue `r < 2 * m` such that
`HalfDensity (subseq center (2 * m) r)` holds, then `Problem1` holds. -/
theorem problem1_of_problem2_and_even_subseq_halfDensity_lt (hP2 : Problem2)
    (heven : ∀ m, 0 < m → ∃ r, r < 2 * m ∧ HalfDensity (subseq center (2 * m) r)) :
    Problem1 :=
  problem1_of_problem2_and_even_subseq_halfDensity hP2 (fun m hm => by
    obtain ⟨r, _, hd⟩ := heven m hm
    exact ⟨r, hd⟩)

/-- **Infinitely Many Left Diagonals simultaneously Satisfy `HalfDensity` and Exclude All Odd Periods
(`D_infinitely_many_not_evPer_odd`):**
for every `N : Nat`, there exists a left diagonal `j ≥ N` such that `D j` satisfies `HalfDensity (D j)`
and has no odd eventual period `2 * m + 1` for any `m : Nat`. -/
theorem D_infinitely_many_not_evPer_odd (N : Nat) :
    ∃ j, N ≤ j ∧ HalfDensity (D j) ∧ ∀ m, ¬ EvPer (D j) (2 * m + 1) := by
  obtain ⟨j, hj, _, _, _, hd⟩ := D_infinitely_many_halfDensity N
  exact ⟨j, by omega, hd, not_evPer_odd_of_halfDensity hd⟩

/-- **Infinitely Many Right Diagonals Simultaneously Satisfy `HalfDensity` and Exclude All Odd Periods
(`R_infinitely_many_not_evPer_odd`):**
for every `k : Nat`, there exists a right diagonal `j` (`k < j ≤ 2 ^ (k + 1) - 1`) such that `R j`
satisfies `HalfDensity (R j)` and has no odd eventual period `2 * m + 1` for any `m : Nat`. -/
theorem R_infinitely_many_not_evPer_odd (k : Nat) :
    ∃ j, k < j ∧ j ≤ 2 ^ (k + 1) - 1 ∧ HalfDensity (R j) ∧ ∀ m, ¬ EvPer (R j) (2 * m + 1) := by
  obtain ⟨j, hkj, hjb, _, _, hd⟩ := R_infinitely_many_halfDensity k
  exact ⟨j, hkj, hjb, hd, not_evPer_odd_of_halfDensity hd⟩

/-! ### Subsequence Semigroup Law, Subsequence Period Inheritance, and Unconditional Elimination of the `Problem2` Hypothesis from Even-Stride Progression Bridges -/

/-- **Unit-Stride Subsequence Identity (`subseq_one_zero`):** for every sequence `f : Nat → Bool`,
`subseq f 1 0 = f`. -/
theorem subseq_one_zero (f : Nat → Bool) : subseq f 1 0 = f := by
  funext k
  simp [subseq]

/-- **Zero-Stride Constant Subsequence (`subseq_zero_left`):** subsampling `f` with stride `0` and
offset `r` yields the constant sequence `fun _ => f r`. -/
theorem subseq_zero_left (f : Nat → Bool) (r : Nat) : subseq f 0 r = fun _ => f r := by
  funext k
  simp [subseq]

/-- **Subsequence Composition Semigroup Law (`subseq_subseq`):** iterating `subseq` with `(d₁, r₁)`
and `(d₂, r₂)` equals `subseq f (d₂ * d₁) (r₁ + r₂ * d₁)`. -/
theorem subseq_subseq (f : Nat → Bool) (d₁ r₁ d₂ r₂ : Nat) :
    subseq (subseq f d₁ r₁) d₂ r₂ = subseq f (d₂ * d₁) (r₁ + r₂ * d₁) := by
  funext k
  simp only [subseq]
  exact congrArg f (by rw [Nat.right_distrib, ← Nat.add_assoc, Nat.mul_assoc])

/-- **Multi-Period Step Invariance (`apply_add_mul_of_periodic`):** if `f (t + L) = f t` for all
`t ≥ T`, then `f (t + d * L) = f t` for every `d : Nat` and `t ≥ T`. -/
theorem apply_add_mul_of_periodic {f : Nat → Bool} {T L : Nat}
    (hT : ∀ t, T ≤ t → f (t + L) = f t) (d : Nat) {t : Nat} (ht : T ≤ t) :
    f (t + d * L) = f t := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.succ_mul, ← Nat.add_assoc, hT (t + d * L) (by omega), ih]

/-- **Eventual Periodicity of Period Multiples (`evPer_mul_of_evPer`):** if `EvPer f L`, then
`EvPer f (d * L)` for every `d : Nat`. -/
theorem evPer_mul_of_evPer {f : Nat → Bool} {L : Nat} (h : EvPer f L) (d : Nat) :
    EvPer f (d * L) := by
  obtain ⟨T, hT⟩ := h
  exact ⟨T, fun t ht => apply_add_mul_of_periodic hT d ht⟩

/-- **Universal Subsequence Period Inheritance (`evPer_subseq_of_evPer`):** if `EvPer f L`, then
for every stride `d : Nat` and offset `r : Nat`, the arithmetic subsequence `subseq f d r` also
satisfies `EvPer (subseq f d r) L`. -/
theorem evPer_subseq_of_evPer {f : Nat → Bool} {L : Nat} (h : EvPer f L) (d r : Nat) :
    EvPer (subseq f d r) L := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact ⟨0, fun k _ => by simp [subseq]⟩
  · obtain ⟨T, hT⟩ := h
    refine ⟨T, fun k hk => ?_⟩
    simp only [subseq]
    have h1 : r + (k + L) * d = (r + k * d) + d * L := by
      rw [Nat.right_distrib, ← Nat.add_assoc, Nat.mul_comm L d]
    have hge : T ≤ r + k * d := by
      have : k * 1 ≤ k * d := Nat.mul_le_mul_left k hd
      omega
    rw [h1]
    exact apply_add_mul_of_periodic hT d hge

/-- **Odd-Period Exclusion Lifted from Any Subsequence (`not_evPer_odd_of_subseq_halfDensity`):**
if there exist ANY stride `d : Nat` and offset `r : Nat` such that `HalfDensity (subseq f d r)`
holds, then `f` has no odd eventual period `2 * m + 1` (`¬ EvPer f (2 * m + 1)`). -/
theorem not_evPer_odd_of_subseq_halfDensity {f : Nat → Bool} {d r : Nat}
    (hd : HalfDensity (subseq f d r)) (m : Nat) :
    ¬ EvPer f (2 * m + 1) :=
  fun hper => not_evPer_odd_of_halfDensity hd m (evPer_subseq_of_evPer hper d r)

/-- **Center Odd-Period Exclusion from Any Single Subsequence
(`center_not_evPer_odd_of_subseq_halfDensity`):** if `HalfDensity (subseq center d r)` holds for
even a single pair `(d, r)`, then `center` has no odd eventual period `2 * m + 1`. -/
theorem center_not_evPer_odd_of_subseq_halfDensity {d r : Nat}
    (hd : HalfDensity (subseq center d r)) (m : Nat) :
    ¬ EvPer center (2 * m + 1) :=
  not_evPer_odd_of_subseq_halfDensity hd m

/-- **Even-Stride Progression Bridge to `Problem1` Without Assuming `Problem2`
(`problem1_of_even_subseq_halfDensity`):** if for every `m > 0` there exists an offset `r : Nat`
such that `HalfDensity (subseq center (2 * m) r)` holds, then `Problem1` holds unconditionally
(eliminating the `hP2 : Problem2` hypothesis from `problem1_of_problem2_and_even_subseq_halfDensity`,
since the `m = 1` progression `subseq center 2 r` already excludes all odd periods of `center`). -/
theorem problem1_of_even_subseq_halfDensity
    (heven : ∀ m, 0 < m → ∃ r, HalfDensity (subseq center (2 * m) r)) :
    Problem1 := by
  rintro ⟨T₀, L, hL, hT₀⟩
  have hper : EvPer center L := ⟨T₀, hT₀⟩
  rcases Nat.mod_two_eq_zero_or_one L with hmod0 | hmod1
  · have hm : 0 < L / 2 := by omega
    have hL_eq : L = 2 * (L / 2) := by omega
    rw [hL_eq] at hper
    obtain ⟨r, hd⟩ := heven (L / 2) hm
    exact not_evPer_of_subseq_halfDensity (by omega : 0 < 2 * (L / 2)) hd hper
  · have hL_eq : L = 2 * (L / 2) + 1 := by omega
    rw [hL_eq] at hper
    obtain ⟨r₁, hd₁⟩ := heven 1 (by decide)
    exact not_evPer_odd_of_subseq_halfDensity hd₁ (L / 2) hper

/-- **Canonical Bounded-Residue Even-Stride Bridge to `Problem1` Without Assuming `Problem2`
(`problem1_of_even_subseq_halfDensity_lt`):** if for every `m > 0` there is a canonical residue
`r < 2 * m` with `HalfDensity (subseq center (2 * m) r)`, then `Problem1` holds (eliminating the
`Problem2` hypothesis from `problem1_of_problem2_and_even_subseq_halfDensity_lt`). -/
theorem problem1_of_even_subseq_halfDensity_lt
    (heven : ∀ m, 0 < m → ∃ r, r < 2 * m ∧ HalfDensity (subseq center (2 * m) r)) :
    Problem1 :=
  problem1_of_even_subseq_halfDensity (fun m hm => by
    obtain ⟨r, _, hd⟩ := heven m hm
    exact ⟨r, hd⟩)

/-! ## 12. Stride-Division Period Reduction and Dyadic Power-of-Two Progression Bridges to `Problem1` -/

/-- **Stride-Division Period Reduction (`evPer_subseq_div_of_evPer_mul`):** if `f` has eventual
period `d * q` (`EvPer f (d * q)`) with `0 < d`, then for every offset `r : Nat`, the stride-`d`
subsequence `subseq f d r` has eventual period `q` (`EvPer (subseq f d r) q`). -/
theorem evPer_subseq_div_of_evPer_mul {f : Nat → Bool} {d q : Nat}
    (hd : 0 < d) (h : EvPer f (d * q)) (r : Nat) :
    EvPer (subseq f d r) q := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T, fun k hk => ?_⟩
  simp only [subseq]
  have h1 : r + (k + q) * d = (r + k * d) + d * q := by
    rw [Nat.right_distrib, ← Nat.add_assoc, Nat.mul_comm q d]
  have hge : T ≤ r + k * d := by
    have : k * 1 ≤ k * d := Nat.mul_le_mul_left k hd
    omega
  rw [h1]
  exact hT (r + k * d) hge

/-- **Exclusion of All Odd Multiples `d * (2 * m + 1)` from a Single Stride-`d` `HalfDensity`
Subsequence (`not_evPer_mul_odd_of_subseq_halfDensity`):** if `0 < d` and
`HalfDensity (subseq f d r)` holds for some offset `r`, then `f` cannot have eventual period
`d * (2 * m + 1)` for any `m : Nat`. -/
theorem not_evPer_mul_odd_of_subseq_halfDensity {f : Nat → Bool} {d r : Nat}
    (hd : 0 < d) (h : HalfDensity (subseq f d r)) (m : Nat) :
    ¬ EvPer f (d * (2 * m + 1)) :=
  fun hper => not_evPer_odd_of_halfDensity h m (evPer_subseq_div_of_evPer_mul hd hper r)

/-- **Exclusion of the Entire 2-Adic Valuation Shell `2^a * (2 * m + 1)` from One Dyadic
Subsequence (`not_evPer_two_pow_mul_odd_of_subseq_halfDensity`):** if
`HalfDensity (subseq f (2 ^ a) r)` holds for some `r`, then `f` has no eventual period of the
form `2 ^ a * (2 * m + 1)` for any `m : Nat`. -/
theorem not_evPer_two_pow_mul_odd_of_subseq_halfDensity {f : Nat → Bool} {a r : Nat}
    (h : HalfDensity (subseq f (2 ^ a) r)) (m : Nat) :
    ¬ EvPer f (2 ^ a * (2 * m + 1)) :=
  not_evPer_mul_odd_of_subseq_halfDensity (Nat.two_pow_pos a) h m

/-- **2-Adic Valuation Factorization of Positive Naturals (`exists_eq_two_pow_mul_odd`):**
every positive integer `L > 0` factors as `L = 2 ^ a * (2 * m + 1)` for some `a, m : Nat`. -/
theorem exists_eq_two_pow_mul_odd : ∀ L : Nat, 0 < L → ∃ a m : Nat, L = 2 ^ a * (2 * m + 1)
  | 0, hL => by omega
  | L + 1, _ => by
    rcases Nat.mod_two_eq_zero_or_one (L + 1) with hmod0 | hmod1
    · have hhalf : 0 < (L + 1) / 2 := by omega
      have hlt : (L + 1) / 2 < L + 1 := by omega
      obtain ⟨a, m, ih⟩ := exists_eq_two_pow_mul_odd ((L + 1) / 2) hhalf
      refine ⟨a + 1, m, ?_⟩
      have heq : L + 1 = 2 * ((L + 1) / 2) := by omega
      rw [heq, ih, Nat.pow_succ, Nat.mul_comm (2 ^ a) 2, Nat.mul_assoc]
    · refine ⟨0, (L + 1) / 2, ?_⟩
      rw [Nat.pow_zero, Nat.one_mul]
      omega
termination_by L => L

/-- **Dyadic Power-of-Two Subsequence Bridge to `Problem1` (`problem1_of_dyadic_subseq_halfDensity`):**
if for every `a >= 1` there exists an offset `r` such that `HalfDensity (subseq center (2 ^ a) r)`
holds, then `Rule30Prize.Problem1` holds (strengthening `problem1_of_even_subseq_halfDensity`
from all even strides `2 * m` to powers of two `2 ^ a` alone). -/
theorem problem1_of_dyadic_subseq_halfDensity
    (hdyadic : ∀ a : Nat, 0 < a → ∃ r : Nat, HalfDensity (subseq center (2 ^ a) r)) :
    Problem1 := by
  rintro ⟨T₀, L, hL, hT₀⟩
  have hper : EvPer center L := ⟨T₀, hT₀⟩
  obtain ⟨a, m, hfac⟩ := exists_eq_two_pow_mul_odd L hL
  rw [hfac] at hper
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [Nat.pow_zero, Nat.one_mul] at hper
    obtain ⟨r₁, hd₁⟩ := hdyadic 1 (by decide)
    exact not_evPer_odd_of_subseq_halfDensity hd₁ m hper
  · obtain ⟨r, hd⟩ := hdyadic a ha
    exact not_evPer_two_pow_mul_odd_of_subseq_halfDensity hd m hper

/-- **Bounded-Residue Dyadic Power-of-Two Bridge to `Problem1`
(`problem1_of_dyadic_subseq_halfDensity_lt`):** if for every `a >= 1` there exists `r < 2 ^ a`
with `HalfDensity (subseq center (2 ^ a) r)`, then `Problem1` holds. -/
theorem problem1_of_dyadic_subseq_halfDensity_lt
    (hdyadic : ∀ a : Nat, 0 < a → ∃ r : Nat, r < 2 ^ a ∧ HalfDensity (subseq center (2 ^ a) r)) :
    Problem1 :=
  problem1_of_dyadic_subseq_halfDensity fun a ha => by
    obtain ⟨r, _, hd⟩ := hdyadic a ha
    exact ⟨r, hd⟩

/-- **Simultaneous Closure of `Problem1 ∧ Problem2` from All Dyadic Strides `2 ^ a` (`a >= 0`)
(`problem1_and_problem2_of_all_dyadic_subseq_halfDensity_lt`):** if for every `a : Nat` (`a >= 0`)
there exists `r < 2 ^ a` with `HalfDensity (subseq center (2 ^ a) r)`, then both `Problem1` and
`Problem2` hold (`a = 0` gives `2 ^ 0 = 1`, i.e., `Problem2`, and `a >= 1` gives `Problem1`). -/
theorem problem1_and_problem2_of_all_dyadic_subseq_halfDensity_lt
    (h : ∀ a : Nat, ∃ r : Nat, r < 2 ^ a ∧ HalfDensity (subseq center (2 ^ a) r)) :
    Problem1 ∧ Problem2 := by
  refine ⟨problem1_of_dyadic_subseq_halfDensity_lt (fun a _ => h a), ?_⟩
  obtain ⟨r, hr, hd⟩ := h 0
  have hr0 : r = 0 := by omega
  subst hr0
  rw [Nat.pow_zero, subseq_one_zero] at hd
  exact hd

/-! ## 13. Finite-Horizon Dyadic Divisibility (`2^(K+1) | L`) and Exponential Period Lower Bounds (`L >= 2^(K+1)`) -/

/-- **Power-of-Two Splitting Above `K + 1` (`pow_two_eq_pow_succ_mul`):** if `K + 1 ≤ a`, then
`2 ^ a = 2 ^ (K + 1) * 2 ^ (a - (K + 1))`. -/
theorem pow_two_eq_pow_succ_mul {K a : Nat} (h : K + 1 ≤ a) :
    2 ^ a = 2 ^ (K + 1) * 2 ^ (a - (K + 1)) := by
  rw [← Nat.pow_add, show K + 1 + (a - (K + 1)) = a by omega]

/-- **Finite-Horizon Dyadic Valuation Divisibility (`two_pow_succ_dvd_of_evPer_and_dyadic_subseq_halfDensity`):**
if `1 ≤ K` and for every `1 ≤ a ≤ K` there exists `r` with `HalfDensity (subseq f (2 ^ a) r)`,
then every eventual period `L > 0` of `f` (`EvPer f L`) is a positive multiple of `2 ^ (K + 1)`
(`∃ q > 0, L = 2 ^ (K + 1) * q`). -/
theorem two_pow_succ_dvd_of_evPer_and_dyadic_subseq_halfDensity
    {f : Nat → Bool} {K L : Nat} (hK : 1 ≤ K) (hL : 0 < L)
    (hdyadic : ∀ a : Nat, 1 ≤ a → a ≤ K → ∃ r : Nat, HalfDensity (subseq f (2 ^ a) r))
    (hper : EvPer f L) :
    ∃ q : Nat, 0 < q ∧ L = 2 ^ (K + 1) * q := by
  obtain ⟨a, m, hfac⟩ := exists_eq_two_pow_mul_odd L hL
  have hper_fac : EvPer f (2 ^ a * (2 * m + 1)) := hfac ▸ hper
  rcases Nat.eq_zero_or_pos a with rfl | ha_pos
  · rw [Nat.pow_zero, Nat.one_mul] at hper_fac
    obtain ⟨r₁, hd₁⟩ := hdyadic 1 (Nat.le_refl 1) hK
    exact False.elim (not_evPer_odd_of_subseq_halfDensity hd₁ m hper_fac)
  · by_cases ha_le : a ≤ K
    · obtain ⟨r, hd⟩ := hdyadic a ha_pos ha_le
      exact False.elim (not_evPer_two_pow_mul_odd_of_subseq_halfDensity hd m hper_fac)
    · have ha_ge : K + 1 ≤ a := by omega
      refine ⟨2 ^ (a - (K + 1)) * (2 * m + 1), Nat.mul_pos (Nat.two_pow_pos _) (by omega), ?_⟩
      rw [hfac, pow_two_eq_pow_succ_mul ha_ge, Nat.mul_assoc]

/-- **Exponential Period Lower Bound from Finite Dyadic Progressions
(`two_pow_succ_le_of_evPer_and_dyadic_subseq_halfDensity`):** under the hypotheses of
`two_pow_succ_dvd_of_evPer_and_dyadic_subseq_halfDensity`, `2 ^ (K + 1) ≤ L`. -/
theorem two_pow_succ_le_of_evPer_and_dyadic_subseq_halfDensity
    {f : Nat → Bool} {K L : Nat} (hK : 1 ≤ K) (hL : 0 < L)
    (hdyadic : ∀ a : Nat, 1 ≤ a → a ≤ K → ∃ r : Nat, HalfDensity (subseq f (2 ^ a) r))
    (hper : EvPer f L) :
    2 ^ (K + 1) ≤ L := by
  obtain ⟨q, hq, hfac⟩ := two_pow_succ_dvd_of_evPer_and_dyadic_subseq_halfDensity hK hL hdyadic hper
  have h1 : 2 ^ (K + 1) * 1 ≤ 2 ^ (K + 1) * q := Nat.mul_le_mul_left (2 ^ (K + 1)) hq
  omega

/-- **Exclusion of All Eventual Periods Below `2 ^ (K + 1)`
(`not_evPer_lt_two_pow_succ_of_dyadic_subseq_halfDensity`):** if `1 ≤ K` and
`HalfDensity (subseq f (2 ^ a) r)` holds for some `r` at each level `1 ≤ a ≤ K`, then
`¬ EvPer f L` for every `1 ≤ L < 2 ^ (K + 1)`. -/
theorem not_evPer_lt_two_pow_succ_of_dyadic_subseq_halfDensity
    {f : Nat → Bool} {K L : Nat} (hK : 1 ≤ K) (hL1 : 1 ≤ L) (hL2 : L < 2 ^ (K + 1))
    (hdyadic : ∀ a : Nat, 1 ≤ a → a ≤ K → ∃ r : Nat, HalfDensity (subseq f (2 ^ a) r)) :
    ¬ EvPer f L := by
  intro hper
  have hge := two_pow_succ_le_of_evPer_and_dyadic_subseq_halfDensity hK hL1 hdyadic hper
  omega

/-- **Modulo-4 Period Divisibility from a Single Stride-2 `HalfDensity` Subsequence
(`four_dvd_of_evPer_and_subseq_two_halfDensity`):** if `HalfDensity (subseq f 2 r)` holds for some
`r`, then every eventual period `L > 0` of `f` satisfies `∃ q > 0, L = 4 * q`. -/
theorem four_dvd_of_evPer_and_subseq_two_halfDensity
    {f : Nat → Bool} {r L : Nat} (hd : HalfDensity (subseq f 2 r))
    (hL : 0 < L) (hper : EvPer f L) :
    ∃ q : Nat, 0 < q ∧ L = 4 * q :=
  two_pow_succ_dvd_of_evPer_and_dyadic_subseq_halfDensity (K := 1) (Nat.le_refl 1) hL
    (fun a ha1 ha2 => by
      obtain rfl : a = 1 := by omega
      exact ⟨r, hd⟩)
    hper

/-- **Modulo-8 Period Divisibility from Stride-2 and Stride-4 `HalfDensity` Subsequences
(`eight_dvd_of_evPer_and_subseq_two_four_halfDensity`):** if `HalfDensity (subseq f 2 r₁)` and
`HalfDensity (subseq f 4 r₂)` hold, then every eventual period `L > 0` of `f` satisfies
`∃ q > 0, L = 8 * q`. -/
theorem eight_dvd_of_evPer_and_subseq_two_four_halfDensity
    {f : Nat → Bool} {r₁ r₂ L : Nat}
    (hd2 : HalfDensity (subseq f 2 r₁)) (hd4 : HalfDensity (subseq f 4 r₂))
    (hL : 0 < L) (hper : EvPer f L) :
    ∃ q : Nat, 0 < q ∧ L = 8 * q :=
  two_pow_succ_dvd_of_evPer_and_dyadic_subseq_halfDensity (K := 2) (by decide) hL
    (fun a ha1 ha2 => by
      have : a = 1 ∨ a = 2 := by omega
      rcases this with rfl | rfl
      · exact ⟨r₁, hd2⟩
      · exact ⟨r₂, hd4⟩)
    hper

/-- **Certificate-Free Exclusion of All Eventual Periods `1 <= L <= 7` from Stride-2 and Stride-4
`HalfDensity` (`not_evPer_le_seven_of_subseq_two_four_halfDensity`):** if
`HalfDensity (subseq f 2 r₁)` and `HalfDensity (subseq f 4 r₂)` hold, then `¬ EvPer f L` for
every `1 ≤ L ≤ 7`. -/
theorem not_evPer_le_seven_of_subseq_two_four_halfDensity
    {f : Nat → Bool} {r₁ r₂ L : Nat}
    (hd2 : HalfDensity (subseq f 2 r₁)) (hd4 : HalfDensity (subseq f 4 r₂))
    (hL1 : 1 ≤ L) (hL7 : L ≤ 7) :
    ¬ EvPer f L :=
  not_evPer_lt_two_pow_succ_of_dyadic_subseq_halfDensity (K := 2) (by decide) hL1 (by omega)
    (fun a ha1 ha2 => by
      have : a = 1 ∨ a = 2 := by omega
      rcases this with rfl | rfl
      · exact ⟨r₁, hd2⟩
      · exact ⟨r₂, hd4⟩)

/-! ### Exact Equivalence Between `(2 * M)`-Periodicity with Stride-`M` Subsequence `HalfDensity` and `M`-Anti-Periodicity -/

/-- **Progression Anti-Periodicity from `(2 * M)`-Periodicity and Stride-`M` `HalfDensity`
(`subseq_antiPeriodic_of_periodic_two_mul_and_subseq_halfDensity`):** if `0 < M`, `f` is
`(2 * M)`-periodic from `T₀` on (`∀ t ≥ T₀, f (t + 2 * M) = f t`), and
`HalfDensity (subseq f M r)` holds, then for every `k ≥ T₀`,
`subseq f M r (k + 1) = !subseq f M r k`. -/
theorem subseq_antiPeriodic_of_periodic_two_mul_and_subseq_halfDensity
    {f : Nat → Bool} {M T₀ r : Nat} (hM : 0 < M)
    (hper : ∀ t : Nat, T₀ ≤ t → f (t + 2 * M) = f t)
    (hhd : HalfDensity (subseq f M r)) :
    ∀ k : Nat, T₀ ≤ k → subseq f M r (k + 1) = !subseq f M r k := by
  intro k hk
  have hper_sub : ∀ j : Nat, k ≤ j → subseq f M r (j + 2) = subseq f M r j := by
    intro j hj
    simp only [subseq]
    have h1 : 1 * j ≤ M * j := Nat.mul_le_mul_right j hM
    have h2 : j * 1 ≤ j * M := Nat.mul_le_mul_left j hM
    have hmul : M * (j + 2) = M * j + 2 * M := by rw [Nat.mul_add]; omega
    have hmul' : (j + 2) * M = j * M + 2 * M := by rw [Nat.add_mul]
    have hstep : r + M * (j + 2) = (r + M * j) + 2 * M := by omega
    have hstep' : M * (j + 2) + r = (M * j + r) + 2 * M := by omega
    have hstep'' : (j + 2) * M + r = (j * M + r) + 2 * M := by omega
    have hstep''' : r + (j + 2) * M = (r + j * M) + 2 * M := by omega
    try (rw [hstep]; exact hper _ (by omega))
    try (rw [hstep']; exact hper _ (by omega))
    try (rw [hstep'']; exact hper _ (by omega))
    try (rw [hstep''']; exact hper _ (by omega))
  have hbal : 2 * winCount (subseq f M r) k 2 = 2 :=
    (periodic_halfDensity_iff_two_mul_winCount_eq (f := subseq f M r) (T := k) (L := 2) (by decide) hper_sub).mp hhd
  have hwin : winCount (subseq f M r) k 2 =
      (if subseq f M r k then 1 else 0) + (if subseq f M r (k + 1) then 1 else 0) := by
    simp [winCount]
  rw [hwin] at hbal
  revert hbal
  cases subseq f M r k <;> cases subseq f M r (k + 1) <;> decide

/-- **Global `M`-Anti-Periodicity from `(2 * M)`-Periodicity and All-Residue Stride-`M`
`HalfDensity` (`antiPeriodic_of_periodic_two_mul_and_all_subseq_halfDensity`):** if `0 < M`,
`∀ t ≥ T₀, f (t + 2 * M) = f t`, and `∀ r < M, HalfDensity (subseq f M r)`, then for every
`t ≥ M * T₀`, `f (t + M) = !f t`. -/
theorem antiPeriodic_of_periodic_two_mul_and_all_subseq_halfDensity
    {f : Nat → Bool} {M T₀ : Nat} (hM : 0 < M)
    (hper : ∀ t : Nat, T₀ ≤ t → f (t + 2 * M) = f t)
    (hhd : ∀ r : Nat, r < M → HalfDensity (subseq f M r)) :
    ∀ t : Nat, M * T₀ ≤ t → f (t + M) = !f t := by
  intro t ht
  let k := t / M
  let r := t % M
  have hr : r < M := Nat.mod_lt t hM
  have hdiv : M * k + r = t := Nat.div_add_mod t M
  have hdiv' : r + M * k = t := by omega
  have hdiv'' : k * M + r = t := by rw [Nat.mul_comm k M]; exact hdiv
  have hdiv''' : r + k * M = t := by omega
  have hk : T₀ ≤ k := by
    refine Classical.byContradiction fun hlt => ?_
    have hle : k + 1 ≤ T₀ := by omega
    have hmul : M * (k + 1) ≤ M * T₀ := Nat.mul_le_mul_left M hle
    rw [Nat.mul_add, Nat.mul_one] at hmul
    omega
  have hanti := subseq_antiPeriodic_of_periodic_two_mul_and_subseq_halfDensity hM hper (hhd r hr) k hk
  simp only [subseq] at hanti
  have hmul1 : M * (k + 1) = M * k + M := by rw [Nat.mul_add, Nat.mul_one]
  have hmul2 : (k + 1) * M = k * M + M := by rw [Nat.add_mul, Nat.one_mul]
  have hs1 : r + M * (k + 1) = t + M := by omega
  have hs2 : M * (k + 1) + r = t + M := by omega
  have hs3 : (k + 1) * M + r = t + M := by omega
  have hs4 : r + (k + 1) * M = t + M := by omega
  try (rw [hs1, hdiv'] at hanti; exact hanti)
  try (rw [hs2, hdiv] at hanti; exact hanti)
  try (rw [hs3, hdiv''] at hanti; exact hanti)
  try (rw [hs4, hdiv'''] at hanti; exact hanti)

/-- **Stride-`M` Subsequence `HalfDensity` from `M`-Anti-Periodicity
(`subseq_halfDensity_of_antiPeriodic`):** if `0 < M` and `∀ t ≥ T₀, f (t + M) = !f t`, then for
every residue `r : Nat`, `HalfDensity (subseq f M r)` holds. -/
theorem subseq_halfDensity_of_antiPeriodic
    {f : Nat → Bool} {M T₀ : Nat} (hM : 0 < M)
    (hanti : ∀ t : Nat, T₀ ≤ t → f (t + M) = !f t) (r : Nat) :
    HalfDensity (subseq f M r) := by
  have hanti_sub : ∀ k : Nat, T₀ ≤ k → subseq f M r (k + 1) = !subseq f M r k := by
    intro k hk
    simp only [subseq]
    have h1 : 1 * k ≤ M * k := Nat.mul_le_mul_right k hM
    have h2 : k * 1 ≤ k * M := Nat.mul_le_mul_left k hM
    have hmul1 : M * (k + 1) = M * k + M := by rw [Nat.mul_add, Nat.mul_one]
    have hmul2 : (k + 1) * M = k * M + M := by rw [Nat.add_mul, Nat.one_mul]
    have hs1 : r + M * (k + 1) = (r + M * k) + M := by omega
    have hs2 : M * (k + 1) + r = (M * k + r) + M := by omega
    have hs3 : (k + 1) * M + r = (k * M + r) + M := by omega
    have hs4 : r + (k + 1) * M = (r + k * M) + M := by omega
    try (rw [hs1]; exact hanti _ (by omega))
    try (rw [hs2]; exact hanti _ (by omega))
    try (rw [hs3]; exact hanti _ (by omega))
    try (rw [hs4]; exact hanti _ (by omega))
  have hper_sub : ∀ k : Nat, T₀ ≤ k → subseq f M r (k + 2) = subseq f M r k := by
    intro k hk
    rw [show k + 2 = (k + 1) + 1 by omega, hanti_sub (k + 1) (by omega), hanti_sub k hk, Bool.not_not]
  refine (periodic_halfDensity_iff_two_mul_winCount_eq (f := subseq f M r) (T := T₀) (L := 2) (by decide) hper_sub).mpr ?_
  have hwin : winCount (subseq f M r) T₀ 2 =
      (if subseq f M r T₀ then 1 else 0) + (if subseq f M r (T₀ + 1) then 1 else 0) := by
    simp [winCount]
  rw [hwin, hanti_sub T₀ (Nat.le_refl T₀)]
  cases subseq f M r T₀ <;> rfl

/-- **Exact Bidirectional Equivalence Between Eventual `M`-Anti-Periodicity and Eventual
`(2 * M)`-Periodicity with All-Residue Stride-`M` `HalfDensity`
(`evAntiPer_iff_evPer_two_mul_and_all_subseq_halfDensity`):** for `0 < M`,
`(∃ T, ∀ t ≥ T, f (t + M) = !f t) ↔ EvPer f (2 * M) ∧ ∀ r < M, HalfDensity (subseq f M r)`. -/
theorem evAntiPer_iff_evPer_two_mul_and_all_subseq_halfDensity
    {f : Nat → Bool} {M : Nat} (hM : 0 < M) :
    (∃ T : Nat, ∀ t : Nat, T ≤ t → f (t + M) = !f t) ↔
      (EvPer f (2 * M) ∧ ∀ r : Nat, r < M → HalfDensity (subseq f M r)) := by
  constructor
  · rintro ⟨T, hanti⟩
    refine ⟨⟨T, fun t ht => ?_⟩, fun r _ => subseq_halfDensity_of_antiPeriodic hM hanti r⟩
    rw [show t + 2 * M = (t + M) + M by omega, hanti (t + M) (by omega), hanti t ht, Bool.not_not]
  · rintro ⟨⟨T₀, hper⟩, hhd⟩
    exact ⟨M * T₀, antiPeriodic_of_periodic_two_mul_and_all_subseq_halfDensity hM hper hhd⟩

/-! ### Stride-Division Anti-Period Reduction (`d * q -> q`), Divisor-Stride `HalfDensity`, and the Dyadic Anti-Periodicity Tower -/

/-- **Stride-Division Anti-Period Reduction (`subseq_antiPeriodic_of_antiPeriodic_mul`):** for
`0 < d`, if `∀ t ≥ T₀, f (t + d * q) = !f t`, then for every residue `r : Nat` and `k ≥ T₀`,
`subseq f d r (k + q) = !subseq f d r k`. -/
theorem subseq_antiPeriodic_of_antiPeriodic_mul {f : Nat → Bool} {d q T₀ : Nat} (hd : 0 < d)
    (hanti : ∀ t : Nat, T₀ ≤ t → f (t + d * q) = !f t) (r : Nat) :
    ∀ k : Nat, T₀ ≤ k → subseq f d r (k + q) = !subseq f d r k := by
  intro k hk
  have hge : T₀ ≤ r + k * d := by
    have : T₀ * d ≤ k * d := Nat.mul_le_mul_right d hk
    have : T₀ ≤ T₀ * d := Nat.le_mul_of_pos_right T₀ hd
    omega
  simp only [subseq]
  have hs : r + (k + q) * d = (r + k * d) + d * q := by
    rw [Nat.add_mul, Nat.mul_comm q d, Nat.add_assoc]
  rw [hs]
  exact hanti (r + k * d) hge

/-- **Global `(d * q)`-Anti-Periodicity from All-Residue Stride-`d` `q`-Anti-Periodicity
(`antiPeriodic_mul_of_all_subseq_antiPeriodic`):** if `0 < d` and for every `r < d`,
`∀ k ≥ T₀, subseq f d r (k + q) = !subseq f d r k`, then `∀ t ≥ d * T₀, f (t + d * q) = !f t`. -/
theorem antiPeriodic_mul_of_all_subseq_antiPeriodic {f : Nat → Bool} {d q T₀ : Nat} (hd : 0 < d)
    (hsub : ∀ r : Nat, r < d → ∀ k : Nat, T₀ ≤ k → subseq f d r (k + q) = !subseq f d r k) :
    ∀ t : Nat, d * T₀ ≤ t → f (t + d * q) = !f t := by
  intro t ht
  let k := t / d
  let r := t % d
  have hr : r < d := Nat.mod_lt t hd
  have hdiv : d * k + r = t := Nat.div_add_mod t d
  have hk : T₀ ≤ k := by
    refine Classical.byContradiction fun hlt => ?_
    have hk1 : k + 1 ≤ T₀ := by omega
    have hmul : d * (k + 1) ≤ d * T₀ := Nat.mul_le_mul_left d hk1
    rw [Nat.mul_add, Nat.mul_one] at hmul
    omega
  have hstep := hsub r hr k hk
  simp only [subseq] at hstep
  have hd1 : r + k * d = t := by rw [Nat.mul_comm k d]; omega
  have ht1 : r + (k + q) * d = t + d * q := by
    rw [Nat.add_mul, Nat.mul_comm k d, Nat.mul_comm q d]; omega
  rw [ht1, hd1] at hstep
  exact hstep

/-- **Divisor-Stride `HalfDensity` from `(d * q)`-Anti-Periodicity
(`subseq_halfDensity_of_antiPeriodic_mul`):** if `0 < d`, `0 < q`, and
`∀ t ≥ T₀, f (t + d * q) = !f t`, then `HalfDensity (subseq f d r)` holds for every residue `r : Nat`. -/
theorem subseq_halfDensity_of_antiPeriodic_mul {f : Nat → Bool} {d q T₀ : Nat}
    (hd : 0 < d) (hq : 0 < q)
    (hanti : ∀ t : Nat, T₀ ≤ t → f (t + d * q) = !f t) (r : Nat) :
    HalfDensity (subseq f d r) :=
  halfDensity_of_antiperiodic hq ⟨T₀, subseq_antiPeriodic_of_antiPeriodic_mul hd hanti r⟩

/-- **Full Dyadic Tower Characterization of Eventual `(2 ^ K)`-Anti-Periodicity
(`evAntiPer_two_pow_iff_evPer_two_pow_succ_and_dyadic_tower_halfDensity`):** for any `K : Nat`,
`f` is eventually `(2 ^ K)`-anti-periodic (`∃ T, ∀ t ≥ T, f (t + 2 ^ K) = !f t`) if and only if
`EvPer f (2 ^ (K + 1))` holds and `HalfDensity (subseq f (2 ^ a) r)` holds at every intermediate
dyadic scale `a ≤ K` and residue `r < 2 ^ a`. -/
theorem evAntiPer_two_pow_iff_evPer_two_pow_succ_and_dyadic_tower_halfDensity
    (f : Nat → Bool) (K : Nat) :
    (∃ T : Nat, ∀ t : Nat, T ≤ t → f (t + 2 ^ K) = !f t) ↔
      (EvPer f (2 ^ (K + 1)) ∧ ∀ a : Nat, a ≤ K → ∀ r : Nat, r < 2 ^ a → HalfDensity (subseq f (2 ^ a) r)) := by
  have h2K : 0 < 2 ^ K := Nat.two_pow_pos K
  have hpow : 2 ^ (K + 1) = 2 * 2 ^ K := by rw [Nat.pow_succ]; omega
  constructor
  · rintro ⟨T, hanti⟩
    have hper : EvPer f (2 ^ (K + 1)) := by
      rw [hpow]
      exact ((evAntiPer_iff_evPer_two_mul_and_all_subseq_halfDensity h2K).mp ⟨T, hanti⟩).1
    refine ⟨hper, fun a ha r _ => ?_⟩
    have hsplit : 2 ^ K = 2 ^ a * 2 ^ (K - a) := by
      rw [← Nat.pow_add, Nat.add_sub_of_le ha]
    have hanti_mul : ∀ t : Nat, T ≤ t → f (t + 2 ^ a * 2 ^ (K - a)) = !f t := by
      intro t ht; rw [← hsplit]; exact hanti t ht
    exact subseq_halfDensity_of_antiPeriodic_mul (Nat.two_pow_pos a) (Nat.two_pow_pos (K - a)) hanti_mul r
  · rintro ⟨hper, htower⟩
    rw [hpow] at hper
    exact (evAntiPer_iff_evPer_two_mul_and_all_subseq_halfDensity h2K).mpr
      ⟨hper, fun r hr => htower K (Nat.le_refl K) r hr⟩

/-! ### Exact 2-Anti-Periodicity and Asymptotic Density `1/2` of the Eighth Left Diagonal `D 8` -/

/-- **Post-Reset XOR Recurrence of the Eighth Left Diagonal (`D_eight_step_eq_xor_D_three`):**
for every `t ≥ 7`, `D 8 (t + 1) = xor (D 3 t) (D 8 t)`. -/
theorem D_eight_step_eq_xor_D_three (t : Nat) (ht : 7 ≤ t) :
    D 8 (t + 1) = xor (D 3 t) (D 8 t) := by
  have hstep := D_step 6 t
  rw [Rule30WhiteSpacing.D_six_eq_D_three t (by omega),
      Rule30WhiteSpacing.D_seven_eq_false t ht, Bool.false_or] at hstep
  exact hstep

/-- **Exact 2-Anti-Periodicity of the Eighth Left Diagonal from `t = 7`
(`D_eight_antiperiodic_two`):** for every `t ≥ 7`, `D 8 (t + 2) = !D 8 t`. -/
theorem D_eight_antiperiodic_two (t : Nat) (ht : 7 ≤ t) :
    D 8 (t + 2) = !D 8 t := by
  have h1 := D_eight_step_eq_xor_D_three t ht
  have h2 := D_eight_step_eq_xor_D_three (t + 1) (by omega)
  have h3 := Rule30WhiteSpacing.D_three_succ t (by omega)
  rw [show t + 1 + 1 = t + 2 by omega, h1, h3] at h2
  revert h2
  cases D 3 t <;> cases D 8 t <;> cases D 8 (t + 2) <;> decide

/-- **Eventual 2-Anti-Periodicity of Diagonal `D 8` (`evAntiPer_D_eight`):**
`EvAntiPer (D 8) 2` holds with onset `7`. -/
theorem evAntiPer_D_eight : EvAntiPer (D 8) 2 :=
  ⟨7, D_eight_antiperiodic_two⟩

/-- **Unconditional Asymptotic Density `1/2` of Diagonal `D 8` (`halfDensity_D_eight`):**
`HalfDensity (D 8)` holds unconditionally. -/
theorem halfDensity_D_eight : HalfDensity (D 8) :=
  halfDensity_of_antiperiodic (by decide : 0 < 2) evAntiPer_D_eight

/-- **Second All-Black Shield Diagonal (`D_nine_eq_true`):** for every `t ≥ 8`, `D 9 t = true`. -/
theorem D_nine_eq_true : ∀ t : Nat, 8 ≤ t → D 9 t = true
  | 8, _ => by decide
  | t + 1, ht => by
    by_cases h8 : t < 8
    · have h_eq : t + 1 = 8 := by omega
      rw [h_eq]; decide
    · have ih := D_nine_eq_true t (by omega)
      have hstep := D_step 7 t
      rw [Rule30WhiteSpacing.D_seven_eq_false t (by omega), ih, Bool.or_true, Bool.false_xor] at hstep
      exact hstep

/-- **Diagonal `D 9` Is Eventually Black (`evBlack_D_nine`):** `EvBlack (D 9)` holds with onset `8`. -/
theorem evBlack_D_nine : Rule30WhiteSpacing.EvBlack (D 9) :=
  ⟨8, D_nine_eq_true⟩

/-- **Shielded Complement Transfer from `D 8` to `D 10` (`D_ten_succ_eq_not_D_eight`):**
for every `t ≥ 8`, `D 10 (t + 1) = !D 8 t`. -/
theorem D_ten_succ_eq_not_D_eight (t : Nat) (ht : 8 ≤ t) :
    D 10 (t + 1) = !D 8 t := by
  have hstep := D_step 8 t
  rw [D_nine_eq_true t ht, Bool.true_or, Bool.xor_true] at hstep
  exact hstep

/-- **Exact 2-Anti-Periodicity of the Tenth Left Diagonal (`D_ten_antiperiodic_two`):**
for every `t ≥ 9`, `D 10 (t + 2) = !D 10 t`. -/
theorem D_ten_antiperiodic_two (t : Nat) (ht : 9 ≤ t) :
    D 10 (t + 2) = !D 10 t := by
  have h1 := D_ten_succ_eq_not_D_eight (t - 1) (by omega)
  have h2 := D_ten_succ_eq_not_D_eight (t + 1) (by omega)
  have h8 := D_eight_antiperiodic_two (t - 1) (by omega)
  rw [show t - 1 + 1 = t by omega] at h1
  rw [show t - 1 + 2 = t + 1 by omega] at h8
  rw [h2, h8, h1]

/-- **Eventual 2-Anti-Periodicity of Diagonal `D 10` (`evAntiPer_D_ten`):**
`EvAntiPer (D 10) 2` holds with onset `9`. -/
theorem evAntiPer_D_ten : EvAntiPer (D 10) 2 :=
  ⟨9, D_ten_antiperiodic_two⟩

/-- **Unconditional Asymptotic Density `1/2` of Diagonal `D 10` (`halfDensity_D_ten`):**
`HalfDensity (D 10)` holds unconditionally. -/
theorem halfDensity_D_ten : HalfDensity (D 10) :=
  halfDensity_of_antiperiodic (by decide : 0 < 2) evAntiPer_D_ten

/-! ### The `(D 8, D 10)` Gray-Code Oscillator and Boolean Gate Laws for `D 11 .. D 15` -/

/-- **First-Step Oscillator Coupling (`D_eight_succ_eq_D_ten`):** for every `t ≥ 9`,
`D 8 (t + 1) = D 10 t`. -/
theorem D_eight_succ_eq_D_ten (t : Nat) (ht : 9 ≤ t) :
    D 8 (t + 1) = D 10 t := by
  have h10 := D_ten_succ_eq_not_D_eight (t - 1) (by omega)
  have h8 := D_eight_antiperiodic_two (t - 1) (by omega)
  rw [show t - 1 + 1 = t by omega] at h10
  rw [show t - 1 + 2 = t + 1 by omega] at h8
  rw [h8, h10]

/-- **NOR-Gate Law for the Eleventh Left Diagonal (`D_eleven_eq_nor_D_eight_D_ten`):**
for every `t ≥ 10`, `D 11 t = !(D 8 t || D 10 t)`. -/
theorem D_eleven_eq_nor_D_eight_D_ten : ∀ t : Nat, 10 ≤ t → D 11 t = !(D 8 t || D 10 t)
  | 10, _ => by decide
  | t + 1, ht => by
    by_cases h10 : t < 10
    · have h_eq : t + 1 = 10 := by omega
      rw [h_eq]; decide
    · have ih := D_eleven_eq_nor_D_eight_D_ten t (by omega)
      have hstep := D_step 9 t
      have h9 := D_nine_eq_true t (by omega)
      have h8s := D_eight_succ_eq_D_ten t (by omega)
      have h10s := D_ten_succ_eq_not_D_eight t (by omega)
      rw [h9, ih] at hstep
      rw [hstep, h8s, h10s]
      cases D 8 t <;> cases D 10 t <;> decide

/-- **NAND-Gate Law for the Twelfth Left Diagonal (`D_twelve_eq_nand_D_eight_D_ten`):**
for every `t ≥ 10`, `D 12 t = !(D 8 t && D 10 t)`. -/
theorem D_twelve_eq_nand_D_eight_D_ten : ∀ t : Nat, 10 ≤ t → D 12 t = !(D 8 t && D 10 t)
  | 10, _ => by decide
  | t + 1, ht => by
    by_cases h10 : t < 10
    · have h_eq : t + 1 = 10 := by omega
      rw [h_eq]; decide
    · have ih := D_twelve_eq_nand_D_eight_D_ten t (by omega)
      have h11 := D_eleven_eq_nor_D_eight_D_ten t (by omega)
      have hstep := D_step 10 t
      have h8s := D_eight_succ_eq_D_ten t (by omega)
      have h10s := D_ten_succ_eq_not_D_eight t (by omega)
      rw [h11, ih] at hstep
      rw [hstep, h8s, h10s]
      cases D 8 t <;> cases D 10 t <;> decide

/-- **Implication-Gate Law for the Thirteenth Left Diagonal (`D_thirteen_eq_or_not_D_eight_D_ten`):**
for every `t ≥ 11`, `D 13 t = (D 8 t || !D 10 t)`. -/
theorem D_thirteen_eq_or_not_D_eight_D_ten : ∀ t : Nat, 11 ≤ t → D 13 t = (D 8 t || !D 10 t)
  | 11, _ => by decide
  | t + 1, ht => by
    by_cases h11 : t < 11
    · have h_eq : t + 1 = 11 := by omega
      rw [h_eq]; decide
    · have ih := D_thirteen_eq_or_not_D_eight_D_ten t (by omega)
      have h11_eq := D_eleven_eq_nor_D_eight_D_ten t (by omega)
      have h12_eq := D_twelve_eq_nand_D_eight_D_ten t (by omega)
      have hstep := D_step 11 t
      have h8s := D_eight_succ_eq_D_ten t (by omega)
      have h10s := D_ten_succ_eq_not_D_eight t (by omega)
      rw [h11_eq, h12_eq, ih] at hstep
      rw [hstep, h8s, h10s]
      cases D 8 t <;> cases D 10 t <;> decide

/-- **Exact Phase-Locking of the Fourteenth and Eighth Left Diagonals (`D_fourteen_eq_D_eight`):**
for every `t ≥ 11`, `D 14 t = D 8 t`. -/
theorem D_fourteen_eq_D_eight : ∀ t : Nat, 11 ≤ t → D 14 t = D 8 t
  | 11, _ => by decide
  | t + 1, ht => by
    by_cases h11 : t < 11
    · have h_eq : t + 1 = 11 := by omega
      rw [h_eq]; decide
    · have ih := D_fourteen_eq_D_eight t (by omega)
      have h12_eq := D_twelve_eq_nand_D_eight_D_ten t (by omega)
      have h13_eq := D_thirteen_eq_or_not_D_eight_D_ten t (by omega)
      have hstep := D_step 12 t
      have h8s := D_eight_succ_eq_D_ten t (by omega)
      rw [h12_eq, h13_eq, ih] at hstep
      rw [hstep, h8s]
      cases D 8 t <;> cases D 10 t <;> decide

/-- **Exact 2-Anti-Periodicity of the Fourteenth Left Diagonal (`D_fourteen_antiperiodic_two`):**
for every `t ≥ 11`, `D 14 (t + 2) = !D 14 t`. -/
theorem D_fourteen_antiperiodic_two (t : Nat) (ht : 11 ≤ t) :
    D 14 (t + 2) = !D 14 t := by
  rw [D_fourteen_eq_D_eight (t + 2) (by omega), D_fourteen_eq_D_eight t ht]
  exact D_eight_antiperiodic_two t (by omega)

/-- **Eventual 2-Anti-Periodicity of Diagonal `D 14` (`evAntiPer_D_fourteen`):**
`EvAntiPer (D 14) 2` holds with onset `11`. -/
theorem evAntiPer_D_fourteen : EvAntiPer (D 14) 2 :=
  ⟨11, D_fourteen_antiperiodic_two⟩

/-- **Unconditional Asymptotic Density `1/2` of Diagonal `D 14` (`halfDensity_D_fourteen`):**
`HalfDensity (D 14)` holds unconditionally. -/
theorem halfDensity_D_fourteen : HalfDensity (D 14) :=
  halfDensity_of_antiperiodic (by decide : 0 < 2) evAntiPer_D_fourteen

/-- **Exact Phase-Locking of the Fifteenth and Tenth Left Diagonals (`D_fifteen_eq_D_ten`):**
for every `t ≥ 13`, `D 15 t = D 10 t`. -/
theorem D_fifteen_eq_D_ten : ∀ t : Nat, 13 ≤ t → D 15 t = D 10 t
  | 13, _ => by decide
  | t + 1, ht => by
    by_cases h13 : t < 13
    · have h_eq : t + 1 = 13 := by omega
      rw [h_eq]; decide
    · have ih := D_fifteen_eq_D_ten t (by omega)
      have h13_eq := D_thirteen_eq_or_not_D_eight_D_ten t (by omega)
      have h14_eq := D_fourteen_eq_D_eight t (by omega)
      have hstep := D_step 13 t
      have h10s := D_ten_succ_eq_not_D_eight t (by omega)
      rw [h13_eq, h14_eq, ih] at hstep
      rw [hstep, h10s]
      cases D 8 t <;> cases D 10 t <;> decide

/-- **Exact 2-Anti-Periodicity of the Fifteenth Left Diagonal (`D_fifteen_antiperiodic_two`):**
for every `t ≥ 13`, `D 15 (t + 2) = !D 15 t`. -/
theorem D_fifteen_antiperiodic_two (t : Nat) (ht : 13 ≤ t) :
    D 15 (t + 2) = !D 15 t := by
  rw [D_fifteen_eq_D_ten (t + 2) (by omega), D_fifteen_eq_D_ten t ht,
      D_ten_antiperiodic_two t (by omega)]

/-- **Eventual 2-Anti-Periodicity of Diagonal `D 15` (`evAntiPer_D_fifteen`):**
`EvAntiPer (D 15) 2` holds with onset `13`. -/
theorem evAntiPer_D_fifteen : EvAntiPer (D 15) 2 :=
  ⟨13, D_fifteen_antiperiodic_two⟩

/-- **Unconditional Asymptotic Density `1/2` of Diagonal `D 15` (`halfDensity_D_fifteen`):**
`HalfDensity (D 15)` holds unconditionally. -/
theorem halfDensity_D_fifteen : HalfDensity (D 15) :=
  halfDensity_of_antiperiodic (by decide : 0 < 2) evAntiPer_D_fifteen


end Rule30LeftAntiPeriod
end Ruliology.CellularAutomata
