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

end Rule30LeftAntiPeriod
end Ruliology.CellularAutomata
