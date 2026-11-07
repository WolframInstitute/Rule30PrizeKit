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

/-! ### Fast `O(j * t)` Dynamic-Programming Table and Cascade `D 16 .. D 31` (`R30-20261107-f15c70`) -/

theorem D_eq_false_of_two_mul_lt (j t : Nat) (h : 2 * t < j) : D j t = false := by
  unfold D
  exact cell_eq_false_of_gt t ((j : Int) - (t : Int)) (by omega)

private theorem d_0_0 : D 0 0 = true := D_zero 0
private theorem d_1_0 : D 1 0 = false := by decide
private theorem d_2_0 : D 2 0 = false := D_eq_false_of_two_mul_lt 2 0 (by decide)
private theorem d_0_1 : D 0 1 = true := D_zero 1
private theorem d_1_1 : D 1 1 = true := D_one 0
private theorem d_2_1 : D 2 1 = true := by have h := D_step 0 0; rw [d_0_0, d_1_0, d_2_0] at h; exact h
private theorem d_3_1 : D 3 1 = false := D_eq_false_of_two_mul_lt 3 1 (by decide)
private theorem d_4_1 : D 4 1 = false := D_eq_false_of_two_mul_lt 4 1 (by decide)
private theorem d_0_2 : D 0 2 = true := D_zero 2
private theorem d_1_2 : D 1 2 = true := D_one 1
private theorem d_2_2 : D 2 2 = false := by have h := D_step 0 1; rw [d_0_1, d_1_1, d_2_1] at h; exact h
private theorem d_3_2 : D 3 2 = false := by have h := D_step 1 1; rw [d_1_1, d_2_1, d_3_1] at h; exact h
private theorem d_4_2 : D 4 2 = true := by have h := D_step 2 1; rw [d_2_1, d_3_1, d_4_1] at h; exact h
private theorem d_5_2 : D 5 2 = false := D_eq_false_of_two_mul_lt 5 2 (by decide)
private theorem d_6_2 : D 6 2 = false := D_eq_false_of_two_mul_lt 6 2 (by decide)
private theorem d_0_3 : D 0 3 = true := D_zero 3
private theorem d_1_3 : D 1 3 = true := D_one 2
private theorem d_2_3 : D 2 3 = false := by have h := D_step 0 2; rw [d_0_2, d_1_2, d_2_2] at h; exact h
private theorem d_3_3 : D 3 3 = true := by have h := D_step 1 2; rw [d_1_2, d_2_2, d_3_2] at h; exact h
private theorem d_4_3 : D 4 3 = true := by have h := D_step 2 2; rw [d_2_2, d_3_2, d_4_2] at h; exact h
private theorem d_5_3 : D 5 3 = true := by have h := D_step 3 2; rw [d_3_2, d_4_2, d_5_2] at h; exact h
private theorem d_6_3 : D 6 3 = true := by have h := D_step 4 2; rw [d_4_2, d_5_2, d_6_2] at h; exact h
private theorem d_7_3 : D 7 3 = false := D_eq_false_of_two_mul_lt 7 3 (by decide)
private theorem d_8_3 : D 8 3 = false := D_eq_false_of_two_mul_lt 8 3 (by decide)
private theorem d_0_4 : D 0 4 = true := D_zero 4
private theorem d_1_4 : D 1 4 = true := D_one 3
private theorem d_2_4 : D 2 4 = false := by have h := D_step 0 3; rw [d_0_3, d_1_3, d_2_3] at h; exact h
private theorem d_3_4 : D 3 4 = false := by have h := D_step 1 3; rw [d_1_3, d_2_3, d_3_3] at h; exact h
private theorem d_4_4 : D 4 4 = true := by have h := D_step 2 3; rw [d_2_3, d_3_3, d_4_3] at h; exact h
private theorem d_5_4 : D 5 4 = false := by have h := D_step 3 3; rw [d_3_3, d_4_3, d_5_3] at h; exact h
private theorem d_6_4 : D 6 4 = false := by have h := D_step 4 3; rw [d_4_3, d_5_3, d_6_3] at h; exact h
private theorem d_7_4 : D 7 4 = false := by have h := D_step 5 3; rw [d_5_3, d_6_3, d_7_3] at h; exact h
private theorem d_8_4 : D 8 4 = true := by have h := D_step 6 3; rw [d_6_3, d_7_3, d_8_3] at h; exact h
private theorem d_9_4 : D 9 4 = false := D_eq_false_of_two_mul_lt 9 4 (by decide)
private theorem d_10_4 : D 10 4 = false := D_eq_false_of_two_mul_lt 10 4 (by decide)
private theorem d_0_5 : D 0 5 = true := D_zero 5
private theorem d_1_5 : D 1 5 = true := D_one 4
private theorem d_2_5 : D 2 5 = false := by have h := D_step 0 4; rw [d_0_4, d_1_4, d_2_4] at h; exact h
private theorem d_3_5 : D 3 5 = true := by have h := D_step 1 4; rw [d_1_4, d_2_4, d_3_4] at h; exact h
private theorem d_4_5 : D 4 5 = true := by have h := D_step 2 4; rw [d_2_4, d_3_4, d_4_4] at h; exact h
private theorem d_5_5 : D 5 5 = true := by have h := D_step 3 4; rw [d_3_4, d_4_4, d_5_4] at h; exact h
private theorem d_6_5 : D 6 5 = true := by have h := D_step 4 4; rw [d_4_4, d_5_4, d_6_4] at h; exact h
private theorem d_7_5 : D 7 5 = false := by have h := D_step 5 4; rw [d_5_4, d_6_4, d_7_4] at h; exact h
private theorem d_8_5 : D 8 5 = true := by have h := D_step 6 4; rw [d_6_4, d_7_4, d_8_4] at h; exact h
private theorem d_9_5 : D 9 5 = true := by have h := D_step 7 4; rw [d_7_4, d_8_4, d_9_4] at h; exact h
private theorem d_10_5 : D 10 5 = true := by have h := D_step 8 4; rw [d_8_4, d_9_4, d_10_4] at h; exact h
private theorem d_11_5 : D 11 5 = false := D_eq_false_of_two_mul_lt 11 5 (by decide)
private theorem d_12_5 : D 12 5 = false := D_eq_false_of_two_mul_lt 12 5 (by decide)
private theorem d_0_6 : D 0 6 = true := D_zero 6
private theorem d_1_6 : D 1 6 = true := D_one 5
private theorem d_2_6 : D 2 6 = false := by have h := D_step 0 5; rw [d_0_5, d_1_5, d_2_5] at h; exact h
private theorem d_3_6 : D 3 6 = false := by have h := D_step 1 5; rw [d_1_5, d_2_5, d_3_5] at h; exact h
private theorem d_4_6 : D 4 6 = true := by have h := D_step 2 5; rw [d_2_5, d_3_5, d_4_5] at h; exact h
private theorem d_5_6 : D 5 6 = false := by have h := D_step 3 5; rw [d_3_5, d_4_5, d_5_5] at h; exact h
private theorem d_6_6 : D 6 6 = false := by have h := D_step 4 5; rw [d_4_5, d_5_5, d_6_5] at h; exact h
private theorem d_7_6 : D 7 6 = false := by have h := D_step 5 5; rw [d_5_5, d_6_5, d_7_5] at h; exact h
private theorem d_8_6 : D 8 6 = false := by have h := D_step 6 5; rw [d_6_5, d_7_5, d_8_5] at h; exact h
private theorem d_9_6 : D 9 6 = true := by have h := D_step 7 5; rw [d_7_5, d_8_5, d_9_5] at h; exact h
private theorem d_10_6 : D 10 6 = false := by have h := D_step 8 5; rw [d_8_5, d_9_5, d_10_5] at h; exact h
private theorem d_11_6 : D 11 6 = false := by have h := D_step 9 5; rw [d_9_5, d_10_5, d_11_5] at h; exact h
private theorem d_12_6 : D 12 6 = true := by have h := D_step 10 5; rw [d_10_5, d_11_5, d_12_5] at h; exact h
private theorem d_13_6 : D 13 6 = false := D_eq_false_of_two_mul_lt 13 6 (by decide)
private theorem d_14_6 : D 14 6 = false := D_eq_false_of_two_mul_lt 14 6 (by decide)
private theorem d_0_7 : D 0 7 = true := D_zero 7
private theorem d_1_7 : D 1 7 = true := D_one 6
private theorem d_2_7 : D 2 7 = false := by have h := D_step 0 6; rw [d_0_6, d_1_6, d_2_6] at h; exact h
private theorem d_3_7 : D 3 7 = true := by have h := D_step 1 6; rw [d_1_6, d_2_6, d_3_6] at h; exact h
private theorem d_4_7 : D 4 7 = true := by have h := D_step 2 6; rw [d_2_6, d_3_6, d_4_6] at h; exact h
private theorem d_5_7 : D 5 7 = true := by have h := D_step 3 6; rw [d_3_6, d_4_6, d_5_6] at h; exact h
private theorem d_6_7 : D 6 7 = true := by have h := D_step 4 6; rw [d_4_6, d_5_6, d_6_6] at h; exact h
private theorem d_7_7 : D 7 7 = false := by have h := D_step 5 6; rw [d_5_6, d_6_6, d_7_6] at h; exact h
private theorem d_8_7 : D 8 7 = false := by have h := D_step 6 6; rw [d_6_6, d_7_6, d_8_6] at h; exact h
private theorem d_9_7 : D 9 7 = true := by have h := D_step 7 6; rw [d_7_6, d_8_6, d_9_6] at h; exact h
private theorem d_10_7 : D 10 7 = true := by have h := D_step 8 6; rw [d_8_6, d_9_6, d_10_6] at h; exact h
private theorem d_11_7 : D 11 7 = true := by have h := D_step 9 6; rw [d_9_6, d_10_6, d_11_6] at h; exact h
private theorem d_12_7 : D 12 7 = true := by have h := D_step 10 6; rw [d_10_6, d_11_6, d_12_6] at h; exact h
private theorem d_13_7 : D 13 7 = true := by have h := D_step 11 6; rw [d_11_6, d_12_6, d_13_6] at h; exact h
private theorem d_14_7 : D 14 7 = true := by have h := D_step 12 6; rw [d_12_6, d_13_6, d_14_6] at h; exact h
private theorem d_15_7 : D 15 7 = false := D_eq_false_of_two_mul_lt 15 7 (by decide)
private theorem d_16_7 : D 16 7 = false := D_eq_false_of_two_mul_lt 16 7 (by decide)
private theorem d_0_8 : D 0 8 = true := D_zero 8
private theorem d_1_8 : D 1 8 = true := D_one 7
private theorem d_2_8 : D 2 8 = false := by have h := D_step 0 7; rw [d_0_7, d_1_7, d_2_7] at h; exact h
private theorem d_3_8 : D 3 8 = false := by have h := D_step 1 7; rw [d_1_7, d_2_7, d_3_7] at h; exact h
private theorem d_4_8 : D 4 8 = true := by have h := D_step 2 7; rw [d_2_7, d_3_7, d_4_7] at h; exact h
private theorem d_5_8 : D 5 8 = false := by have h := D_step 3 7; rw [d_3_7, d_4_7, d_5_7] at h; exact h
private theorem d_6_8 : D 6 8 = false := by have h := D_step 4 7; rw [d_4_7, d_5_7, d_6_7] at h; exact h
private theorem d_7_8 : D 7 8 = false := by have h := D_step 5 7; rw [d_5_7, d_6_7, d_7_7] at h; exact h
private theorem d_8_8 : D 8 8 = true := by have h := D_step 6 7; rw [d_6_7, d_7_7, d_8_7] at h; exact h
private theorem d_9_8 : D 9 8 = true := by have h := D_step 7 7; rw [d_7_7, d_8_7, d_9_7] at h; exact h
private theorem d_10_8 : D 10 8 = true := by have h := D_step 8 7; rw [d_8_7, d_9_7, d_10_7] at h; exact h
private theorem d_11_8 : D 11 8 = false := by have h := D_step 9 7; rw [d_9_7, d_10_7, d_11_7] at h; exact h
private theorem d_12_8 : D 12 8 = false := by have h := D_step 10 7; rw [d_10_7, d_11_7, d_12_7] at h; exact h
private theorem d_13_8 : D 13 8 = false := by have h := D_step 11 7; rw [d_11_7, d_12_7, d_13_7] at h; exact h
private theorem d_14_8 : D 14 8 = false := by have h := D_step 12 7; rw [d_12_7, d_13_7, d_14_7] at h; exact h
private theorem d_15_8 : D 15 8 = false := by have h := D_step 13 7; rw [d_13_7, d_14_7, d_15_7] at h; exact h
private theorem d_16_8 : D 16 8 = true := by have h := D_step 14 7; rw [d_14_7, d_15_7, d_16_7] at h; exact h
private theorem d_17_8 : D 17 8 = false := D_eq_false_of_two_mul_lt 17 8 (by decide)
private theorem d_18_8 : D 18 8 = false := D_eq_false_of_two_mul_lt 18 8 (by decide)
private theorem d_0_9 : D 0 9 = true := D_zero 9
private theorem d_1_9 : D 1 9 = true := D_one 8
private theorem d_2_9 : D 2 9 = false := by have h := D_step 0 8; rw [d_0_8, d_1_8, d_2_8] at h; exact h
private theorem d_3_9 : D 3 9 = true := by have h := D_step 1 8; rw [d_1_8, d_2_8, d_3_8] at h; exact h
private theorem d_4_9 : D 4 9 = true := by have h := D_step 2 8; rw [d_2_8, d_3_8, d_4_8] at h; exact h
private theorem d_5_9 : D 5 9 = true := by have h := D_step 3 8; rw [d_3_8, d_4_8, d_5_8] at h; exact h
private theorem d_6_9 : D 6 9 = true := by have h := D_step 4 8; rw [d_4_8, d_5_8, d_6_8] at h; exact h
private theorem d_7_9 : D 7 9 = false := by have h := D_step 5 8; rw [d_5_8, d_6_8, d_7_8] at h; exact h
private theorem d_8_9 : D 8 9 = true := by have h := D_step 6 8; rw [d_6_8, d_7_8, d_8_8] at h; exact h
private theorem d_9_9 : D 9 9 = true := by have h := D_step 7 8; rw [d_7_8, d_8_8, d_9_8] at h; exact h
private theorem d_10_9 : D 10 9 = false := by have h := D_step 8 8; rw [d_8_8, d_9_8, d_10_8] at h; exact h
private theorem d_11_9 : D 11 9 = false := by have h := D_step 9 8; rw [d_9_8, d_10_8, d_11_8] at h; exact h
private theorem d_12_9 : D 12 9 = true := by have h := D_step 10 8; rw [d_10_8, d_11_8, d_12_8] at h; exact h
private theorem d_13_9 : D 13 9 = false := by have h := D_step 11 8; rw [d_11_8, d_12_8, d_13_8] at h; exact h
private theorem d_14_9 : D 14 9 = false := by have h := D_step 12 8; rw [d_12_8, d_13_8, d_14_8] at h; exact h
private theorem d_15_9 : D 15 9 = false := by have h := D_step 13 8; rw [d_13_8, d_14_8, d_15_8] at h; exact h
private theorem d_16_9 : D 16 9 = true := by have h := D_step 14 8; rw [d_14_8, d_15_8, d_16_8] at h; exact h
private theorem d_17_9 : D 17 9 = true := by have h := D_step 15 8; rw [d_15_8, d_16_8, d_17_8] at h; exact h
private theorem d_18_9 : D 18 9 = true := by have h := D_step 16 8; rw [d_16_8, d_17_8, d_18_8] at h; exact h
private theorem d_19_9 : D 19 9 = false := D_eq_false_of_two_mul_lt 19 9 (by decide)
private theorem d_20_9 : D 20 9 = false := D_eq_false_of_two_mul_lt 20 9 (by decide)
private theorem d_0_10 : D 0 10 = true := D_zero 10
private theorem d_1_10 : D 1 10 = true := D_one 9
private theorem d_2_10 : D 2 10 = false := by have h := D_step 0 9; rw [d_0_9, d_1_9, d_2_9] at h; exact h
private theorem d_3_10 : D 3 10 = false := by have h := D_step 1 9; rw [d_1_9, d_2_9, d_3_9] at h; exact h
private theorem d_4_10 : D 4 10 = true := by have h := D_step 2 9; rw [d_2_9, d_3_9, d_4_9] at h; exact h
private theorem d_5_10 : D 5 10 = false := by have h := D_step 3 9; rw [d_3_9, d_4_9, d_5_9] at h; exact h
private theorem d_6_10 : D 6 10 = false := by have h := D_step 4 9; rw [d_4_9, d_5_9, d_6_9] at h; exact h
private theorem d_7_10 : D 7 10 = false := by have h := D_step 5 9; rw [d_5_9, d_6_9, d_7_9] at h; exact h
private theorem d_8_10 : D 8 10 = false := by have h := D_step 6 9; rw [d_6_9, d_7_9, d_8_9] at h; exact h
private theorem d_9_10 : D 9 10 = true := by have h := D_step 7 9; rw [d_7_9, d_8_9, d_9_9] at h; exact h
private theorem d_10_10 : D 10 10 = false := by have h := D_step 8 9; rw [d_8_9, d_9_9, d_10_9] at h; exact h
private theorem d_11_10 : D 11 10 = true := by have h := D_step 9 9; rw [d_9_9, d_10_9, d_11_9] at h; exact h
private theorem d_12_10 : D 12 10 = true := by have h := D_step 10 9; rw [d_10_9, d_11_9, d_12_9] at h; exact h
private theorem d_13_10 : D 13 10 = true := by have h := D_step 11 9; rw [d_11_9, d_12_9, d_13_9] at h; exact h
private theorem d_14_10 : D 14 10 = true := by have h := D_step 12 9; rw [d_12_9, d_13_9, d_14_9] at h; exact h
private theorem d_15_10 : D 15 10 = false := by have h := D_step 13 9; rw [d_13_9, d_14_9, d_15_9] at h; exact h
private theorem d_16_10 : D 16 10 = true := by have h := D_step 14 9; rw [d_14_9, d_15_9, d_16_9] at h; exact h
private theorem d_17_10 : D 17 10 = true := by have h := D_step 15 9; rw [d_15_9, d_16_9, d_17_9] at h; exact h
private theorem d_18_10 : D 18 10 = false := by have h := D_step 16 9; rw [d_16_9, d_17_9, d_18_9] at h; exact h
private theorem d_19_10 : D 19 10 = false := by have h := D_step 17 9; rw [d_17_9, d_18_9, d_19_9] at h; exact h
private theorem d_20_10 : D 20 10 = true := by have h := D_step 18 9; rw [d_18_9, d_19_9, d_20_9] at h; exact h
private theorem d_21_10 : D 21 10 = false := D_eq_false_of_two_mul_lt 21 10 (by decide)
private theorem d_22_10 : D 22 10 = false := D_eq_false_of_two_mul_lt 22 10 (by decide)
private theorem d_0_11 : D 0 11 = true := D_zero 11
private theorem d_1_11 : D 1 11 = true := D_one 10
private theorem d_2_11 : D 2 11 = false := by have h := D_step 0 10; rw [d_0_10, d_1_10, d_2_10] at h; exact h
private theorem d_3_11 : D 3 11 = true := by have h := D_step 1 10; rw [d_1_10, d_2_10, d_3_10] at h; exact h
private theorem d_4_11 : D 4 11 = true := by have h := D_step 2 10; rw [d_2_10, d_3_10, d_4_10] at h; exact h
private theorem d_5_11 : D 5 11 = true := by have h := D_step 3 10; rw [d_3_10, d_4_10, d_5_10] at h; exact h
private theorem d_6_11 : D 6 11 = true := by have h := D_step 4 10; rw [d_4_10, d_5_10, d_6_10] at h; exact h
private theorem d_7_11 : D 7 11 = false := by have h := D_step 5 10; rw [d_5_10, d_6_10, d_7_10] at h; exact h
private theorem d_8_11 : D 8 11 = false := by have h := D_step 6 10; rw [d_6_10, d_7_10, d_8_10] at h; exact h
private theorem d_9_11 : D 9 11 = true := by have h := D_step 7 10; rw [d_7_10, d_8_10, d_9_10] at h; exact h
private theorem d_10_11 : D 10 11 = true := by have h := D_step 8 10; rw [d_8_10, d_9_10, d_10_10] at h; exact h
private theorem d_11_11 : D 11 11 = false := by have h := D_step 9 10; rw [d_9_10, d_10_10, d_11_10] at h; exact h
private theorem d_12_11 : D 12 11 = true := by have h := D_step 10 10; rw [d_10_10, d_11_10, d_12_10] at h; exact h
private theorem d_13_11 : D 13 11 = false := by have h := D_step 11 10; rw [d_11_10, d_12_10, d_13_10] at h; exact h
private theorem d_14_11 : D 14 11 = false := by have h := D_step 12 10; rw [d_12_10, d_13_10, d_14_10] at h; exact h
private theorem d_15_11 : D 15 11 = false := by have h := D_step 13 10; rw [d_13_10, d_14_10, d_15_10] at h; exact h
private theorem d_16_11 : D 16 11 = false := by have h := D_step 14 10; rw [d_14_10, d_15_10, d_16_10] at h; exact h
private theorem d_17_11 : D 17 11 = true := by have h := D_step 15 10; rw [d_15_10, d_16_10, d_17_10] at h; exact h
private theorem d_18_11 : D 18 11 = false := by have h := D_step 16 10; rw [d_16_10, d_17_10, d_18_10] at h; exact h
private theorem d_19_11 : D 19 11 = true := by have h := D_step 17 10; rw [d_17_10, d_18_10, d_19_10] at h; exact h
private theorem d_20_11 : D 20 11 = true := by have h := D_step 18 10; rw [d_18_10, d_19_10, d_20_10] at h; exact h
private theorem d_21_11 : D 21 11 = true := by have h := D_step 19 10; rw [d_19_10, d_20_10, d_21_10] at h; exact h
private theorem d_22_11 : D 22 11 = true := by have h := D_step 20 10; rw [d_20_10, d_21_10, d_22_10] at h; exact h
private theorem d_23_11 : D 23 11 = false := D_eq_false_of_two_mul_lt 23 11 (by decide)
private theorem d_24_11 : D 24 11 = false := D_eq_false_of_two_mul_lt 24 11 (by decide)
private theorem d_0_12 : D 0 12 = true := D_zero 12
private theorem d_1_12 : D 1 12 = true := D_one 11
private theorem d_2_12 : D 2 12 = false := by have h := D_step 0 11; rw [d_0_11, d_1_11, d_2_11] at h; exact h
private theorem d_3_12 : D 3 12 = false := by have h := D_step 1 11; rw [d_1_11, d_2_11, d_3_11] at h; exact h
private theorem d_4_12 : D 4 12 = true := by have h := D_step 2 11; rw [d_2_11, d_3_11, d_4_11] at h; exact h
private theorem d_5_12 : D 5 12 = false := by have h := D_step 3 11; rw [d_3_11, d_4_11, d_5_11] at h; exact h
private theorem d_6_12 : D 6 12 = false := by have h := D_step 4 11; rw [d_4_11, d_5_11, d_6_11] at h; exact h
private theorem d_7_12 : D 7 12 = false := by have h := D_step 5 11; rw [d_5_11, d_6_11, d_7_11] at h; exact h
private theorem d_8_12 : D 8 12 = true := by have h := D_step 6 11; rw [d_6_11, d_7_11, d_8_11] at h; exact h
private theorem d_9_12 : D 9 12 = true := by have h := D_step 7 11; rw [d_7_11, d_8_11, d_9_11] at h; exact h
private theorem d_10_12 : D 10 12 = true := by have h := D_step 8 11; rw [d_8_11, d_9_11, d_10_11] at h; exact h
private theorem d_11_12 : D 11 12 = false := by have h := D_step 9 11; rw [d_9_11, d_10_11, d_11_11] at h; exact h
private theorem d_12_12 : D 12 12 = false := by have h := D_step 10 11; rw [d_10_11, d_11_11, d_12_11] at h; exact h
private theorem d_13_12 : D 13 12 = true := by have h := D_step 11 11; rw [d_11_11, d_12_11, d_13_11] at h; exact h
private theorem d_14_12 : D 14 12 = true := by have h := D_step 12 11; rw [d_12_11, d_13_11, d_14_11] at h; exact h
private theorem d_15_12 : D 15 12 = false := by have h := D_step 13 11; rw [d_13_11, d_14_11, d_15_11] at h; exact h
private theorem d_16_12 : D 16 12 = false := by have h := D_step 14 11; rw [d_14_11, d_15_11, d_16_11] at h; exact h
private theorem d_17_12 : D 17 12 = true := by have h := D_step 15 11; rw [d_15_11, d_16_11, d_17_11] at h; exact h
private theorem d_18_12 : D 18 12 = true := by have h := D_step 16 11; rw [d_16_11, d_17_11, d_18_11] at h; exact h
private theorem d_19_12 : D 19 12 = false := by have h := D_step 17 11; rw [d_17_11, d_18_11, d_19_11] at h; exact h
private theorem d_20_12 : D 20 12 = true := by have h := D_step 18 11; rw [d_18_11, d_19_11, d_20_11] at h; exact h
private theorem d_21_12 : D 21 12 = false := by have h := D_step 19 11; rw [d_19_11, d_20_11, d_21_11] at h; exact h
private theorem d_22_12 : D 22 12 = false := by have h := D_step 20 11; rw [d_20_11, d_21_11, d_22_11] at h; exact h
private theorem d_23_12 : D 23 12 = false := by have h := D_step 21 11; rw [d_21_11, d_22_11, d_23_11] at h; exact h
private theorem d_24_12 : D 24 12 = true := by have h := D_step 22 11; rw [d_22_11, d_23_11, d_24_11] at h; exact h
private theorem d_25_12 : D 25 12 = false := D_eq_false_of_two_mul_lt 25 12 (by decide)
private theorem d_26_12 : D 26 12 = false := D_eq_false_of_two_mul_lt 26 12 (by decide)
private theorem d_0_13 : D 0 13 = true := D_zero 13
private theorem d_1_13 : D 1 13 = true := D_one 12
private theorem d_2_13 : D 2 13 = false := by have h := D_step 0 12; rw [d_0_12, d_1_12, d_2_12] at h; exact h
private theorem d_3_13 : D 3 13 = true := by have h := D_step 1 12; rw [d_1_12, d_2_12, d_3_12] at h; exact h
private theorem d_4_13 : D 4 13 = true := by have h := D_step 2 12; rw [d_2_12, d_3_12, d_4_12] at h; exact h
private theorem d_5_13 : D 5 13 = true := by have h := D_step 3 12; rw [d_3_12, d_4_12, d_5_12] at h; exact h
private theorem d_6_13 : D 6 13 = true := by have h := D_step 4 12; rw [d_4_12, d_5_12, d_6_12] at h; exact h
private theorem d_7_13 : D 7 13 = false := by have h := D_step 5 12; rw [d_5_12, d_6_12, d_7_12] at h; exact h
private theorem d_8_13 : D 8 13 = true := by have h := D_step 6 12; rw [d_6_12, d_7_12, d_8_12] at h; exact h
private theorem d_9_13 : D 9 13 = true := by have h := D_step 7 12; rw [d_7_12, d_8_12, d_9_12] at h; exact h
private theorem d_10_13 : D 10 13 = false := by have h := D_step 8 12; rw [d_8_12, d_9_12, d_10_12] at h; exact h
private theorem d_11_13 : D 11 13 = false := by have h := D_step 9 12; rw [d_9_12, d_10_12, d_11_12] at h; exact h
private theorem d_12_13 : D 12 13 = true := by have h := D_step 10 12; rw [d_10_12, d_11_12, d_12_12] at h; exact h
private theorem d_13_13 : D 13 13 = true := by have h := D_step 11 12; rw [d_11_12, d_12_12, d_13_12] at h; exact h
private theorem d_14_13 : D 14 13 = true := by have h := D_step 12 12; rw [d_12_12, d_13_12, d_14_12] at h; exact h
private theorem d_15_13 : D 15 13 = false := by have h := D_step 13 12; rw [d_13_12, d_14_12, d_15_12] at h; exact h
private theorem d_16_13 : D 16 13 = true := by have h := D_step 14 12; rw [d_14_12, d_15_12, d_16_12] at h; exact h
private theorem d_17_13 : D 17 13 = true := by have h := D_step 15 12; rw [d_15_12, d_16_12, d_17_12] at h; exact h
private theorem d_18_13 : D 18 13 = true := by have h := D_step 16 12; rw [d_16_12, d_17_12, d_18_12] at h; exact h
private theorem d_19_13 : D 19 13 = false := by have h := D_step 17 12; rw [d_17_12, d_18_12, d_19_12] at h; exact h
private theorem d_20_13 : D 20 13 = false := by have h := D_step 18 12; rw [d_18_12, d_19_12, d_20_12] at h; exact h
private theorem d_21_13 : D 21 13 = true := by have h := D_step 19 12; rw [d_19_12, d_20_12, d_21_12] at h; exact h
private theorem d_22_13 : D 22 13 = true := by have h := D_step 20 12; rw [d_20_12, d_21_12, d_22_12] at h; exact h
private theorem d_23_13 : D 23 13 = false := by have h := D_step 21 12; rw [d_21_12, d_22_12, d_23_12] at h; exact h
private theorem d_24_13 : D 24 13 = true := by have h := D_step 22 12; rw [d_22_12, d_23_12, d_24_12] at h; exact h
private theorem d_25_13 : D 25 13 = true := by have h := D_step 23 12; rw [d_23_12, d_24_12, d_25_12] at h; exact h
private theorem d_26_13 : D 26 13 = true := by have h := D_step 24 12; rw [d_24_12, d_25_12, d_26_12] at h; exact h
private theorem d_27_13 : D 27 13 = false := D_eq_false_of_two_mul_lt 27 13 (by decide)
private theorem d_28_13 : D 28 13 = false := D_eq_false_of_two_mul_lt 28 13 (by decide)
private theorem d_0_14 : D 0 14 = true := D_zero 14
private theorem d_1_14 : D 1 14 = true := D_one 13
private theorem d_2_14 : D 2 14 = false := by have h := D_step 0 13; rw [d_0_13, d_1_13, d_2_13] at h; exact h
private theorem d_3_14 : D 3 14 = false := by have h := D_step 1 13; rw [d_1_13, d_2_13, d_3_13] at h; exact h
private theorem d_4_14 : D 4 14 = true := by have h := D_step 2 13; rw [d_2_13, d_3_13, d_4_13] at h; exact h
private theorem d_5_14 : D 5 14 = false := by have h := D_step 3 13; rw [d_3_13, d_4_13, d_5_13] at h; exact h
private theorem d_6_14 : D 6 14 = false := by have h := D_step 4 13; rw [d_4_13, d_5_13, d_6_13] at h; exact h
private theorem d_7_14 : D 7 14 = false := by have h := D_step 5 13; rw [d_5_13, d_6_13, d_7_13] at h; exact h
private theorem d_8_14 : D 8 14 = false := by have h := D_step 6 13; rw [d_6_13, d_7_13, d_8_13] at h; exact h
private theorem d_9_14 : D 9 14 = true := by have h := D_step 7 13; rw [d_7_13, d_8_13, d_9_13] at h; exact h
private theorem d_10_14 : D 10 14 = false := by have h := D_step 8 13; rw [d_8_13, d_9_13, d_10_13] at h; exact h
private theorem d_11_14 : D 11 14 = true := by have h := D_step 9 13; rw [d_9_13, d_10_13, d_11_13] at h; exact h
private theorem d_12_14 : D 12 14 = true := by have h := D_step 10 13; rw [d_10_13, d_11_13, d_12_13] at h; exact h
private theorem d_13_14 : D 13 14 = true := by have h := D_step 11 13; rw [d_11_13, d_12_13, d_13_13] at h; exact h
private theorem d_14_14 : D 14 14 = false := by have h := D_step 12 13; rw [d_12_13, d_13_13, d_14_13] at h; exact h
private theorem d_15_14 : D 15 14 = false := by have h := D_step 13 13; rw [d_13_13, d_14_13, d_15_13] at h; exact h
private theorem d_16_14 : D 16 14 = false := by have h := D_step 14 13; rw [d_14_13, d_15_13, d_16_13] at h; exact h
private theorem d_17_14 : D 17 14 = true := by have h := D_step 15 13; rw [d_15_13, d_16_13, d_17_13] at h; exact h
private theorem d_18_14 : D 18 14 = false := by have h := D_step 16 13; rw [d_16_13, d_17_13, d_18_13] at h; exact h
private theorem d_19_14 : D 19 14 = false := by have h := D_step 17 13; rw [d_17_13, d_18_13, d_19_13] at h; exact h
private theorem d_20_14 : D 20 14 = true := by have h := D_step 18 13; rw [d_18_13, d_19_13, d_20_13] at h; exact h
private theorem d_21_14 : D 21 14 = true := by have h := D_step 19 13; rw [d_19_13, d_20_13, d_21_13] at h; exact h
private theorem d_22_14 : D 22 14 = true := by have h := D_step 20 13; rw [d_20_13, d_21_13, d_22_13] at h; exact h
private theorem d_23_14 : D 23 14 = false := by have h := D_step 21 13; rw [d_21_13, d_22_13, d_23_13] at h; exact h
private theorem d_24_14 : D 24 14 = false := by have h := D_step 22 13; rw [d_22_13, d_23_13, d_24_13] at h; exact h
private theorem d_25_14 : D 25 14 = true := by have h := D_step 23 13; rw [d_23_13, d_24_13, d_25_13] at h; exact h
private theorem d_26_14 : D 26 14 = false := by have h := D_step 24 13; rw [d_24_13, d_25_13, d_26_13] at h; exact h
private theorem d_27_14 : D 27 14 = false := by have h := D_step 25 13; rw [d_25_13, d_26_13, d_27_13] at h; exact h
private theorem d_28_14 : D 28 14 = true := by have h := D_step 26 13; rw [d_26_13, d_27_13, d_28_13] at h; exact h
private theorem d_29_14 : D 29 14 = false := D_eq_false_of_two_mul_lt 29 14 (by decide)
private theorem d_30_14 : D 30 14 = false := D_eq_false_of_two_mul_lt 30 14 (by decide)
private theorem d_0_15 : D 0 15 = true := D_zero 15
private theorem d_1_15 : D 1 15 = true := D_one 14
private theorem d_2_15 : D 2 15 = false := by have h := D_step 0 14; rw [d_0_14, d_1_14, d_2_14] at h; exact h
private theorem d_3_15 : D 3 15 = true := by have h := D_step 1 14; rw [d_1_14, d_2_14, d_3_14] at h; exact h
private theorem d_4_15 : D 4 15 = true := by have h := D_step 2 14; rw [d_2_14, d_3_14, d_4_14] at h; exact h
private theorem d_5_15 : D 5 15 = true := by have h := D_step 3 14; rw [d_3_14, d_4_14, d_5_14] at h; exact h
private theorem d_6_15 : D 6 15 = true := by have h := D_step 4 14; rw [d_4_14, d_5_14, d_6_14] at h; exact h
private theorem d_7_15 : D 7 15 = false := by have h := D_step 5 14; rw [d_5_14, d_6_14, d_7_14] at h; exact h
private theorem d_8_15 : D 8 15 = false := by have h := D_step 6 14; rw [d_6_14, d_7_14, d_8_14] at h; exact h
private theorem d_9_15 : D 9 15 = true := by have h := D_step 7 14; rw [d_7_14, d_8_14, d_9_14] at h; exact h
private theorem d_10_15 : D 10 15 = true := by have h := D_step 8 14; rw [d_8_14, d_9_14, d_10_14] at h; exact h
private theorem d_11_15 : D 11 15 = false := by have h := D_step 9 14; rw [d_9_14, d_10_14, d_11_14] at h; exact h
private theorem d_12_15 : D 12 15 = true := by have h := D_step 10 14; rw [d_10_14, d_11_14, d_12_14] at h; exact h
private theorem d_13_15 : D 13 15 = false := by have h := D_step 11 14; rw [d_11_14, d_12_14, d_13_14] at h; exact h
private theorem d_14_15 : D 14 15 = false := by have h := D_step 12 14; rw [d_12_14, d_13_14, d_14_14] at h; exact h
private theorem d_15_15 : D 15 15 = true := by have h := D_step 13 14; rw [d_13_14, d_14_14, d_15_14] at h; exact h
private theorem d_16_15 : D 16 15 = false := by have h := D_step 14 14; rw [d_14_14, d_15_14, d_16_14] at h; exact h
private theorem d_17_15 : D 17 15 = true := by have h := D_step 15 14; rw [d_15_14, d_16_14, d_17_14] at h; exact h
private theorem d_18_15 : D 18 15 = true := by have h := D_step 16 14; rw [d_16_14, d_17_14, d_18_14] at h; exact h
private theorem d_19_15 : D 19 15 = true := by have h := D_step 17 14; rw [d_17_14, d_18_14, d_19_14] at h; exact h
private theorem d_20_15 : D 20 15 = true := by have h := D_step 18 14; rw [d_18_14, d_19_14, d_20_14] at h; exact h
private theorem d_21_15 : D 21 15 = true := by have h := D_step 19 14; rw [d_19_14, d_20_14, d_21_14] at h; exact h
private theorem d_22_15 : D 22 15 = false := by have h := D_step 20 14; rw [d_20_14, d_21_14, d_22_14] at h; exact h
private theorem d_23_15 : D 23 15 = false := by have h := D_step 21 14; rw [d_21_14, d_22_14, d_23_14] at h; exact h
private theorem d_24_15 : D 24 15 = true := by have h := D_step 22 14; rw [d_22_14, d_23_14, d_24_14] at h; exact h
private theorem d_25_15 : D 25 15 = true := by have h := D_step 23 14; rw [d_23_14, d_24_14, d_25_14] at h; exact h
private theorem d_26_15 : D 26 15 = true := by have h := D_step 24 14; rw [d_24_14, d_25_14, d_26_14] at h; exact h
private theorem d_27_15 : D 27 15 = true := by have h := D_step 25 14; rw [d_25_14, d_26_14, d_27_14] at h; exact h
private theorem d_28_15 : D 28 15 = true := by have h := D_step 26 14; rw [d_26_14, d_27_14, d_28_14] at h; exact h
private theorem d_29_15 : D 29 15 = true := by have h := D_step 27 14; rw [d_27_14, d_28_14, d_29_14] at h; exact h
private theorem d_30_15 : D 30 15 = true := by have h := D_step 28 14; rw [d_28_14, d_29_14, d_30_14] at h; exact h
private theorem d_0_16 : D 0 16 = true := D_zero 16
private theorem d_1_16 : D 1 16 = true := D_one 15
private theorem d_2_16 : D 2 16 = false := by have h := D_step 0 15; rw [d_0_15, d_1_15, d_2_15] at h; exact h
private theorem d_3_16 : D 3 16 = false := by have h := D_step 1 15; rw [d_1_15, d_2_15, d_3_15] at h; exact h
private theorem d_4_16 : D 4 16 = true := by have h := D_step 2 15; rw [d_2_15, d_3_15, d_4_15] at h; exact h
private theorem d_5_16 : D 5 16 = false := by have h := D_step 3 15; rw [d_3_15, d_4_15, d_5_15] at h; exact h
private theorem d_6_16 : D 6 16 = false := by have h := D_step 4 15; rw [d_4_15, d_5_15, d_6_15] at h; exact h
private theorem d_7_16 : D 7 16 = false := by have h := D_step 5 15; rw [d_5_15, d_6_15, d_7_15] at h; exact h
private theorem d_8_16 : D 8 16 = true := by have h := D_step 6 15; rw [d_6_15, d_7_15, d_8_15] at h; exact h
private theorem d_9_16 : D 9 16 = true := by have h := D_step 7 15; rw [d_7_15, d_8_15, d_9_15] at h; exact h
private theorem d_10_16 : D 10 16 = true := by have h := D_step 8 15; rw [d_8_15, d_9_15, d_10_15] at h; exact h
private theorem d_11_16 : D 11 16 = false := by have h := D_step 9 15; rw [d_9_15, d_10_15, d_11_15] at h; exact h
private theorem d_12_16 : D 12 16 = false := by have h := D_step 10 15; rw [d_10_15, d_11_15, d_12_15] at h; exact h
private theorem d_13_16 : D 13 16 = true := by have h := D_step 11 15; rw [d_11_15, d_12_15, d_13_15] at h; exact h
private theorem d_14_16 : D 14 16 = true := by have h := D_step 12 15; rw [d_12_15, d_13_15, d_14_15] at h; exact h
private theorem d_15_16 : D 15 16 = true := by have h := D_step 13 15; rw [d_13_15, d_14_15, d_15_15] at h; exact h
private theorem d_16_16 : D 16 16 = true := by have h := D_step 14 15; rw [d_14_15, d_15_15, d_16_15] at h; exact h
private theorem d_17_16 : D 17 16 = false := by have h := D_step 15 15; rw [d_15_15, d_16_15, d_17_15] at h; exact h
private theorem d_18_16 : D 18 16 = true := by have h := D_step 16 15; rw [d_16_15, d_17_15, d_18_15] at h; exact h
private theorem d_19_16 : D 19 16 = false := by have h := D_step 17 15; rw [d_17_15, d_18_15, d_19_15] at h; exact h
private theorem d_20_16 : D 20 16 = false := by have h := D_step 18 15; rw [d_18_15, d_19_15, d_20_15] at h; exact h
private theorem d_21_16 : D 21 16 = false := by have h := D_step 19 15; rw [d_19_15, d_20_15, d_21_15] at h; exact h
private theorem d_22_16 : D 22 16 = false := by have h := D_step 20 15; rw [d_20_15, d_21_15, d_22_15] at h; exact h
private theorem d_23_16 : D 23 16 = true := by have h := D_step 21 15; rw [d_21_15, d_22_15, d_23_15] at h; exact h
private theorem d_24_16 : D 24 16 = true := by have h := D_step 22 15; rw [d_22_15, d_23_15, d_24_15] at h; exact h
private theorem d_25_16 : D 25 16 = true := by have h := D_step 23 15; rw [d_23_15, d_24_15, d_25_15] at h; exact h
private theorem d_26_16 : D 26 16 = false := by have h := D_step 24 15; rw [d_24_15, d_25_15, d_26_15] at h; exact h
private theorem d_27_16 : D 27 16 = false := by have h := D_step 25 15; rw [d_25_15, d_26_15, d_27_15] at h; exact h
private theorem d_28_16 : D 28 16 = false := by have h := D_step 26 15; rw [d_26_15, d_27_15, d_28_15] at h; exact h
private theorem d_29_16 : D 29 16 = false := by have h := D_step 27 15; rw [d_27_15, d_28_15, d_29_15] at h; exact h
private theorem d_30_16 : D 30 16 = false := by have h := D_step 28 15; rw [d_28_15, d_29_15, d_30_15] at h; exact h
private theorem d_0_17 : D 0 17 = true := D_zero 17
private theorem d_1_17 : D 1 17 = true := D_one 16
private theorem d_2_17 : D 2 17 = false := by have h := D_step 0 16; rw [d_0_16, d_1_16, d_2_16] at h; exact h
private theorem d_3_17 : D 3 17 = true := by have h := D_step 1 16; rw [d_1_16, d_2_16, d_3_16] at h; exact h
private theorem d_4_17 : D 4 17 = true := by have h := D_step 2 16; rw [d_2_16, d_3_16, d_4_16] at h; exact h
private theorem d_5_17 : D 5 17 = true := by have h := D_step 3 16; rw [d_3_16, d_4_16, d_5_16] at h; exact h
private theorem d_6_17 : D 6 17 = true := by have h := D_step 4 16; rw [d_4_16, d_5_16, d_6_16] at h; exact h
private theorem d_7_17 : D 7 17 = false := by have h := D_step 5 16; rw [d_5_16, d_6_16, d_7_16] at h; exact h
private theorem d_8_17 : D 8 17 = true := by have h := D_step 6 16; rw [d_6_16, d_7_16, d_8_16] at h; exact h
private theorem d_9_17 : D 9 17 = true := by have h := D_step 7 16; rw [d_7_16, d_8_16, d_9_16] at h; exact h
private theorem d_10_17 : D 10 17 = false := by have h := D_step 8 16; rw [d_8_16, d_9_16, d_10_16] at h; exact h
private theorem d_11_17 : D 11 17 = false := by have h := D_step 9 16; rw [d_9_16, d_10_16, d_11_16] at h; exact h
private theorem d_12_17 : D 12 17 = true := by have h := D_step 10 16; rw [d_10_16, d_11_16, d_12_16] at h; exact h
private theorem d_13_17 : D 13 17 = true := by have h := D_step 11 16; rw [d_11_16, d_12_16, d_13_16] at h; exact h
private theorem d_14_17 : D 14 17 = true := by have h := D_step 12 16; rw [d_12_16, d_13_16, d_14_16] at h; exact h
private theorem d_15_17 : D 15 17 = false := by have h := D_step 13 16; rw [d_13_16, d_14_16, d_15_16] at h; exact h
private theorem d_16_17 : D 16 17 = false := by have h := D_step 14 16; rw [d_14_16, d_15_16, d_16_16] at h; exact h
private theorem d_17_17 : D 17 17 = false := by have h := D_step 15 16; rw [d_15_16, d_16_16, d_17_16] at h; exact h
private theorem d_18_17 : D 18 17 = false := by have h := D_step 16 16; rw [d_16_16, d_17_16, d_18_16] at h; exact h
private theorem d_19_17 : D 19 17 = true := by have h := D_step 17 16; rw [d_17_16, d_18_16, d_19_16] at h; exact h
private theorem d_20_17 : D 20 17 = true := by have h := D_step 18 16; rw [d_18_16, d_19_16, d_20_16] at h; exact h
private theorem d_21_17 : D 21 17 = false := by have h := D_step 19 16; rw [d_19_16, d_20_16, d_21_16] at h; exact h
private theorem d_22_17 : D 22 17 = false := by have h := D_step 20 16; rw [d_20_16, d_21_16, d_22_16] at h; exact h
private theorem d_23_17 : D 23 17 = true := by have h := D_step 21 16; rw [d_21_16, d_22_16, d_23_16] at h; exact h
private theorem d_24_17 : D 24 17 = true := by have h := D_step 22 16; rw [d_22_16, d_23_16, d_24_16] at h; exact h
private theorem d_25_17 : D 25 17 = false := by have h := D_step 23 16; rw [d_23_16, d_24_16, d_25_16] at h; exact h
private theorem d_26_17 : D 26 17 = false := by have h := D_step 24 16; rw [d_24_16, d_25_16, d_26_16] at h; exact h
private theorem d_27_17 : D 27 17 = true := by have h := D_step 25 16; rw [d_25_16, d_26_16, d_27_16] at h; exact h
private theorem d_28_17 : D 28 17 = false := by have h := D_step 26 16; rw [d_26_16, d_27_16, d_28_16] at h; exact h
private theorem d_29_17 : D 29 17 = false := by have h := D_step 27 16; rw [d_27_16, d_28_16, d_29_16] at h; exact h
private theorem d_30_17 : D 30 17 = false := by have h := D_step 28 16; rw [d_28_16, d_29_16, d_30_16] at h; exact h
private theorem d_0_18 : D 0 18 = true := D_zero 18
private theorem d_1_18 : D 1 18 = true := D_one 17
private theorem d_2_18 : D 2 18 = false := by have h := D_step 0 17; rw [d_0_17, d_1_17, d_2_17] at h; exact h
private theorem d_3_18 : D 3 18 = false := by have h := D_step 1 17; rw [d_1_17, d_2_17, d_3_17] at h; exact h
private theorem d_4_18 : D 4 18 = true := by have h := D_step 2 17; rw [d_2_17, d_3_17, d_4_17] at h; exact h
private theorem d_5_18 : D 5 18 = false := by have h := D_step 3 17; rw [d_3_17, d_4_17, d_5_17] at h; exact h
private theorem d_6_18 : D 6 18 = false := by have h := D_step 4 17; rw [d_4_17, d_5_17, d_6_17] at h; exact h
private theorem d_7_18 : D 7 18 = false := by have h := D_step 5 17; rw [d_5_17, d_6_17, d_7_17] at h; exact h
private theorem d_8_18 : D 8 18 = false := by have h := D_step 6 17; rw [d_6_17, d_7_17, d_8_17] at h; exact h
private theorem d_9_18 : D 9 18 = true := by have h := D_step 7 17; rw [d_7_17, d_8_17, d_9_17] at h; exact h
private theorem d_10_18 : D 10 18 = false := by have h := D_step 8 17; rw [d_8_17, d_9_17, d_10_17] at h; exact h
private theorem d_11_18 : D 11 18 = true := by have h := D_step 9 17; rw [d_9_17, d_10_17, d_11_17] at h; exact h
private theorem d_12_18 : D 12 18 = true := by have h := D_step 10 17; rw [d_10_17, d_11_17, d_12_17] at h; exact h
private theorem d_13_18 : D 13 18 = true := by have h := D_step 11 17; rw [d_11_17, d_12_17, d_13_17] at h; exact h
private theorem d_14_18 : D 14 18 = false := by have h := D_step 12 17; rw [d_12_17, d_13_17, d_14_17] at h; exact h
private theorem d_15_18 : D 15 18 = false := by have h := D_step 13 17; rw [d_13_17, d_14_17, d_15_17] at h; exact h
private theorem d_16_18 : D 16 18 = true := by have h := D_step 14 17; rw [d_14_17, d_15_17, d_16_17] at h; exact h
private theorem d_17_18 : D 17 18 = false := by have h := D_step 15 17; rw [d_15_17, d_16_17, d_17_17] at h; exact h
private theorem d_18_18 : D 18 18 = false := by have h := D_step 16 17; rw [d_16_17, d_17_17, d_18_17] at h; exact h
private theorem d_19_18 : D 19 18 = true := by have h := D_step 17 17; rw [d_17_17, d_18_17, d_19_17] at h; exact h
private theorem d_20_18 : D 20 18 = true := by have h := D_step 18 17; rw [d_18_17, d_19_17, d_20_17] at h; exact h
private theorem d_21_18 : D 21 18 = false := by have h := D_step 19 17; rw [d_19_17, d_20_17, d_21_17] at h; exact h
private theorem d_22_18 : D 22 18 = true := by have h := D_step 20 17; rw [d_20_17, d_21_17, d_22_17] at h; exact h
private theorem d_23_18 : D 23 18 = true := by have h := D_step 21 17; rw [d_21_17, d_22_17, d_23_17] at h; exact h
private theorem d_24_18 : D 24 18 = true := by have h := D_step 22 17; rw [d_22_17, d_23_17, d_24_17] at h; exact h
private theorem d_25_18 : D 25 18 = false := by have h := D_step 23 17; rw [d_23_17, d_24_17, d_25_17] at h; exact h
private theorem d_26_18 : D 26 18 = true := by have h := D_step 24 17; rw [d_24_17, d_25_17, d_26_17] at h; exact h
private theorem d_27_18 : D 27 18 = true := by have h := D_step 25 17; rw [d_25_17, d_26_17, d_27_17] at h; exact h
private theorem d_28_18 : D 28 18 = true := by have h := D_step 26 17; rw [d_26_17, d_27_17, d_28_17] at h; exact h
private theorem d_29_18 : D 29 18 = true := by have h := D_step 27 17; rw [d_27_17, d_28_17, d_29_17] at h; exact h
private theorem d_30_18 : D 30 18 = false := by have h := D_step 28 17; rw [d_28_17, d_29_17, d_30_17] at h; exact h
private theorem d_0_19 : D 0 19 = true := D_zero 19
private theorem d_1_19 : D 1 19 = true := D_one 18
private theorem d_2_19 : D 2 19 = false := by have h := D_step 0 18; rw [d_0_18, d_1_18, d_2_18] at h; exact h
private theorem d_3_19 : D 3 19 = true := by have h := D_step 1 18; rw [d_1_18, d_2_18, d_3_18] at h; exact h
private theorem d_4_19 : D 4 19 = true := by have h := D_step 2 18; rw [d_2_18, d_3_18, d_4_18] at h; exact h
private theorem d_5_19 : D 5 19 = true := by have h := D_step 3 18; rw [d_3_18, d_4_18, d_5_18] at h; exact h
private theorem d_6_19 : D 6 19 = true := by have h := D_step 4 18; rw [d_4_18, d_5_18, d_6_18] at h; exact h
private theorem d_7_19 : D 7 19 = false := by have h := D_step 5 18; rw [d_5_18, d_6_18, d_7_18] at h; exact h
private theorem d_8_19 : D 8 19 = false := by have h := D_step 6 18; rw [d_6_18, d_7_18, d_8_18] at h; exact h
private theorem d_9_19 : D 9 19 = true := by have h := D_step 7 18; rw [d_7_18, d_8_18, d_9_18] at h; exact h
private theorem d_10_19 : D 10 19 = true := by have h := D_step 8 18; rw [d_8_18, d_9_18, d_10_18] at h; exact h
private theorem d_11_19 : D 11 19 = false := by have h := D_step 9 18; rw [d_9_18, d_10_18, d_11_18] at h; exact h
private theorem d_12_19 : D 12 19 = true := by have h := D_step 10 18; rw [d_10_18, d_11_18, d_12_18] at h; exact h
private theorem d_13_19 : D 13 19 = false := by have h := D_step 11 18; rw [d_11_18, d_12_18, d_13_18] at h; exact h
private theorem d_14_19 : D 14 19 = false := by have h := D_step 12 18; rw [d_12_18, d_13_18, d_14_18] at h; exact h
private theorem d_15_19 : D 15 19 = true := by have h := D_step 13 18; rw [d_13_18, d_14_18, d_15_18] at h; exact h
private theorem d_16_19 : D 16 19 = true := by have h := D_step 14 18; rw [d_14_18, d_15_18, d_16_18] at h; exact h
private theorem d_17_19 : D 17 19 = true := by have h := D_step 15 18; rw [d_15_18, d_16_18, d_17_18] at h; exact h
private theorem d_18_19 : D 18 19 = true := by have h := D_step 16 18; rw [d_16_18, d_17_18, d_18_18] at h; exact h
private theorem d_19_19 : D 19 19 = true := by have h := D_step 17 18; rw [d_17_18, d_18_18, d_19_18] at h; exact h
private theorem d_20_19 : D 20 19 = true := by have h := D_step 18 18; rw [d_18_18, d_19_18, d_20_18] at h; exact h
private theorem d_21_19 : D 21 19 = false := by have h := D_step 19 18; rw [d_19_18, d_20_18, d_21_18] at h; exact h
private theorem d_22_19 : D 22 19 = false := by have h := D_step 20 18; rw [d_20_18, d_21_18, d_22_18] at h; exact h
private theorem d_23_19 : D 23 19 = true := by have h := D_step 21 18; rw [d_21_18, d_22_18, d_23_18] at h; exact h
private theorem d_24_19 : D 24 19 = false := by have h := D_step 22 18; rw [d_22_18, d_23_18, d_24_18] at h; exact h
private theorem d_25_19 : D 25 19 = false := by have h := D_step 23 18; rw [d_23_18, d_24_18, d_25_18] at h; exact h
private theorem d_26_19 : D 26 19 = false := by have h := D_step 24 18; rw [d_24_18, d_25_18, d_26_18] at h; exact h
private theorem d_27_19 : D 27 19 = true := by have h := D_step 25 18; rw [d_25_18, d_26_18, d_27_18] at h; exact h
private theorem d_28_19 : D 28 19 = false := by have h := D_step 26 18; rw [d_26_18, d_27_18, d_28_18] at h; exact h
private theorem d_29_19 : D 29 19 = false := by have h := D_step 27 18; rw [d_27_18, d_28_18, d_29_18] at h; exact h
private theorem d_30_19 : D 30 19 = false := by have h := D_step 28 18; rw [d_28_18, d_29_18, d_30_18] at h; exact h
private theorem d_0_20 : D 0 20 = true := D_zero 20
private theorem d_1_20 : D 1 20 = true := D_one 19
private theorem d_2_20 : D 2 20 = false := by have h := D_step 0 19; rw [d_0_19, d_1_19, d_2_19] at h; exact h
private theorem d_3_20 : D 3 20 = false := by have h := D_step 1 19; rw [d_1_19, d_2_19, d_3_19] at h; exact h
private theorem d_4_20 : D 4 20 = true := by have h := D_step 2 19; rw [d_2_19, d_3_19, d_4_19] at h; exact h
private theorem d_5_20 : D 5 20 = false := by have h := D_step 3 19; rw [d_3_19, d_4_19, d_5_19] at h; exact h
private theorem d_6_20 : D 6 20 = false := by have h := D_step 4 19; rw [d_4_19, d_5_19, d_6_19] at h; exact h
private theorem d_7_20 : D 7 20 = false := by have h := D_step 5 19; rw [d_5_19, d_6_19, d_7_19] at h; exact h
private theorem d_8_20 : D 8 20 = true := by have h := D_step 6 19; rw [d_6_19, d_7_19, d_8_19] at h; exact h
private theorem d_9_20 : D 9 20 = true := by have h := D_step 7 19; rw [d_7_19, d_8_19, d_9_19] at h; exact h
private theorem d_10_20 : D 10 20 = true := by have h := D_step 8 19; rw [d_8_19, d_9_19, d_10_19] at h; exact h
private theorem d_11_20 : D 11 20 = false := by have h := D_step 9 19; rw [d_9_19, d_10_19, d_11_19] at h; exact h
private theorem d_12_20 : D 12 20 = false := by have h := D_step 10 19; rw [d_10_19, d_11_19, d_12_19] at h; exact h
private theorem d_13_20 : D 13 20 = true := by have h := D_step 11 19; rw [d_11_19, d_12_19, d_13_19] at h; exact h
private theorem d_14_20 : D 14 20 = true := by have h := D_step 12 19; rw [d_12_19, d_13_19, d_14_19] at h; exact h
private theorem d_15_20 : D 15 20 = true := by have h := D_step 13 19; rw [d_13_19, d_14_19, d_15_19] at h; exact h
private theorem d_16_20 : D 16 20 = true := by have h := D_step 14 19; rw [d_14_19, d_15_19, d_16_19] at h; exact h
private theorem d_17_20 : D 17 20 = false := by have h := D_step 15 19; rw [d_15_19, d_16_19, d_17_19] at h; exact h
private theorem d_18_20 : D 18 20 = false := by have h := D_step 16 19; rw [d_16_19, d_17_19, d_18_19] at h; exact h
private theorem d_19_20 : D 19 20 = false := by have h := D_step 17 19; rw [d_17_19, d_18_19, d_19_19] at h; exact h
private theorem d_20_20 : D 20 20 = false := by have h := D_step 18 19; rw [d_18_19, d_19_19, d_20_19] at h; exact h
private theorem d_21_20 : D 21 20 = false := by have h := D_step 19 19; rw [d_19_19, d_20_19, d_21_19] at h; exact h
private theorem d_22_20 : D 22 20 = true := by have h := D_step 20 19; rw [d_20_19, d_21_19, d_22_19] at h; exact h
private theorem d_23_20 : D 23 20 = true := by have h := D_step 21 19; rw [d_21_19, d_22_19, d_23_19] at h; exact h
private theorem d_24_20 : D 24 20 = true := by have h := D_step 22 19; rw [d_22_19, d_23_19, d_24_19] at h; exact h
private theorem d_25_20 : D 25 20 = true := by have h := D_step 23 19; rw [d_23_19, d_24_19, d_25_19] at h; exact h
private theorem d_26_20 : D 26 20 = false := by have h := D_step 24 19; rw [d_24_19, d_25_19, d_26_19] at h; exact h
private theorem d_27_20 : D 27 20 = true := by have h := D_step 25 19; rw [d_25_19, d_26_19, d_27_19] at h; exact h
private theorem d_28_20 : D 28 20 = true := by have h := D_step 26 19; rw [d_26_19, d_27_19, d_28_19] at h; exact h
private theorem d_29_20 : D 29 20 = true := by have h := D_step 27 19; rw [d_27_19, d_28_19, d_29_19] at h; exact h
private theorem d_30_20 : D 30 20 = false := by have h := D_step 28 19; rw [d_28_19, d_29_19, d_30_19] at h; exact h
private theorem d_0_21 : D 0 21 = true := D_zero 21
private theorem d_1_21 : D 1 21 = true := D_one 20
private theorem d_2_21 : D 2 21 = false := by have h := D_step 0 20; rw [d_0_20, d_1_20, d_2_20] at h; exact h
private theorem d_3_21 : D 3 21 = true := by have h := D_step 1 20; rw [d_1_20, d_2_20, d_3_20] at h; exact h
private theorem d_4_21 : D 4 21 = true := by have h := D_step 2 20; rw [d_2_20, d_3_20, d_4_20] at h; exact h
private theorem d_5_21 : D 5 21 = true := by have h := D_step 3 20; rw [d_3_20, d_4_20, d_5_20] at h; exact h
private theorem d_6_21 : D 6 21 = true := by have h := D_step 4 20; rw [d_4_20, d_5_20, d_6_20] at h; exact h
private theorem d_7_21 : D 7 21 = false := by have h := D_step 5 20; rw [d_5_20, d_6_20, d_7_20] at h; exact h
private theorem d_8_21 : D 8 21 = true := by have h := D_step 6 20; rw [d_6_20, d_7_20, d_8_20] at h; exact h
private theorem d_9_21 : D 9 21 = true := by have h := D_step 7 20; rw [d_7_20, d_8_20, d_9_20] at h; exact h
private theorem d_10_21 : D 10 21 = false := by have h := D_step 8 20; rw [d_8_20, d_9_20, d_10_20] at h; exact h
private theorem d_11_21 : D 11 21 = false := by have h := D_step 9 20; rw [d_9_20, d_10_20, d_11_20] at h; exact h
private theorem d_12_21 : D 12 21 = true := by have h := D_step 10 20; rw [d_10_20, d_11_20, d_12_20] at h; exact h
private theorem d_13_21 : D 13 21 = true := by have h := D_step 11 20; rw [d_11_20, d_12_20, d_13_20] at h; exact h
private theorem d_14_21 : D 14 21 = true := by have h := D_step 12 20; rw [d_12_20, d_13_20, d_14_20] at h; exact h
private theorem d_15_21 : D 15 21 = false := by have h := D_step 13 20; rw [d_13_20, d_14_20, d_15_20] at h; exact h
private theorem d_16_21 : D 16 21 = false := by have h := D_step 14 20; rw [d_14_20, d_15_20, d_16_20] at h; exact h
private theorem d_17_21 : D 17 21 = false := by have h := D_step 15 20; rw [d_15_20, d_16_20, d_17_20] at h; exact h
private theorem d_18_21 : D 18 21 = true := by have h := D_step 16 20; rw [d_16_20, d_17_20, d_18_20] at h; exact h
private theorem d_19_21 : D 19 21 = false := by have h := D_step 17 20; rw [d_17_20, d_18_20, d_19_20] at h; exact h
private theorem d_20_21 : D 20 21 = false := by have h := D_step 18 20; rw [d_18_20, d_19_20, d_20_20] at h; exact h
private theorem d_21_21 : D 21 21 = false := by have h := D_step 19 20; rw [d_19_20, d_20_20, d_21_20] at h; exact h
private theorem d_22_21 : D 22 21 = true := by have h := D_step 20 20; rw [d_20_20, d_21_20, d_22_20] at h; exact h
private theorem d_23_21 : D 23 21 = true := by have h := D_step 21 20; rw [d_21_20, d_22_20, d_23_20] at h; exact h
private theorem d_24_21 : D 24 21 = false := by have h := D_step 22 20; rw [d_22_20, d_23_20, d_24_20] at h; exact h
private theorem d_25_21 : D 25 21 = false := by have h := D_step 23 20; rw [d_23_20, d_24_20, d_25_20] at h; exact h
private theorem d_26_21 : D 26 21 = false := by have h := D_step 24 20; rw [d_24_20, d_25_20, d_26_20] at h; exact h
private theorem d_27_21 : D 27 21 = false := by have h := D_step 25 20; rw [d_25_20, d_26_20, d_27_20] at h; exact h
private theorem d_28_21 : D 28 21 = true := by have h := D_step 26 20; rw [d_26_20, d_27_20, d_28_20] at h; exact h
private theorem d_29_21 : D 29 21 = false := by have h := D_step 27 20; rw [d_27_20, d_28_20, d_29_20] at h; exact h
private theorem d_30_21 : D 30 21 = false := by have h := D_step 28 20; rw [d_28_20, d_29_20, d_30_20] at h; exact h
private theorem d_0_22 : D 0 22 = true := D_zero 22
private theorem d_1_22 : D 1 22 = true := D_one 21
private theorem d_2_22 : D 2 22 = false := by have h := D_step 0 21; rw [d_0_21, d_1_21, d_2_21] at h; exact h
private theorem d_3_22 : D 3 22 = false := by have h := D_step 1 21; rw [d_1_21, d_2_21, d_3_21] at h; exact h
private theorem d_4_22 : D 4 22 = true := by have h := D_step 2 21; rw [d_2_21, d_3_21, d_4_21] at h; exact h
private theorem d_5_22 : D 5 22 = false := by have h := D_step 3 21; rw [d_3_21, d_4_21, d_5_21] at h; exact h
private theorem d_6_22 : D 6 22 = false := by have h := D_step 4 21; rw [d_4_21, d_5_21, d_6_21] at h; exact h
private theorem d_7_22 : D 7 22 = false := by have h := D_step 5 21; rw [d_5_21, d_6_21, d_7_21] at h; exact h
private theorem d_8_22 : D 8 22 = false := by have h := D_step 6 21; rw [d_6_21, d_7_21, d_8_21] at h; exact h
private theorem d_9_22 : D 9 22 = true := by have h := D_step 7 21; rw [d_7_21, d_8_21, d_9_21] at h; exact h
private theorem d_10_22 : D 10 22 = false := by have h := D_step 8 21; rw [d_8_21, d_9_21, d_10_21] at h; exact h
private theorem d_11_22 : D 11 22 = true := by have h := D_step 9 21; rw [d_9_21, d_10_21, d_11_21] at h; exact h
private theorem d_12_22 : D 12 22 = true := by have h := D_step 10 21; rw [d_10_21, d_11_21, d_12_21] at h; exact h
private theorem d_13_22 : D 13 22 = true := by have h := D_step 11 21; rw [d_11_21, d_12_21, d_13_21] at h; exact h
private theorem d_14_22 : D 14 22 = false := by have h := D_step 12 21; rw [d_12_21, d_13_21, d_14_21] at h; exact h
private theorem d_15_22 : D 15 22 = false := by have h := D_step 13 21; rw [d_13_21, d_14_21, d_15_21] at h; exact h
private theorem d_16_22 : D 16 22 = true := by have h := D_step 14 21; rw [d_14_21, d_15_21, d_16_21] at h; exact h
private theorem d_17_22 : D 17 22 = false := by have h := D_step 15 21; rw [d_15_21, d_16_21, d_17_21] at h; exact h
private theorem d_18_22 : D 18 22 = true := by have h := D_step 16 21; rw [d_16_21, d_17_21, d_18_21] at h; exact h
private theorem d_19_22 : D 19 22 = true := by have h := D_step 17 21; rw [d_17_21, d_18_21, d_19_21] at h; exact h
private theorem d_20_22 : D 20 22 = true := by have h := D_step 18 21; rw [d_18_21, d_19_21, d_20_21] at h; exact h
private theorem d_21_22 : D 21 22 = false := by have h := D_step 19 21; rw [d_19_21, d_20_21, d_21_21] at h; exact h
private theorem d_22_22 : D 22 22 = true := by have h := D_step 20 21; rw [d_20_21, d_21_21, d_22_21] at h; exact h
private theorem d_23_22 : D 23 22 = true := by have h := D_step 21 21; rw [d_21_21, d_22_21, d_23_21] at h; exact h
private theorem d_24_22 : D 24 22 = false := by have h := D_step 22 21; rw [d_22_21, d_23_21, d_24_21] at h; exact h
private theorem d_25_22 : D 25 22 = true := by have h := D_step 23 21; rw [d_23_21, d_24_21, d_25_21] at h; exact h
private theorem d_26_22 : D 26 22 = false := by have h := D_step 24 21; rw [d_24_21, d_25_21, d_26_21] at h; exact h
private theorem d_27_22 : D 27 22 = false := by have h := D_step 25 21; rw [d_25_21, d_26_21, d_27_21] at h; exact h
private theorem d_28_22 : D 28 22 = true := by have h := D_step 26 21; rw [d_26_21, d_27_21, d_28_21] at h; exact h
private theorem d_29_22 : D 29 22 = true := by have h := D_step 27 21; rw [d_27_21, d_28_21, d_29_21] at h; exact h
private theorem d_30_22 : D 30 22 = true := by have h := D_step 28 21; rw [d_28_21, d_29_21, d_30_21] at h; exact h
private theorem d_0_23 : D 0 23 = true := D_zero 23
private theorem d_1_23 : D 1 23 = true := D_one 22
private theorem d_2_23 : D 2 23 = false := by have h := D_step 0 22; rw [d_0_22, d_1_22, d_2_22] at h; exact h
private theorem d_3_23 : D 3 23 = true := by have h := D_step 1 22; rw [d_1_22, d_2_22, d_3_22] at h; exact h
private theorem d_4_23 : D 4 23 = true := by have h := D_step 2 22; rw [d_2_22, d_3_22, d_4_22] at h; exact h
private theorem d_5_23 : D 5 23 = true := by have h := D_step 3 22; rw [d_3_22, d_4_22, d_5_22] at h; exact h
private theorem d_6_23 : D 6 23 = true := by have h := D_step 4 22; rw [d_4_22, d_5_22, d_6_22] at h; exact h
private theorem d_7_23 : D 7 23 = false := by have h := D_step 5 22; rw [d_5_22, d_6_22, d_7_22] at h; exact h
private theorem d_8_23 : D 8 23 = false := by have h := D_step 6 22; rw [d_6_22, d_7_22, d_8_22] at h; exact h
private theorem d_9_23 : D 9 23 = true := by have h := D_step 7 22; rw [d_7_22, d_8_22, d_9_22] at h; exact h
private theorem d_10_23 : D 10 23 = true := by have h := D_step 8 22; rw [d_8_22, d_9_22, d_10_22] at h; exact h
private theorem d_11_23 : D 11 23 = false := by have h := D_step 9 22; rw [d_9_22, d_10_22, d_11_22] at h; exact h
private theorem d_12_23 : D 12 23 = true := by have h := D_step 10 22; rw [d_10_22, d_11_22, d_12_22] at h; exact h
private theorem d_13_23 : D 13 23 = false := by have h := D_step 11 22; rw [d_11_22, d_12_22, d_13_22] at h; exact h
private theorem d_14_23 : D 14 23 = false := by have h := D_step 12 22; rw [d_12_22, d_13_22, d_14_22] at h; exact h
private theorem d_15_23 : D 15 23 = true := by have h := D_step 13 22; rw [d_13_22, d_14_22, d_15_22] at h; exact h
private theorem d_16_23 : D 16 23 = true := by have h := D_step 14 22; rw [d_14_22, d_15_22, d_16_22] at h; exact h
private theorem d_17_23 : D 17 23 = true := by have h := D_step 15 22; rw [d_15_22, d_16_22, d_17_22] at h; exact h
private theorem d_18_23 : D 18 23 = false := by have h := D_step 16 22; rw [d_16_22, d_17_22, d_18_22] at h; exact h
private theorem d_19_23 : D 19 23 = true := by have h := D_step 17 22; rw [d_17_22, d_18_22, d_19_22] at h; exact h
private theorem d_20_23 : D 20 23 = false := by have h := D_step 18 22; rw [d_18_22, d_19_22, d_20_22] at h; exact h
private theorem d_21_23 : D 21 23 = false := by have h := D_step 19 22; rw [d_19_22, d_20_22, d_21_22] at h; exact h
private theorem d_22_23 : D 22 23 = false := by have h := D_step 20 22; rw [d_20_22, d_21_22, d_22_22] at h; exact h
private theorem d_23_23 : D 23 23 = true := by have h := D_step 21 22; rw [d_21_22, d_22_22, d_23_22] at h; exact h
private theorem d_24_23 : D 24 23 = false := by have h := D_step 22 22; rw [d_22_22, d_23_22, d_24_22] at h; exact h
private theorem d_25_23 : D 25 23 = false := by have h := D_step 23 22; rw [d_23_22, d_24_22, d_25_22] at h; exact h
private theorem d_26_23 : D 26 23 = true := by have h := D_step 24 22; rw [d_24_22, d_25_22, d_26_22] at h; exact h
private theorem d_27_23 : D 27 23 = true := by have h := D_step 25 22; rw [d_25_22, d_26_22, d_27_22] at h; exact h
private theorem d_28_23 : D 28 23 = true := by have h := D_step 26 22; rw [d_26_22, d_27_22, d_28_22] at h; exact h
private theorem d_29_23 : D 29 23 = true := by have h := D_step 27 22; rw [d_27_22, d_28_22, d_29_22] at h; exact h
private theorem d_30_23 : D 30 23 = false := by have h := D_step 28 22; rw [d_28_22, d_29_22, d_30_22] at h; exact h
private theorem d_0_24 : D 0 24 = true := D_zero 24
private theorem d_1_24 : D 1 24 = true := D_one 23
private theorem d_2_24 : D 2 24 = false := by have h := D_step 0 23; rw [d_0_23, d_1_23, d_2_23] at h; exact h
private theorem d_3_24 : D 3 24 = false := by have h := D_step 1 23; rw [d_1_23, d_2_23, d_3_23] at h; exact h
private theorem d_4_24 : D 4 24 = true := by have h := D_step 2 23; rw [d_2_23, d_3_23, d_4_23] at h; exact h
private theorem d_5_24 : D 5 24 = false := by have h := D_step 3 23; rw [d_3_23, d_4_23, d_5_23] at h; exact h
private theorem d_6_24 : D 6 24 = false := by have h := D_step 4 23; rw [d_4_23, d_5_23, d_6_23] at h; exact h
private theorem d_7_24 : D 7 24 = false := by have h := D_step 5 23; rw [d_5_23, d_6_23, d_7_23] at h; exact h
private theorem d_8_24 : D 8 24 = true := by have h := D_step 6 23; rw [d_6_23, d_7_23, d_8_23] at h; exact h
private theorem d_9_24 : D 9 24 = true := by have h := D_step 7 23; rw [d_7_23, d_8_23, d_9_23] at h; exact h
private theorem d_10_24 : D 10 24 = true := by have h := D_step 8 23; rw [d_8_23, d_9_23, d_10_23] at h; exact h
private theorem d_12_24 : D 12 24 = false := by have h := D_step 10 23; rw [d_10_23, d_11_23, d_12_23] at h; exact h
private theorem d_13_24 : D 13 24 = true := by have h := D_step 11 23; rw [d_11_23, d_12_23, d_13_23] at h; exact h
private theorem d_14_24 : D 14 24 = true := by have h := D_step 12 23; rw [d_12_23, d_13_23, d_14_23] at h; exact h
private theorem d_15_24 : D 15 24 = true := by have h := D_step 13 23; rw [d_13_23, d_14_23, d_15_23] at h; exact h
private theorem d_16_24 : D 16 24 = true := by have h := D_step 14 23; rw [d_14_23, d_15_23, d_16_23] at h; exact h
private theorem d_17_24 : D 17 24 = false := by have h := D_step 15 23; rw [d_15_23, d_16_23, d_17_23] at h; exact h
private theorem d_18_24 : D 18 24 = false := by have h := D_step 16 23; rw [d_16_23, d_17_23, d_18_23] at h; exact h
private theorem d_19_24 : D 19 24 = false := by have h := D_step 17 23; rw [d_17_23, d_18_23, d_19_23] at h; exact h
private theorem d_20_24 : D 20 24 = true := by have h := D_step 18 23; rw [d_18_23, d_19_23, d_20_23] at h; exact h
private theorem d_21_24 : D 21 24 = true := by have h := D_step 19 23; rw [d_19_23, d_20_23, d_21_23] at h; exact h
private theorem d_22_24 : D 22 24 = false := by have h := D_step 20 23; rw [d_20_23, d_21_23, d_22_23] at h; exact h
private theorem d_23_24 : D 23 24 = true := by have h := D_step 21 23; rw [d_21_23, d_22_23, d_23_23] at h; exact h
private theorem d_24_24 : D 24 24 = true := by have h := D_step 22 23; rw [d_22_23, d_23_23, d_24_23] at h; exact h
private theorem d_25_24 : D 25 24 = true := by have h := D_step 23 23; rw [d_23_23, d_24_23, d_25_23] at h; exact h
private theorem d_26_24 : D 26 24 = true := by have h := D_step 24 23; rw [d_24_23, d_25_23, d_26_23] at h; exact h
private theorem d_27_24 : D 27 24 = true := by have h := D_step 25 23; rw [d_25_23, d_26_23, d_27_23] at h; exact h
private theorem d_28_24 : D 28 24 = false := by have h := D_step 26 23; rw [d_26_23, d_27_23, d_28_23] at h; exact h
private theorem d_29_24 : D 29 24 = false := by have h := D_step 27 23; rw [d_27_23, d_28_23, d_29_23] at h; exact h
private theorem d_30_24 : D 30 24 = false := by have h := D_step 28 23; rw [d_28_23, d_29_23, d_30_23] at h; exact h
private theorem d_0_25 : D 0 25 = true := D_zero 25
private theorem d_1_25 : D 1 25 = true := D_one 24
private theorem d_2_25 : D 2 25 = false := by have h := D_step 0 24; rw [d_0_24, d_1_24, d_2_24] at h; exact h
private theorem d_3_25 : D 3 25 = true := by have h := D_step 1 24; rw [d_1_24, d_2_24, d_3_24] at h; exact h
private theorem d_4_25 : D 4 25 = true := by have h := D_step 2 24; rw [d_2_24, d_3_24, d_4_24] at h; exact h
private theorem d_5_25 : D 5 25 = true := by have h := D_step 3 24; rw [d_3_24, d_4_24, d_5_24] at h; exact h
private theorem d_6_25 : D 6 25 = true := by have h := D_step 4 24; rw [d_4_24, d_5_24, d_6_24] at h; exact h
private theorem d_7_25 : D 7 25 = false := by have h := D_step 5 24; rw [d_5_24, d_6_24, d_7_24] at h; exact h
private theorem d_8_25 : D 8 25 = true := by have h := D_step 6 24; rw [d_6_24, d_7_24, d_8_24] at h; exact h
private theorem d_9_25 : D 9 25 = true := by have h := D_step 7 24; rw [d_7_24, d_8_24, d_9_24] at h; exact h
private theorem d_10_25 : D 10 25 = false := by have h := D_step 8 24; rw [d_8_24, d_9_24, d_10_24] at h; exact h
private theorem d_14_25 : D 14 25 = true := by have h := D_step 12 24; rw [d_12_24, d_13_24, d_14_24] at h; exact h
private theorem d_15_25 : D 15 25 = false := by have h := D_step 13 24; rw [d_13_24, d_14_24, d_15_24] at h; exact h
private theorem d_16_25 : D 16 25 = false := by have h := D_step 14 24; rw [d_14_24, d_15_24, d_16_24] at h; exact h
private theorem d_17_25 : D 17 25 = false := by have h := D_step 15 24; rw [d_15_24, d_16_24, d_17_24] at h; exact h
private theorem d_18_25 : D 18 25 = true := by have h := D_step 16 24; rw [d_16_24, d_17_24, d_18_24] at h; exact h
private theorem d_19_25 : D 19 25 = false := by have h := D_step 17 24; rw [d_17_24, d_18_24, d_19_24] at h; exact h
private theorem d_20_25 : D 20 25 = true := by have h := D_step 18 24; rw [d_18_24, d_19_24, d_20_24] at h; exact h
private theorem d_21_25 : D 21 25 = true := by have h := D_step 19 24; rw [d_19_24, d_20_24, d_21_24] at h; exact h
private theorem d_22_25 : D 22 25 = false := by have h := D_step 20 24; rw [d_20_24, d_21_24, d_22_24] at h; exact h
private theorem d_23_25 : D 23 25 = false := by have h := D_step 21 24; rw [d_21_24, d_22_24, d_23_24] at h; exact h
private theorem d_24_25 : D 24 25 = true := by have h := D_step 22 24; rw [d_22_24, d_23_24, d_24_24] at h; exact h
private theorem d_25_25 : D 25 25 = false := by have h := D_step 23 24; rw [d_23_24, d_24_24, d_25_24] at h; exact h
private theorem d_26_25 : D 26 25 = false := by have h := D_step 24 24; rw [d_24_24, d_25_24, d_26_24] at h; exact h
private theorem d_27_25 : D 27 25 = false := by have h := D_step 25 24; rw [d_25_24, d_26_24, d_27_24] at h; exact h
private theorem d_28_25 : D 28 25 = false := by have h := D_step 26 24; rw [d_26_24, d_27_24, d_28_24] at h; exact h
private theorem d_29_25 : D 29 25 = true := by have h := D_step 27 24; rw [d_27_24, d_28_24, d_29_24] at h; exact h
private theorem d_30_25 : D 30 25 = false := by have h := D_step 28 24; rw [d_28_24, d_29_24, d_30_24] at h; exact h
private theorem d_0_26 : D 0 26 = true := D_zero 26
private theorem d_1_26 : D 1 26 = true := D_one 25
private theorem d_2_26 : D 2 26 = false := by have h := D_step 0 25; rw [d_0_25, d_1_25, d_2_25] at h; exact h
private theorem d_3_26 : D 3 26 = false := by have h := D_step 1 25; rw [d_1_25, d_2_25, d_3_25] at h; exact h
private theorem d_4_26 : D 4 26 = true := by have h := D_step 2 25; rw [d_2_25, d_3_25, d_4_25] at h; exact h
private theorem d_5_26 : D 5 26 = false := by have h := D_step 3 25; rw [d_3_25, d_4_25, d_5_25] at h; exact h
private theorem d_6_26 : D 6 26 = false := by have h := D_step 4 25; rw [d_4_25, d_5_25, d_6_25] at h; exact h
private theorem d_7_26 : D 7 26 = false := by have h := D_step 5 25; rw [d_5_25, d_6_25, d_7_25] at h; exact h
private theorem d_8_26 : D 8 26 = false := by have h := D_step 6 25; rw [d_6_25, d_7_25, d_8_25] at h; exact h
private theorem d_9_26 : D 9 26 = true := by have h := D_step 7 25; rw [d_7_25, d_8_25, d_9_25] at h; exact h
private theorem d_10_26 : D 10 26 = false := by have h := D_step 8 25; rw [d_8_25, d_9_25, d_10_25] at h; exact h
private theorem d_16_26 : D 16 26 = true := by have h := D_step 14 25; rw [d_14_25, d_15_25, d_16_25] at h; exact h
private theorem d_17_26 : D 17 26 = false := by have h := D_step 15 25; rw [d_15_25, d_16_25, d_17_25] at h; exact h
private theorem d_18_26 : D 18 26 = true := by have h := D_step 16 25; rw [d_16_25, d_17_25, d_18_25] at h; exact h
private theorem d_19_26 : D 19 26 = true := by have h := D_step 17 25; rw [d_17_25, d_18_25, d_19_25] at h; exact h
private theorem d_20_26 : D 20 26 = false := by have h := D_step 18 25; rw [d_18_25, d_19_25, d_20_25] at h; exact h
private theorem d_21_26 : D 21 26 = true := by have h := D_step 19 25; rw [d_19_25, d_20_25, d_21_25] at h; exact h
private theorem d_22_26 : D 22 26 = false := by have h := D_step 20 25; rw [d_20_25, d_21_25, d_22_25] at h; exact h
private theorem d_23_26 : D 23 26 = true := by have h := D_step 21 25; rw [d_21_25, d_22_25, d_23_25] at h; exact h
private theorem d_24_26 : D 24 26 = true := by have h := D_step 22 25; rw [d_22_25, d_23_25, d_24_25] at h; exact h
private theorem d_25_26 : D 25 26 = true := by have h := D_step 23 25; rw [d_23_25, d_24_25, d_25_25] at h; exact h
private theorem d_26_26 : D 26 26 = true := by have h := D_step 24 25; rw [d_24_25, d_25_25, d_26_25] at h; exact h
private theorem d_27_26 : D 27 26 = false := by have h := D_step 25 25; rw [d_25_25, d_26_25, d_27_25] at h; exact h
private theorem d_28_26 : D 28 26 = false := by have h := D_step 26 25; rw [d_26_25, d_27_25, d_28_25] at h; exact h
private theorem d_29_26 : D 29 26 = true := by have h := D_step 27 25; rw [d_27_25, d_28_25, d_29_25] at h; exact h
private theorem d_30_26 : D 30 26 = true := by have h := D_step 28 25; rw [d_28_25, d_29_25, d_30_25] at h; exact h
private theorem d_2_27 : D 2 27 = false := by have h := D_step 0 26; rw [d_0_26, d_1_26, d_2_26] at h; exact h
private theorem d_3_27 : D 3 27 = true := by have h := D_step 1 26; rw [d_1_26, d_2_26, d_3_26] at h; exact h
private theorem d_4_27 : D 4 27 = true := by have h := D_step 2 26; rw [d_2_26, d_3_26, d_4_26] at h; exact h
private theorem d_5_27 : D 5 27 = true := by have h := D_step 3 26; rw [d_3_26, d_4_26, d_5_26] at h; exact h
private theorem d_6_27 : D 6 27 = true := by have h := D_step 4 26; rw [d_4_26, d_5_26, d_6_26] at h; exact h
private theorem d_7_27 : D 7 27 = false := by have h := D_step 5 26; rw [d_5_26, d_6_26, d_7_26] at h; exact h
private theorem d_8_27 : D 8 27 = false := by have h := D_step 6 26; rw [d_6_26, d_7_26, d_8_26] at h; exact h
private theorem d_9_27 : D 9 27 = true := by have h := D_step 7 26; rw [d_7_26, d_8_26, d_9_26] at h; exact h
private theorem d_10_27 : D 10 27 = true := by have h := D_step 8 26; rw [d_8_26, d_9_26, d_10_26] at h; exact h
private theorem d_18_27 : D 18 27 = false := by have h := D_step 16 26; rw [d_16_26, d_17_26, d_18_26] at h; exact h
private theorem d_19_27 : D 19 27 = true := by have h := D_step 17 26; rw [d_17_26, d_18_26, d_19_26] at h; exact h
private theorem d_20_27 : D 20 27 = false := by have h := D_step 18 26; rw [d_18_26, d_19_26, d_20_26] at h; exact h
private theorem d_21_27 : D 21 27 = false := by have h := D_step 19 26; rw [d_19_26, d_20_26, d_21_26] at h; exact h
private theorem d_22_27 : D 22 27 = true := by have h := D_step 20 26; rw [d_20_26, d_21_26, d_22_26] at h; exact h
private theorem d_23_27 : D 23 27 = false := by have h := D_step 21 26; rw [d_21_26, d_22_26, d_23_26] at h; exact h
private theorem d_24_27 : D 24 27 = true := by have h := D_step 22 26; rw [d_22_26, d_23_26, d_24_26] at h; exact h
private theorem d_25_27 : D 25 27 = false := by have h := D_step 23 26; rw [d_23_26, d_24_26, d_25_26] at h; exact h
private theorem d_26_27 : D 26 27 = false := by have h := D_step 24 26; rw [d_24_26, d_25_26, d_26_26] at h; exact h
private theorem d_27_27 : D 27 27 = false := by have h := D_step 25 26; rw [d_25_26, d_26_26, d_27_26] at h; exact h
private theorem d_28_27 : D 28 27 = true := by have h := D_step 26 26; rw [d_26_26, d_27_26, d_28_26] at h; exact h
private theorem d_29_27 : D 29 27 = true := by have h := D_step 27 26; rw [d_27_26, d_28_26, d_29_26] at h; exact h
private theorem d_30_27 : D 30 27 = true := by have h := D_step 28 26; rw [d_28_26, d_29_26, d_30_26] at h; exact h
private theorem d_4_28 : D 4 28 = true := by have h := D_step 2 27; rw [d_2_27, d_3_27, d_4_27] at h; exact h
private theorem d_5_28 : D 5 28 = false := by have h := D_step 3 27; rw [d_3_27, d_4_27, d_5_27] at h; exact h
private theorem d_6_28 : D 6 28 = false := by have h := D_step 4 27; rw [d_4_27, d_5_27, d_6_27] at h; exact h
private theorem d_7_28 : D 7 28 = false := by have h := D_step 5 27; rw [d_5_27, d_6_27, d_7_27] at h; exact h
private theorem d_8_28 : D 8 28 = true := by have h := D_step 6 27; rw [d_6_27, d_7_27, d_8_27] at h; exact h
private theorem d_9_28 : D 9 28 = true := by have h := D_step 7 27; rw [d_7_27, d_8_27, d_9_27] at h; exact h
private theorem d_10_28 : D 10 28 = true := by have h := D_step 8 27; rw [d_8_27, d_9_27, d_10_27] at h; exact h
private theorem d_20_28 : D 20 28 = true := by have h := D_step 18 27; rw [d_18_27, d_19_27, d_20_27] at h; exact h
private theorem d_21_28 : D 21 28 = true := by have h := D_step 19 27; rw [d_19_27, d_20_27, d_21_27] at h; exact h
private theorem d_22_28 : D 22 28 = true := by have h := D_step 20 27; rw [d_20_27, d_21_27, d_22_27] at h; exact h
private theorem d_23_28 : D 23 28 = true := by have h := D_step 21 27; rw [d_21_27, d_22_27, d_23_27] at h; exact h
private theorem d_24_28 : D 24 28 = false := by have h := D_step 22 27; rw [d_22_27, d_23_27, d_24_27] at h; exact h
private theorem d_25_28 : D 25 28 = true := by have h := D_step 23 27; rw [d_23_27, d_24_27, d_25_27] at h; exact h
private theorem d_26_28 : D 26 28 = true := by have h := D_step 24 27; rw [d_24_27, d_25_27, d_26_27] at h; exact h
private theorem d_27_28 : D 27 28 = false := by have h := D_step 25 27; rw [d_25_27, d_26_27, d_27_27] at h; exact h
private theorem d_28_28 : D 28 28 = true := by have h := D_step 26 27; rw [d_26_27, d_27_27, d_28_27] at h; exact h
private theorem d_29_28 : D 29 28 = true := by have h := D_step 27 27; rw [d_27_27, d_28_27, d_29_27] at h; exact h
private theorem d_30_28 : D 30 28 = false := by have h := D_step 28 27; rw [d_28_27, d_29_27, d_30_27] at h; exact h
private theorem d_6_29 : D 6 29 = true := by have h := D_step 4 28; rw [d_4_28, d_5_28, d_6_28] at h; exact h
private theorem d_7_29 : D 7 29 = false := by have h := D_step 5 28; rw [d_5_28, d_6_28, d_7_28] at h; exact h
private theorem d_8_29 : D 8 29 = true := by have h := D_step 6 28; rw [d_6_28, d_7_28, d_8_28] at h; exact h
private theorem d_9_29 : D 9 29 = true := by have h := D_step 7 28; rw [d_7_28, d_8_28, d_9_28] at h; exact h
private theorem d_10_29 : D 10 29 = false := by have h := D_step 8 28; rw [d_8_28, d_9_28, d_10_28] at h; exact h
private theorem d_22_29 : D 22 29 = false := by have h := D_step 20 28; rw [d_20_28, d_21_28, d_22_28] at h; exact h
private theorem d_23_29 : D 23 29 = false := by have h := D_step 21 28; rw [d_21_28, d_22_28, d_23_28] at h; exact h
private theorem d_24_29 : D 24 29 = false := by have h := D_step 22 28; rw [d_22_28, d_23_28, d_24_28] at h; exact h
private theorem d_25_29 : D 25 29 = false := by have h := D_step 23 28; rw [d_23_28, d_24_28, d_25_28] at h; exact h
private theorem d_26_29 : D 26 29 = true := by have h := D_step 24 28; rw [d_24_28, d_25_28, d_26_28] at h; exact h
private theorem d_27_29 : D 27 29 = false := by have h := D_step 25 28; rw [d_25_28, d_26_28, d_27_28] at h; exact h
private theorem d_28_29 : D 28 29 = false := by have h := D_step 26 28; rw [d_26_28, d_27_28, d_28_28] at h; exact h
private theorem d_29_29 : D 29 29 = true := by have h := D_step 27 28; rw [d_27_28, d_28_28, d_29_28] at h; exact h
private theorem d_30_29 : D 30 29 = false := by have h := D_step 28 28; rw [d_28_28, d_29_28, d_30_28] at h; exact h
private theorem d_8_30 : D 8 30 = false := by have h := D_step 6 29; rw [d_6_29, d_7_29, d_8_29] at h; exact h
private theorem d_10_30 : D 10 30 = false := by have h := D_step 8 29; rw [d_8_29, d_9_29, d_10_29] at h; exact h
private theorem d_24_30 : D 24 30 = false := by have h := D_step 22 29; rw [d_22_29, d_23_29, d_24_29] at h; exact h
private theorem d_25_30 : D 25 30 = false := by have h := D_step 23 29; rw [d_23_29, d_24_29, d_25_29] at h; exact h
private theorem d_26_30 : D 26 30 = true := by have h := D_step 24 29; rw [d_24_29, d_25_29, d_26_29] at h; exact h
private theorem d_27_30 : D 27 30 = true := by have h := D_step 25 29; rw [d_25_29, d_26_29, d_27_29] at h; exact h
private theorem d_28_30 : D 28 30 = true := by have h := D_step 26 29; rw [d_26_29, d_27_29, d_28_29] at h; exact h
private theorem d_29_30 : D 29 30 = true := by have h := D_step 27 29; rw [d_27_29, d_28_29, d_29_29] at h; exact h
private theorem d_30_30 : D 30 30 = true := by have h := D_step 28 29; rw [d_28_29, d_29_29, d_30_29] at h; exact h
private theorem d_26_31 : D 26 31 = true := by have h := D_step 24 30; rw [d_24_30, d_25_30, d_26_30] at h; exact h
private theorem d_27_31 : D 27 31 = true := by have h := D_step 25 30; rw [d_25_30, d_26_30, d_27_30] at h; exact h
private theorem d_28_31 : D 28 31 = false := by have h := D_step 26 30; rw [d_26_30, d_27_30, d_28_30] at h; exact h
private theorem d_29_31 : D 29 31 = false := by have h := D_step 27 30; rw [d_27_30, d_28_30, d_29_30] at h; exact h
private theorem d_30_31 : D 30 31 = false := by have h := D_step 28 30; rw [d_28_30, d_29_30, d_30_30] at h; exact h
private theorem d_28_32 : D 28 32 = false := by have h := D_step 26 31; rw [d_26_31, d_27_31, d_28_31] at h; exact h
private theorem d_29_32 : D 29 32 = true := by have h := D_step 27 31; rw [d_27_31, d_28_31, d_29_31] at h; exact h
private theorem d_30_32 : D 30 32 = false := by have h := D_step 28 31; rw [d_28_31, d_29_31, d_30_31] at h; exact h
private theorem d_30_33 : D 30 33 = true := by have h := D_step 28 32; rw [d_28_32, d_29_32, d_30_32] at h; exact h

/-- **Implication-Gate Law for the Sixteenth Left Diagonal (`D_sixteen_eq_not_D_eight_or_D_ten`):**
for every `t ≥ 16`, `D 16 t = (!D 8 t || D 10 t)`. -/
theorem D_sixteen_eq_not_D_eight_or_D_ten : ∀ t : Nat, 16 ≤ t → D 16 t = (!D 8 t || D 10 t)
  | 16, _ => by rw [d_16_16, d_8_16, d_10_16]; rfl
  | t + 1, ht => by
    by_cases h : t < 16
    · have h_eq : t + 1 = 16 := by omega
      rw [h_eq, d_16_16, d_8_16, d_10_16]; rfl
    · have ih := D_sixteen_eq_not_D_eight_or_D_ten t (by omega)
      have hstep := D_step 14 t
      rw [D_fourteen_eq_D_eight t (by omega), D_fifteen_eq_D_ten t (by omega), ih] at hstep
      rw [hstep, D_eight_succ_eq_D_ten t (by omega), D_ten_succ_eq_not_D_eight t (by omega)]
      cases D 8 t <;> cases D 10 t <;> decide

/-- **Inhibition-Gate Law for the Seventeenth Left Diagonal (`D_seventeen_eq_not_D_eight_and_D_ten`):**
for every `t ≥ 16`, `D 17 t = (!D 8 t && D 10 t)`. -/
theorem D_seventeen_eq_not_D_eight_and_D_ten : ∀ t : Nat, 16 ≤ t → D 17 t = (!D 8 t && D 10 t)
  | 16, _ => by rw [d_17_16, d_8_16, d_10_16]; rfl
  | t + 1, ht => by
    by_cases h : t < 16
    · have h_eq : t + 1 = 16 := by omega
      rw [h_eq, d_17_16, d_8_16, d_10_16]; rfl
    · have ih := D_seventeen_eq_not_D_eight_and_D_ten t (by omega)
      have hstep := D_step 15 t
      rw [D_fifteen_eq_D_ten t (by omega), D_sixteen_eq_not_D_eight_or_D_ten t (by omega), ih] at hstep
      rw [hstep, D_eight_succ_eq_D_ten t (by omega), D_ten_succ_eq_not_D_eight t (by omega)]
      cases D 8 t <;> cases D 10 t <;> decide

/-- **Complementation of the Eighteenth and Tenth Left Diagonals (`D_eighteen_eq_not_D_ten`):**
for every `t ≥ 20`, `D 18 t = !D 10 t`. -/
theorem D_eighteen_eq_not_D_ten : ∀ t : Nat, 20 ≤ t → D 18 t = !D 10 t
  | 20, _ => by rw [d_18_20, d_10_20]; rfl
  | t + 1, ht => by
    by_cases h : t < 20
    · have h_eq : t + 1 = 20 := by omega
      rw [h_eq, d_18_20, d_10_20]; rfl
    · have ih := D_eighteen_eq_not_D_ten t (by omega)
      have hstep := D_step 16 t
      rw [D_sixteen_eq_not_D_eight_or_D_ten t (by omega), D_seventeen_eq_not_D_eight_and_D_ten t (by omega), ih] at hstep
      rw [hstep, D_ten_succ_eq_not_D_eight t (by omega)]
      cases D 8 t <;> cases D 10 t <;> decide

/-- **Complementation of the Nineteenth and Eighth Left Diagonals (`D_nineteen_eq_not_D_eight`):**
for every `t ≥ 20`, `D 19 t = !D 8 t`. -/
theorem D_nineteen_eq_not_D_eight : ∀ t : Nat, 20 ≤ t → D 19 t = !D 8 t
  | 20, _ => by rw [d_19_20, d_8_20]; rfl
  | t + 1, ht => by
    by_cases h : t < 20
    · have h_eq : t + 1 = 20 := by omega
      rw [h_eq, d_19_20, d_8_20]; rfl
    · have ih := D_nineteen_eq_not_D_eight t (by omega)
      have hstep := D_step 17 t
      rw [D_seventeen_eq_not_D_eight_and_D_ten t (by omega), D_eighteen_eq_not_D_ten t (by omega), ih] at hstep
      rw [hstep, D_eight_succ_eq_D_ten t (by omega)]
      cases D 8 t <;> cases D 10 t <;> decide

/-- **Phase-Locking of the Twentieth and Eighth Left Diagonals (`D_twenty_eq_D_eight`):**
for every `t ≥ 23`, `D 20 t = D 8 t`. -/
theorem D_twenty_eq_D_eight : ∀ t : Nat, 23 ≤ t → D 20 t = D 8 t
  | 23, _ => by rw [d_20_23, d_8_23]
  | t + 1, ht => by
    by_cases h : t < 23
    · have h_eq : t + 1 = 23 := by omega
      rw [h_eq, d_20_23, d_8_23]
    · have ih := D_twenty_eq_D_eight t (by omega)
      have hstep := D_step 18 t
      rw [D_eighteen_eq_not_D_ten t (by omega), D_nineteen_eq_not_D_eight t (by omega), ih] at hstep
      rw [hstep, D_eight_succ_eq_D_ten t (by omega)]
      cases D 8 t <;> cases D 10 t <;> decide

/-- **Implication-Gate Law for the Twenty-First Left Diagonal (`D_twenty_one_eq_D_eight_or_not_D_ten`):**
for every `t ≥ 23`, `D 21 t = (D 8 t || !D 10 t)`. -/
theorem D_twenty_one_eq_D_eight_or_not_D_ten : ∀ t : Nat, 23 ≤ t → D 21 t = (D 8 t || !D 10 t)
  | 23, _ => by rw [d_21_23, d_8_23, d_10_23]; rfl
  | t + 1, ht => by
    by_cases h : t < 23
    · have h_eq : t + 1 = 23 := by omega
      rw [h_eq, d_21_23, d_8_23, d_10_23]; rfl
    · have ih := D_twenty_one_eq_D_eight_or_not_D_ten t (by omega)
      have hstep := D_step 19 t
      rw [D_nineteen_eq_not_D_eight t (by omega), D_twenty_eq_D_eight t (by omega), ih] at hstep
      rw [hstep, D_eight_succ_eq_D_ten t (by omega), D_ten_succ_eq_not_D_eight t (by omega)]
      cases D 8 t <;> cases D 10 t <;> decide

/-- **Phase-Locking of the Twenty-Second and Tenth Left Diagonals (`D_twenty_two_eq_D_ten`):**
for every `t ≥ 25`, `D 22 t = D 10 t`. -/
theorem D_twenty_two_eq_D_ten : ∀ t : Nat, 25 ≤ t → D 22 t = D 10 t
  | 25, _ => by rw [d_22_25, d_10_25]
  | t + 1, ht => by
    by_cases h : t < 25
    · have h_eq : t + 1 = 25 := by omega
      rw [h_eq, d_22_25, d_10_25]
    · have ih := D_twenty_two_eq_D_ten t (by omega)
      have hstep := D_step 20 t
      rw [D_twenty_eq_D_eight t (by omega), D_twenty_one_eq_D_eight_or_not_D_ten t (by omega), ih] at hstep
      rw [hstep, D_ten_succ_eq_not_D_eight t (by omega)]
      cases D 8 t <;> cases D 10 t <;> decide

/-- **XNOR-Gate Law for the Twenty-Third Left Diagonal (`D_twenty_three_eq_not_xor_D_eight_D_ten`):**
for every `t ≥ 25`, `D 23 t = !xor (D 8 t) (D 10 t)`. -/
theorem D_twenty_three_eq_not_xor_D_eight_D_ten : ∀ t : Nat, 25 ≤ t → D 23 t = !xor (D 8 t) (D 10 t)
  | 25, _ => by rw [d_23_25, d_8_25, d_10_25]; rfl
  | t + 1, ht => by
    by_cases h : t < 25
    · have h_eq : t + 1 = 25 := by omega
      rw [h_eq, d_23_25, d_8_25, d_10_25]; rfl
    · have ih := D_twenty_three_eq_not_xor_D_eight_D_ten t (by omega)
      have hstep := D_step 21 t
      rw [D_twenty_one_eq_D_eight_or_not_D_ten t (by omega), D_twenty_two_eq_D_ten t (by omega), ih] at hstep
      rw [hstep, D_eight_succ_eq_D_ten t (by omega), D_ten_succ_eq_not_D_eight t (by omega)]
      cases D 8 t <;> cases D 10 t <;> decide

/-- **Exact 1-Anti-Periodicity of the Twenty-Third Left Diagonal (`D_twenty_three_succ_eq_not`):**
for every `t ≥ 25`, `D 23 (t + 1) = !D 23 t`. -/
theorem D_twenty_three_succ_eq_not (t : Nat) (ht : 25 ≤ t) :
    D 23 (t + 1) = !D 23 t := by
  rw [D_twenty_three_eq_not_xor_D_eight_D_ten (t + 1) (by omega),
      D_twenty_three_eq_not_xor_D_eight_D_ten t ht,
      D_eight_succ_eq_D_ten t (by omega), D_ten_succ_eq_not_D_eight t (by omega)]
  cases D 8 t <;> cases D 10 t <;> decide

/-- **Eventual 1-Anti-Periodicity of Diagonal `D 23` (`evAntiPer_D_twenty_three`):**
`EvAntiPer (D 23) 1` holds with onset `25`. -/
theorem evAntiPer_D_twenty_three : EvAntiPer (D 23) 1 :=
  ⟨25, D_twenty_three_succ_eq_not⟩

/-- **Unconditional Asymptotic Density `1/2` of Diagonal `D 23` (`halfDensity_D_twenty_three`):**
`HalfDensity (D 23)` holds unconditionally. -/
theorem halfDensity_D_twenty_three : HalfDensity (D 23) :=
  halfDensity_of_antiperiodic (by decide : 0 < 1) evAntiPer_D_twenty_three

/-- **Inhibition-Gate Law for the Twenty-Fourth Left Diagonal (`D_twenty_four_eq_not_D_eight_and_D_ten`):**
for every `t ≥ 27`, `D 24 t = (!D 8 t && D 10 t)`. -/
theorem D_twenty_four_eq_not_D_eight_and_D_ten : ∀ t : Nat, 27 ≤ t → D 24 t = (!D 8 t && D 10 t)
  | 27, _ => by rw [d_24_27, d_8_27, d_10_27]; rfl
  | t + 1, ht => by
    by_cases h : t < 27
    · have h_eq : t + 1 = 27 := by omega
      rw [h_eq, d_24_27, d_8_27, d_10_27]; rfl
    · have ih := D_twenty_four_eq_not_D_eight_and_D_ten t (by omega)
      have hstep := D_step 22 t
      rw [D_twenty_two_eq_D_ten t (by omega), D_twenty_three_eq_not_xor_D_eight_D_ten t (by omega), ih] at hstep
      rw [hstep, D_eight_succ_eq_D_ten t (by omega), D_ten_succ_eq_not_D_eight t (by omega)]
      cases D 8 t <;> cases D 10 t <;> decide

/-- **Phase-Locking of the Twenty-Fifth and Tenth Left Diagonals (`D_twenty_five_eq_D_ten`):**
for every `t ≥ 28`, `D 25 t = D 10 t`. -/
theorem D_twenty_five_eq_D_ten : ∀ t : Nat, 28 ≤ t → D 25 t = D 10 t
  | 28, _ => by rw [d_25_28, d_10_28]
  | t + 1, ht => by
    by_cases h : t < 28
    · have h_eq : t + 1 = 28 := by omega
      rw [h_eq, d_25_28, d_10_28]
    · have ih := D_twenty_five_eq_D_ten t (by omega)
      have hstep := D_step 23 t
      rw [D_twenty_three_eq_not_xor_D_eight_D_ten t (by omega), D_twenty_four_eq_not_D_eight_and_D_ten t (by omega), ih] at hstep
      rw [hstep, D_ten_succ_eq_not_D_eight t (by omega)]
      cases D 8 t <;> cases D 10 t <;> decide

/-- **NAND-Gate Law for the Twenty-Sixth Left Diagonal (`D_twenty_six_eq_nand_D_eight_D_ten`):**
for every `t ≥ 29`, `D 26 t = !(D 8 t && D 10 t)`. -/
theorem D_twenty_six_eq_nand_D_eight_D_ten : ∀ t : Nat, 29 ≤ t → D 26 t = !(D 8 t && D 10 t)
  | 29, _ => by rw [d_26_29, d_8_29, d_10_29]; rfl
  | t + 1, ht => by
    by_cases h : t < 29
    · have h_eq : t + 1 = 29 := by omega
      rw [h_eq, d_26_29, d_8_29, d_10_29]; rfl
    · have ih := D_twenty_six_eq_nand_D_eight_D_ten t (by omega)
      have hstep := D_step 24 t
      rw [D_twenty_four_eq_not_D_eight_and_D_ten t (by omega), D_twenty_five_eq_D_ten t (by omega), ih] at hstep
      rw [hstep, D_eight_succ_eq_D_ten t (by omega), D_ten_succ_eq_not_D_eight t (by omega)]
      cases D 8 t <;> cases D 10 t <;> decide

/-- **Twin-NAND Coincidence on the Twenty-Seventh Left Diagonal (`D_twenty_seven_eq_nand_D_eight_D_ten`):**
for every `t ≥ 30`, `D 27 t = !(D 8 t && D 10 t)`. -/
theorem D_twenty_seven_eq_nand_D_eight_D_ten : ∀ t : Nat, 30 ≤ t → D 27 t = !(D 8 t && D 10 t)
  | 30, _ => by rw [d_27_30, d_8_30, d_10_30]; rfl
  | t + 1, ht => by
    by_cases h : t < 30
    · have h_eq : t + 1 = 30 := by omega
      rw [h_eq, d_27_30, d_8_30, d_10_30]; rfl
    · have ih := D_twenty_seven_eq_nand_D_eight_D_ten t (by omega)
      have hstep := D_step 25 t
      rw [D_twenty_five_eq_D_ten t (by omega), D_twenty_six_eq_nand_D_eight_D_ten t (by omega), ih] at hstep
      rw [hstep, D_eight_succ_eq_D_ten t (by omega), D_ten_succ_eq_not_D_eight t (by omega)]
      cases D 8 t <;> cases D 10 t <;> decide

/-- **Third Universal All-White Reset Diagonal (`D_twenty_eight_eq_false`):**
for every `t ≥ 31`, `D 28 t = false`. -/
theorem D_twenty_eight_eq_false : ∀ t : Nat, 31 ≤ t → D 28 t = false
  | 31, _ => d_28_31
  | t + 1, ht => by
    by_cases h : t < 31
    · have h_eq : t + 1 = 31 := by omega
      rw [h_eq]; exact d_28_31
    · have ih := D_twenty_eight_eq_false t (by omega)
      have hstep := D_step 26 t
      rw [D_twenty_six_eq_nand_D_eight_D_ten t (by omega),
          D_twenty_seven_eq_nand_D_eight_D_ten t (by omega), ih] at hstep
      rw [hstep]
      cases D 8 t <;> cases D 10 t <;> decide

/-- **Diagonal `D 28` Is Eventually White (`evWhite_D_twenty_eight`):**
`EvWhite (D 28)` holds with onset `31`. -/
theorem evWhite_D_twenty_eight : Rule30LeftReset.EvWhite (D 28) :=
  ⟨31, D_twenty_eight_eq_false⟩

/-- **Post-Reset XOR Recurrence of the Twenty-Ninth Left Diagonal (`D_twenty_nine_step_eq_xor_D_twenty_seven`):**
for every `t ≥ 31`, `D 29 (t + 1) = xor (D 27 t) (D 29 t)`. -/
theorem D_twenty_nine_step_eq_xor_D_twenty_seven (t : Nat) (ht : 31 ≤ t) :
    D 29 (t + 1) = xor (D 27 t) (D 29 t) := by
  have hstep := D_step 27 t
  rw [D_twenty_eight_eq_false t ht, Bool.false_or] at hstep
  exact hstep

/-- **Exact 4-Anti-Periodicity of the Twenty-Ninth Left Diagonal (`D_twenty_nine_antiperiodic_four`):**
for every `t ≥ 31`, `D 29 (t + 4) = !D 29 t`. -/
theorem D_twenty_nine_antiperiodic_four (t : Nat) (ht : 31 ≤ t) :
    D 29 (t + 4) = !D 29 t := by
  have s0 := D_twenty_nine_step_eq_xor_D_twenty_seven t ht
  have s1 := D_twenty_nine_step_eq_xor_D_twenty_seven (t + 1) (by omega)
  have s2 := D_twenty_nine_step_eq_xor_D_twenty_seven (t + 2) (by omega)
  have s3 := D_twenty_nine_step_eq_xor_D_twenty_seven (t + 3) (by omega)
  have g0 := D_twenty_seven_eq_nand_D_eight_D_ten t (by omega)
  have g1 := D_twenty_seven_eq_nand_D_eight_D_ten (t + 1) (by omega)
  have g2 := D_twenty_seven_eq_nand_D_eight_D_ten (t + 2) (by omega)
  have g3 := D_twenty_seven_eq_nand_D_eight_D_ten (t + 3) (by omega)
  have a8_1 := D_eight_succ_eq_D_ten t (by omega)
  have a10_1 := D_ten_succ_eq_not_D_eight t (by omega)
  have a8_2 := D_eight_antiperiodic_two t (by omega)
  have a10_2 : D 10 (t + 2) = !D 10 t := by
    rw [show t + 2 = (t + 1) + 1 by omega, D_ten_succ_eq_not_D_eight (t + 1) (by omega), a8_1]
  have a8_3 : D 8 (t + 3) = !D 10 t := by
    rw [show t + 3 = (t + 1) + 2 by omega, D_eight_antiperiodic_two (t + 1) (by omega), a8_1]
  have a10_3 : D 10 (t + 3) = D 8 t := by
    rw [show t + 3 = (t + 2) + 1 by omega, D_ten_succ_eq_not_D_eight (t + 2) (by omega), a8_2, Bool.not_not]
  rw [a8_1, a10_1] at g1
  rw [a8_2, a10_2] at g2
  rw [a8_3, a10_3] at g3
  rw [show t + 1 + 1 = t + 2 by omega] at s1
  rw [show t + 2 + 1 = t + 3 by omega] at s2
  rw [show t + 3 + 1 = t + 4 by omega] at s3
  rw [s3, s2, s1, s0, g0, g1, g2, g3]
  cases D 8 t <;> cases D 10 t <;> cases D 29 t <;> decide

/-- **Eventual 4-Anti-Periodicity of Diagonal `D 29` (`evAntiPer_D_twenty_nine`):**
`EvAntiPer (D 29) 4` holds with onset `31`. -/
theorem evAntiPer_D_twenty_nine : EvAntiPer (D 29) 4 :=
  ⟨31, D_twenty_nine_antiperiodic_four⟩

/-- **Unconditional Asymptotic Density `1/2` of Diagonal `D 29` (`halfDensity_D_twenty_nine`):**
`HalfDensity (D 29)` holds unconditionally. -/
theorem halfDensity_D_twenty_nine : HalfDensity (D 29) :=
  halfDensity_of_antiperiodic (by decide : 0 < 4) evAntiPer_D_twenty_nine

/-- **Third Universal All-Black Shield Diagonal (`D_thirty_eq_true`):**
for every `t ≥ 33`, `D 30 t = true`. -/
theorem D_thirty_eq_true : ∀ t : Nat, 33 ≤ t → D 30 t = true
  | 33, _ => d_30_33
  | t + 1, ht => by
    by_cases h : t < 33
    · have h_eq : t + 1 = 33 := by omega
      rw [h_eq]; exact d_30_33
    · have ih := D_thirty_eq_true t (by omega)
      have hstep := D_step 28 t
      rw [D_twenty_eight_eq_false t (by omega), ih, Bool.or_true, Bool.false_xor] at hstep
      exact hstep

/-- **Diagonal `D 30` Is Eventually Black (`evBlack_D_thirty`):**
`EvBlack (D 30)` holds with onset `33`. -/
theorem evBlack_D_thirty : Rule30WhiteSpacing.EvBlack (D 30) :=
  ⟨33, D_thirty_eq_true⟩

/-- **Shielded Complement Transfer from `D 29` to `D 31` (`D_thirty_one_succ_eq_not_D_twenty_nine`):**
for every `t ≥ 33`, `D 31 (t + 1) = !D 29 t`. -/
theorem D_thirty_one_succ_eq_not_D_twenty_nine (t : Nat) (ht : 33 ≤ t) :
    D 31 (t + 1) = !D 29 t := by
  have hstep := D_step 29 t
  rw [D_thirty_eq_true t ht, Bool.true_or, Bool.xor_true] at hstep
  exact hstep

/-- **Exact 4-Anti-Periodicity of the Thirty-First Left Diagonal (`D_thirty_one_antiperiodic_four`):**
for every `t ≥ 34`, `D 31 (t + 4) = !D 31 t`. -/
theorem D_thirty_one_antiperiodic_four (t : Nat) (ht : 34 ≤ t) :
    D 31 (t + 4) = !D 31 t := by
  have h1 := D_thirty_one_succ_eq_not_D_twenty_nine (t - 1) (by omega)
  have h2 := D_thirty_one_succ_eq_not_D_twenty_nine (t + 3) (by omega)
  have h29 := D_twenty_nine_antiperiodic_four (t - 1) (by omega)
  rw [show t - 1 + 1 = t by omega] at h1
  rw [show t - 1 + 4 = t + 3 by omega] at h29
  rw [show t + 4 = (t + 3) + 1 by omega, h2, h29, h1]

/-- **Eventual 4-Anti-Periodicity of Diagonal `D 31` (`evAntiPer_D_thirty_one`):**
`EvAntiPer (D 31) 4` holds with onset `34`. -/
theorem evAntiPer_D_thirty_one : EvAntiPer (D 31) 4 :=
  ⟨34, D_thirty_one_antiperiodic_four⟩

/-- **Unconditional Asymptotic Density `1/2` of Diagonal `D 31` (`halfDensity_D_thirty_one`):**
`HalfDensity (D 31)` holds unconditionally. -/
theorem halfDensity_D_thirty_one : HalfDensity (D 31) :=
  halfDensity_of_antiperiodic (by decide : 0 < 4) evAntiPer_D_thirty_one

/-! ### Exact `whiteCount` Classification Through Depth 33 (`7 ≤ j ≤ 33`) -/

private theorem oscillator_steps (t : Nat) (ht : 9 ≤ t) :
    D 8 (t + 1) = D 10 t ∧
      D 10 (t + 1) = !D 8 t ∧
      D 8 (t + 2) = !D 8 t ∧
      D 10 (t + 2) = !D 10 t ∧
      D 8 (t + 3) = !D 10 t ∧
      D 10 (t + 3) = D 8 t := by
  have a8_1 := D_eight_succ_eq_D_ten t ht
  have a10_1 := D_ten_succ_eq_not_D_eight t (by omega)
  have a8_2 := D_eight_antiperiodic_two t (by omega)
  have a10_2 := D_ten_antiperiodic_two t ht
  have a8_3 : D 8 (t + 3) = !D 10 t := by
    rw [show t + 3 = (t + 1) + 2 by omega, D_eight_antiperiodic_two (t + 1) (by omega), a8_1]
  have a10_3 : D 10 (t + 3) = D 8 t := by
    rw [show t + 3 = (t + 2) + 1 by omega, D_ten_succ_eq_not_D_eight (t + 2) (by omega), a8_2, Bool.not_not]
  exact ⟨a8_1, a10_1, a8_2, a10_2, a8_3, a10_3⟩

/-- **No Eventually White Left Diagonals on `[13, 27]` (`not_evWhite_between_thirteen_and_twenty_eight`):**
for every `j` with `13 ≤ j < 28`, `¬ EvWhite (D j)`. -/
theorem not_evWhite_between_thirteen_and_twenty_eight {j : Nat} (h1 : 13 ≤ j) (h2 : j < 28) :
    ¬ Rule30LeftReset.EvWhite (D j) := by
  rintro ⟨t0, hw⟩
  let t := Nat.max t0 30
  have ht0 : t0 ≤ t := Nat.le_max_left t0 30
  have ht30 : 30 ≤ t := Nat.le_max_right t0 30
  have w0 : D j t = false := hw t ht0
  have w1 : D j (t + 1) = false := hw (t + 1) (by omega)
  have w2 : D j (t + 2) = false := hw (t + 2) (by omega)
  have w3 : D j (t + 3) = false := hw (t + 3) (by omega)
  obtain ⟨s8_1, s10_1, s8_2, s10_2, s8_3, s10_3⟩ := oscillator_steps t (by omega)
  rcases (by omega : j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 ∨
      j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨ j = 25 ∨ j = 26 ∨ j = 27) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [D_thirteen_eq_or_not_D_eight_D_ten t (by omega)] at w0
    rw [D_thirteen_eq_or_not_D_eight_D_ten (t + 1) (by omega), s8_1, s10_1] at w1
    revert w0 w1; cases D 8 t <;> cases D 10 t <;> decide
  · rw [D_fourteen_eq_D_eight t (by omega)] at w0
    rw [D_fourteen_eq_D_eight (t + 2) (by omega), s8_2] at w2
    revert w0 w2; cases D 8 t <;> decide
  · rw [D_fifteen_eq_D_ten t (by omega)] at w0
    rw [D_fifteen_eq_D_ten (t + 2) (by omega), s10_2] at w2
    revert w0 w2; cases D 10 t <;> decide
  · rw [D_sixteen_eq_not_D_eight_or_D_ten t (by omega)] at w0
    rw [D_sixteen_eq_not_D_eight_or_D_ten (t + 1) (by omega), s8_1, s10_1] at w1
    revert w0 w1; cases D 8 t <;> cases D 10 t <;> decide
  · rw [D_seventeen_eq_not_D_eight_and_D_ten t (by omega)] at w0
    rw [D_seventeen_eq_not_D_eight_and_D_ten (t + 1) (by omega), s8_1, s10_1] at w1
    rw [D_seventeen_eq_not_D_eight_and_D_ten (t + 2) (by omega), s8_2, s10_2] at w2
    rw [D_seventeen_eq_not_D_eight_and_D_ten (t + 3) (by omega), s8_3, s10_3] at w3
    revert w0 w1 w2 w3; cases D 8 t <;> cases D 10 t <;> decide
  · rw [D_eighteen_eq_not_D_ten t (by omega)] at w0
    rw [D_eighteen_eq_not_D_ten (t + 2) (by omega), s10_2] at w2
    revert w0 w2; cases D 10 t <;> decide
  · rw [D_nineteen_eq_not_D_eight t (by omega)] at w0
    rw [D_nineteen_eq_not_D_eight (t + 2) (by omega), s8_2] at w2
    revert w0 w2; cases D 8 t <;> decide
  · rw [D_twenty_eq_D_eight t (by omega)] at w0
    rw [D_twenty_eq_D_eight (t + 2) (by omega), s8_2] at w2
    revert w0 w2; cases D 8 t <;> decide
  · rw [D_twenty_one_eq_D_eight_or_not_D_ten t (by omega)] at w0
    rw [D_twenty_one_eq_D_eight_or_not_D_ten (t + 1) (by omega), s8_1, s10_1] at w1
    revert w0 w1; cases D 8 t <;> cases D 10 t <;> decide
  · rw [D_twenty_two_eq_D_ten t (by omega)] at w0
    rw [D_twenty_two_eq_D_ten (t + 2) (by omega), s10_2] at w2
    revert w0 w2; cases D 10 t <;> decide
  · rw [D_twenty_three_eq_not_xor_D_eight_D_ten t (by omega)] at w0
    rw [D_twenty_three_eq_not_xor_D_eight_D_ten (t + 1) (by omega), s8_1, s10_1] at w1
    revert w0 w1; cases D 8 t <;> cases D 10 t <;> decide
  · rw [D_twenty_four_eq_not_D_eight_and_D_ten t (by omega)] at w0
    rw [D_twenty_four_eq_not_D_eight_and_D_ten (t + 1) (by omega), s8_1, s10_1] at w1
    rw [D_twenty_four_eq_not_D_eight_and_D_ten (t + 2) (by omega), s8_2, s10_2] at w2
    rw [D_twenty_four_eq_not_D_eight_and_D_ten (t + 3) (by omega), s8_3, s10_3] at w3
    revert w0 w1 w2 w3; cases D 8 t <;> cases D 10 t <;> decide
  · rw [D_twenty_five_eq_D_ten t (by omega)] at w0
    rw [D_twenty_five_eq_D_ten (t + 2) (by omega), s10_2] at w2
    revert w0 w2; cases D 10 t <;> decide
  · rw [D_twenty_six_eq_nand_D_eight_D_ten t (by omega)] at w0
    rw [D_twenty_six_eq_nand_D_eight_D_ten (t + 1) (by omega), s8_1, s10_1] at w1
    revert w0 w1; cases D 8 t <;> cases D 10 t <;> decide
  · rw [D_twenty_seven_eq_nand_D_eight_D_ten t (by omega)] at w0
    rw [D_twenty_seven_eq_nand_D_eight_D_ten (t + 1) (by omega), s8_1, s10_1] at w1
    revert w0 w1; cases D 8 t <;> cases D 10 t <;> decide

/-- **No Eventually White Left Diagonals Strictly Between `7` and `28`
(`not_evWhite_between_seven_and_twenty_eight`):** for every `j` with `7 < j < 28`, `¬ EvWhite (D j)`. -/
theorem not_evWhite_between_seven_and_twenty_eight {j : Nat} (h1 : 7 < j) (h2 : j < 28) :
    ¬ Rule30LeftReset.EvWhite (D j) := by
  by_cases h13 : j < 13
  · exact Rule30WhiteSpacing.not_evWhite_between_seven_and_thirteen h1 h13
  · exact not_evWhite_between_thirteen_and_twenty_eight (by omega) h2

private theorem whiteCount_eq_of_no_white_local {m N : Nat}
    (hno : ∀ i, m < i → i ≤ N → ¬ Rule30LeftReset.EvWhite (D i)) :
    ∀ j, m ≤ j → j ≤ N → Rule30LeftReset.whiteCount j = Rule30LeftReset.whiteCount m
  | 0, hm, _ => by
    have h0 : m = 0 := by omega
    rw [h0]
  | j + 1, hm, hN => by
    by_cases hmj : j < m
    · have heq : j + 1 = m := by omega
      rw [heq]
    · have ih := whiteCount_eq_of_no_white_local hno j (by omega) (by omega)
      have hnw : ¬ Rule30LeftReset.EvWhite (D (j + 1)) := hno (j + 1) (by omega) hN
      simp [Rule30LeftReset.whiteCount, hnw, ih]

/-- **Exact Value of `whiteCount` on `[7, 27]` (`whiteCount_eq_two_of_seven_le_le_twenty_seven`):**
for every `j` with `7 ≤ j ≤ 27`, `Rule30LeftReset.whiteCount j = 2`. -/
theorem whiteCount_eq_two_of_seven_le_le_twenty_seven (j : Nat) (h1 : 7 ≤ j) (h2 : j ≤ 27) :
    Rule30LeftReset.whiteCount j = 2 := by
  have hconst := whiteCount_eq_of_no_white_local (m := 7) (N := 27)
    (fun i hi1 hi2 => not_evWhite_between_seven_and_twenty_eight hi1 (by omega))
  rw [hconst j h1 h2, Rule30WhiteSpacing.whiteCount_seven]

/-- **Exact Value `whiteCount 28 = 3` (`whiteCount_twenty_eight`):**
`Rule30LeftReset.whiteCount 28 = 3`. -/
theorem whiteCount_twenty_eight : Rule30LeftReset.whiteCount 28 = 3 := by
  have hcount : Rule30LeftReset.whiteCount (27 + 1) = Rule30LeftReset.whiteCount 27 + 1 := by
    simp [Rule30LeftReset.whiteCount, evWhite_D_twenty_eight]
  rw [show (28 : Nat) = 27 + 1 by rfl, hcount,
      whiteCount_eq_two_of_seven_le_le_twenty_seven 27 (by omega) (by omega)]

/-- **No Eventually White Left Diagonals Strictly Between `28` and `34`
(`not_evWhite_between_twenty_eight_and_thirty_four`):** for `28 < j < 34`, `¬ EvWhite (D j)`. -/
theorem not_evWhite_between_twenty_eight_and_thirty_four {j : Nat} (h1 : 28 < j) (h2 : j < 34) :
    ¬ Rule30LeftReset.EvWhite (D j) := by
  intro hj
  have := Rule30WhiteSpacing.white_spacing_six evWhite_D_twenty_eight hj h1 (by decide)
  omega

/-- **Exact Value of `whiteCount` on `[28, 33]` (`whiteCount_eq_three_of_twenty_eight_le_le_thirty_three`):**
for every `j` with `28 ≤ j ≤ 33`, `Rule30LeftReset.whiteCount j = 3`. -/
theorem whiteCount_eq_three_of_twenty_eight_le_le_thirty_three (j : Nat) (h1 : 28 ≤ j) (h2 : j ≤ 33) :
    Rule30LeftReset.whiteCount j = 3 := by
  have hconst := whiteCount_eq_of_no_white_local (m := 28) (N := 33)
    (fun i hi1 hi2 => not_evWhite_between_twenty_eight_and_thirty_four hi1 (by omega))
  rw [hconst j h1 h2, whiteCount_twenty_eight]

/-- **Exact Complementation of the Twenty-Third and Third Left Diagonals (`D_twenty_three_eq_not_D_three`):**
for every `t ≥ 25`, `D 23 t = !D 3 t`. -/
theorem D_twenty_three_eq_not_D_three : ∀ t : Nat, 25 ≤ t → D 23 t = !D 3 t
  | 25, _ => by rw [d_23_25, d_3_25]; rfl
  | t + 1, ht => by
    by_cases h : t < 25
    · have h_eq : t + 1 = 25 := by omega
      rw [h_eq, d_23_25, d_3_25]; rfl
    · have ih := D_twenty_three_eq_not_D_three t (by omega)
      rw [D_twenty_three_succ_eq_not t (by omega), Rule30WhiteSpacing.D_three_succ t (by omega), ih]

private theorem D_eight_periodic_four (t : Nat) (ht : 7 ≤ t) :
    D 8 (t + 4) = D 8 t := by
  have h1 := D_eight_antiperiodic_two t ht
  have h2 := D_eight_antiperiodic_two (t + 2) (by omega)
  rw [show t + 2 + 2 = t + 4 by omega, h1, Bool.not_not] at h2
  exact h2

private theorem D_ten_periodic_four (t : Nat) (ht : 9 ≤ t) :
    D 10 (t + 4) = D 10 t := by
  have h1 := D_ten_antiperiodic_two t ht
  have h2 := D_ten_antiperiodic_two (t + 2) (by omega)
  rw [show t + 2 + 2 = t + 4 by omega, h1, Bool.not_not] at h2
  exact h2

/-! ### 6. Period-8 Oscillator Gates `D 31 .. D 34`, Multiplexer Conservation, and 21/24-Column Inward Non-Periodicity -/

private theorem d_31_16 : D 31 16 = false := by have h := D_step 29 15; rw [d_29_15, d_30_15, (D_eq_false_of_two_mul_lt 31 15 (by omega))] at h; exact h
private theorem d_32_16 : D 32 16 = true := by have h := D_step 30 15; rw [d_30_15, (D_eq_false_of_two_mul_lt 31 15 (by omega)), (D_eq_false_of_two_mul_lt 32 15 (by omega))] at h; exact h
private theorem d_31_17 : D 31 17 = false := by have h := D_step 29 16; rw [d_29_16, d_30_16, d_31_16] at h; exact h
private theorem d_32_17 : D 32 17 = true := by have h := D_step 30 16; rw [d_30_16, d_31_16, d_32_16] at h; exact h
private theorem d_33_17 : D 33 17 = true := by have h := D_step 31 16; rw [d_31_16, d_32_16, (D_eq_false_of_two_mul_lt 33 16 (by omega))] at h; exact h
private theorem d_34_17 : D 34 17 = true := by have h := D_step 32 16; rw [d_32_16, (D_eq_false_of_two_mul_lt 33 16 (by omega)), (D_eq_false_of_two_mul_lt 34 16 (by omega))] at h; exact h
private theorem d_31_18 : D 31 18 = false := by have h := D_step 29 17; rw [d_29_17, d_30_17, d_31_17] at h; exact h
private theorem d_32_18 : D 32 18 = true := by have h := D_step 30 17; rw [d_30_17, d_31_17, d_32_17] at h; exact h
private theorem d_33_18 : D 33 18 = true := by have h := D_step 31 17; rw [d_31_17, d_32_17, d_33_17] at h; exact h
private theorem d_34_18 : D 34 18 = false := by have h := D_step 32 17; rw [d_32_17, d_33_17, d_34_17] at h; exact h
private theorem d_31_19 : D 31 19 = true := by have h := D_step 29 18; rw [d_29_18, d_30_18, d_31_18] at h; exact h
private theorem d_32_19 : D 32 19 = true := by have h := D_step 30 18; rw [d_30_18, d_31_18, d_32_18] at h; exact h
private theorem d_33_19 : D 33 19 = true := by have h := D_step 31 18; rw [d_31_18, d_32_18, d_33_18] at h; exact h
private theorem d_34_19 : D 34 19 = false := by have h := D_step 32 18; rw [d_32_18, d_33_18, d_34_18] at h; exact h
private theorem d_31_20 : D 31 20 = true := by have h := D_step 29 19; rw [d_29_19, d_30_19, d_31_19] at h; exact h
private theorem d_32_20 : D 32 20 = true := by have h := D_step 30 19; rw [d_30_19, d_31_19, d_32_19] at h; exact h
private theorem d_33_20 : D 33 20 = false := by have h := D_step 31 19; rw [d_31_19, d_32_19, d_33_19] at h; exact h
private theorem d_34_20 : D 34 20 = false := by have h := D_step 32 19; rw [d_32_19, d_33_19, d_34_19] at h; exact h
private theorem d_31_21 : D 31 21 = false := by have h := D_step 29 20; rw [d_29_20, d_30_20, d_31_20] at h; exact h
private theorem d_32_21 : D 32 21 = true := by have h := D_step 30 20; rw [d_30_20, d_31_20, d_32_20] at h; exact h
private theorem d_33_21 : D 33 21 = false := by have h := D_step 31 20; rw [d_31_20, d_32_20, d_33_20] at h; exact h
private theorem d_34_21 : D 34 21 = true := by have h := D_step 32 20; rw [d_32_20, d_33_20, d_34_20] at h; exact h
private theorem d_31_22 : D 31 22 = false := by have h := D_step 29 21; rw [d_29_21, d_30_21, d_31_21] at h; exact h
private theorem d_32_22 : D 32 22 = true := by have h := D_step 30 21; rw [d_30_21, d_31_21, d_32_21] at h; exact h
private theorem d_33_22 : D 33 22 = true := by have h := D_step 31 21; rw [d_31_21, d_32_21, d_33_21] at h; exact h
private theorem d_34_22 : D 34 22 = false := by have h := D_step 32 21; rw [d_32_21, d_33_21, d_34_21] at h; exact h
private theorem d_31_23 : D 31 23 = false := by have h := D_step 29 22; rw [d_29_22, d_30_22, d_31_22] at h; exact h
private theorem d_32_23 : D 32 23 = false := by have h := D_step 30 22; rw [d_30_22, d_31_22, d_32_22] at h; exact h
private theorem d_33_23 : D 33 23 = true := by have h := D_step 31 22; rw [d_31_22, d_32_22, d_33_22] at h; exact h
private theorem d_34_23 : D 34 23 = false := by have h := D_step 32 22; rw [d_32_22, d_33_22, d_34_22] at h; exact h
private theorem d_11_24 : D 11 24 = false := by have h := D_step 9 23; rw [d_9_23, d_10_23, d_11_23] at h; exact h
private theorem d_31_24 : D 31 24 = true := by have h := D_step 29 23; rw [d_29_23, d_30_23, d_31_23] at h; exact h
private theorem d_32_24 : D 32 24 = false := by have h := D_step 30 23; rw [d_30_23, d_31_23, d_32_23] at h; exact h
private theorem d_33_24 : D 33 24 = true := by have h := D_step 31 23; rw [d_31_23, d_32_23, d_33_23] at h; exact h
private theorem d_34_24 : D 34 24 = true := by have h := D_step 32 23; rw [d_32_23, d_33_23, d_34_23] at h; exact h
private theorem d_11_25 : D 11 25 = false := by have h := D_step 9 24; rw [d_9_24, d_10_24, d_11_24] at h; exact h
private theorem d_12_25 : D 12 25 = true := by have h := D_step 10 24; rw [d_10_24, d_11_24, d_12_24] at h; exact h
private theorem d_13_25 : D 13 25 = true := by have h := D_step 11 24; rw [d_11_24, d_12_24, d_13_24] at h; exact h
private theorem d_31_25 : D 31 25 = true := by have h := D_step 29 24; rw [d_29_24, d_30_24, d_31_24] at h; exact h
private theorem d_32_25 : D 32 25 = true := by have h := D_step 30 24; rw [d_30_24, d_31_24, d_32_24] at h; exact h
private theorem d_33_25 : D 33 25 = false := by have h := D_step 31 24; rw [d_31_24, d_32_24, d_33_24] at h; exact h
private theorem d_34_25 : D 34 25 = true := by have h := D_step 32 24; rw [d_32_24, d_33_24, d_34_24] at h; exact h
private theorem d_11_26 : D 11 26 = true := by have h := D_step 9 25; rw [d_9_25, d_10_25, d_11_25] at h; exact h
private theorem d_12_26 : D 12 26 = true := by have h := D_step 10 25; rw [d_10_25, d_11_25, d_12_25] at h; exact h
private theorem d_13_26 : D 13 26 = true := by have h := D_step 11 25; rw [d_11_25, d_12_25, d_13_25] at h; exact h
private theorem d_14_26 : D 14 26 = false := by have h := D_step 12 25; rw [d_12_25, d_13_25, d_14_25] at h; exact h
private theorem d_15_26 : D 15 26 = false := by have h := D_step 13 25; rw [d_13_25, d_14_25, d_15_25] at h; exact h
private theorem d_31_26 : D 31 26 = false := by have h := D_step 29 25; rw [d_29_25, d_30_25, d_31_25] at h; exact h
private theorem d_32_26 : D 32 26 = true := by have h := D_step 30 25; rw [d_30_25, d_31_25, d_32_25] at h; exact h
private theorem d_33_26 : D 33 26 = false := by have h := D_step 31 25; rw [d_31_25, d_32_25, d_33_25] at h; exact h
private theorem d_34_26 : D 34 26 = false := by have h := D_step 32 25; rw [d_32_25, d_33_25, d_34_25] at h; exact h
private theorem d_0_27 : D 0 27 = true := D_zero 27
private theorem d_1_27 : D 1 27 = true := by simpa using D_one 26
private theorem d_11_27 : D 11 27 = false := by have h := D_step 9 26; rw [d_9_26, d_10_26, d_11_26] at h; exact h
private theorem d_12_27 : D 12 27 = true := by have h := D_step 10 26; rw [d_10_26, d_11_26, d_12_26] at h; exact h
private theorem d_13_27 : D 13 27 = false := by have h := D_step 11 26; rw [d_11_26, d_12_26, d_13_26] at h; exact h
private theorem d_14_27 : D 14 27 = false := by have h := D_step 12 26; rw [d_12_26, d_13_26, d_14_26] at h; exact h
private theorem d_15_27 : D 15 27 = true := by have h := D_step 13 26; rw [d_13_26, d_14_26, d_15_26] at h; exact h
private theorem d_16_27 : D 16 27 = true := by have h := D_step 14 26; rw [d_14_26, d_15_26, d_16_26] at h; exact h
private theorem d_17_27 : D 17 27 = true := by have h := D_step 15 26; rw [d_15_26, d_16_26, d_17_26] at h; exact h
private theorem d_31_27 : D 31 27 = false := by have h := D_step 29 26; rw [d_29_26, d_30_26, d_31_26] at h; exact h
private theorem d_32_27 : D 32 27 = false := by have h := D_step 30 26; rw [d_30_26, d_31_26, d_32_26] at h; exact h
private theorem d_33_27 : D 33 27 = true := by have h := D_step 31 26; rw [d_31_26, d_32_26, d_33_26] at h; exact h
private theorem d_34_27 : D 34 27 = true := by have h := D_step 32 26; rw [d_32_26, d_33_26, d_34_26] at h; exact h
private theorem d_0_28 : D 0 28 = true := D_zero 28
private theorem d_1_28 : D 1 28 = true := by simpa using D_one 27
private theorem d_2_28 : D 2 28 = false := by have h := D_step 0 27; rw [d_0_27, d_1_27, d_2_27] at h; exact h
private theorem d_3_28 : D 3 28 = false := by have h := D_step 1 27; rw [d_1_27, d_2_27, d_3_27] at h; exact h
private theorem d_11_28 : D 11 28 = false := by have h := D_step 9 27; rw [d_9_27, d_10_27, d_11_27] at h; exact h
private theorem d_12_28 : D 12 28 = false := by have h := D_step 10 27; rw [d_10_27, d_11_27, d_12_27] at h; exact h
private theorem d_13_28 : D 13 28 = true := by have h := D_step 11 27; rw [d_11_27, d_12_27, d_13_27] at h; exact h
private theorem d_14_28 : D 14 28 = true := by have h := D_step 12 27; rw [d_12_27, d_13_27, d_14_27] at h; exact h
private theorem d_15_28 : D 15 28 = true := by have h := D_step 13 27; rw [d_13_27, d_14_27, d_15_27] at h; exact h
private theorem d_16_28 : D 16 28 = true := by have h := D_step 14 27; rw [d_14_27, d_15_27, d_16_27] at h; exact h
private theorem d_17_28 : D 17 28 = false := by have h := D_step 15 27; rw [d_15_27, d_16_27, d_17_27] at h; exact h
private theorem d_18_28 : D 18 28 = false := by have h := D_step 16 27; rw [d_16_27, d_17_27, d_18_27] at h; exact h
private theorem d_19_28 : D 19 28 = false := by have h := D_step 17 27; rw [d_17_27, d_18_27, d_19_27] at h; exact h
private theorem d_31_28 : D 31 28 = false := by have h := D_step 29 27; rw [d_29_27, d_30_27, d_31_27] at h; exact h
private theorem d_32_28 : D 32 28 = true := by have h := D_step 30 27; rw [d_30_27, d_31_27, d_32_27] at h; exact h
private theorem d_33_28 : D 33 28 = true := by have h := D_step 31 27; rw [d_31_27, d_32_27, d_33_27] at h; exact h
private theorem d_34_28 : D 34 28 = true := by have h := D_step 32 27; rw [d_32_27, d_33_27, d_34_27] at h; exact h
private theorem d_0_29 : D 0 29 = true := D_zero 29
private theorem d_1_29 : D 1 29 = true := by simpa using D_one 28
private theorem d_2_29 : D 2 29 = false := by have h := D_step 0 28; rw [d_0_28, d_1_28, d_2_28] at h; exact h
private theorem d_3_29 : D 3 29 = true := by have h := D_step 1 28; rw [d_1_28, d_2_28, d_3_28] at h; exact h
private theorem d_4_29 : D 4 29 = true := by have h := D_step 2 28; rw [d_2_28, d_3_28, d_4_28] at h; exact h
private theorem d_5_29 : D 5 29 = true := by have h := D_step 3 28; rw [d_3_28, d_4_28, d_5_28] at h; exact h
private theorem d_11_29 : D 11 29 = false := by have h := D_step 9 28; rw [d_9_28, d_10_28, d_11_28] at h; exact h
private theorem d_12_29 : D 12 29 = true := by have h := D_step 10 28; rw [d_10_28, d_11_28, d_12_28] at h; exact h
private theorem d_13_29 : D 13 29 = true := by have h := D_step 11 28; rw [d_11_28, d_12_28, d_13_28] at h; exact h
private theorem d_14_29 : D 14 29 = true := by have h := D_step 12 28; rw [d_12_28, d_13_28, d_14_28] at h; exact h
private theorem d_15_29 : D 15 29 = false := by have h := D_step 13 28; rw [d_13_28, d_14_28, d_15_28] at h; exact h
private theorem d_16_29 : D 16 29 = false := by have h := D_step 14 28; rw [d_14_28, d_15_28, d_16_28] at h; exact h
private theorem d_17_29 : D 17 29 = false := by have h := D_step 15 28; rw [d_15_28, d_16_28, d_17_28] at h; exact h
private theorem d_18_29 : D 18 29 = true := by have h := D_step 16 28; rw [d_16_28, d_17_28, d_18_28] at h; exact h
private theorem d_19_29 : D 19 29 = false := by have h := D_step 17 28; rw [d_17_28, d_18_28, d_19_28] at h; exact h
private theorem d_20_29 : D 20 29 = true := by have h := D_step 18 28; rw [d_18_28, d_19_28, d_20_28] at h; exact h
private theorem d_21_29 : D 21 29 = true := by have h := D_step 19 28; rw [d_19_28, d_20_28, d_21_28] at h; exact h
private theorem d_31_29 : D 31 29 = true := by have h := D_step 29 28; rw [d_29_28, d_30_28, d_31_28] at h; exact h
private theorem d_32_29 : D 32 29 = true := by have h := D_step 30 28; rw [d_30_28, d_31_28, d_32_28] at h; exact h
private theorem d_33_29 : D 33 29 = true := by have h := D_step 31 28; rw [d_31_28, d_32_28, d_33_28] at h; exact h
private theorem d_34_29 : D 34 29 = false := by have h := D_step 32 28; rw [d_32_28, d_33_28, d_34_28] at h; exact h
private theorem d_0_30 : D 0 30 = true := D_zero 30
private theorem d_1_30 : D 1 30 = true := by simpa using D_one 29
private theorem d_2_30 : D 2 30 = false := by have h := D_step 0 29; rw [d_0_29, d_1_29, d_2_29] at h; exact h
private theorem d_3_30 : D 3 30 = false := by have h := D_step 1 29; rw [d_1_29, d_2_29, d_3_29] at h; exact h
private theorem d_4_30 : D 4 30 = true := by have h := D_step 2 29; rw [d_2_29, d_3_29, d_4_29] at h; exact h
private theorem d_5_30 : D 5 30 = false := by have h := D_step 3 29; rw [d_3_29, d_4_29, d_5_29] at h; exact h
private theorem d_6_30 : D 6 30 = false := by have h := D_step 4 29; rw [d_4_29, d_5_29, d_6_29] at h; exact h
private theorem d_7_30 : D 7 30 = false := by have h := D_step 5 29; rw [d_5_29, d_6_29, d_7_29] at h; exact h
private theorem d_9_30 : D 9 30 = true := by have h := D_step 7 29; rw [d_7_29, d_8_29, d_9_29] at h; exact h
private theorem d_11_30 : D 11 30 = true := by have h := D_step 9 29; rw [d_9_29, d_10_29, d_11_29] at h; exact h
private theorem d_12_30 : D 12 30 = true := by have h := D_step 10 29; rw [d_10_29, d_11_29, d_12_29] at h; exact h
private theorem d_13_30 : D 13 30 = true := by have h := D_step 11 29; rw [d_11_29, d_12_29, d_13_29] at h; exact h
private theorem d_14_30 : D 14 30 = false := by have h := D_step 12 29; rw [d_12_29, d_13_29, d_14_29] at h; exact h
private theorem d_15_30 : D 15 30 = false := by have h := D_step 13 29; rw [d_13_29, d_14_29, d_15_29] at h; exact h
private theorem d_16_30 : D 16 30 = true := by have h := D_step 14 29; rw [d_14_29, d_15_29, d_16_29] at h; exact h
private theorem d_17_30 : D 17 30 = false := by have h := D_step 15 29; rw [d_15_29, d_16_29, d_17_29] at h; exact h
private theorem d_18_30 : D 18 30 = true := by have h := D_step 16 29; rw [d_16_29, d_17_29, d_18_29] at h; exact h
private theorem d_19_30 : D 19 30 = true := by have h := D_step 17 29; rw [d_17_29, d_18_29, d_19_29] at h; exact h
private theorem d_20_30 : D 20 30 = false := by have h := D_step 18 29; rw [d_18_29, d_19_29, d_20_29] at h; exact h
private theorem d_21_30 : D 21 30 = true := by have h := D_step 19 29; rw [d_19_29, d_20_29, d_21_29] at h; exact h
private theorem d_22_30 : D 22 30 = false := by have h := D_step 20 29; rw [d_20_29, d_21_29, d_22_29] at h; exact h
private theorem d_23_30 : D 23 30 = true := by have h := D_step 21 29; rw [d_21_29, d_22_29, d_23_29] at h; exact h
private theorem d_31_30 : D 31 30 = false := by have h := D_step 29 29; rw [d_29_29, d_30_29, d_31_29] at h; exact h
private theorem d_32_30 : D 32 30 = true := by have h := D_step 30 29; rw [d_30_29, d_31_29, d_32_29] at h; exact h
private theorem d_33_30 : D 33 30 = false := by have h := D_step 31 29; rw [d_31_29, d_32_29, d_33_29] at h; exact h
private theorem d_34_30 : D 34 30 = false := by have h := D_step 32 29; rw [d_32_29, d_33_29, d_34_29] at h; exact h
private theorem d_0_31 : D 0 31 = true := D_zero 31
private theorem d_1_31 : D 1 31 = true := by simpa using D_one 30
private theorem d_2_31 : D 2 31 = false := by have h := D_step 0 30; rw [d_0_30, d_1_30, d_2_30] at h; exact h
private theorem d_3_31 : D 3 31 = true := by have h := D_step 1 30; rw [d_1_30, d_2_30, d_3_30] at h; exact h
private theorem d_4_31 : D 4 31 = true := by have h := D_step 2 30; rw [d_2_30, d_3_30, d_4_30] at h; exact h
private theorem d_5_31 : D 5 31 = true := by have h := D_step 3 30; rw [d_3_30, d_4_30, d_5_30] at h; exact h
private theorem d_6_31 : D 6 31 = true := by have h := D_step 4 30; rw [d_4_30, d_5_30, d_6_30] at h; exact h
private theorem d_7_31 : D 7 31 = false := by have h := D_step 5 30; rw [d_5_30, d_6_30, d_7_30] at h; exact h
private theorem d_8_31 : D 8 31 = false := by have h := D_step 6 30; rw [d_6_30, d_7_30, d_8_30] at h; exact h
private theorem d_9_31 : D 9 31 = true := by have h := D_step 7 30; rw [d_7_30, d_8_30, d_9_30] at h; exact h
private theorem d_10_31 : D 10 31 = true := by have h := D_step 8 30; rw [d_8_30, d_9_30, d_10_30] at h; exact h
private theorem d_11_31 : D 11 31 = false := by have h := D_step 9 30; rw [d_9_30, d_10_30, d_11_30] at h; exact h
private theorem d_12_31 : D 12 31 = true := by have h := D_step 10 30; rw [d_10_30, d_11_30, d_12_30] at h; exact h
private theorem d_13_31 : D 13 31 = false := by have h := D_step 11 30; rw [d_11_30, d_12_30, d_13_30] at h; exact h
private theorem d_14_31 : D 14 31 = false := by have h := D_step 12 30; rw [d_12_30, d_13_30, d_14_30] at h; exact h
private theorem d_15_31 : D 15 31 = true := by have h := D_step 13 30; rw [d_13_30, d_14_30, d_15_30] at h; exact h
private theorem d_16_31 : D 16 31 = true := by have h := D_step 14 30; rw [d_14_30, d_15_30, d_16_30] at h; exact h
private theorem d_17_31 : D 17 31 = true := by have h := D_step 15 30; rw [d_15_30, d_16_30, d_17_30] at h; exact h
private theorem d_18_31 : D 18 31 = false := by have h := D_step 16 30; rw [d_16_30, d_17_30, d_18_30] at h; exact h
private theorem d_19_31 : D 19 31 = true := by have h := D_step 17 30; rw [d_17_30, d_18_30, d_19_30] at h; exact h
private theorem d_20_31 : D 20 31 = false := by have h := D_step 18 30; rw [d_18_30, d_19_30, d_20_30] at h; exact h
private theorem d_21_31 : D 21 31 = false := by have h := D_step 19 30; rw [d_19_30, d_20_30, d_21_30] at h; exact h
private theorem d_22_31 : D 22 31 = true := by have h := D_step 20 30; rw [d_20_30, d_21_30, d_22_30] at h; exact h
private theorem d_23_31 : D 23 31 = false := by have h := D_step 21 30; rw [d_21_30, d_22_30, d_23_30] at h; exact h
private theorem d_24_31 : D 24 31 = true := by have h := D_step 22 30; rw [d_22_30, d_23_30, d_24_30] at h; exact h
private theorem d_25_31 : D 25 31 = true := by have h := D_step 23 30; rw [d_23_30, d_24_30, d_25_30] at h; exact h
private theorem d_31_31 : D 31 31 = false := by have h := D_step 29 30; rw [d_29_30, d_30_30, d_31_30] at h; exact h
private theorem d_32_31 : D 32 31 = false := by have h := D_step 30 30; rw [d_30_30, d_31_30, d_32_30] at h; exact h
private theorem d_33_31 : D 33 31 = true := by have h := D_step 31 30; rw [d_31_30, d_32_30, d_33_30] at h; exact h
private theorem d_34_31 : D 34 31 = true := by have h := D_step 32 30; rw [d_32_30, d_33_30, d_34_30] at h; exact h
private theorem d_0_32 : D 0 32 = true := D_zero 32
private theorem d_1_32 : D 1 32 = true := by simpa using D_one 31
private theorem d_2_32 : D 2 32 = false := by have h := D_step 0 31; rw [d_0_31, d_1_31, d_2_31] at h; exact h
private theorem d_3_32 : D 3 32 = false := by have h := D_step 1 31; rw [d_1_31, d_2_31, d_3_31] at h; exact h
private theorem d_4_32 : D 4 32 = true := by have h := D_step 2 31; rw [d_2_31, d_3_31, d_4_31] at h; exact h
private theorem d_5_32 : D 5 32 = false := by have h := D_step 3 31; rw [d_3_31, d_4_31, d_5_31] at h; exact h
private theorem d_6_32 : D 6 32 = false := by have h := D_step 4 31; rw [d_4_31, d_5_31, d_6_31] at h; exact h
private theorem d_7_32 : D 7 32 = false := by have h := D_step 5 31; rw [d_5_31, d_6_31, d_7_31] at h; exact h
private theorem d_8_32 : D 8 32 = true := by have h := D_step 6 31; rw [d_6_31, d_7_31, d_8_31] at h; exact h
private theorem d_9_32 : D 9 32 = true := by have h := D_step 7 31; rw [d_7_31, d_8_31, d_9_31] at h; exact h
private theorem d_10_32 : D 10 32 = true := by have h := D_step 8 31; rw [d_8_31, d_9_31, d_10_31] at h; exact h
private theorem d_11_32 : D 11 32 = false := by have h := D_step 9 31; rw [d_9_31, d_10_31, d_11_31] at h; exact h
private theorem d_12_32 : D 12 32 = false := by have h := D_step 10 31; rw [d_10_31, d_11_31, d_12_31] at h; exact h
private theorem d_13_32 : D 13 32 = true := by have h := D_step 11 31; rw [d_11_31, d_12_31, d_13_31] at h; exact h
private theorem d_14_32 : D 14 32 = true := by have h := D_step 12 31; rw [d_12_31, d_13_31, d_14_31] at h; exact h
private theorem d_15_32 : D 15 32 = true := by have h := D_step 13 31; rw [d_13_31, d_14_31, d_15_31] at h; exact h
private theorem d_16_32 : D 16 32 = true := by have h := D_step 14 31; rw [d_14_31, d_15_31, d_16_31] at h; exact h
private theorem d_17_32 : D 17 32 = false := by have h := D_step 15 31; rw [d_15_31, d_16_31, d_17_31] at h; exact h
private theorem d_18_32 : D 18 32 = false := by have h := D_step 16 31; rw [d_16_31, d_17_31, d_18_31] at h; exact h
private theorem d_19_32 : D 19 32 = false := by have h := D_step 17 31; rw [d_17_31, d_18_31, d_19_31] at h; exact h
private theorem d_20_32 : D 20 32 = true := by have h := D_step 18 31; rw [d_18_31, d_19_31, d_20_31] at h; exact h
private theorem d_21_32 : D 21 32 = true := by have h := D_step 19 31; rw [d_19_31, d_20_31, d_21_31] at h; exact h
private theorem d_22_32 : D 22 32 = true := by have h := D_step 20 31; rw [d_20_31, d_21_31, d_22_31] at h; exact h
private theorem d_23_32 : D 23 32 = true := by have h := D_step 21 31; rw [d_21_31, d_22_31, d_23_31] at h; exact h
private theorem d_24_32 : D 24 32 = false := by have h := D_step 22 31; rw [d_22_31, d_23_31, d_24_31] at h; exact h
private theorem d_25_32 : D 25 32 = true := by have h := D_step 23 31; rw [d_23_31, d_24_31, d_25_31] at h; exact h
private theorem d_26_32 : D 26 32 = false := by have h := D_step 24 31; rw [d_24_31, d_25_31, d_26_31] at h; exact h
private theorem d_27_32 : D 27 32 = false := by have h := D_step 25 31; rw [d_25_31, d_26_31, d_27_31] at h; exact h
private theorem d_31_32 : D 31 32 = false := by have h := D_step 29 31; rw [d_29_31, d_30_31, d_31_31] at h; exact h
private theorem d_32_32 : D 32 32 = false := by have h := D_step 30 31; rw [d_30_31, d_31_31, d_32_31] at h; exact h
private theorem d_33_32 : D 33 32 = true := by have h := D_step 31 31; rw [d_31_31, d_32_31, d_33_31] at h; exact h
private theorem d_34_32 : D 34 32 = true := by have h := D_step 32 31; rw [d_32_31, d_33_31, d_34_31] at h; exact h
private theorem d_0_33 : D 0 33 = true := D_zero 33
private theorem d_1_33 : D 1 33 = true := by simpa using D_one 32
private theorem d_2_33 : D 2 33 = false := by have h := D_step 0 32; rw [d_0_32, d_1_32, d_2_32] at h; exact h
private theorem d_3_33 : D 3 33 = true := by have h := D_step 1 32; rw [d_1_32, d_2_32, d_3_32] at h; exact h
private theorem d_4_33 : D 4 33 = true := by have h := D_step 2 32; rw [d_2_32, d_3_32, d_4_32] at h; exact h
private theorem d_5_33 : D 5 33 = true := by have h := D_step 3 32; rw [d_3_32, d_4_32, d_5_32] at h; exact h
private theorem d_6_33 : D 6 33 = true := by have h := D_step 4 32; rw [d_4_32, d_5_32, d_6_32] at h; exact h
private theorem d_7_33 : D 7 33 = false := by have h := D_step 5 32; rw [d_5_32, d_6_32, d_7_32] at h; exact h
private theorem d_8_33 : D 8 33 = true := by have h := D_step 6 32; rw [d_6_32, d_7_32, d_8_32] at h; exact h
private theorem d_9_33 : D 9 33 = true := by have h := D_step 7 32; rw [d_7_32, d_8_32, d_9_32] at h; exact h
private theorem d_10_33 : D 10 33 = false := by have h := D_step 8 32; rw [d_8_32, d_9_32, d_10_32] at h; exact h
private theorem d_11_33 : D 11 33 = false := by have h := D_step 9 32; rw [d_9_32, d_10_32, d_11_32] at h; exact h
private theorem d_12_33 : D 12 33 = true := by have h := D_step 10 32; rw [d_10_32, d_11_32, d_12_32] at h; exact h
private theorem d_13_33 : D 13 33 = true := by have h := D_step 11 32; rw [d_11_32, d_12_32, d_13_32] at h; exact h
private theorem d_14_33 : D 14 33 = true := by have h := D_step 12 32; rw [d_12_32, d_13_32, d_14_32] at h; exact h
private theorem d_15_33 : D 15 33 = false := by have h := D_step 13 32; rw [d_13_32, d_14_32, d_15_32] at h; exact h
private theorem d_16_33 : D 16 33 = false := by have h := D_step 14 32; rw [d_14_32, d_15_32, d_16_32] at h; exact h
private theorem d_17_33 : D 17 33 = false := by have h := D_step 15 32; rw [d_15_32, d_16_32, d_17_32] at h; exact h
private theorem d_18_33 : D 18 33 = true := by have h := D_step 16 32; rw [d_16_32, d_17_32, d_18_32] at h; exact h
private theorem d_19_33 : D 19 33 = false := by have h := D_step 17 32; rw [d_17_32, d_18_32, d_19_32] at h; exact h
private theorem d_20_33 : D 20 33 = true := by have h := D_step 18 32; rw [d_18_32, d_19_32, d_20_32] at h; exact h
private theorem d_21_33 : D 21 33 = true := by have h := D_step 19 32; rw [d_19_32, d_20_32, d_21_32] at h; exact h
private theorem d_22_33 : D 22 33 = false := by have h := D_step 20 32; rw [d_20_32, d_21_32, d_22_32] at h; exact h
private theorem d_23_33 : D 23 33 = false := by have h := D_step 21 32; rw [d_21_32, d_22_32, d_23_32] at h; exact h
private theorem d_24_33 : D 24 33 = false := by have h := D_step 22 32; rw [d_22_32, d_23_32, d_24_32] at h; exact h
private theorem d_25_33 : D 25 33 = false := by have h := D_step 23 32; rw [d_23_32, d_24_32, d_25_32] at h; exact h
private theorem d_26_33 : D 26 33 = true := by have h := D_step 24 32; rw [d_24_32, d_25_32, d_26_32] at h; exact h
private theorem d_27_33 : D 27 33 = true := by have h := D_step 25 32; rw [d_25_32, d_26_32, d_27_32] at h; exact h
private theorem d_28_33 : D 28 33 = false := by have h := D_step 26 32; rw [d_26_32, d_27_32, d_28_32] at h; exact h
private theorem d_29_33 : D 29 33 = true := by have h := D_step 27 32; rw [d_27_32, d_28_32, d_29_32] at h; exact h
private theorem d_31_33 : D 31 33 = true := by have h := D_step 29 32; rw [d_29_32, d_30_32, d_31_32] at h; exact h
private theorem d_32_33 : D 32 33 = false := by have h := D_step 30 32; rw [d_30_32, d_31_32, d_32_32] at h; exact h
private theorem d_33_33 : D 33 33 = true := by have h := D_step 31 32; rw [d_31_32, d_32_32, d_33_32] at h; exact h
private theorem d_34_33 : D 34 33 = true := by have h := D_step 32 32; rw [d_32_32, d_33_32, d_34_32] at h; exact h
private theorem d_0_34 : D 0 34 = true := D_zero 34
private theorem d_1_34 : D 1 34 = true := by simpa using D_one 33
private theorem d_2_34 : D 2 34 = false := by have h := D_step 0 33; rw [d_0_33, d_1_33, d_2_33] at h; exact h
private theorem d_3_34 : D 3 34 = false := by have h := D_step 1 33; rw [d_1_33, d_2_33, d_3_33] at h; exact h
private theorem d_4_34 : D 4 34 = true := by have h := D_step 2 33; rw [d_2_33, d_3_33, d_4_33] at h; exact h
private theorem d_5_34 : D 5 34 = false := by have h := D_step 3 33; rw [d_3_33, d_4_33, d_5_33] at h; exact h
private theorem d_6_34 : D 6 34 = false := by have h := D_step 4 33; rw [d_4_33, d_5_33, d_6_33] at h; exact h
private theorem d_7_34 : D 7 34 = false := by have h := D_step 5 33; rw [d_5_33, d_6_33, d_7_33] at h; exact h
private theorem d_8_34 : D 8 34 = false := by have h := D_step 6 33; rw [d_6_33, d_7_33, d_8_33] at h; exact h
private theorem d_9_34 : D 9 34 = true := by have h := D_step 7 33; rw [d_7_33, d_8_33, d_9_33] at h; exact h
private theorem d_10_34 : D 10 34 = false := by have h := D_step 8 33; rw [d_8_33, d_9_33, d_10_33] at h; exact h
private theorem d_11_34 : D 11 34 = true := by have h := D_step 9 33; rw [d_9_33, d_10_33, d_11_33] at h; exact h
private theorem d_12_34 : D 12 34 = true := by have h := D_step 10 33; rw [d_10_33, d_11_33, d_12_33] at h; exact h
private theorem d_13_34 : D 13 34 = true := by have h := D_step 11 33; rw [d_11_33, d_12_33, d_13_33] at h; exact h
private theorem d_14_34 : D 14 34 = false := by have h := D_step 12 33; rw [d_12_33, d_13_33, d_14_33] at h; exact h
private theorem d_15_34 : D 15 34 = false := by have h := D_step 13 33; rw [d_13_33, d_14_33, d_15_33] at h; exact h
private theorem d_16_34 : D 16 34 = true := by have h := D_step 14 33; rw [d_14_33, d_15_33, d_16_33] at h; exact h
private theorem d_17_34 : D 17 34 = false := by have h := D_step 15 33; rw [d_15_33, d_16_33, d_17_33] at h; exact h
private theorem d_18_34 : D 18 34 = true := by have h := D_step 16 33; rw [d_16_33, d_17_33, d_18_33] at h; exact h
private theorem d_19_34 : D 19 34 = true := by have h := D_step 17 33; rw [d_17_33, d_18_33, d_19_33] at h; exact h
private theorem d_20_34 : D 20 34 = false := by have h := D_step 18 33; rw [d_18_33, d_19_33, d_20_33] at h; exact h
private theorem d_21_34 : D 21 34 = true := by have h := D_step 19 33; rw [d_19_33, d_20_33, d_21_33] at h; exact h
private theorem d_22_34 : D 22 34 = false := by have h := D_step 20 33; rw [d_20_33, d_21_33, d_22_33] at h; exact h
private theorem d_23_34 : D 23 34 = true := by have h := D_step 21 33; rw [d_21_33, d_22_33, d_23_33] at h; exact h
private theorem d_24_34 : D 24 34 = false := by have h := D_step 22 33; rw [d_22_33, d_23_33, d_24_33] at h; exact h
private theorem d_25_34 : D 25 34 = false := by have h := D_step 23 33; rw [d_23_33, d_24_33, d_25_33] at h; exact h
private theorem d_26_34 : D 26 34 = true := by have h := D_step 24 33; rw [d_24_33, d_25_33, d_26_33] at h; exact h
private theorem d_27_34 : D 27 34 = true := by have h := D_step 25 33; rw [d_25_33, d_26_33, d_27_33] at h; exact h
private theorem d_28_34 : D 28 34 = false := by have h := D_step 26 33; rw [d_26_33, d_27_33, d_28_33] at h; exact h
private theorem d_29_34 : D 29 34 = false := by have h := D_step 27 33; rw [d_27_33, d_28_33, d_29_33] at h; exact h
private theorem d_30_34 : D 30 34 = true := by have h := D_step 28 33; rw [d_28_33, d_29_33, d_30_33] at h; exact h
private theorem d_31_34 : D 31 34 = false := by have h := D_step 29 33; rw [d_29_33, d_30_33, d_31_33] at h; exact h
private theorem d_32_34 : D 32 34 = false := by have h := D_step 30 33; rw [d_30_33, d_31_33, d_32_33] at h; exact h
private theorem d_33_34 : D 33 34 = false := by have h := D_step 31 33; rw [d_31_33, d_32_33, d_33_33] at h; exact h
private theorem d_34_34 : D 34 34 = true := by have h := D_step 32 33; rw [d_32_33, d_33_33, d_34_33] at h; exact h
private theorem d_0_35 : D 0 35 = true := D_zero 35
private theorem d_1_35 : D 1 35 = true := by simpa using D_one 34
private theorem d_2_35 : D 2 35 = false := by have h := D_step 0 34; rw [d_0_34, d_1_34, d_2_34] at h; exact h
private theorem d_3_35 : D 3 35 = true := by have h := D_step 1 34; rw [d_1_34, d_2_34, d_3_34] at h; exact h
private theorem d_4_35 : D 4 35 = true := by have h := D_step 2 34; rw [d_2_34, d_3_34, d_4_34] at h; exact h
private theorem d_5_35 : D 5 35 = true := by have h := D_step 3 34; rw [d_3_34, d_4_34, d_5_34] at h; exact h
private theorem d_6_35 : D 6 35 = true := by have h := D_step 4 34; rw [d_4_34, d_5_34, d_6_34] at h; exact h
private theorem d_7_35 : D 7 35 = false := by have h := D_step 5 34; rw [d_5_34, d_6_34, d_7_34] at h; exact h
private theorem d_8_35 : D 8 35 = false := by have h := D_step 6 34; rw [d_6_34, d_7_34, d_8_34] at h; exact h
private theorem d_9_35 : D 9 35 = true := by have h := D_step 7 34; rw [d_7_34, d_8_34, d_9_34] at h; exact h
private theorem d_10_35 : D 10 35 = true := by have h := D_step 8 34; rw [d_8_34, d_9_34, d_10_34] at h; exact h
private theorem d_11_35 : D 11 35 = false := by have h := D_step 9 34; rw [d_9_34, d_10_34, d_11_34] at h; exact h
private theorem d_12_35 : D 12 35 = true := by have h := D_step 10 34; rw [d_10_34, d_11_34, d_12_34] at h; exact h
private theorem d_13_35 : D 13 35 = false := by have h := D_step 11 34; rw [d_11_34, d_12_34, d_13_34] at h; exact h
private theorem d_14_35 : D 14 35 = false := by have h := D_step 12 34; rw [d_12_34, d_13_34, d_14_34] at h; exact h
private theorem d_15_35 : D 15 35 = true := by have h := D_step 13 34; rw [d_13_34, d_14_34, d_15_34] at h; exact h
private theorem d_16_35 : D 16 35 = true := by have h := D_step 14 34; rw [d_14_34, d_15_34, d_16_34] at h; exact h
private theorem d_17_35 : D 17 35 = true := by have h := D_step 15 34; rw [d_15_34, d_16_34, d_17_34] at h; exact h
private theorem d_18_35 : D 18 35 = false := by have h := D_step 16 34; rw [d_16_34, d_17_34, d_18_34] at h; exact h
private theorem d_19_35 : D 19 35 = true := by have h := D_step 17 34; rw [d_17_34, d_18_34, d_19_34] at h; exact h
private theorem d_20_35 : D 20 35 = false := by have h := D_step 18 34; rw [d_18_34, d_19_34, d_20_34] at h; exact h
private theorem d_21_35 : D 21 35 = false := by have h := D_step 19 34; rw [d_19_34, d_20_34, d_21_34] at h; exact h
private theorem d_22_35 : D 22 35 = true := by have h := D_step 20 34; rw [d_20_34, d_21_34, d_22_34] at h; exact h
private theorem d_23_35 : D 23 35 = false := by have h := D_step 21 34; rw [d_21_34, d_22_34, d_23_34] at h; exact h
private theorem d_24_35 : D 24 35 = true := by have h := D_step 22 34; rw [d_22_34, d_23_34, d_24_34] at h; exact h
private theorem d_25_35 : D 25 35 = true := by have h := D_step 23 34; rw [d_23_34, d_24_34, d_25_34] at h; exact h
private theorem d_26_35 : D 26 35 = true := by have h := D_step 24 34; rw [d_24_34, d_25_34, d_26_34] at h; exact h
private theorem d_27_35 : D 27 35 = true := by have h := D_step 25 34; rw [d_25_34, d_26_34, d_27_34] at h; exact h
private theorem d_28_35 : D 28 35 = false := by have h := D_step 26 34; rw [d_26_34, d_27_34, d_28_34] at h; exact h
private theorem d_29_35 : D 29 35 = true := by have h := D_step 27 34; rw [d_27_34, d_28_34, d_29_34] at h; exact h
private theorem d_30_35 : D 30 35 = true := by have h := D_step 28 34; rw [d_28_34, d_29_34, d_30_34] at h; exact h
private theorem d_31_35 : D 31 35 = true := by have h := D_step 29 34; rw [d_29_34, d_30_34, d_31_34] at h; exact h
private theorem d_32_35 : D 32 35 = true := by have h := D_step 30 34; rw [d_30_34, d_31_34, d_32_34] at h; exact h
private theorem d_33_35 : D 33 35 = false := by have h := D_step 31 34; rw [d_31_34, d_32_34, d_33_34] at h; exact h
private theorem d_34_35 : D 34 35 = true := by have h := D_step 32 34; rw [d_32_34, d_33_34, d_34_34] at h; exact h
private theorem d_0_36 : D 0 36 = true := D_zero 36
private theorem d_1_36 : D 1 36 = true := by simpa using D_one 35
private theorem d_2_36 : D 2 36 = false := by have h := D_step 0 35; rw [d_0_35, d_1_35, d_2_35] at h; exact h
private theorem d_3_36 : D 3 36 = false := by have h := D_step 1 35; rw [d_1_35, d_2_35, d_3_35] at h; exact h
private theorem d_4_36 : D 4 36 = true := by have h := D_step 2 35; rw [d_2_35, d_3_35, d_4_35] at h; exact h
private theorem d_5_36 : D 5 36 = false := by have h := D_step 3 35; rw [d_3_35, d_4_35, d_5_35] at h; exact h
private theorem d_6_36 : D 6 36 = false := by have h := D_step 4 35; rw [d_4_35, d_5_35, d_6_35] at h; exact h
private theorem d_7_36 : D 7 36 = false := by have h := D_step 5 35; rw [d_5_35, d_6_35, d_7_35] at h; exact h
private theorem d_8_36 : D 8 36 = true := by have h := D_step 6 35; rw [d_6_35, d_7_35, d_8_35] at h; exact h
private theorem d_9_36 : D 9 36 = true := by have h := D_step 7 35; rw [d_7_35, d_8_35, d_9_35] at h; exact h
private theorem d_10_36 : D 10 36 = true := by have h := D_step 8 35; rw [d_8_35, d_9_35, d_10_35] at h; exact h
private theorem d_11_36 : D 11 36 = false := by have h := D_step 9 35; rw [d_9_35, d_10_35, d_11_35] at h; exact h
private theorem d_12_36 : D 12 36 = false := by have h := D_step 10 35; rw [d_10_35, d_11_35, d_12_35] at h; exact h
private theorem d_13_36 : D 13 36 = true := by have h := D_step 11 35; rw [d_11_35, d_12_35, d_13_35] at h; exact h
private theorem d_14_36 : D 14 36 = true := by have h := D_step 12 35; rw [d_12_35, d_13_35, d_14_35] at h; exact h
private theorem d_15_36 : D 15 36 = true := by have h := D_step 13 35; rw [d_13_35, d_14_35, d_15_35] at h; exact h
private theorem d_16_36 : D 16 36 = true := by have h := D_step 14 35; rw [d_14_35, d_15_35, d_16_35] at h; exact h
private theorem d_17_36 : D 17 36 = false := by have h := D_step 15 35; rw [d_15_35, d_16_35, d_17_35] at h; exact h
private theorem d_18_36 : D 18 36 = false := by have h := D_step 16 35; rw [d_16_35, d_17_35, d_18_35] at h; exact h
private theorem d_19_36 : D 19 36 = false := by have h := D_step 17 35; rw [d_17_35, d_18_35, d_19_35] at h; exact h
private theorem d_20_36 : D 20 36 = true := by have h := D_step 18 35; rw [d_18_35, d_19_35, d_20_35] at h; exact h
private theorem d_21_36 : D 21 36 = true := by have h := D_step 19 35; rw [d_19_35, d_20_35, d_21_35] at h; exact h
private theorem d_22_36 : D 22 36 = true := by have h := D_step 20 35; rw [d_20_35, d_21_35, d_22_35] at h; exact h
private theorem d_23_36 : D 23 36 = true := by have h := D_step 21 35; rw [d_21_35, d_22_35, d_23_35] at h; exact h
private theorem d_24_36 : D 24 36 = false := by have h := D_step 22 35; rw [d_22_35, d_23_35, d_24_35] at h; exact h
private theorem d_25_36 : D 25 36 = true := by have h := D_step 23 35; rw [d_23_35, d_24_35, d_25_35] at h; exact h
private theorem d_26_36 : D 26 36 = false := by have h := D_step 24 35; rw [d_24_35, d_25_35, d_26_35] at h; exact h
private theorem d_27_36 : D 27 36 = false := by have h := D_step 25 35; rw [d_25_35, d_26_35, d_27_35] at h; exact h
private theorem d_28_36 : D 28 36 = false := by have h := D_step 26 35; rw [d_26_35, d_27_35, d_28_35] at h; exact h
private theorem d_29_36 : D 29 36 = false := by have h := D_step 27 35; rw [d_27_35, d_28_35, d_29_35] at h; exact h
private theorem d_30_36 : D 30 36 = true := by have h := D_step 28 35; rw [d_28_35, d_29_35, d_30_35] at h; exact h
private theorem d_31_36 : D 31 36 = false := by have h := D_step 29 35; rw [d_29_35, d_30_35, d_31_35] at h; exact h
private theorem d_32_36 : D 32 36 = false := by have h := D_step 30 35; rw [d_30_35, d_31_35, d_32_35] at h; exact h
private theorem d_33_36 : D 33 36 = false := by have h := D_step 31 35; rw [d_31_35, d_32_35, d_33_35] at h; exact h
private theorem d_34_36 : D 34 36 = false := by have h := D_step 32 35; rw [d_32_35, d_33_35, d_34_35] at h; exact h
private theorem d_0_37 : D 0 37 = true := D_zero 37
private theorem d_1_37 : D 1 37 = true := by simpa using D_one 36
private theorem d_2_37 : D 2 37 = false := by have h := D_step 0 36; rw [d_0_36, d_1_36, d_2_36] at h; exact h
private theorem d_3_37 : D 3 37 = true := by have h := D_step 1 36; rw [d_1_36, d_2_36, d_3_36] at h; exact h
private theorem d_4_37 : D 4 37 = true := by have h := D_step 2 36; rw [d_2_36, d_3_36, d_4_36] at h; exact h
private theorem d_5_37 : D 5 37 = true := by have h := D_step 3 36; rw [d_3_36, d_4_36, d_5_36] at h; exact h
private theorem d_6_37 : D 6 37 = true := by have h := D_step 4 36; rw [d_4_36, d_5_36, d_6_36] at h; exact h
private theorem d_7_37 : D 7 37 = false := by have h := D_step 5 36; rw [d_5_36, d_6_36, d_7_36] at h; exact h
private theorem d_8_37 : D 8 37 = true := by have h := D_step 6 36; rw [d_6_36, d_7_36, d_8_36] at h; exact h
private theorem d_9_37 : D 9 37 = true := by have h := D_step 7 36; rw [d_7_36, d_8_36, d_9_36] at h; exact h
private theorem d_10_37 : D 10 37 = false := by have h := D_step 8 36; rw [d_8_36, d_9_36, d_10_36] at h; exact h
private theorem d_11_37 : D 11 37 = false := by have h := D_step 9 36; rw [d_9_36, d_10_36, d_11_36] at h; exact h
private theorem d_12_37 : D 12 37 = true := by have h := D_step 10 36; rw [d_10_36, d_11_36, d_12_36] at h; exact h
private theorem d_13_37 : D 13 37 = true := by have h := D_step 11 36; rw [d_11_36, d_12_36, d_13_36] at h; exact h
private theorem d_14_37 : D 14 37 = true := by have h := D_step 12 36; rw [d_12_36, d_13_36, d_14_36] at h; exact h
private theorem d_15_37 : D 15 37 = false := by have h := D_step 13 36; rw [d_13_36, d_14_36, d_15_36] at h; exact h
private theorem d_16_37 : D 16 37 = false := by have h := D_step 14 36; rw [d_14_36, d_15_36, d_16_36] at h; exact h
private theorem d_17_37 : D 17 37 = false := by have h := D_step 15 36; rw [d_15_36, d_16_36, d_17_36] at h; exact h
private theorem d_18_37 : D 18 37 = true := by have h := D_step 16 36; rw [d_16_36, d_17_36, d_18_36] at h; exact h
private theorem d_19_37 : D 19 37 = false := by have h := D_step 17 36; rw [d_17_36, d_18_36, d_19_36] at h; exact h
private theorem d_20_37 : D 20 37 = true := by have h := D_step 18 36; rw [d_18_36, d_19_36, d_20_36] at h; exact h
private theorem d_21_37 : D 21 37 = true := by have h := D_step 19 36; rw [d_19_36, d_20_36, d_21_36] at h; exact h
private theorem d_22_37 : D 22 37 = false := by have h := D_step 20 36; rw [d_20_36, d_21_36, d_22_36] at h; exact h
private theorem d_23_37 : D 23 37 = false := by have h := D_step 21 36; rw [d_21_36, d_22_36, d_23_36] at h; exact h
private theorem d_24_37 : D 24 37 = false := by have h := D_step 22 36; rw [d_22_36, d_23_36, d_24_36] at h; exact h
private theorem d_25_37 : D 25 37 = false := by have h := D_step 23 36; rw [d_23_36, d_24_36, d_25_36] at h; exact h
private theorem d_26_37 : D 26 37 = true := by have h := D_step 24 36; rw [d_24_36, d_25_36, d_26_36] at h; exact h
private theorem d_27_37 : D 27 37 = true := by have h := D_step 25 36; rw [d_25_36, d_26_36, d_27_36] at h; exact h
private theorem d_28_37 : D 28 37 = false := by have h := D_step 26 36; rw [d_26_36, d_27_36, d_28_36] at h; exact h
private theorem d_29_37 : D 29 37 = false := by have h := D_step 27 36; rw [d_27_36, d_28_36, d_29_36] at h; exact h
private theorem d_30_37 : D 30 37 = true := by have h := D_step 28 36; rw [d_28_36, d_29_36, d_30_36] at h; exact h
private theorem d_31_37 : D 31 37 = true := by have h := D_step 29 36; rw [d_29_36, d_30_36, d_31_36] at h; exact h
private theorem d_32_37 : D 32 37 = true := by have h := D_step 30 36; rw [d_30_36, d_31_36, d_32_36] at h; exact h
private theorem d_33_37 : D 33 37 = false := by have h := D_step 31 36; rw [d_31_36, d_32_36, d_33_36] at h; exact h
private theorem d_34_37 : D 34 37 = false := by have h := D_step 32 36; rw [d_32_36, d_33_36, d_34_36] at h; exact h
private theorem d_0_38 : D 0 38 = true := D_zero 38
private theorem d_1_38 : D 1 38 = true := by simpa using D_one 37
private theorem d_2_38 : D 2 38 = false := by have h := D_step 0 37; rw [d_0_37, d_1_37, d_2_37] at h; exact h
private theorem d_3_38 : D 3 38 = false := by have h := D_step 1 37; rw [d_1_37, d_2_37, d_3_37] at h; exact h
private theorem d_4_38 : D 4 38 = true := by have h := D_step 2 37; rw [d_2_37, d_3_37, d_4_37] at h; exact h
private theorem d_5_38 : D 5 38 = false := by have h := D_step 3 37; rw [d_3_37, d_4_37, d_5_37] at h; exact h
private theorem d_6_38 : D 6 38 = false := by have h := D_step 4 37; rw [d_4_37, d_5_37, d_6_37] at h; exact h
private theorem d_7_38 : D 7 38 = false := by have h := D_step 5 37; rw [d_5_37, d_6_37, d_7_37] at h; exact h
private theorem d_8_38 : D 8 38 = false := by have h := D_step 6 37; rw [d_6_37, d_7_37, d_8_37] at h; exact h
private theorem d_9_38 : D 9 38 = true := by have h := D_step 7 37; rw [d_7_37, d_8_37, d_9_37] at h; exact h
private theorem d_10_38 : D 10 38 = false := by have h := D_step 8 37; rw [d_8_37, d_9_37, d_10_37] at h; exact h
private theorem d_11_38 : D 11 38 = true := by have h := D_step 9 37; rw [d_9_37, d_10_37, d_11_37] at h; exact h
private theorem d_12_38 : D 12 38 = true := by have h := D_step 10 37; rw [d_10_37, d_11_37, d_12_37] at h; exact h
private theorem d_13_38 : D 13 38 = true := by have h := D_step 11 37; rw [d_11_37, d_12_37, d_13_37] at h; exact h
private theorem d_14_38 : D 14 38 = false := by have h := D_step 12 37; rw [d_12_37, d_13_37, d_14_37] at h; exact h
private theorem d_15_38 : D 15 38 = false := by have h := D_step 13 37; rw [d_13_37, d_14_37, d_15_37] at h; exact h
private theorem d_16_38 : D 16 38 = true := by have h := D_step 14 37; rw [d_14_37, d_15_37, d_16_37] at h; exact h
private theorem d_17_38 : D 17 38 = false := by have h := D_step 15 37; rw [d_15_37, d_16_37, d_17_37] at h; exact h
private theorem d_18_38 : D 18 38 = true := by have h := D_step 16 37; rw [d_16_37, d_17_37, d_18_37] at h; exact h
private theorem d_19_38 : D 19 38 = true := by have h := D_step 17 37; rw [d_17_37, d_18_37, d_19_37] at h; exact h
private theorem d_20_38 : D 20 38 = false := by have h := D_step 18 37; rw [d_18_37, d_19_37, d_20_37] at h; exact h
private theorem d_21_38 : D 21 38 = true := by have h := D_step 19 37; rw [d_19_37, d_20_37, d_21_37] at h; exact h
private theorem d_22_38 : D 22 38 = false := by have h := D_step 20 37; rw [d_20_37, d_21_37, d_22_37] at h; exact h
private theorem d_23_38 : D 23 38 = true := by have h := D_step 21 37; rw [d_21_37, d_22_37, d_23_37] at h; exact h
private theorem d_24_38 : D 24 38 = false := by have h := D_step 22 37; rw [d_22_37, d_23_37, d_24_37] at h; exact h
private theorem d_25_38 : D 25 38 = false := by have h := D_step 23 37; rw [d_23_37, d_24_37, d_25_37] at h; exact h
private theorem d_26_38 : D 26 38 = true := by have h := D_step 24 37; rw [d_24_37, d_25_37, d_26_37] at h; exact h
private theorem d_27_38 : D 27 38 = true := by have h := D_step 25 37; rw [d_25_37, d_26_37, d_27_37] at h; exact h
private theorem d_28_38 : D 28 38 = false := by have h := D_step 26 37; rw [d_26_37, d_27_37, d_28_37] at h; exact h
private theorem d_29_38 : D 29 38 = true := by have h := D_step 27 37; rw [d_27_37, d_28_37, d_29_37] at h; exact h
private theorem d_30_38 : D 30 38 = true := by have h := D_step 28 37; rw [d_28_37, d_29_37, d_30_37] at h; exact h
private theorem d_31_38 : D 31 38 = true := by have h := D_step 29 37; rw [d_29_37, d_30_37, d_31_37] at h; exact h
private theorem d_32_38 : D 32 38 = false := by have h := D_step 30 37; rw [d_30_37, d_31_37, d_32_37] at h; exact h
private theorem d_33_38 : D 33 38 = false := by have h := D_step 31 37; rw [d_31_37, d_32_37, d_33_37] at h; exact h
private theorem d_34_38 : D 34 38 = true := by have h := D_step 32 37; rw [d_32_37, d_33_37, d_34_37] at h; exact h
private theorem d_0_39 : D 0 39 = true := D_zero 39
private theorem d_1_39 : D 1 39 = true := by simpa using D_one 38
private theorem d_2_39 : D 2 39 = false := by have h := D_step 0 38; rw [d_0_38, d_1_38, d_2_38] at h; exact h
private theorem d_3_39 : D 3 39 = true := by have h := D_step 1 38; rw [d_1_38, d_2_38, d_3_38] at h; exact h
private theorem d_4_39 : D 4 39 = true := by have h := D_step 2 38; rw [d_2_38, d_3_38, d_4_38] at h; exact h
private theorem d_5_39 : D 5 39 = true := by have h := D_step 3 38; rw [d_3_38, d_4_38, d_5_38] at h; exact h
private theorem d_6_39 : D 6 39 = true := by have h := D_step 4 38; rw [d_4_38, d_5_38, d_6_38] at h; exact h
private theorem d_7_39 : D 7 39 = false := by have h := D_step 5 38; rw [d_5_38, d_6_38, d_7_38] at h; exact h
private theorem d_8_39 : D 8 39 = false := by have h := D_step 6 38; rw [d_6_38, d_7_38, d_8_38] at h; exact h
private theorem d_9_39 : D 9 39 = true := by have h := D_step 7 38; rw [d_7_38, d_8_38, d_9_38] at h; exact h
private theorem d_10_39 : D 10 39 = true := by have h := D_step 8 38; rw [d_8_38, d_9_38, d_10_38] at h; exact h
private theorem d_11_39 : D 11 39 = false := by have h := D_step 9 38; rw [d_9_38, d_10_38, d_11_38] at h; exact h
private theorem d_12_39 : D 12 39 = true := by have h := D_step 10 38; rw [d_10_38, d_11_38, d_12_38] at h; exact h
private theorem d_13_39 : D 13 39 = false := by have h := D_step 11 38; rw [d_11_38, d_12_38, d_13_38] at h; exact h
private theorem d_14_39 : D 14 39 = false := by have h := D_step 12 38; rw [d_12_38, d_13_38, d_14_38] at h; exact h
private theorem d_15_39 : D 15 39 = true := by have h := D_step 13 38; rw [d_13_38, d_14_38, d_15_38] at h; exact h
private theorem d_16_39 : D 16 39 = true := by have h := D_step 14 38; rw [d_14_38, d_15_38, d_16_38] at h; exact h
private theorem d_17_39 : D 17 39 = true := by have h := D_step 15 38; rw [d_15_38, d_16_38, d_17_38] at h; exact h
private theorem d_18_39 : D 18 39 = false := by have h := D_step 16 38; rw [d_16_38, d_17_38, d_18_38] at h; exact h
private theorem d_19_39 : D 19 39 = true := by have h := D_step 17 38; rw [d_17_38, d_18_38, d_19_38] at h; exact h
private theorem d_20_39 : D 20 39 = false := by have h := D_step 18 38; rw [d_18_38, d_19_38, d_20_38] at h; exact h
private theorem d_21_39 : D 21 39 = false := by have h := D_step 19 38; rw [d_19_38, d_20_38, d_21_38] at h; exact h
private theorem d_22_39 : D 22 39 = true := by have h := D_step 20 38; rw [d_20_38, d_21_38, d_22_38] at h; exact h
private theorem d_23_39 : D 23 39 = false := by have h := D_step 21 38; rw [d_21_38, d_22_38, d_23_38] at h; exact h
private theorem d_24_39 : D 24 39 = true := by have h := D_step 22 38; rw [d_22_38, d_23_38, d_24_38] at h; exact h
private theorem d_25_39 : D 25 39 = true := by have h := D_step 23 38; rw [d_23_38, d_24_38, d_25_38] at h; exact h
private theorem d_26_39 : D 26 39 = true := by have h := D_step 24 38; rw [d_24_38, d_25_38, d_26_38] at h; exact h
private theorem d_27_39 : D 27 39 = true := by have h := D_step 25 38; rw [d_25_38, d_26_38, d_27_38] at h; exact h
private theorem d_28_39 : D 28 39 = false := by have h := D_step 26 38; rw [d_26_38, d_27_38, d_28_38] at h; exact h
private theorem d_29_39 : D 29 39 = false := by have h := D_step 27 38; rw [d_27_38, d_28_38, d_29_38] at h; exact h
private theorem d_30_39 : D 30 39 = true := by have h := D_step 28 38; rw [d_28_38, d_29_38, d_30_38] at h; exact h
private theorem d_31_39 : D 31 39 = false := by have h := D_step 29 38; rw [d_29_38, d_30_38, d_31_38] at h; exact h
private theorem d_32_39 : D 32 39 = false := by have h := D_step 30 38; rw [d_30_38, d_31_38, d_32_38] at h; exact h
private theorem d_33_39 : D 33 39 = true := by have h := D_step 31 38; rw [d_31_38, d_32_38, d_33_38] at h; exact h
private theorem d_34_39 : D 34 39 = true := by have h := D_step 32 38; rw [d_32_38, d_33_38, d_34_38] at h; exact h
private theorem d_0_40 : D 0 40 = true := D_zero 40
private theorem d_1_40 : D 1 40 = true := by simpa using D_one 39
private theorem d_2_40 : D 2 40 = false := by have h := D_step 0 39; rw [d_0_39, d_1_39, d_2_39] at h; exact h
private theorem d_3_40 : D 3 40 = false := by have h := D_step 1 39; rw [d_1_39, d_2_39, d_3_39] at h; exact h
private theorem d_4_40 : D 4 40 = true := by have h := D_step 2 39; rw [d_2_39, d_3_39, d_4_39] at h; exact h
private theorem d_5_40 : D 5 40 = false := by have h := D_step 3 39; rw [d_3_39, d_4_39, d_5_39] at h; exact h
private theorem d_6_40 : D 6 40 = false := by have h := D_step 4 39; rw [d_4_39, d_5_39, d_6_39] at h; exact h
private theorem d_7_40 : D 7 40 = false := by have h := D_step 5 39; rw [d_5_39, d_6_39, d_7_39] at h; exact h
private theorem d_8_40 : D 8 40 = true := by have h := D_step 6 39; rw [d_6_39, d_7_39, d_8_39] at h; exact h
private theorem d_9_40 : D 9 40 = true := by have h := D_step 7 39; rw [d_7_39, d_8_39, d_9_39] at h; exact h
private theorem d_10_40 : D 10 40 = true := by have h := D_step 8 39; rw [d_8_39, d_9_39, d_10_39] at h; exact h
private theorem d_11_40 : D 11 40 = false := by have h := D_step 9 39; rw [d_9_39, d_10_39, d_11_39] at h; exact h
private theorem d_12_40 : D 12 40 = false := by have h := D_step 10 39; rw [d_10_39, d_11_39, d_12_39] at h; exact h
private theorem d_13_40 : D 13 40 = true := by have h := D_step 11 39; rw [d_11_39, d_12_39, d_13_39] at h; exact h
private theorem d_14_40 : D 14 40 = true := by have h := D_step 12 39; rw [d_12_39, d_13_39, d_14_39] at h; exact h
private theorem d_15_40 : D 15 40 = true := by have h := D_step 13 39; rw [d_13_39, d_14_39, d_15_39] at h; exact h
private theorem d_16_40 : D 16 40 = true := by have h := D_step 14 39; rw [d_14_39, d_15_39, d_16_39] at h; exact h
private theorem d_17_40 : D 17 40 = false := by have h := D_step 15 39; rw [d_15_39, d_16_39, d_17_39] at h; exact h
private theorem d_18_40 : D 18 40 = false := by have h := D_step 16 39; rw [d_16_39, d_17_39, d_18_39] at h; exact h
private theorem d_19_40 : D 19 40 = false := by have h := D_step 17 39; rw [d_17_39, d_18_39, d_19_39] at h; exact h
private theorem d_20_40 : D 20 40 = true := by have h := D_step 18 39; rw [d_18_39, d_19_39, d_20_39] at h; exact h
private theorem d_21_40 : D 21 40 = true := by have h := D_step 19 39; rw [d_19_39, d_20_39, d_21_39] at h; exact h
private theorem d_22_40 : D 22 40 = true := by have h := D_step 20 39; rw [d_20_39, d_21_39, d_22_39] at h; exact h
private theorem d_23_40 : D 23 40 = true := by have h := D_step 21 39; rw [d_21_39, d_22_39, d_23_39] at h; exact h
private theorem d_24_40 : D 24 40 = false := by have h := D_step 22 39; rw [d_22_39, d_23_39, d_24_39] at h; exact h
private theorem d_25_40 : D 25 40 = true := by have h := D_step 23 39; rw [d_23_39, d_24_39, d_25_39] at h; exact h
private theorem d_26_40 : D 26 40 = false := by have h := D_step 24 39; rw [d_24_39, d_25_39, d_26_39] at h; exact h
private theorem d_27_40 : D 27 40 = false := by have h := D_step 25 39; rw [d_25_39, d_26_39, d_27_39] at h; exact h
private theorem d_28_40 : D 28 40 = false := by have h := D_step 26 39; rw [d_26_39, d_27_39, d_28_39] at h; exact h
private theorem d_29_40 : D 29 40 = true := by have h := D_step 27 39; rw [d_27_39, d_28_39, d_29_39] at h; exact h
private theorem d_30_40 : D 30 40 = true := by have h := D_step 28 39; rw [d_28_39, d_29_39, d_30_39] at h; exact h
private theorem d_31_40 : D 31 40 = true := by have h := D_step 29 39; rw [d_29_39, d_30_39, d_31_39] at h; exact h
private theorem d_32_40 : D 32 40 = true := by have h := D_step 30 39; rw [d_30_39, d_31_39, d_32_39] at h; exact h
private theorem d_33_40 : D 33 40 = true := by have h := D_step 31 39; rw [d_31_39, d_32_39, d_33_39] at h; exact h
private theorem d_34_40 : D 34 40 = true := by have h := D_step 32 39; rw [d_32_39, d_33_39, d_34_39] at h; exact h

/-- **Three-Bit Gate Law for the Thirty-First Left Diagonal (`D_thirty_one_eq_gate`):**
for every `t ≥ 34`, `D 31 t = !xor (!(D 8 t && !D 10 t)) (D 29 t)`. -/
theorem D_thirty_one_eq_gate (t : Nat) (ht : 34 ≤ t) :
    D 31 t = !xor (!(D 8 t && !D 10 t)) (D 29 t) := by
  have hs31 := D_thirty_one_succ_eq_not_D_twenty_nine (t - 1) (by omega)
  have hs29 := D_twenty_nine_step_eq_xor_D_twenty_seven (t - 1) (by omega)
  have hg27 := D_twenty_seven_eq_nand_D_eight_D_ten (t - 1) (by omega)
  have a8 := D_eight_succ_eq_D_ten (t - 1) (by omega)
  have a10 := D_ten_succ_eq_not_D_eight (t - 1) (by omega)
  rw [show t - 1 + 1 = t by omega] at hs31 hs29 a8 a10
  rw [hs31]
  revert hs29 hg27 a8 a10
  cases D 8 (t - 1) <;> cases D 10 (t - 1) <;> cases D 8 t <;> cases D 10 t <;>
    cases D 27 (t - 1) <;> cases D 29 (t - 1) <;> cases D 29 t <;> decide

/-- **Three-Bit Gate Law for the Thirty-Second Left Diagonal (`D_thirty_two_eq_gate`):**
for every `t ≥ 36`, `D 32 t = ((!D 10 t && !D 29 t) || (D 8 t && D 10 t && D 29 t))`. -/
theorem D_thirty_two_eq_gate : ∀ t : Nat, 36 ≤ t →
    D 32 t = ((!D 10 t && !D 29 t) || (D 8 t && D 10 t && D 29 t))
  | 36, _ => by rw [d_32_36, d_8_36, d_10_36, d_29_36]; rfl
  | t + 1, ht => by
    by_cases h : t < 36
    · have h_eq : t + 1 = 36 := by omega
      rw [h_eq, d_32_36, d_8_36, d_10_36, d_29_36]; rfl
    · have ih := D_thirty_two_eq_gate t (by omega)
      have hstep := D_step 30 t
      rw [D_thirty_eq_true t (by omega), D_thirty_one_eq_gate t (by omega), ih] at hstep
      rw [hstep, D_eight_succ_eq_D_ten t (by omega), D_ten_succ_eq_not_D_eight t (by omega),
          D_twenty_nine_step_eq_xor_D_twenty_seven t (by omega),
          D_twenty_seven_eq_nand_D_eight_D_ten t (by omega)]
      cases D 8 t <;> cases D 10 t <;> cases D 29 t <;> decide

/-- **Three-Bit Gate Law for the Thirty-Third Left Diagonal (`D_thirty_three_eq_gate`):**
for every `t ≥ 36`, `D 33 t = (D 10 t && (!D 8 t || D 29 t))`. -/
theorem D_thirty_three_eq_gate : ∀ t : Nat, 36 ≤ t →
    D 33 t = (D 10 t && (!D 8 t || D 29 t))
  | 36, _ => by rw [d_33_36, d_8_36, d_10_36, d_29_36]; rfl
  | t + 1, ht => by
    by_cases h : t < 36
    · have h_eq : t + 1 = 36 := by omega
      rw [h_eq, d_33_36, d_8_36, d_10_36, d_29_36]; rfl
    · have ih := D_thirty_three_eq_gate t (by omega)
      have hstep := D_step 31 t
      rw [D_thirty_one_eq_gate t (by omega), D_thirty_two_eq_gate t (by omega), ih] at hstep
      rw [hstep, D_eight_succ_eq_D_ten t (by omega), D_ten_succ_eq_not_D_eight t (by omega),
          D_twenty_nine_step_eq_xor_D_twenty_seven t (by omega),
          D_twenty_seven_eq_nand_D_eight_D_ten t (by omega)]
      cases D 8 t <;> cases D 10 t <;> cases D 29 t <;> decide

/-- **Multiplexer Gate Law for the Thirty-Fourth Left Diagonal (`D_thirty_four_eq_mux`):**
for every `t ≥ 40`, `D 34 t = ((D 8 t && !D 29 t) || (D 10 t && D 29 t))`. -/
theorem D_thirty_four_eq_mux : ∀ t : Nat, 40 ≤ t →
    D 34 t = ((D 8 t && !D 29 t) || (D 10 t && D 29 t))
  | 40, _ => by rw [d_34_40, d_8_40, d_10_40, d_29_40]; rfl
  | t + 1, ht => by
    by_cases h : t < 40
    · have h_eq : t + 1 = 40 := by omega
      rw [h_eq, d_34_40, d_8_40, d_10_40, d_29_40]; rfl
    · have ih := D_thirty_four_eq_mux t (by omega)
      have hstep := D_step 32 t
      rw [D_thirty_two_eq_gate t (by omega), D_thirty_three_eq_gate t (by omega), ih] at hstep
      rw [hstep, D_eight_succ_eq_D_ten t (by omega), D_ten_succ_eq_not_D_eight t (by omega),
          D_twenty_nine_step_eq_xor_D_twenty_seven t (by omega),
          D_twenty_seven_eq_nand_D_eight_D_ten t (by omega)]
      cases D 8 t <;> cases D 10 t <;> cases D 29 t <;> decide

/-- **Four-Step Multiplexer Conservation Law for `D 34` (`D_thirty_four_pair_sum_eq_D_eight_D_ten`):**
for every `t ≥ 40`, `(if D 34 t then 1 else 0) + (if D 34 (t + 4) then 1 else 0) =
(if D 8 t then 1 else 0) + (if D 10 t then 1 else 0)`. -/
theorem D_thirty_four_pair_sum_eq_D_eight_D_ten (t : Nat) (ht : 40 ≤ t) :
    (if D 34 t then 1 else 0) + (if D 34 (t + 4) then 1 else 0) =
      (if D 8 t then 1 else 0) + (if D 10 t then 1 else 0) := by
  rw [D_thirty_four_eq_mux (t + 4) (by omega), D_thirty_four_eq_mux t ht,
      D_eight_periodic_four t (by omega), D_ten_periodic_four t (by omega),
      D_twenty_nine_antiperiodic_four t (by omega)]
  cases D 8 t <;> cases D 10 t <;> cases D 29 t <;> decide

/-- **Exact 8-Periodicity of the Multiplexer Diagonal `D 34` (`D_thirty_four_periodic_eight`):**
for every `t ≥ 40`, `D 34 (t + 8) = D 34 t`. -/
theorem D_thirty_four_periodic_eight (t : Nat) (ht : 40 ≤ t) :
    D 34 (t + 8) = D 34 t := by
  have p8 : D 8 (t + 8) = D 8 t := by
    rw [show t + 8 = (t + 4) + 4 by omega, D_eight_periodic_four (t + 4) (by omega),
        D_eight_periodic_four t (by omega)]
  have p10 : D 10 (t + 8) = D 10 t := by
    rw [show t + 8 = (t + 4) + 4 by omega, D_ten_periodic_four (t + 4) (by omega),
        D_ten_periodic_four t (by omega)]
  have p29 : D 29 (t + 8) = D 29 t := by
    rw [show t + 8 = (t + 4) + 4 by omega, D_twenty_nine_antiperiodic_four (t + 4) (by omega),
        D_twenty_nine_antiperiodic_four t (by omega), Bool.not_not]
  rw [D_thirty_four_eq_mux (t + 8) (by omega), D_thirty_four_eq_mux t ht, p8, p10, p29]



end Rule30LeftAntiPeriod
end Ruliology.CellularAutomata
