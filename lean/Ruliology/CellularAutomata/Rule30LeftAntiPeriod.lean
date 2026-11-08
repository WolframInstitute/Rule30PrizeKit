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
/-! ### 8. Eight-Step Block Balance of `D 34`, Arrival Entries `col_at_32 .. col_at_34`, and All-Period 27-Column Inward Non-Periodicity -/

/-- **Four-Step Anti-Periodic Sum on `(D 8, D 10)` (`D_eight_D_ten_pair_sum_add_two`):**
for every `t ≥ 9`, `(if D 8 t then 1 else 0) + (if D 10 t then 1 else 0) +
(if D 8 (t + 2) then 1 else 0) + (if D 10 (t + 2) then 1 else 0) = 2`. -/
theorem D_eight_D_ten_pair_sum_add_two (t : Nat) (ht : 9 ≤ t) :
    (if D 8 t then 1 else 0) + (if D 10 t then 1 else 0) +
      (if D 8 (t + 2) then 1 else 0) + (if D 10 (t + 2) then 1 else 0) = 2 := by
  rw [D_eight_antiperiodic_two t (by omega), D_ten_antiperiodic_two t ht]
  cases D 8 t <;> cases D 10 t <;> decide

/-- **Four-Point Even/Odd Stride Balance of the Multiplexer Diagonal `D 34` (`D_thirty_four_stride_two_sum`):**
for every `t ≥ 40`, `(if D 34 t then 1 else 0) + (if D 34 (t + 4) then 1 else 0) +
(if D 34 (t + 2) then 1 else 0) + (if D 34 (t + 6) then 1 else 0) = 2`. -/
theorem D_thirty_four_stride_two_sum (t : Nat) (ht : 40 ≤ t) :
    (if D 34 t then 1 else 0) + (if D 34 (t + 4) then 1 else 0) +
      (if D 34 (t + 2) then 1 else 0) + (if D 34 (t + 6) then 1 else 0) = 2 := by
  have h0 := D_thirty_four_pair_sum_eq_D_eight_D_ten t ht
  have h2 := D_thirty_four_pair_sum_eq_D_eight_D_ten (t + 2) (by omega)
  have hsum := D_eight_D_ten_pair_sum_add_two t (by omega)
  rw [show t + 2 + 4 = t + 6 by omega] at h2
  omega

/-- **Exact Eight-Step Block Balance of the Non-Anti-Periodic Multiplexer Diagonal `D 34` (`D_thirty_four_block_eight_sum`):**
every 8 consecutive ticks from `t ≥ 40` on contain diagnostic balance: exactly 4 black cells and 4 white cells. -/
theorem D_thirty_four_block_eight_sum (t : Nat) (ht : 40 ≤ t) :
    (if D 34 t then 1 else 0) + (if D 34 (t + 1) then 1 else 0) +
      (if D 34 (t + 2) then 1 else 0) + (if D 34 (t + 3) then 1 else 0) +
      (if D 34 (t + 4) then 1 else 0) + (if D 34 (t + 5) then 1 else 0) +
      (if D 34 (t + 6) then 1 else 0) + (if D 34 (t + 7) then 1 else 0) = 4 := by
  have heven := D_thirty_four_stride_two_sum t ht
  have hodd := D_thirty_four_stride_two_sum (t + 1) (by omega)
  rw [show t + 1 + 4 = t + 5 by omega, show t + 1 + 2 = t + 3 by omega, show t + 1 + 6 = t + 7 by omega] at hodd
  omega

/-! ### 9. Closed 3-Bit Oscillator `osc3Step`, `D 35` Gate, Block-8 Weights, `HalfDensity (D 34)`, Center-Diagonal Equivalence, and 28-Column Closure -/

private theorem d_35_18 : D 35 18 = false := by have h := D_step 33 17; rw [d_33_17, d_34_17, (D_eq_false_of_two_mul_lt 35 17 (by omega))] at h; exact h
private theorem d_35_19 : D 35 19 = true := by have h := D_step 33 18; rw [d_33_18, d_34_18, d_35_18] at h; exact h
private theorem d_35_20 : D 35 20 = false := by have h := D_step 33 19; rw [d_33_19, d_34_19, d_35_19] at h; exact h
private theorem d_35_21 : D 35 21 = false := by have h := D_step 33 20; rw [d_33_20, d_34_20, d_35_20] at h; exact h
private theorem d_35_22 : D 35 22 = true := by have h := D_step 33 21; rw [d_33_21, d_34_21, d_35_21] at h; exact h
private theorem d_35_23 : D 35 23 = false := by have h := D_step 33 22; rw [d_33_22, d_34_22, d_35_22] at h; exact h
private theorem d_35_24 : D 35 24 = true := by have h := D_step 33 23; rw [d_33_23, d_34_23, d_35_23] at h; exact h
private theorem d_35_25 : D 35 25 = false := by have h := D_step 33 24; rw [d_33_24, d_34_24, d_35_24] at h; exact h
private theorem d_35_26 : D 35 26 = true := by have h := D_step 33 25; rw [d_33_25, d_34_25, d_35_25] at h; exact h
private theorem d_35_27 : D 35 27 = true := by have h := D_step 33 26; rw [d_33_26, d_34_26, d_35_26] at h; exact h
private theorem d_35_28 : D 35 28 = false := by have h := D_step 33 27; rw [d_33_27, d_34_27, d_35_27] at h; exact h
private theorem d_35_29 : D 35 29 = false := by have h := D_step 33 28; rw [d_33_28, d_34_28, d_35_28] at h; exact h
private theorem d_35_30 : D 35 30 = true := by have h := D_step 33 29; rw [d_33_29, d_34_29, d_35_29] at h; exact h
private theorem d_35_31 : D 35 31 = true := by have h := D_step 33 30; rw [d_33_30, d_34_30, d_35_30] at h; exact h
private theorem d_35_32 : D 35 32 = false := by have h := D_step 33 31; rw [d_33_31, d_34_31, d_35_31] at h; exact h
private theorem d_35_33 : D 35 33 = false := by have h := D_step 33 32; rw [d_33_32, d_34_32, d_35_32] at h; exact h
private theorem d_35_34 : D 35 34 = false := by have h := D_step 33 33; rw [d_33_33, d_34_33, d_35_33] at h; exact h
private theorem d_35_35 : D 35 35 = true := by have h := D_step 33 34; rw [d_33_34, d_34_34, d_35_34] at h; exact h
private theorem d_35_36 : D 35 36 = true := by have h := D_step 33 35; rw [d_33_35, d_34_35, d_35_35] at h; exact h
private theorem d_35_37 : D 35 37 = true := by have h := D_step 33 36; rw [d_33_36, d_34_36, d_35_36] at h; exact h
private theorem d_35_38 : D 35 38 = true := by have h := D_step 33 37; rw [d_33_37, d_34_37, d_35_37] at h; exact h
private theorem d_35_39 : D 35 39 = true := by have h := D_step 33 38; rw [d_33_38, d_34_38, d_35_38] at h; exact h
private theorem d_35_40 : D 35 40 = false := by have h := D_step 33 39; rw [d_33_39, d_34_39, d_35_39] at h; exact h

/-- **Closed Autonomous Recurrence for `D 29` (`D_twenty_nine_step_closed`):**
for every `t ≥ 30`, `D 29 (t + 1) = xor (!(D 8 t && D 10 t)) (D 29 t)`. -/
theorem D_twenty_nine_step_closed (t : Nat) (ht : 31 ≤ t) :
    D 29 (t + 1) = xor (!(D 8 t && D 10 t)) (D 29 t) := by
  rw [D_twenty_nine_step_eq_xor_D_twenty_seven t (by omega),
      D_twenty_seven_eq_nand_D_eight_D_ten t (by omega)]

/-- **Three-Bit Gate Law for the Thirty-Fifth Left Diagonal (`D_thirty_five_eq_gate`):**
for every `t ≥ 40`, `D 35 t = ((!D 8 t && xor (D 10 t) (D 29 t)) || (D 8 t && !D 10 t && !D 29 t))`. -/
theorem D_thirty_five_eq_gate : ∀ t : Nat, 40 ≤ t →
    D 35 t = ((!D 8 t && xor (D 10 t) (D 29 t)) || (D 8 t && !D 10 t && !D 29 t))
  | 40, _ => by rw [d_35_40, d_8_40, d_10_40, d_29_40]; rfl
  | t + 1, ht => by
    by_cases h : t < 40
    · have h_eq : t + 1 = 40 := by omega
      rw [h_eq, d_35_40, d_8_40, d_10_40, d_29_40]; rfl
    · have ih := D_thirty_five_eq_gate t (by omega)
      have hstep := D_step 33 t
      rw [D_thirty_three_eq_gate t (by omega), D_thirty_four_eq_mux t (by omega), ih] at hstep
      rw [hstep, D_eight_succ_eq_D_ten t (by omega), D_ten_succ_eq_not_D_eight t (by omega),
          D_twenty_nine_step_closed t (by omega)]
      cases D 8 t <;> cases D 10 t <;> cases D 29 t <;> decide

/-- **Exact Eight-Step Block Weight of `D 32` (`D_thirty_two_block_eight_sum`):**
every 8 consecutive ticks of `D 32` from `t ≥ 36` on contain exactly 3 ones and 5 zeros. -/
theorem D_thirty_two_block_eight_sum (t : Nat) (ht : 36 ≤ t) :
    (if D 32 t then 1 else 0) + (if D 32 (t + 1) then 1 else 0) +
      (if D 32 (t + 2) then 1 else 0) + (if D 32 (t + 3) then 1 else 0) +
      (if D 32 (t + 4) then 1 else 0) + (if D 32 (t + 5) then 1 else 0) +
      (if D 32 (t + 6) then 1 else 0) + (if D 32 (t + 7) then 1 else 0) = 3 := by
  have g0 := D_thirty_two_eq_gate t ht
  have g1 := D_thirty_two_eq_gate (t + 1) (by omega)
  have g2 := D_thirty_two_eq_gate (t + 2) (by omega)
  have g3 := D_thirty_two_eq_gate (t + 3) (by omega)
  have g4 := D_thirty_two_eq_gate (t + 4) (by omega)
  have g5 := D_thirty_two_eq_gate (t + 5) (by omega)
  have g6 := D_thirty_two_eq_gate (t + 6) (by omega)
  have g7 := D_thirty_two_eq_gate (t + 7) (by omega)
  have s8_1 := D_eight_succ_eq_D_ten t (by omega)
  have s10_1 := D_ten_succ_eq_not_D_eight t (by omega)
  have s29_1 := D_twenty_nine_step_closed t (by omega)
  have s8_2 := D_eight_succ_eq_D_ten (t + 1) (by omega)
  have s10_2 := D_ten_succ_eq_not_D_eight (t + 1) (by omega)
  have s29_2 := D_twenty_nine_step_closed (t + 1) (by omega)
  have s8_3 := D_eight_succ_eq_D_ten (t + 2) (by omega)
  have s10_3 := D_ten_succ_eq_not_D_eight (t + 2) (by omega)
  have s29_3 := D_twenty_nine_step_closed (t + 2) (by omega)
  have p8_4 := D_eight_periodic_four t (by omega)
  have p10_4 := D_ten_periodic_four t (by omega)
  have p29_4 := D_twenty_nine_antiperiodic_four t (by omega)
  have p8_5 := D_eight_periodic_four (t + 1) (by omega)
  have p10_5 := D_ten_periodic_four (t + 1) (by omega)
  have p29_5 := D_twenty_nine_antiperiodic_four (t + 1) (by omega)
  have p8_6 := D_eight_periodic_four (t + 2) (by omega)
  have p10_6 := D_ten_periodic_four (t + 2) (by omega)
  have p29_6 := D_twenty_nine_antiperiodic_four (t + 2) (by omega)
  have p8_7 := D_eight_periodic_four (t + 3) (by omega)
  have p10_7 := D_ten_periodic_four (t + 3) (by omega)
  have p29_7 := D_twenty_nine_antiperiodic_four (t + 3) (by omega)
  rw [show t + 1 + 1 = t + 2 by omega] at s8_2 s10_2 s29_2
  rw [show t + 2 + 1 = t + 3 by omega] at s8_3 s10_3 s29_3
  rw [show t + 1 + 4 = t + 5 by omega] at p8_5 p10_5 p29_5
  rw [show t + 2 + 4 = t + 6 by omega] at p8_6 p10_6 p29_6
  rw [show t + 3 + 4 = t + 7 by omega] at p8_7 p10_7 p29_7
  rw [g0, g1, g2, g3, g4, g5, g6, g7,
      p8_4, p10_4, p29_4, p8_5, p10_5, p29_5, p8_6, p10_6, p29_6, p8_7, p10_7, p29_7,
      s8_3, s10_3, s29_3, s8_2, s10_2, s29_2, s8_1, s10_1, s29_1]
  cases D 8 t <;> cases D 10 t <;> cases D 29 t <;> decide

/-- **Exact Eight-Step Block Weight of `D 33` (`D_thirty_three_block_eight_sum`):**
every 8 consecutive ticks of `D 33` from `t ≥ 36` on contain exactly 3 ones and 5 zeros. -/
theorem D_thirty_three_block_eight_sum (t : Nat) (ht : 36 ≤ t) :
    (if D 33 t then 1 else 0) + (if D 33 (t + 1) then 1 else 0) +
      (if D 33 (t + 2) then 1 else 0) + (if D 33 (t + 3) then 1 else 0) +
      (if D 33 (t + 4) then 1 else 0) + (if D 33 (t + 5) then 1 else 0) +
      (if D 33 (t + 6) then 1 else 0) + (if D 33 (t + 7) then 1 else 0) = 3 := by
  have g0 := D_thirty_three_eq_gate t ht
  have g1 := D_thirty_three_eq_gate (t + 1) (by omega)
  have g2 := D_thirty_three_eq_gate (t + 2) (by omega)
  have g3 := D_thirty_three_eq_gate (t + 3) (by omega)
  have g4 := D_thirty_three_eq_gate (t + 4) (by omega)
  have g5 := D_thirty_three_eq_gate (t + 5) (by omega)
  have g6 := D_thirty_three_eq_gate (t + 6) (by omega)
  have g7 := D_thirty_three_eq_gate (t + 7) (by omega)
  have s8_1 := D_eight_succ_eq_D_ten t (by omega)
  have s10_1 := D_ten_succ_eq_not_D_eight t (by omega)
  have s29_1 := D_twenty_nine_step_closed t (by omega)
  have s8_2 := D_eight_succ_eq_D_ten (t + 1) (by omega)
  have s10_2 := D_ten_succ_eq_not_D_eight (t + 1) (by omega)
  have s29_2 := D_twenty_nine_step_closed (t + 1) (by omega)
  have s8_3 := D_eight_succ_eq_D_ten (t + 2) (by omega)
  have s10_3 := D_ten_succ_eq_not_D_eight (t + 2) (by omega)
  have s29_3 := D_twenty_nine_step_closed (t + 2) (by omega)
  have p8_4 := D_eight_periodic_four t (by omega)
  have p10_4 := D_ten_periodic_four t (by omega)
  have p29_4 := D_twenty_nine_antiperiodic_four t (by omega)
  have p8_5 := D_eight_periodic_four (t + 1) (by omega)
  have p10_5 := D_ten_periodic_four (t + 1) (by omega)
  have p29_5 := D_twenty_nine_antiperiodic_four (t + 1) (by omega)
  have p8_6 := D_eight_periodic_four (t + 2) (by omega)
  have p10_6 := D_ten_periodic_four (t + 2) (by omega)
  have p29_6 := D_twenty_nine_antiperiodic_four (t + 2) (by omega)
  have p8_7 := D_eight_periodic_four (t + 3) (by omega)
  have p10_7 := D_ten_periodic_four (t + 3) (by omega)
  have p29_7 := D_twenty_nine_antiperiodic_four (t + 3) (by omega)
  rw [show t + 1 + 1 = t + 2 by omega] at s8_2 s10_2 s29_2
  rw [show t + 2 + 1 = t + 3 by omega] at s8_3 s10_3 s29_3
  rw [show t + 1 + 4 = t + 5 by omega] at p8_5 p10_5 p29_5
  rw [show t + 2 + 4 = t + 6 by omega] at p8_6 p10_6 p29_6
  rw [show t + 3 + 4 = t + 7 by omega] at p8_7 p10_7 p29_7
  rw [g0, g1, g2, g3, g4, g5, g6, g7,
      p8_4, p10_4, p29_4, p8_5, p10_5, p29_5, p8_6, p10_6, p29_6, p8_7, p10_7, p29_7,
      s8_3, s10_3, s29_3, s8_2, s10_2, s29_2, s8_1, s10_1, s29_1]
  cases D 8 t <;> cases D 10 t <;> cases D 29 t <;> decide

/-- **Exact Eight-Step Block Weight of `D 35` (`D_thirty_five_block_eight_sum`):**
every 8 consecutive ticks of `D 35` from `t ≥ 40` on contain exactly 3 ones and 5 zeros. -/
theorem D_thirty_five_block_eight_sum (t : Nat) (ht : 40 ≤ t) :
    (if D 35 t then 1 else 0) + (if D 35 (t + 1) then 1 else 0) +
      (if D 35 (t + 2) then 1 else 0) + (if D 35 (t + 3) then 1 else 0) +
      (if D 35 (t + 4) then 1 else 0) + (if D 35 (t + 5) then 1 else 0) +
      (if D 35 (t + 6) then 1 else 0) + (if D 35 (t + 7) then 1 else 0) = 3 := by
  have g0 := D_thirty_five_eq_gate t ht
  have g1 := D_thirty_five_eq_gate (t + 1) (by omega)
  have g2 := D_thirty_five_eq_gate (t + 2) (by omega)
  have g3 := D_thirty_five_eq_gate (t + 3) (by omega)
  have g4 := D_thirty_five_eq_gate (t + 4) (by omega)
  have g5 := D_thirty_five_eq_gate (t + 5) (by omega)
  have g6 := D_thirty_five_eq_gate (t + 6) (by omega)
  have g7 := D_thirty_five_eq_gate (t + 7) (by omega)
  have s8_1 := D_eight_succ_eq_D_ten t (by omega)
  have s10_1 := D_ten_succ_eq_not_D_eight t (by omega)
  have s29_1 := D_twenty_nine_step_closed t (by omega)
  have s8_2 := D_eight_succ_eq_D_ten (t + 1) (by omega)
  have s10_2 := D_ten_succ_eq_not_D_eight (t + 1) (by omega)
  have s29_2 := D_twenty_nine_step_closed (t + 1) (by omega)
  have s8_3 := D_eight_succ_eq_D_ten (t + 2) (by omega)
  have s10_3 := D_ten_succ_eq_not_D_eight (t + 2) (by omega)
  have s29_3 := D_twenty_nine_step_closed (t + 2) (by omega)
  have p8_4 := D_eight_periodic_four t (by omega)
  have p10_4 := D_ten_periodic_four t (by omega)
  have p29_4 := D_twenty_nine_antiperiodic_four t (by omega)
  have p8_5 := D_eight_periodic_four (t + 1) (by omega)
  have p10_5 := D_ten_periodic_four (t + 1) (by omega)
  have p29_5 := D_twenty_nine_antiperiodic_four (t + 1) (by omega)
  have p8_6 := D_eight_periodic_four (t + 2) (by omega)
  have p10_6 := D_ten_periodic_four (t + 2) (by omega)
  have p29_6 := D_twenty_nine_antiperiodic_four (t + 2) (by omega)
  have p8_7 := D_eight_periodic_four (t + 3) (by omega)
  have p10_7 := D_ten_periodic_four (t + 3) (by omega)
  have p29_7 := D_twenty_nine_antiperiodic_four (t + 3) (by omega)
  rw [show t + 1 + 1 = t + 2 by omega] at s8_2 s10_2 s29_2
  rw [show t + 2 + 1 = t + 3 by omega] at s8_3 s10_3 s29_3
  rw [show t + 1 + 4 = t + 5 by omega] at p8_5 p10_5 p29_5
  rw [show t + 2 + 4 = t + 6 by omega] at p8_6 p10_6 p29_6
  rw [show t + 3 + 4 = t + 7 by omega] at p8_7 p10_7 p29_7
  rw [g0, g1, g2, g3, g4, g5, g6, g7,
      p8_4, p10_4, p29_4, p8_5, p10_5, p29_5, p8_6, p10_6, p29_6, p8_7, p10_7, p29_7,
      s8_3, s10_3, s29_3, s8_2, s10_2, s29_2, s8_1, s10_1, s29_1]
  cases D 8 t <;> cases D 10 t <;> cases D 29 t <;> decide

/-- **Black-Count Step by Eight (`blackCountFor_add_eight`):**
for any `f : Nat → Bool` and `n : Nat`, `blackCountFor f (n + 8)` expands as `blackCountFor f n` plus the 8 indicator bits on `n .. n + 7`. -/
theorem blackCountFor_add_eight (f : Nat → Bool) (n : Nat) :
    blackCountFor f (n + 8) = blackCountFor f n +
      ((if f n then 1 else 0) + (if f (n + 1) then 1 else 0) +
       (if f (n + 2) then 1 else 0) + (if f (n + 3) then 1 else 0) +
       (if f (n + 4) then 1 else 0) + (if f (n + 5) then 1 else 0) +
       (if f (n + 6) then 1 else 0) + (if f (n + 7) then 1 else 0)) := by
  have s1 := blackCountFor_succ f n
  have s2 := blackCountFor_succ f (n + 1); rw [show n + 1 + 1 = n + 2 by omega] at s2
  have s3 := blackCountFor_succ f (n + 2); rw [show n + 2 + 1 = n + 3 by omega] at s3
  have s4 := blackCountFor_succ f (n + 3); rw [show n + 3 + 1 = n + 4 by omega] at s4
  have s5 := blackCountFor_succ f (n + 4); rw [show n + 4 + 1 = n + 5 by omega] at s5
  have s6 := blackCountFor_succ f (n + 5); rw [show n + 5 + 1 = n + 6 by omega] at s6
  have s7 := blackCountFor_succ f (n + 6); rw [show n + 6 + 1 = n + 7 by omega] at s7
  have s8 := blackCountFor_succ f (n + 7); rw [show n + 7 + 1 = n + 8 by omega] at s8
  omega

/-- **General Eight-Step Block Balance Implies `HalfDensity` (`halfDensity_of_block_eight_sum`):**
if every 8-step window of `f : Nat → Bool` from `t₀` on has weight 4, then `HalfDensity f` holds. -/
theorem halfDensity_of_block_eight_sum (f : Nat → Bool) (t₀ : Nat)
    (hblock : ∀ t : Nat, t₀ ≤ t →
      (if f t then 1 else 0) + (if f (t + 1) then 1 else 0) +
      (if f (t + 2) then 1 else 0) + (if f (t + 3) then 1 else 0) +
      (if f (t + 4) then 1 else 0) + (if f (t + 5) then 1 else 0) +
      (if f (t + 6) then 1 else 0) + (if f (t + 7) then 1 else 0) = 4) :
    HalfDensity f := by
  have hB : ∀ n : Nat, (2 * (blackCountFor f n : Int) - (n : Int)).natAbs ≤ t₀ + 8 := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      by_cases hlt : n < t₀ + 8
      · have hle := (blackCountFor_add_bounds f 0 n).2
        have h0 : blackCountFor f 0 = 0 := rfl
        rw [Nat.zero_add, h0, Nat.zero_add] at hle
        omega
      · have hge : t₀ ≤ n - 8 := by omega
        have ih_prev := ih (n - 8) (by omega)
        have h8 := blackCountFor_add_eight f (n - 8)
        have hb := hblock (n - 8) hge
        rw [hb, show n - 8 + 8 = n by omega] at h8
        omega
  intro k _hk
  refine ⟨k * (t₀ + 8), ?_⟩
  intro n hn
  exact Nat.le_trans (Nat.mul_le_mul_left k (hB n)) hn

/-- **Problem 3 for the Non-Anti-Periodic Multiplexer Diagonal `D 34` (`halfDensity_D_thirty_four`):**
`D 34` has exact asymptotic density `1/2` (`HalfDensity (D 34)`). -/
theorem halfDensity_D_thirty_four : HalfDensity (D 34) :=
  halfDensity_of_block_eight_sum (D 34) 40 D_thirty_four_block_eight_sum

/-! ### 11. Three-Bit Gate Laws and Block-8 Weights for `D 36` and `D 37` -/

private theorem d_36_18 : D 36 18 = true := by have h := D_step 34 17; rw [d_34_17, (D_eq_false_of_two_mul_lt 35 17 (by omega)), (D_eq_false_of_two_mul_lt 36 17 (by omega))] at h; exact h
private theorem d_36_19 : D 36 19 = true := by have h := D_step 34 18; rw [d_34_18, d_35_18, d_36_18] at h; exact h
private theorem d_37_19 : D 37 19 = true := by have h := D_step 35 18; rw [d_35_18, d_36_18, (D_eq_false_of_two_mul_lt 37 18 (by omega))] at h; exact h
private theorem d_36_20 : D 36 20 = true := by have h := D_step 34 19; rw [d_34_19, d_35_19, d_36_19] at h; exact h
private theorem d_37_20 : D 37 20 = false := by have h := D_step 35 19; rw [d_35_19, d_36_19, d_37_19] at h; exact h
private theorem d_36_21 : D 36 21 = true := by have h := D_step 34 20; rw [d_34_20, d_35_20, d_36_20] at h; exact h
private theorem d_37_21 : D 37 21 = true := by have h := D_step 35 20; rw [d_35_20, d_36_20, d_37_20] at h; exact h
private theorem d_36_22 : D 36 22 = false := by have h := D_step 34 21; rw [d_34_21, d_35_21, d_36_21] at h; exact h
private theorem d_37_22 : D 37 22 = true := by have h := D_step 35 21; rw [d_35_21, d_36_21, d_37_21] at h; exact h
private theorem d_36_23 : D 36 23 = true := by have h := D_step 34 22; rw [d_34_22, d_35_22, d_36_22] at h; exact h
private theorem d_37_23 : D 37 23 = false := by have h := D_step 35 22; rw [d_35_22, d_36_22, d_37_22] at h; exact h
private theorem d_36_24 : D 36 24 = true := by have h := D_step 34 23; rw [d_34_23, d_35_23, d_36_23] at h; exact h
private theorem d_37_24 : D 37 24 = true := by have h := D_step 35 23; rw [d_35_23, d_36_23, d_37_23] at h; exact h
private theorem d_36_25 : D 36 25 = false := by have h := D_step 34 24; rw [d_34_24, d_35_24, d_36_24] at h; exact h
private theorem d_37_25 : D 37 25 = false := by have h := D_step 35 24; rw [d_35_24, d_36_24, d_37_24] at h; exact h
private theorem d_36_26 : D 36 26 = true := by have h := D_step 34 25; rw [d_34_25, d_35_25, d_36_25] at h; exact h
private theorem d_37_26 : D 37 26 = false := by have h := D_step 35 25; rw [d_35_25, d_36_25, d_37_25] at h; exact h
private theorem d_36_27 : D 36 27 = true := by have h := D_step 34 26; rw [d_34_26, d_35_26, d_36_26] at h; exact h
private theorem d_37_27 : D 37 27 = false := by have h := D_step 35 26; rw [d_35_26, d_36_26, d_37_26] at h; exact h
private theorem d_36_28 : D 36 28 = false := by have h := D_step 34 27; rw [d_34_27, d_35_27, d_36_27] at h; exact h
private theorem d_37_28 : D 37 28 = false := by have h := D_step 35 27; rw [d_35_27, d_36_27, d_37_27] at h; exact h
private theorem d_36_29 : D 36 29 = true := by have h := D_step 34 28; rw [d_34_28, d_35_28, d_36_28] at h; exact h
private theorem d_37_29 : D 37 29 = false := by have h := D_step 35 28; rw [d_35_28, d_36_28, d_37_28] at h; exact h
private theorem d_36_30 : D 36 30 = true := by have h := D_step 34 29; rw [d_34_29, d_35_29, d_36_29] at h; exact h
private theorem d_37_30 : D 37 30 = true := by have h := D_step 35 29; rw [d_35_29, d_36_29, d_37_29] at h; exact h
private theorem d_36_31 : D 36 31 = true := by have h := D_step 34 30; rw [d_34_30, d_35_30, d_36_30] at h; exact h
private theorem d_37_31 : D 37 31 = false := by have h := D_step 35 30; rw [d_35_30, d_36_30, d_37_30] at h; exact h
private theorem d_36_32 : D 36 32 = false := by have h := D_step 34 31; rw [d_34_31, d_35_31, d_36_31] at h; exact h
private theorem d_37_32 : D 37 32 = false := by have h := D_step 35 31; rw [d_35_31, d_36_31, d_37_31] at h; exact h
private theorem d_36_33 : D 36 33 = true := by have h := D_step 34 32; rw [d_34_32, d_35_32, d_36_32] at h; exact h
private theorem d_37_33 : D 37 33 = false := by have h := D_step 35 32; rw [d_35_32, d_36_32, d_37_32] at h; exact h
private theorem d_36_34 : D 36 34 = false := by have h := D_step 34 33; rw [d_34_33, d_35_33, d_36_33] at h; exact h
private theorem d_37_34 : D 37 34 = true := by have h := D_step 35 33; rw [d_35_33, d_36_33, d_37_33] at h; exact h
private theorem d_36_35 : D 36 35 = true := by have h := D_step 34 34; rw [d_34_34, d_35_34, d_36_34] at h; exact h
private theorem d_37_35 : D 37 35 = true := by have h := D_step 35 34; rw [d_35_34, d_36_34, d_37_34] at h; exact h
private theorem d_36_36 : D 36 36 = false := by have h := D_step 34 35; rw [d_34_35, d_35_35, d_36_35] at h; exact h
private theorem d_37_36 : D 37 36 = false := by have h := D_step 35 35; rw [d_35_35, d_36_35, d_37_35] at h; exact h
private theorem d_36_37 : D 36 37 = true := by have h := D_step 34 36; rw [d_34_36, d_35_36, d_36_36] at h; exact h
private theorem d_37_37 : D 37 37 = true := by have h := D_step 35 36; rw [d_35_36, d_36_36, d_37_36] at h; exact h
private theorem d_36_38 : D 36 38 = true := by have h := D_step 34 37; rw [d_34_37, d_35_37, d_36_37] at h; exact h
private theorem d_37_38 : D 37 38 = false := by have h := D_step 35 37; rw [d_35_37, d_36_37, d_37_37] at h; exact h
private theorem d_36_39 : D 36 39 = false := by have h := D_step 34 38; rw [d_34_38, d_35_38, d_36_38] at h; exact h
private theorem d_37_39 : D 37 39 = false := by have h := D_step 35 38; rw [d_35_38, d_36_38, d_37_38] at h; exact h
private theorem d_36_40 : D 36 40 = false := by have h := D_step 34 39; rw [d_34_39, d_35_39, d_36_39] at h; exact h
private theorem d_37_40 : D 37 40 = true := by have h := D_step 35 39; rw [d_35_39, d_36_39, d_37_39] at h; exact h
private theorem d_0_41 : D 0 41 = true := D_zero 41
private theorem d_1_41 : D 1 41 = true := by simpa using D_one 40
private theorem d_2_41 : D 2 41 = false := by have h := D_step 0 40; rw [d_0_40, d_1_40, d_2_40] at h; exact h
private theorem d_3_41 : D 3 41 = true := by have h := D_step 1 40; rw [d_1_40, d_2_40, d_3_40] at h; exact h
private theorem d_4_41 : D 4 41 = true := by have h := D_step 2 40; rw [d_2_40, d_3_40, d_4_40] at h; exact h
private theorem d_5_41 : D 5 41 = true := by have h := D_step 3 40; rw [d_3_40, d_4_40, d_5_40] at h; exact h
private theorem d_6_41 : D 6 41 = true := by have h := D_step 4 40; rw [d_4_40, d_5_40, d_6_40] at h; exact h
private theorem d_7_41 : D 7 41 = false := by have h := D_step 5 40; rw [d_5_40, d_6_40, d_7_40] at h; exact h
private theorem d_8_41 : D 8 41 = true := by have h := D_step 6 40; rw [d_6_40, d_7_40, d_8_40] at h; exact h
private theorem d_9_41 : D 9 41 = true := by have h := D_step 7 40; rw [d_7_40, d_8_40, d_9_40] at h; exact h
private theorem d_10_41 : D 10 41 = false := by have h := D_step 8 40; rw [d_8_40, d_9_40, d_10_40] at h; exact h
private theorem d_11_41 : D 11 41 = false := by have h := D_step 9 40; rw [d_9_40, d_10_40, d_11_40] at h; exact h
private theorem d_12_41 : D 12 41 = true := by have h := D_step 10 40; rw [d_10_40, d_11_40, d_12_40] at h; exact h
private theorem d_13_41 : D 13 41 = true := by have h := D_step 11 40; rw [d_11_40, d_12_40, d_13_40] at h; exact h
private theorem d_14_41 : D 14 41 = true := by have h := D_step 12 40; rw [d_12_40, d_13_40, d_14_40] at h; exact h
private theorem d_15_41 : D 15 41 = false := by have h := D_step 13 40; rw [d_13_40, d_14_40, d_15_40] at h; exact h
private theorem d_16_41 : D 16 41 = false := by have h := D_step 14 40; rw [d_14_40, d_15_40, d_16_40] at h; exact h
private theorem d_17_41 : D 17 41 = false := by have h := D_step 15 40; rw [d_15_40, d_16_40, d_17_40] at h; exact h
private theorem d_18_41 : D 18 41 = true := by have h := D_step 16 40; rw [d_16_40, d_17_40, d_18_40] at h; exact h
private theorem d_19_41 : D 19 41 = false := by have h := D_step 17 40; rw [d_17_40, d_18_40, d_19_40] at h; exact h
private theorem d_20_41 : D 20 41 = true := by have h := D_step 18 40; rw [d_18_40, d_19_40, d_20_40] at h; exact h
private theorem d_21_41 : D 21 41 = true := by have h := D_step 19 40; rw [d_19_40, d_20_40, d_21_40] at h; exact h
private theorem d_22_41 : D 22 41 = false := by have h := D_step 20 40; rw [d_20_40, d_21_40, d_22_40] at h; exact h
private theorem d_23_41 : D 23 41 = false := by have h := D_step 21 40; rw [d_21_40, d_22_40, d_23_40] at h; exact h
private theorem d_24_41 : D 24 41 = false := by have h := D_step 22 40; rw [d_22_40, d_23_40, d_24_40] at h; exact h
private theorem d_25_41 : D 25 41 = false := by have h := D_step 23 40; rw [d_23_40, d_24_40, d_25_40] at h; exact h
private theorem d_26_41 : D 26 41 = true := by have h := D_step 24 40; rw [d_24_40, d_25_40, d_26_40] at h; exact h
private theorem d_27_41 : D 27 41 = true := by have h := D_step 25 40; rw [d_25_40, d_26_40, d_27_40] at h; exact h
private theorem d_28_41 : D 28 41 = false := by have h := D_step 26 40; rw [d_26_40, d_27_40, d_28_40] at h; exact h
private theorem d_29_41 : D 29 41 = true := by have h := D_step 27 40; rw [d_27_40, d_28_40, d_29_40] at h; exact h
private theorem d_30_41 : D 30 41 = true := by have h := D_step 28 40; rw [d_28_40, d_29_40, d_30_40] at h; exact h
private theorem d_31_41 : D 31 41 = false := by have h := D_step 29 40; rw [d_29_40, d_30_40, d_31_40] at h; exact h
private theorem d_32_41 : D 32 41 = false := by have h := D_step 30 40; rw [d_30_40, d_31_40, d_32_40] at h; exact h
private theorem d_33_41 : D 33 41 = false := by have h := D_step 31 40; rw [d_31_40, d_32_40, d_33_40] at h; exact h
private theorem d_34_41 : D 34 41 = false := by have h := D_step 32 40; rw [d_32_40, d_33_40, d_34_40] at h; exact h
private theorem d_35_41 : D 35 41 = false := by have h := D_step 33 40; rw [d_33_40, d_34_40, d_35_40] at h; exact h
private theorem d_36_41 : D 36 41 = true := by have h := D_step 34 40; rw [d_34_40, d_35_40, d_36_40] at h; exact h
private theorem d_37_41 : D 37 41 = true := by have h := D_step 35 40; rw [d_35_40, d_36_40, d_37_40] at h; exact h
private theorem d_0_42 : D 0 42 = true := D_zero 42
private theorem d_1_42 : D 1 42 = true := by simpa using D_one 41
private theorem d_2_42 : D 2 42 = false := by have h := D_step 0 41; rw [d_0_41, d_1_41, d_2_41] at h; exact h
private theorem d_3_42 : D 3 42 = false := by have h := D_step 1 41; rw [d_1_41, d_2_41, d_3_41] at h; exact h
private theorem d_4_42 : D 4 42 = true := by have h := D_step 2 41; rw [d_2_41, d_3_41, d_4_41] at h; exact h
private theorem d_5_42 : D 5 42 = false := by have h := D_step 3 41; rw [d_3_41, d_4_41, d_5_41] at h; exact h
private theorem d_6_42 : D 6 42 = false := by have h := D_step 4 41; rw [d_4_41, d_5_41, d_6_41] at h; exact h
private theorem d_7_42 : D 7 42 = false := by have h := D_step 5 41; rw [d_5_41, d_6_41, d_7_41] at h; exact h
private theorem d_8_42 : D 8 42 = false := by have h := D_step 6 41; rw [d_6_41, d_7_41, d_8_41] at h; exact h
private theorem d_9_42 : D 9 42 = true := by have h := D_step 7 41; rw [d_7_41, d_8_41, d_9_41] at h; exact h
private theorem d_10_42 : D 10 42 = false := by have h := D_step 8 41; rw [d_8_41, d_9_41, d_10_41] at h; exact h
private theorem d_11_42 : D 11 42 = true := by have h := D_step 9 41; rw [d_9_41, d_10_41, d_11_41] at h; exact h
private theorem d_12_42 : D 12 42 = true := by have h := D_step 10 41; rw [d_10_41, d_11_41, d_12_41] at h; exact h
private theorem d_13_42 : D 13 42 = true := by have h := D_step 11 41; rw [d_11_41, d_12_41, d_13_41] at h; exact h
private theorem d_14_42 : D 14 42 = false := by have h := D_step 12 41; rw [d_12_41, d_13_41, d_14_41] at h; exact h
private theorem d_15_42 : D 15 42 = false := by have h := D_step 13 41; rw [d_13_41, d_14_41, d_15_41] at h; exact h
private theorem d_16_42 : D 16 42 = true := by have h := D_step 14 41; rw [d_14_41, d_15_41, d_16_41] at h; exact h
private theorem d_17_42 : D 17 42 = false := by have h := D_step 15 41; rw [d_15_41, d_16_41, d_17_41] at h; exact h
private theorem d_18_42 : D 18 42 = true := by have h := D_step 16 41; rw [d_16_41, d_17_41, d_18_41] at h; exact h
private theorem d_19_42 : D 19 42 = true := by have h := D_step 17 41; rw [d_17_41, d_18_41, d_19_41] at h; exact h
private theorem d_20_42 : D 20 42 = false := by have h := D_step 18 41; rw [d_18_41, d_19_41, d_20_41] at h; exact h
private theorem d_21_42 : D 21 42 = true := by have h := D_step 19 41; rw [d_19_41, d_20_41, d_21_41] at h; exact h
private theorem d_22_42 : D 22 42 = false := by have h := D_step 20 41; rw [d_20_41, d_21_41, d_22_41] at h; exact h
private theorem d_23_42 : D 23 42 = true := by have h := D_step 21 41; rw [d_21_41, d_22_41, d_23_41] at h; exact h
private theorem d_24_42 : D 24 42 = false := by have h := D_step 22 41; rw [d_22_41, d_23_41, d_24_41] at h; exact h
private theorem d_25_42 : D 25 42 = false := by have h := D_step 23 41; rw [d_23_41, d_24_41, d_25_41] at h; exact h
private theorem d_26_42 : D 26 42 = true := by have h := D_step 24 41; rw [d_24_41, d_25_41, d_26_41] at h; exact h
private theorem d_27_42 : D 27 42 = true := by have h := D_step 25 41; rw [d_25_41, d_26_41, d_27_41] at h; exact h
private theorem d_28_42 : D 28 42 = false := by have h := D_step 26 41; rw [d_26_41, d_27_41, d_28_41] at h; exact h
private theorem d_29_42 : D 29 42 = false := by have h := D_step 27 41; rw [d_27_41, d_28_41, d_29_41] at h; exact h
private theorem d_30_42 : D 30 42 = true := by have h := D_step 28 41; rw [d_28_41, d_29_41, d_30_41] at h; exact h
private theorem d_31_42 : D 31 42 = false := by have h := D_step 29 41; rw [d_29_41, d_30_41, d_31_41] at h; exact h
private theorem d_32_42 : D 32 42 = true := by have h := D_step 30 41; rw [d_30_41, d_31_41, d_32_41] at h; exact h
private theorem d_33_42 : D 33 42 = false := by have h := D_step 31 41; rw [d_31_41, d_32_41, d_33_41] at h; exact h
private theorem d_34_42 : D 34 42 = false := by have h := D_step 32 41; rw [d_32_41, d_33_41, d_34_41] at h; exact h
private theorem d_35_42 : D 35 42 = false := by have h := D_step 33 41; rw [d_33_41, d_34_41, d_35_41] at h; exact h
private theorem d_36_42 : D 36 42 = true := by have h := D_step 34 41; rw [d_34_41, d_35_41, d_36_41] at h; exact h
private theorem d_37_42 : D 37 42 = true := by have h := D_step 35 41; rw [d_35_41, d_36_41, d_37_41] at h; exact h
private theorem d_0_43 : D 0 43 = true := D_zero 43
private theorem d_1_43 : D 1 43 = true := by simpa using D_one 42
private theorem d_2_43 : D 2 43 = false := by have h := D_step 0 42; rw [d_0_42, d_1_42, d_2_42] at h; exact h
private theorem d_3_43 : D 3 43 = true := by have h := D_step 1 42; rw [d_1_42, d_2_42, d_3_42] at h; exact h
private theorem d_4_43 : D 4 43 = true := by have h := D_step 2 42; rw [d_2_42, d_3_42, d_4_42] at h; exact h
private theorem d_5_43 : D 5 43 = true := by have h := D_step 3 42; rw [d_3_42, d_4_42, d_5_42] at h; exact h
private theorem d_6_43 : D 6 43 = true := by have h := D_step 4 42; rw [d_4_42, d_5_42, d_6_42] at h; exact h
private theorem d_7_43 : D 7 43 = false := by have h := D_step 5 42; rw [d_5_42, d_6_42, d_7_42] at h; exact h
private theorem d_8_43 : D 8 43 = false := by have h := D_step 6 42; rw [d_6_42, d_7_42, d_8_42] at h; exact h
private theorem d_9_43 : D 9 43 = true := by have h := D_step 7 42; rw [d_7_42, d_8_42, d_9_42] at h; exact h
private theorem d_10_43 : D 10 43 = true := by have h := D_step 8 42; rw [d_8_42, d_9_42, d_10_42] at h; exact h
private theorem d_11_43 : D 11 43 = false := by have h := D_step 9 42; rw [d_9_42, d_10_42, d_11_42] at h; exact h
private theorem d_12_43 : D 12 43 = true := by have h := D_step 10 42; rw [d_10_42, d_11_42, d_12_42] at h; exact h
private theorem d_13_43 : D 13 43 = false := by have h := D_step 11 42; rw [d_11_42, d_12_42, d_13_42] at h; exact h
private theorem d_14_43 : D 14 43 = false := by have h := D_step 12 42; rw [d_12_42, d_13_42, d_14_42] at h; exact h
private theorem d_15_43 : D 15 43 = true := by have h := D_step 13 42; rw [d_13_42, d_14_42, d_15_42] at h; exact h
private theorem d_16_43 : D 16 43 = true := by have h := D_step 14 42; rw [d_14_42, d_15_42, d_16_42] at h; exact h
private theorem d_17_43 : D 17 43 = true := by have h := D_step 15 42; rw [d_15_42, d_16_42, d_17_42] at h; exact h
private theorem d_18_43 : D 18 43 = false := by have h := D_step 16 42; rw [d_16_42, d_17_42, d_18_42] at h; exact h
private theorem d_19_43 : D 19 43 = true := by have h := D_step 17 42; rw [d_17_42, d_18_42, d_19_42] at h; exact h
private theorem d_20_43 : D 20 43 = false := by have h := D_step 18 42; rw [d_18_42, d_19_42, d_20_42] at h; exact h
private theorem d_21_43 : D 21 43 = false := by have h := D_step 19 42; rw [d_19_42, d_20_42, d_21_42] at h; exact h
private theorem d_22_43 : D 22 43 = true := by have h := D_step 20 42; rw [d_20_42, d_21_42, d_22_42] at h; exact h
private theorem d_23_43 : D 23 43 = false := by have h := D_step 21 42; rw [d_21_42, d_22_42, d_23_42] at h; exact h
private theorem d_24_43 : D 24 43 = true := by have h := D_step 22 42; rw [d_22_42, d_23_42, d_24_42] at h; exact h
private theorem d_25_43 : D 25 43 = true := by have h := D_step 23 42; rw [d_23_42, d_24_42, d_25_42] at h; exact h
private theorem d_26_43 : D 26 43 = true := by have h := D_step 24 42; rw [d_24_42, d_25_42, d_26_42] at h; exact h
private theorem d_27_43 : D 27 43 = true := by have h := D_step 25 42; rw [d_25_42, d_26_42, d_27_42] at h; exact h
private theorem d_28_43 : D 28 43 = false := by have h := D_step 26 42; rw [d_26_42, d_27_42, d_28_42] at h; exact h
private theorem d_29_43 : D 29 43 = true := by have h := D_step 27 42; rw [d_27_42, d_28_42, d_29_42] at h; exact h
private theorem d_30_43 : D 30 43 = true := by have h := D_step 28 42; rw [d_28_42, d_29_42, d_30_42] at h; exact h
private theorem d_31_43 : D 31 43 = true := by have h := D_step 29 42; rw [d_29_42, d_30_42, d_31_42] at h; exact h
private theorem d_32_43 : D 32 43 = false := by have h := D_step 30 42; rw [d_30_42, d_31_42, d_32_42] at h; exact h
private theorem d_33_43 : D 33 43 = true := by have h := D_step 31 42; rw [d_31_42, d_32_42, d_33_42] at h; exact h
private theorem d_34_43 : D 34 43 = true := by have h := D_step 32 42; rw [d_32_42, d_33_42, d_34_42] at h; exact h
private theorem d_35_43 : D 35 43 = false := by have h := D_step 33 42; rw [d_33_42, d_34_42, d_35_42] at h; exact h
private theorem d_36_43 : D 36 43 = true := by have h := D_step 34 42; rw [d_34_42, d_35_42, d_36_42] at h; exact h
private theorem d_37_43 : D 37 43 = true := by have h := D_step 35 42; rw [d_35_42, d_36_42, d_37_42] at h; exact h
private theorem d_0_44 : D 0 44 = true := D_zero 44
private theorem d_1_44 : D 1 44 = true := by simpa using D_one 43
private theorem d_2_44 : D 2 44 = false := by have h := D_step 0 43; rw [d_0_43, d_1_43, d_2_43] at h; exact h
private theorem d_3_44 : D 3 44 = false := by have h := D_step 1 43; rw [d_1_43, d_2_43, d_3_43] at h; exact h
private theorem d_4_44 : D 4 44 = true := by have h := D_step 2 43; rw [d_2_43, d_3_43, d_4_43] at h; exact h
private theorem d_5_44 : D 5 44 = false := by have h := D_step 3 43; rw [d_3_43, d_4_43, d_5_43] at h; exact h
private theorem d_6_44 : D 6 44 = false := by have h := D_step 4 43; rw [d_4_43, d_5_43, d_6_43] at h; exact h
private theorem d_7_44 : D 7 44 = false := by have h := D_step 5 43; rw [d_5_43, d_6_43, d_7_43] at h; exact h
private theorem d_8_44 : D 8 44 = true := by have h := D_step 6 43; rw [d_6_43, d_7_43, d_8_43] at h; exact h
private theorem d_9_44 : D 9 44 = true := by have h := D_step 7 43; rw [d_7_43, d_8_43, d_9_43] at h; exact h
private theorem d_10_44 : D 10 44 = true := by have h := D_step 8 43; rw [d_8_43, d_9_43, d_10_43] at h; exact h
private theorem d_11_44 : D 11 44 = false := by have h := D_step 9 43; rw [d_9_43, d_10_43, d_11_43] at h; exact h
private theorem d_12_44 : D 12 44 = false := by have h := D_step 10 43; rw [d_10_43, d_11_43, d_12_43] at h; exact h
private theorem d_13_44 : D 13 44 = true := by have h := D_step 11 43; rw [d_11_43, d_12_43, d_13_43] at h; exact h
private theorem d_14_44 : D 14 44 = true := by have h := D_step 12 43; rw [d_12_43, d_13_43, d_14_43] at h; exact h
private theorem d_15_44 : D 15 44 = true := by have h := D_step 13 43; rw [d_13_43, d_14_43, d_15_43] at h; exact h
private theorem d_16_44 : D 16 44 = true := by have h := D_step 14 43; rw [d_14_43, d_15_43, d_16_43] at h; exact h
private theorem d_17_44 : D 17 44 = false := by have h := D_step 15 43; rw [d_15_43, d_16_43, d_17_43] at h; exact h
private theorem d_18_44 : D 18 44 = false := by have h := D_step 16 43; rw [d_16_43, d_17_43, d_18_43] at h; exact h
private theorem d_19_44 : D 19 44 = false := by have h := D_step 17 43; rw [d_17_43, d_18_43, d_19_43] at h; exact h
private theorem d_20_44 : D 20 44 = true := by have h := D_step 18 43; rw [d_18_43, d_19_43, d_20_43] at h; exact h
private theorem d_21_44 : D 21 44 = true := by have h := D_step 19 43; rw [d_19_43, d_20_43, d_21_43] at h; exact h
private theorem d_22_44 : D 22 44 = true := by have h := D_step 20 43; rw [d_20_43, d_21_43, d_22_43] at h; exact h
private theorem d_23_44 : D 23 44 = true := by have h := D_step 21 43; rw [d_21_43, d_22_43, d_23_43] at h; exact h
private theorem d_24_44 : D 24 44 = false := by have h := D_step 22 43; rw [d_22_43, d_23_43, d_24_43] at h; exact h
private theorem d_25_44 : D 25 44 = true := by have h := D_step 23 43; rw [d_23_43, d_24_43, d_25_43] at h; exact h
private theorem d_26_44 : D 26 44 = false := by have h := D_step 24 43; rw [d_24_43, d_25_43, d_26_43] at h; exact h
private theorem d_27_44 : D 27 44 = false := by have h := D_step 25 43; rw [d_25_43, d_26_43, d_27_43] at h; exact h
private theorem d_28_44 : D 28 44 = false := by have h := D_step 26 43; rw [d_26_43, d_27_43, d_28_43] at h; exact h
private theorem d_29_44 : D 29 44 = false := by have h := D_step 27 43; rw [d_27_43, d_28_43, d_29_43] at h; exact h
private theorem d_30_44 : D 30 44 = true := by have h := D_step 28 43; rw [d_28_43, d_29_43, d_30_43] at h; exact h
private theorem d_31_44 : D 31 44 = false := by have h := D_step 29 43; rw [d_29_43, d_30_43, d_31_43] at h; exact h
private theorem d_32_44 : D 32 44 = false := by have h := D_step 30 43; rw [d_30_43, d_31_43, d_32_43] at h; exact h
private theorem d_33_44 : D 33 44 = false := by have h := D_step 31 43; rw [d_31_43, d_32_43, d_33_43] at h; exact h
private theorem d_34_44 : D 34 44 = true := by have h := D_step 32 43; rw [d_32_43, d_33_43, d_34_43] at h; exact h
private theorem d_35_44 : D 35 44 = false := by have h := D_step 33 43; rw [d_33_43, d_34_43, d_35_43] at h; exact h
private theorem d_36_44 : D 36 44 = false := by have h := D_step 34 43; rw [d_34_43, d_35_43, d_36_43] at h; exact h
private theorem d_37_44 : D 37 44 = true := by have h := D_step 35 43; rw [d_35_43, d_36_43, d_37_43] at h; exact h
private theorem d_0_45 : D 0 45 = true := D_zero 45
private theorem d_1_45 : D 1 45 = true := by simpa using D_one 44
private theorem d_2_45 : D 2 45 = false := by have h := D_step 0 44; rw [d_0_44, d_1_44, d_2_44] at h; exact h
private theorem d_3_45 : D 3 45 = true := by have h := D_step 1 44; rw [d_1_44, d_2_44, d_3_44] at h; exact h
private theorem d_4_45 : D 4 45 = true := by have h := D_step 2 44; rw [d_2_44, d_3_44, d_4_44] at h; exact h
private theorem d_5_45 : D 5 45 = true := by have h := D_step 3 44; rw [d_3_44, d_4_44, d_5_44] at h; exact h
private theorem d_6_45 : D 6 45 = true := by have h := D_step 4 44; rw [d_4_44, d_5_44, d_6_44] at h; exact h
private theorem d_7_45 : D 7 45 = false := by have h := D_step 5 44; rw [d_5_44, d_6_44, d_7_44] at h; exact h
private theorem d_8_45 : D 8 45 = true := by have h := D_step 6 44; rw [d_6_44, d_7_44, d_8_44] at h; exact h
private theorem d_9_45 : D 9 45 = true := by have h := D_step 7 44; rw [d_7_44, d_8_44, d_9_44] at h; exact h
private theorem d_10_45 : D 10 45 = false := by have h := D_step 8 44; rw [d_8_44, d_9_44, d_10_44] at h; exact h
private theorem d_11_45 : D 11 45 = false := by have h := D_step 9 44; rw [d_9_44, d_10_44, d_11_44] at h; exact h
private theorem d_12_45 : D 12 45 = true := by have h := D_step 10 44; rw [d_10_44, d_11_44, d_12_44] at h; exact h
private theorem d_13_45 : D 13 45 = true := by have h := D_step 11 44; rw [d_11_44, d_12_44, d_13_44] at h; exact h
private theorem d_14_45 : D 14 45 = true := by have h := D_step 12 44; rw [d_12_44, d_13_44, d_14_44] at h; exact h
private theorem d_15_45 : D 15 45 = false := by have h := D_step 13 44; rw [d_13_44, d_14_44, d_15_44] at h; exact h
private theorem d_16_45 : D 16 45 = false := by have h := D_step 14 44; rw [d_14_44, d_15_44, d_16_44] at h; exact h
private theorem d_17_45 : D 17 45 = false := by have h := D_step 15 44; rw [d_15_44, d_16_44, d_17_44] at h; exact h
private theorem d_18_45 : D 18 45 = true := by have h := D_step 16 44; rw [d_16_44, d_17_44, d_18_44] at h; exact h
private theorem d_19_45 : D 19 45 = false := by have h := D_step 17 44; rw [d_17_44, d_18_44, d_19_44] at h; exact h
private theorem d_20_45 : D 20 45 = true := by have h := D_step 18 44; rw [d_18_44, d_19_44, d_20_44] at h; exact h
private theorem d_21_45 : D 21 45 = true := by have h := D_step 19 44; rw [d_19_44, d_20_44, d_21_44] at h; exact h
private theorem d_22_45 : D 22 45 = false := by have h := D_step 20 44; rw [d_20_44, d_21_44, d_22_44] at h; exact h
private theorem d_23_45 : D 23 45 = false := by have h := D_step 21 44; rw [d_21_44, d_22_44, d_23_44] at h; exact h
private theorem d_24_45 : D 24 45 = false := by have h := D_step 22 44; rw [d_22_44, d_23_44, d_24_44] at h; exact h
private theorem d_25_45 : D 25 45 = false := by have h := D_step 23 44; rw [d_23_44, d_24_44, d_25_44] at h; exact h
private theorem d_26_45 : D 26 45 = true := by have h := D_step 24 44; rw [d_24_44, d_25_44, d_26_44] at h; exact h
private theorem d_27_45 : D 27 45 = true := by have h := D_step 25 44; rw [d_25_44, d_26_44, d_27_44] at h; exact h
private theorem d_28_45 : D 28 45 = false := by have h := D_step 26 44; rw [d_26_44, d_27_44, d_28_44] at h; exact h
private theorem d_29_45 : D 29 45 = false := by have h := D_step 27 44; rw [d_27_44, d_28_44, d_29_44] at h; exact h
private theorem d_30_45 : D 30 45 = true := by have h := D_step 28 44; rw [d_28_44, d_29_44, d_30_44] at h; exact h
private theorem d_31_45 : D 31 45 = true := by have h := D_step 29 44; rw [d_29_44, d_30_44, d_31_44] at h; exact h
private theorem d_32_45 : D 32 45 = true := by have h := D_step 30 44; rw [d_30_44, d_31_44, d_32_44] at h; exact h
private theorem d_33_45 : D 33 45 = false := by have h := D_step 31 44; rw [d_31_44, d_32_44, d_33_44] at h; exact h
private theorem d_34_45 : D 34 45 = true := by have h := D_step 32 44; rw [d_32_44, d_33_44, d_34_44] at h; exact h
private theorem d_35_45 : D 35 45 = true := by have h := D_step 33 44; rw [d_33_44, d_34_44, d_35_44] at h; exact h
private theorem d_36_45 : D 36 45 = true := by have h := D_step 34 44; rw [d_34_44, d_35_44, d_36_44] at h; exact h
private theorem d_37_45 : D 37 45 = true := by have h := D_step 35 44; rw [d_35_44, d_36_44, d_37_44] at h; exact h
private theorem d_0_46 : D 0 46 = true := D_zero 46
private theorem d_1_46 : D 1 46 = true := by simpa using D_one 45
private theorem d_2_46 : D 2 46 = false := by have h := D_step 0 45; rw [d_0_45, d_1_45, d_2_45] at h; exact h
private theorem d_3_46 : D 3 46 = false := by have h := D_step 1 45; rw [d_1_45, d_2_45, d_3_45] at h; exact h
private theorem d_4_46 : D 4 46 = true := by have h := D_step 2 45; rw [d_2_45, d_3_45, d_4_45] at h; exact h
private theorem d_5_46 : D 5 46 = false := by have h := D_step 3 45; rw [d_3_45, d_4_45, d_5_45] at h; exact h
private theorem d_6_46 : D 6 46 = false := by have h := D_step 4 45; rw [d_4_45, d_5_45, d_6_45] at h; exact h
private theorem d_7_46 : D 7 46 = false := by have h := D_step 5 45; rw [d_5_45, d_6_45, d_7_45] at h; exact h
private theorem d_8_46 : D 8 46 = false := by have h := D_step 6 45; rw [d_6_45, d_7_45, d_8_45] at h; exact h
private theorem d_9_46 : D 9 46 = true := by have h := D_step 7 45; rw [d_7_45, d_8_45, d_9_45] at h; exact h
private theorem d_10_46 : D 10 46 = false := by have h := D_step 8 45; rw [d_8_45, d_9_45, d_10_45] at h; exact h
private theorem d_11_46 : D 11 46 = true := by have h := D_step 9 45; rw [d_9_45, d_10_45, d_11_45] at h; exact h
private theorem d_12_46 : D 12 46 = true := by have h := D_step 10 45; rw [d_10_45, d_11_45, d_12_45] at h; exact h
private theorem d_13_46 : D 13 46 = true := by have h := D_step 11 45; rw [d_11_45, d_12_45, d_13_45] at h; exact h
private theorem d_14_46 : D 14 46 = false := by have h := D_step 12 45; rw [d_12_45, d_13_45, d_14_45] at h; exact h
private theorem d_15_46 : D 15 46 = false := by have h := D_step 13 45; rw [d_13_45, d_14_45, d_15_45] at h; exact h
private theorem d_16_46 : D 16 46 = true := by have h := D_step 14 45; rw [d_14_45, d_15_45, d_16_45] at h; exact h
private theorem d_17_46 : D 17 46 = false := by have h := D_step 15 45; rw [d_15_45, d_16_45, d_17_45] at h; exact h
private theorem d_18_46 : D 18 46 = true := by have h := D_step 16 45; rw [d_16_45, d_17_45, d_18_45] at h; exact h
private theorem d_19_46 : D 19 46 = true := by have h := D_step 17 45; rw [d_17_45, d_18_45, d_19_45] at h; exact h
private theorem d_20_46 : D 20 46 = false := by have h := D_step 18 45; rw [d_18_45, d_19_45, d_20_45] at h; exact h
private theorem d_21_46 : D 21 46 = true := by have h := D_step 19 45; rw [d_19_45, d_20_45, d_21_45] at h; exact h
private theorem d_22_46 : D 22 46 = false := by have h := D_step 20 45; rw [d_20_45, d_21_45, d_22_45] at h; exact h
private theorem d_23_46 : D 23 46 = true := by have h := D_step 21 45; rw [d_21_45, d_22_45, d_23_45] at h; exact h
private theorem d_24_46 : D 24 46 = false := by have h := D_step 22 45; rw [d_22_45, d_23_45, d_24_45] at h; exact h
private theorem d_25_46 : D 25 46 = false := by have h := D_step 23 45; rw [d_23_45, d_24_45, d_25_45] at h; exact h
private theorem d_26_46 : D 26 46 = true := by have h := D_step 24 45; rw [d_24_45, d_25_45, d_26_45] at h; exact h
private theorem d_27_46 : D 27 46 = true := by have h := D_step 25 45; rw [d_25_45, d_26_45, d_27_45] at h; exact h
private theorem d_28_46 : D 28 46 = false := by have h := D_step 26 45; rw [d_26_45, d_27_45, d_28_45] at h; exact h
private theorem d_29_46 : D 29 46 = true := by have h := D_step 27 45; rw [d_27_45, d_28_45, d_29_45] at h; exact h
private theorem d_30_46 : D 30 46 = true := by have h := D_step 28 45; rw [d_28_45, d_29_45, d_30_45] at h; exact h
private theorem d_31_46 : D 31 46 = true := by have h := D_step 29 45; rw [d_29_45, d_30_45, d_31_45] at h; exact h
private theorem d_32_46 : D 32 46 = false := by have h := D_step 30 45; rw [d_30_45, d_31_45, d_32_45] at h; exact h
private theorem d_33_46 : D 33 46 = false := by have h := D_step 31 45; rw [d_31_45, d_32_45, d_33_45] at h; exact h
private theorem d_34_46 : D 34 46 = false := by have h := D_step 32 45; rw [d_32_45, d_33_45, d_34_45] at h; exact h
private theorem d_35_46 : D 35 46 = true := by have h := D_step 33 45; rw [d_33_45, d_34_45, d_35_45] at h; exact h
private theorem d_36_46 : D 36 46 = false := by have h := D_step 34 45; rw [d_34_45, d_35_45, d_36_45] at h; exact h
private theorem d_37_46 : D 37 46 = false := by have h := D_step 35 45; rw [d_35_45, d_36_45, d_37_45] at h; exact h

/-- **Three-Bit Gate Law for the Thirty-Sixth Left Diagonal (`D_thirty_six_eq_gate`):**
for every `t ≥ 46`, `D 36 t = (D 10 t && (D 8 t || !D 29 t))`. -/
theorem D_thirty_six_eq_gate : ∀ t : Nat, 46 ≤ t →
    D 36 t = (D 10 t && (D 8 t || !D 29 t))
  | 46, _ => by rw [d_36_46, d_8_46, d_10_46, d_29_46]; rfl
  | t + 1, ht => by
    by_cases h : t < 46
    · have h_eq : t + 1 = 46 := by omega
      rw [h_eq, d_36_46, d_8_46, d_10_46, d_29_46]; rfl
    · have ih := D_thirty_six_eq_gate t (by omega)
      have hstep := D_step 34 t
      rw [D_thirty_four_eq_mux t (by omega), D_thirty_five_eq_gate t (by omega), ih] at hstep
      rw [hstep, D_eight_succ_eq_D_ten t (by omega), D_ten_succ_eq_not_D_eight t (by omega),
          D_twenty_nine_step_closed t (by omega)]
      cases D 8 t <;> cases D 10 t <;> cases D 29 t <;> decide

/-- **Three-Bit Gate Law for the Thirty-Seventh Left Diagonal (`D_thirty_seven_eq_gate`):**
for every `t ≥ 46`, `D 37 t = (xor (D 8 t) (D 10 t) || !D 29 t)`. -/
theorem D_thirty_seven_eq_gate : ∀ t : Nat, 46 ≤ t →
    D 37 t = (xor (D 8 t) (D 10 t) || !D 29 t)
  | 46, _ => by rw [d_37_46, d_8_46, d_10_46, d_29_46]; rfl
  | t + 1, ht => by
    by_cases h : t < 46
    · have h_eq : t + 1 = 46 := by omega
      rw [h_eq, d_37_46, d_8_46, d_10_46, d_29_46]; rfl
    · have ih := D_thirty_seven_eq_gate t (by omega)
      have hstep := D_step 35 t
      rw [D_thirty_five_eq_gate t (by omega), D_thirty_six_eq_gate t (by omega), ih] at hstep
      rw [hstep, D_eight_succ_eq_D_ten t (by omega), D_ten_succ_eq_not_D_eight t (by omega),
          D_twenty_nine_step_closed t (by omega)]
      cases D 8 t <;> cases D 10 t <;> cases D 29 t <;> decide

/-- **Exact Eight-Step Block Weight of `D 36` (`D_thirty_six_block_eight_sum`):**
every 8 consecutive ticks of `D 36` from `t ≥ 46` on contain exactly 3 ones and 5 zeros. -/
theorem D_thirty_six_block_eight_sum (t : Nat) (ht : 46 ≤ t) :
    (if D 36 t then 1 else 0) + (if D 36 (t + 1) then 1 else 0) +
      (if D 36 (t + 2) then 1 else 0) + (if D 36 (t + 3) then 1 else 0) +
      (if D 36 (t + 4) then 1 else 0) + (if D 36 (t + 5) then 1 else 0) +
      (if D 36 (t + 6) then 1 else 0) + (if D 36 (t + 7) then 1 else 0) = 3 := by
  have g0 := D_thirty_six_eq_gate t ht
  have g1 := D_thirty_six_eq_gate (t + 1) (by omega)
  have g2 := D_thirty_six_eq_gate (t + 2) (by omega)
  have g3 := D_thirty_six_eq_gate (t + 3) (by omega)
  have g4 := D_thirty_six_eq_gate (t + 4) (by omega)
  have g5 := D_thirty_six_eq_gate (t + 5) (by omega)
  have g6 := D_thirty_six_eq_gate (t + 6) (by omega)
  have g7 := D_thirty_six_eq_gate (t + 7) (by omega)
  have s8_1 := D_eight_succ_eq_D_ten t (by omega)
  have s10_1 := D_ten_succ_eq_not_D_eight t (by omega)
  have s29_1 := D_twenty_nine_step_closed t (by omega)
  have s8_2 := D_eight_succ_eq_D_ten (t + 1) (by omega)
  have s10_2 := D_ten_succ_eq_not_D_eight (t + 1) (by omega)
  have s29_2 := D_twenty_nine_step_closed (t + 1) (by omega)
  have s8_3 := D_eight_succ_eq_D_ten (t + 2) (by omega)
  have s10_3 := D_ten_succ_eq_not_D_eight (t + 2) (by omega)
  have s29_3 := D_twenty_nine_step_closed (t + 2) (by omega)
  have p8_4 := D_eight_periodic_four t (by omega)
  have p10_4 := D_ten_periodic_four t (by omega)
  have p29_4 := D_twenty_nine_antiperiodic_four t (by omega)
  have p8_5 := D_eight_periodic_four (t + 1) (by omega)
  have p10_5 := D_ten_periodic_four (t + 1) (by omega)
  have p29_5 := D_twenty_nine_antiperiodic_four (t + 1) (by omega)
  have p8_6 := D_eight_periodic_four (t + 2) (by omega)
  have p10_6 := D_ten_periodic_four (t + 2) (by omega)
  have p29_6 := D_twenty_nine_antiperiodic_four (t + 2) (by omega)
  have p8_7 := D_eight_periodic_four (t + 3) (by omega)
  have p10_7 := D_ten_periodic_four (t + 3) (by omega)
  have p29_7 := D_twenty_nine_antiperiodic_four (t + 3) (by omega)
  rw [show t + 1 + 1 = t + 2 by omega] at s8_2 s10_2 s29_2
  rw [show t + 2 + 1 = t + 3 by omega] at s8_3 s10_3 s29_3
  rw [show t + 1 + 4 = t + 5 by omega] at p8_5 p10_5 p29_5
  rw [show t + 2 + 4 = t + 6 by omega] at p8_6 p10_6 p29_6
  rw [show t + 3 + 4 = t + 7 by omega] at p8_7 p10_7 p29_7
  rw [g0, g1, g2, g3, g4, g5, g6, g7,
      p8_4, p10_4, p29_4, p8_5, p10_5, p29_5, p8_6, p10_6, p29_6, p8_7, p10_7, p29_7,
      s8_3, s10_3, s29_3, s8_2, s10_2, s29_2, s8_1, s10_1, s29_1]
  cases D 8 t <;> cases D 10 t <;> cases D 29 t <;> decide

/-- **Exact Eight-Step Block Weight of `D 37` (`D_thirty_seven_block_eight_sum`):**
every 8 consecutive ticks of `D 37` from `t ≥ 46` on contain exactly 6 ones and 2 zeros. -/
theorem D_thirty_seven_block_eight_sum (t : Nat) (ht : 46 ≤ t) :
    (if D 37 t then 1 else 0) + (if D 37 (t + 1) then 1 else 0) +
      (if D 37 (t + 2) then 1 else 0) + (if D 37 (t + 3) then 1 else 0) +
      (if D 37 (t + 4) then 1 else 0) + (if D 37 (t + 5) then 1 else 0) +
      (if D 37 (t + 6) then 1 else 0) + (if D 37 (t + 7) then 1 else 0) = 6 := by
  have g0 := D_thirty_seven_eq_gate t ht
  have g1 := D_thirty_seven_eq_gate (t + 1) (by omega)
  have g2 := D_thirty_seven_eq_gate (t + 2) (by omega)
  have g3 := D_thirty_seven_eq_gate (t + 3) (by omega)
  have g4 := D_thirty_seven_eq_gate (t + 4) (by omega)
  have g5 := D_thirty_seven_eq_gate (t + 5) (by omega)
  have g6 := D_thirty_seven_eq_gate (t + 6) (by omega)
  have g7 := D_thirty_seven_eq_gate (t + 7) (by omega)
  have s8_1 := D_eight_succ_eq_D_ten t (by omega)
  have s10_1 := D_ten_succ_eq_not_D_eight t (by omega)
  have s29_1 := D_twenty_nine_step_closed t (by omega)
  have s8_2 := D_eight_succ_eq_D_ten (t + 1) (by omega)
  have s10_2 := D_ten_succ_eq_not_D_eight (t + 1) (by omega)
  have s29_2 := D_twenty_nine_step_closed (t + 1) (by omega)
  have s8_3 := D_eight_succ_eq_D_ten (t + 2) (by omega)
  have s10_3 := D_ten_succ_eq_not_D_eight (t + 2) (by omega)
  have s29_3 := D_twenty_nine_step_closed (t + 2) (by omega)
  have p8_4 := D_eight_periodic_four t (by omega)
  have p10_4 := D_ten_periodic_four t (by omega)
  have p29_4 := D_twenty_nine_antiperiodic_four t (by omega)
  have p8_5 := D_eight_periodic_four (t + 1) (by omega)
  have p10_5 := D_ten_periodic_four (t + 1) (by omega)
  have p29_5 := D_twenty_nine_antiperiodic_four (t + 1) (by omega)
  have p8_6 := D_eight_periodic_four (t + 2) (by omega)
  have p10_6 := D_ten_periodic_four (t + 2) (by omega)
  have p29_6 := D_twenty_nine_antiperiodic_four (t + 2) (by omega)
  have p8_7 := D_eight_periodic_four (t + 3) (by omega)
  have p10_7 := D_ten_periodic_four (t + 3) (by omega)
  have p29_7 := D_twenty_nine_antiperiodic_four (t + 3) (by omega)
  rw [show t + 1 + 1 = t + 2 by omega] at s8_2 s10_2 s29_2
  rw [show t + 2 + 1 = t + 3 by omega] at s8_3 s10_3 s29_3
  rw [show t + 1 + 4 = t + 5 by omega] at p8_5 p10_5 p29_5
  rw [show t + 2 + 4 = t + 6 by omega] at p8_6 p10_6 p29_6
  rw [show t + 3 + 4 = t + 7 by omega] at p8_7 p10_7 p29_7
  rw [g0, g1, g2, g3, g4, g5, g6, g7,
      p8_4, p10_4, p29_4, p8_5, p10_5, p29_5, p8_6, p10_6, p29_6, p8_7, p10_7, p29_7,
      s8_3, s10_3, s29_3, s8_2, s10_2, s29_2, s8_1, s10_1, s29_1]
  cases D 8 t <;> cases D 10 t <;> cases D 29 t <;> decide

/-! ### 13. Three-Bit Gate Cascade `D 38 .. D 44`, Period-4 Collapse `D 45 = D 10`, `HalfDensity (D 45)`, and All-Period 29-Column / 20-Period 31-Column Closure -/

private theorem d_38_19 : D 38 19 = true := by have h := D_step 36 18; rw [d_36_18, (D_eq_false_of_two_mul_lt 37 18 (by omega)), (D_eq_false_of_two_mul_lt 38 18 (by omega))] at h; exact h
private theorem d_38_20 : D 38 20 = false := by have h := D_step 36 19; rw [d_36_19, d_37_19, d_38_19] at h; exact h
private theorem d_39_20 : D 39 20 = false := by have h := D_step 37 19; rw [d_37_19, d_38_19, (D_eq_false_of_two_mul_lt 39 19 (by omega))] at h; exact h
private theorem d_40_20 : D 40 20 = true := by have h := D_step 38 19; rw [d_38_19, (D_eq_false_of_two_mul_lt 39 19 (by omega)), (D_eq_false_of_two_mul_lt 40 19 (by omega))] at h; exact h
private theorem d_38_21 : D 38 21 = true := by have h := D_step 36 20; rw [d_36_20, d_37_20, d_38_20] at h; exact h
private theorem d_39_21 : D 39 21 = false := by have h := D_step 37 20; rw [d_37_20, d_38_20, d_39_20] at h; exact h
private theorem d_40_21 : D 40 21 = true := by have h := D_step 38 20; rw [d_38_20, d_39_20, d_40_20] at h; exact h
private theorem d_41_21 : D 41 21 = true := by have h := D_step 39 20; rw [d_39_20, d_40_20, (D_eq_false_of_two_mul_lt 41 20 (by omega))] at h; exact h
private theorem d_42_21 : D 42 21 = true := by have h := D_step 40 20; rw [d_40_20, (D_eq_false_of_two_mul_lt 41 20 (by omega)), (D_eq_false_of_two_mul_lt 42 20 (by omega))] at h; exact h
private theorem d_38_22 : D 38 22 = false := by have h := D_step 36 21; rw [d_36_21, d_37_21, d_38_21] at h; exact h
private theorem d_39_22 : D 39 22 = false := by have h := D_step 37 21; rw [d_37_21, d_38_21, d_39_21] at h; exact h
private theorem d_40_22 : D 40 22 = false := by have h := D_step 38 21; rw [d_38_21, d_39_21, d_40_21] at h; exact h
private theorem d_41_22 : D 41 22 = true := by have h := D_step 39 21; rw [d_39_21, d_40_21, d_41_21] at h; exact h
private theorem d_42_22 : D 42 22 = false := by have h := D_step 40 21; rw [d_40_21, d_41_21, d_42_21] at h; exact h
private theorem d_43_22 : D 43 22 = false := by have h := D_step 41 21; rw [d_41_21, d_42_21, (D_eq_false_of_two_mul_lt 43 21 (by omega))] at h; exact h
private theorem d_44_22 : D 44 22 = true := by have h := D_step 42 21; rw [d_42_21, (D_eq_false_of_two_mul_lt 43 21 (by omega)), (D_eq_false_of_two_mul_lt 44 21 (by omega))] at h; exact h
private theorem d_38_23 : D 38 23 = true := by have h := D_step 36 22; rw [d_36_22, d_37_22, d_38_22] at h; exact h
private theorem d_39_23 : D 39 23 = true := by have h := D_step 37 22; rw [d_37_22, d_38_22, d_39_22] at h; exact h
private theorem d_40_23 : D 40 23 = false := by have h := D_step 38 22; rw [d_38_22, d_39_22, d_40_22] at h; exact h
private theorem d_41_23 : D 41 23 = true := by have h := D_step 39 22; rw [d_39_22, d_40_22, d_41_22] at h; exact h
private theorem d_42_23 : D 42 23 = true := by have h := D_step 40 22; rw [d_40_22, d_41_22, d_42_22] at h; exact h
private theorem d_43_23 : D 43 23 = true := by have h := D_step 41 22; rw [d_41_22, d_42_22, d_43_22] at h; exact h
private theorem d_44_23 : D 44 23 = true := by have h := D_step 42 22; rw [d_42_22, d_43_22, d_44_22] at h; exact h
private theorem d_45_23 : D 45 23 = true := by have h := D_step 43 22; rw [d_43_22, d_44_22, (D_eq_false_of_two_mul_lt 45 22 (by omega))] at h; exact h
private theorem d_38_24 : D 38 24 = false := by have h := D_step 36 23; rw [d_36_23, d_37_23, d_38_23] at h; exact h
private theorem d_39_24 : D 39 24 = true := by have h := D_step 37 23; rw [d_37_23, d_38_23, d_39_23] at h; exact h
private theorem d_40_24 : D 40 24 = false := by have h := D_step 38 23; rw [d_38_23, d_39_23, d_40_23] at h; exact h
private theorem d_41_24 : D 41 24 = false := by have h := D_step 39 23; rw [d_39_23, d_40_23, d_41_23] at h; exact h
private theorem d_42_24 : D 42 24 = true := by have h := D_step 40 23; rw [d_40_23, d_41_23, d_42_23] at h; exact h
private theorem d_43_24 : D 43 24 = false := by have h := D_step 41 23; rw [d_41_23, d_42_23, d_43_23] at h; exact h
private theorem d_44_24 : D 44 24 = false := by have h := D_step 42 23; rw [d_42_23, d_43_23, d_44_23] at h; exact h
private theorem d_45_24 : D 45 24 = false := by have h := D_step 43 23; rw [d_43_23, d_44_23, d_45_23] at h; exact h
private theorem d_38_25 : D 38 25 = false := by have h := D_step 36 24; rw [d_36_24, d_37_24, d_38_24] at h; exact h
private theorem d_39_25 : D 39 25 = false := by have h := D_step 37 24; rw [d_37_24, d_38_24, d_39_24] at h; exact h
private theorem d_40_25 : D 40 25 = true := by have h := D_step 38 24; rw [d_38_24, d_39_24, d_40_24] at h; exact h
private theorem d_41_25 : D 41 25 = true := by have h := D_step 39 24; rw [d_39_24, d_40_24, d_41_24] at h; exact h
private theorem d_42_25 : D 42 25 = true := by have h := D_step 40 24; rw [d_40_24, d_41_24, d_42_24] at h; exact h
private theorem d_43_25 : D 43 25 = true := by have h := D_step 41 24; rw [d_41_24, d_42_24, d_43_24] at h; exact h
private theorem d_44_25 : D 44 25 = true := by have h := D_step 42 24; rw [d_42_24, d_43_24, d_44_24] at h; exact h
private theorem d_45_25 : D 45 25 = false := by have h := D_step 43 24; rw [d_43_24, d_44_24, d_45_24] at h; exact h
private theorem d_38_26 : D 38 26 = false := by have h := D_step 36 25; rw [d_36_25, d_37_25, d_38_25] at h; exact h
private theorem d_39_26 : D 39 26 = false := by have h := D_step 37 25; rw [d_37_25, d_38_25, d_39_25] at h; exact h
private theorem d_40_26 : D 40 26 = true := by have h := D_step 38 25; rw [d_38_25, d_39_25, d_40_25] at h; exact h
private theorem d_41_26 : D 41 26 = true := by have h := D_step 39 25; rw [d_39_25, d_40_25, d_41_25] at h; exact h
private theorem d_42_26 : D 42 26 = false := by have h := D_step 40 25; rw [d_40_25, d_41_25, d_42_25] at h; exact h
private theorem d_43_26 : D 43 26 = false := by have h := D_step 41 25; rw [d_41_25, d_42_25, d_43_25] at h; exact h
private theorem d_44_26 : D 44 26 = false := by have h := D_step 42 25; rw [d_42_25, d_43_25, d_44_25] at h; exact h
private theorem d_45_26 : D 45 26 = false := by have h := D_step 43 25; rw [d_43_25, d_44_25, d_45_25] at h; exact h
private theorem d_38_27 : D 38 27 = true := by have h := D_step 36 26; rw [d_36_26, d_37_26, d_38_26] at h; exact h
private theorem d_39_27 : D 39 27 = false := by have h := D_step 37 26; rw [d_37_26, d_38_26, d_39_26] at h; exact h
private theorem d_40_27 : D 40 27 = true := by have h := D_step 38 26; rw [d_38_26, d_39_26, d_40_26] at h; exact h
private theorem d_41_27 : D 41 27 = true := by have h := D_step 39 26; rw [d_39_26, d_40_26, d_41_26] at h; exact h
private theorem d_42_27 : D 42 27 = false := by have h := D_step 40 26; rw [d_40_26, d_41_26, d_42_26] at h; exact h
private theorem d_43_27 : D 43 27 = true := by have h := D_step 41 26; rw [d_41_26, d_42_26, d_43_26] at h; exact h
private theorem d_44_27 : D 44 27 = false := by have h := D_step 42 26; rw [d_42_26, d_43_26, d_44_26] at h; exact h
private theorem d_45_27 : D 45 27 = false := by have h := D_step 43 26; rw [d_43_26, d_44_26, d_45_26] at h; exact h
private theorem d_38_28 : D 38 28 = false := by have h := D_step 36 27; rw [d_36_27, d_37_27, d_38_27] at h; exact h
private theorem d_39_28 : D 39 28 = true := by have h := D_step 37 27; rw [d_37_27, d_38_27, d_39_27] at h; exact h
private theorem d_40_28 : D 40 28 = false := by have h := D_step 38 27; rw [d_38_27, d_39_27, d_40_27] at h; exact h
private theorem d_41_28 : D 41 28 = true := by have h := D_step 39 27; rw [d_39_27, d_40_27, d_41_27] at h; exact h
private theorem d_42_28 : D 42 28 = false := by have h := D_step 40 27; rw [d_40_27, d_41_27, d_42_27] at h; exact h
private theorem d_43_28 : D 43 28 = false := by have h := D_step 41 27; rw [d_41_27, d_42_27, d_43_27] at h; exact h
private theorem d_44_28 : D 44 28 = true := by have h := D_step 42 27; rw [d_42_27, d_43_27, d_44_27] at h; exact h
private theorem d_45_28 : D 45 28 = true := by have h := D_step 43 27; rw [d_43_27, d_44_27, d_45_27] at h; exact h
private theorem d_38_29 : D 38 29 = false := by have h := D_step 36 28; rw [d_36_28, d_37_28, d_38_28] at h; exact h
private theorem d_39_29 : D 39 29 = true := by have h := D_step 37 28; rw [d_37_28, d_38_28, d_39_28] at h; exact h
private theorem d_40_29 : D 40 29 = true := by have h := D_step 38 28; rw [d_38_28, d_39_28, d_40_28] at h; exact h
private theorem d_41_29 : D 41 29 = false := by have h := D_step 39 28; rw [d_39_28, d_40_28, d_41_28] at h; exact h
private theorem d_42_29 : D 42 29 = true := by have h := D_step 40 28; rw [d_40_28, d_41_28, d_42_28] at h; exact h
private theorem d_43_29 : D 43 29 = true := by have h := D_step 41 28; rw [d_41_28, d_42_28, d_43_28] at h; exact h
private theorem d_44_29 : D 44 29 = true := by have h := D_step 42 28; rw [d_42_28, d_43_28, d_44_28] at h; exact h
private theorem d_45_29 : D 45 29 = true := by have h := D_step 43 28; rw [d_43_28, d_44_28, d_45_28] at h; exact h
private theorem d_38_30 : D 38 30 = true := by have h := D_step 36 29; rw [d_36_29, d_37_29, d_38_29] at h; exact h
private theorem d_39_30 : D 39 30 = true := by have h := D_step 37 29; rw [d_37_29, d_38_29, d_39_29] at h; exact h
private theorem d_40_30 : D 40 30 = true := by have h := D_step 38 29; rw [d_38_29, d_39_29, d_40_29] at h; exact h
private theorem d_41_30 : D 41 30 = false := by have h := D_step 39 29; rw [d_39_29, d_40_29, d_41_29] at h; exact h
private theorem d_42_30 : D 42 30 = false := by have h := D_step 40 29; rw [d_40_29, d_41_29, d_42_29] at h; exact h
private theorem d_43_30 : D 43 30 = true := by have h := D_step 41 29; rw [d_41_29, d_42_29, d_43_29] at h; exact h
private theorem d_44_30 : D 44 30 = false := by have h := D_step 42 29; rw [d_42_29, d_43_29, d_44_29] at h; exact h
private theorem d_45_30 : D 45 30 = false := by have h := D_step 43 29; rw [d_43_29, d_44_29, d_45_29] at h; exact h
private theorem d_38_31 : D 38 31 = false := by have h := D_step 36 30; rw [d_36_30, d_37_30, d_38_30] at h; exact h
private theorem d_39_31 : D 39 31 = false := by have h := D_step 37 30; rw [d_37_30, d_38_30, d_39_30] at h; exact h
private theorem d_40_31 : D 40 31 = false := by have h := D_step 38 30; rw [d_38_30, d_39_30, d_40_30] at h; exact h
private theorem d_41_31 : D 41 31 = false := by have h := D_step 39 30; rw [d_39_30, d_40_30, d_41_30] at h; exact h
private theorem d_42_31 : D 42 31 = true := by have h := D_step 40 30; rw [d_40_30, d_41_30, d_42_30] at h; exact h
private theorem d_43_31 : D 43 31 = true := by have h := D_step 41 30; rw [d_41_30, d_42_30, d_43_30] at h; exact h
private theorem d_44_31 : D 44 31 = true := by have h := D_step 42 30; rw [d_42_30, d_43_30, d_44_30] at h; exact h
private theorem d_45_31 : D 45 31 = true := by have h := D_step 43 30; rw [d_43_30, d_44_30, d_45_30] at h; exact h
private theorem d_38_32 : D 38 32 = true := by have h := D_step 36 31; rw [d_36_31, d_37_31, d_38_31] at h; exact h
private theorem d_39_32 : D 39 32 = false := by have h := D_step 37 31; rw [d_37_31, d_38_31, d_39_31] at h; exact h
private theorem d_40_32 : D 40 32 = false := by have h := D_step 38 31; rw [d_38_31, d_39_31, d_40_31] at h; exact h
private theorem d_41_32 : D 41 32 = false := by have h := D_step 39 31; rw [d_39_31, d_40_31, d_41_31] at h; exact h
private theorem d_42_32 : D 42 32 = true := by have h := D_step 40 31; rw [d_40_31, d_41_31, d_42_31] at h; exact h
private theorem d_43_32 : D 43 32 = true := by have h := D_step 41 31; rw [d_41_31, d_42_31, d_43_31] at h; exact h
private theorem d_44_32 : D 44 32 = false := by have h := D_step 42 31; rw [d_42_31, d_43_31, d_44_31] at h; exact h
private theorem d_45_32 : D 45 32 = false := by have h := D_step 43 31; rw [d_43_31, d_44_31, d_45_31] at h; exact h
private theorem d_38_33 : D 38 33 = true := by have h := D_step 36 32; rw [d_36_32, d_37_32, d_38_32] at h; exact h
private theorem d_39_33 : D 39 33 = true := by have h := D_step 37 32; rw [d_37_32, d_38_32, d_39_32] at h; exact h
private theorem d_40_33 : D 40 33 = true := by have h := D_step 38 32; rw [d_38_32, d_39_32, d_40_32] at h; exact h
private theorem d_41_33 : D 41 33 = false := by have h := D_step 39 32; rw [d_39_32, d_40_32, d_41_32] at h; exact h
private theorem d_42_33 : D 42 33 = true := by have h := D_step 40 32; rw [d_40_32, d_41_32, d_42_32] at h; exact h
private theorem d_43_33 : D 43 33 = true := by have h := D_step 41 32; rw [d_41_32, d_42_32, d_43_32] at h; exact h
private theorem d_44_33 : D 44 33 = false := by have h := D_step 42 32; rw [d_42_32, d_43_32, d_44_32] at h; exact h
private theorem d_45_33 : D 45 33 = true := by have h := D_step 43 32; rw [d_43_32, d_44_32, d_45_32] at h; exact h
private theorem d_38_34 : D 38 34 = false := by have h := D_step 36 33; rw [d_36_33, d_37_33, d_38_33] at h; exact h
private theorem d_39_34 : D 39 34 = true := by have h := D_step 37 33; rw [d_37_33, d_38_33, d_39_33] at h; exact h
private theorem d_40_34 : D 40 34 = false := by have h := D_step 38 33; rw [d_38_33, d_39_33, d_40_33] at h; exact h
private theorem d_41_34 : D 41 34 = false := by have h := D_step 39 33; rw [d_39_33, d_40_33, d_41_33] at h; exact h
private theorem d_42_34 : D 42 34 = false := by have h := D_step 40 33; rw [d_40_33, d_41_33, d_42_33] at h; exact h
private theorem d_43_34 : D 43 34 = true := by have h := D_step 41 33; rw [d_41_33, d_42_33, d_43_33] at h; exact h
private theorem d_44_34 : D 44 34 = false := by have h := D_step 42 33; rw [d_42_33, d_43_33, d_44_33] at h; exact h
private theorem d_45_34 : D 45 34 = false := by have h := D_step 43 33; rw [d_43_33, d_44_33, d_45_33] at h; exact h
private theorem d_38_35 : D 38 35 = true := by have h := D_step 36 34; rw [d_36_34, d_37_34, d_38_34] at h; exact h
private theorem d_39_35 : D 39 35 = false := by have h := D_step 37 34; rw [d_37_34, d_38_34, d_39_34] at h; exact h
private theorem d_40_35 : D 40 35 = true := by have h := D_step 38 34; rw [d_38_34, d_39_34, d_40_34] at h; exact h
private theorem d_41_35 : D 41 35 = true := by have h := D_step 39 34; rw [d_39_34, d_40_34, d_41_34] at h; exact h
private theorem d_42_35 : D 42 35 = false := by have h := D_step 40 34; rw [d_40_34, d_41_34, d_42_34] at h; exact h
private theorem d_43_35 : D 43 35 = true := by have h := D_step 41 34; rw [d_41_34, d_42_34, d_43_34] at h; exact h
private theorem d_44_35 : D 44 35 = true := by have h := D_step 42 34; rw [d_42_34, d_43_34, d_44_34] at h; exact h
private theorem d_45_35 : D 45 35 = true := by have h := D_step 43 34; rw [d_43_34, d_44_34, d_45_34] at h; exact h
private theorem d_38_36 : D 38 36 = false := by have h := D_step 36 35; rw [d_36_35, d_37_35, d_38_35] at h; exact h
private theorem d_39_36 : D 39 36 = false := by have h := D_step 37 35; rw [d_37_35, d_38_35, d_39_35] at h; exact h
private theorem d_40_36 : D 40 36 = false := by have h := D_step 38 35; rw [d_38_35, d_39_35, d_40_35] at h; exact h
private theorem d_41_36 : D 41 36 = true := by have h := D_step 39 35; rw [d_39_35, d_40_35, d_41_35] at h; exact h
private theorem d_42_36 : D 42 36 = false := by have h := D_step 40 35; rw [d_40_35, d_41_35, d_42_35] at h; exact h
private theorem d_43_36 : D 43 36 = false := by have h := D_step 41 35; rw [d_41_35, d_42_35, d_43_35] at h; exact h
private theorem d_44_36 : D 44 36 = true := by have h := D_step 42 35; rw [d_42_35, d_43_35, d_44_35] at h; exact h
private theorem d_45_36 : D 45 36 = false := by have h := D_step 43 35; rw [d_43_35, d_44_35, d_45_35] at h; exact h
private theorem d_38_37 : D 38 37 = false := by have h := D_step 36 36; rw [d_36_36, d_37_36, d_38_36] at h; exact h
private theorem d_39_37 : D 39 37 = false := by have h := D_step 37 36; rw [d_37_36, d_38_36, d_39_36] at h; exact h
private theorem d_40_37 : D 40 37 = false := by have h := D_step 38 36; rw [d_38_36, d_39_36, d_40_36] at h; exact h
private theorem d_41_37 : D 41 37 = true := by have h := D_step 39 36; rw [d_39_36, d_40_36, d_41_36] at h; exact h
private theorem d_42_37 : D 42 37 = true := by have h := D_step 40 36; rw [d_40_36, d_41_36, d_42_36] at h; exact h
private theorem d_43_37 : D 43 37 = true := by have h := D_step 41 36; rw [d_41_36, d_42_36, d_43_36] at h; exact h
private theorem d_44_37 : D 44 37 = true := by have h := D_step 42 36; rw [d_42_36, d_43_36, d_44_36] at h; exact h
private theorem d_45_37 : D 45 37 = true := by have h := D_step 43 36; rw [d_43_36, d_44_36, d_45_36] at h; exact h
private theorem d_38_38 : D 38 38 = false := by have h := D_step 36 37; rw [d_36_37, d_37_37, d_38_37] at h; exact h
private theorem d_39_38 : D 39 38 = true := by have h := D_step 37 37; rw [d_37_37, d_38_37, d_39_37] at h; exact h
private theorem d_40_38 : D 40 38 = false := by have h := D_step 38 37; rw [d_38_37, d_39_37, d_40_37] at h; exact h
private theorem d_41_38 : D 41 38 = true := by have h := D_step 39 37; rw [d_39_37, d_40_37, d_41_37] at h; exact h
private theorem d_42_38 : D 42 38 = true := by have h := D_step 40 37; rw [d_40_37, d_41_37, d_42_37] at h; exact h
private theorem d_43_38 : D 43 38 = false := by have h := D_step 41 37; rw [d_41_37, d_42_37, d_43_37] at h; exact h
private theorem d_44_38 : D 44 38 = false := by have h := D_step 42 37; rw [d_42_37, d_43_37, d_44_37] at h; exact h
private theorem d_45_38 : D 45 38 = false := by have h := D_step 43 37; rw [d_43_37, d_44_37, d_45_37] at h; exact h
private theorem d_38_39 : D 38 39 = true := by have h := D_step 36 38; rw [d_36_38, d_37_38, d_38_38] at h; exact h
private theorem d_39_39 : D 39 39 = true := by have h := D_step 37 38; rw [d_37_38, d_38_38, d_39_38] at h; exact h
private theorem d_40_39 : D 40 39 = true := by have h := D_step 38 38; rw [d_38_38, d_39_38, d_40_38] at h; exact h
private theorem d_41_39 : D 41 39 = false := by have h := D_step 39 38; rw [d_39_38, d_40_38, d_41_38] at h; exact h
private theorem d_42_39 : D 42 39 = true := by have h := D_step 40 38; rw [d_40_38, d_41_38, d_42_38] at h; exact h
private theorem d_43_39 : D 43 39 = false := by have h := D_step 41 38; rw [d_41_38, d_42_38, d_43_38] at h; exact h
private theorem d_44_39 : D 44 39 = true := by have h := D_step 42 38; rw [d_42_38, d_43_38, d_44_38] at h; exact h
private theorem d_45_39 : D 45 39 = false := by have h := D_step 43 38; rw [d_43_38, d_44_38, d_45_38] at h; exact h
private theorem d_38_40 : D 38 40 = true := by have h := D_step 36 39; rw [d_36_39, d_37_39, d_38_39] at h; exact h
private theorem d_39_40 : D 39 40 = true := by have h := D_step 37 39; rw [d_37_39, d_38_39, d_39_39] at h; exact h
private theorem d_40_40 : D 40 40 = false := by have h := D_step 38 39; rw [d_38_39, d_39_39, d_40_39] at h; exact h
private theorem d_41_40 : D 41 40 = false := by have h := D_step 39 39; rw [d_39_39, d_40_39, d_41_39] at h; exact h
private theorem d_42_40 : D 42 40 = false := by have h := D_step 40 39; rw [d_40_39, d_41_39, d_42_39] at h; exact h
private theorem d_43_40 : D 43 40 = true := by have h := D_step 41 39; rw [d_41_39, d_42_39, d_43_39] at h; exact h
private theorem d_44_40 : D 44 40 = false := by have h := D_step 42 39; rw [d_42_39, d_43_39, d_44_39] at h; exact h
private theorem d_45_40 : D 45 40 = true := by have h := D_step 43 39; rw [d_43_39, d_44_39, d_45_39] at h; exact h
private theorem d_38_41 : D 38 41 = true := by have h := D_step 36 40; rw [d_36_40, d_37_40, d_38_40] at h; exact h
private theorem d_39_41 : D 39 41 = false := by have h := D_step 37 40; rw [d_37_40, d_38_40, d_39_40] at h; exact h
private theorem d_40_41 : D 40 41 = false := by have h := D_step 38 40; rw [d_38_40, d_39_40, d_40_40] at h; exact h
private theorem d_41_41 : D 41 41 = true := by have h := D_step 39 40; rw [d_39_40, d_40_40, d_41_40] at h; exact h
private theorem d_42_41 : D 42 41 = false := by have h := D_step 40 40; rw [d_40_40, d_41_40, d_42_40] at h; exact h
private theorem d_43_41 : D 43 41 = true := by have h := D_step 41 40; rw [d_41_40, d_42_40, d_43_40] at h; exact h
private theorem d_44_41 : D 44 41 = true := by have h := D_step 42 40; rw [d_42_40, d_43_40, d_44_40] at h; exact h
private theorem d_45_41 : D 45 41 = false := by have h := D_step 43 40; rw [d_43_40, d_44_40, d_45_40] at h; exact h
private theorem d_38_42 : D 38 42 = false := by have h := D_step 36 41; rw [d_36_41, d_37_41, d_38_41] at h; exact h
private theorem d_39_42 : D 39 42 = false := by have h := D_step 37 41; rw [d_37_41, d_38_41, d_39_41] at h; exact h
private theorem d_40_42 : D 40 42 = true := by have h := D_step 38 41; rw [d_38_41, d_39_41, d_40_41] at h; exact h
private theorem d_41_42 : D 41 42 = true := by have h := D_step 39 41; rw [d_39_41, d_40_41, d_41_41] at h; exact h
private theorem d_42_42 : D 42 42 = true := by have h := D_step 40 41; rw [d_40_41, d_41_41, d_42_41] at h; exact h
private theorem d_43_42 : D 43 42 = false := by have h := D_step 41 41; rw [d_41_41, d_42_41, d_43_41] at h; exact h
private theorem d_44_42 : D 44 42 = true := by have h := D_step 42 41; rw [d_42_41, d_43_41, d_44_41] at h; exact h
private theorem d_45_42 : D 45 42 = false := by have h := D_step 43 41; rw [d_43_41, d_44_41, d_45_41] at h; exact h
private theorem d_38_43 : D 38 43 = false := by have h := D_step 36 42; rw [d_36_42, d_37_42, d_38_42] at h; exact h
private theorem d_39_43 : D 39 43 = true := by have h := D_step 37 42; rw [d_37_42, d_38_42, d_39_42] at h; exact h
private theorem d_40_43 : D 40 43 = true := by have h := D_step 38 42; rw [d_38_42, d_39_42, d_40_42] at h; exact h
private theorem d_41_43 : D 41 43 = true := by have h := D_step 39 42; rw [d_39_42, d_40_42, d_41_42] at h; exact h
private theorem d_42_43 : D 42 43 = false := by have h := D_step 40 42; rw [d_40_42, d_41_42, d_42_42] at h; exact h
private theorem d_43_43 : D 43 43 = false := by have h := D_step 41 42; rw [d_41_42, d_42_42, d_43_42] at h; exact h
private theorem d_44_43 : D 44 43 = false := by have h := D_step 42 42; rw [d_42_42, d_43_42, d_44_42] at h; exact h
private theorem d_45_43 : D 45 43 = true := by have h := D_step 43 42; rw [d_43_42, d_44_42, d_45_42] at h; exact h
private theorem d_38_44 : D 38 44 = false := by have h := D_step 36 43; rw [d_36_43, d_37_43, d_38_43] at h; exact h
private theorem d_39_44 : D 39 44 = false := by have h := D_step 37 43; rw [d_37_43, d_38_43, d_39_43] at h; exact h
private theorem d_40_44 : D 40 44 = true := by have h := D_step 38 43; rw [d_38_43, d_39_43, d_40_43] at h; exact h
private theorem d_41_44 : D 41 44 = false := by have h := D_step 39 43; rw [d_39_43, d_40_43, d_41_43] at h; exact h
private theorem d_42_44 : D 42 44 = false := by have h := D_step 40 43; rw [d_40_43, d_41_43, d_42_43] at h; exact h
private theorem d_43_44 : D 43 44 = true := by have h := D_step 41 43; rw [d_41_43, d_42_43, d_43_43] at h; exact h
private theorem d_44_44 : D 44 44 = false := by have h := D_step 42 43; rw [d_42_43, d_43_43, d_44_43] at h; exact h
private theorem d_45_44 : D 45 44 = true := by have h := D_step 43 43; rw [d_43_43, d_44_43, d_45_43] at h; exact h
private theorem d_38_45 : D 38 45 = true := by have h := D_step 36 44; rw [d_36_44, d_37_44, d_38_44] at h; exact h
private theorem d_39_45 : D 39 45 = true := by have h := D_step 37 44; rw [d_37_44, d_38_44, d_39_44] at h; exact h
private theorem d_40_45 : D 40 45 = true := by have h := D_step 38 44; rw [d_38_44, d_39_44, d_40_44] at h; exact h
private theorem d_41_45 : D 41 45 = true := by have h := D_step 39 44; rw [d_39_44, d_40_44, d_41_44] at h; exact h
private theorem d_42_45 : D 42 45 = true := by have h := D_step 40 44; rw [d_40_44, d_41_44, d_42_44] at h; exact h
private theorem d_43_45 : D 43 45 = true := by have h := D_step 41 44; rw [d_41_44, d_42_44, d_43_44] at h; exact h
private theorem d_44_45 : D 44 45 = true := by have h := D_step 42 44; rw [d_42_44, d_43_44, d_44_44] at h; exact h
private theorem d_45_45 : D 45 45 = false := by have h := D_step 43 44; rw [d_43_44, d_44_44, d_45_44] at h; exact h
private theorem d_38_46 : D 38 46 = false := by have h := D_step 36 45; rw [d_36_45, d_37_45, d_38_45] at h; exact h
private theorem d_39_46 : D 39 46 = false := by have h := D_step 37 45; rw [d_37_45, d_38_45, d_39_45] at h; exact h
private theorem d_40_46 : D 40 46 = false := by have h := D_step 38 45; rw [d_38_45, d_39_45, d_40_45] at h; exact h
private theorem d_41_46 : D 41 46 = false := by have h := D_step 39 45; rw [d_39_45, d_40_45, d_41_45] at h; exact h
private theorem d_42_46 : D 42 46 = false := by have h := D_step 40 45; rw [d_40_45, d_41_45, d_42_45] at h; exact h
private theorem d_43_46 : D 43 46 = false := by have h := D_step 41 45; rw [d_41_45, d_42_45, d_43_45] at h; exact h
private theorem d_44_46 : D 44 46 = false := by have h := D_step 42 45; rw [d_42_45, d_43_45, d_44_45] at h; exact h
private theorem d_45_46 : D 45 46 = false := by have h := D_step 43 45; rw [d_43_45, d_44_45, d_45_45] at h; exact h
private theorem d_0_47 : D 0 47 = true := D_zero 47
private theorem d_1_47 : D 1 47 = true := by simpa using D_one 46
private theorem d_2_47 : D 2 47 = false := by have h := D_step 0 46; rw [d_0_46, d_1_46, d_2_46] at h; exact h
private theorem d_3_47 : D 3 47 = true := by have h := D_step 1 46; rw [d_1_46, d_2_46, d_3_46] at h; exact h
private theorem d_4_47 : D 4 47 = true := by have h := D_step 2 46; rw [d_2_46, d_3_46, d_4_46] at h; exact h
private theorem d_5_47 : D 5 47 = true := by have h := D_step 3 46; rw [d_3_46, d_4_46, d_5_46] at h; exact h
private theorem d_6_47 : D 6 47 = true := by have h := D_step 4 46; rw [d_4_46, d_5_46, d_6_46] at h; exact h
private theorem d_7_47 : D 7 47 = false := by have h := D_step 5 46; rw [d_5_46, d_6_46, d_7_46] at h; exact h
private theorem d_8_47 : D 8 47 = false := by have h := D_step 6 46; rw [d_6_46, d_7_46, d_8_46] at h; exact h
private theorem d_9_47 : D 9 47 = true := by have h := D_step 7 46; rw [d_7_46, d_8_46, d_9_46] at h; exact h
private theorem d_10_47 : D 10 47 = true := by have h := D_step 8 46; rw [d_8_46, d_9_46, d_10_46] at h; exact h
private theorem d_11_47 : D 11 47 = false := by have h := D_step 9 46; rw [d_9_46, d_10_46, d_11_46] at h; exact h
private theorem d_12_47 : D 12 47 = true := by have h := D_step 10 46; rw [d_10_46, d_11_46, d_12_46] at h; exact h
private theorem d_13_47 : D 13 47 = false := by have h := D_step 11 46; rw [d_11_46, d_12_46, d_13_46] at h; exact h
private theorem d_14_47 : D 14 47 = false := by have h := D_step 12 46; rw [d_12_46, d_13_46, d_14_46] at h; exact h
private theorem d_15_47 : D 15 47 = true := by have h := D_step 13 46; rw [d_13_46, d_14_46, d_15_46] at h; exact h
private theorem d_16_47 : D 16 47 = true := by have h := D_step 14 46; rw [d_14_46, d_15_46, d_16_46] at h; exact h
private theorem d_17_47 : D 17 47 = true := by have h := D_step 15 46; rw [d_15_46, d_16_46, d_17_46] at h; exact h
private theorem d_18_47 : D 18 47 = false := by have h := D_step 16 46; rw [d_16_46, d_17_46, d_18_46] at h; exact h
private theorem d_19_47 : D 19 47 = true := by have h := D_step 17 46; rw [d_17_46, d_18_46, d_19_46] at h; exact h
private theorem d_20_47 : D 20 47 = false := by have h := D_step 18 46; rw [d_18_46, d_19_46, d_20_46] at h; exact h
private theorem d_21_47 : D 21 47 = false := by have h := D_step 19 46; rw [d_19_46, d_20_46, d_21_46] at h; exact h
private theorem d_22_47 : D 22 47 = true := by have h := D_step 20 46; rw [d_20_46, d_21_46, d_22_46] at h; exact h
private theorem d_23_47 : D 23 47 = false := by have h := D_step 21 46; rw [d_21_46, d_22_46, d_23_46] at h; exact h
private theorem d_24_47 : D 24 47 = true := by have h := D_step 22 46; rw [d_22_46, d_23_46, d_24_46] at h; exact h
private theorem d_25_47 : D 25 47 = true := by have h := D_step 23 46; rw [d_23_46, d_24_46, d_25_46] at h; exact h
private theorem d_26_47 : D 26 47 = true := by have h := D_step 24 46; rw [d_24_46, d_25_46, d_26_46] at h; exact h
private theorem d_27_47 : D 27 47 = true := by have h := D_step 25 46; rw [d_25_46, d_26_46, d_27_46] at h; exact h
private theorem d_28_47 : D 28 47 = false := by have h := D_step 26 46; rw [d_26_46, d_27_46, d_28_46] at h; exact h
private theorem d_29_47 : D 29 47 = false := by have h := D_step 27 46; rw [d_27_46, d_28_46, d_29_46] at h; exact h
private theorem d_30_47 : D 30 47 = true := by have h := D_step 28 46; rw [d_28_46, d_29_46, d_30_46] at h; exact h
private theorem d_31_47 : D 31 47 = false := by have h := D_step 29 46; rw [d_29_46, d_30_46, d_31_46] at h; exact h
private theorem d_32_47 : D 32 47 = false := by have h := D_step 30 46; rw [d_30_46, d_31_46, d_32_46] at h; exact h
private theorem d_33_47 : D 33 47 = true := by have h := D_step 31 46; rw [d_31_46, d_32_46, d_33_46] at h; exact h
private theorem d_34_47 : D 34 47 = false := by have h := D_step 32 46; rw [d_32_46, d_33_46, d_34_46] at h; exact h
private theorem d_35_47 : D 35 47 = true := by have h := D_step 33 46; rw [d_33_46, d_34_46, d_35_46] at h; exact h
private theorem d_36_47 : D 36 47 = true := by have h := D_step 34 46; rw [d_34_46, d_35_46, d_36_46] at h; exact h
private theorem d_37_47 : D 37 47 = true := by have h := D_step 35 46; rw [d_35_46, d_36_46, d_37_46] at h; exact h
private theorem d_38_47 : D 38 47 = false := by have h := D_step 36 46; rw [d_36_46, d_37_46, d_38_46] at h; exact h
private theorem d_39_47 : D 39 47 = false := by have h := D_step 37 46; rw [d_37_46, d_38_46, d_39_46] at h; exact h
private theorem d_40_47 : D 40 47 = false := by have h := D_step 38 46; rw [d_38_46, d_39_46, d_40_46] at h; exact h
private theorem d_41_47 : D 41 47 = false := by have h := D_step 39 46; rw [d_39_46, d_40_46, d_41_46] at h; exact h
private theorem d_42_47 : D 42 47 = false := by have h := D_step 40 46; rw [d_40_46, d_41_46, d_42_46] at h; exact h
private theorem d_43_47 : D 43 47 = false := by have h := D_step 41 46; rw [d_41_46, d_42_46, d_43_46] at h; exact h
private theorem d_44_47 : D 44 47 = false := by have h := D_step 42 46; rw [d_42_46, d_43_46, d_44_46] at h; exact h
private theorem d_45_47 : D 45 47 = false := by have h := D_step 43 46; rw [d_43_46, d_44_46, d_45_46] at h; exact h
private theorem d_0_48 : D 0 48 = true := D_zero 48
private theorem d_1_48 : D 1 48 = true := by simpa using D_one 47
private theorem d_2_48 : D 2 48 = false := by have h := D_step 0 47; rw [d_0_47, d_1_47, d_2_47] at h; exact h
private theorem d_3_48 : D 3 48 = false := by have h := D_step 1 47; rw [d_1_47, d_2_47, d_3_47] at h; exact h
private theorem d_4_48 : D 4 48 = true := by have h := D_step 2 47; rw [d_2_47, d_3_47, d_4_47] at h; exact h
private theorem d_5_48 : D 5 48 = false := by have h := D_step 3 47; rw [d_3_47, d_4_47, d_5_47] at h; exact h
private theorem d_6_48 : D 6 48 = false := by have h := D_step 4 47; rw [d_4_47, d_5_47, d_6_47] at h; exact h
private theorem d_7_48 : D 7 48 = false := by have h := D_step 5 47; rw [d_5_47, d_6_47, d_7_47] at h; exact h
private theorem d_8_48 : D 8 48 = true := by have h := D_step 6 47; rw [d_6_47, d_7_47, d_8_47] at h; exact h
private theorem d_9_48 : D 9 48 = true := by have h := D_step 7 47; rw [d_7_47, d_8_47, d_9_47] at h; exact h
private theorem d_10_48 : D 10 48 = true := by have h := D_step 8 47; rw [d_8_47, d_9_47, d_10_47] at h; exact h
private theorem d_11_48 : D 11 48 = false := by have h := D_step 9 47; rw [d_9_47, d_10_47, d_11_47] at h; exact h
private theorem d_12_48 : D 12 48 = false := by have h := D_step 10 47; rw [d_10_47, d_11_47, d_12_47] at h; exact h
private theorem d_13_48 : D 13 48 = true := by have h := D_step 11 47; rw [d_11_47, d_12_47, d_13_47] at h; exact h
private theorem d_14_48 : D 14 48 = true := by have h := D_step 12 47; rw [d_12_47, d_13_47, d_14_47] at h; exact h
private theorem d_15_48 : D 15 48 = true := by have h := D_step 13 47; rw [d_13_47, d_14_47, d_15_47] at h; exact h
private theorem d_16_48 : D 16 48 = true := by have h := D_step 14 47; rw [d_14_47, d_15_47, d_16_47] at h; exact h
private theorem d_17_48 : D 17 48 = false := by have h := D_step 15 47; rw [d_15_47, d_16_47, d_17_47] at h; exact h
private theorem d_18_48 : D 18 48 = false := by have h := D_step 16 47; rw [d_16_47, d_17_47, d_18_47] at h; exact h
private theorem d_19_48 : D 19 48 = false := by have h := D_step 17 47; rw [d_17_47, d_18_47, d_19_47] at h; exact h
private theorem d_20_48 : D 20 48 = true := by have h := D_step 18 47; rw [d_18_47, d_19_47, d_20_47] at h; exact h
private theorem d_21_48 : D 21 48 = true := by have h := D_step 19 47; rw [d_19_47, d_20_47, d_21_47] at h; exact h
private theorem d_22_48 : D 22 48 = true := by have h := D_step 20 47; rw [d_20_47, d_21_47, d_22_47] at h; exact h
private theorem d_23_48 : D 23 48 = true := by have h := D_step 21 47; rw [d_21_47, d_22_47, d_23_47] at h; exact h
private theorem d_24_48 : D 24 48 = false := by have h := D_step 22 47; rw [d_22_47, d_23_47, d_24_47] at h; exact h
private theorem d_25_48 : D 25 48 = true := by have h := D_step 23 47; rw [d_23_47, d_24_47, d_25_47] at h; exact h
private theorem d_26_48 : D 26 48 = false := by have h := D_step 24 47; rw [d_24_47, d_25_47, d_26_47] at h; exact h
private theorem d_27_48 : D 27 48 = false := by have h := D_step 25 47; rw [d_25_47, d_26_47, d_27_47] at h; exact h
private theorem d_28_48 : D 28 48 = false := by have h := D_step 26 47; rw [d_26_47, d_27_47, d_28_47] at h; exact h
private theorem d_29_48 : D 29 48 = true := by have h := D_step 27 47; rw [d_27_47, d_28_47, d_29_47] at h; exact h
private theorem d_30_48 : D 30 48 = true := by have h := D_step 28 47; rw [d_28_47, d_29_47, d_30_47] at h; exact h
private theorem d_31_48 : D 31 48 = true := by have h := D_step 29 47; rw [d_29_47, d_30_47, d_31_47] at h; exact h
private theorem d_32_48 : D 32 48 = true := by have h := D_step 30 47; rw [d_30_47, d_31_47, d_32_47] at h; exact h
private theorem d_33_48 : D 33 48 = true := by have h := D_step 31 47; rw [d_31_47, d_32_47, d_33_47] at h; exact h
private theorem d_34_48 : D 34 48 = true := by have h := D_step 32 47; rw [d_32_47, d_33_47, d_34_47] at h; exact h
private theorem d_35_48 : D 35 48 = false := by have h := D_step 33 47; rw [d_33_47, d_34_47, d_35_47] at h; exact h
private theorem d_36_48 : D 36 48 = true := by have h := D_step 34 47; rw [d_34_47, d_35_47, d_36_47] at h; exact h
private theorem d_37_48 : D 37 48 = false := by have h := D_step 35 47; rw [d_35_47, d_36_47, d_37_47] at h; exact h
private theorem d_38_48 : D 38 48 = false := by have h := D_step 36 47; rw [d_36_47, d_37_47, d_38_47] at h; exact h
private theorem d_39_48 : D 39 48 = true := by have h := D_step 37 47; rw [d_37_47, d_38_47, d_39_47] at h; exact h
private theorem d_40_48 : D 40 48 = false := by have h := D_step 38 47; rw [d_38_47, d_39_47, d_40_47] at h; exact h
private theorem d_41_48 : D 41 48 = false := by have h := D_step 39 47; rw [d_39_47, d_40_47, d_41_47] at h; exact h
private theorem d_42_48 : D 42 48 = false := by have h := D_step 40 47; rw [d_40_47, d_41_47, d_42_47] at h; exact h
private theorem d_43_48 : D 43 48 = false := by have h := D_step 41 47; rw [d_41_47, d_42_47, d_43_47] at h; exact h
private theorem d_44_48 : D 44 48 = false := by have h := D_step 42 47; rw [d_42_47, d_43_47, d_44_47] at h; exact h
private theorem d_45_48 : D 45 48 = false := by have h := D_step 43 47; rw [d_43_47, d_44_47, d_45_47] at h; exact h
private theorem d_0_49 : D 0 49 = true := D_zero 49
private theorem d_1_49 : D 1 49 = true := by simpa using D_one 48
private theorem d_2_49 : D 2 49 = false := by have h := D_step 0 48; rw [d_0_48, d_1_48, d_2_48] at h; exact h
private theorem d_3_49 : D 3 49 = true := by have h := D_step 1 48; rw [d_1_48, d_2_48, d_3_48] at h; exact h
private theorem d_4_49 : D 4 49 = true := by have h := D_step 2 48; rw [d_2_48, d_3_48, d_4_48] at h; exact h
private theorem d_5_49 : D 5 49 = true := by have h := D_step 3 48; rw [d_3_48, d_4_48, d_5_48] at h; exact h
private theorem d_6_49 : D 6 49 = true := by have h := D_step 4 48; rw [d_4_48, d_5_48, d_6_48] at h; exact h
private theorem d_7_49 : D 7 49 = false := by have h := D_step 5 48; rw [d_5_48, d_6_48, d_7_48] at h; exact h
private theorem d_8_49 : D 8 49 = true := by have h := D_step 6 48; rw [d_6_48, d_7_48, d_8_48] at h; exact h
private theorem d_9_49 : D 9 49 = true := by have h := D_step 7 48; rw [d_7_48, d_8_48, d_9_48] at h; exact h
private theorem d_10_49 : D 10 49 = false := by have h := D_step 8 48; rw [d_8_48, d_9_48, d_10_48] at h; exact h
private theorem d_11_49 : D 11 49 = false := by have h := D_step 9 48; rw [d_9_48, d_10_48, d_11_48] at h; exact h
private theorem d_12_49 : D 12 49 = true := by have h := D_step 10 48; rw [d_10_48, d_11_48, d_12_48] at h; exact h
private theorem d_13_49 : D 13 49 = true := by have h := D_step 11 48; rw [d_11_48, d_12_48, d_13_48] at h; exact h
private theorem d_14_49 : D 14 49 = true := by have h := D_step 12 48; rw [d_12_48, d_13_48, d_14_48] at h; exact h
private theorem d_15_49 : D 15 49 = false := by have h := D_step 13 48; rw [d_13_48, d_14_48, d_15_48] at h; exact h
private theorem d_16_49 : D 16 49 = false := by have h := D_step 14 48; rw [d_14_48, d_15_48, d_16_48] at h; exact h
private theorem d_17_49 : D 17 49 = false := by have h := D_step 15 48; rw [d_15_48, d_16_48, d_17_48] at h; exact h
private theorem d_18_49 : D 18 49 = true := by have h := D_step 16 48; rw [d_16_48, d_17_48, d_18_48] at h; exact h
private theorem d_19_49 : D 19 49 = false := by have h := D_step 17 48; rw [d_17_48, d_18_48, d_19_48] at h; exact h
private theorem d_20_49 : D 20 49 = true := by have h := D_step 18 48; rw [d_18_48, d_19_48, d_20_48] at h; exact h
private theorem d_21_49 : D 21 49 = true := by have h := D_step 19 48; rw [d_19_48, d_20_48, d_21_48] at h; exact h
private theorem d_22_49 : D 22 49 = false := by have h := D_step 20 48; rw [d_20_48, d_21_48, d_22_48] at h; exact h
private theorem d_23_49 : D 23 49 = false := by have h := D_step 21 48; rw [d_21_48, d_22_48, d_23_48] at h; exact h
private theorem d_24_49 : D 24 49 = false := by have h := D_step 22 48; rw [d_22_48, d_23_48, d_24_48] at h; exact h
private theorem d_25_49 : D 25 49 = false := by have h := D_step 23 48; rw [d_23_48, d_24_48, d_25_48] at h; exact h
private theorem d_26_49 : D 26 49 = true := by have h := D_step 24 48; rw [d_24_48, d_25_48, d_26_48] at h; exact h
private theorem d_27_49 : D 27 49 = true := by have h := D_step 25 48; rw [d_25_48, d_26_48, d_27_48] at h; exact h
private theorem d_28_49 : D 28 49 = false := by have h := D_step 26 48; rw [d_26_48, d_27_48, d_28_48] at h; exact h
private theorem d_29_49 : D 29 49 = true := by have h := D_step 27 48; rw [d_27_48, d_28_48, d_29_48] at h; exact h
private theorem d_30_49 : D 30 49 = true := by have h := D_step 28 48; rw [d_28_48, d_29_48, d_30_48] at h; exact h
private theorem d_31_49 : D 31 49 = false := by have h := D_step 29 48; rw [d_29_48, d_30_48, d_31_48] at h; exact h
private theorem d_32_49 : D 32 49 = false := by have h := D_step 30 48; rw [d_30_48, d_31_48, d_32_48] at h; exact h
private theorem d_33_49 : D 33 49 = false := by have h := D_step 31 48; rw [d_31_48, d_32_48, d_33_48] at h; exact h
private theorem d_34_49 : D 34 49 = false := by have h := D_step 32 48; rw [d_32_48, d_33_48, d_34_48] at h; exact h
private theorem d_35_49 : D 35 49 = false := by have h := D_step 33 48; rw [d_33_48, d_34_48, d_35_48] at h; exact h
private theorem d_36_49 : D 36 49 = false := by have h := D_step 34 48; rw [d_34_48, d_35_48, d_36_48] at h; exact h
private theorem d_37_49 : D 37 49 = true := by have h := D_step 35 48; rw [d_35_48, d_36_48, d_37_48] at h; exact h
private theorem d_38_49 : D 38 49 = true := by have h := D_step 36 48; rw [d_36_48, d_37_48, d_38_48] at h; exact h
private theorem d_39_49 : D 39 49 = true := by have h := D_step 37 48; rw [d_37_48, d_38_48, d_39_48] at h; exact h
private theorem d_40_49 : D 40 49 = true := by have h := D_step 38 48; rw [d_38_48, d_39_48, d_40_48] at h; exact h
private theorem d_41_49 : D 41 49 = true := by have h := D_step 39 48; rw [d_39_48, d_40_48, d_41_48] at h; exact h
private theorem d_42_49 : D 42 49 = false := by have h := D_step 40 48; rw [d_40_48, d_41_48, d_42_48] at h; exact h
private theorem d_43_49 : D 43 49 = false := by have h := D_step 41 48; rw [d_41_48, d_42_48, d_43_48] at h; exact h
private theorem d_44_49 : D 44 49 = false := by have h := D_step 42 48; rw [d_42_48, d_43_48, d_44_48] at h; exact h
private theorem d_45_49 : D 45 49 = false := by have h := D_step 43 48; rw [d_43_48, d_44_48, d_45_48] at h; exact h
private theorem d_0_50 : D 0 50 = true := D_zero 50
private theorem d_1_50 : D 1 50 = true := by simpa using D_one 49
private theorem d_2_50 : D 2 50 = false := by have h := D_step 0 49; rw [d_0_49, d_1_49, d_2_49] at h; exact h
private theorem d_3_50 : D 3 50 = false := by have h := D_step 1 49; rw [d_1_49, d_2_49, d_3_49] at h; exact h
private theorem d_4_50 : D 4 50 = true := by have h := D_step 2 49; rw [d_2_49, d_3_49, d_4_49] at h; exact h
private theorem d_5_50 : D 5 50 = false := by have h := D_step 3 49; rw [d_3_49, d_4_49, d_5_49] at h; exact h
private theorem d_6_50 : D 6 50 = false := by have h := D_step 4 49; rw [d_4_49, d_5_49, d_6_49] at h; exact h
private theorem d_7_50 : D 7 50 = false := by have h := D_step 5 49; rw [d_5_49, d_6_49, d_7_49] at h; exact h
private theorem d_8_50 : D 8 50 = false := by have h := D_step 6 49; rw [d_6_49, d_7_49, d_8_49] at h; exact h
private theorem d_9_50 : D 9 50 = true := by have h := D_step 7 49; rw [d_7_49, d_8_49, d_9_49] at h; exact h
private theorem d_10_50 : D 10 50 = false := by have h := D_step 8 49; rw [d_8_49, d_9_49, d_10_49] at h; exact h
private theorem d_11_50 : D 11 50 = true := by have h := D_step 9 49; rw [d_9_49, d_10_49, d_11_49] at h; exact h
private theorem d_12_50 : D 12 50 = true := by have h := D_step 10 49; rw [d_10_49, d_11_49, d_12_49] at h; exact h
private theorem d_13_50 : D 13 50 = true := by have h := D_step 11 49; rw [d_11_49, d_12_49, d_13_49] at h; exact h
private theorem d_14_50 : D 14 50 = false := by have h := D_step 12 49; rw [d_12_49, d_13_49, d_14_49] at h; exact h
private theorem d_15_50 : D 15 50 = false := by have h := D_step 13 49; rw [d_13_49, d_14_49, d_15_49] at h; exact h
private theorem d_16_50 : D 16 50 = true := by have h := D_step 14 49; rw [d_14_49, d_15_49, d_16_49] at h; exact h
private theorem d_17_50 : D 17 50 = false := by have h := D_step 15 49; rw [d_15_49, d_16_49, d_17_49] at h; exact h
private theorem d_18_50 : D 18 50 = true := by have h := D_step 16 49; rw [d_16_49, d_17_49, d_18_49] at h; exact h
private theorem d_19_50 : D 19 50 = true := by have h := D_step 17 49; rw [d_17_49, d_18_49, d_19_49] at h; exact h
private theorem d_20_50 : D 20 50 = false := by have h := D_step 18 49; rw [d_18_49, d_19_49, d_20_49] at h; exact h
private theorem d_21_50 : D 21 50 = true := by have h := D_step 19 49; rw [d_19_49, d_20_49, d_21_49] at h; exact h
private theorem d_22_50 : D 22 50 = false := by have h := D_step 20 49; rw [d_20_49, d_21_49, d_22_49] at h; exact h
private theorem d_23_50 : D 23 50 = true := by have h := D_step 21 49; rw [d_21_49, d_22_49, d_23_49] at h; exact h
private theorem d_24_50 : D 24 50 = false := by have h := D_step 22 49; rw [d_22_49, d_23_49, d_24_49] at h; exact h
private theorem d_25_50 : D 25 50 = false := by have h := D_step 23 49; rw [d_23_49, d_24_49, d_25_49] at h; exact h
private theorem d_26_50 : D 26 50 = true := by have h := D_step 24 49; rw [d_24_49, d_25_49, d_26_49] at h; exact h
private theorem d_27_50 : D 27 50 = true := by have h := D_step 25 49; rw [d_25_49, d_26_49, d_27_49] at h; exact h
private theorem d_28_50 : D 28 50 = false := by have h := D_step 26 49; rw [d_26_49, d_27_49, d_28_49] at h; exact h
private theorem d_29_50 : D 29 50 = false := by have h := D_step 27 49; rw [d_27_49, d_28_49, d_29_49] at h; exact h
private theorem d_30_50 : D 30 50 = true := by have h := D_step 28 49; rw [d_28_49, d_29_49, d_30_49] at h; exact h
private theorem d_31_50 : D 31 50 = false := by have h := D_step 29 49; rw [d_29_49, d_30_49, d_31_49] at h; exact h
private theorem d_32_50 : D 32 50 = true := by have h := D_step 30 49; rw [d_30_49, d_31_49, d_32_49] at h; exact h
private theorem d_33_50 : D 33 50 = false := by have h := D_step 31 49; rw [d_31_49, d_32_49, d_33_49] at h; exact h
private theorem d_34_50 : D 34 50 = false := by have h := D_step 32 49; rw [d_32_49, d_33_49, d_34_49] at h; exact h
private theorem d_35_50 : D 35 50 = false := by have h := D_step 33 49; rw [d_33_49, d_34_49, d_35_49] at h; exact h
private theorem d_36_50 : D 36 50 = false := by have h := D_step 34 49; rw [d_34_49, d_35_49, d_36_49] at h; exact h
private theorem d_37_50 : D 37 50 = true := by have h := D_step 35 49; rw [d_35_49, d_36_49, d_37_49] at h; exact h
private theorem d_38_50 : D 38 50 = true := by have h := D_step 36 49; rw [d_36_49, d_37_49, d_38_49] at h; exact h
private theorem d_39_50 : D 39 50 = false := by have h := D_step 37 49; rw [d_37_49, d_38_49, d_39_49] at h; exact h
private theorem d_40_50 : D 40 50 = false := by have h := D_step 38 49; rw [d_38_49, d_39_49, d_40_49] at h; exact h
private theorem d_41_50 : D 41 50 = false := by have h := D_step 39 49; rw [d_39_49, d_40_49, d_41_49] at h; exact h
private theorem d_42_50 : D 42 50 = false := by have h := D_step 40 49; rw [d_40_49, d_41_49, d_42_49] at h; exact h
private theorem d_43_50 : D 43 50 = true := by have h := D_step 41 49; rw [d_41_49, d_42_49, d_43_49] at h; exact h
private theorem d_44_50 : D 44 50 = false := by have h := D_step 42 49; rw [d_42_49, d_43_49, d_44_49] at h; exact h
private theorem d_45_50 : D 45 50 = false := by have h := D_step 43 49; rw [d_43_49, d_44_49, d_45_49] at h; exact h
private theorem d_0_51 : D 0 51 = true := D_zero 51
private theorem d_1_51 : D 1 51 = true := by simpa using D_one 50
private theorem d_2_51 : D 2 51 = false := by have h := D_step 0 50; rw [d_0_50, d_1_50, d_2_50] at h; exact h
private theorem d_3_51 : D 3 51 = true := by have h := D_step 1 50; rw [d_1_50, d_2_50, d_3_50] at h; exact h
private theorem d_4_51 : D 4 51 = true := by have h := D_step 2 50; rw [d_2_50, d_3_50, d_4_50] at h; exact h
private theorem d_5_51 : D 5 51 = true := by have h := D_step 3 50; rw [d_3_50, d_4_50, d_5_50] at h; exact h
private theorem d_6_51 : D 6 51 = true := by have h := D_step 4 50; rw [d_4_50, d_5_50, d_6_50] at h; exact h
private theorem d_7_51 : D 7 51 = false := by have h := D_step 5 50; rw [d_5_50, d_6_50, d_7_50] at h; exact h
private theorem d_8_51 : D 8 51 = false := by have h := D_step 6 50; rw [d_6_50, d_7_50, d_8_50] at h; exact h
private theorem d_9_51 : D 9 51 = true := by have h := D_step 7 50; rw [d_7_50, d_8_50, d_9_50] at h; exact h
private theorem d_10_51 : D 10 51 = true := by have h := D_step 8 50; rw [d_8_50, d_9_50, d_10_50] at h; exact h
private theorem d_11_51 : D 11 51 = false := by have h := D_step 9 50; rw [d_9_50, d_10_50, d_11_50] at h; exact h
private theorem d_12_51 : D 12 51 = true := by have h := D_step 10 50; rw [d_10_50, d_11_50, d_12_50] at h; exact h
private theorem d_13_51 : D 13 51 = false := by have h := D_step 11 50; rw [d_11_50, d_12_50, d_13_50] at h; exact h
private theorem d_14_51 : D 14 51 = false := by have h := D_step 12 50; rw [d_12_50, d_13_50, d_14_50] at h; exact h
private theorem d_15_51 : D 15 51 = true := by have h := D_step 13 50; rw [d_13_50, d_14_50, d_15_50] at h; exact h
private theorem d_16_51 : D 16 51 = true := by have h := D_step 14 50; rw [d_14_50, d_15_50, d_16_50] at h; exact h
private theorem d_17_51 : D 17 51 = true := by have h := D_step 15 50; rw [d_15_50, d_16_50, d_17_50] at h; exact h
private theorem d_18_51 : D 18 51 = false := by have h := D_step 16 50; rw [d_16_50, d_17_50, d_18_50] at h; exact h
private theorem d_19_51 : D 19 51 = true := by have h := D_step 17 50; rw [d_17_50, d_18_50, d_19_50] at h; exact h
private theorem d_20_51 : D 20 51 = false := by have h := D_step 18 50; rw [d_18_50, d_19_50, d_20_50] at h; exact h
private theorem d_21_51 : D 21 51 = false := by have h := D_step 19 50; rw [d_19_50, d_20_50, d_21_50] at h; exact h
private theorem d_22_51 : D 22 51 = true := by have h := D_step 20 50; rw [d_20_50, d_21_50, d_22_50] at h; exact h
private theorem d_23_51 : D 23 51 = false := by have h := D_step 21 50; rw [d_21_50, d_22_50, d_23_50] at h; exact h
private theorem d_24_51 : D 24 51 = true := by have h := D_step 22 50; rw [d_22_50, d_23_50, d_24_50] at h; exact h
private theorem d_25_51 : D 25 51 = true := by have h := D_step 23 50; rw [d_23_50, d_24_50, d_25_50] at h; exact h
private theorem d_26_51 : D 26 51 = true := by have h := D_step 24 50; rw [d_24_50, d_25_50, d_26_50] at h; exact h
private theorem d_27_51 : D 27 51 = true := by have h := D_step 25 50; rw [d_25_50, d_26_50, d_27_50] at h; exact h
private theorem d_28_51 : D 28 51 = false := by have h := D_step 26 50; rw [d_26_50, d_27_50, d_28_50] at h; exact h
private theorem d_29_51 : D 29 51 = true := by have h := D_step 27 50; rw [d_27_50, d_28_50, d_29_50] at h; exact h
private theorem d_30_51 : D 30 51 = true := by have h := D_step 28 50; rw [d_28_50, d_29_50, d_30_50] at h; exact h
private theorem d_31_51 : D 31 51 = true := by have h := D_step 29 50; rw [d_29_50, d_30_50, d_31_50] at h; exact h
private theorem d_32_51 : D 32 51 = false := by have h := D_step 30 50; rw [d_30_50, d_31_50, d_32_50] at h; exact h
private theorem d_33_51 : D 33 51 = true := by have h := D_step 31 50; rw [d_31_50, d_32_50, d_33_50] at h; exact h
private theorem d_34_51 : D 34 51 = true := by have h := D_step 32 50; rw [d_32_50, d_33_50, d_34_50] at h; exact h
private theorem d_35_51 : D 35 51 = false := by have h := D_step 33 50; rw [d_33_50, d_34_50, d_35_50] at h; exact h
private theorem d_36_51 : D 36 51 = false := by have h := D_step 34 50; rw [d_34_50, d_35_50, d_36_50] at h; exact h
private theorem d_37_51 : D 37 51 = true := by have h := D_step 35 50; rw [d_35_50, d_36_50, d_37_50] at h; exact h
private theorem d_38_51 : D 38 51 = true := by have h := D_step 36 50; rw [d_36_50, d_37_50, d_38_50] at h; exact h
private theorem d_39_51 : D 39 51 = false := by have h := D_step 37 50; rw [d_37_50, d_38_50, d_39_50] at h; exact h
private theorem d_40_51 : D 40 51 = true := by have h := D_step 38 50; rw [d_38_50, d_39_50, d_40_50] at h; exact h
private theorem d_41_51 : D 41 51 = false := by have h := D_step 39 50; rw [d_39_50, d_40_50, d_41_50] at h; exact h
private theorem d_42_51 : D 42 51 = false := by have h := D_step 40 50; rw [d_40_50, d_41_50, d_42_50] at h; exact h
private theorem d_43_51 : D 43 51 = true := by have h := D_step 41 50; rw [d_41_50, d_42_50, d_43_50] at h; exact h
private theorem d_44_51 : D 44 51 = true := by have h := D_step 42 50; rw [d_42_50, d_43_50, d_44_50] at h; exact h
private theorem d_45_51 : D 45 51 = true := by have h := D_step 43 50; rw [d_43_50, d_44_50, d_45_50] at h; exact h
private theorem d_0_52 : D 0 52 = true := D_zero 52
private theorem d_1_52 : D 1 52 = true := by simpa using D_one 51
private theorem d_2_52 : D 2 52 = false := by have h := D_step 0 51; rw [d_0_51, d_1_51, d_2_51] at h; exact h
private theorem d_3_52 : D 3 52 = false := by have h := D_step 1 51; rw [d_1_51, d_2_51, d_3_51] at h; exact h
private theorem d_4_52 : D 4 52 = true := by have h := D_step 2 51; rw [d_2_51, d_3_51, d_4_51] at h; exact h
private theorem d_5_52 : D 5 52 = false := by have h := D_step 3 51; rw [d_3_51, d_4_51, d_5_51] at h; exact h
private theorem d_6_52 : D 6 52 = false := by have h := D_step 4 51; rw [d_4_51, d_5_51, d_6_51] at h; exact h
private theorem d_7_52 : D 7 52 = false := by have h := D_step 5 51; rw [d_5_51, d_6_51, d_7_51] at h; exact h
private theorem d_8_52 : D 8 52 = true := by have h := D_step 6 51; rw [d_6_51, d_7_51, d_8_51] at h; exact h
private theorem d_9_52 : D 9 52 = true := by have h := D_step 7 51; rw [d_7_51, d_8_51, d_9_51] at h; exact h
private theorem d_10_52 : D 10 52 = true := by have h := D_step 8 51; rw [d_8_51, d_9_51, d_10_51] at h; exact h
private theorem d_11_52 : D 11 52 = false := by have h := D_step 9 51; rw [d_9_51, d_10_51, d_11_51] at h; exact h
private theorem d_12_52 : D 12 52 = false := by have h := D_step 10 51; rw [d_10_51, d_11_51, d_12_51] at h; exact h
private theorem d_13_52 : D 13 52 = true := by have h := D_step 11 51; rw [d_11_51, d_12_51, d_13_51] at h; exact h
private theorem d_14_52 : D 14 52 = true := by have h := D_step 12 51; rw [d_12_51, d_13_51, d_14_51] at h; exact h
private theorem d_15_52 : D 15 52 = true := by have h := D_step 13 51; rw [d_13_51, d_14_51, d_15_51] at h; exact h
private theorem d_16_52 : D 16 52 = true := by have h := D_step 14 51; rw [d_14_51, d_15_51, d_16_51] at h; exact h
private theorem d_17_52 : D 17 52 = false := by have h := D_step 15 51; rw [d_15_51, d_16_51, d_17_51] at h; exact h
private theorem d_18_52 : D 18 52 = false := by have h := D_step 16 51; rw [d_16_51, d_17_51, d_18_51] at h; exact h
private theorem d_19_52 : D 19 52 = false := by have h := D_step 17 51; rw [d_17_51, d_18_51, d_19_51] at h; exact h
private theorem d_20_52 : D 20 52 = true := by have h := D_step 18 51; rw [d_18_51, d_19_51, d_20_51] at h; exact h
private theorem d_21_52 : D 21 52 = true := by have h := D_step 19 51; rw [d_19_51, d_20_51, d_21_51] at h; exact h
private theorem d_22_52 : D 22 52 = true := by have h := D_step 20 51; rw [d_20_51, d_21_51, d_22_51] at h; exact h
private theorem d_23_52 : D 23 52 = true := by have h := D_step 21 51; rw [d_21_51, d_22_51, d_23_51] at h; exact h
private theorem d_24_52 : D 24 52 = false := by have h := D_step 22 51; rw [d_22_51, d_23_51, d_24_51] at h; exact h
private theorem d_25_52 : D 25 52 = true := by have h := D_step 23 51; rw [d_23_51, d_24_51, d_25_51] at h; exact h
private theorem d_26_52 : D 26 52 = false := by have h := D_step 24 51; rw [d_24_51, d_25_51, d_26_51] at h; exact h
private theorem d_27_52 : D 27 52 = false := by have h := D_step 25 51; rw [d_25_51, d_26_51, d_27_51] at h; exact h
private theorem d_28_52 : D 28 52 = false := by have h := D_step 26 51; rw [d_26_51, d_27_51, d_28_51] at h; exact h
private theorem d_29_52 : D 29 52 = false := by have h := D_step 27 51; rw [d_27_51, d_28_51, d_29_51] at h; exact h
private theorem d_30_52 : D 30 52 = true := by have h := D_step 28 51; rw [d_28_51, d_29_51, d_30_51] at h; exact h
private theorem d_31_52 : D 31 52 = false := by have h := D_step 29 51; rw [d_29_51, d_30_51, d_31_51] at h; exact h
private theorem d_32_52 : D 32 52 = false := by have h := D_step 30 51; rw [d_30_51, d_31_51, d_32_51] at h; exact h
private theorem d_33_52 : D 33 52 = false := by have h := D_step 31 51; rw [d_31_51, d_32_51, d_33_51] at h; exact h
private theorem d_34_52 : D 34 52 = true := by have h := D_step 32 51; rw [d_32_51, d_33_51, d_34_51] at h; exact h
private theorem d_35_52 : D 35 52 = false := by have h := D_step 33 51; rw [d_33_51, d_34_51, d_35_51] at h; exact h
private theorem d_36_52 : D 36 52 = true := by have h := D_step 34 51; rw [d_34_51, d_35_51, d_36_51] at h; exact h
private theorem d_37_52 : D 37 52 = true := by have h := D_step 35 51; rw [d_35_51, d_36_51, d_37_51] at h; exact h
private theorem d_38_52 : D 38 52 = true := by have h := D_step 36 51; rw [d_36_51, d_37_51, d_38_51] at h; exact h
private theorem d_39_52 : D 39 52 = false := by have h := D_step 37 51; rw [d_37_51, d_38_51, d_39_51] at h; exact h
private theorem d_40_52 : D 40 52 = false := by have h := D_step 38 51; rw [d_38_51, d_39_51, d_40_51] at h; exact h
private theorem d_41_52 : D 41 52 = true := by have h := D_step 39 51; rw [d_39_51, d_40_51, d_41_51] at h; exact h
private theorem d_42_52 : D 42 52 = true := by have h := D_step 40 51; rw [d_40_51, d_41_51, d_42_51] at h; exact h
private theorem d_43_52 : D 43 52 = true := by have h := D_step 41 51; rw [d_41_51, d_42_51, d_43_51] at h; exact h
private theorem d_44_52 : D 44 52 = true := by have h := D_step 42 51; rw [d_42_51, d_43_51, d_44_51] at h; exact h
private theorem d_45_52 : D 45 52 = false := by have h := D_step 43 51; rw [d_43_51, d_44_51, d_45_51] at h; exact h
private theorem d_0_53 : D 0 53 = true := D_zero 53
private theorem d_1_53 : D 1 53 = true := by simpa using D_one 52
private theorem d_2_53 : D 2 53 = false := by have h := D_step 0 52; rw [d_0_52, d_1_52, d_2_52] at h; exact h
private theorem d_3_53 : D 3 53 = true := by have h := D_step 1 52; rw [d_1_52, d_2_52, d_3_52] at h; exact h
private theorem d_4_53 : D 4 53 = true := by have h := D_step 2 52; rw [d_2_52, d_3_52, d_4_52] at h; exact h
private theorem d_5_53 : D 5 53 = true := by have h := D_step 3 52; rw [d_3_52, d_4_52, d_5_52] at h; exact h
private theorem d_6_53 : D 6 53 = true := by have h := D_step 4 52; rw [d_4_52, d_5_52, d_6_52] at h; exact h
private theorem d_7_53 : D 7 53 = false := by have h := D_step 5 52; rw [d_5_52, d_6_52, d_7_52] at h; exact h
private theorem d_8_53 : D 8 53 = true := by have h := D_step 6 52; rw [d_6_52, d_7_52, d_8_52] at h; exact h
private theorem d_9_53 : D 9 53 = true := by have h := D_step 7 52; rw [d_7_52, d_8_52, d_9_52] at h; exact h
private theorem d_10_53 : D 10 53 = false := by have h := D_step 8 52; rw [d_8_52, d_9_52, d_10_52] at h; exact h
private theorem d_11_53 : D 11 53 = false := by have h := D_step 9 52; rw [d_9_52, d_10_52, d_11_52] at h; exact h
private theorem d_12_53 : D 12 53 = true := by have h := D_step 10 52; rw [d_10_52, d_11_52, d_12_52] at h; exact h
private theorem d_13_53 : D 13 53 = true := by have h := D_step 11 52; rw [d_11_52, d_12_52, d_13_52] at h; exact h
private theorem d_14_53 : D 14 53 = true := by have h := D_step 12 52; rw [d_12_52, d_13_52, d_14_52] at h; exact h
private theorem d_15_53 : D 15 53 = false := by have h := D_step 13 52; rw [d_13_52, d_14_52, d_15_52] at h; exact h
private theorem d_16_53 : D 16 53 = false := by have h := D_step 14 52; rw [d_14_52, d_15_52, d_16_52] at h; exact h
private theorem d_17_53 : D 17 53 = false := by have h := D_step 15 52; rw [d_15_52, d_16_52, d_17_52] at h; exact h
private theorem d_18_53 : D 18 53 = true := by have h := D_step 16 52; rw [d_16_52, d_17_52, d_18_52] at h; exact h
private theorem d_19_53 : D 19 53 = false := by have h := D_step 17 52; rw [d_17_52, d_18_52, d_19_52] at h; exact h
private theorem d_20_53 : D 20 53 = true := by have h := D_step 18 52; rw [d_18_52, d_19_52, d_20_52] at h; exact h
private theorem d_21_53 : D 21 53 = true := by have h := D_step 19 52; rw [d_19_52, d_20_52, d_21_52] at h; exact h
private theorem d_22_53 : D 22 53 = false := by have h := D_step 20 52; rw [d_20_52, d_21_52, d_22_52] at h; exact h
private theorem d_23_53 : D 23 53 = false := by have h := D_step 21 52; rw [d_21_52, d_22_52, d_23_52] at h; exact h
private theorem d_24_53 : D 24 53 = false := by have h := D_step 22 52; rw [d_22_52, d_23_52, d_24_52] at h; exact h
private theorem d_25_53 : D 25 53 = false := by have h := D_step 23 52; rw [d_23_52, d_24_52, d_25_52] at h; exact h
private theorem d_26_53 : D 26 53 = true := by have h := D_step 24 52; rw [d_24_52, d_25_52, d_26_52] at h; exact h
private theorem d_27_53 : D 27 53 = true := by have h := D_step 25 52; rw [d_25_52, d_26_52, d_27_52] at h; exact h
private theorem d_28_53 : D 28 53 = false := by have h := D_step 26 52; rw [d_26_52, d_27_52, d_28_52] at h; exact h
private theorem d_29_53 : D 29 53 = false := by have h := D_step 27 52; rw [d_27_52, d_28_52, d_29_52] at h; exact h
private theorem d_30_53 : D 30 53 = true := by have h := D_step 28 52; rw [d_28_52, d_29_52, d_30_52] at h; exact h
private theorem d_31_53 : D 31 53 = true := by have h := D_step 29 52; rw [d_29_52, d_30_52, d_31_52] at h; exact h
private theorem d_32_53 : D 32 53 = true := by have h := D_step 30 52; rw [d_30_52, d_31_52, d_32_52] at h; exact h
private theorem d_33_53 : D 33 53 = false := by have h := D_step 31 52; rw [d_31_52, d_32_52, d_33_52] at h; exact h
private theorem d_34_53 : D 34 53 = true := by have h := D_step 32 52; rw [d_32_52, d_33_52, d_34_52] at h; exact h
private theorem d_35_53 : D 35 53 = true := by have h := D_step 33 52; rw [d_33_52, d_34_52, d_35_52] at h; exact h
private theorem d_36_53 : D 36 53 = false := by have h := D_step 34 52; rw [d_34_52, d_35_52, d_36_52] at h; exact h
private theorem d_37_53 : D 37 53 = true := by have h := D_step 35 52; rw [d_35_52, d_36_52, d_37_52] at h; exact h
private theorem d_38_53 : D 38 53 = false := by have h := D_step 36 52; rw [d_36_52, d_37_52, d_38_52] at h; exact h
private theorem d_39_53 : D 39 53 = false := by have h := D_step 37 52; rw [d_37_52, d_38_52, d_39_52] at h; exact h
private theorem d_40_53 : D 40 53 = true := by have h := D_step 38 52; rw [d_38_52, d_39_52, d_40_52] at h; exact h
private theorem d_41_53 : D 41 53 = true := by have h := D_step 39 52; rw [d_39_52, d_40_52, d_41_52] at h; exact h
private theorem d_42_53 : D 42 53 = true := by have h := D_step 40 52; rw [d_40_52, d_41_52, d_42_52] at h; exact h
private theorem d_43_53 : D 43 53 = false := by have h := D_step 41 52; rw [d_41_52, d_42_52, d_43_52] at h; exact h
private theorem d_44_53 : D 44 53 = false := by have h := D_step 42 52; rw [d_42_52, d_43_52, d_44_52] at h; exact h
private theorem d_45_53 : D 45 53 = false := by have h := D_step 43 52; rw [d_43_52, d_44_52, d_45_52] at h; exact h
private theorem d_0_54 : D 0 54 = true := D_zero 54
private theorem d_1_54 : D 1 54 = true := by simpa using D_one 53
private theorem d_2_54 : D 2 54 = false := by have h := D_step 0 53; rw [d_0_53, d_1_53, d_2_53] at h; exact h
private theorem d_3_54 : D 3 54 = false := by have h := D_step 1 53; rw [d_1_53, d_2_53, d_3_53] at h; exact h
private theorem d_4_54 : D 4 54 = true := by have h := D_step 2 53; rw [d_2_53, d_3_53, d_4_53] at h; exact h
private theorem d_5_54 : D 5 54 = false := by have h := D_step 3 53; rw [d_3_53, d_4_53, d_5_53] at h; exact h
private theorem d_6_54 : D 6 54 = false := by have h := D_step 4 53; rw [d_4_53, d_5_53, d_6_53] at h; exact h
private theorem d_7_54 : D 7 54 = false := by have h := D_step 5 53; rw [d_5_53, d_6_53, d_7_53] at h; exact h
private theorem d_8_54 : D 8 54 = false := by have h := D_step 6 53; rw [d_6_53, d_7_53, d_8_53] at h; exact h
private theorem d_9_54 : D 9 54 = true := by have h := D_step 7 53; rw [d_7_53, d_8_53, d_9_53] at h; exact h
private theorem d_10_54 : D 10 54 = false := by have h := D_step 8 53; rw [d_8_53, d_9_53, d_10_53] at h; exact h
private theorem d_11_54 : D 11 54 = true := by have h := D_step 9 53; rw [d_9_53, d_10_53, d_11_53] at h; exact h
private theorem d_12_54 : D 12 54 = true := by have h := D_step 10 53; rw [d_10_53, d_11_53, d_12_53] at h; exact h
private theorem d_13_54 : D 13 54 = true := by have h := D_step 11 53; rw [d_11_53, d_12_53, d_13_53] at h; exact h
private theorem d_14_54 : D 14 54 = false := by have h := D_step 12 53; rw [d_12_53, d_13_53, d_14_53] at h; exact h
private theorem d_15_54 : D 15 54 = false := by have h := D_step 13 53; rw [d_13_53, d_14_53, d_15_53] at h; exact h
private theorem d_16_54 : D 16 54 = true := by have h := D_step 14 53; rw [d_14_53, d_15_53, d_16_53] at h; exact h
private theorem d_17_54 : D 17 54 = false := by have h := D_step 15 53; rw [d_15_53, d_16_53, d_17_53] at h; exact h
private theorem d_18_54 : D 18 54 = true := by have h := D_step 16 53; rw [d_16_53, d_17_53, d_18_53] at h; exact h
private theorem d_19_54 : D 19 54 = true := by have h := D_step 17 53; rw [d_17_53, d_18_53, d_19_53] at h; exact h
private theorem d_20_54 : D 20 54 = false := by have h := D_step 18 53; rw [d_18_53, d_19_53, d_20_53] at h; exact h
private theorem d_21_54 : D 21 54 = true := by have h := D_step 19 53; rw [d_19_53, d_20_53, d_21_53] at h; exact h
private theorem d_22_54 : D 22 54 = false := by have h := D_step 20 53; rw [d_20_53, d_21_53, d_22_53] at h; exact h
private theorem d_23_54 : D 23 54 = true := by have h := D_step 21 53; rw [d_21_53, d_22_53, d_23_53] at h; exact h
private theorem d_24_54 : D 24 54 = false := by have h := D_step 22 53; rw [d_22_53, d_23_53, d_24_53] at h; exact h
private theorem d_25_54 : D 25 54 = false := by have h := D_step 23 53; rw [d_23_53, d_24_53, d_25_53] at h; exact h
private theorem d_26_54 : D 26 54 = true := by have h := D_step 24 53; rw [d_24_53, d_25_53, d_26_53] at h; exact h
private theorem d_27_54 : D 27 54 = true := by have h := D_step 25 53; rw [d_25_53, d_26_53, d_27_53] at h; exact h
private theorem d_28_54 : D 28 54 = false := by have h := D_step 26 53; rw [d_26_53, d_27_53, d_28_53] at h; exact h
private theorem d_29_54 : D 29 54 = true := by have h := D_step 27 53; rw [d_27_53, d_28_53, d_29_53] at h; exact h
private theorem d_30_54 : D 30 54 = true := by have h := D_step 28 53; rw [d_28_53, d_29_53, d_30_53] at h; exact h
private theorem d_31_54 : D 31 54 = true := by have h := D_step 29 53; rw [d_29_53, d_30_53, d_31_53] at h; exact h
private theorem d_32_54 : D 32 54 = false := by have h := D_step 30 53; rw [d_30_53, d_31_53, d_32_53] at h; exact h
private theorem d_33_54 : D 33 54 = false := by have h := D_step 31 53; rw [d_31_53, d_32_53, d_33_53] at h; exact h
private theorem d_34_54 : D 34 54 = false := by have h := D_step 32 53; rw [d_32_53, d_33_53, d_34_53] at h; exact h
private theorem d_35_54 : D 35 54 = true := by have h := D_step 33 53; rw [d_33_53, d_34_53, d_35_53] at h; exact h
private theorem d_36_54 : D 36 54 = false := by have h := D_step 34 53; rw [d_34_53, d_35_53, d_36_53] at h; exact h
private theorem d_37_54 : D 37 54 = false := by have h := D_step 35 53; rw [d_35_53, d_36_53, d_37_53] at h; exact h
private theorem d_38_54 : D 38 54 = true := by have h := D_step 36 53; rw [d_36_53, d_37_53, d_38_53] at h; exact h
private theorem d_39_54 : D 39 54 = true := by have h := D_step 37 53; rw [d_37_53, d_38_53, d_39_53] at h; exact h
private theorem d_40_54 : D 40 54 = true := by have h := D_step 38 53; rw [d_38_53, d_39_53, d_40_53] at h; exact h
private theorem d_41_54 : D 41 54 = true := by have h := D_step 39 53; rw [d_39_53, d_40_53, d_41_53] at h; exact h
private theorem d_42_54 : D 42 54 = false := by have h := D_step 40 53; rw [d_40_53, d_41_53, d_42_53] at h; exact h
private theorem d_43_54 : D 43 54 = false := by have h := D_step 41 53; rw [d_41_53, d_42_53, d_43_53] at h; exact h
private theorem d_44_54 : D 44 54 = true := by have h := D_step 42 53; rw [d_42_53, d_43_53, d_44_53] at h; exact h
private theorem d_45_54 : D 45 54 = false := by have h := D_step 43 53; rw [d_43_53, d_44_53, d_45_53] at h; exact h
private theorem d_0_55 : D 0 55 = true := D_zero 55
private theorem d_1_55 : D 1 55 = true := by simpa using D_one 54
private theorem d_2_55 : D 2 55 = false := by have h := D_step 0 54; rw [d_0_54, d_1_54, d_2_54] at h; exact h
private theorem d_3_55 : D 3 55 = true := by have h := D_step 1 54; rw [d_1_54, d_2_54, d_3_54] at h; exact h
private theorem d_4_55 : D 4 55 = true := by have h := D_step 2 54; rw [d_2_54, d_3_54, d_4_54] at h; exact h
private theorem d_5_55 : D 5 55 = true := by have h := D_step 3 54; rw [d_3_54, d_4_54, d_5_54] at h; exact h
private theorem d_6_55 : D 6 55 = true := by have h := D_step 4 54; rw [d_4_54, d_5_54, d_6_54] at h; exact h
private theorem d_7_55 : D 7 55 = false := by have h := D_step 5 54; rw [d_5_54, d_6_54, d_7_54] at h; exact h
private theorem d_8_55 : D 8 55 = false := by have h := D_step 6 54; rw [d_6_54, d_7_54, d_8_54] at h; exact h
private theorem d_9_55 : D 9 55 = true := by have h := D_step 7 54; rw [d_7_54, d_8_54, d_9_54] at h; exact h
private theorem d_10_55 : D 10 55 = true := by have h := D_step 8 54; rw [d_8_54, d_9_54, d_10_54] at h; exact h
private theorem d_11_55 : D 11 55 = false := by have h := D_step 9 54; rw [d_9_54, d_10_54, d_11_54] at h; exact h
private theorem d_12_55 : D 12 55 = true := by have h := D_step 10 54; rw [d_10_54, d_11_54, d_12_54] at h; exact h
private theorem d_13_55 : D 13 55 = false := by have h := D_step 11 54; rw [d_11_54, d_12_54, d_13_54] at h; exact h
private theorem d_14_55 : D 14 55 = false := by have h := D_step 12 54; rw [d_12_54, d_13_54, d_14_54] at h; exact h
private theorem d_15_55 : D 15 55 = true := by have h := D_step 13 54; rw [d_13_54, d_14_54, d_15_54] at h; exact h
private theorem d_16_55 : D 16 55 = true := by have h := D_step 14 54; rw [d_14_54, d_15_54, d_16_54] at h; exact h
private theorem d_17_55 : D 17 55 = true := by have h := D_step 15 54; rw [d_15_54, d_16_54, d_17_54] at h; exact h
private theorem d_18_55 : D 18 55 = false := by have h := D_step 16 54; rw [d_16_54, d_17_54, d_18_54] at h; exact h
private theorem d_19_55 : D 19 55 = true := by have h := D_step 17 54; rw [d_17_54, d_18_54, d_19_54] at h; exact h
private theorem d_20_55 : D 20 55 = false := by have h := D_step 18 54; rw [d_18_54, d_19_54, d_20_54] at h; exact h
private theorem d_21_55 : D 21 55 = false := by have h := D_step 19 54; rw [d_19_54, d_20_54, d_21_54] at h; exact h
private theorem d_22_55 : D 22 55 = true := by have h := D_step 20 54; rw [d_20_54, d_21_54, d_22_54] at h; exact h
private theorem d_23_55 : D 23 55 = false := by have h := D_step 21 54; rw [d_21_54, d_22_54, d_23_54] at h; exact h
private theorem d_24_55 : D 24 55 = true := by have h := D_step 22 54; rw [d_22_54, d_23_54, d_24_54] at h; exact h
private theorem d_25_55 : D 25 55 = true := by have h := D_step 23 54; rw [d_23_54, d_24_54, d_25_54] at h; exact h
private theorem d_26_55 : D 26 55 = true := by have h := D_step 24 54; rw [d_24_54, d_25_54, d_26_54] at h; exact h
private theorem d_27_55 : D 27 55 = true := by have h := D_step 25 54; rw [d_25_54, d_26_54, d_27_54] at h; exact h
private theorem d_28_55 : D 28 55 = false := by have h := D_step 26 54; rw [d_26_54, d_27_54, d_28_54] at h; exact h
private theorem d_29_55 : D 29 55 = false := by have h := D_step 27 54; rw [d_27_54, d_28_54, d_29_54] at h; exact h
private theorem d_30_55 : D 30 55 = true := by have h := D_step 28 54; rw [d_28_54, d_29_54, d_30_54] at h; exact h
private theorem d_31_55 : D 31 55 = false := by have h := D_step 29 54; rw [d_29_54, d_30_54, d_31_54] at h; exact h
private theorem d_32_55 : D 32 55 = false := by have h := D_step 30 54; rw [d_30_54, d_31_54, d_32_54] at h; exact h
private theorem d_33_55 : D 33 55 = true := by have h := D_step 31 54; rw [d_31_54, d_32_54, d_33_54] at h; exact h
private theorem d_34_55 : D 34 55 = false := by have h := D_step 32 54; rw [d_32_54, d_33_54, d_34_54] at h; exact h
private theorem d_35_55 : D 35 55 = true := by have h := D_step 33 54; rw [d_33_54, d_34_54, d_35_54] at h; exact h
private theorem d_36_55 : D 36 55 = true := by have h := D_step 34 54; rw [d_34_54, d_35_54, d_36_54] at h; exact h
private theorem d_37_55 : D 37 55 = true := by have h := D_step 35 54; rw [d_35_54, d_36_54, d_37_54] at h; exact h
private theorem d_38_55 : D 38 55 = true := by have h := D_step 36 54; rw [d_36_54, d_37_54, d_38_54] at h; exact h
private theorem d_39_55 : D 39 55 = true := by have h := D_step 37 54; rw [d_37_54, d_38_54, d_39_54] at h; exact h
private theorem d_40_55 : D 40 55 = false := by have h := D_step 38 54; rw [d_38_54, d_39_54, d_40_54] at h; exact h
private theorem d_41_55 : D 41 55 = false := by have h := D_step 39 54; rw [d_39_54, d_40_54, d_41_54] at h; exact h
private theorem d_42_55 : D 42 55 = false := by have h := D_step 40 54; rw [d_40_54, d_41_54, d_42_54] at h; exact h
private theorem d_43_55 : D 43 55 = true := by have h := D_step 41 54; rw [d_41_54, d_42_54, d_43_54] at h; exact h
private theorem d_44_55 : D 44 55 = true := by have h := D_step 42 54; rw [d_42_54, d_43_54, d_44_54] at h; exact h
private theorem d_45_55 : D 45 55 = true := by have h := D_step 43 54; rw [d_43_54, d_44_54, d_45_54] at h; exact h
private theorem d_0_56 : D 0 56 = true := D_zero 56
private theorem d_1_56 : D 1 56 = true := by simpa using D_one 55
private theorem d_2_56 : D 2 56 = false := by have h := D_step 0 55; rw [d_0_55, d_1_55, d_2_55] at h; exact h
private theorem d_3_56 : D 3 56 = false := by have h := D_step 1 55; rw [d_1_55, d_2_55, d_3_55] at h; exact h
private theorem d_4_56 : D 4 56 = true := by have h := D_step 2 55; rw [d_2_55, d_3_55, d_4_55] at h; exact h
private theorem d_5_56 : D 5 56 = false := by have h := D_step 3 55; rw [d_3_55, d_4_55, d_5_55] at h; exact h
private theorem d_6_56 : D 6 56 = false := by have h := D_step 4 55; rw [d_4_55, d_5_55, d_6_55] at h; exact h
private theorem d_7_56 : D 7 56 = false := by have h := D_step 5 55; rw [d_5_55, d_6_55, d_7_55] at h; exact h
private theorem d_8_56 : D 8 56 = true := by have h := D_step 6 55; rw [d_6_55, d_7_55, d_8_55] at h; exact h
private theorem d_9_56 : D 9 56 = true := by have h := D_step 7 55; rw [d_7_55, d_8_55, d_9_55] at h; exact h
private theorem d_10_56 : D 10 56 = true := by have h := D_step 8 55; rw [d_8_55, d_9_55, d_10_55] at h; exact h
private theorem d_11_56 : D 11 56 = false := by have h := D_step 9 55; rw [d_9_55, d_10_55, d_11_55] at h; exact h
private theorem d_12_56 : D 12 56 = false := by have h := D_step 10 55; rw [d_10_55, d_11_55, d_12_55] at h; exact h
private theorem d_13_56 : D 13 56 = true := by have h := D_step 11 55; rw [d_11_55, d_12_55, d_13_55] at h; exact h
private theorem d_14_56 : D 14 56 = true := by have h := D_step 12 55; rw [d_12_55, d_13_55, d_14_55] at h; exact h
private theorem d_15_56 : D 15 56 = true := by have h := D_step 13 55; rw [d_13_55, d_14_55, d_15_55] at h; exact h
private theorem d_16_56 : D 16 56 = true := by have h := D_step 14 55; rw [d_14_55, d_15_55, d_16_55] at h; exact h
private theorem d_17_56 : D 17 56 = false := by have h := D_step 15 55; rw [d_15_55, d_16_55, d_17_55] at h; exact h
private theorem d_18_56 : D 18 56 = false := by have h := D_step 16 55; rw [d_16_55, d_17_55, d_18_55] at h; exact h
private theorem d_19_56 : D 19 56 = false := by have h := D_step 17 55; rw [d_17_55, d_18_55, d_19_55] at h; exact h
private theorem d_20_56 : D 20 56 = true := by have h := D_step 18 55; rw [d_18_55, d_19_55, d_20_55] at h; exact h
private theorem d_21_56 : D 21 56 = true := by have h := D_step 19 55; rw [d_19_55, d_20_55, d_21_55] at h; exact h
private theorem d_22_56 : D 22 56 = true := by have h := D_step 20 55; rw [d_20_55, d_21_55, d_22_55] at h; exact h
private theorem d_23_56 : D 23 56 = true := by have h := D_step 21 55; rw [d_21_55, d_22_55, d_23_55] at h; exact h
private theorem d_24_56 : D 24 56 = false := by have h := D_step 22 55; rw [d_22_55, d_23_55, d_24_55] at h; exact h
private theorem d_25_56 : D 25 56 = true := by have h := D_step 23 55; rw [d_23_55, d_24_55, d_25_55] at h; exact h
private theorem d_26_56 : D 26 56 = false := by have h := D_step 24 55; rw [d_24_55, d_25_55, d_26_55] at h; exact h
private theorem d_27_56 : D 27 56 = false := by have h := D_step 25 55; rw [d_25_55, d_26_55, d_27_55] at h; exact h
private theorem d_28_56 : D 28 56 = false := by have h := D_step 26 55; rw [d_26_55, d_27_55, d_28_55] at h; exact h
private theorem d_29_56 : D 29 56 = true := by have h := D_step 27 55; rw [d_27_55, d_28_55, d_29_55] at h; exact h
private theorem d_30_56 : D 30 56 = true := by have h := D_step 28 55; rw [d_28_55, d_29_55, d_30_55] at h; exact h
private theorem d_31_56 : D 31 56 = true := by have h := D_step 29 55; rw [d_29_55, d_30_55, d_31_55] at h; exact h
private theorem d_32_56 : D 32 56 = true := by have h := D_step 30 55; rw [d_30_55, d_31_55, d_32_55] at h; exact h
private theorem d_33_56 : D 33 56 = true := by have h := D_step 31 55; rw [d_31_55, d_32_55, d_33_55] at h; exact h
private theorem d_34_56 : D 34 56 = true := by have h := D_step 32 55; rw [d_32_55, d_33_55, d_34_55] at h; exact h
private theorem d_35_56 : D 35 56 = false := by have h := D_step 33 55; rw [d_33_55, d_34_55, d_35_55] at h; exact h
private theorem d_36_56 : D 36 56 = true := by have h := D_step 34 55; rw [d_34_55, d_35_55, d_36_55] at h; exact h
private theorem d_37_56 : D 37 56 = false := by have h := D_step 35 55; rw [d_35_55, d_36_55, d_37_55] at h; exact h
private theorem d_38_56 : D 38 56 = false := by have h := D_step 36 55; rw [d_36_55, d_37_55, d_38_55] at h; exact h
private theorem d_39_56 : D 39 56 = false := by have h := D_step 37 55; rw [d_37_55, d_38_55, d_39_55] at h; exact h
private theorem d_40_56 : D 40 56 = false := by have h := D_step 38 55; rw [d_38_55, d_39_55, d_40_55] at h; exact h
private theorem d_41_56 : D 41 56 = true := by have h := D_step 39 55; rw [d_39_55, d_40_55, d_41_55] at h; exact h
private theorem d_42_56 : D 42 56 = false := by have h := D_step 40 55; rw [d_40_55, d_41_55, d_42_55] at h; exact h
private theorem d_43_56 : D 43 56 = true := by have h := D_step 41 55; rw [d_41_55, d_42_55, d_43_55] at h; exact h
private theorem d_44_56 : D 44 56 = true := by have h := D_step 42 55; rw [d_42_55, d_43_55, d_44_55] at h; exact h
private theorem d_45_56 : D 45 56 = false := by have h := D_step 43 55; rw [d_43_55, d_44_55, d_45_55] at h; exact h
private theorem d_0_57 : D 0 57 = true := D_zero 57
private theorem d_1_57 : D 1 57 = true := by simpa using D_one 56
private theorem d_2_57 : D 2 57 = false := by have h := D_step 0 56; rw [d_0_56, d_1_56, d_2_56] at h; exact h
private theorem d_3_57 : D 3 57 = true := by have h := D_step 1 56; rw [d_1_56, d_2_56, d_3_56] at h; exact h
private theorem d_4_57 : D 4 57 = true := by have h := D_step 2 56; rw [d_2_56, d_3_56, d_4_56] at h; exact h
private theorem d_5_57 : D 5 57 = true := by have h := D_step 3 56; rw [d_3_56, d_4_56, d_5_56] at h; exact h
private theorem d_6_57 : D 6 57 = true := by have h := D_step 4 56; rw [d_4_56, d_5_56, d_6_56] at h; exact h
private theorem d_7_57 : D 7 57 = false := by have h := D_step 5 56; rw [d_5_56, d_6_56, d_7_56] at h; exact h
private theorem d_8_57 : D 8 57 = true := by have h := D_step 6 56; rw [d_6_56, d_7_56, d_8_56] at h; exact h
private theorem d_9_57 : D 9 57 = true := by have h := D_step 7 56; rw [d_7_56, d_8_56, d_9_56] at h; exact h
private theorem d_10_57 : D 10 57 = false := by have h := D_step 8 56; rw [d_8_56, d_9_56, d_10_56] at h; exact h
private theorem d_11_57 : D 11 57 = false := by have h := D_step 9 56; rw [d_9_56, d_10_56, d_11_56] at h; exact h
private theorem d_12_57 : D 12 57 = true := by have h := D_step 10 56; rw [d_10_56, d_11_56, d_12_56] at h; exact h
private theorem d_13_57 : D 13 57 = true := by have h := D_step 11 56; rw [d_11_56, d_12_56, d_13_56] at h; exact h
private theorem d_14_57 : D 14 57 = true := by have h := D_step 12 56; rw [d_12_56, d_13_56, d_14_56] at h; exact h
private theorem d_15_57 : D 15 57 = false := by have h := D_step 13 56; rw [d_13_56, d_14_56, d_15_56] at h; exact h
private theorem d_16_57 : D 16 57 = false := by have h := D_step 14 56; rw [d_14_56, d_15_56, d_16_56] at h; exact h
private theorem d_17_57 : D 17 57 = false := by have h := D_step 15 56; rw [d_15_56, d_16_56, d_17_56] at h; exact h
private theorem d_18_57 : D 18 57 = true := by have h := D_step 16 56; rw [d_16_56, d_17_56, d_18_56] at h; exact h
private theorem d_19_57 : D 19 57 = false := by have h := D_step 17 56; rw [d_17_56, d_18_56, d_19_56] at h; exact h
private theorem d_20_57 : D 20 57 = true := by have h := D_step 18 56; rw [d_18_56, d_19_56, d_20_56] at h; exact h
private theorem d_21_57 : D 21 57 = true := by have h := D_step 19 56; rw [d_19_56, d_20_56, d_21_56] at h; exact h
private theorem d_22_57 : D 22 57 = false := by have h := D_step 20 56; rw [d_20_56, d_21_56, d_22_56] at h; exact h
private theorem d_23_57 : D 23 57 = false := by have h := D_step 21 56; rw [d_21_56, d_22_56, d_23_56] at h; exact h
private theorem d_24_57 : D 24 57 = false := by have h := D_step 22 56; rw [d_22_56, d_23_56, d_24_56] at h; exact h
private theorem d_25_57 : D 25 57 = false := by have h := D_step 23 56; rw [d_23_56, d_24_56, d_25_56] at h; exact h
private theorem d_26_57 : D 26 57 = true := by have h := D_step 24 56; rw [d_24_56, d_25_56, d_26_56] at h; exact h
private theorem d_27_57 : D 27 57 = true := by have h := D_step 25 56; rw [d_25_56, d_26_56, d_27_56] at h; exact h
private theorem d_28_57 : D 28 57 = false := by have h := D_step 26 56; rw [d_26_56, d_27_56, d_28_56] at h; exact h
private theorem d_29_57 : D 29 57 = true := by have h := D_step 27 56; rw [d_27_56, d_28_56, d_29_56] at h; exact h
private theorem d_30_57 : D 30 57 = true := by have h := D_step 28 56; rw [d_28_56, d_29_56, d_30_56] at h; exact h
private theorem d_31_57 : D 31 57 = false := by have h := D_step 29 56; rw [d_29_56, d_30_56, d_31_56] at h; exact h
private theorem d_32_57 : D 32 57 = false := by have h := D_step 30 56; rw [d_30_56, d_31_56, d_32_56] at h; exact h
private theorem d_33_57 : D 33 57 = false := by have h := D_step 31 56; rw [d_31_56, d_32_56, d_33_56] at h; exact h
private theorem d_34_57 : D 34 57 = false := by have h := D_step 32 56; rw [d_32_56, d_33_56, d_34_56] at h; exact h
private theorem d_35_57 : D 35 57 = false := by have h := D_step 33 56; rw [d_33_56, d_34_56, d_35_56] at h; exact h
private theorem d_36_57 : D 36 57 = false := by have h := D_step 34 56; rw [d_34_56, d_35_56, d_36_56] at h; exact h
private theorem d_37_57 : D 37 57 = true := by have h := D_step 35 56; rw [d_35_56, d_36_56, d_37_56] at h; exact h
private theorem d_38_57 : D 38 57 = true := by have h := D_step 36 56; rw [d_36_56, d_37_56, d_38_56] at h; exact h
private theorem d_39_57 : D 39 57 = false := by have h := D_step 37 56; rw [d_37_56, d_38_56, d_39_56] at h; exact h
private theorem d_40_57 : D 40 57 = false := by have h := D_step 38 56; rw [d_38_56, d_39_56, d_40_56] at h; exact h
private theorem d_41_57 : D 41 57 = true := by have h := D_step 39 56; rw [d_39_56, d_40_56, d_41_56] at h; exact h
private theorem d_42_57 : D 42 57 = true := by have h := D_step 40 56; rw [d_40_56, d_41_56, d_42_56] at h; exact h
private theorem d_43_57 : D 43 57 = false := by have h := D_step 41 56; rw [d_41_56, d_42_56, d_43_56] at h; exact h
private theorem d_44_57 : D 44 57 = true := by have h := D_step 42 56; rw [d_42_56, d_43_56, d_44_56] at h; exact h
private theorem d_45_57 : D 45 57 = false := by have h := D_step 43 56; rw [d_43_56, d_44_56, d_45_56] at h; exact h
private theorem d_0_58 : D 0 58 = true := D_zero 58
private theorem d_1_58 : D 1 58 = true := by simpa using D_one 57
private theorem d_2_58 : D 2 58 = false := by have h := D_step 0 57; rw [d_0_57, d_1_57, d_2_57] at h; exact h
private theorem d_3_58 : D 3 58 = false := by have h := D_step 1 57; rw [d_1_57, d_2_57, d_3_57] at h; exact h
private theorem d_4_58 : D 4 58 = true := by have h := D_step 2 57; rw [d_2_57, d_3_57, d_4_57] at h; exact h
private theorem d_5_58 : D 5 58 = false := by have h := D_step 3 57; rw [d_3_57, d_4_57, d_5_57] at h; exact h
private theorem d_6_58 : D 6 58 = false := by have h := D_step 4 57; rw [d_4_57, d_5_57, d_6_57] at h; exact h
private theorem d_7_58 : D 7 58 = false := by have h := D_step 5 57; rw [d_5_57, d_6_57, d_7_57] at h; exact h
private theorem d_8_58 : D 8 58 = false := by have h := D_step 6 57; rw [d_6_57, d_7_57, d_8_57] at h; exact h
private theorem d_9_58 : D 9 58 = true := by have h := D_step 7 57; rw [d_7_57, d_8_57, d_9_57] at h; exact h
private theorem d_10_58 : D 10 58 = false := by have h := D_step 8 57; rw [d_8_57, d_9_57, d_10_57] at h; exact h
private theorem d_11_58 : D 11 58 = true := by have h := D_step 9 57; rw [d_9_57, d_10_57, d_11_57] at h; exact h
private theorem d_12_58 : D 12 58 = true := by have h := D_step 10 57; rw [d_10_57, d_11_57, d_12_57] at h; exact h
private theorem d_13_58 : D 13 58 = true := by have h := D_step 11 57; rw [d_11_57, d_12_57, d_13_57] at h; exact h
private theorem d_14_58 : D 14 58 = false := by have h := D_step 12 57; rw [d_12_57, d_13_57, d_14_57] at h; exact h
private theorem d_15_58 : D 15 58 = false := by have h := D_step 13 57; rw [d_13_57, d_14_57, d_15_57] at h; exact h
private theorem d_16_58 : D 16 58 = true := by have h := D_step 14 57; rw [d_14_57, d_15_57, d_16_57] at h; exact h
private theorem d_17_58 : D 17 58 = false := by have h := D_step 15 57; rw [d_15_57, d_16_57, d_17_57] at h; exact h
private theorem d_18_58 : D 18 58 = true := by have h := D_step 16 57; rw [d_16_57, d_17_57, d_18_57] at h; exact h
private theorem d_19_58 : D 19 58 = true := by have h := D_step 17 57; rw [d_17_57, d_18_57, d_19_57] at h; exact h
private theorem d_20_58 : D 20 58 = false := by have h := D_step 18 57; rw [d_18_57, d_19_57, d_20_57] at h; exact h
private theorem d_21_58 : D 21 58 = true := by have h := D_step 19 57; rw [d_19_57, d_20_57, d_21_57] at h; exact h
private theorem d_22_58 : D 22 58 = false := by have h := D_step 20 57; rw [d_20_57, d_21_57, d_22_57] at h; exact h
private theorem d_23_58 : D 23 58 = true := by have h := D_step 21 57; rw [d_21_57, d_22_57, d_23_57] at h; exact h
private theorem d_24_58 : D 24 58 = false := by have h := D_step 22 57; rw [d_22_57, d_23_57, d_24_57] at h; exact h
private theorem d_25_58 : D 25 58 = false := by have h := D_step 23 57; rw [d_23_57, d_24_57, d_25_57] at h; exact h
private theorem d_26_58 : D 26 58 = true := by have h := D_step 24 57; rw [d_24_57, d_25_57, d_26_57] at h; exact h
private theorem d_27_58 : D 27 58 = true := by have h := D_step 25 57; rw [d_25_57, d_26_57, d_27_57] at h; exact h
private theorem d_28_58 : D 28 58 = false := by have h := D_step 26 57; rw [d_26_57, d_27_57, d_28_57] at h; exact h
private theorem d_29_58 : D 29 58 = false := by have h := D_step 27 57; rw [d_27_57, d_28_57, d_29_57] at h; exact h
private theorem d_30_58 : D 30 58 = true := by have h := D_step 28 57; rw [d_28_57, d_29_57, d_30_57] at h; exact h
private theorem d_31_58 : D 31 58 = false := by have h := D_step 29 57; rw [d_29_57, d_30_57, d_31_57] at h; exact h
private theorem d_32_58 : D 32 58 = true := by have h := D_step 30 57; rw [d_30_57, d_31_57, d_32_57] at h; exact h
private theorem d_33_58 : D 33 58 = false := by have h := D_step 31 57; rw [d_31_57, d_32_57, d_33_57] at h; exact h
private theorem d_34_58 : D 34 58 = false := by have h := D_step 32 57; rw [d_32_57, d_33_57, d_34_57] at h; exact h
private theorem d_35_58 : D 35 58 = false := by have h := D_step 33 57; rw [d_33_57, d_34_57, d_35_57] at h; exact h
private theorem d_36_58 : D 36 58 = false := by have h := D_step 34 57; rw [d_34_57, d_35_57, d_36_57] at h; exact h
private theorem d_37_58 : D 37 58 = true := by have h := D_step 35 57; rw [d_35_57, d_36_57, d_37_57] at h; exact h
private theorem d_38_58 : D 38 58 = true := by have h := D_step 36 57; rw [d_36_57, d_37_57, d_38_57] at h; exact h
private theorem d_39_58 : D 39 58 = false := by have h := D_step 37 57; rw [d_37_57, d_38_57, d_39_57] at h; exact h
private theorem d_40_58 : D 40 58 = true := by have h := D_step 38 57; rw [d_38_57, d_39_57, d_40_57] at h; exact h
private theorem d_41_58 : D 41 58 = true := by have h := D_step 39 57; rw [d_39_57, d_40_57, d_41_57] at h; exact h
private theorem d_42_58 : D 42 58 = true := by have h := D_step 40 57; rw [d_40_57, d_41_57, d_42_57] at h; exact h
private theorem d_43_58 : D 43 58 = false := by have h := D_step 41 57; rw [d_41_57, d_42_57, d_43_57] at h; exact h
private theorem d_44_58 : D 44 58 = false := by have h := D_step 42 57; rw [d_42_57, d_43_57, d_44_57] at h; exact h
private theorem d_45_58 : D 45 58 = true := by have h := D_step 43 57; rw [d_43_57, d_44_57, d_45_57] at h; exact h
private theorem d_0_59 : D 0 59 = true := D_zero 59
private theorem d_1_59 : D 1 59 = true := by simpa using D_one 58
private theorem d_2_59 : D 2 59 = false := by have h := D_step 0 58; rw [d_0_58, d_1_58, d_2_58] at h; exact h
private theorem d_3_59 : D 3 59 = true := by have h := D_step 1 58; rw [d_1_58, d_2_58, d_3_58] at h; exact h
private theorem d_4_59 : D 4 59 = true := by have h := D_step 2 58; rw [d_2_58, d_3_58, d_4_58] at h; exact h
private theorem d_5_59 : D 5 59 = true := by have h := D_step 3 58; rw [d_3_58, d_4_58, d_5_58] at h; exact h
private theorem d_6_59 : D 6 59 = true := by have h := D_step 4 58; rw [d_4_58, d_5_58, d_6_58] at h; exact h
private theorem d_7_59 : D 7 59 = false := by have h := D_step 5 58; rw [d_5_58, d_6_58, d_7_58] at h; exact h
private theorem d_8_59 : D 8 59 = false := by have h := D_step 6 58; rw [d_6_58, d_7_58, d_8_58] at h; exact h
private theorem d_9_59 : D 9 59 = true := by have h := D_step 7 58; rw [d_7_58, d_8_58, d_9_58] at h; exact h
private theorem d_10_59 : D 10 59 = true := by have h := D_step 8 58; rw [d_8_58, d_9_58, d_10_58] at h; exact h
private theorem d_11_59 : D 11 59 = false := by have h := D_step 9 58; rw [d_9_58, d_10_58, d_11_58] at h; exact h
private theorem d_12_59 : D 12 59 = true := by have h := D_step 10 58; rw [d_10_58, d_11_58, d_12_58] at h; exact h
private theorem d_13_59 : D 13 59 = false := by have h := D_step 11 58; rw [d_11_58, d_12_58, d_13_58] at h; exact h
private theorem d_14_59 : D 14 59 = false := by have h := D_step 12 58; rw [d_12_58, d_13_58, d_14_58] at h; exact h
private theorem d_15_59 : D 15 59 = true := by have h := D_step 13 58; rw [d_13_58, d_14_58, d_15_58] at h; exact h
private theorem d_16_59 : D 16 59 = true := by have h := D_step 14 58; rw [d_14_58, d_15_58, d_16_58] at h; exact h
private theorem d_17_59 : D 17 59 = true := by have h := D_step 15 58; rw [d_15_58, d_16_58, d_17_58] at h; exact h
private theorem d_18_59 : D 18 59 = false := by have h := D_step 16 58; rw [d_16_58, d_17_58, d_18_58] at h; exact h
private theorem d_19_59 : D 19 59 = true := by have h := D_step 17 58; rw [d_17_58, d_18_58, d_19_58] at h; exact h
private theorem d_20_59 : D 20 59 = false := by have h := D_step 18 58; rw [d_18_58, d_19_58, d_20_58] at h; exact h
private theorem d_21_59 : D 21 59 = false := by have h := D_step 19 58; rw [d_19_58, d_20_58, d_21_58] at h; exact h
private theorem d_22_59 : D 22 59 = true := by have h := D_step 20 58; rw [d_20_58, d_21_58, d_22_58] at h; exact h
private theorem d_23_59 : D 23 59 = false := by have h := D_step 21 58; rw [d_21_58, d_22_58, d_23_58] at h; exact h
private theorem d_24_59 : D 24 59 = true := by have h := D_step 22 58; rw [d_22_58, d_23_58, d_24_58] at h; exact h
private theorem d_25_59 : D 25 59 = true := by have h := D_step 23 58; rw [d_23_58, d_24_58, d_25_58] at h; exact h
private theorem d_26_59 : D 26 59 = true := by have h := D_step 24 58; rw [d_24_58, d_25_58, d_26_58] at h; exact h
private theorem d_27_59 : D 27 59 = true := by have h := D_step 25 58; rw [d_25_58, d_26_58, d_27_58] at h; exact h
private theorem d_28_59 : D 28 59 = false := by have h := D_step 26 58; rw [d_26_58, d_27_58, d_28_58] at h; exact h
private theorem d_29_59 : D 29 59 = true := by have h := D_step 27 58; rw [d_27_58, d_28_58, d_29_58] at h; exact h
private theorem d_30_59 : D 30 59 = true := by have h := D_step 28 58; rw [d_28_58, d_29_58, d_30_58] at h; exact h
private theorem d_31_59 : D 31 59 = true := by have h := D_step 29 58; rw [d_29_58, d_30_58, d_31_58] at h; exact h
private theorem d_32_59 : D 32 59 = false := by have h := D_step 30 58; rw [d_30_58, d_31_58, d_32_58] at h; exact h
private theorem d_33_59 : D 33 59 = true := by have h := D_step 31 58; rw [d_31_58, d_32_58, d_33_58] at h; exact h
private theorem d_34_59 : D 34 59 = true := by have h := D_step 32 58; rw [d_32_58, d_33_58, d_34_58] at h; exact h
private theorem d_35_59 : D 35 59 = false := by have h := D_step 33 58; rw [d_33_58, d_34_58, d_35_58] at h; exact h
private theorem d_36_59 : D 36 59 = false := by have h := D_step 34 58; rw [d_34_58, d_35_58, d_36_58] at h; exact h
private theorem d_37_59 : D 37 59 = true := by have h := D_step 35 58; rw [d_35_58, d_36_58, d_37_58] at h; exact h
private theorem d_38_59 : D 38 59 = true := by have h := D_step 36 58; rw [d_36_58, d_37_58, d_38_58] at h; exact h
private theorem d_39_59 : D 39 59 = false := by have h := D_step 37 58; rw [d_37_58, d_38_58, d_39_58] at h; exact h
private theorem d_40_59 : D 40 59 = false := by have h := D_step 38 58; rw [d_38_58, d_39_58, d_40_58] at h; exact h
private theorem d_41_59 : D 41 59 = true := by have h := D_step 39 58; rw [d_39_58, d_40_58, d_41_58] at h; exact h
private theorem d_42_59 : D 42 59 = false := by have h := D_step 40 58; rw [d_40_58, d_41_58, d_42_58] at h; exact h
private theorem d_43_59 : D 43 59 = false := by have h := D_step 41 58; rw [d_41_58, d_42_58, d_43_58] at h; exact h
private theorem d_44_59 : D 44 59 = true := by have h := D_step 42 58; rw [d_42_58, d_43_58, d_44_58] at h; exact h
private theorem d_45_59 : D 45 59 = true := by have h := D_step 43 58; rw [d_43_58, d_44_58, d_45_58] at h; exact h
private theorem d_0_60 : D 0 60 = true := D_zero 60
private theorem d_1_60 : D 1 60 = true := by simpa using D_one 59
private theorem d_2_60 : D 2 60 = false := by have h := D_step 0 59; rw [d_0_59, d_1_59, d_2_59] at h; exact h
private theorem d_3_60 : D 3 60 = false := by have h := D_step 1 59; rw [d_1_59, d_2_59, d_3_59] at h; exact h
private theorem d_4_60 : D 4 60 = true := by have h := D_step 2 59; rw [d_2_59, d_3_59, d_4_59] at h; exact h
private theorem d_5_60 : D 5 60 = false := by have h := D_step 3 59; rw [d_3_59, d_4_59, d_5_59] at h; exact h
private theorem d_6_60 : D 6 60 = false := by have h := D_step 4 59; rw [d_4_59, d_5_59, d_6_59] at h; exact h
private theorem d_7_60 : D 7 60 = false := by have h := D_step 5 59; rw [d_5_59, d_6_59, d_7_59] at h; exact h
private theorem d_8_60 : D 8 60 = true := by have h := D_step 6 59; rw [d_6_59, d_7_59, d_8_59] at h; exact h
private theorem d_9_60 : D 9 60 = true := by have h := D_step 7 59; rw [d_7_59, d_8_59, d_9_59] at h; exact h
private theorem d_10_60 : D 10 60 = true := by have h := D_step 8 59; rw [d_8_59, d_9_59, d_10_59] at h; exact h
private theorem d_11_60 : D 11 60 = false := by have h := D_step 9 59; rw [d_9_59, d_10_59, d_11_59] at h; exact h
private theorem d_12_60 : D 12 60 = false := by have h := D_step 10 59; rw [d_10_59, d_11_59, d_12_59] at h; exact h
private theorem d_13_60 : D 13 60 = true := by have h := D_step 11 59; rw [d_11_59, d_12_59, d_13_59] at h; exact h
private theorem d_14_60 : D 14 60 = true := by have h := D_step 12 59; rw [d_12_59, d_13_59, d_14_59] at h; exact h
private theorem d_15_60 : D 15 60 = true := by have h := D_step 13 59; rw [d_13_59, d_14_59, d_15_59] at h; exact h
private theorem d_16_60 : D 16 60 = true := by have h := D_step 14 59; rw [d_14_59, d_15_59, d_16_59] at h; exact h
private theorem d_17_60 : D 17 60 = false := by have h := D_step 15 59; rw [d_15_59, d_16_59, d_17_59] at h; exact h
private theorem d_18_60 : D 18 60 = false := by have h := D_step 16 59; rw [d_16_59, d_17_59, d_18_59] at h; exact h
private theorem d_19_60 : D 19 60 = false := by have h := D_step 17 59; rw [d_17_59, d_18_59, d_19_59] at h; exact h
private theorem d_20_60 : D 20 60 = true := by have h := D_step 18 59; rw [d_18_59, d_19_59, d_20_59] at h; exact h
private theorem d_21_60 : D 21 60 = true := by have h := D_step 19 59; rw [d_19_59, d_20_59, d_21_59] at h; exact h
private theorem d_22_60 : D 22 60 = true := by have h := D_step 20 59; rw [d_20_59, d_21_59, d_22_59] at h; exact h
private theorem d_23_60 : D 23 60 = true := by have h := D_step 21 59; rw [d_21_59, d_22_59, d_23_59] at h; exact h
private theorem d_24_60 : D 24 60 = false := by have h := D_step 22 59; rw [d_22_59, d_23_59, d_24_59] at h; exact h
private theorem d_25_60 : D 25 60 = true := by have h := D_step 23 59; rw [d_23_59, d_24_59, d_25_59] at h; exact h
private theorem d_26_60 : D 26 60 = false := by have h := D_step 24 59; rw [d_24_59, d_25_59, d_26_59] at h; exact h
private theorem d_27_60 : D 27 60 = false := by have h := D_step 25 59; rw [d_25_59, d_26_59, d_27_59] at h; exact h
private theorem d_28_60 : D 28 60 = false := by have h := D_step 26 59; rw [d_26_59, d_27_59, d_28_59] at h; exact h
private theorem d_29_60 : D 29 60 = false := by have h := D_step 27 59; rw [d_27_59, d_28_59, d_29_59] at h; exact h
private theorem d_30_60 : D 30 60 = true := by have h := D_step 28 59; rw [d_28_59, d_29_59, d_30_59] at h; exact h
private theorem d_31_60 : D 31 60 = false := by have h := D_step 29 59; rw [d_29_59, d_30_59, d_31_59] at h; exact h
private theorem d_32_60 : D 32 60 = false := by have h := D_step 30 59; rw [d_30_59, d_31_59, d_32_59] at h; exact h
private theorem d_33_60 : D 33 60 = false := by have h := D_step 31 59; rw [d_31_59, d_32_59, d_33_59] at h; exact h
private theorem d_34_60 : D 34 60 = true := by have h := D_step 32 59; rw [d_32_59, d_33_59, d_34_59] at h; exact h
private theorem d_35_60 : D 35 60 = false := by have h := D_step 33 59; rw [d_33_59, d_34_59, d_35_59] at h; exact h
private theorem d_36_60 : D 36 60 = true := by have h := D_step 34 59; rw [d_34_59, d_35_59, d_36_59] at h; exact h
private theorem d_37_60 : D 37 60 = true := by have h := D_step 35 59; rw [d_35_59, d_36_59, d_37_59] at h; exact h
private theorem d_38_60 : D 38 60 = true := by have h := D_step 36 59; rw [d_36_59, d_37_59, d_38_59] at h; exact h
private theorem d_39_60 : D 39 60 = false := by have h := D_step 37 59; rw [d_37_59, d_38_59, d_39_59] at h; exact h
private theorem d_40_60 : D 40 60 = true := by have h := D_step 38 59; rw [d_38_59, d_39_59, d_40_59] at h; exact h
private theorem d_41_60 : D 41 60 = true := by have h := D_step 39 59; rw [d_39_59, d_40_59, d_41_59] at h; exact h
private theorem d_42_60 : D 42 60 = true := by have h := D_step 40 59; rw [d_40_59, d_41_59, d_42_59] at h; exact h
private theorem d_43_60 : D 43 60 = true := by have h := D_step 41 59; rw [d_41_59, d_42_59, d_43_59] at h; exact h
private theorem d_44_60 : D 44 60 = true := by have h := D_step 42 59; rw [d_42_59, d_43_59, d_44_59] at h; exact h
private theorem d_45_60 : D 45 60 = true := by have h := D_step 43 59; rw [d_43_59, d_44_59, d_45_59] at h; exact h
private theorem d_0_61 : D 0 61 = true := D_zero 61
private theorem d_1_61 : D 1 61 = true := by simpa using D_one 60
private theorem d_2_61 : D 2 61 = false := by have h := D_step 0 60; rw [d_0_60, d_1_60, d_2_60] at h; exact h
private theorem d_3_61 : D 3 61 = true := by have h := D_step 1 60; rw [d_1_60, d_2_60, d_3_60] at h; exact h
private theorem d_4_61 : D 4 61 = true := by have h := D_step 2 60; rw [d_2_60, d_3_60, d_4_60] at h; exact h
private theorem d_5_61 : D 5 61 = true := by have h := D_step 3 60; rw [d_3_60, d_4_60, d_5_60] at h; exact h
private theorem d_6_61 : D 6 61 = true := by have h := D_step 4 60; rw [d_4_60, d_5_60, d_6_60] at h; exact h
private theorem d_7_61 : D 7 61 = false := by have h := D_step 5 60; rw [d_5_60, d_6_60, d_7_60] at h; exact h
private theorem d_8_61 : D 8 61 = true := by have h := D_step 6 60; rw [d_6_60, d_7_60, d_8_60] at h; exact h
private theorem d_9_61 : D 9 61 = true := by have h := D_step 7 60; rw [d_7_60, d_8_60, d_9_60] at h; exact h
private theorem d_10_61 : D 10 61 = false := by have h := D_step 8 60; rw [d_8_60, d_9_60, d_10_60] at h; exact h
private theorem d_11_61 : D 11 61 = false := by have h := D_step 9 60; rw [d_9_60, d_10_60, d_11_60] at h; exact h
private theorem d_12_61 : D 12 61 = true := by have h := D_step 10 60; rw [d_10_60, d_11_60, d_12_60] at h; exact h
private theorem d_13_61 : D 13 61 = true := by have h := D_step 11 60; rw [d_11_60, d_12_60, d_13_60] at h; exact h
private theorem d_14_61 : D 14 61 = true := by have h := D_step 12 60; rw [d_12_60, d_13_60, d_14_60] at h; exact h
private theorem d_15_61 : D 15 61 = false := by have h := D_step 13 60; rw [d_13_60, d_14_60, d_15_60] at h; exact h
private theorem d_16_61 : D 16 61 = false := by have h := D_step 14 60; rw [d_14_60, d_15_60, d_16_60] at h; exact h
private theorem d_17_61 : D 17 61 = false := by have h := D_step 15 60; rw [d_15_60, d_16_60, d_17_60] at h; exact h
private theorem d_18_61 : D 18 61 = true := by have h := D_step 16 60; rw [d_16_60, d_17_60, d_18_60] at h; exact h
private theorem d_19_61 : D 19 61 = false := by have h := D_step 17 60; rw [d_17_60, d_18_60, d_19_60] at h; exact h
private theorem d_20_61 : D 20 61 = true := by have h := D_step 18 60; rw [d_18_60, d_19_60, d_20_60] at h; exact h
private theorem d_21_61 : D 21 61 = true := by have h := D_step 19 60; rw [d_19_60, d_20_60, d_21_60] at h; exact h
private theorem d_22_61 : D 22 61 = false := by have h := D_step 20 60; rw [d_20_60, d_21_60, d_22_60] at h; exact h
private theorem d_23_61 : D 23 61 = false := by have h := D_step 21 60; rw [d_21_60, d_22_60, d_23_60] at h; exact h
private theorem d_24_61 : D 24 61 = false := by have h := D_step 22 60; rw [d_22_60, d_23_60, d_24_60] at h; exact h
private theorem d_25_61 : D 25 61 = false := by have h := D_step 23 60; rw [d_23_60, d_24_60, d_25_60] at h; exact h
private theorem d_26_61 : D 26 61 = true := by have h := D_step 24 60; rw [d_24_60, d_25_60, d_26_60] at h; exact h
private theorem d_27_61 : D 27 61 = true := by have h := D_step 25 60; rw [d_25_60, d_26_60, d_27_60] at h; exact h
private theorem d_28_61 : D 28 61 = false := by have h := D_step 26 60; rw [d_26_60, d_27_60, d_28_60] at h; exact h
private theorem d_29_61 : D 29 61 = false := by have h := D_step 27 60; rw [d_27_60, d_28_60, d_29_60] at h; exact h
private theorem d_30_61 : D 30 61 = true := by have h := D_step 28 60; rw [d_28_60, d_29_60, d_30_60] at h; exact h
private theorem d_31_61 : D 31 61 = true := by have h := D_step 29 60; rw [d_29_60, d_30_60, d_31_60] at h; exact h
private theorem d_32_61 : D 32 61 = true := by have h := D_step 30 60; rw [d_30_60, d_31_60, d_32_60] at h; exact h
private theorem d_33_61 : D 33 61 = false := by have h := D_step 31 60; rw [d_31_60, d_32_60, d_33_60] at h; exact h
private theorem d_34_61 : D 34 61 = true := by have h := D_step 32 60; rw [d_32_60, d_33_60, d_34_60] at h; exact h
private theorem d_35_61 : D 35 61 = true := by have h := D_step 33 60; rw [d_33_60, d_34_60, d_35_60] at h; exact h
private theorem d_36_61 : D 36 61 = false := by have h := D_step 34 60; rw [d_34_60, d_35_60, d_36_60] at h; exact h
private theorem d_37_61 : D 37 61 = true := by have h := D_step 35 60; rw [d_35_60, d_36_60, d_37_60] at h; exact h
private theorem d_38_61 : D 38 61 = false := by have h := D_step 36 60; rw [d_36_60, d_37_60, d_38_60] at h; exact h
private theorem d_39_61 : D 39 61 = false := by have h := D_step 37 60; rw [d_37_60, d_38_60, d_39_60] at h; exact h
private theorem d_40_61 : D 40 61 = false := by have h := D_step 38 60; rw [d_38_60, d_39_60, d_40_60] at h; exact h
private theorem d_41_61 : D 41 61 = true := by have h := D_step 39 60; rw [d_39_60, d_40_60, d_41_60] at h; exact h
private theorem d_42_61 : D 42 61 = false := by have h := D_step 40 60; rw [d_40_60, d_41_60, d_42_60] at h; exact h
private theorem d_43_61 : D 43 61 = false := by have h := D_step 41 60; rw [d_41_60, d_42_60, d_43_60] at h; exact h
private theorem d_44_61 : D 44 61 = false := by have h := D_step 42 60; rw [d_42_60, d_43_60, d_44_60] at h; exact h
private theorem d_45_61 : D 45 61 = false := by have h := D_step 43 60; rw [d_43_60, d_44_60, d_45_60] at h; exact h

/-- **Three-Bit Gate Law for the Thirty-Eighth Left Diagonal (`D_thirty_eight_eq_gate`):**
for every `t ≥ 48`, `D 38 t = (!D 8 t || xor (D 10 t) (D 29 t))`. -/
theorem D_thirty_eight_eq_gate : ∀ t : Nat, 48 ≤ t →
    D 38 t = (!D 8 t || xor (D 10 t) (D 29 t))
  | 48, _ => by rw [d_38_48, d_8_48, d_10_48, d_29_48]; rfl
  | t + 1, ht => by
    by_cases h : t < 48
    · have h_eq : t + 1 = 48 := by omega
      rw [h_eq, d_38_48, d_8_48, d_10_48, d_29_48]; rfl
    · have ih := D_thirty_eight_eq_gate t (by omega)
      have hstep := D_step 36 t
      rw [D_thirty_six_eq_gate t (by omega), D_thirty_seven_eq_gate t (by omega), ih] at hstep
      rw [hstep, D_eight_succ_eq_D_ten t (by omega), D_ten_succ_eq_not_D_eight t (by omega),
          D_twenty_nine_step_closed t (by omega)]
      cases D 8 t <;> cases D 10 t <;> cases D 29 t <;> decide

/-- **Three-Bit Gate Law for the Thirty-Ninth Left Diagonal (`D_thirty_nine_eq_gate`):**
for every `t ≥ 50`, `D 39 t = (!D 8 t && xor (D 10 t) (D 29 t))`. -/
theorem D_thirty_nine_eq_gate : ∀ t : Nat, 50 ≤ t →
    D 39 t = (!D 8 t && xor (D 10 t) (D 29 t))
  | 50, _ => by rw [d_39_50, d_8_50, d_10_50, d_29_50]; rfl
  | t + 1, ht => by
    by_cases h : t < 50
    · have h_eq : t + 1 = 50 := by omega
      rw [h_eq, d_39_50, d_8_50, d_10_50, d_29_50]; rfl
    · have ih := D_thirty_nine_eq_gate t (by omega)
      have hstep := D_step 37 t
      rw [D_thirty_seven_eq_gate t (by omega), D_thirty_eight_eq_gate t (by omega), ih] at hstep
      rw [hstep, D_eight_succ_eq_D_ten t (by omega), D_ten_succ_eq_not_D_eight t (by omega),
          D_twenty_nine_step_closed t (by omega)]
      cases D 8 t <;> cases D 10 t <;> cases D 29 t <;> decide

/-- **Three-Bit Gate Law for the Fortieth Left Diagonal (`D_forty_eq_gate`):**
for every `t ≥ 55`, `D 40 t = (!(xor (D 8 t) (D 10 t)) && !D 29 t)`. -/
theorem D_forty_eq_gate : ∀ t : Nat, 55 ≤ t →
    D 40 t = (!(xor (D 8 t) (D 10 t)) && !D 29 t)
  | 55, _ => by rw [d_40_55, d_8_55, d_10_55, d_29_55]; rfl
  | t + 1, ht => by
    by_cases h : t < 55
    · have h_eq : t + 1 = 55 := by omega
      rw [h_eq, d_40_55, d_8_55, d_10_55, d_29_55]; rfl
    · have ih := D_forty_eq_gate t (by omega)
      have hstep := D_step 38 t
      rw [D_thirty_eight_eq_gate t (by omega), D_thirty_nine_eq_gate t (by omega), ih] at hstep
      rw [hstep, D_eight_succ_eq_D_ten t (by omega), D_ten_succ_eq_not_D_eight t (by omega),
          D_twenty_nine_step_closed t (by omega)]
      cases D 8 t <;> cases D 10 t <;> cases D 29 t <;> decide

/-- **Three-Bit Gate Law for the Forty-First Left Diagonal (`D_forty_one_eq_gate`):**
for every `t ≥ 55`, `D 41 t = (D 8 t || !D 10 t || D 29 t)`. -/
theorem D_forty_one_eq_gate : ∀ t : Nat, 55 ≤ t →
    D 41 t = (D 8 t || !D 10 t || D 29 t)
  | 55, _ => by rw [d_41_55, d_8_55, d_10_55, d_29_55]; rfl
  | t + 1, ht => by
    by_cases h : t < 55
    · have h_eq : t + 1 = 55 := by omega
      rw [h_eq, d_41_55, d_8_55, d_10_55, d_29_55]; rfl
    · have ih := D_forty_one_eq_gate t (by omega)
      have hstep := D_step 39 t
      rw [D_thirty_nine_eq_gate t (by omega), D_forty_eq_gate t (by omega), ih] at hstep
      rw [hstep, D_eight_succ_eq_D_ten t (by omega), D_ten_succ_eq_not_D_eight t (by omega),
          D_twenty_nine_step_closed t (by omega)]
      cases D 8 t <;> cases D 10 t <;> cases D 29 t <;> decide

/-- **Three-Bit Gate Law for the Forty-Second Left Diagonal (`D_forty_two_eq_gate`):**
for every `t ≥ 57`, `D 42 t = (!(xor (D 8 t) (D 10 t)) || !(xor (D 8 t) (D 29 t)))`. -/
theorem D_forty_two_eq_gate : ∀ t : Nat, 57 ≤ t →
    D 42 t = (!(xor (D 8 t) (D 10 t)) || !(xor (D 8 t) (D 29 t)))
  | 57, _ => by rw [d_42_57, d_8_57, d_10_57, d_29_57]; rfl
  | t + 1, ht => by
    by_cases h : t < 57
    · have h_eq : t + 1 = 57 := by omega
      rw [h_eq, d_42_57, d_8_57, d_10_57, d_29_57]; rfl
    · have ih := D_forty_two_eq_gate t (by omega)
      have hstep := D_step 40 t
      rw [D_forty_eq_gate t (by omega), D_forty_one_eq_gate t (by omega), ih] at hstep
      rw [hstep, D_eight_succ_eq_D_ten t (by omega), D_ten_succ_eq_not_D_eight t (by omega),
          D_twenty_nine_step_closed t (by omega)]
      cases D 8 t <;> cases D 10 t <;> cases D 29 t <;> decide

/-- **Three-Bit Gate Law for the Forty-Third Left Diagonal (`D_forty_three_eq_gate`):**
for every `t ≥ 57`, `D 43 t = ((D 8 t && D 10 t) || (!D 8 t && !D 10 t && D 29 t))`. -/
theorem D_forty_three_eq_gate : ∀ t : Nat, 57 ≤ t →
    D 43 t = ((D 8 t && D 10 t) || (!D 8 t && !D 10 t && D 29 t))
  | 57, _ => by rw [d_43_57, d_8_57, d_10_57, d_29_57]; rfl
  | t + 1, ht => by
    by_cases h : t < 57
    · have h_eq : t + 1 = 57 := by omega
      rw [h_eq, d_43_57, d_8_57, d_10_57, d_29_57]; rfl
    · have ih := D_forty_three_eq_gate t (by omega)
      have hstep := D_step 41 t
      rw [D_forty_one_eq_gate t (by omega), D_forty_two_eq_gate t (by omega), ih] at hstep
      rw [hstep, D_eight_succ_eq_D_ten t (by omega), D_ten_succ_eq_not_D_eight t (by omega),
          D_twenty_nine_step_closed t (by omega)]
      cases D 8 t <;> cases D 10 t <;> cases D 29 t <;> decide

/-- **Three-Bit Gate Law for the Forty-Fourth Left Diagonal (`D_forty_four_eq_gate`):**
for every `t ≥ 61`, `D 44 t = (!(xor (D 8 t) (D 10 t)) && !(xor (D 10 t) (D 29 t)))`. -/
theorem D_forty_four_eq_gate : ∀ t : Nat, 61 ≤ t →
    D 44 t = (!(xor (D 8 t) (D 10 t)) && !(xor (D 10 t) (D 29 t)))
  | 61, _ => by rw [d_44_61, d_8_61, d_10_61, d_29_61]; rfl
  | t + 1, ht => by
    by_cases h : t < 61
    · have h_eq : t + 1 = 61 := by omega
      rw [h_eq, d_44_61, d_8_61, d_10_61, d_29_61]; rfl
    · have ih := D_forty_four_eq_gate t (by omega)
      have hstep := D_step 42 t
      rw [D_forty_two_eq_gate t (by omega), D_forty_three_eq_gate t (by omega), ih] at hstep
      rw [hstep, D_eight_succ_eq_D_ten t (by omega), D_ten_succ_eq_not_D_eight t (by omega),
          D_twenty_nine_step_closed t (by omega)]
      cases D 8 t <;> cases D 10 t <;> cases D 29 t <;> decide

/-- **Period-4 Collapse Law on the Forty-Fifth Left Diagonal (`D_forty_five_eq_D_ten`):**
at depth 45, the dependence on `D 29 t` cancels identically and `D 45 t = D 10 t` for all `t ≥ 61`. -/
theorem D_forty_five_eq_D_ten : ∀ t : Nat, 61 ≤ t →
    D 45 t = D 10 t
  | 61, _ => by rw [d_45_61, d_10_61]
  | t + 1, ht => by
    by_cases h : t < 61
    · have h_eq : t + 1 = 61 := by omega
      rw [h_eq, d_45_61, d_10_61]
    · have ih := D_forty_five_eq_D_ten t (by omega)
      have hstep := D_step 43 t
      rw [D_forty_three_eq_gate t (by omega), D_forty_four_eq_gate t (by omega), ih] at hstep
      rw [hstep, D_ten_succ_eq_not_D_eight t (by omega)]
      cases D 8 t <;> cases D 10 t <;> cases D 29 t <;> decide

/-- **Two-Anti-Periodicity of the Forty-Fifth Left Diagonal (`D_forty_five_antiperiodic_two`):**
for every `t ≥ 61`, `D 45 (t + 2) = !D 45 t`. -/
theorem D_forty_five_antiperiodic_two (t : Nat) (ht : 61 ≤ t) :
    D 45 (t + 2) = !D 45 t := by
  rw [D_forty_five_eq_D_ten (t + 2) (by omega), D_forty_five_eq_D_ten t ht,
      D_ten_antiperiodic_two t (by omega)]

/-- **Eventual Two-Anti-Periodicity of `D 45` (`evAntiPer_D_forty_five`):**
`EvAntiPer (D 45) 2` holds unconditionally. -/
theorem evAntiPer_D_forty_five : EvAntiPer (D 45) 2 :=
  ⟨61, D_forty_five_antiperiodic_two⟩

/-- **Problem 3 for the Forty-Fifth Left Diagonal (`halfDensity_D_forty_five`):**
`D 45` has exact asymptotic density `1/2` (`HalfDensity (D 45)`). -/
theorem halfDensity_D_forty_five : HalfDensity (D 45) :=
  halfDensity_of_antiperiodic (by omega) evAntiPer_D_forty_five

/-! ### 16. Multiplexer Cascade `D 46 .. D 52`, Block-8 Balance of `D 48, D 50, D 51`, 4-Anti-Periodicity of `D 52`, and `HalfDensity` on `D 48, D 50, D 51, D 52` -/

private theorem d_46_23 : D 46 23 = true := by have h := D_step 44 22; rw [d_44_22, (D_eq_false_of_two_mul_lt 45 22 (by omega)), (D_eq_false_of_two_mul_lt 46 22 (by omega))] at h; exact h
private theorem d_46_24 : D 46 24 = false := by have h := D_step 44 23; rw [d_44_23, d_45_23, d_46_23] at h; exact h
private theorem d_47_24 : D 47 24 = false := by have h := D_step 45 23; rw [d_45_23, d_46_23, (D_eq_false_of_two_mul_lt 47 23 (by omega))] at h; exact h
private theorem d_48_24 : D 48 24 = true := by have h := D_step 46 23; rw [d_46_23, (D_eq_false_of_two_mul_lt 47 23 (by omega)), (D_eq_false_of_two_mul_lt 48 23 (by omega))] at h; exact h
private theorem d_46_25 : D 46 25 = false := by have h := D_step 44 24; rw [d_44_24, d_45_24, d_46_24] at h; exact h
private theorem d_47_25 : D 47 25 = false := by have h := D_step 45 24; rw [d_45_24, d_46_24, d_47_24] at h; exact h
private theorem d_48_25 : D 48 25 = true := by have h := D_step 46 24; rw [d_46_24, d_47_24, d_48_24] at h; exact h
private theorem d_49_25 : D 49 25 = true := by have h := D_step 47 24; rw [d_47_24, d_48_24, (D_eq_false_of_two_mul_lt 49 24 (by omega))] at h; exact h
private theorem d_50_25 : D 50 25 = true := by have h := D_step 48 24; rw [d_48_24, (D_eq_false_of_two_mul_lt 49 24 (by omega)), (D_eq_false_of_two_mul_lt 50 24 (by omega))] at h; exact h
private theorem d_46_26 : D 46 26 = true := by have h := D_step 44 25; rw [d_44_25, d_45_25, d_46_25] at h; exact h
private theorem d_47_26 : D 47 26 = false := by have h := D_step 45 25; rw [d_45_25, d_46_25, d_47_25] at h; exact h
private theorem d_48_26 : D 48 26 = true := by have h := D_step 46 25; rw [d_46_25, d_47_25, d_48_25] at h; exact h
private theorem d_49_26 : D 49 26 = true := by have h := D_step 47 25; rw [d_47_25, d_48_25, d_49_25] at h; exact h
private theorem d_50_26 : D 50 26 = false := by have h := D_step 48 25; rw [d_48_25, d_49_25, d_50_25] at h; exact h
private theorem d_51_26 : D 51 26 = false := by have h := D_step 49 25; rw [d_49_25, d_50_25, (D_eq_false_of_two_mul_lt 51 25 (by omega))] at h; exact h
private theorem d_52_26 : D 52 26 = true := by have h := D_step 50 25; rw [d_50_25, (D_eq_false_of_two_mul_lt 51 25 (by omega)), (D_eq_false_of_two_mul_lt 52 25 (by omega))] at h; exact h
private theorem d_46_27 : D 46 27 = true := by have h := D_step 44 26; rw [d_44_26, d_45_26, d_46_26] at h; exact h
private theorem d_47_27 : D 47 27 = true := by have h := D_step 45 26; rw [d_45_26, d_46_26, d_47_26] at h; exact h
private theorem d_48_27 : D 48 27 = false := by have h := D_step 46 26; rw [d_46_26, d_47_26, d_48_26] at h; exact h
private theorem d_49_27 : D 49 27 = true := by have h := D_step 47 26; rw [d_47_26, d_48_26, d_49_26] at h; exact h
private theorem d_50_27 : D 50 27 = false := by have h := D_step 48 26; rw [d_48_26, d_49_26, d_50_26] at h; exact h
private theorem d_51_27 : D 51 27 = true := by have h := D_step 49 26; rw [d_49_26, d_50_26, d_51_26] at h; exact h
private theorem d_52_27 : D 52 27 = true := by have h := D_step 50 26; rw [d_50_26, d_51_26, d_52_26] at h; exact h
private theorem d_46_28 : D 46 28 = true := by have h := D_step 44 27; rw [d_44_27, d_45_27, d_46_27] at h; exact h
private theorem d_47_28 : D 47 28 = true := by have h := D_step 45 27; rw [d_45_27, d_46_27, d_47_27] at h; exact h
private theorem d_48_28 : D 48 28 = false := by have h := D_step 46 27; rw [d_46_27, d_47_27, d_48_27] at h; exact h
private theorem d_49_28 : D 49 28 = false := by have h := D_step 47 27; rw [d_47_27, d_48_27, d_49_27] at h; exact h
private theorem d_50_28 : D 50 28 = true := by have h := D_step 48 27; rw [d_48_27, d_49_27, d_50_27] at h; exact h
private theorem d_51_28 : D 51 28 = false := by have h := D_step 49 27; rw [d_49_27, d_50_27, d_51_27] at h; exact h
private theorem d_52_28 : D 52 28 = true := by have h := D_step 50 27; rw [d_50_27, d_51_27, d_52_27] at h; exact h
private theorem d_46_29 : D 46 29 = false := by have h := D_step 44 28; rw [d_44_28, d_45_28, d_46_28] at h; exact h
private theorem d_47_29 : D 47 29 = false := by have h := D_step 45 28; rw [d_45_28, d_46_28, d_47_28] at h; exact h
private theorem d_48_29 : D 48 29 = false := by have h := D_step 46 28; rw [d_46_28, d_47_28, d_48_28] at h; exact h
private theorem d_49_29 : D 49 29 = true := by have h := D_step 47 28; rw [d_47_28, d_48_28, d_49_28] at h; exact h
private theorem d_50_29 : D 50 29 = true := by have h := D_step 48 28; rw [d_48_28, d_49_28, d_50_28] at h; exact h
private theorem d_51_29 : D 51 29 = true := by have h := D_step 49 28; rw [d_49_28, d_50_28, d_51_28] at h; exact h
private theorem d_52_29 : D 52 29 = false := by have h := D_step 50 28; rw [d_50_28, d_51_28, d_52_28] at h; exact h
private theorem d_46_30 : D 46 30 = false := by have h := D_step 44 29; rw [d_44_29, d_45_29, d_46_29] at h; exact h
private theorem d_47_30 : D 47 30 = true := by have h := D_step 45 29; rw [d_45_29, d_46_29, d_47_29] at h; exact h
private theorem d_48_30 : D 48 30 = false := by have h := D_step 46 29; rw [d_46_29, d_47_29, d_48_29] at h; exact h
private theorem d_49_30 : D 49 30 = true := by have h := D_step 47 29; rw [d_47_29, d_48_29, d_49_29] at h; exact h
private theorem d_50_30 : D 50 30 = true := by have h := D_step 48 29; rw [d_48_29, d_49_29, d_50_29] at h; exact h
private theorem d_51_30 : D 51 30 = false := by have h := D_step 49 29; rw [d_49_29, d_50_29, d_51_29] at h; exact h
private theorem d_52_30 : D 52 30 = false := by have h := D_step 50 29; rw [d_50_29, d_51_29, d_52_29] at h; exact h
private theorem d_46_31 : D 46 31 = false := by have h := D_step 44 30; rw [d_44_30, d_45_30, d_46_30] at h; exact h
private theorem d_47_31 : D 47 31 = true := by have h := D_step 45 30; rw [d_45_30, d_46_30, d_47_30] at h; exact h
private theorem d_48_31 : D 48 31 = true := by have h := D_step 46 30; rw [d_46_30, d_47_30, d_48_30] at h; exact h
private theorem d_49_31 : D 49 31 = false := by have h := D_step 47 30; rw [d_47_30, d_48_30, d_49_30] at h; exact h
private theorem d_50_31 : D 50 31 = true := by have h := D_step 48 30; rw [d_48_30, d_49_30, d_50_30] at h; exact h
private theorem d_51_31 : D 51 31 = false := by have h := D_step 49 30; rw [d_49_30, d_50_30, d_51_30] at h; exact h
private theorem d_52_31 : D 52 31 = true := by have h := D_step 50 30; rw [d_50_30, d_51_30, d_52_30] at h; exact h
private theorem d_46_32 : D 46 32 = false := by have h := D_step 44 31; rw [d_44_31, d_45_31, d_46_31] at h; exact h
private theorem d_47_32 : D 47 32 = false := by have h := D_step 45 31; rw [d_45_31, d_46_31, d_47_31] at h; exact h
private theorem d_48_32 : D 48 32 = true := by have h := D_step 46 31; rw [d_46_31, d_47_31, d_48_31] at h; exact h
private theorem d_49_32 : D 49 32 = false := by have h := D_step 47 31; rw [d_47_31, d_48_31, d_49_31] at h; exact h
private theorem d_50_32 : D 50 32 = false := by have h := D_step 48 31; rw [d_48_31, d_49_31, d_50_31] at h; exact h
private theorem d_51_32 : D 51 32 = true := by have h := D_step 49 31; rw [d_49_31, d_50_31, d_51_31] at h; exact h
private theorem d_52_32 : D 52 32 = false := by have h := D_step 50 31; rw [d_50_31, d_51_31, d_52_31] at h; exact h
private theorem d_46_33 : D 46 33 = false := by have h := D_step 44 32; rw [d_44_32, d_45_32, d_46_32] at h; exact h
private theorem d_47_33 : D 47 33 = false := by have h := D_step 45 32; rw [d_45_32, d_46_32, d_47_32] at h; exact h
private theorem d_48_33 : D 48 33 = true := by have h := D_step 46 32; rw [d_46_32, d_47_32, d_48_32] at h; exact h
private theorem d_49_33 : D 49 33 = true := by have h := D_step 47 32; rw [d_47_32, d_48_32, d_49_32] at h; exact h
private theorem d_50_33 : D 50 33 = true := by have h := D_step 48 32; rw [d_48_32, d_49_32, d_50_32] at h; exact h
private theorem d_51_33 : D 51 33 = true := by have h := D_step 49 32; rw [d_49_32, d_50_32, d_51_32] at h; exact h
private theorem d_52_33 : D 52 33 = true := by have h := D_step 50 32; rw [d_50_32, d_51_32, d_52_32] at h; exact h
private theorem d_46_34 : D 46 34 = true := by have h := D_step 44 33; rw [d_44_33, d_45_33, d_46_33] at h; exact h
private theorem d_47_34 : D 47 34 = true := by have h := D_step 45 33; rw [d_45_33, d_46_33, d_47_33] at h; exact h
private theorem d_48_34 : D 48 34 = true := by have h := D_step 46 33; rw [d_46_33, d_47_33, d_48_33] at h; exact h
private theorem d_49_34 : D 49 34 = true := by have h := D_step 47 33; rw [d_47_33, d_48_33, d_49_33] at h; exact h
private theorem d_50_34 : D 50 34 = false := by have h := D_step 48 33; rw [d_48_33, d_49_33, d_50_33] at h; exact h
private theorem d_51_34 : D 51 34 = false := by have h := D_step 49 33; rw [d_49_33, d_50_33, d_51_33] at h; exact h
private theorem d_52_34 : D 52 34 = false := by have h := D_step 50 33; rw [d_50_33, d_51_33, d_52_33] at h; exact h
private theorem d_46_35 : D 46 35 = true := by have h := D_step 44 34; rw [d_44_34, d_45_34, d_46_34] at h; exact h
private theorem d_47_35 : D 47 35 = true := by have h := D_step 45 34; rw [d_45_34, d_46_34, d_47_34] at h; exact h
private theorem d_48_35 : D 48 35 = false := by have h := D_step 46 34; rw [d_46_34, d_47_34, d_48_34] at h; exact h
private theorem d_49_35 : D 49 35 = false := by have h := D_step 47 34; rw [d_47_34, d_48_34, d_49_34] at h; exact h
private theorem d_50_35 : D 50 35 = false := by have h := D_step 48 34; rw [d_48_34, d_49_34, d_50_34] at h; exact h
private theorem d_51_35 : D 51 35 = true := by have h := D_step 49 34; rw [d_49_34, d_50_34, d_51_34] at h; exact h
private theorem d_52_35 : D 52 35 = false := by have h := D_step 50 34; rw [d_50_34, d_51_34, d_52_34] at h; exact h
private theorem d_46_36 : D 46 36 = false := by have h := D_step 44 35; rw [d_44_35, d_45_35, d_46_35] at h; exact h
private theorem d_47_36 : D 47 36 = false := by have h := D_step 45 35; rw [d_45_35, d_46_35, d_47_35] at h; exact h
private theorem d_48_36 : D 48 36 = false := by have h := D_step 46 35; rw [d_46_35, d_47_35, d_48_35] at h; exact h
private theorem d_49_36 : D 49 36 = true := by have h := D_step 47 35; rw [d_47_35, d_48_35, d_49_35] at h; exact h
private theorem d_50_36 : D 50 36 = false := by have h := D_step 48 35; rw [d_48_35, d_49_35, d_50_35] at h; exact h
private theorem d_51_36 : D 51 36 = true := by have h := D_step 49 35; rw [d_49_35, d_50_35, d_51_35] at h; exact h
private theorem d_52_36 : D 52 36 = true := by have h := D_step 50 35; rw [d_50_35, d_51_35, d_52_35] at h; exact h
private theorem d_46_37 : D 46 37 = true := by have h := D_step 44 36; rw [d_44_36, d_45_36, d_46_36] at h; exact h
private theorem d_47_37 : D 47 37 = false := by have h := D_step 45 36; rw [d_45_36, d_46_36, d_47_36] at h; exact h
private theorem d_48_37 : D 48 37 = false := by have h := D_step 46 36; rw [d_46_36, d_47_36, d_48_36] at h; exact h
private theorem d_49_37 : D 49 37 = true := by have h := D_step 47 36; rw [d_47_36, d_48_36, d_49_36] at h; exact h
private theorem d_50_37 : D 50 37 = true := by have h := D_step 48 36; rw [d_48_36, d_49_36, d_50_36] at h; exact h
private theorem d_51_37 : D 51 37 = false := by have h := D_step 49 36; rw [d_49_36, d_50_36, d_51_36] at h; exact h
private theorem d_52_37 : D 52 37 = true := by have h := D_step 50 36; rw [d_50_36, d_51_36, d_52_36] at h; exact h
private theorem d_46_38 : D 46 38 = false := by have h := D_step 44 37; rw [d_44_37, d_45_37, d_46_37] at h; exact h
private theorem d_47_38 : D 47 38 = false := by have h := D_step 45 37; rw [d_45_37, d_46_37, d_47_37] at h; exact h
private theorem d_48_38 : D 48 38 = true := by have h := D_step 46 37; rw [d_46_37, d_47_37, d_48_37] at h; exact h
private theorem d_49_38 : D 49 38 = true := by have h := D_step 47 37; rw [d_47_37, d_48_37, d_49_37] at h; exact h
private theorem d_50_38 : D 50 38 = true := by have h := D_step 48 37; rw [d_48_37, d_49_37, d_50_37] at h; exact h
private theorem d_51_38 : D 51 38 = false := by have h := D_step 49 37; rw [d_49_37, d_50_37, d_51_37] at h; exact h
private theorem d_52_38 : D 52 38 = false := by have h := D_step 50 37; rw [d_50_37, d_51_37, d_52_37] at h; exact h
private theorem d_46_39 : D 46 39 = false := by have h := D_step 44 38; rw [d_44_38, d_45_38, d_46_38] at h; exact h
private theorem d_47_39 : D 47 39 = false := by have h := D_step 45 38; rw [d_45_38, d_46_38, d_47_38] at h; exact h
private theorem d_48_39 : D 48 39 = true := by have h := D_step 46 38; rw [d_46_38, d_47_38, d_48_38] at h; exact h
private theorem d_49_39 : D 49 39 = true := by have h := D_step 47 38; rw [d_47_38, d_48_38, d_49_38] at h; exact h
private theorem d_50_39 : D 50 39 = false := by have h := D_step 48 38; rw [d_48_38, d_49_38, d_50_38] at h; exact h
private theorem d_51_39 : D 51 39 = false := by have h := D_step 49 38; rw [d_49_38, d_50_38, d_51_38] at h; exact h
private theorem d_52_39 : D 52 39 = true := by have h := D_step 50 38; rw [d_50_38, d_51_38, d_52_38] at h; exact h
private theorem d_46_40 : D 46 40 = true := by have h := D_step 44 39; rw [d_44_39, d_45_39, d_46_39] at h; exact h
private theorem d_47_40 : D 47 40 = false := by have h := D_step 45 39; rw [d_45_39, d_46_39, d_47_39] at h; exact h
private theorem d_48_40 : D 48 40 = true := by have h := D_step 46 39; rw [d_46_39, d_47_39, d_48_39] at h; exact h
private theorem d_49_40 : D 49 40 = true := by have h := D_step 47 39; rw [d_47_39, d_48_39, d_49_39] at h; exact h
private theorem d_50_40 : D 50 40 = false := by have h := D_step 48 39; rw [d_48_39, d_49_39, d_50_39] at h; exact h
private theorem d_51_40 : D 51 40 = true := by have h := D_step 49 39; rw [d_49_39, d_50_39, d_51_39] at h; exact h
private theorem d_52_40 : D 52 40 = true := by have h := D_step 50 39; rw [d_50_39, d_51_39, d_52_39] at h; exact h
private theorem d_46_41 : D 46 41 = true := by have h := D_step 44 40; rw [d_44_40, d_45_40, d_46_40] at h; exact h
private theorem d_47_41 : D 47 41 = false := by have h := D_step 45 40; rw [d_45_40, d_46_40, d_47_40] at h; exact h
private theorem d_48_41 : D 48 41 = false := by have h := D_step 46 40; rw [d_46_40, d_47_40, d_48_40] at h; exact h
private theorem d_49_41 : D 49 41 = true := by have h := D_step 47 40; rw [d_47_40, d_48_40, d_49_40] at h; exact h
private theorem d_50_41 : D 50 41 = false := by have h := D_step 48 40; rw [d_48_40, d_49_40, d_50_40] at h; exact h
private theorem d_51_41 : D 51 41 = false := by have h := D_step 49 40; rw [d_49_40, d_50_40, d_51_40] at h; exact h
private theorem d_52_41 : D 52 41 = true := by have h := D_step 50 40; rw [d_50_40, d_51_40, d_52_40] at h; exact h
private theorem d_46_42 : D 46 42 = false := by have h := D_step 44 41; rw [d_44_41, d_45_41, d_46_41] at h; exact h
private theorem d_47_42 : D 47 42 = true := by have h := D_step 45 41; rw [d_45_41, d_46_41, d_47_41] at h; exact h
private theorem d_48_42 : D 48 42 = true := by have h := D_step 46 41; rw [d_46_41, d_47_41, d_48_41] at h; exact h
private theorem d_49_42 : D 49 42 = true := by have h := D_step 47 41; rw [d_47_41, d_48_41, d_49_41] at h; exact h
private theorem d_50_42 : D 50 42 = true := by have h := D_step 48 41; rw [d_48_41, d_49_41, d_50_41] at h; exact h
private theorem d_51_42 : D 51 42 = true := by have h := D_step 49 41; rw [d_49_41, d_50_41, d_51_41] at h; exact h
private theorem d_52_42 : D 52 42 = true := by have h := D_step 50 41; rw [d_50_41, d_51_41, d_52_41] at h; exact h
private theorem d_46_43 : D 46 43 = true := by have h := D_step 44 42; rw [d_44_42, d_45_42, d_46_42] at h; exact h
private theorem d_47_43 : D 47 43 = true := by have h := D_step 45 42; rw [d_45_42, d_46_42, d_47_42] at h; exact h
private theorem d_48_43 : D 48 43 = true := by have h := D_step 46 42; rw [d_46_42, d_47_42, d_48_42] at h; exact h
private theorem d_49_43 : D 49 43 = false := by have h := D_step 47 42; rw [d_47_42, d_48_42, d_49_42] at h; exact h
private theorem d_50_43 : D 50 43 = false := by have h := D_step 48 42; rw [d_48_42, d_49_42, d_50_42] at h; exact h
private theorem d_51_43 : D 51 43 = false := by have h := D_step 49 42; rw [d_49_42, d_50_42, d_51_42] at h; exact h
private theorem d_52_43 : D 52 43 = false := by have h := D_step 50 42; rw [d_50_42, d_51_42, d_52_42] at h; exact h
private theorem d_46_44 : D 46 44 = true := by have h := D_step 44 43; rw [d_44_43, d_45_43, d_46_43] at h; exact h
private theorem d_47_44 : D 47 44 = false := by have h := D_step 45 43; rw [d_45_43, d_46_43, d_47_43] at h; exact h
private theorem d_48_44 : D 48 44 = false := by have h := D_step 46 43; rw [d_46_43, d_47_43, d_48_43] at h; exact h
private theorem d_49_44 : D 49 44 = false := by have h := D_step 47 43; rw [d_47_43, d_48_43, d_49_43] at h; exact h
private theorem d_50_44 : D 50 44 = true := by have h := D_step 48 43; rw [d_48_43, d_49_43, d_50_43] at h; exact h
private theorem d_51_44 : D 51 44 = false := by have h := D_step 49 43; rw [d_49_43, d_50_43, d_51_43] at h; exact h
private theorem d_52_44 : D 52 44 = false := by have h := D_step 50 43; rw [d_50_43, d_51_43, d_52_43] at h; exact h
private theorem d_46_45 : D 46 45 = true := by have h := D_step 44 44; rw [d_44_44, d_45_44, d_46_44] at h; exact h
private theorem d_47_45 : D 47 45 = false := by have h := D_step 45 44; rw [d_45_44, d_46_44, d_47_44] at h; exact h
private theorem d_48_45 : D 48 45 = true := by have h := D_step 46 44; rw [d_46_44, d_47_44, d_48_44] at h; exact h
private theorem d_49_45 : D 49 45 = false := by have h := D_step 47 44; rw [d_47_44, d_48_44, d_49_44] at h; exact h
private theorem d_50_45 : D 50 45 = true := by have h := D_step 48 44; rw [d_48_44, d_49_44, d_50_44] at h; exact h
private theorem d_51_45 : D 51 45 = true := by have h := D_step 49 44; rw [d_49_44, d_50_44, d_51_44] at h; exact h
private theorem d_52_45 : D 52 45 = true := by have h := D_step 50 44; rw [d_50_44, d_51_44, d_52_44] at h; exact h
private theorem d_46_46 : D 46 46 = false := by have h := D_step 44 45; rw [d_44_45, d_45_45, d_46_45] at h; exact h
private theorem d_47_46 : D 47 46 = true := by have h := D_step 45 45; rw [d_45_45, d_46_45, d_47_45] at h; exact h
private theorem d_48_46 : D 48 46 = false := by have h := D_step 46 45; rw [d_46_45, d_47_45, d_48_45] at h; exact h
private theorem d_49_46 : D 49 46 = true := by have h := D_step 47 45; rw [d_47_45, d_48_45, d_49_45] at h; exact h
private theorem d_50_46 : D 50 46 = false := by have h := D_step 48 45; rw [d_48_45, d_49_45, d_50_45] at h; exact h
private theorem d_51_46 : D 51 46 = true := by have h := D_step 49 45; rw [d_49_45, d_50_45, d_51_45] at h; exact h
private theorem d_52_46 : D 52 46 = false := by have h := D_step 50 45; rw [d_50_45, d_51_45, d_52_45] at h; exact h
private theorem d_46_47 : D 46 47 = false := by have h := D_step 44 46; rw [d_44_46, d_45_46, d_46_46] at h; exact h
private theorem d_47_47 : D 47 47 = true := by have h := D_step 45 46; rw [d_45_46, d_46_46, d_47_46] at h; exact h
private theorem d_48_47 : D 48 47 = true := by have h := D_step 46 46; rw [d_46_46, d_47_46, d_48_46] at h; exact h
private theorem d_49_47 : D 49 47 = false := by have h := D_step 47 46; rw [d_47_46, d_48_46, d_49_46] at h; exact h
private theorem d_50_47 : D 50 47 = true := by have h := D_step 48 46; rw [d_48_46, d_49_46, d_50_46] at h; exact h
private theorem d_51_47 : D 51 47 = false := by have h := D_step 49 46; rw [d_49_46, d_50_46, d_51_46] at h; exact h
private theorem d_52_47 : D 52 47 = true := by have h := D_step 50 46; rw [d_50_46, d_51_46, d_52_46] at h; exact h
private theorem d_46_48 : D 46 48 = false := by have h := D_step 44 47; rw [d_44_47, d_45_47, d_46_47] at h; exact h
private theorem d_47_48 : D 47 48 = true := by have h := D_step 45 47; rw [d_45_47, d_46_47, d_47_47] at h; exact h
private theorem d_48_48 : D 48 48 = true := by have h := D_step 46 47; rw [d_46_47, d_47_47, d_48_47] at h; exact h
private theorem d_49_48 : D 49 48 = false := by have h := D_step 47 47; rw [d_47_47, d_48_47, d_49_47] at h; exact h
private theorem d_50_48 : D 50 48 = false := by have h := D_step 48 47; rw [d_48_47, d_49_47, d_50_47] at h; exact h
private theorem d_51_48 : D 51 48 = true := by have h := D_step 49 47; rw [d_49_47, d_50_47, d_51_47] at h; exact h
private theorem d_52_48 : D 52 48 = false := by have h := D_step 50 47; rw [d_50_47, d_51_47, d_52_47] at h; exact h
private theorem d_46_49 : D 46 49 = false := by have h := D_step 44 48; rw [d_44_48, d_45_48, d_46_48] at h; exact h
private theorem d_47_49 : D 47 49 = true := by have h := D_step 45 48; rw [d_45_48, d_46_48, d_47_48] at h; exact h
private theorem d_48_49 : D 48 49 = true := by have h := D_step 46 48; rw [d_46_48, d_47_48, d_48_48] at h; exact h
private theorem d_49_49 : D 49 49 = false := by have h := D_step 47 48; rw [d_47_48, d_48_48, d_49_48] at h; exact h
private theorem d_50_49 : D 50 49 = true := by have h := D_step 48 48; rw [d_48_48, d_49_48, d_50_48] at h; exact h
private theorem d_51_49 : D 51 49 = true := by have h := D_step 49 48; rw [d_49_48, d_50_48, d_51_48] at h; exact h
private theorem d_52_49 : D 52 49 = true := by have h := D_step 50 48; rw [d_50_48, d_51_48, d_52_48] at h; exact h
private theorem d_46_50 : D 46 50 = false := by have h := D_step 44 49; rw [d_44_49, d_45_49, d_46_49] at h; exact h
private theorem d_47_50 : D 47 50 = true := by have h := D_step 45 49; rw [d_45_49, d_46_49, d_47_49] at h; exact h
private theorem d_48_50 : D 48 50 = true := by have h := D_step 46 49; rw [d_46_49, d_47_49, d_48_49] at h; exact h
private theorem d_49_50 : D 49 50 = false := by have h := D_step 47 49; rw [d_47_49, d_48_49, d_49_49] at h; exact h
private theorem d_50_50 : D 50 50 = false := by have h := D_step 48 49; rw [d_48_49, d_49_49, d_50_49] at h; exact h
private theorem d_51_50 : D 51 50 = true := by have h := D_step 49 49; rw [d_49_49, d_50_49, d_51_49] at h; exact h
private theorem d_52_50 : D 52 50 = false := by have h := D_step 50 49; rw [d_50_49, d_51_49, d_52_49] at h; exact h
private theorem d_46_51 : D 46 51 = false := by have h := D_step 44 50; rw [d_44_50, d_45_50, d_46_50] at h; exact h
private theorem d_47_51 : D 47 51 = true := by have h := D_step 45 50; rw [d_45_50, d_46_50, d_47_50] at h; exact h
private theorem d_48_51 : D 48 51 = true := by have h := D_step 46 50; rw [d_46_50, d_47_50, d_48_50] at h; exact h
private theorem d_49_51 : D 49 51 = false := by have h := D_step 47 50; rw [d_47_50, d_48_50, d_49_50] at h; exact h
private theorem d_50_51 : D 50 51 = true := by have h := D_step 48 50; rw [d_48_50, d_49_50, d_50_50] at h; exact h
private theorem d_51_51 : D 51 51 = true := by have h := D_step 49 50; rw [d_49_50, d_50_50, d_51_50] at h; exact h
private theorem d_52_51 : D 52 51 = true := by have h := D_step 50 50; rw [d_50_50, d_51_50, d_52_50] at h; exact h
private theorem d_46_52 : D 46 52 = false := by have h := D_step 44 51; rw [d_44_51, d_45_51, d_46_51] at h; exact h
private theorem d_47_52 : D 47 52 = false := by have h := D_step 45 51; rw [d_45_51, d_46_51, d_47_51] at h; exact h
private theorem d_48_52 : D 48 52 = true := by have h := D_step 46 51; rw [d_46_51, d_47_51, d_48_51] at h; exact h
private theorem d_49_52 : D 49 52 = false := by have h := D_step 47 51; rw [d_47_51, d_48_51, d_49_51] at h; exact h
private theorem d_50_52 : D 50 52 = false := by have h := D_step 48 51; rw [d_48_51, d_49_51, d_50_51] at h; exact h
private theorem d_51_52 : D 51 52 = true := by have h := D_step 49 51; rw [d_49_51, d_50_51, d_51_51] at h; exact h
private theorem d_52_52 : D 52 52 = false := by have h := D_step 50 51; rw [d_50_51, d_51_51, d_52_51] at h; exact h
private theorem d_46_53 : D 46 53 = true := by have h := D_step 44 52; rw [d_44_52, d_45_52, d_46_52] at h; exact h
private theorem d_47_53 : D 47 53 = false := by have h := D_step 45 52; rw [d_45_52, d_46_52, d_47_52] at h; exact h
private theorem d_48_53 : D 48 53 = true := by have h := D_step 46 52; rw [d_46_52, d_47_52, d_48_52] at h; exact h
private theorem d_49_53 : D 49 53 = true := by have h := D_step 47 52; rw [d_47_52, d_48_52, d_49_52] at h; exact h
private theorem d_50_53 : D 50 53 = true := by have h := D_step 48 52; rw [d_48_52, d_49_52, d_50_52] at h; exact h
private theorem d_51_53 : D 51 53 = true := by have h := D_step 49 52; rw [d_49_52, d_50_52, d_51_52] at h; exact h
private theorem d_52_53 : D 52 53 = true := by have h := D_step 50 52; rw [d_50_52, d_51_52, d_52_52] at h; exact h
private theorem d_46_54 : D 46 54 = true := by have h := D_step 44 53; rw [d_44_53, d_45_53, d_46_53] at h; exact h
private theorem d_47_54 : D 47 54 = true := by have h := D_step 45 53; rw [d_45_53, d_46_53, d_47_53] at h; exact h
private theorem d_48_54 : D 48 54 = false := by have h := D_step 46 53; rw [d_46_53, d_47_53, d_48_53] at h; exact h
private theorem d_49_54 : D 49 54 = true := by have h := D_step 47 53; rw [d_47_53, d_48_53, d_49_53] at h; exact h
private theorem d_50_54 : D 50 54 = false := by have h := D_step 48 53; rw [d_48_53, d_49_53, d_50_53] at h; exact h
private theorem d_51_54 : D 51 54 = false := by have h := D_step 49 53; rw [d_49_53, d_50_53, d_51_53] at h; exact h
private theorem d_52_54 : D 52 54 = false := by have h := D_step 50 53; rw [d_50_53, d_51_53, d_52_53] at h; exact h
private theorem d_46_55 : D 46 55 = false := by have h := D_step 44 54; rw [d_44_54, d_45_54, d_46_54] at h; exact h
private theorem d_47_55 : D 47 55 = true := by have h := D_step 45 54; rw [d_45_54, d_46_54, d_47_54] at h; exact h
private theorem d_48_55 : D 48 55 = false := by have h := D_step 46 54; rw [d_46_54, d_47_54, d_48_54] at h; exact h
private theorem d_49_55 : D 49 55 = false := by have h := D_step 47 54; rw [d_47_54, d_48_54, d_49_54] at h; exact h
private theorem d_50_55 : D 50 55 = true := by have h := D_step 48 54; rw [d_48_54, d_49_54, d_50_54] at h; exact h
private theorem d_51_55 : D 51 55 = true := by have h := D_step 49 54; rw [d_49_54, d_50_54, d_51_54] at h; exact h
private theorem d_52_55 : D 52 55 = false := by have h := D_step 50 54; rw [d_50_54, d_51_54, d_52_54] at h; exact h
private theorem d_46_56 : D 46 56 = false := by have h := D_step 44 55; rw [d_44_55, d_45_55, d_46_55] at h; exact h
private theorem d_47_56 : D 47 56 = false := by have h := D_step 45 55; rw [d_45_55, d_46_55, d_47_55] at h; exact h
private theorem d_48_56 : D 48 56 = true := by have h := D_step 46 55; rw [d_46_55, d_47_55, d_48_55] at h; exact h
private theorem d_49_56 : D 49 56 = true := by have h := D_step 47 55; rw [d_47_55, d_48_55, d_49_55] at h; exact h
private theorem d_50_56 : D 50 56 = true := by have h := D_step 48 55; rw [d_48_55, d_49_55, d_50_55] at h; exact h
private theorem d_51_56 : D 51 56 = true := by have h := D_step 49 55; rw [d_49_55, d_50_55, d_51_55] at h; exact h
private theorem d_52_56 : D 52 56 = false := by have h := D_step 50 55; rw [d_50_55, d_51_55, d_52_55] at h; exact h
private theorem d_46_57 : D 46 57 = true := by have h := D_step 44 56; rw [d_44_56, d_45_56, d_46_56] at h; exact h
private theorem d_47_57 : D 47 57 = false := by have h := D_step 45 56; rw [d_45_56, d_46_56, d_47_56] at h; exact h
private theorem d_48_57 : D 48 57 = true := by have h := D_step 46 56; rw [d_46_56, d_47_56, d_48_56] at h; exact h
private theorem d_49_57 : D 49 57 = true := by have h := D_step 47 56; rw [d_47_56, d_48_56, d_49_56] at h; exact h
private theorem d_50_57 : D 50 57 = false := by have h := D_step 48 56; rw [d_48_56, d_49_56, d_50_56] at h; exact h
private theorem d_51_57 : D 51 57 = false := by have h := D_step 49 56; rw [d_49_56, d_50_56, d_51_56] at h; exact h
private theorem d_52_57 : D 52 57 = false := by have h := D_step 50 56; rw [d_50_56, d_51_56, d_52_56] at h; exact h
private theorem d_46_58 : D 46 58 = false := by have h := D_step 44 57; rw [d_44_57, d_45_57, d_46_57] at h; exact h
private theorem d_47_58 : D 47 58 = true := by have h := D_step 45 57; rw [d_45_57, d_46_57, d_47_57] at h; exact h
private theorem d_48_58 : D 48 58 = false := by have h := D_step 46 57; rw [d_46_57, d_47_57, d_48_57] at h; exact h
private theorem d_49_58 : D 49 58 = true := by have h := D_step 47 57; rw [d_47_57, d_48_57, d_49_57] at h; exact h
private theorem d_50_58 : D 50 58 = false := by have h := D_step 48 57; rw [d_48_57, d_49_57, d_50_57] at h; exact h
private theorem d_51_58 : D 51 58 = true := by have h := D_step 49 57; rw [d_49_57, d_50_57, d_51_57] at h; exact h
private theorem d_52_58 : D 52 58 = false := by have h := D_step 50 57; rw [d_50_57, d_51_57, d_52_57] at h; exact h
private theorem d_46_59 : D 46 59 = true := by have h := D_step 44 58; rw [d_44_58, d_45_58, d_46_58] at h; exact h
private theorem d_47_59 : D 47 59 = false := by have h := D_step 45 58; rw [d_45_58, d_46_58, d_47_58] at h; exact h
private theorem d_48_59 : D 48 59 = true := by have h := D_step 46 58; rw [d_46_58, d_47_58, d_48_58] at h; exact h
private theorem d_49_59 : D 49 59 = false := by have h := D_step 47 58; rw [d_47_58, d_48_58, d_49_58] at h; exact h
private theorem d_50_59 : D 50 59 = true := by have h := D_step 48 58; rw [d_48_58, d_49_58, d_50_58] at h; exact h
private theorem d_51_59 : D 51 59 = false := by have h := D_step 49 58; rw [d_49_58, d_50_58, d_51_58] at h; exact h
private theorem d_52_59 : D 52 59 = true := by have h := D_step 50 58; rw [d_50_58, d_51_58, d_52_58] at h; exact h
private theorem d_46_60 : D 46 60 = false := by have h := D_step 44 59; rw [d_44_59, d_45_59, d_46_59] at h; exact h
private theorem d_47_60 : D 47 60 = false := by have h := D_step 45 59; rw [d_45_59, d_46_59, d_47_59] at h; exact h
private theorem d_48_60 : D 48 60 = false := by have h := D_step 46 59; rw [d_46_59, d_47_59, d_48_59] at h; exact h
private theorem d_49_60 : D 49 60 = true := by have h := D_step 47 59; rw [d_47_59, d_48_59, d_49_59] at h; exact h
private theorem d_50_60 : D 50 60 = false := by have h := D_step 48 59; rw [d_48_59, d_49_59, d_50_59] at h; exact h
private theorem d_51_60 : D 51 60 = true := by have h := D_step 49 59; rw [d_49_59, d_50_59, d_51_59] at h; exact h
private theorem d_52_60 : D 52 60 = false := by have h := D_step 50 59; rw [d_50_59, d_51_59, d_52_59] at h; exact h
private theorem d_46_61 : D 46 61 = false := by have h := D_step 44 60; rw [d_44_60, d_45_60, d_46_60] at h; exact h
private theorem d_47_61 : D 47 61 = true := by have h := D_step 45 60; rw [d_45_60, d_46_60, d_47_60] at h; exact h
private theorem d_48_61 : D 48 61 = false := by have h := D_step 46 60; rw [d_46_60, d_47_60, d_48_60] at h; exact h
private theorem d_49_61 : D 49 61 = true := by have h := D_step 47 60; rw [d_47_60, d_48_60, d_49_60] at h; exact h
private theorem d_50_61 : D 50 61 = true := by have h := D_step 48 60; rw [d_48_60, d_49_60, d_50_60] at h; exact h
private theorem d_51_61 : D 51 61 = false := by have h := D_step 49 60; rw [d_49_60, d_50_60, d_51_60] at h; exact h
private theorem d_52_61 : D 52 61 = true := by have h := D_step 50 60; rw [d_50_60, d_51_60, d_52_60] at h; exact h
private theorem d_0_62 : D 0 62 = true := D_zero 62
private theorem d_1_62 : D 1 62 = true := by simpa using D_one 61
private theorem d_2_62 : D 2 62 = false := by have h := D_step 0 61; rw [d_0_61, d_1_61, d_2_61] at h; exact h
private theorem d_3_62 : D 3 62 = false := by have h := D_step 1 61; rw [d_1_61, d_2_61, d_3_61] at h; exact h
private theorem d_4_62 : D 4 62 = true := by have h := D_step 2 61; rw [d_2_61, d_3_61, d_4_61] at h; exact h
private theorem d_5_62 : D 5 62 = false := by have h := D_step 3 61; rw [d_3_61, d_4_61, d_5_61] at h; exact h
private theorem d_6_62 : D 6 62 = false := by have h := D_step 4 61; rw [d_4_61, d_5_61, d_6_61] at h; exact h
private theorem d_7_62 : D 7 62 = false := by have h := D_step 5 61; rw [d_5_61, d_6_61, d_7_61] at h; exact h
private theorem d_8_62 : D 8 62 = false := by have h := D_step 6 61; rw [d_6_61, d_7_61, d_8_61] at h; exact h
private theorem d_9_62 : D 9 62 = true := by have h := D_step 7 61; rw [d_7_61, d_8_61, d_9_61] at h; exact h
private theorem d_10_62 : D 10 62 = false := by have h := D_step 8 61; rw [d_8_61, d_9_61, d_10_61] at h; exact h
private theorem d_11_62 : D 11 62 = true := by have h := D_step 9 61; rw [d_9_61, d_10_61, d_11_61] at h; exact h
private theorem d_12_62 : D 12 62 = true := by have h := D_step 10 61; rw [d_10_61, d_11_61, d_12_61] at h; exact h
private theorem d_13_62 : D 13 62 = true := by have h := D_step 11 61; rw [d_11_61, d_12_61, d_13_61] at h; exact h
private theorem d_14_62 : D 14 62 = false := by have h := D_step 12 61; rw [d_12_61, d_13_61, d_14_61] at h; exact h
private theorem d_15_62 : D 15 62 = false := by have h := D_step 13 61; rw [d_13_61, d_14_61, d_15_61] at h; exact h
private theorem d_16_62 : D 16 62 = true := by have h := D_step 14 61; rw [d_14_61, d_15_61, d_16_61] at h; exact h
private theorem d_17_62 : D 17 62 = false := by have h := D_step 15 61; rw [d_15_61, d_16_61, d_17_61] at h; exact h
private theorem d_18_62 : D 18 62 = true := by have h := D_step 16 61; rw [d_16_61, d_17_61, d_18_61] at h; exact h
private theorem d_19_62 : D 19 62 = true := by have h := D_step 17 61; rw [d_17_61, d_18_61, d_19_61] at h; exact h
private theorem d_20_62 : D 20 62 = false := by have h := D_step 18 61; rw [d_18_61, d_19_61, d_20_61] at h; exact h
private theorem d_21_62 : D 21 62 = true := by have h := D_step 19 61; rw [d_19_61, d_20_61, d_21_61] at h; exact h
private theorem d_22_62 : D 22 62 = false := by have h := D_step 20 61; rw [d_20_61, d_21_61, d_22_61] at h; exact h
private theorem d_23_62 : D 23 62 = true := by have h := D_step 21 61; rw [d_21_61, d_22_61, d_23_61] at h; exact h
private theorem d_24_62 : D 24 62 = false := by have h := D_step 22 61; rw [d_22_61, d_23_61, d_24_61] at h; exact h
private theorem d_25_62 : D 25 62 = false := by have h := D_step 23 61; rw [d_23_61, d_24_61, d_25_61] at h; exact h
private theorem d_26_62 : D 26 62 = true := by have h := D_step 24 61; rw [d_24_61, d_25_61, d_26_61] at h; exact h
private theorem d_27_62 : D 27 62 = true := by have h := D_step 25 61; rw [d_25_61, d_26_61, d_27_61] at h; exact h
private theorem d_28_62 : D 28 62 = false := by have h := D_step 26 61; rw [d_26_61, d_27_61, d_28_61] at h; exact h
private theorem d_29_62 : D 29 62 = true := by have h := D_step 27 61; rw [d_27_61, d_28_61, d_29_61] at h; exact h
private theorem d_30_62 : D 30 62 = true := by have h := D_step 28 61; rw [d_28_61, d_29_61, d_30_61] at h; exact h
private theorem d_31_62 : D 31 62 = true := by have h := D_step 29 61; rw [d_29_61, d_30_61, d_31_61] at h; exact h
private theorem d_32_62 : D 32 62 = false := by have h := D_step 30 61; rw [d_30_61, d_31_61, d_32_61] at h; exact h
private theorem d_33_62 : D 33 62 = false := by have h := D_step 31 61; rw [d_31_61, d_32_61, d_33_61] at h; exact h
private theorem d_34_62 : D 34 62 = false := by have h := D_step 32 61; rw [d_32_61, d_33_61, d_34_61] at h; exact h
private theorem d_35_62 : D 35 62 = true := by have h := D_step 33 61; rw [d_33_61, d_34_61, d_35_61] at h; exact h
private theorem d_36_62 : D 36 62 = false := by have h := D_step 34 61; rw [d_34_61, d_35_61, d_36_61] at h; exact h
private theorem d_37_62 : D 37 62 = false := by have h := D_step 35 61; rw [d_35_61, d_36_61, d_37_61] at h; exact h
private theorem d_38_62 : D 38 62 = true := by have h := D_step 36 61; rw [d_36_61, d_37_61, d_38_61] at h; exact h
private theorem d_39_62 : D 39 62 = true := by have h := D_step 37 61; rw [d_37_61, d_38_61, d_39_61] at h; exact h
private theorem d_40_62 : D 40 62 = false := by have h := D_step 38 61; rw [d_38_61, d_39_61, d_40_61] at h; exact h
private theorem d_41_62 : D 41 62 = true := by have h := D_step 39 61; rw [d_39_61, d_40_61, d_41_61] at h; exact h
private theorem d_42_62 : D 42 62 = true := by have h := D_step 40 61; rw [d_40_61, d_41_61, d_42_61] at h; exact h
private theorem d_43_62 : D 43 62 = true := by have h := D_step 41 61; rw [d_41_61, d_42_61, d_43_61] at h; exact h
private theorem d_44_62 : D 44 62 = false := by have h := D_step 42 61; rw [d_42_61, d_43_61, d_44_61] at h; exact h
private theorem d_45_62 : D 45 62 = false := by have h := D_step 43 61; rw [d_43_61, d_44_61, d_45_61] at h; exact h
private theorem d_46_62 : D 46 62 = false := by have h := D_step 44 61; rw [d_44_61, d_45_61, d_46_61] at h; exact h
private theorem d_47_62 : D 47 62 = true := by have h := D_step 45 61; rw [d_45_61, d_46_61, d_47_61] at h; exact h
private theorem d_48_62 : D 48 62 = true := by have h := D_step 46 61; rw [d_46_61, d_47_61, d_48_61] at h; exact h
private theorem d_49_62 : D 49 62 = false := by have h := D_step 47 61; rw [d_47_61, d_48_61, d_49_61] at h; exact h
private theorem d_50_62 : D 50 62 = true := by have h := D_step 48 61; rw [d_48_61, d_49_61, d_50_61] at h; exact h
private theorem d_51_62 : D 51 62 = false := by have h := D_step 49 61; rw [d_49_61, d_50_61, d_51_61] at h; exact h
private theorem d_52_62 : D 52 62 = false := by have h := D_step 50 61; rw [d_50_61, d_51_61, d_52_61] at h; exact h
private theorem d_0_63 : D 0 63 = true := D_zero 63
private theorem d_1_63 : D 1 63 = true := by simpa using D_one 62
private theorem d_2_63 : D 2 63 = false := by have h := D_step 0 62; rw [d_0_62, d_1_62, d_2_62] at h; exact h
private theorem d_3_63 : D 3 63 = true := by have h := D_step 1 62; rw [d_1_62, d_2_62, d_3_62] at h; exact h
private theorem d_4_63 : D 4 63 = true := by have h := D_step 2 62; rw [d_2_62, d_3_62, d_4_62] at h; exact h
private theorem d_5_63 : D 5 63 = true := by have h := D_step 3 62; rw [d_3_62, d_4_62, d_5_62] at h; exact h
private theorem d_6_63 : D 6 63 = true := by have h := D_step 4 62; rw [d_4_62, d_5_62, d_6_62] at h; exact h
private theorem d_7_63 : D 7 63 = false := by have h := D_step 5 62; rw [d_5_62, d_6_62, d_7_62] at h; exact h
private theorem d_8_63 : D 8 63 = false := by have h := D_step 6 62; rw [d_6_62, d_7_62, d_8_62] at h; exact h
private theorem d_9_63 : D 9 63 = true := by have h := D_step 7 62; rw [d_7_62, d_8_62, d_9_62] at h; exact h
private theorem d_10_63 : D 10 63 = true := by have h := D_step 8 62; rw [d_8_62, d_9_62, d_10_62] at h; exact h
private theorem d_11_63 : D 11 63 = false := by have h := D_step 9 62; rw [d_9_62, d_10_62, d_11_62] at h; exact h
private theorem d_12_63 : D 12 63 = true := by have h := D_step 10 62; rw [d_10_62, d_11_62, d_12_62] at h; exact h
private theorem d_13_63 : D 13 63 = false := by have h := D_step 11 62; rw [d_11_62, d_12_62, d_13_62] at h; exact h
private theorem d_14_63 : D 14 63 = false := by have h := D_step 12 62; rw [d_12_62, d_13_62, d_14_62] at h; exact h
private theorem d_15_63 : D 15 63 = true := by have h := D_step 13 62; rw [d_13_62, d_14_62, d_15_62] at h; exact h
private theorem d_16_63 : D 16 63 = true := by have h := D_step 14 62; rw [d_14_62, d_15_62, d_16_62] at h; exact h
private theorem d_17_63 : D 17 63 = true := by have h := D_step 15 62; rw [d_15_62, d_16_62, d_17_62] at h; exact h
private theorem d_18_63 : D 18 63 = false := by have h := D_step 16 62; rw [d_16_62, d_17_62, d_18_62] at h; exact h
private theorem d_19_63 : D 19 63 = true := by have h := D_step 17 62; rw [d_17_62, d_18_62, d_19_62] at h; exact h
private theorem d_20_63 : D 20 63 = false := by have h := D_step 18 62; rw [d_18_62, d_19_62, d_20_62] at h; exact h
private theorem d_21_63 : D 21 63 = false := by have h := D_step 19 62; rw [d_19_62, d_20_62, d_21_62] at h; exact h
private theorem d_22_63 : D 22 63 = true := by have h := D_step 20 62; rw [d_20_62, d_21_62, d_22_62] at h; exact h
private theorem d_23_63 : D 23 63 = false := by have h := D_step 21 62; rw [d_21_62, d_22_62, d_23_62] at h; exact h
private theorem d_24_63 : D 24 63 = true := by have h := D_step 22 62; rw [d_22_62, d_23_62, d_24_62] at h; exact h
private theorem d_25_63 : D 25 63 = true := by have h := D_step 23 62; rw [d_23_62, d_24_62, d_25_62] at h; exact h
private theorem d_26_63 : D 26 63 = true := by have h := D_step 24 62; rw [d_24_62, d_25_62, d_26_62] at h; exact h
private theorem d_27_63 : D 27 63 = true := by have h := D_step 25 62; rw [d_25_62, d_26_62, d_27_62] at h; exact h
private theorem d_28_63 : D 28 63 = false := by have h := D_step 26 62; rw [d_26_62, d_27_62, d_28_62] at h; exact h
private theorem d_29_63 : D 29 63 = false := by have h := D_step 27 62; rw [d_27_62, d_28_62, d_29_62] at h; exact h
private theorem d_30_63 : D 30 63 = true := by have h := D_step 28 62; rw [d_28_62, d_29_62, d_30_62] at h; exact h
private theorem d_31_63 : D 31 63 = false := by have h := D_step 29 62; rw [d_29_62, d_30_62, d_31_62] at h; exact h
private theorem d_32_63 : D 32 63 = false := by have h := D_step 30 62; rw [d_30_62, d_31_62, d_32_62] at h; exact h
private theorem d_33_63 : D 33 63 = true := by have h := D_step 31 62; rw [d_31_62, d_32_62, d_33_62] at h; exact h
private theorem d_34_63 : D 34 63 = false := by have h := D_step 32 62; rw [d_32_62, d_33_62, d_34_62] at h; exact h
private theorem d_35_63 : D 35 63 = true := by have h := D_step 33 62; rw [d_33_62, d_34_62, d_35_62] at h; exact h
private theorem d_36_63 : D 36 63 = true := by have h := D_step 34 62; rw [d_34_62, d_35_62, d_36_62] at h; exact h
private theorem d_37_63 : D 37 63 = true := by have h := D_step 35 62; rw [d_35_62, d_36_62, d_37_62] at h; exact h
private theorem d_38_63 : D 38 63 = true := by have h := D_step 36 62; rw [d_36_62, d_37_62, d_38_62] at h; exact h
private theorem d_39_63 : D 39 63 = true := by have h := D_step 37 62; rw [d_37_62, d_38_62, d_39_62] at h; exact h
private theorem d_40_63 : D 40 63 = false := by have h := D_step 38 62; rw [d_38_62, d_39_62, d_40_62] at h; exact h
private theorem d_41_63 : D 41 63 = false := by have h := D_step 39 62; rw [d_39_62, d_40_62, d_41_62] at h; exact h
private theorem d_42_63 : D 42 63 = true := by have h := D_step 40 62; rw [d_40_62, d_41_62, d_42_62] at h; exact h
private theorem d_43_63 : D 43 63 = false := by have h := D_step 41 62; rw [d_41_62, d_42_62, d_43_62] at h; exact h
private theorem d_44_63 : D 44 63 = false := by have h := D_step 42 62; rw [d_42_62, d_43_62, d_44_62] at h; exact h
private theorem d_45_63 : D 45 63 = true := by have h := D_step 43 62; rw [d_43_62, d_44_62, d_45_62] at h; exact h
private theorem d_46_63 : D 46 63 = false := by have h := D_step 44 62; rw [d_44_62, d_45_62, d_46_62] at h; exact h
private theorem d_47_63 : D 47 63 = true := by have h := D_step 45 62; rw [d_45_62, d_46_62, d_47_62] at h; exact h
private theorem d_48_63 : D 48 63 = true := by have h := D_step 46 62; rw [d_46_62, d_47_62, d_48_62] at h; exact h
private theorem d_49_63 : D 49 63 = false := by have h := D_step 47 62; rw [d_47_62, d_48_62, d_49_62] at h; exact h
private theorem d_50_63 : D 50 63 = false := by have h := D_step 48 62; rw [d_48_62, d_49_62, d_50_62] at h; exact h
private theorem d_51_63 : D 51 63 = true := by have h := D_step 49 62; rw [d_49_62, d_50_62, d_51_62] at h; exact h
private theorem d_52_63 : D 52 63 = true := by have h := D_step 50 62; rw [d_50_62, d_51_62, d_52_62] at h; exact h
private theorem d_0_64 : D 0 64 = true := D_zero 64
private theorem d_1_64 : D 1 64 = true := by simpa using D_one 63
private theorem d_2_64 : D 2 64 = false := by have h := D_step 0 63; rw [d_0_63, d_1_63, d_2_63] at h; exact h
private theorem d_3_64 : D 3 64 = false := by have h := D_step 1 63; rw [d_1_63, d_2_63, d_3_63] at h; exact h
private theorem d_4_64 : D 4 64 = true := by have h := D_step 2 63; rw [d_2_63, d_3_63, d_4_63] at h; exact h
private theorem d_5_64 : D 5 64 = false := by have h := D_step 3 63; rw [d_3_63, d_4_63, d_5_63] at h; exact h
private theorem d_6_64 : D 6 64 = false := by have h := D_step 4 63; rw [d_4_63, d_5_63, d_6_63] at h; exact h
private theorem d_7_64 : D 7 64 = false := by have h := D_step 5 63; rw [d_5_63, d_6_63, d_7_63] at h; exact h
private theorem d_8_64 : D 8 64 = true := by have h := D_step 6 63; rw [d_6_63, d_7_63, d_8_63] at h; exact h
private theorem d_9_64 : D 9 64 = true := by have h := D_step 7 63; rw [d_7_63, d_8_63, d_9_63] at h; exact h
private theorem d_10_64 : D 10 64 = true := by have h := D_step 8 63; rw [d_8_63, d_9_63, d_10_63] at h; exact h
private theorem d_11_64 : D 11 64 = false := by have h := D_step 9 63; rw [d_9_63, d_10_63, d_11_63] at h; exact h
private theorem d_12_64 : D 12 64 = false := by have h := D_step 10 63; rw [d_10_63, d_11_63, d_12_63] at h; exact h
private theorem d_13_64 : D 13 64 = true := by have h := D_step 11 63; rw [d_11_63, d_12_63, d_13_63] at h; exact h
private theorem d_14_64 : D 14 64 = true := by have h := D_step 12 63; rw [d_12_63, d_13_63, d_14_63] at h; exact h
private theorem d_15_64 : D 15 64 = true := by have h := D_step 13 63; rw [d_13_63, d_14_63, d_15_63] at h; exact h
private theorem d_16_64 : D 16 64 = true := by have h := D_step 14 63; rw [d_14_63, d_15_63, d_16_63] at h; exact h
private theorem d_17_64 : D 17 64 = false := by have h := D_step 15 63; rw [d_15_63, d_16_63, d_17_63] at h; exact h
private theorem d_18_64 : D 18 64 = false := by have h := D_step 16 63; rw [d_16_63, d_17_63, d_18_63] at h; exact h
private theorem d_19_64 : D 19 64 = false := by have h := D_step 17 63; rw [d_17_63, d_18_63, d_19_63] at h; exact h
private theorem d_20_64 : D 20 64 = true := by have h := D_step 18 63; rw [d_18_63, d_19_63, d_20_63] at h; exact h
private theorem d_21_64 : D 21 64 = true := by have h := D_step 19 63; rw [d_19_63, d_20_63, d_21_63] at h; exact h
private theorem d_22_64 : D 22 64 = true := by have h := D_step 20 63; rw [d_20_63, d_21_63, d_22_63] at h; exact h
private theorem d_23_64 : D 23 64 = true := by have h := D_step 21 63; rw [d_21_63, d_22_63, d_23_63] at h; exact h
private theorem d_24_64 : D 24 64 = false := by have h := D_step 22 63; rw [d_22_63, d_23_63, d_24_63] at h; exact h
private theorem d_25_64 : D 25 64 = true := by have h := D_step 23 63; rw [d_23_63, d_24_63, d_25_63] at h; exact h
private theorem d_26_64 : D 26 64 = false := by have h := D_step 24 63; rw [d_24_63, d_25_63, d_26_63] at h; exact h
private theorem d_27_64 : D 27 64 = false := by have h := D_step 25 63; rw [d_25_63, d_26_63, d_27_63] at h; exact h
private theorem d_28_64 : D 28 64 = false := by have h := D_step 26 63; rw [d_26_63, d_27_63, d_28_63] at h; exact h
private theorem d_29_64 : D 29 64 = true := by have h := D_step 27 63; rw [d_27_63, d_28_63, d_29_63] at h; exact h
private theorem d_30_64 : D 30 64 = true := by have h := D_step 28 63; rw [d_28_63, d_29_63, d_30_63] at h; exact h
private theorem d_31_64 : D 31 64 = true := by have h := D_step 29 63; rw [d_29_63, d_30_63, d_31_63] at h; exact h
private theorem d_32_64 : D 32 64 = true := by have h := D_step 30 63; rw [d_30_63, d_31_63, d_32_63] at h; exact h
private theorem d_33_64 : D 33 64 = true := by have h := D_step 31 63; rw [d_31_63, d_32_63, d_33_63] at h; exact h
private theorem d_34_64 : D 34 64 = true := by have h := D_step 32 63; rw [d_32_63, d_33_63, d_34_63] at h; exact h
private theorem d_35_64 : D 35 64 = false := by have h := D_step 33 63; rw [d_33_63, d_34_63, d_35_63] at h; exact h
private theorem d_36_64 : D 36 64 = true := by have h := D_step 34 63; rw [d_34_63, d_35_63, d_36_63] at h; exact h
private theorem d_37_64 : D 37 64 = false := by have h := D_step 35 63; rw [d_35_63, d_36_63, d_37_63] at h; exact h
private theorem d_38_64 : D 38 64 = false := by have h := D_step 36 63; rw [d_36_63, d_37_63, d_38_63] at h; exact h
private theorem d_39_64 : D 39 64 = false := by have h := D_step 37 63; rw [d_37_63, d_38_63, d_39_63] at h; exact h
private theorem d_40_64 : D 40 64 = false := by have h := D_step 38 63; rw [d_38_63, d_39_63, d_40_63] at h; exact h
private theorem d_41_64 : D 41 64 = true := by have h := D_step 39 63; rw [d_39_63, d_40_63, d_41_63] at h; exact h
private theorem d_42_64 : D 42 64 = true := by have h := D_step 40 63; rw [d_40_63, d_41_63, d_42_63] at h; exact h
private theorem d_43_64 : D 43 64 = true := by have h := D_step 41 63; rw [d_41_63, d_42_63, d_43_63] at h; exact h
private theorem d_44_64 : D 44 64 = true := by have h := D_step 42 63; rw [d_42_63, d_43_63, d_44_63] at h; exact h
private theorem d_45_64 : D 45 64 = true := by have h := D_step 43 63; rw [d_43_63, d_44_63, d_45_63] at h; exact h
private theorem d_46_64 : D 46 64 = true := by have h := D_step 44 63; rw [d_44_63, d_45_63, d_46_63] at h; exact h
private theorem d_47_64 : D 47 64 = false := by have h := D_step 45 63; rw [d_45_63, d_46_63, d_47_63] at h; exact h
private theorem d_48_64 : D 48 64 = true := by have h := D_step 46 63; rw [d_46_63, d_47_63, d_48_63] at h; exact h
private theorem d_49_64 : D 49 64 = false := by have h := D_step 47 63; rw [d_47_63, d_48_63, d_49_63] at h; exact h
private theorem d_50_64 : D 50 64 = true := by have h := D_step 48 63; rw [d_48_63, d_49_63, d_50_63] at h; exact h
private theorem d_51_64 : D 51 64 = true := by have h := D_step 49 63; rw [d_49_63, d_50_63, d_51_63] at h; exact h
private theorem d_52_64 : D 52 64 = true := by have h := D_step 50 63; rw [d_50_63, d_51_63, d_52_63] at h; exact h
private theorem d_0_65 : D 0 65 = true := D_zero 65
private theorem d_1_65 : D 1 65 = true := by simpa using D_one 64
private theorem d_2_65 : D 2 65 = false := by have h := D_step 0 64; rw [d_0_64, d_1_64, d_2_64] at h; exact h
private theorem d_3_65 : D 3 65 = true := by have h := D_step 1 64; rw [d_1_64, d_2_64, d_3_64] at h; exact h
private theorem d_4_65 : D 4 65 = true := by have h := D_step 2 64; rw [d_2_64, d_3_64, d_4_64] at h; exact h
private theorem d_5_65 : D 5 65 = true := by have h := D_step 3 64; rw [d_3_64, d_4_64, d_5_64] at h; exact h
private theorem d_6_65 : D 6 65 = true := by have h := D_step 4 64; rw [d_4_64, d_5_64, d_6_64] at h; exact h
private theorem d_7_65 : D 7 65 = false := by have h := D_step 5 64; rw [d_5_64, d_6_64, d_7_64] at h; exact h
private theorem d_8_65 : D 8 65 = true := by have h := D_step 6 64; rw [d_6_64, d_7_64, d_8_64] at h; exact h
private theorem d_9_65 : D 9 65 = true := by have h := D_step 7 64; rw [d_7_64, d_8_64, d_9_64] at h; exact h
private theorem d_10_65 : D 10 65 = false := by have h := D_step 8 64; rw [d_8_64, d_9_64, d_10_64] at h; exact h
private theorem d_11_65 : D 11 65 = false := by have h := D_step 9 64; rw [d_9_64, d_10_64, d_11_64] at h; exact h
private theorem d_12_65 : D 12 65 = true := by have h := D_step 10 64; rw [d_10_64, d_11_64, d_12_64] at h; exact h
private theorem d_13_65 : D 13 65 = true := by have h := D_step 11 64; rw [d_11_64, d_12_64, d_13_64] at h; exact h
private theorem d_14_65 : D 14 65 = true := by have h := D_step 12 64; rw [d_12_64, d_13_64, d_14_64] at h; exact h
private theorem d_15_65 : D 15 65 = false := by have h := D_step 13 64; rw [d_13_64, d_14_64, d_15_64] at h; exact h
private theorem d_16_65 : D 16 65 = false := by have h := D_step 14 64; rw [d_14_64, d_15_64, d_16_64] at h; exact h
private theorem d_17_65 : D 17 65 = false := by have h := D_step 15 64; rw [d_15_64, d_16_64, d_17_64] at h; exact h
private theorem d_18_65 : D 18 65 = true := by have h := D_step 16 64; rw [d_16_64, d_17_64, d_18_64] at h; exact h
private theorem d_19_65 : D 19 65 = false := by have h := D_step 17 64; rw [d_17_64, d_18_64, d_19_64] at h; exact h
private theorem d_20_65 : D 20 65 = true := by have h := D_step 18 64; rw [d_18_64, d_19_64, d_20_64] at h; exact h
private theorem d_21_65 : D 21 65 = true := by have h := D_step 19 64; rw [d_19_64, d_20_64, d_21_64] at h; exact h
private theorem d_22_65 : D 22 65 = false := by have h := D_step 20 64; rw [d_20_64, d_21_64, d_22_64] at h; exact h
private theorem d_23_65 : D 23 65 = false := by have h := D_step 21 64; rw [d_21_64, d_22_64, d_23_64] at h; exact h
private theorem d_24_65 : D 24 65 = false := by have h := D_step 22 64; rw [d_22_64, d_23_64, d_24_64] at h; exact h
private theorem d_25_65 : D 25 65 = false := by have h := D_step 23 64; rw [d_23_64, d_24_64, d_25_64] at h; exact h
private theorem d_26_65 : D 26 65 = true := by have h := D_step 24 64; rw [d_24_64, d_25_64, d_26_64] at h; exact h
private theorem d_27_65 : D 27 65 = true := by have h := D_step 25 64; rw [d_25_64, d_26_64, d_27_64] at h; exact h
private theorem d_28_65 : D 28 65 = false := by have h := D_step 26 64; rw [d_26_64, d_27_64, d_28_64] at h; exact h
private theorem d_29_65 : D 29 65 = true := by have h := D_step 27 64; rw [d_27_64, d_28_64, d_29_64] at h; exact h
private theorem d_30_65 : D 30 65 = true := by have h := D_step 28 64; rw [d_28_64, d_29_64, d_30_64] at h; exact h
private theorem d_31_65 : D 31 65 = false := by have h := D_step 29 64; rw [d_29_64, d_30_64, d_31_64] at h; exact h
private theorem d_32_65 : D 32 65 = false := by have h := D_step 30 64; rw [d_30_64, d_31_64, d_32_64] at h; exact h
private theorem d_33_65 : D 33 65 = false := by have h := D_step 31 64; rw [d_31_64, d_32_64, d_33_64] at h; exact h
private theorem d_34_65 : D 34 65 = false := by have h := D_step 32 64; rw [d_32_64, d_33_64, d_34_64] at h; exact h
private theorem d_35_65 : D 35 65 = false := by have h := D_step 33 64; rw [d_33_64, d_34_64, d_35_64] at h; exact h
private theorem d_36_65 : D 36 65 = false := by have h := D_step 34 64; rw [d_34_64, d_35_64, d_36_64] at h; exact h
private theorem d_37_65 : D 37 65 = true := by have h := D_step 35 64; rw [d_35_64, d_36_64, d_37_64] at h; exact h
private theorem d_38_65 : D 38 65 = true := by have h := D_step 36 64; rw [d_36_64, d_37_64, d_38_64] at h; exact h
private theorem d_39_65 : D 39 65 = false := by have h := D_step 37 64; rw [d_37_64, d_38_64, d_39_64] at h; exact h
private theorem d_40_65 : D 40 65 = false := by have h := D_step 38 64; rw [d_38_64, d_39_64, d_40_64] at h; exact h
private theorem d_41_65 : D 41 65 = true := by have h := D_step 39 64; rw [d_39_64, d_40_64, d_41_64] at h; exact h
private theorem d_42_65 : D 42 65 = true := by have h := D_step 40 64; rw [d_40_64, d_41_64, d_42_64] at h; exact h
private theorem d_43_65 : D 43 65 = false := by have h := D_step 41 64; rw [d_41_64, d_42_64, d_43_64] at h; exact h
private theorem d_44_65 : D 44 65 = false := by have h := D_step 42 64; rw [d_42_64, d_43_64, d_44_64] at h; exact h
private theorem d_45_65 : D 45 65 = false := by have h := D_step 43 64; rw [d_43_64, d_44_64, d_45_64] at h; exact h
private theorem d_46_65 : D 46 65 = false := by have h := D_step 44 64; rw [d_44_64, d_45_64, d_46_64] at h; exact h
private theorem d_47_65 : D 47 65 = false := by have h := D_step 45 64; rw [d_45_64, d_46_64, d_47_64] at h; exact h
private theorem d_48_65 : D 48 65 = false := by have h := D_step 46 64; rw [d_46_64, d_47_64, d_48_64] at h; exact h
private theorem d_49_65 : D 49 65 = true := by have h := D_step 47 64; rw [d_47_64, d_48_64, d_49_64] at h; exact h
private theorem d_50_65 : D 50 65 = false := by have h := D_step 48 64; rw [d_48_64, d_49_64, d_50_64] at h; exact h
private theorem d_51_65 : D 51 65 = true := by have h := D_step 49 64; rw [d_49_64, d_50_64, d_51_64] at h; exact h
private theorem d_52_65 : D 52 65 = false := by have h := D_step 50 64; rw [d_50_64, d_51_64, d_52_64] at h; exact h
private theorem d_0_66 : D 0 66 = true := D_zero 66
private theorem d_1_66 : D 1 66 = true := by simpa using D_one 65
private theorem d_2_66 : D 2 66 = false := by have h := D_step 0 65; rw [d_0_65, d_1_65, d_2_65] at h; exact h
private theorem d_3_66 : D 3 66 = false := by have h := D_step 1 65; rw [d_1_65, d_2_65, d_3_65] at h; exact h
private theorem d_4_66 : D 4 66 = true := by have h := D_step 2 65; rw [d_2_65, d_3_65, d_4_65] at h; exact h
private theorem d_5_66 : D 5 66 = false := by have h := D_step 3 65; rw [d_3_65, d_4_65, d_5_65] at h; exact h
private theorem d_6_66 : D 6 66 = false := by have h := D_step 4 65; rw [d_4_65, d_5_65, d_6_65] at h; exact h
private theorem d_7_66 : D 7 66 = false := by have h := D_step 5 65; rw [d_5_65, d_6_65, d_7_65] at h; exact h
private theorem d_8_66 : D 8 66 = false := by have h := D_step 6 65; rw [d_6_65, d_7_65, d_8_65] at h; exact h
private theorem d_9_66 : D 9 66 = true := by have h := D_step 7 65; rw [d_7_65, d_8_65, d_9_65] at h; exact h
private theorem d_10_66 : D 10 66 = false := by have h := D_step 8 65; rw [d_8_65, d_9_65, d_10_65] at h; exact h
private theorem d_11_66 : D 11 66 = true := by have h := D_step 9 65; rw [d_9_65, d_10_65, d_11_65] at h; exact h
private theorem d_12_66 : D 12 66 = true := by have h := D_step 10 65; rw [d_10_65, d_11_65, d_12_65] at h; exact h
private theorem d_13_66 : D 13 66 = true := by have h := D_step 11 65; rw [d_11_65, d_12_65, d_13_65] at h; exact h
private theorem d_14_66 : D 14 66 = false := by have h := D_step 12 65; rw [d_12_65, d_13_65, d_14_65] at h; exact h
private theorem d_15_66 : D 15 66 = false := by have h := D_step 13 65; rw [d_13_65, d_14_65, d_15_65] at h; exact h
private theorem d_16_66 : D 16 66 = true := by have h := D_step 14 65; rw [d_14_65, d_15_65, d_16_65] at h; exact h
private theorem d_17_66 : D 17 66 = false := by have h := D_step 15 65; rw [d_15_65, d_16_65, d_17_65] at h; exact h
private theorem d_18_66 : D 18 66 = true := by have h := D_step 16 65; rw [d_16_65, d_17_65, d_18_65] at h; exact h
private theorem d_19_66 : D 19 66 = true := by have h := D_step 17 65; rw [d_17_65, d_18_65, d_19_65] at h; exact h
private theorem d_20_66 : D 20 66 = false := by have h := D_step 18 65; rw [d_18_65, d_19_65, d_20_65] at h; exact h
private theorem d_21_66 : D 21 66 = true := by have h := D_step 19 65; rw [d_19_65, d_20_65, d_21_65] at h; exact h
private theorem d_22_66 : D 22 66 = false := by have h := D_step 20 65; rw [d_20_65, d_21_65, d_22_65] at h; exact h
private theorem d_23_66 : D 23 66 = true := by have h := D_step 21 65; rw [d_21_65, d_22_65, d_23_65] at h; exact h
private theorem d_24_66 : D 24 66 = false := by have h := D_step 22 65; rw [d_22_65, d_23_65, d_24_65] at h; exact h
private theorem d_25_66 : D 25 66 = false := by have h := D_step 23 65; rw [d_23_65, d_24_65, d_25_65] at h; exact h
private theorem d_26_66 : D 26 66 = true := by have h := D_step 24 65; rw [d_24_65, d_25_65, d_26_65] at h; exact h
private theorem d_27_66 : D 27 66 = true := by have h := D_step 25 65; rw [d_25_65, d_26_65, d_27_65] at h; exact h
private theorem d_28_66 : D 28 66 = false := by have h := D_step 26 65; rw [d_26_65, d_27_65, d_28_65] at h; exact h
private theorem d_29_66 : D 29 66 = false := by have h := D_step 27 65; rw [d_27_65, d_28_65, d_29_65] at h; exact h
private theorem d_30_66 : D 30 66 = true := by have h := D_step 28 65; rw [d_28_65, d_29_65, d_30_65] at h; exact h
private theorem d_31_66 : D 31 66 = false := by have h := D_step 29 65; rw [d_29_65, d_30_65, d_31_65] at h; exact h
private theorem d_32_66 : D 32 66 = true := by have h := D_step 30 65; rw [d_30_65, d_31_65, d_32_65] at h; exact h
private theorem d_33_66 : D 33 66 = false := by have h := D_step 31 65; rw [d_31_65, d_32_65, d_33_65] at h; exact h
private theorem d_34_66 : D 34 66 = false := by have h := D_step 32 65; rw [d_32_65, d_33_65, d_34_65] at h; exact h
private theorem d_35_66 : D 35 66 = false := by have h := D_step 33 65; rw [d_33_65, d_34_65, d_35_65] at h; exact h
private theorem d_36_66 : D 36 66 = false := by have h := D_step 34 65; rw [d_34_65, d_35_65, d_36_65] at h; exact h
private theorem d_37_66 : D 37 66 = true := by have h := D_step 35 65; rw [d_35_65, d_36_65, d_37_65] at h; exact h
private theorem d_38_66 : D 38 66 = true := by have h := D_step 36 65; rw [d_36_65, d_37_65, d_38_65] at h; exact h
private theorem d_39_66 : D 39 66 = false := by have h := D_step 37 65; rw [d_37_65, d_38_65, d_39_65] at h; exact h
private theorem d_40_66 : D 40 66 = true := by have h := D_step 38 65; rw [d_38_65, d_39_65, d_40_65] at h; exact h
private theorem d_41_66 : D 41 66 = true := by have h := D_step 39 65; rw [d_39_65, d_40_65, d_41_65] at h; exact h
private theorem d_42_66 : D 42 66 = true := by have h := D_step 40 65; rw [d_40_65, d_41_65, d_42_65] at h; exact h
private theorem d_43_66 : D 43 66 = false := by have h := D_step 41 65; rw [d_41_65, d_42_65, d_43_65] at h; exact h
private theorem d_44_66 : D 44 66 = true := by have h := D_step 42 65; rw [d_42_65, d_43_65, d_44_65] at h; exact h
private theorem d_45_66 : D 45 66 = false := by have h := D_step 43 65; rw [d_43_65, d_44_65, d_45_65] at h; exact h
private theorem d_46_66 : D 46 66 = false := by have h := D_step 44 65; rw [d_44_65, d_45_65, d_46_65] at h; exact h
private theorem d_47_66 : D 47 66 = false := by have h := D_step 45 65; rw [d_45_65, d_46_65, d_47_65] at h; exact h
private theorem d_48_66 : D 48 66 = false := by have h := D_step 46 65; rw [d_46_65, d_47_65, d_48_65] at h; exact h
private theorem d_49_66 : D 49 66 = true := by have h := D_step 47 65; rw [d_47_65, d_48_65, d_49_65] at h; exact h
private theorem d_50_66 : D 50 66 = true := by have h := D_step 48 65; rw [d_48_65, d_49_65, d_50_65] at h; exact h
private theorem d_51_66 : D 51 66 = false := by have h := D_step 49 65; rw [d_49_65, d_50_65, d_51_65] at h; exact h
private theorem d_52_66 : D 52 66 = true := by have h := D_step 50 65; rw [d_50_65, d_51_65, d_52_65] at h; exact h
private theorem d_0_67 : D 0 67 = true := D_zero 67
private theorem d_1_67 : D 1 67 = true := by simpa using D_one 66
private theorem d_2_67 : D 2 67 = false := by have h := D_step 0 66; rw [d_0_66, d_1_66, d_2_66] at h; exact h
private theorem d_3_67 : D 3 67 = true := by have h := D_step 1 66; rw [d_1_66, d_2_66, d_3_66] at h; exact h
private theorem d_4_67 : D 4 67 = true := by have h := D_step 2 66; rw [d_2_66, d_3_66, d_4_66] at h; exact h
private theorem d_5_67 : D 5 67 = true := by have h := D_step 3 66; rw [d_3_66, d_4_66, d_5_66] at h; exact h
private theorem d_6_67 : D 6 67 = true := by have h := D_step 4 66; rw [d_4_66, d_5_66, d_6_66] at h; exact h
private theorem d_7_67 : D 7 67 = false := by have h := D_step 5 66; rw [d_5_66, d_6_66, d_7_66] at h; exact h
private theorem d_8_67 : D 8 67 = false := by have h := D_step 6 66; rw [d_6_66, d_7_66, d_8_66] at h; exact h
private theorem d_9_67 : D 9 67 = true := by have h := D_step 7 66; rw [d_7_66, d_8_66, d_9_66] at h; exact h
private theorem d_10_67 : D 10 67 = true := by have h := D_step 8 66; rw [d_8_66, d_9_66, d_10_66] at h; exact h
private theorem d_11_67 : D 11 67 = false := by have h := D_step 9 66; rw [d_9_66, d_10_66, d_11_66] at h; exact h
private theorem d_12_67 : D 12 67 = true := by have h := D_step 10 66; rw [d_10_66, d_11_66, d_12_66] at h; exact h
private theorem d_13_67 : D 13 67 = false := by have h := D_step 11 66; rw [d_11_66, d_12_66, d_13_66] at h; exact h
private theorem d_14_67 : D 14 67 = false := by have h := D_step 12 66; rw [d_12_66, d_13_66, d_14_66] at h; exact h
private theorem d_15_67 : D 15 67 = true := by have h := D_step 13 66; rw [d_13_66, d_14_66, d_15_66] at h; exact h
private theorem d_16_67 : D 16 67 = true := by have h := D_step 14 66; rw [d_14_66, d_15_66, d_16_66] at h; exact h
private theorem d_17_67 : D 17 67 = true := by have h := D_step 15 66; rw [d_15_66, d_16_66, d_17_66] at h; exact h
private theorem d_18_67 : D 18 67 = false := by have h := D_step 16 66; rw [d_16_66, d_17_66, d_18_66] at h; exact h
private theorem d_19_67 : D 19 67 = true := by have h := D_step 17 66; rw [d_17_66, d_18_66, d_19_66] at h; exact h
private theorem d_20_67 : D 20 67 = false := by have h := D_step 18 66; rw [d_18_66, d_19_66, d_20_66] at h; exact h
private theorem d_21_67 : D 21 67 = false := by have h := D_step 19 66; rw [d_19_66, d_20_66, d_21_66] at h; exact h
private theorem d_22_67 : D 22 67 = true := by have h := D_step 20 66; rw [d_20_66, d_21_66, d_22_66] at h; exact h
private theorem d_23_67 : D 23 67 = false := by have h := D_step 21 66; rw [d_21_66, d_22_66, d_23_66] at h; exact h
private theorem d_24_67 : D 24 67 = true := by have h := D_step 22 66; rw [d_22_66, d_23_66, d_24_66] at h; exact h
private theorem d_25_67 : D 25 67 = true := by have h := D_step 23 66; rw [d_23_66, d_24_66, d_25_66] at h; exact h
private theorem d_26_67 : D 26 67 = true := by have h := D_step 24 66; rw [d_24_66, d_25_66, d_26_66] at h; exact h
private theorem d_27_67 : D 27 67 = true := by have h := D_step 25 66; rw [d_25_66, d_26_66, d_27_66] at h; exact h
private theorem d_28_67 : D 28 67 = false := by have h := D_step 26 66; rw [d_26_66, d_27_66, d_28_66] at h; exact h
private theorem d_29_67 : D 29 67 = true := by have h := D_step 27 66; rw [d_27_66, d_28_66, d_29_66] at h; exact h
private theorem d_30_67 : D 30 67 = true := by have h := D_step 28 66; rw [d_28_66, d_29_66, d_30_66] at h; exact h
private theorem d_31_67 : D 31 67 = true := by have h := D_step 29 66; rw [d_29_66, d_30_66, d_31_66] at h; exact h
private theorem d_32_67 : D 32 67 = false := by have h := D_step 30 66; rw [d_30_66, d_31_66, d_32_66] at h; exact h
private theorem d_33_67 : D 33 67 = true := by have h := D_step 31 66; rw [d_31_66, d_32_66, d_33_66] at h; exact h
private theorem d_34_67 : D 34 67 = true := by have h := D_step 32 66; rw [d_32_66, d_33_66, d_34_66] at h; exact h
private theorem d_35_67 : D 35 67 = false := by have h := D_step 33 66; rw [d_33_66, d_34_66, d_35_66] at h; exact h
private theorem d_36_67 : D 36 67 = false := by have h := D_step 34 66; rw [d_34_66, d_35_66, d_36_66] at h; exact h
private theorem d_37_67 : D 37 67 = true := by have h := D_step 35 66; rw [d_35_66, d_36_66, d_37_66] at h; exact h
private theorem d_38_67 : D 38 67 = true := by have h := D_step 36 66; rw [d_36_66, d_37_66, d_38_66] at h; exact h
private theorem d_39_67 : D 39 67 = false := by have h := D_step 37 66; rw [d_37_66, d_38_66, d_39_66] at h; exact h
private theorem d_40_67 : D 40 67 = false := by have h := D_step 38 66; rw [d_38_66, d_39_66, d_40_66] at h; exact h
private theorem d_41_67 : D 41 67 = true := by have h := D_step 39 66; rw [d_39_66, d_40_66, d_41_66] at h; exact h
private theorem d_42_67 : D 42 67 = false := by have h := D_step 40 66; rw [d_40_66, d_41_66, d_42_66] at h; exact h
private theorem d_43_67 : D 43 67 = false := by have h := D_step 41 66; rw [d_41_66, d_42_66, d_43_66] at h; exact h
private theorem d_44_67 : D 44 67 = false := by have h := D_step 42 66; rw [d_42_66, d_43_66, d_44_66] at h; exact h
private theorem d_45_67 : D 45 67 = true := by have h := D_step 43 66; rw [d_43_66, d_44_66, d_45_66] at h; exact h
private theorem d_46_67 : D 46 67 = true := by have h := D_step 44 66; rw [d_44_66, d_45_66, d_46_66] at h; exact h
private theorem d_47_67 : D 47 67 = false := by have h := D_step 45 66; rw [d_45_66, d_46_66, d_47_66] at h; exact h
private theorem d_48_67 : D 48 67 = false := by have h := D_step 46 66; rw [d_46_66, d_47_66, d_48_66] at h; exact h
private theorem d_49_67 : D 49 67 = true := by have h := D_step 47 66; rw [d_47_66, d_48_66, d_49_66] at h; exact h
private theorem d_50_67 : D 50 67 = true := by have h := D_step 48 66; rw [d_48_66, d_49_66, d_50_66] at h; exact h
private theorem d_51_67 : D 51 67 = false := by have h := D_step 49 66; rw [d_49_66, d_50_66, d_51_66] at h; exact h
private theorem d_52_67 : D 52 67 = false := by have h := D_step 50 66; rw [d_50_66, d_51_66, d_52_66] at h; exact h
private theorem d_0_68 : D 0 68 = true := D_zero 68
private theorem d_1_68 : D 1 68 = true := by simpa using D_one 67
private theorem d_2_68 : D 2 68 = false := by have h := D_step 0 67; rw [d_0_67, d_1_67, d_2_67] at h; exact h
private theorem d_3_68 : D 3 68 = false := by have h := D_step 1 67; rw [d_1_67, d_2_67, d_3_67] at h; exact h
private theorem d_4_68 : D 4 68 = true := by have h := D_step 2 67; rw [d_2_67, d_3_67, d_4_67] at h; exact h
private theorem d_5_68 : D 5 68 = false := by have h := D_step 3 67; rw [d_3_67, d_4_67, d_5_67] at h; exact h
private theorem d_6_68 : D 6 68 = false := by have h := D_step 4 67; rw [d_4_67, d_5_67, d_6_67] at h; exact h
private theorem d_7_68 : D 7 68 = false := by have h := D_step 5 67; rw [d_5_67, d_6_67, d_7_67] at h; exact h
private theorem d_8_68 : D 8 68 = true := by have h := D_step 6 67; rw [d_6_67, d_7_67, d_8_67] at h; exact h
private theorem d_9_68 : D 9 68 = true := by have h := D_step 7 67; rw [d_7_67, d_8_67, d_9_67] at h; exact h
private theorem d_10_68 : D 10 68 = true := by have h := D_step 8 67; rw [d_8_67, d_9_67, d_10_67] at h; exact h
private theorem d_11_68 : D 11 68 = false := by have h := D_step 9 67; rw [d_9_67, d_10_67, d_11_67] at h; exact h
private theorem d_12_68 : D 12 68 = false := by have h := D_step 10 67; rw [d_10_67, d_11_67, d_12_67] at h; exact h
private theorem d_13_68 : D 13 68 = true := by have h := D_step 11 67; rw [d_11_67, d_12_67, d_13_67] at h; exact h
private theorem d_14_68 : D 14 68 = true := by have h := D_step 12 67; rw [d_12_67, d_13_67, d_14_67] at h; exact h
private theorem d_15_68 : D 15 68 = true := by have h := D_step 13 67; rw [d_13_67, d_14_67, d_15_67] at h; exact h
private theorem d_16_68 : D 16 68 = true := by have h := D_step 14 67; rw [d_14_67, d_15_67, d_16_67] at h; exact h
private theorem d_17_68 : D 17 68 = false := by have h := D_step 15 67; rw [d_15_67, d_16_67, d_17_67] at h; exact h
private theorem d_18_68 : D 18 68 = false := by have h := D_step 16 67; rw [d_16_67, d_17_67, d_18_67] at h; exact h
private theorem d_19_68 : D 19 68 = false := by have h := D_step 17 67; rw [d_17_67, d_18_67, d_19_67] at h; exact h
private theorem d_20_68 : D 20 68 = true := by have h := D_step 18 67; rw [d_18_67, d_19_67, d_20_67] at h; exact h
private theorem d_21_68 : D 21 68 = true := by have h := D_step 19 67; rw [d_19_67, d_20_67, d_21_67] at h; exact h
private theorem d_22_68 : D 22 68 = true := by have h := D_step 20 67; rw [d_20_67, d_21_67, d_22_67] at h; exact h
private theorem d_23_68 : D 23 68 = true := by have h := D_step 21 67; rw [d_21_67, d_22_67, d_23_67] at h; exact h
private theorem d_24_68 : D 24 68 = false := by have h := D_step 22 67; rw [d_22_67, d_23_67, d_24_67] at h; exact h
private theorem d_25_68 : D 25 68 = true := by have h := D_step 23 67; rw [d_23_67, d_24_67, d_25_67] at h; exact h
private theorem d_26_68 : D 26 68 = false := by have h := D_step 24 67; rw [d_24_67, d_25_67, d_26_67] at h; exact h
private theorem d_27_68 : D 27 68 = false := by have h := D_step 25 67; rw [d_25_67, d_26_67, d_27_67] at h; exact h
private theorem d_28_68 : D 28 68 = false := by have h := D_step 26 67; rw [d_26_67, d_27_67, d_28_67] at h; exact h
private theorem d_29_68 : D 29 68 = false := by have h := D_step 27 67; rw [d_27_67, d_28_67, d_29_67] at h; exact h
private theorem d_30_68 : D 30 68 = true := by have h := D_step 28 67; rw [d_28_67, d_29_67, d_30_67] at h; exact h
private theorem d_31_68 : D 31 68 = false := by have h := D_step 29 67; rw [d_29_67, d_30_67, d_31_67] at h; exact h
private theorem d_32_68 : D 32 68 = false := by have h := D_step 30 67; rw [d_30_67, d_31_67, d_32_67] at h; exact h
private theorem d_33_68 : D 33 68 = false := by have h := D_step 31 67; rw [d_31_67, d_32_67, d_33_67] at h; exact h
private theorem d_34_68 : D 34 68 = true := by have h := D_step 32 67; rw [d_32_67, d_33_67, d_34_67] at h; exact h
private theorem d_35_68 : D 35 68 = false := by have h := D_step 33 67; rw [d_33_67, d_34_67, d_35_67] at h; exact h
private theorem d_36_68 : D 36 68 = true := by have h := D_step 34 67; rw [d_34_67, d_35_67, d_36_67] at h; exact h
private theorem d_37_68 : D 37 68 = true := by have h := D_step 35 67; rw [d_35_67, d_36_67, d_37_67] at h; exact h
private theorem d_38_68 : D 38 68 = true := by have h := D_step 36 67; rw [d_36_67, d_37_67, d_38_67] at h; exact h
private theorem d_39_68 : D 39 68 = false := by have h := D_step 37 67; rw [d_37_67, d_38_67, d_39_67] at h; exact h
private theorem d_40_68 : D 40 68 = true := by have h := D_step 38 67; rw [d_38_67, d_39_67, d_40_67] at h; exact h
private theorem d_41_68 : D 41 68 = true := by have h := D_step 39 67; rw [d_39_67, d_40_67, d_41_67] at h; exact h
private theorem d_42_68 : D 42 68 = true := by have h := D_step 40 67; rw [d_40_67, d_41_67, d_42_67] at h; exact h
private theorem d_43_68 : D 43 68 = true := by have h := D_step 41 67; rw [d_41_67, d_42_67, d_43_67] at h; exact h
private theorem d_44_68 : D 44 68 = false := by have h := D_step 42 67; rw [d_42_67, d_43_67, d_44_67] at h; exact h
private theorem d_45_68 : D 45 68 = true := by have h := D_step 43 67; rw [d_43_67, d_44_67, d_45_67] at h; exact h
private theorem d_46_68 : D 46 68 = true := by have h := D_step 44 67; rw [d_44_67, d_45_67, d_46_67] at h; exact h
private theorem d_47_68 : D 47 68 = false := by have h := D_step 45 67; rw [d_45_67, d_46_67, d_47_67] at h; exact h
private theorem d_48_68 : D 48 68 = true := by have h := D_step 46 67; rw [d_46_67, d_47_67, d_48_67] at h; exact h
private theorem d_49_68 : D 49 68 = true := by have h := D_step 47 67; rw [d_47_67, d_48_67, d_49_67] at h; exact h
private theorem d_50_68 : D 50 68 = true := by have h := D_step 48 67; rw [d_48_67, d_49_67, d_50_67] at h; exact h
private theorem d_51_68 : D 51 68 = false := by have h := D_step 49 67; rw [d_49_67, d_50_67, d_51_67] at h; exact h
private theorem d_52_68 : D 52 68 = true := by have h := D_step 50 67; rw [d_50_67, d_51_67, d_52_67] at h; exact h
private theorem d_0_69 : D 0 69 = true := D_zero 69
private theorem d_1_69 : D 1 69 = true := by simpa using D_one 68
private theorem d_2_69 : D 2 69 = false := by have h := D_step 0 68; rw [d_0_68, d_1_68, d_2_68] at h; exact h
private theorem d_3_69 : D 3 69 = true := by have h := D_step 1 68; rw [d_1_68, d_2_68, d_3_68] at h; exact h
private theorem d_4_69 : D 4 69 = true := by have h := D_step 2 68; rw [d_2_68, d_3_68, d_4_68] at h; exact h
private theorem d_5_69 : D 5 69 = true := by have h := D_step 3 68; rw [d_3_68, d_4_68, d_5_68] at h; exact h
private theorem d_6_69 : D 6 69 = true := by have h := D_step 4 68; rw [d_4_68, d_5_68, d_6_68] at h; exact h
private theorem d_7_69 : D 7 69 = false := by have h := D_step 5 68; rw [d_5_68, d_6_68, d_7_68] at h; exact h
private theorem d_8_69 : D 8 69 = true := by have h := D_step 6 68; rw [d_6_68, d_7_68, d_8_68] at h; exact h
private theorem d_9_69 : D 9 69 = true := by have h := D_step 7 68; rw [d_7_68, d_8_68, d_9_68] at h; exact h
private theorem d_10_69 : D 10 69 = false := by have h := D_step 8 68; rw [d_8_68, d_9_68, d_10_68] at h; exact h
private theorem d_11_69 : D 11 69 = false := by have h := D_step 9 68; rw [d_9_68, d_10_68, d_11_68] at h; exact h
private theorem d_12_69 : D 12 69 = true := by have h := D_step 10 68; rw [d_10_68, d_11_68, d_12_68] at h; exact h
private theorem d_13_69 : D 13 69 = true := by have h := D_step 11 68; rw [d_11_68, d_12_68, d_13_68] at h; exact h
private theorem d_14_69 : D 14 69 = true := by have h := D_step 12 68; rw [d_12_68, d_13_68, d_14_68] at h; exact h
private theorem d_15_69 : D 15 69 = false := by have h := D_step 13 68; rw [d_13_68, d_14_68, d_15_68] at h; exact h
private theorem d_16_69 : D 16 69 = false := by have h := D_step 14 68; rw [d_14_68, d_15_68, d_16_68] at h; exact h
private theorem d_17_69 : D 17 69 = false := by have h := D_step 15 68; rw [d_15_68, d_16_68, d_17_68] at h; exact h
private theorem d_18_69 : D 18 69 = true := by have h := D_step 16 68; rw [d_16_68, d_17_68, d_18_68] at h; exact h
private theorem d_19_69 : D 19 69 = false := by have h := D_step 17 68; rw [d_17_68, d_18_68, d_19_68] at h; exact h
private theorem d_20_69 : D 20 69 = true := by have h := D_step 18 68; rw [d_18_68, d_19_68, d_20_68] at h; exact h
private theorem d_21_69 : D 21 69 = true := by have h := D_step 19 68; rw [d_19_68, d_20_68, d_21_68] at h; exact h
private theorem d_22_69 : D 22 69 = false := by have h := D_step 20 68; rw [d_20_68, d_21_68, d_22_68] at h; exact h
private theorem d_23_69 : D 23 69 = false := by have h := D_step 21 68; rw [d_21_68, d_22_68, d_23_68] at h; exact h
private theorem d_24_69 : D 24 69 = false := by have h := D_step 22 68; rw [d_22_68, d_23_68, d_24_68] at h; exact h
private theorem d_25_69 : D 25 69 = false := by have h := D_step 23 68; rw [d_23_68, d_24_68, d_25_68] at h; exact h
private theorem d_26_69 : D 26 69 = true := by have h := D_step 24 68; rw [d_24_68, d_25_68, d_26_68] at h; exact h
private theorem d_27_69 : D 27 69 = true := by have h := D_step 25 68; rw [d_25_68, d_26_68, d_27_68] at h; exact h
private theorem d_28_69 : D 28 69 = false := by have h := D_step 26 68; rw [d_26_68, d_27_68, d_28_68] at h; exact h
private theorem d_29_69 : D 29 69 = false := by have h := D_step 27 68; rw [d_27_68, d_28_68, d_29_68] at h; exact h
private theorem d_30_69 : D 30 69 = true := by have h := D_step 28 68; rw [d_28_68, d_29_68, d_30_68] at h; exact h
private theorem d_31_69 : D 31 69 = true := by have h := D_step 29 68; rw [d_29_68, d_30_68, d_31_68] at h; exact h
private theorem d_32_69 : D 32 69 = true := by have h := D_step 30 68; rw [d_30_68, d_31_68, d_32_68] at h; exact h
private theorem d_33_69 : D 33 69 = false := by have h := D_step 31 68; rw [d_31_68, d_32_68, d_33_68] at h; exact h
private theorem d_34_69 : D 34 69 = true := by have h := D_step 32 68; rw [d_32_68, d_33_68, d_34_68] at h; exact h
private theorem d_35_69 : D 35 69 = true := by have h := D_step 33 68; rw [d_33_68, d_34_68, d_35_68] at h; exact h
private theorem d_36_69 : D 36 69 = false := by have h := D_step 34 68; rw [d_34_68, d_35_68, d_36_68] at h; exact h
private theorem d_37_69 : D 37 69 = true := by have h := D_step 35 68; rw [d_35_68, d_36_68, d_37_68] at h; exact h
private theorem d_38_69 : D 38 69 = false := by have h := D_step 36 68; rw [d_36_68, d_37_68, d_38_68] at h; exact h
private theorem d_39_69 : D 39 69 = false := by have h := D_step 37 68; rw [d_37_68, d_38_68, d_39_68] at h; exact h
private theorem d_40_69 : D 40 69 = false := by have h := D_step 38 68; rw [d_38_68, d_39_68, d_40_68] at h; exact h
private theorem d_41_69 : D 41 69 = true := by have h := D_step 39 68; rw [d_39_68, d_40_68, d_41_68] at h; exact h
private theorem d_42_69 : D 42 69 = false := by have h := D_step 40 68; rw [d_40_68, d_41_68, d_42_68] at h; exact h
private theorem d_43_69 : D 43 69 = false := by have h := D_step 41 68; rw [d_41_68, d_42_68, d_43_68] at h; exact h
private theorem d_44_69 : D 44 69 = false := by have h := D_step 42 68; rw [d_42_68, d_43_68, d_44_68] at h; exact h
private theorem d_45_69 : D 45 69 = false := by have h := D_step 43 68; rw [d_43_68, d_44_68, d_45_68] at h; exact h
private theorem d_46_69 : D 46 69 = true := by have h := D_step 44 68; rw [d_44_68, d_45_68, d_46_68] at h; exact h
private theorem d_47_69 : D 47 69 = false := by have h := D_step 45 68; rw [d_45_68, d_46_68, d_47_68] at h; exact h
private theorem d_48_69 : D 48 69 = false := by have h := D_step 46 68; rw [d_46_68, d_47_68, d_48_68] at h; exact h
private theorem d_49_69 : D 49 69 = true := by have h := D_step 47 68; rw [d_47_68, d_48_68, d_49_68] at h; exact h
private theorem d_50_69 : D 50 69 = false := by have h := D_step 48 68; rw [d_48_68, d_49_68, d_50_68] at h; exact h
private theorem d_51_69 : D 51 69 = false := by have h := D_step 49 68; rw [d_49_68, d_50_68, d_51_68] at h; exact h
private theorem d_52_69 : D 52 69 = false := by have h := D_step 50 68; rw [d_50_68, d_51_68, d_52_68] at h; exact h
private theorem d_0_70 : D 0 70 = true := D_zero 70
private theorem d_1_70 : D 1 70 = true := by simpa using D_one 69
private theorem d_2_70 : D 2 70 = false := by have h := D_step 0 69; rw [d_0_69, d_1_69, d_2_69] at h; exact h
private theorem d_3_70 : D 3 70 = false := by have h := D_step 1 69; rw [d_1_69, d_2_69, d_3_69] at h; exact h
private theorem d_4_70 : D 4 70 = true := by have h := D_step 2 69; rw [d_2_69, d_3_69, d_4_69] at h; exact h
private theorem d_5_70 : D 5 70 = false := by have h := D_step 3 69; rw [d_3_69, d_4_69, d_5_69] at h; exact h
private theorem d_6_70 : D 6 70 = false := by have h := D_step 4 69; rw [d_4_69, d_5_69, d_6_69] at h; exact h
private theorem d_7_70 : D 7 70 = false := by have h := D_step 5 69; rw [d_5_69, d_6_69, d_7_69] at h; exact h
private theorem d_8_70 : D 8 70 = false := by have h := D_step 6 69; rw [d_6_69, d_7_69, d_8_69] at h; exact h
private theorem d_9_70 : D 9 70 = true := by have h := D_step 7 69; rw [d_7_69, d_8_69, d_9_69] at h; exact h
private theorem d_10_70 : D 10 70 = false := by have h := D_step 8 69; rw [d_8_69, d_9_69, d_10_69] at h; exact h
private theorem d_11_70 : D 11 70 = true := by have h := D_step 9 69; rw [d_9_69, d_10_69, d_11_69] at h; exact h
private theorem d_12_70 : D 12 70 = true := by have h := D_step 10 69; rw [d_10_69, d_11_69, d_12_69] at h; exact h
private theorem d_13_70 : D 13 70 = true := by have h := D_step 11 69; rw [d_11_69, d_12_69, d_13_69] at h; exact h
private theorem d_14_70 : D 14 70 = false := by have h := D_step 12 69; rw [d_12_69, d_13_69, d_14_69] at h; exact h
private theorem d_15_70 : D 15 70 = false := by have h := D_step 13 69; rw [d_13_69, d_14_69, d_15_69] at h; exact h
private theorem d_16_70 : D 16 70 = true := by have h := D_step 14 69; rw [d_14_69, d_15_69, d_16_69] at h; exact h
private theorem d_17_70 : D 17 70 = false := by have h := D_step 15 69; rw [d_15_69, d_16_69, d_17_69] at h; exact h
private theorem d_18_70 : D 18 70 = true := by have h := D_step 16 69; rw [d_16_69, d_17_69, d_18_69] at h; exact h
private theorem d_19_70 : D 19 70 = true := by have h := D_step 17 69; rw [d_17_69, d_18_69, d_19_69] at h; exact h
private theorem d_20_70 : D 20 70 = false := by have h := D_step 18 69; rw [d_18_69, d_19_69, d_20_69] at h; exact h
private theorem d_21_70 : D 21 70 = true := by have h := D_step 19 69; rw [d_19_69, d_20_69, d_21_69] at h; exact h
private theorem d_22_70 : D 22 70 = false := by have h := D_step 20 69; rw [d_20_69, d_21_69, d_22_69] at h; exact h
private theorem d_23_70 : D 23 70 = true := by have h := D_step 21 69; rw [d_21_69, d_22_69, d_23_69] at h; exact h
private theorem d_24_70 : D 24 70 = false := by have h := D_step 22 69; rw [d_22_69, d_23_69, d_24_69] at h; exact h
private theorem d_25_70 : D 25 70 = false := by have h := D_step 23 69; rw [d_23_69, d_24_69, d_25_69] at h; exact h
private theorem d_26_70 : D 26 70 = true := by have h := D_step 24 69; rw [d_24_69, d_25_69, d_26_69] at h; exact h
private theorem d_27_70 : D 27 70 = true := by have h := D_step 25 69; rw [d_25_69, d_26_69, d_27_69] at h; exact h
private theorem d_28_70 : D 28 70 = false := by have h := D_step 26 69; rw [d_26_69, d_27_69, d_28_69] at h; exact h
private theorem d_29_70 : D 29 70 = true := by have h := D_step 27 69; rw [d_27_69, d_28_69, d_29_69] at h; exact h
private theorem d_30_70 : D 30 70 = true := by have h := D_step 28 69; rw [d_28_69, d_29_69, d_30_69] at h; exact h
private theorem d_31_70 : D 31 70 = true := by have h := D_step 29 69; rw [d_29_69, d_30_69, d_31_69] at h; exact h
private theorem d_32_70 : D 32 70 = false := by have h := D_step 30 69; rw [d_30_69, d_31_69, d_32_69] at h; exact h
private theorem d_33_70 : D 33 70 = false := by have h := D_step 31 69; rw [d_31_69, d_32_69, d_33_69] at h; exact h
private theorem d_34_70 : D 34 70 = false := by have h := D_step 32 69; rw [d_32_69, d_33_69, d_34_69] at h; exact h
private theorem d_35_70 : D 35 70 = true := by have h := D_step 33 69; rw [d_33_69, d_34_69, d_35_69] at h; exact h
private theorem d_36_70 : D 36 70 = false := by have h := D_step 34 69; rw [d_34_69, d_35_69, d_36_69] at h; exact h
private theorem d_37_70 : D 37 70 = false := by have h := D_step 35 69; rw [d_35_69, d_36_69, d_37_69] at h; exact h
private theorem d_38_70 : D 38 70 = true := by have h := D_step 36 69; rw [d_36_69, d_37_69, d_38_69] at h; exact h
private theorem d_39_70 : D 39 70 = true := by have h := D_step 37 69; rw [d_37_69, d_38_69, d_39_69] at h; exact h
private theorem d_40_70 : D 40 70 = false := by have h := D_step 38 69; rw [d_38_69, d_39_69, d_40_69] at h; exact h
private theorem d_41_70 : D 41 70 = true := by have h := D_step 39 69; rw [d_39_69, d_40_69, d_41_69] at h; exact h
private theorem d_42_70 : D 42 70 = true := by have h := D_step 40 69; rw [d_40_69, d_41_69, d_42_69] at h; exact h
private theorem d_43_70 : D 43 70 = true := by have h := D_step 41 69; rw [d_41_69, d_42_69, d_43_69] at h; exact h
private theorem d_44_70 : D 44 70 = false := by have h := D_step 42 69; rw [d_42_69, d_43_69, d_44_69] at h; exact h
private theorem d_45_70 : D 45 70 = false := by have h := D_step 43 69; rw [d_43_69, d_44_69, d_45_69] at h; exact h
private theorem d_46_70 : D 46 70 = true := by have h := D_step 44 69; rw [d_44_69, d_45_69, d_46_69] at h; exact h
private theorem d_47_70 : D 47 70 = true := by have h := D_step 45 69; rw [d_45_69, d_46_69, d_47_69] at h; exact h
private theorem d_48_70 : D 48 70 = true := by have h := D_step 46 69; rw [d_46_69, d_47_69, d_48_69] at h; exact h
private theorem d_49_70 : D 49 70 = true := by have h := D_step 47 69; rw [d_47_69, d_48_69, d_49_69] at h; exact h
private theorem d_50_70 : D 50 70 = true := by have h := D_step 48 69; rw [d_48_69, d_49_69, d_50_69] at h; exact h
private theorem d_51_70 : D 51 70 = true := by have h := D_step 49 69; rw [d_49_69, d_50_69, d_51_69] at h; exact h
private theorem d_52_70 : D 52 70 = false := by have h := D_step 50 69; rw [d_50_69, d_51_69, d_52_69] at h; exact h
private theorem d_0_71 : D 0 71 = true := D_zero 71
private theorem d_1_71 : D 1 71 = true := by simpa using D_one 70
private theorem d_2_71 : D 2 71 = false := by have h := D_step 0 70; rw [d_0_70, d_1_70, d_2_70] at h; exact h
private theorem d_3_71 : D 3 71 = true := by have h := D_step 1 70; rw [d_1_70, d_2_70, d_3_70] at h; exact h
private theorem d_4_71 : D 4 71 = true := by have h := D_step 2 70; rw [d_2_70, d_3_70, d_4_70] at h; exact h
private theorem d_5_71 : D 5 71 = true := by have h := D_step 3 70; rw [d_3_70, d_4_70, d_5_70] at h; exact h
private theorem d_6_71 : D 6 71 = true := by have h := D_step 4 70; rw [d_4_70, d_5_70, d_6_70] at h; exact h
private theorem d_7_71 : D 7 71 = false := by have h := D_step 5 70; rw [d_5_70, d_6_70, d_7_70] at h; exact h
private theorem d_8_71 : D 8 71 = false := by have h := D_step 6 70; rw [d_6_70, d_7_70, d_8_70] at h; exact h
private theorem d_9_71 : D 9 71 = true := by have h := D_step 7 70; rw [d_7_70, d_8_70, d_9_70] at h; exact h
private theorem d_10_71 : D 10 71 = true := by have h := D_step 8 70; rw [d_8_70, d_9_70, d_10_70] at h; exact h
private theorem d_11_71 : D 11 71 = false := by have h := D_step 9 70; rw [d_9_70, d_10_70, d_11_70] at h; exact h
private theorem d_12_71 : D 12 71 = true := by have h := D_step 10 70; rw [d_10_70, d_11_70, d_12_70] at h; exact h
private theorem d_13_71 : D 13 71 = false := by have h := D_step 11 70; rw [d_11_70, d_12_70, d_13_70] at h; exact h
private theorem d_14_71 : D 14 71 = false := by have h := D_step 12 70; rw [d_12_70, d_13_70, d_14_70] at h; exact h
private theorem d_15_71 : D 15 71 = true := by have h := D_step 13 70; rw [d_13_70, d_14_70, d_15_70] at h; exact h
private theorem d_16_71 : D 16 71 = true := by have h := D_step 14 70; rw [d_14_70, d_15_70, d_16_70] at h; exact h
private theorem d_17_71 : D 17 71 = true := by have h := D_step 15 70; rw [d_15_70, d_16_70, d_17_70] at h; exact h
private theorem d_18_71 : D 18 71 = false := by have h := D_step 16 70; rw [d_16_70, d_17_70, d_18_70] at h; exact h
private theorem d_19_71 : D 19 71 = true := by have h := D_step 17 70; rw [d_17_70, d_18_70, d_19_70] at h; exact h
private theorem d_20_71 : D 20 71 = false := by have h := D_step 18 70; rw [d_18_70, d_19_70, d_20_70] at h; exact h
private theorem d_21_71 : D 21 71 = false := by have h := D_step 19 70; rw [d_19_70, d_20_70, d_21_70] at h; exact h
private theorem d_22_71 : D 22 71 = true := by have h := D_step 20 70; rw [d_20_70, d_21_70, d_22_70] at h; exact h
private theorem d_23_71 : D 23 71 = false := by have h := D_step 21 70; rw [d_21_70, d_22_70, d_23_70] at h; exact h
private theorem d_24_71 : D 24 71 = true := by have h := D_step 22 70; rw [d_22_70, d_23_70, d_24_70] at h; exact h
private theorem d_25_71 : D 25 71 = true := by have h := D_step 23 70; rw [d_23_70, d_24_70, d_25_70] at h; exact h
private theorem d_26_71 : D 26 71 = true := by have h := D_step 24 70; rw [d_24_70, d_25_70, d_26_70] at h; exact h
private theorem d_27_71 : D 27 71 = true := by have h := D_step 25 70; rw [d_25_70, d_26_70, d_27_70] at h; exact h
private theorem d_28_71 : D 28 71 = false := by have h := D_step 26 70; rw [d_26_70, d_27_70, d_28_70] at h; exact h
private theorem d_29_71 : D 29 71 = false := by have h := D_step 27 70; rw [d_27_70, d_28_70, d_29_70] at h; exact h
private theorem d_30_71 : D 30 71 = true := by have h := D_step 28 70; rw [d_28_70, d_29_70, d_30_70] at h; exact h
private theorem d_31_71 : D 31 71 = false := by have h := D_step 29 70; rw [d_29_70, d_30_70, d_31_70] at h; exact h
private theorem d_32_71 : D 32 71 = false := by have h := D_step 30 70; rw [d_30_70, d_31_70, d_32_70] at h; exact h
private theorem d_33_71 : D 33 71 = true := by have h := D_step 31 70; rw [d_31_70, d_32_70, d_33_70] at h; exact h
private theorem d_34_71 : D 34 71 = false := by have h := D_step 32 70; rw [d_32_70, d_33_70, d_34_70] at h; exact h
private theorem d_35_71 : D 35 71 = true := by have h := D_step 33 70; rw [d_33_70, d_34_70, d_35_70] at h; exact h
private theorem d_36_71 : D 36 71 = true := by have h := D_step 34 70; rw [d_34_70, d_35_70, d_36_70] at h; exact h
private theorem d_37_71 : D 37 71 = true := by have h := D_step 35 70; rw [d_35_70, d_36_70, d_37_70] at h; exact h
private theorem d_38_71 : D 38 71 = true := by have h := D_step 36 70; rw [d_36_70, d_37_70, d_38_70] at h; exact h
private theorem d_39_71 : D 39 71 = true := by have h := D_step 37 70; rw [d_37_70, d_38_70, d_39_70] at h; exact h
private theorem d_40_71 : D 40 71 = false := by have h := D_step 38 70; rw [d_38_70, d_39_70, d_40_70] at h; exact h
private theorem d_41_71 : D 41 71 = false := by have h := D_step 39 70; rw [d_39_70, d_40_70, d_41_70] at h; exact h
private theorem d_42_71 : D 42 71 = true := by have h := D_step 40 70; rw [d_40_70, d_41_70, d_42_70] at h; exact h
private theorem d_43_71 : D 43 71 = false := by have h := D_step 41 70; rw [d_41_70, d_42_70, d_43_70] at h; exact h
private theorem d_44_71 : D 44 71 = false := by have h := D_step 42 70; rw [d_42_70, d_43_70, d_44_70] at h; exact h
private theorem d_45_71 : D 45 71 = true := by have h := D_step 43 70; rw [d_43_70, d_44_70, d_45_70] at h; exact h
private theorem d_46_71 : D 46 71 = true := by have h := D_step 44 70; rw [d_44_70, d_45_70, d_46_70] at h; exact h
private theorem d_47_71 : D 47 71 = true := by have h := D_step 45 70; rw [d_45_70, d_46_70, d_47_70] at h; exact h
private theorem d_48_71 : D 48 71 = false := by have h := D_step 46 70; rw [d_46_70, d_47_70, d_48_70] at h; exact h
private theorem d_49_71 : D 49 71 = false := by have h := D_step 47 70; rw [d_47_70, d_48_70, d_49_70] at h; exact h
private theorem d_50_71 : D 50 71 = false := by have h := D_step 48 70; rw [d_48_70, d_49_70, d_50_70] at h; exact h
private theorem d_51_71 : D 51 71 = false := by have h := D_step 49 70; rw [d_49_70, d_50_70, d_51_70] at h; exact h
private theorem d_52_71 : D 52 71 = false := by have h := D_step 50 70; rw [d_50_70, d_51_70, d_52_70] at h; exact h
private theorem d_0_72 : D 0 72 = true := D_zero 72
private theorem d_1_72 : D 1 72 = true := by simpa using D_one 71
private theorem d_2_72 : D 2 72 = false := by have h := D_step 0 71; rw [d_0_71, d_1_71, d_2_71] at h; exact h
private theorem d_3_72 : D 3 72 = false := by have h := D_step 1 71; rw [d_1_71, d_2_71, d_3_71] at h; exact h
private theorem d_4_72 : D 4 72 = true := by have h := D_step 2 71; rw [d_2_71, d_3_71, d_4_71] at h; exact h
private theorem d_5_72 : D 5 72 = false := by have h := D_step 3 71; rw [d_3_71, d_4_71, d_5_71] at h; exact h
private theorem d_6_72 : D 6 72 = false := by have h := D_step 4 71; rw [d_4_71, d_5_71, d_6_71] at h; exact h
private theorem d_7_72 : D 7 72 = false := by have h := D_step 5 71; rw [d_5_71, d_6_71, d_7_71] at h; exact h
private theorem d_8_72 : D 8 72 = true := by have h := D_step 6 71; rw [d_6_71, d_7_71, d_8_71] at h; exact h
private theorem d_9_72 : D 9 72 = true := by have h := D_step 7 71; rw [d_7_71, d_8_71, d_9_71] at h; exact h
private theorem d_10_72 : D 10 72 = true := by have h := D_step 8 71; rw [d_8_71, d_9_71, d_10_71] at h; exact h
private theorem d_11_72 : D 11 72 = false := by have h := D_step 9 71; rw [d_9_71, d_10_71, d_11_71] at h; exact h
private theorem d_12_72 : D 12 72 = false := by have h := D_step 10 71; rw [d_10_71, d_11_71, d_12_71] at h; exact h
private theorem d_13_72 : D 13 72 = true := by have h := D_step 11 71; rw [d_11_71, d_12_71, d_13_71] at h; exact h
private theorem d_14_72 : D 14 72 = true := by have h := D_step 12 71; rw [d_12_71, d_13_71, d_14_71] at h; exact h
private theorem d_15_72 : D 15 72 = true := by have h := D_step 13 71; rw [d_13_71, d_14_71, d_15_71] at h; exact h
private theorem d_16_72 : D 16 72 = true := by have h := D_step 14 71; rw [d_14_71, d_15_71, d_16_71] at h; exact h
private theorem d_17_72 : D 17 72 = false := by have h := D_step 15 71; rw [d_15_71, d_16_71, d_17_71] at h; exact h
private theorem d_18_72 : D 18 72 = false := by have h := D_step 16 71; rw [d_16_71, d_17_71, d_18_71] at h; exact h
private theorem d_19_72 : D 19 72 = false := by have h := D_step 17 71; rw [d_17_71, d_18_71, d_19_71] at h; exact h
private theorem d_20_72 : D 20 72 = true := by have h := D_step 18 71; rw [d_18_71, d_19_71, d_20_71] at h; exact h
private theorem d_21_72 : D 21 72 = true := by have h := D_step 19 71; rw [d_19_71, d_20_71, d_21_71] at h; exact h
private theorem d_22_72 : D 22 72 = true := by have h := D_step 20 71; rw [d_20_71, d_21_71, d_22_71] at h; exact h
private theorem d_23_72 : D 23 72 = true := by have h := D_step 21 71; rw [d_21_71, d_22_71, d_23_71] at h; exact h
private theorem d_24_72 : D 24 72 = false := by have h := D_step 22 71; rw [d_22_71, d_23_71, d_24_71] at h; exact h
private theorem d_25_72 : D 25 72 = true := by have h := D_step 23 71; rw [d_23_71, d_24_71, d_25_71] at h; exact h
private theorem d_26_72 : D 26 72 = false := by have h := D_step 24 71; rw [d_24_71, d_25_71, d_26_71] at h; exact h
private theorem d_27_72 : D 27 72 = false := by have h := D_step 25 71; rw [d_25_71, d_26_71, d_27_71] at h; exact h
private theorem d_28_72 : D 28 72 = false := by have h := D_step 26 71; rw [d_26_71, d_27_71, d_28_71] at h; exact h
private theorem d_29_72 : D 29 72 = true := by have h := D_step 27 71; rw [d_27_71, d_28_71, d_29_71] at h; exact h
private theorem d_30_72 : D 30 72 = true := by have h := D_step 28 71; rw [d_28_71, d_29_71, d_30_71] at h; exact h
private theorem d_31_72 : D 31 72 = true := by have h := D_step 29 71; rw [d_29_71, d_30_71, d_31_71] at h; exact h
private theorem d_32_72 : D 32 72 = true := by have h := D_step 30 71; rw [d_30_71, d_31_71, d_32_71] at h; exact h
private theorem d_33_72 : D 33 72 = true := by have h := D_step 31 71; rw [d_31_71, d_32_71, d_33_71] at h; exact h
private theorem d_34_72 : D 34 72 = true := by have h := D_step 32 71; rw [d_32_71, d_33_71, d_34_71] at h; exact h
private theorem d_35_72 : D 35 72 = false := by have h := D_step 33 71; rw [d_33_71, d_34_71, d_35_71] at h; exact h
private theorem d_36_72 : D 36 72 = true := by have h := D_step 34 71; rw [d_34_71, d_35_71, d_36_71] at h; exact h
private theorem d_37_72 : D 37 72 = false := by have h := D_step 35 71; rw [d_35_71, d_36_71, d_37_71] at h; exact h
private theorem d_38_72 : D 38 72 = false := by have h := D_step 36 71; rw [d_36_71, d_37_71, d_38_71] at h; exact h
private theorem d_39_72 : D 39 72 = false := by have h := D_step 37 71; rw [d_37_71, d_38_71, d_39_71] at h; exact h
private theorem d_40_72 : D 40 72 = false := by have h := D_step 38 71; rw [d_38_71, d_39_71, d_40_71] at h; exact h
private theorem d_41_72 : D 41 72 = true := by have h := D_step 39 71; rw [d_39_71, d_40_71, d_41_71] at h; exact h
private theorem d_42_72 : D 42 72 = true := by have h := D_step 40 71; rw [d_40_71, d_41_71, d_42_71] at h; exact h
private theorem d_43_72 : D 43 72 = true := by have h := D_step 41 71; rw [d_41_71, d_42_71, d_43_71] at h; exact h
private theorem d_44_72 : D 44 72 = true := by have h := D_step 42 71; rw [d_42_71, d_43_71, d_44_71] at h; exact h
private theorem d_45_72 : D 45 72 = true := by have h := D_step 43 71; rw [d_43_71, d_44_71, d_45_71] at h; exact h
private theorem d_46_72 : D 46 72 = true := by have h := D_step 44 71; rw [d_44_71, d_45_71, d_46_71] at h; exact h
private theorem d_47_72 : D 47 72 = false := by have h := D_step 45 71; rw [d_45_71, d_46_71, d_47_71] at h; exact h
private theorem d_48_72 : D 48 72 = false := by have h := D_step 46 71; rw [d_46_71, d_47_71, d_48_71] at h; exact h
private theorem d_49_72 : D 49 72 = true := by have h := D_step 47 71; rw [d_47_71, d_48_71, d_49_71] at h; exact h
private theorem d_50_72 : D 50 72 = false := by have h := D_step 48 71; rw [d_48_71, d_49_71, d_50_71] at h; exact h
private theorem d_51_72 : D 51 72 = false := by have h := D_step 49 71; rw [d_49_71, d_50_71, d_51_71] at h; exact h
private theorem d_52_72 : D 52 72 = false := by have h := D_step 50 71; rw [d_50_71, d_51_71, d_52_71] at h; exact h
private theorem d_0_73 : D 0 73 = true := D_zero 73
private theorem d_1_73 : D 1 73 = true := by simpa using D_one 72
private theorem d_2_73 : D 2 73 = false := by have h := D_step 0 72; rw [d_0_72, d_1_72, d_2_72] at h; exact h
private theorem d_3_73 : D 3 73 = true := by have h := D_step 1 72; rw [d_1_72, d_2_72, d_3_72] at h; exact h
private theorem d_4_73 : D 4 73 = true := by have h := D_step 2 72; rw [d_2_72, d_3_72, d_4_72] at h; exact h
private theorem d_5_73 : D 5 73 = true := by have h := D_step 3 72; rw [d_3_72, d_4_72, d_5_72] at h; exact h
private theorem d_6_73 : D 6 73 = true := by have h := D_step 4 72; rw [d_4_72, d_5_72, d_6_72] at h; exact h
private theorem d_7_73 : D 7 73 = false := by have h := D_step 5 72; rw [d_5_72, d_6_72, d_7_72] at h; exact h
private theorem d_8_73 : D 8 73 = true := by have h := D_step 6 72; rw [d_6_72, d_7_72, d_8_72] at h; exact h
private theorem d_9_73 : D 9 73 = true := by have h := D_step 7 72; rw [d_7_72, d_8_72, d_9_72] at h; exact h
private theorem d_10_73 : D 10 73 = false := by have h := D_step 8 72; rw [d_8_72, d_9_72, d_10_72] at h; exact h
private theorem d_11_73 : D 11 73 = false := by have h := D_step 9 72; rw [d_9_72, d_10_72, d_11_72] at h; exact h
private theorem d_12_73 : D 12 73 = true := by have h := D_step 10 72; rw [d_10_72, d_11_72, d_12_72] at h; exact h
private theorem d_13_73 : D 13 73 = true := by have h := D_step 11 72; rw [d_11_72, d_12_72, d_13_72] at h; exact h
private theorem d_14_73 : D 14 73 = true := by have h := D_step 12 72; rw [d_12_72, d_13_72, d_14_72] at h; exact h
private theorem d_15_73 : D 15 73 = false := by have h := D_step 13 72; rw [d_13_72, d_14_72, d_15_72] at h; exact h
private theorem d_16_73 : D 16 73 = false := by have h := D_step 14 72; rw [d_14_72, d_15_72, d_16_72] at h; exact h
private theorem d_17_73 : D 17 73 = false := by have h := D_step 15 72; rw [d_15_72, d_16_72, d_17_72] at h; exact h
private theorem d_18_73 : D 18 73 = true := by have h := D_step 16 72; rw [d_16_72, d_17_72, d_18_72] at h; exact h
private theorem d_19_73 : D 19 73 = false := by have h := D_step 17 72; rw [d_17_72, d_18_72, d_19_72] at h; exact h
private theorem d_20_73 : D 20 73 = true := by have h := D_step 18 72; rw [d_18_72, d_19_72, d_20_72] at h; exact h
private theorem d_21_73 : D 21 73 = true := by have h := D_step 19 72; rw [d_19_72, d_20_72, d_21_72] at h; exact h
private theorem d_22_73 : D 22 73 = false := by have h := D_step 20 72; rw [d_20_72, d_21_72, d_22_72] at h; exact h
private theorem d_23_73 : D 23 73 = false := by have h := D_step 21 72; rw [d_21_72, d_22_72, d_23_72] at h; exact h
private theorem d_24_73 : D 24 73 = false := by have h := D_step 22 72; rw [d_22_72, d_23_72, d_24_72] at h; exact h
private theorem d_25_73 : D 25 73 = false := by have h := D_step 23 72; rw [d_23_72, d_24_72, d_25_72] at h; exact h
private theorem d_26_73 : D 26 73 = true := by have h := D_step 24 72; rw [d_24_72, d_25_72, d_26_72] at h; exact h
private theorem d_27_73 : D 27 73 = true := by have h := D_step 25 72; rw [d_25_72, d_26_72, d_27_72] at h; exact h
private theorem d_28_73 : D 28 73 = false := by have h := D_step 26 72; rw [d_26_72, d_27_72, d_28_72] at h; exact h
private theorem d_29_73 : D 29 73 = true := by have h := D_step 27 72; rw [d_27_72, d_28_72, d_29_72] at h; exact h
private theorem d_30_73 : D 30 73 = true := by have h := D_step 28 72; rw [d_28_72, d_29_72, d_30_72] at h; exact h
private theorem d_31_73 : D 31 73 = false := by have h := D_step 29 72; rw [d_29_72, d_30_72, d_31_72] at h; exact h
private theorem d_32_73 : D 32 73 = false := by have h := D_step 30 72; rw [d_30_72, d_31_72, d_32_72] at h; exact h
private theorem d_33_73 : D 33 73 = false := by have h := D_step 31 72; rw [d_31_72, d_32_72, d_33_72] at h; exact h
private theorem d_34_73 : D 34 73 = false := by have h := D_step 32 72; rw [d_32_72, d_33_72, d_34_72] at h; exact h
private theorem d_35_73 : D 35 73 = false := by have h := D_step 33 72; rw [d_33_72, d_34_72, d_35_72] at h; exact h
private theorem d_36_73 : D 36 73 = false := by have h := D_step 34 72; rw [d_34_72, d_35_72, d_36_72] at h; exact h
private theorem d_37_73 : D 37 73 = true := by have h := D_step 35 72; rw [d_35_72, d_36_72, d_37_72] at h; exact h
private theorem d_38_73 : D 38 73 = true := by have h := D_step 36 72; rw [d_36_72, d_37_72, d_38_72] at h; exact h
private theorem d_39_73 : D 39 73 = false := by have h := D_step 37 72; rw [d_37_72, d_38_72, d_39_72] at h; exact h
private theorem d_40_73 : D 40 73 = false := by have h := D_step 38 72; rw [d_38_72, d_39_72, d_40_72] at h; exact h
private theorem d_41_73 : D 41 73 = true := by have h := D_step 39 72; rw [d_39_72, d_40_72, d_41_72] at h; exact h
private theorem d_42_73 : D 42 73 = true := by have h := D_step 40 72; rw [d_40_72, d_41_72, d_42_72] at h; exact h
private theorem d_43_73 : D 43 73 = false := by have h := D_step 41 72; rw [d_41_72, d_42_72, d_43_72] at h; exact h
private theorem d_44_73 : D 44 73 = false := by have h := D_step 42 72; rw [d_42_72, d_43_72, d_44_72] at h; exact h
private theorem d_45_73 : D 45 73 = false := by have h := D_step 43 72; rw [d_43_72, d_44_72, d_45_72] at h; exact h
private theorem d_46_73 : D 46 73 = false := by have h := D_step 44 72; rw [d_44_72, d_45_72, d_46_72] at h; exact h
private theorem d_47_73 : D 47 73 = false := by have h := D_step 45 72; rw [d_45_72, d_46_72, d_47_72] at h; exact h
private theorem d_48_73 : D 48 73 = true := by have h := D_step 46 72; rw [d_46_72, d_47_72, d_48_72] at h; exact h
private theorem d_49_73 : D 49 73 = true := by have h := D_step 47 72; rw [d_47_72, d_48_72, d_49_72] at h; exact h
private theorem d_50_73 : D 50 73 = true := by have h := D_step 48 72; rw [d_48_72, d_49_72, d_50_72] at h; exact h
private theorem d_51_73 : D 51 73 = true := by have h := D_step 49 72; rw [d_49_72, d_50_72, d_51_72] at h; exact h
private theorem d_52_73 : D 52 73 = false := by have h := D_step 50 72; rw [d_50_72, d_51_72, d_52_72] at h; exact h
private theorem d_0_74 : D 0 74 = true := D_zero 74
private theorem d_1_74 : D 1 74 = true := by simpa using D_one 73
private theorem d_2_74 : D 2 74 = false := by have h := D_step 0 73; rw [d_0_73, d_1_73, d_2_73] at h; exact h
private theorem d_3_74 : D 3 74 = false := by have h := D_step 1 73; rw [d_1_73, d_2_73, d_3_73] at h; exact h
private theorem d_4_74 : D 4 74 = true := by have h := D_step 2 73; rw [d_2_73, d_3_73, d_4_73] at h; exact h
private theorem d_5_74 : D 5 74 = false := by have h := D_step 3 73; rw [d_3_73, d_4_73, d_5_73] at h; exact h
private theorem d_6_74 : D 6 74 = false := by have h := D_step 4 73; rw [d_4_73, d_5_73, d_6_73] at h; exact h
private theorem d_7_74 : D 7 74 = false := by have h := D_step 5 73; rw [d_5_73, d_6_73, d_7_73] at h; exact h
private theorem d_8_74 : D 8 74 = false := by have h := D_step 6 73; rw [d_6_73, d_7_73, d_8_73] at h; exact h
private theorem d_9_74 : D 9 74 = true := by have h := D_step 7 73; rw [d_7_73, d_8_73, d_9_73] at h; exact h
private theorem d_10_74 : D 10 74 = false := by have h := D_step 8 73; rw [d_8_73, d_9_73, d_10_73] at h; exact h
private theorem d_11_74 : D 11 74 = true := by have h := D_step 9 73; rw [d_9_73, d_10_73, d_11_73] at h; exact h
private theorem d_12_74 : D 12 74 = true := by have h := D_step 10 73; rw [d_10_73, d_11_73, d_12_73] at h; exact h
private theorem d_13_74 : D 13 74 = true := by have h := D_step 11 73; rw [d_11_73, d_12_73, d_13_73] at h; exact h
private theorem d_14_74 : D 14 74 = false := by have h := D_step 12 73; rw [d_12_73, d_13_73, d_14_73] at h; exact h
private theorem d_15_74 : D 15 74 = false := by have h := D_step 13 73; rw [d_13_73, d_14_73, d_15_73] at h; exact h
private theorem d_16_74 : D 16 74 = true := by have h := D_step 14 73; rw [d_14_73, d_15_73, d_16_73] at h; exact h
private theorem d_17_74 : D 17 74 = false := by have h := D_step 15 73; rw [d_15_73, d_16_73, d_17_73] at h; exact h
private theorem d_18_74 : D 18 74 = true := by have h := D_step 16 73; rw [d_16_73, d_17_73, d_18_73] at h; exact h
private theorem d_19_74 : D 19 74 = true := by have h := D_step 17 73; rw [d_17_73, d_18_73, d_19_73] at h; exact h
private theorem d_20_74 : D 20 74 = false := by have h := D_step 18 73; rw [d_18_73, d_19_73, d_20_73] at h; exact h
private theorem d_21_74 : D 21 74 = true := by have h := D_step 19 73; rw [d_19_73, d_20_73, d_21_73] at h; exact h
private theorem d_22_74 : D 22 74 = false := by have h := D_step 20 73; rw [d_20_73, d_21_73, d_22_73] at h; exact h
private theorem d_23_74 : D 23 74 = true := by have h := D_step 21 73; rw [d_21_73, d_22_73, d_23_73] at h; exact h
private theorem d_24_74 : D 24 74 = false := by have h := D_step 22 73; rw [d_22_73, d_23_73, d_24_73] at h; exact h
private theorem d_25_74 : D 25 74 = false := by have h := D_step 23 73; rw [d_23_73, d_24_73, d_25_73] at h; exact h
private theorem d_26_74 : D 26 74 = true := by have h := D_step 24 73; rw [d_24_73, d_25_73, d_26_73] at h; exact h
private theorem d_27_74 : D 27 74 = true := by have h := D_step 25 73; rw [d_25_73, d_26_73, d_27_73] at h; exact h
private theorem d_28_74 : D 28 74 = false := by have h := D_step 26 73; rw [d_26_73, d_27_73, d_28_73] at h; exact h
private theorem d_29_74 : D 29 74 = false := by have h := D_step 27 73; rw [d_27_73, d_28_73, d_29_73] at h; exact h
private theorem d_30_74 : D 30 74 = true := by have h := D_step 28 73; rw [d_28_73, d_29_73, d_30_73] at h; exact h
private theorem d_31_74 : D 31 74 = false := by have h := D_step 29 73; rw [d_29_73, d_30_73, d_31_73] at h; exact h
private theorem d_32_74 : D 32 74 = true := by have h := D_step 30 73; rw [d_30_73, d_31_73, d_32_73] at h; exact h
private theorem d_33_74 : D 33 74 = false := by have h := D_step 31 73; rw [d_31_73, d_32_73, d_33_73] at h; exact h
private theorem d_34_74 : D 34 74 = false := by have h := D_step 32 73; rw [d_32_73, d_33_73, d_34_73] at h; exact h
private theorem d_35_74 : D 35 74 = false := by have h := D_step 33 73; rw [d_33_73, d_34_73, d_35_73] at h; exact h
private theorem d_36_74 : D 36 74 = false := by have h := D_step 34 73; rw [d_34_73, d_35_73, d_36_73] at h; exact h
private theorem d_37_74 : D 37 74 = true := by have h := D_step 35 73; rw [d_35_73, d_36_73, d_37_73] at h; exact h
private theorem d_38_74 : D 38 74 = true := by have h := D_step 36 73; rw [d_36_73, d_37_73, d_38_73] at h; exact h
private theorem d_39_74 : D 39 74 = false := by have h := D_step 37 73; rw [d_37_73, d_38_73, d_39_73] at h; exact h
private theorem d_40_74 : D 40 74 = true := by have h := D_step 38 73; rw [d_38_73, d_39_73, d_40_73] at h; exact h
private theorem d_41_74 : D 41 74 = true := by have h := D_step 39 73; rw [d_39_73, d_40_73, d_41_73] at h; exact h
private theorem d_42_74 : D 42 74 = true := by have h := D_step 40 73; rw [d_40_73, d_41_73, d_42_73] at h; exact h
private theorem d_43_74 : D 43 74 = false := by have h := D_step 41 73; rw [d_41_73, d_42_73, d_43_73] at h; exact h
private theorem d_44_74 : D 44 74 = true := by have h := D_step 42 73; rw [d_42_73, d_43_73, d_44_73] at h; exact h
private theorem d_45_74 : D 45 74 = false := by have h := D_step 43 73; rw [d_43_73, d_44_73, d_45_73] at h; exact h
private theorem d_46_74 : D 46 74 = false := by have h := D_step 44 73; rw [d_44_73, d_45_73, d_46_73] at h; exact h
private theorem d_47_74 : D 47 74 = false := by have h := D_step 45 73; rw [d_45_73, d_46_73, d_47_73] at h; exact h
private theorem d_48_74 : D 48 74 = true := by have h := D_step 46 73; rw [d_46_73, d_47_73, d_48_73] at h; exact h
private theorem d_49_74 : D 49 74 = true := by have h := D_step 47 73; rw [d_47_73, d_48_73, d_49_73] at h; exact h
private theorem d_50_74 : D 50 74 = false := by have h := D_step 48 73; rw [d_48_73, d_49_73, d_50_73] at h; exact h
private theorem d_51_74 : D 51 74 = false := by have h := D_step 49 73; rw [d_49_73, d_50_73, d_51_73] at h; exact h
private theorem d_52_74 : D 52 74 = false := by have h := D_step 50 73; rw [d_50_73, d_51_73, d_52_73] at h; exact h
private theorem d_0_75 : D 0 75 = true := D_zero 75
private theorem d_1_75 : D 1 75 = true := by simpa using D_one 74
private theorem d_2_75 : D 2 75 = false := by have h := D_step 0 74; rw [d_0_74, d_1_74, d_2_74] at h; exact h
private theorem d_3_75 : D 3 75 = true := by have h := D_step 1 74; rw [d_1_74, d_2_74, d_3_74] at h; exact h
private theorem d_4_75 : D 4 75 = true := by have h := D_step 2 74; rw [d_2_74, d_3_74, d_4_74] at h; exact h
private theorem d_5_75 : D 5 75 = true := by have h := D_step 3 74; rw [d_3_74, d_4_74, d_5_74] at h; exact h
private theorem d_6_75 : D 6 75 = true := by have h := D_step 4 74; rw [d_4_74, d_5_74, d_6_74] at h; exact h
private theorem d_7_75 : D 7 75 = false := by have h := D_step 5 74; rw [d_5_74, d_6_74, d_7_74] at h; exact h
private theorem d_8_75 : D 8 75 = false := by have h := D_step 6 74; rw [d_6_74, d_7_74, d_8_74] at h; exact h
private theorem d_9_75 : D 9 75 = true := by have h := D_step 7 74; rw [d_7_74, d_8_74, d_9_74] at h; exact h
private theorem d_10_75 : D 10 75 = true := by have h := D_step 8 74; rw [d_8_74, d_9_74, d_10_74] at h; exact h
private theorem d_11_75 : D 11 75 = false := by have h := D_step 9 74; rw [d_9_74, d_10_74, d_11_74] at h; exact h
private theorem d_12_75 : D 12 75 = true := by have h := D_step 10 74; rw [d_10_74, d_11_74, d_12_74] at h; exact h
private theorem d_13_75 : D 13 75 = false := by have h := D_step 11 74; rw [d_11_74, d_12_74, d_13_74] at h; exact h
private theorem d_14_75 : D 14 75 = false := by have h := D_step 12 74; rw [d_12_74, d_13_74, d_14_74] at h; exact h
private theorem d_15_75 : D 15 75 = true := by have h := D_step 13 74; rw [d_13_74, d_14_74, d_15_74] at h; exact h
private theorem d_16_75 : D 16 75 = true := by have h := D_step 14 74; rw [d_14_74, d_15_74, d_16_74] at h; exact h
private theorem d_17_75 : D 17 75 = true := by have h := D_step 15 74; rw [d_15_74, d_16_74, d_17_74] at h; exact h
private theorem d_18_75 : D 18 75 = false := by have h := D_step 16 74; rw [d_16_74, d_17_74, d_18_74] at h; exact h
private theorem d_19_75 : D 19 75 = true := by have h := D_step 17 74; rw [d_17_74, d_18_74, d_19_74] at h; exact h
private theorem d_20_75 : D 20 75 = false := by have h := D_step 18 74; rw [d_18_74, d_19_74, d_20_74] at h; exact h
private theorem d_21_75 : D 21 75 = false := by have h := D_step 19 74; rw [d_19_74, d_20_74, d_21_74] at h; exact h
private theorem d_22_75 : D 22 75 = true := by have h := D_step 20 74; rw [d_20_74, d_21_74, d_22_74] at h; exact h
private theorem d_23_75 : D 23 75 = false := by have h := D_step 21 74; rw [d_21_74, d_22_74, d_23_74] at h; exact h
private theorem d_24_75 : D 24 75 = true := by have h := D_step 22 74; rw [d_22_74, d_23_74, d_24_74] at h; exact h
private theorem d_25_75 : D 25 75 = true := by have h := D_step 23 74; rw [d_23_74, d_24_74, d_25_74] at h; exact h
private theorem d_26_75 : D 26 75 = true := by have h := D_step 24 74; rw [d_24_74, d_25_74, d_26_74] at h; exact h
private theorem d_27_75 : D 27 75 = true := by have h := D_step 25 74; rw [d_25_74, d_26_74, d_27_74] at h; exact h
private theorem d_28_75 : D 28 75 = false := by have h := D_step 26 74; rw [d_26_74, d_27_74, d_28_74] at h; exact h
private theorem d_29_75 : D 29 75 = true := by have h := D_step 27 74; rw [d_27_74, d_28_74, d_29_74] at h; exact h
private theorem d_30_75 : D 30 75 = true := by have h := D_step 28 74; rw [d_28_74, d_29_74, d_30_74] at h; exact h
private theorem d_31_75 : D 31 75 = true := by have h := D_step 29 74; rw [d_29_74, d_30_74, d_31_74] at h; exact h
private theorem d_32_75 : D 32 75 = false := by have h := D_step 30 74; rw [d_30_74, d_31_74, d_32_74] at h; exact h
private theorem d_33_75 : D 33 75 = true := by have h := D_step 31 74; rw [d_31_74, d_32_74, d_33_74] at h; exact h
private theorem d_34_75 : D 34 75 = true := by have h := D_step 32 74; rw [d_32_74, d_33_74, d_34_74] at h; exact h
private theorem d_35_75 : D 35 75 = false := by have h := D_step 33 74; rw [d_33_74, d_34_74, d_35_74] at h; exact h
private theorem d_36_75 : D 36 75 = false := by have h := D_step 34 74; rw [d_34_74, d_35_74, d_36_74] at h; exact h
private theorem d_37_75 : D 37 75 = true := by have h := D_step 35 74; rw [d_35_74, d_36_74, d_37_74] at h; exact h
private theorem d_38_75 : D 38 75 = true := by have h := D_step 36 74; rw [d_36_74, d_37_74, d_38_74] at h; exact h
private theorem d_39_75 : D 39 75 = false := by have h := D_step 37 74; rw [d_37_74, d_38_74, d_39_74] at h; exact h
private theorem d_40_75 : D 40 75 = false := by have h := D_step 38 74; rw [d_38_74, d_39_74, d_40_74] at h; exact h
private theorem d_41_75 : D 41 75 = true := by have h := D_step 39 74; rw [d_39_74, d_40_74, d_41_74] at h; exact h
private theorem d_42_75 : D 42 75 = false := by have h := D_step 40 74; rw [d_40_74, d_41_74, d_42_74] at h; exact h
private theorem d_43_75 : D 43 75 = false := by have h := D_step 41 74; rw [d_41_74, d_42_74, d_43_74] at h; exact h
private theorem d_44_75 : D 44 75 = false := by have h := D_step 42 74; rw [d_42_74, d_43_74, d_44_74] at h; exact h
private theorem d_45_75 : D 45 75 = true := by have h := D_step 43 74; rw [d_43_74, d_44_74, d_45_74] at h; exact h
private theorem d_46_75 : D 46 75 = true := by have h := D_step 44 74; rw [d_44_74, d_45_74, d_46_74] at h; exact h
private theorem d_47_75 : D 47 75 = false := by have h := D_step 45 74; rw [d_45_74, d_46_74, d_47_74] at h; exact h
private theorem d_48_75 : D 48 75 = true := by have h := D_step 46 74; rw [d_46_74, d_47_74, d_48_74] at h; exact h
private theorem d_49_75 : D 49 75 = true := by have h := D_step 47 74; rw [d_47_74, d_48_74, d_49_74] at h; exact h
private theorem d_50_75 : D 50 75 = false := by have h := D_step 48 74; rw [d_48_74, d_49_74, d_50_74] at h; exact h
private theorem d_51_75 : D 51 75 = true := by have h := D_step 49 74; rw [d_49_74, d_50_74, d_51_74] at h; exact h
private theorem d_52_75 : D 52 75 = false := by have h := D_step 50 74; rw [d_50_74, d_51_74, d_52_74] at h; exact h
private theorem d_0_76 : D 0 76 = true := D_zero 76
private theorem d_1_76 : D 1 76 = true := by simpa using D_one 75
private theorem d_2_76 : D 2 76 = false := by have h := D_step 0 75; rw [d_0_75, d_1_75, d_2_75] at h; exact h
private theorem d_3_76 : D 3 76 = false := by have h := D_step 1 75; rw [d_1_75, d_2_75, d_3_75] at h; exact h
private theorem d_4_76 : D 4 76 = true := by have h := D_step 2 75; rw [d_2_75, d_3_75, d_4_75] at h; exact h
private theorem d_5_76 : D 5 76 = false := by have h := D_step 3 75; rw [d_3_75, d_4_75, d_5_75] at h; exact h
private theorem d_6_76 : D 6 76 = false := by have h := D_step 4 75; rw [d_4_75, d_5_75, d_6_75] at h; exact h
private theorem d_7_76 : D 7 76 = false := by have h := D_step 5 75; rw [d_5_75, d_6_75, d_7_75] at h; exact h
private theorem d_8_76 : D 8 76 = true := by have h := D_step 6 75; rw [d_6_75, d_7_75, d_8_75] at h; exact h
private theorem d_9_76 : D 9 76 = true := by have h := D_step 7 75; rw [d_7_75, d_8_75, d_9_75] at h; exact h
private theorem d_10_76 : D 10 76 = true := by have h := D_step 8 75; rw [d_8_75, d_9_75, d_10_75] at h; exact h
private theorem d_11_76 : D 11 76 = false := by have h := D_step 9 75; rw [d_9_75, d_10_75, d_11_75] at h; exact h
private theorem d_12_76 : D 12 76 = false := by have h := D_step 10 75; rw [d_10_75, d_11_75, d_12_75] at h; exact h
private theorem d_13_76 : D 13 76 = true := by have h := D_step 11 75; rw [d_11_75, d_12_75, d_13_75] at h; exact h
private theorem d_14_76 : D 14 76 = true := by have h := D_step 12 75; rw [d_12_75, d_13_75, d_14_75] at h; exact h
private theorem d_15_76 : D 15 76 = true := by have h := D_step 13 75; rw [d_13_75, d_14_75, d_15_75] at h; exact h
private theorem d_16_76 : D 16 76 = true := by have h := D_step 14 75; rw [d_14_75, d_15_75, d_16_75] at h; exact h
private theorem d_17_76 : D 17 76 = false := by have h := D_step 15 75; rw [d_15_75, d_16_75, d_17_75] at h; exact h
private theorem d_18_76 : D 18 76 = false := by have h := D_step 16 75; rw [d_16_75, d_17_75, d_18_75] at h; exact h
private theorem d_19_76 : D 19 76 = false := by have h := D_step 17 75; rw [d_17_75, d_18_75, d_19_75] at h; exact h
private theorem d_20_76 : D 20 76 = true := by have h := D_step 18 75; rw [d_18_75, d_19_75, d_20_75] at h; exact h
private theorem d_21_76 : D 21 76 = true := by have h := D_step 19 75; rw [d_19_75, d_20_75, d_21_75] at h; exact h
private theorem d_22_76 : D 22 76 = true := by have h := D_step 20 75; rw [d_20_75, d_21_75, d_22_75] at h; exact h
private theorem d_23_76 : D 23 76 = true := by have h := D_step 21 75; rw [d_21_75, d_22_75, d_23_75] at h; exact h
private theorem d_24_76 : D 24 76 = false := by have h := D_step 22 75; rw [d_22_75, d_23_75, d_24_75] at h; exact h
private theorem d_25_76 : D 25 76 = true := by have h := D_step 23 75; rw [d_23_75, d_24_75, d_25_75] at h; exact h
private theorem d_26_76 : D 26 76 = false := by have h := D_step 24 75; rw [d_24_75, d_25_75, d_26_75] at h; exact h
private theorem d_27_76 : D 27 76 = false := by have h := D_step 25 75; rw [d_25_75, d_26_75, d_27_75] at h; exact h
private theorem d_28_76 : D 28 76 = false := by have h := D_step 26 75; rw [d_26_75, d_27_75, d_28_75] at h; exact h
private theorem d_29_76 : D 29 76 = false := by have h := D_step 27 75; rw [d_27_75, d_28_75, d_29_75] at h; exact h
private theorem d_30_76 : D 30 76 = true := by have h := D_step 28 75; rw [d_28_75, d_29_75, d_30_75] at h; exact h
private theorem d_31_76 : D 31 76 = false := by have h := D_step 29 75; rw [d_29_75, d_30_75, d_31_75] at h; exact h
private theorem d_32_76 : D 32 76 = false := by have h := D_step 30 75; rw [d_30_75, d_31_75, d_32_75] at h; exact h
private theorem d_33_76 : D 33 76 = false := by have h := D_step 31 75; rw [d_31_75, d_32_75, d_33_75] at h; exact h
private theorem d_34_76 : D 34 76 = true := by have h := D_step 32 75; rw [d_32_75, d_33_75, d_34_75] at h; exact h
private theorem d_35_76 : D 35 76 = false := by have h := D_step 33 75; rw [d_33_75, d_34_75, d_35_75] at h; exact h
private theorem d_36_76 : D 36 76 = true := by have h := D_step 34 75; rw [d_34_75, d_35_75, d_36_75] at h; exact h
private theorem d_37_76 : D 37 76 = true := by have h := D_step 35 75; rw [d_35_75, d_36_75, d_37_75] at h; exact h
private theorem d_38_76 : D 38 76 = true := by have h := D_step 36 75; rw [d_36_75, d_37_75, d_38_75] at h; exact h
private theorem d_39_76 : D 39 76 = false := by have h := D_step 37 75; rw [d_37_75, d_38_75, d_39_75] at h; exact h
private theorem d_40_76 : D 40 76 = true := by have h := D_step 38 75; rw [d_38_75, d_39_75, d_40_75] at h; exact h
private theorem d_41_76 : D 41 76 = true := by have h := D_step 39 75; rw [d_39_75, d_40_75, d_41_75] at h; exact h
private theorem d_42_76 : D 42 76 = true := by have h := D_step 40 75; rw [d_40_75, d_41_75, d_42_75] at h; exact h
private theorem d_43_76 : D 43 76 = true := by have h := D_step 41 75; rw [d_41_75, d_42_75, d_43_75] at h; exact h
private theorem d_44_76 : D 44 76 = false := by have h := D_step 42 75; rw [d_42_75, d_43_75, d_44_75] at h; exact h
private theorem d_45_76 : D 45 76 = true := by have h := D_step 43 75; rw [d_43_75, d_44_75, d_45_75] at h; exact h
private theorem d_46_76 : D 46 76 = true := by have h := D_step 44 75; rw [d_44_75, d_45_75, d_46_75] at h; exact h
private theorem d_47_76 : D 47 76 = false := by have h := D_step 45 75; rw [d_45_75, d_46_75, d_47_75] at h; exact h
private theorem d_48_76 : D 48 76 = false := by have h := D_step 46 75; rw [d_46_75, d_47_75, d_48_75] at h; exact h
private theorem d_49_76 : D 49 76 = true := by have h := D_step 47 75; rw [d_47_75, d_48_75, d_49_75] at h; exact h
private theorem d_50_76 : D 50 76 = false := by have h := D_step 48 75; rw [d_48_75, d_49_75, d_50_75] at h; exact h
private theorem d_51_76 : D 51 76 = false := by have h := D_step 49 75; rw [d_49_75, d_50_75, d_51_75] at h; exact h
private theorem d_52_76 : D 52 76 = true := by have h := D_step 50 75; rw [d_50_75, d_51_75, d_52_75] at h; exact h

/-- **Three-Bit Gate Law for the Forty-Sixth Left Diagonal (`D_forty_six_eq_gate`):**
for every `t ≥ 64`, `D 46 t = (D 10 t || xor (D 8 t) (D 29 t))`. -/
theorem D_forty_six_eq_gate : ∀ t : Nat, 64 ≤ t →
    D 46 t = (D 10 t || xor (D 8 t) (D 29 t))
  | 64, _ => by rw [d_46_64, d_8_64, d_10_64, d_29_64]; rfl
  | t + 1, ht => by
    by_cases h : t < 64
    · have h_eq : t + 1 = 64 := by omega
      rw [h_eq, d_46_64, d_8_64, d_10_64, d_29_64]; rfl
    · have ih := D_forty_six_eq_gate t (by omega)
      have hstep := D_step 44 t
      rw [D_forty_four_eq_gate t (by omega), D_forty_five_eq_D_ten t (by omega), ih] at hstep
      rw [hstep, D_eight_succ_eq_D_ten t (by omega), D_ten_succ_eq_not_D_eight t (by omega),
          D_twenty_nine_step_closed t (by omega)]
      cases D 8 t <;> cases D 10 t <;> cases D 29 t <;> decide

/-- **Three-Bit Gate Law for the Forty-Seventh Left Diagonal (`D_forty_seven_eq_gate`):**
for every `t ≥ 64`, `D 47 t = (!D 8 t && xor (D 10 t) (D 29 t))`. -/
theorem D_forty_seven_eq_gate : ∀ t : Nat, 64 ≤ t →
    D 47 t = (!D 8 t && xor (D 10 t) (D 29 t))
  | 64, _ => by rw [d_47_64, d_8_64, d_10_64, d_29_64]; rfl
  | t + 1, ht => by
    by_cases h : t < 64
    · have h_eq : t + 1 = 64 := by omega
      rw [h_eq, d_47_64, d_8_64, d_10_64, d_29_64]; rfl
    · have ih := D_forty_seven_eq_gate t (by omega)
      have hstep := D_step 45 t
      rw [D_forty_five_eq_D_ten t (by omega), D_forty_six_eq_gate t (by omega), ih] at hstep
      rw [hstep, D_eight_succ_eq_D_ten t (by omega), D_ten_succ_eq_not_D_eight t (by omega),
          D_twenty_nine_step_closed t (by omega)]
      cases D 8 t <;> cases D 10 t <;> cases D 29 t <;> decide

/-- **Two-to-One Multiplexer Law for the Forty-Eighth Left Diagonal (`D_forty_eight_eq_mux`):**
for every `t ≥ 71`, `D 48 t = ((!D 10 t && !D 29 t) || (xor (D 8 t) (D 10 t) && D 29 t))`. -/
theorem D_forty_eight_eq_mux : ∀ t : Nat, 71 ≤ t →
    D 48 t = ((!D 10 t && !D 29 t) || (xor (D 8 t) (D 10 t) && D 29 t))
  | 71, _ => by rw [d_48_71, d_8_71, d_10_71, d_29_71]; rfl
  | t + 1, ht => by
    by_cases h : t < 71
    · have h_eq : t + 1 = 71 := by omega
      rw [h_eq, d_48_71, d_8_71, d_10_71, d_29_71]; rfl
    · have ih := D_forty_eight_eq_mux t (by omega)
      have hstep := D_step 46 t
      rw [D_forty_six_eq_gate t (by omega), D_forty_seven_eq_gate t (by omega), ih] at hstep
      rw [hstep, D_eight_succ_eq_D_ten t (by omega), D_ten_succ_eq_not_D_eight t (by omega),
          D_twenty_nine_step_closed t (by omega)]
      cases D 8 t <;> cases D 10 t <;> cases D 29 t <;> decide

/-- **Three-Bit Gate Law for the Forty-Ninth Left Diagonal (`D_forty_nine_eq_gate`):**
for every `t ≥ 71`, `D 49 t = (D 8 t || !D 10 t || D 29 t)`. -/
theorem D_forty_nine_eq_gate : ∀ t : Nat, 71 ≤ t →
    D 49 t = (D 8 t || !D 10 t || D 29 t)
  | 71, _ => by rw [d_49_71, d_8_71, d_10_71, d_29_71]; rfl
  | t + 1, ht => by
    by_cases h : t < 71
    · have h_eq : t + 1 = 71 := by omega
      rw [h_eq, d_49_71, d_8_71, d_10_71, d_29_71]; rfl
    · have ih := D_forty_nine_eq_gate t (by omega)
      have hstep := D_step 47 t
      rw [D_forty_seven_eq_gate t (by omega), D_forty_eight_eq_mux t (by omega), ih] at hstep
      rw [hstep, D_eight_succ_eq_D_ten t (by omega), D_ten_succ_eq_not_D_eight t (by omega),
          D_twenty_nine_step_closed t (by omega)]
      cases D 8 t <;> cases D 10 t <;> cases D 29 t <;> decide

/-- **Two-to-One Multiplexer Law for the Fiftieth Left Diagonal (`D_fifty_eq_mux`):**
for every `t ≥ 73`, `D 50 t = ((xor (D 8 t) (D 10 t) && !D 29 t) || (D 8 t && D 29 t))`. -/
theorem D_fifty_eq_mux : ∀ t : Nat, 73 ≤ t →
    D 50 t = ((xor (D 8 t) (D 10 t) && !D 29 t) || (D 8 t && D 29 t))
  | 73, _ => by rw [d_50_73, d_8_73, d_10_73, d_29_73]; rfl
  | t + 1, ht => by
    by_cases h : t < 73
    · have h_eq : t + 1 = 73 := by omega
      rw [h_eq, d_50_73, d_8_73, d_10_73, d_29_73]; rfl
    · have ih := D_fifty_eq_mux t (by omega)
      have hstep := D_step 48 t
      rw [D_forty_eight_eq_mux t (by omega), D_forty_nine_eq_gate t (by omega), ih] at hstep
      rw [hstep, D_eight_succ_eq_D_ten t (by omega), D_ten_succ_eq_not_D_eight t (by omega),
          D_twenty_nine_step_closed t (by omega)]
      cases D 8 t <;> cases D 10 t <;> cases D 29 t <;> decide

/-- **Two-to-One Multiplexer Law for the Fifty-First Left Diagonal (`D_fifty_one_eq_mux`):**
for every `t ≥ 74`, `D 51 t = ((xor (D 8 t) (D 10 t) && !D 29 t) || (D 10 t && D 29 t))`. -/
theorem D_fifty_one_eq_mux : ∀ t : Nat, 74 ≤ t →
    D 51 t = ((xor (D 8 t) (D 10 t) && !D 29 t) || (D 10 t && D 29 t))
  | 74, _ => by rw [d_51_74, d_8_74, d_10_74, d_29_74]; rfl
  | t + 1, ht => by
    by_cases h : t < 74
    · have h_eq : t + 1 = 74 := by omega
      rw [h_eq, d_51_74, d_8_74, d_10_74, d_29_74]; rfl
    · have ih := D_fifty_one_eq_mux t (by omega)
      have hstep := D_step 49 t
      rw [D_forty_nine_eq_gate t (by omega), D_fifty_eq_mux t (by omega), ih] at hstep
      rw [hstep, D_eight_succ_eq_D_ten t (by omega), D_ten_succ_eq_not_D_eight t (by omega),
          D_twenty_nine_step_closed t (by omega)]
      cases D 8 t <;> cases D 10 t <;> cases D 29 t <;> decide

/-- **Three-Bit Gate Law for the Fifty-Second Left Diagonal (`D_fifty_two_eq_gate`):**
for every `t ≥ 76`, `D 52 t = xor (!D 8 t && D 10 t) (!D 29 t)`. -/
theorem D_fifty_two_eq_gate : ∀ t : Nat, 76 ≤ t →
    D 52 t = xor (!D 8 t && D 10 t) (!D 29 t)
  | 76, _ => by rw [d_52_76, d_8_76, d_10_76, d_29_76]; rfl
  | t + 1, ht => by
    by_cases h : t < 76
    · have h_eq : t + 1 = 76 := by omega
      rw [h_eq, d_52_76, d_8_76, d_10_76, d_29_76]; rfl
    · have ih := D_fifty_two_eq_gate t (by omega)
      have hstep := D_step 50 t
      rw [D_fifty_eq_mux t (by omega), D_fifty_one_eq_mux t (by omega), ih] at hstep
      rw [hstep, D_eight_succ_eq_D_ten t (by omega), D_ten_succ_eq_not_D_eight t (by omega),
          D_twenty_nine_step_closed t (by omega)]
      cases D 8 t <;> cases D 10 t <;> cases D 29 t <;> decide

/-- **Exact Eight-Step Block Weight of `D 48` (`D_forty_eight_block_eight_sum`):**
every 8 consecutive ticks of `D 48` from `t ≥ 71` on contain exactly 4 ones. -/
theorem D_forty_eight_block_eight_sum (t : Nat) (ht : 71 ≤ t) :
    (if D 48 t then 1 else 0) + (if D 48 (t + 1) then 1 else 0) +
      (if D 48 (t + 2) then 1 else 0) + (if D 48 (t + 3) then 1 else 0) +
      (if D 48 (t + 4) then 1 else 0) + (if D 48 (t + 5) then 1 else 0) +
      (if D 48 (t + 6) then 1 else 0) + (if D 48 (t + 7) then 1 else 0) = 4 := by
  have g0 := D_forty_eight_eq_mux t ht
  have g1 := D_forty_eight_eq_mux (t + 1) (by omega)
  have g2 := D_forty_eight_eq_mux (t + 2) (by omega)
  have g3 := D_forty_eight_eq_mux (t + 3) (by omega)
  have g4 := D_forty_eight_eq_mux (t + 4) (by omega)
  have g5 := D_forty_eight_eq_mux (t + 5) (by omega)
  have g6 := D_forty_eight_eq_mux (t + 6) (by omega)
  have g7 := D_forty_eight_eq_mux (t + 7) (by omega)
  have s8_1 := D_eight_succ_eq_D_ten t (by omega)
  have s10_1 := D_ten_succ_eq_not_D_eight t (by omega)
  have s29_1 := D_twenty_nine_step_closed t (by omega)
  have s8_2 := D_eight_succ_eq_D_ten (t + 1) (by omega)
  have s10_2 := D_ten_succ_eq_not_D_eight (t + 1) (by omega)
  have s29_2 := D_twenty_nine_step_closed (t + 1) (by omega)
  have s8_3 := D_eight_succ_eq_D_ten (t + 2) (by omega)
  have s10_3 := D_ten_succ_eq_not_D_eight (t + 2) (by omega)
  have s29_3 := D_twenty_nine_step_closed (t + 2) (by omega)
  have p8_4 := D_eight_periodic_four t (by omega)
  have p10_4 := D_ten_periodic_four t (by omega)
  have p29_4 := D_twenty_nine_antiperiodic_four t (by omega)
  have p8_5 := D_eight_periodic_four (t + 1) (by omega)
  have p10_5 := D_ten_periodic_four (t + 1) (by omega)
  have p29_5 := D_twenty_nine_antiperiodic_four (t + 1) (by omega)
  have p8_6 := D_eight_periodic_four (t + 2) (by omega)
  have p10_6 := D_ten_periodic_four (t + 2) (by omega)
  have p29_6 := D_twenty_nine_antiperiodic_four (t + 2) (by omega)
  have p8_7 := D_eight_periodic_four (t + 3) (by omega)
  have p10_7 := D_ten_periodic_four (t + 3) (by omega)
  have p29_7 := D_twenty_nine_antiperiodic_four (t + 3) (by omega)
  rw [show t + 1 + 1 = t + 2 by omega] at s8_2 s10_2 s29_2
  rw [show t + 2 + 1 = t + 3 by omega] at s8_3 s10_3 s29_3
  rw [show t + 1 + 4 = t + 5 by omega] at p8_5 p10_5 p29_5
  rw [show t + 2 + 4 = t + 6 by omega] at p8_6 p10_6 p29_6
  rw [show t + 3 + 4 = t + 7 by omega] at p8_7 p10_7 p29_7
  rw [g0, g1, g2, g3, g4, g5, g6, g7,
      p8_4, p10_4, p29_4, p8_5, p10_5, p29_5, p8_6, p10_6, p29_6, p8_7, p10_7, p29_7,
      s8_3, s10_3, s29_3, s8_2, s10_2, s29_2, s8_1, s10_1, s29_1]
  cases D 8 t <;> cases D 10 t <;> cases D 29 t <;> decide

/-- **Exact Eight-Step Block Weight of `D 50` (`D_fifty_block_eight_sum`):**
every 8 consecutive ticks of `D 50` from `t ≥ 73` on contain exactly 4 ones. -/
theorem D_fifty_block_eight_sum (t : Nat) (ht : 73 ≤ t) :
    (if D 50 t then 1 else 0) + (if D 50 (t + 1) then 1 else 0) +
      (if D 50 (t + 2) then 1 else 0) + (if D 50 (t + 3) then 1 else 0) +
      (if D 50 (t + 4) then 1 else 0) + (if D 50 (t + 5) then 1 else 0) +
      (if D 50 (t + 6) then 1 else 0) + (if D 50 (t + 7) then 1 else 0) = 4 := by
  have g0 := D_fifty_eq_mux t ht
  have g1 := D_fifty_eq_mux (t + 1) (by omega)
  have g2 := D_fifty_eq_mux (t + 2) (by omega)
  have g3 := D_fifty_eq_mux (t + 3) (by omega)
  have g4 := D_fifty_eq_mux (t + 4) (by omega)
  have g5 := D_fifty_eq_mux (t + 5) (by omega)
  have g6 := D_fifty_eq_mux (t + 6) (by omega)
  have g7 := D_fifty_eq_mux (t + 7) (by omega)
  have s8_1 := D_eight_succ_eq_D_ten t (by omega)
  have s10_1 := D_ten_succ_eq_not_D_eight t (by omega)
  have s29_1 := D_twenty_nine_step_closed t (by omega)
  have s8_2 := D_eight_succ_eq_D_ten (t + 1) (by omega)
  have s10_2 := D_ten_succ_eq_not_D_eight (t + 1) (by omega)
  have s29_2 := D_twenty_nine_step_closed (t + 1) (by omega)
  have s8_3 := D_eight_succ_eq_D_ten (t + 2) (by omega)
  have s10_3 := D_ten_succ_eq_not_D_eight (t + 2) (by omega)
  have s29_3 := D_twenty_nine_step_closed (t + 2) (by omega)
  have p8_4 := D_eight_periodic_four t (by omega)
  have p10_4 := D_ten_periodic_four t (by omega)
  have p29_4 := D_twenty_nine_antiperiodic_four t (by omega)
  have p8_5 := D_eight_periodic_four (t + 1) (by omega)
  have p10_5 := D_ten_periodic_four (t + 1) (by omega)
  have p29_5 := D_twenty_nine_antiperiodic_four (t + 1) (by omega)
  have p8_6 := D_eight_periodic_four (t + 2) (by omega)
  have p10_6 := D_ten_periodic_four (t + 2) (by omega)
  have p29_6 := D_twenty_nine_antiperiodic_four (t + 2) (by omega)
  have p8_7 := D_eight_periodic_four (t + 3) (by omega)
  have p10_7 := D_ten_periodic_four (t + 3) (by omega)
  have p29_7 := D_twenty_nine_antiperiodic_four (t + 3) (by omega)
  rw [show t + 1 + 1 = t + 2 by omega] at s8_2 s10_2 s29_2
  rw [show t + 2 + 1 = t + 3 by omega] at s8_3 s10_3 s29_3
  rw [show t + 1 + 4 = t + 5 by omega] at p8_5 p10_5 p29_5
  rw [show t + 2 + 4 = t + 6 by omega] at p8_6 p10_6 p29_6
  rw [show t + 3 + 4 = t + 7 by omega] at p8_7 p10_7 p29_7
  rw [g0, g1, g2, g3, g4, g5, g6, g7,
      p8_4, p10_4, p29_4, p8_5, p10_5, p29_5, p8_6, p10_6, p29_6, p8_7, p10_7, p29_7,
      s8_3, s10_3, s29_3, s8_2, s10_2, s29_2, s8_1, s10_1, s29_1]
  cases D 8 t <;> cases D 10 t <;> cases D 29 t <;> decide

/-- **Exact Eight-Step Block Weight of `D 51` (`D_fifty_one_block_eight_sum`):**
every 8 consecutive ticks of `D 51` from `t ≥ 74` on contain exactly 4 ones. -/
theorem D_fifty_one_block_eight_sum (t : Nat) (ht : 74 ≤ t) :
    (if D 51 t then 1 else 0) + (if D 51 (t + 1) then 1 else 0) +
      (if D 51 (t + 2) then 1 else 0) + (if D 51 (t + 3) then 1 else 0) +
      (if D 51 (t + 4) then 1 else 0) + (if D 51 (t + 5) then 1 else 0) +
      (if D 51 (t + 6) then 1 else 0) + (if D 51 (t + 7) then 1 else 0) = 4 := by
  have g0 := D_fifty_one_eq_mux t ht
  have g1 := D_fifty_one_eq_mux (t + 1) (by omega)
  have g2 := D_fifty_one_eq_mux (t + 2) (by omega)
  have g3 := D_fifty_one_eq_mux (t + 3) (by omega)
  have g4 := D_fifty_one_eq_mux (t + 4) (by omega)
  have g5 := D_fifty_one_eq_mux (t + 5) (by omega)
  have g6 := D_fifty_one_eq_mux (t + 6) (by omega)
  have g7 := D_fifty_one_eq_mux (t + 7) (by omega)
  have s8_1 := D_eight_succ_eq_D_ten t (by omega)
  have s10_1 := D_ten_succ_eq_not_D_eight t (by omega)
  have s29_1 := D_twenty_nine_step_closed t (by omega)
  have s8_2 := D_eight_succ_eq_D_ten (t + 1) (by omega)
  have s10_2 := D_ten_succ_eq_not_D_eight (t + 1) (by omega)
  have s29_2 := D_twenty_nine_step_closed (t + 1) (by omega)
  have s8_3 := D_eight_succ_eq_D_ten (t + 2) (by omega)
  have s10_3 := D_ten_succ_eq_not_D_eight (t + 2) (by omega)
  have s29_3 := D_twenty_nine_step_closed (t + 2) (by omega)
  have p8_4 := D_eight_periodic_four t (by omega)
  have p10_4 := D_ten_periodic_four t (by omega)
  have p29_4 := D_twenty_nine_antiperiodic_four t (by omega)
  have p8_5 := D_eight_periodic_four (t + 1) (by omega)
  have p10_5 := D_ten_periodic_four (t + 1) (by omega)
  have p29_5 := D_twenty_nine_antiperiodic_four (t + 1) (by omega)
  have p8_6 := D_eight_periodic_four (t + 2) (by omega)
  have p10_6 := D_ten_periodic_four (t + 2) (by omega)
  have p29_6 := D_twenty_nine_antiperiodic_four (t + 2) (by omega)
  have p8_7 := D_eight_periodic_four (t + 3) (by omega)
  have p10_7 := D_ten_periodic_four (t + 3) (by omega)
  have p29_7 := D_twenty_nine_antiperiodic_four (t + 3) (by omega)
  rw [show t + 1 + 1 = t + 2 by omega] at s8_2 s10_2 s29_2
  rw [show t + 2 + 1 = t + 3 by omega] at s8_3 s10_3 s29_3
  rw [show t + 1 + 4 = t + 5 by omega] at p8_5 p10_5 p29_5
  rw [show t + 2 + 4 = t + 6 by omega] at p8_6 p10_6 p29_6
  rw [show t + 3 + 4 = t + 7 by omega] at p8_7 p10_7 p29_7
  rw [g0, g1, g2, g3, g4, g5, g6, g7,
      p8_4, p10_4, p29_4, p8_5, p10_5, p29_5, p8_6, p10_6, p29_6, p8_7, p10_7, p29_7,
      s8_3, s10_3, s29_3, s8_2, s10_2, s29_2, s8_1, s10_1, s29_1]
  cases D 8 t <;> cases D 10 t <;> cases D 29 t <;> decide


/-- **Problem 3 for the Forty-Eighth Left Diagonal (`halfDensity_D_forty_eight`):**
`D 48` has exact asymptotic density `1/2` (`HalfDensity (D 48)`). -/
theorem halfDensity_D_forty_eight : HalfDensity (D 48) :=
  halfDensity_of_block_eight_sum (D 48) 71 D_forty_eight_block_eight_sum

/-- **Problem 3 for the Fiftieth Left Diagonal (`halfDensity_D_fifty`):**
`D 50` has exact asymptotic density `1/2` (`HalfDensity (D 50)`). -/
theorem halfDensity_D_fifty : HalfDensity (D 50) :=
  halfDensity_of_block_eight_sum (D 50) 73 D_fifty_block_eight_sum

/-- **Problem 3 for the Fifty-First Left Diagonal (`halfDensity_D_fifty_one`):**
`D 51` has exact asymptotic density `1/2` (`HalfDensity (D 51)`). -/
theorem halfDensity_D_fifty_one : HalfDensity (D 51) :=
  halfDensity_of_block_eight_sum (D 51) 74 D_fifty_one_block_eight_sum

/-- **Four-Anti-Periodicity of the Fifty-Second Left Diagonal (`D_fifty_two_antiperiodic_four`):**
for every `t ≥ 76`, `D 52 (t + 4) = !D 52 t`. -/
theorem D_fifty_two_antiperiodic_four (t : Nat) (ht : 76 ≤ t) :
    D 52 (t + 4) = !D 52 t := by
  rw [D_fifty_two_eq_gate (t + 4) (by omega), D_fifty_two_eq_gate t ht,
      D_eight_periodic_four t (by omega), D_ten_periodic_four t (by omega),
      D_twenty_nine_antiperiodic_four t (by omega)]
  cases D 8 t <;> cases D 10 t <;> cases D 29 t <;> decide

/-- **Eventual Four-Anti-Periodicity of `D 52` (`evAntiPer_D_fifty_two`):**
`EvAntiPer (D 52) 4` holds unconditionally. -/
theorem evAntiPer_D_fifty_two : EvAntiPer (D 52) 4 :=
  ⟨76, D_fifty_two_antiperiodic_four⟩

/-- **Problem 3 for the Fifty-Second Left Diagonal (`halfDensity_D_fifty_two`):**
`D 52` has exact asymptotic density `1/2` (`HalfDensity (D 52)`). -/
theorem halfDensity_D_fifty_two : HalfDensity (D 52) :=
  halfDensity_of_antiperiodic (by omega) evAntiPer_D_fifty_two

/-! ### 17. Eight-State Cascade Closure Criterion, Exact 370-Step Horizon to `D 399`, and Four-Bit Period-16 Oscillator Extension at `D 400` -/

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

/-- State of the 3-bit period-8 oscillator `(D 8 t, D 10 t, D 29 t)` at time `t`. -/
def osc3State (t : Nat) : (Bool × Bool) × Bool :=
  ((D 8 t, D 10 t), D 29 t)

/-- Closed deterministic transition map `(x, y, z) ↦ (y, !x, xor (!(x && y)) z)` on the 8-state system. -/
def osc3Step (s : (Bool × Bool) × Bool) : (Bool × Bool) × Bool :=
  ((s.1.2, !s.1.1), xor (!(s.1.1 && s.1.2)) s.2)

/-- **One-Step Autonomous Evolution of `osc3State` (`osc3State_succ`):**
for every `t ≥ 32`, `osc3State (t + 1) = osc3Step (osc3State t)`. -/
theorem osc3State_succ (t : Nat) (ht : 32 ≤ t) :
    osc3State (t + 1) = osc3Step (osc3State t) := by
  unfold osc3State osc3Step
  rw [D_eight_succ_eq_D_ten t (by omega), D_ten_succ_eq_not_D_eight t (by omega),
      D_twenty_nine_step_closed t (by omega)]

/-- **Eight-Step Periodicity of `osc3State` (`osc3State_periodic_eight`):**
for every `t ≥ 32`, `osc3State (t + 8) = osc3State t`. -/
theorem osc3State_periodic_eight (t : Nat) (ht : 32 ≤ t) :
    osc3State (t + 8) = osc3State t := by
  unfold osc3State
  rw [show t + 8 = (t + 4) + 4 by omega,
      D_eight_periodic_four (t + 4) (by omega), D_eight_periodic_four t (by omega),
      D_ten_periodic_four (t + 4) (by omega), D_ten_periodic_four t (by omega),
      D_twenty_nine_antiperiodic_four (t + 4) (by omega), D_twenty_nine_antiperiodic_four t (by omega),
      Bool.not_not]

/-- Compact 8-bit truth table on the 8 states of `(D 8 t, D 10 t, D 29 t)`. -/
structure Gate8 where
  b000 : Bool
  b001 : Bool
  b010 : Bool
  b011 : Bool
  b100 : Bool
  b101 : Bool
  b110 : Bool
  b111 : Bool
  deriving DecidableEq

/-- Evaluation of a compact 8-bit truth table `g : Gate8` on a state `s : (Bool × Bool) × Bool`. -/
def Gate8.eval (g : Gate8) (s : (Bool × Bool) × Bool) : Bool :=
  match s.1.1, s.1.2, s.2 with
  | false, false, false => g.b000
  | false, false, true  => g.b001
  | false, true,  false => g.b010
  | false, true,  true  => g.b011
  | true,  false, false => g.b100
  | true,  false, true  => g.b101
  | true,  true,  false => g.b110
  | true,  true,  true  => g.b111

/-- One-step 8-cycle unrolling helper starting from state `s` and initial bit `b`. -/
def unroll8From (g0 g1 : Gate8) (s : (Bool × Bool) × Bool) (b : Bool) : Bool :=
  let s1 := osc3Step s
  let s2 := osc3Step s1
  let s3 := osc3Step s2
  let s4 := osc3Step s3
  let s5 := osc3Step s4
  let s6 := osc3Step s5
  let s7 := osc3Step s6
  let b1 := xor (g0.eval s) (g1.eval s || b)
  let b2 := xor (g0.eval s1) (g1.eval s1 || b1)
  let b3 := xor (g0.eval s2) (g1.eval s2 || b2)
  let b4 := xor (g0.eval s3) (g1.eval s3 || b3)
  let b5 := xor (g0.eval s4) (g1.eval s4 || b4)
  let b6 := xor (g0.eval s5) (g1.eval s5 || b5)
  let b7 := xor (g0.eval s6) (g1.eval s6 || b6)
  xor (g0.eval s7) (g1.eval s7 || b7)

/-- Deterministic truth-table transfer operator `nextGate8 g0 g1` on `Gate8`. -/
def nextGate8 (g0 g1 : Gate8) : Gate8 :=
  { b000 := unroll8From g0 g1 ((false, false), false) false
    b001 := unroll8From g0 g1 ((false, false), true)  false
    b010 := unroll8From g0 g1 ((false, true),  false) false
    b011 := unroll8From g0 g1 ((false, true),  true)  false
    b100 := unroll8From g0 g1 ((true,  false), false) false
    b101 := unroll8From g0 g1 ((true,  false), true)  false
    b110 := unroll8From g0 g1 ((true,  true),  false) false
    b111 := unroll8From g0 g1 ((true,  true),  true)  false }

/-- Boolean test whether `g : Gate8` is non-white (has at least one `true` entry). -/
def Gate8.isNonWhite (g : Gate8) : Bool :=
  g.b000 || g.b001 || g.b010 || g.b011 || g.b100 || g.b101 || g.b110 || g.b111

/-- Eight-state XOR parity of `g : Gate8`. -/
def Gate8.xorParity (g : Gate8) : Bool :=
  xor (xor (xor g.b000 g.b001) (xor g.b010 g.b011))
      (xor (xor g.b100 g.b101) (xor g.b110 g.b111))

/-- **Eight-Step Memory-Erasure Law on `Gate8` (`unroll8From_eq_nextGate8_eval`):**
whenever `g1.isNonWhite = true`, unrolling 8 steps of the Rule 30 diagonal recurrence from any
state `s` and any initial bit `b : Bool` yields `(nextGate8 g0 g1).eval s` independent of `b`. -/
theorem unroll8From_eq_nextGate8_eval (g0 g1 : Gate8)
    (h1 : g1.isNonWhite = true) (s : (Bool × Bool) × Bool) (b : Bool) :
    unroll8From g0 g1 s b = (nextGate8 g0 g1).eval s := by
  rcases s with ⟨⟨x, y⟩, z⟩
  cases b
  · cases x <;> cases y <;> cases z <;> rfl
  · rcases g1 with ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩
    unfold Gate8.isNonWhite at h1
    revert h1
    cases c0
    · cases c1
      · cases c2
        · cases c3
          · cases c4
            · cases c5
              · cases c6
                · cases c7
                  · intro h1; cases h1
                  · intro _; cases x <;> cases y <;> cases z <;> rfl
                · intro _; cases x <;> cases y <;> cases z <;> rfl
              · intro _; cases x <;> cases y <;> cases z <;> rfl
            · intro _; cases x <;> cases y <;> cases z <;> rfl
          · intro _; cases x <;> cases y <;> cases z <;> rfl
        · intro _; cases x <;> cases y <;> cases z <;> rfl
      · intro _; cases x <;> cases y <;> cases z <;> rfl
    · intro _; cases x <;> cases y <;> cases z <;> rfl

/-- **General Eight-State Cascade Closure Theorem (`D_stays_in_eight_state_system_of_nonwhite`):**
for any diagonal index `j` and horizon `t0 ≥ 32`, if `D j t = g0.eval (osc3State t)` and
`D (j + 1) t = g1.eval (osc3State t)` for all `t ≥ t0`, and `g1.isNonWhite = true`, then
for every `t ≥ t0 + 8`, `D (j + 2) t = (nextGate8 g0 g1).eval (osc3State t)`. -/
theorem D_stays_in_eight_state_system_of_nonwhite (j t0 : Nat) (ht0 : 32 ≤ t0)
    (g0 g1 : Gate8)
    (hg0 : ∀ t : Nat, t0 ≤ t → D j t = g0.eval (osc3State t))
    (hg1 : ∀ t : Nat, t0 ≤ t → D (j + 1) t = g1.eval (osc3State t))
    (h1 : g1.isNonWhite = true) :
    ∀ t : Nat, t0 + 8 ≤ t → D (j + 2) t = (nextGate8 g0 g1).eval (osc3State t) := by
  intro t ht
  have hu : t0 ≤ t - 8 := by omega
  have ht_eq : t = (t - 8) + 8 := by omega
  generalize h_u : t - 8 = u at hu ht_eq
  have st0 := D_step j u
  have st1 := D_step j (u + 1)
  have st2 := D_step j (u + 2)
  have st3 := D_step j (u + 3)
  have st4 := D_step j (u + 4)
  have st5 := D_step j (u + 5)
  have st6 := D_step j (u + 6)
  have st7 := D_step j (u + 7)
  have o1 := osc3State_succ u (by omega)
  have o2 := osc3State_succ (u + 1) (by omega)
  have o3 := osc3State_succ (u + 2) (by omega)
  have o4 := osc3State_succ (u + 3) (by omega)
  have o5 := osc3State_succ (u + 4) (by omega)
  have o6 := osc3State_succ (u + 5) (by omega)
  have o7 := osc3State_succ (u + 6) (by omega)
  rw [show u + 1 + 1 = u + 2 by omega] at o2 st1
  rw [show u + 2 + 1 = u + 3 by omega] at o3 st2
  rw [show u + 3 + 1 = u + 4 by omega] at o4 st3
  rw [show u + 4 + 1 = u + 5 by omega] at o5 st4
  rw [show u + 5 + 1 = u + 6 by omega] at o6 st5
  rw [show u + 6 + 1 = u + 7 by omega] at o7 st6
  rw [show u + 7 + 1 = u + 8 by omega] at st7
  rw [hg0 u hu, hg1 u hu] at st0
  rw [hg0 (u + 1) (by omega), hg1 (u + 1) (by omega), o1] at st1
  rw [hg0 (u + 2) (by omega), hg1 (u + 2) (by omega), o2, o1] at st2
  rw [hg0 (u + 3) (by omega), hg1 (u + 3) (by omega), o3, o2, o1] at st3
  rw [hg0 (u + 4) (by omega), hg1 (u + 4) (by omega), o4, o3, o2, o1] at st4
  rw [hg0 (u + 5) (by omega), hg1 (u + 5) (by omega), o5, o4, o3, o2, o1] at st5
  rw [hg0 (u + 6) (by omega), hg1 (u + 6) (by omega), o6, o5, o4, o3, o2, o1] at st6
  rw [hg0 (u + 7) (by omega), hg1 (u + 7) (by omega), o7, o6, o5, o4, o3, o2, o1] at st7
  have h_era := unroll8From_eq_nextGate8_eval g0 g1 h1 (osc3State u) (D (j + 2) u)
  unfold unroll8From at h_era
  dsimp only at h_era
  rw [← st0, ← st1, ← st2, ← st3, ← st4, ← st5, ← st6, ← st7] at h_era
  rw [ht_eq, osc3State_periodic_eight u (by omega), h_era]

/-- Strict normalizer forcing a `Bool` to a literal `true` or `false` before continuing. -/
def withStrictBool {α : Type} (b : Bool) (k : Bool → α) : α :=
  match b with
  | true => k true
  | false => k false

theorem withStrictBool_eq {α : Type} (b : Bool) (k : Bool → α) :
    withStrictBool b k = k b := by
  cases b <;> rfl

/-- Strict normalizer forcing all 8 fields of `g : Gate8` to literal `true`/`false` before continuing. -/
def withStrictGate8 {α : Type} (g : Gate8) (k : Gate8 → α) : α :=
  withStrictBool g.b000 fun v0 =>
  withStrictBool g.b001 fun v1 =>
  withStrictBool g.b010 fun v2 =>
  withStrictBool g.b011 fun v3 =>
  withStrictBool g.b100 fun v4 =>
  withStrictBool g.b101 fun v5 =>
  withStrictBool g.b110 fun v6 =>
  withStrictBool g.b111 fun v7 =>
  k ⟨v0, v1, v2, v3, v4, v5, v6, v7⟩

theorem withStrictGate8_eq {α : Type} (g : Gate8) (k : Gate8 → α) :
    withStrictGate8 g k = k g := by
  rcases g with ⟨v0, v1, v2, v3, v4, v5, v6, v7⟩
  unfold withStrictGate8
  rw [withStrictBool_eq, withStrictBool_eq, withStrictBool_eq, withStrictBool_eq,
      withStrictBool_eq, withStrictBool_eq, withStrictBool_eq, withStrictBool_eq]

/-- Initial 8-bit truth table for `D 29` (`s.2`). -/
def gate8_D29 : Gate8 := ⟨false, true, false, true, false, true, false, true⟩

/-- Initial 8-bit truth table for `D 30` (`true`). -/
def gate8_D30 : Gate8 := ⟨true, true, true, true, true, true, true, true⟩

/-- Combined state `(g0, g1, allNonWhite)` for linear `O(k)` kernel evaluation of the 8-state cascade. -/
structure CascadeState8 where
  g0 : Gate8
  g1 : Gate8
  allNonWhite : Bool
  deriving DecidableEq

/-- One-step strict transition on `CascadeState8` that forces `ok'` and `g2` to literals before constructing the state. -/
def nextCascadeState8 (st : CascadeState8) : CascadeState8 :=
  withStrictGate8 st.g0 fun g0 =>
  withStrictGate8 st.g1 fun g1 =>
  withStrictBool (st.allNonWhite && g1.isNonWhite) fun ok' =>
  withStrictGate8 (nextGate8 g0 g1) fun g2 =>
  ⟨g1, g2, ok'⟩

/-- Iterated 8-state cascade `cascadeState8 k` representing `(D (29 + k), D (30 + k), allNonWhiteUpTo k)`. -/
def cascadeState8 : Nat → CascadeState8
  | 0 => ⟨gate8_D29, gate8_D30, true⟩
  | k + 1 => nextCascadeState8 (cascadeState8 k)

theorem cascadeState8_succ (k : Nat) :
    cascadeState8 (k + 1) =
      ⟨(cascadeState8 k).g1, nextGate8 (cascadeState8 k).g0 (cascadeState8 k).g1,
       (cascadeState8 k).allNonWhite && (cascadeState8 k).g1.isNonWhite⟩ := by
  change nextCascadeState8 (cascadeState8 k) = _
  unfold nextCascadeState8
  rw [withStrictGate8_eq, withStrictGate8_eq, withStrictBool_eq, withStrictGate8_eq]

/-- **Exact 369-Step Non-White Cascade Prefix (`cascadeState8_369_allNonWhite`):**
for all `m < 369` (covering `D 30` through `D 398`), `(cascadeState8 m).g1.isNonWhite = true`. -/
theorem cascadeState8_369_allNonWhite : (cascadeState8 369).allNonWhite = true := by decide

theorem cascadeState8_369_g1_eq_white :
    (cascadeState8 369).g1 = ⟨false, false, false, false, false, false, false, false⟩ := by decide

theorem cascadeState8_369_g0_odd_parity : (cascadeState8 369).g0.xorParity = true := by decide

/-- **Inductive `N`-Step Gate-Cascade Theorem on the 8-State System (`D_twenty_nine_add_eq_cascadeState8`):**
for every `k : Nat`, if `(cascadeState8 k).allNonWhite = true`, then for all `t ≥ 33 + 8 * k`,
`D (29 + k) t = (cascadeState8 k).g0.eval (osc3State t)` and
`D (30 + k) t = (cascadeState8 k).g1.eval (osc3State t)`. -/
theorem D_twenty_nine_add_eq_cascadeState8 : ∀ k : Nat,
    (cascadeState8 k).allNonWhite = true →
    (∀ t : Nat, 33 + 8 * k ≤ t → D (29 + k) t = (cascadeState8 k).g0.eval (osc3State t)) ∧
    (∀ t : Nat, 33 + 8 * k ≤ t → D (30 + k) t = (cascadeState8 k).g1.eval (osc3State t))
  | 0, _ => by
    refine ⟨?_, ?_⟩
    · intro t _
      unfold cascadeState8 gate8_D29 osc3State Gate8.eval
      cases D 8 t <;> cases D 10 t <;> cases D 29 t <;> rfl
    · intro t ht
      rw [D_thirty_eq_true t (Nat.le_trans (by decide) ht)]
      unfold cascadeState8 gate8_D30 osc3State Gate8.eval
      cases D 8 t <;> cases D 10 t <;> cases D 29 t <;> rfl
  | k + 1, hall => by
    rw [cascadeState8_succ] at hall ⊢
    rcases Bool.and_eq_true_iff.mp hall with ⟨hk, hnw⟩
    rcases D_twenty_nine_add_eq_cascadeState8 k hk with ⟨ih1, ih2⟩
    refine ⟨?_, ?_⟩
    · intro t ht
      rw [show 29 + (k + 1) = 30 + k by omega]
      exact ih2 t (by omega)
    · intro t ht
      rw [show 30 + (k + 1) = (29 + k) + 2 by omega]
      exact D_stays_in_eight_state_system_of_nonwhite (29 + k) (33 + 8 * k) (by omega)
        (cascadeState8 k).g0 (cascadeState8 k).g1 ih1
        (fun s hs => by rw [show 29 + k + 1 = 30 + k by omega]; exact ih2 s hs)
        hnw t (by omega)

/-- Monotonicity of `allNonWhite`: if `(cascadeState8 n).allNonWhite = true` and `k ≤ n`,
then `(cascadeState8 k).allNonWhite = true`. -/
theorem cascadeState8_allNonWhite_of_le {k n : Nat} (hkn : k ≤ n)
    (hn : (cascadeState8 n).allNonWhite = true) :
    (cascadeState8 k).allNonWhite = true := by
  induction n with
  | zero =>
    have hk0 : k = 0 := by omega
    subst hk0; exact hn
  | succ m ih =>
    rcases (by omega : k ≤ m ∨ k = m + 1) with hle | rfl
    · rw [cascadeState8_succ] at hn
      exact ih hle (Bool.and_eq_true_iff.mp hn).1
    · exact hn

/-- **Uniform Period-8 Closure Across All 371 Diagonals `D 29 .. D 399` (`D_twenty_nine_add_periodic_eight`):**
for every offset `k ≤ 369` and every `t ≥ 33 + 8 * k`, both `D (29 + k)` and `D (30 + k)` are
8-periodic from `33 + 8 * k` on (`D (29 + k) (t + 8) = D (29 + k) t` and `D (30 + k) (t + 8) = D (30 + k) t`),
covering every diagonal `D 29` through `D 399`. -/
theorem D_twenty_nine_add_periodic_eight {k : Nat} (hk : k ≤ 369) (t : Nat) (ht : 33 + 8 * k ≤ t) :
    D (29 + k) (t + 8) = D (29 + k) t ∧ D (30 + k) (t + 8) = D (30 + k) t := by
  have hall := cascadeState8_allNonWhite_of_le hk cascadeState8_369_allNonWhite
  rcases D_twenty_nine_add_eq_cascadeState8 k hall with ⟨h29, h30⟩
  refine ⟨?_, ?_⟩
  · rw [h29 (t + 8) (by omega), h29 t ht, osc3State_periodic_eight t (by omega)]
  · rw [h30 (t + 8) (by omega), h30 t ht, osc3State_periodic_eight t (by omega)]

/-- **Exact Eight-State Gate Law for `D 398` (`D_three_hundred_ninety_eight_eq_gate`):**
for every `t ≥ 2985` (`33 + 8 * 369`), `D 398 t = (cascadeState8 369).g0.eval (osc3State t)`. -/
theorem D_three_hundred_ninety_eight_eq_gate (t : Nat) (ht : 2985 ≤ t) :
    D 398 t = (cascadeState8 369).g0.eval (osc3State t) := by
  have h := (D_twenty_nine_add_eq_cascadeState8 369 cascadeState8_369_allNonWhite).1 t (by omega)
  rw [show (29 + 369 : Nat) = 398 by rfl] at h
  exact h

/-- **Fourth All-White Left Diagonal at `D 399` (`D_three_hundred_ninety_nine_eq_false`):**
for every `t ≥ 2985` (`33 + 8 * 369`), `D 399 t = false`. -/
theorem D_three_hundred_ninety_nine_eq_false (t : Nat) (ht : 2985 ≤ t) :
    D 399 t = false := by
  have h := (D_twenty_nine_add_eq_cascadeState8 369 cascadeState8_369_allNonWhite).2 t (by omega)
  rw [show (30 + 369 : Nat) = 399 by rfl, cascadeState8_369_g1_eq_white] at h
  rw [h]
  unfold osc3State Gate8.eval
  cases D 8 t <;> cases D 10 t <;> cases D 29 t <;> rfl

theorem D_step_eq_xor_of_white (j t : Nat) (hw : D (j + 1) t = false) :
    D (j + 2) (t + 1) = xor (D j t) (D (j + 2) t) := by
  have h := D_step j t
  rw [hw, Bool.false_or] at h
  exact h

/-- **Orbit XOR-Parity Invariance Law on `Gate8` (`osc3_orbit_xor_eq_xorParity`):**
for any `g : Gate8` and any `t ≥ 32`, the 8-step XOR sum of `g.eval (osc3State (t + k))`
for `k = 0 .. 7` equals `g.xorParity`. -/
theorem osc3_orbit_xor_eq_xorParity (g : Gate8) (t : Nat) (ht : 32 ≤ t) :
    xor (xor (xor (g.eval (osc3State t)) (g.eval (osc3State (t + 1))))
             (xor (g.eval (osc3State (t + 2))) (g.eval (osc3State (t + 3)))))
        (xor (xor (g.eval (osc3State (t + 4))) (g.eval (osc3State (t + 5))))
             (xor (g.eval (osc3State (t + 6))) (g.eval (osc3State (t + 7))))) = g.xorParity := by
  have o1 := osc3State_succ t ht
  have o2 := osc3State_succ (t + 1) (by omega)
  have o3 := osc3State_succ (t + 2) (by omega)
  have o4 := osc3State_succ (t + 3) (by omega)
  have o5 := osc3State_succ (t + 4) (by omega)
  have o6 := osc3State_succ (t + 5) (by omega)
  have o7 := osc3State_succ (t + 6) (by omega)
  rw [show t + 1 + 1 = t + 2 by omega] at o2
  rw [show t + 2 + 1 = t + 3 by omega] at o3
  rw [show t + 3 + 1 = t + 4 by omega] at o4
  rw [show t + 4 + 1 = t + 5 by omega] at o5
  rw [show t + 5 + 1 = t + 6 by omega] at o6
  rw [show t + 6 + 1 = t + 7 by omega] at o7
  rw [o7, o6, o5, o4, o3, o2, o1]
  rcases g with ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩
  generalize osc3State t = s
  rcases s with ⟨⟨x, y⟩, z⟩
  revert b0 b1 b2 b3 b4 b5 b6 b7 x y z
  decide

/-- **Exact Odd Eight-Step XOR Parity of `D 398` (`D_three_hundred_ninety_eight_eight_step_xor_eq_true`):**
for every `t ≥ 2985`, the 8-step XOR sum of `D 398 (t + k)` across `k = 0 .. 7` equals `true`. -/
theorem D_three_hundred_ninety_eight_eight_step_xor_eq_true (t : Nat) (ht : 2985 ≤ t) :
    xor (xor (xor (D 398 t) (D 398 (t + 1))) (xor (D 398 (t + 2)) (D 398 (t + 3))))
        (xor (xor (D 398 (t + 4)) (D 398 (t + 5))) (xor (D 398 (t + 6)) (D 398 (t + 7)))) = true := by
  rw [D_three_hundred_ninety_eight_eq_gate t ht,
      D_three_hundred_ninety_eight_eq_gate (t + 1) (by omega),
      D_three_hundred_ninety_eight_eq_gate (t + 2) (by omega),
      D_three_hundred_ninety_eight_eq_gate (t + 3) (by omega),
      D_three_hundred_ninety_eight_eq_gate (t + 4) (by omega),
      D_three_hundred_ninety_eight_eq_gate (t + 5) (by omega),
      D_three_hundred_ninety_eight_eq_gate (t + 6) (by omega),
      D_three_hundred_ninety_eight_eq_gate (t + 7) (by omega),
      osc3_orbit_xor_eq_xorParity (cascadeState8 369).g0 t (by omega),
      cascadeState8_369_g0_odd_parity]

/-- **General Bit-Addition / Eight-Anti-Periodicity Theorem Across a White Diagonal (`D_antiperiodic_eight_of_white_and_odd_gate`):**
if `D j t = g.eval (osc3State t)` (`t ≥ t0 ≥ 32`) with `g.xorParity = true` and
`D (j + 1) t = false` (`t ≥ t0`), then `D (j + 2) (t + 8) = !D (j + 2) t` for all `t ≥ t0`. -/
theorem D_antiperiodic_eight_of_white_and_odd_gate (j t0 : Nat) (ht0 : 32 ≤ t0)
    (g : Gate8)
    (hg : ∀ t : Nat, t0 ≤ t → D j t = g.eval (osc3State t))
    (hpar : g.xorParity = true)
    (hw : ∀ t : Nat, t0 ≤ t → D (j + 1) t = false) :
    ∀ t : Nat, t0 ≤ t → D (j + 2) (t + 8) = !D (j + 2) t := by
  intro t ht
  have s0 := D_step_eq_xor_of_white j t (hw t ht)
  have s1 := D_step_eq_xor_of_white j (t + 1) (hw (t + 1) (by omega))
  have s2 := D_step_eq_xor_of_white j (t + 2) (hw (t + 2) (by omega))
  have s3 := D_step_eq_xor_of_white j (t + 3) (hw (t + 3) (by omega))
  have s4 := D_step_eq_xor_of_white j (t + 4) (hw (t + 4) (by omega))
  have s5 := D_step_eq_xor_of_white j (t + 5) (hw (t + 5) (by omega))
  have s6 := D_step_eq_xor_of_white j (t + 6) (hw (t + 6) (by omega))
  have s7 := D_step_eq_xor_of_white j (t + 7) (hw (t + 7) (by omega))
  rw [show t + 1 + 1 = t + 2 by omega] at s1
  rw [show t + 2 + 1 = t + 3 by omega] at s2
  rw [show t + 3 + 1 = t + 4 by omega] at s3
  rw [show t + 4 + 1 = t + 5 by omega] at s4
  rw [show t + 5 + 1 = t + 6 by omega] at s5
  rw [show t + 6 + 1 = t + 7 by omega] at s6
  rw [show t + 7 + 1 = t + 8 by omega] at s7
  have ho : xor (xor (xor (D j t) (D j (t + 1))) (xor (D j (t + 2)) (D j (t + 3))))
                (xor (xor (D j (t + 4)) (D j (t + 5))) (xor (D j (t + 6)) (D j (t + 7)))) = true := by
    rw [hg t ht, hg (t + 1) (by omega), hg (t + 2) (by omega), hg (t + 3) (by omega),
        hg (t + 4) (by omega), hg (t + 5) (by omega), hg (t + 6) (by omega), hg (t + 7) (by omega),
        osc3_orbit_xor_eq_xorParity g t (by omega), hpar]
  rw [s7, s6, s5, s4, s3, s2, s1, s0]
  revert ho
  cases D j t <;> cases D j (t + 1) <;> cases D j (t + 2) <;> cases D j (t + 3) <;>
    cases D j (t + 4) <;> cases D j (t + 5) <;> cases D j (t + 6) <;> cases D j (t + 7) <;>
    cases D (j + 2) t <;> decide

/-- **Eight-Anti-Periodicity of the Four-Hundredth Left Diagonal (`D_four_hundred_antiperiodic_eight`):**
for every `t ≥ 2985`, `D 400 (t + 8) = !D 400 t` (spawning the 4th oscillator bit of period 16). -/
theorem D_four_hundred_antiperiodic_eight (t : Nat) (ht : 2985 ≤ t) :
    D 400 (t + 8) = !D 400 t :=
  D_antiperiodic_eight_of_white_and_odd_gate 398 2985 (by decide)
    (cascadeState8 369).g0 D_three_hundred_ninety_eight_eq_gate
    cascadeState8_369_g0_odd_parity D_three_hundred_ninety_nine_eq_false t ht

theorem evAntiPer_D_four_hundred : EvAntiPer (D 400) 8 :=
  ⟨2985, D_four_hundred_antiperiodic_eight⟩

/-- **Problem 3 for the Four-Hundredth Left Diagonal (`halfDensity_D_four_hundred`):**
`D 400` has exact asymptotic density `1/2` (`HalfDensity (D 400)`). -/
theorem halfDensity_D_four_hundred : HalfDensity (D 400) :=
  halfDensity_of_antiperiodic (by omega) evAntiPer_D_four_hundred

/-- **Impossibility of Representing `D 400` Inside the Eight-State System (`not_D_four_hundred_in_eight_state_system`):**
for every truth table `g : Gate8` on the 3-bit oscillator `(D 8, D 10, D 29)` and every horizon `T : Nat`,
`D 400` cannot equal `g.eval (osc3State t)` for all `t ≥ T`, proving that `D 399` strictly adds a 4th bit. -/
theorem not_D_four_hundred_in_eight_state_system (g : Gate8) (T : Nat) :
    ¬ (∀ t : Nat, T ≤ t → D 400 t = g.eval (osc3State t)) := by
  intro hg
  let t0 : Nat := max T 2985
  have hanti := D_four_hundred_antiperiodic_eight t0 (by omega)
  have h1 := hg t0 (by omega)
  have h2 := hg (t0 + 8) (by omega)
  rw [osc3State_periodic_eight t0 (by omega), ← h1, hanti] at h2
  revert h2
  cases D 400 t0 <;> decide

/-- State of the extended 4-bit period-16 oscillator `((D 8 t, D 10 t, D 29 t), D 400 t)` at time `t`. -/
def osc4State (t : Nat) : ((Bool × Bool) × Bool) × Bool :=
  (osc3State t, D 400 t)

/-- Closed deterministic transition map on the 16-state system incorporating the 4th bit `D 400`. -/
def osc4Step (s : ((Bool × Bool) × Bool) × Bool) : ((Bool × Bool) × Bool) × Bool :=
  (osc3Step s.1, xor ((cascadeState8 369).g0.eval s.1) s.2)

/-- **Closed Autonomous Evolution of the 4-Bit Period-16 Oscillator (`osc4State_succ`):**
for every `t ≥ 2985`, `osc4State (t + 1) = osc4Step (osc4State t)`. -/
theorem osc4State_succ (t : Nat) (ht : 2985 ≤ t) :
    osc4State (t + 1) = osc4Step (osc4State t) := by
  unfold osc4State osc4Step
  rw [osc3State_succ t (by omega),
      D_step_eq_xor_of_white 398 t (D_three_hundred_ninety_nine_eq_false t ht),
      D_three_hundred_ninety_eight_eq_gate t ht]

/-- **Half-Cycle Negation and Period-16 Law of the 4-Bit Oscillator (`osc4State_half_cycle_and_period_sixteen`):**
for every `t ≥ 2985`, advancing `osc4State` by 8 steps preserves `osc3State t` while negating the 4th bit
(`osc4State (t + 8) = (osc3State t, !D 400 t)`), and advancing by 16 steps returns to `osc4State t`. -/
theorem osc4State_half_cycle_and_period_sixteen (t : Nat) (ht : 2985 ≤ t) :
    osc4State (t + 8) = (osc3State t, !D 400 t) ∧ osc4State (t + 16) = osc4State t := by
  refine ⟨?_, ?_⟩
  · unfold osc4State
    rw [osc3State_periodic_eight t (by omega), D_four_hundred_antiperiodic_eight t ht]
  · unfold osc4State
    rw [show t + 16 = (t + 8) + 8 by omega,
        osc3State_periodic_eight (t + 8) (by omega), osc3State_periodic_eight t (by omega),
        D_four_hundred_antiperiodic_eight (t + 8) (by omega), D_four_hundred_antiperiodic_eight t ht,
        Bool.not_not]



end Rule30LeftAntiPeriod
end Ruliology.CellularAutomata
