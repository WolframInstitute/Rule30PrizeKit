module

public import Ruliology.CellularAutomata.Rule30Diagonals
public import Ruliology.CellularAutomata.Rule30Window
public import Ruliology.CellularAutomata.Rule30DifferenceOrder

/-!
# Rule 30: the periods of the right diagonals

`R j t = cell t (t - j)` is the `j`-th diagonal from the right edge. `Rule30Diagonals.R_periodic`
says it repeats with period `2^j`. Here the periods are pinned down much further. Write
`Per j p` for "`R j` repeats with period `p` from time `0`", and `e_j` for the least `e` with
`Per j (2^e)` (`IsE j e`; it exists by `exists_IsE`).

**Monotonicity and the doubling rule.**
* `per_mono_all`: if `R (j + 1)` repeats with some period `H`, so does every `R i`, `i ≤ j`.
  So `e_0 ≤ e_1 ≤ e_2 ≤ …` (`e_mono`). The proof descends from a white light-cone triangle that
  diagonal `j + 1` repeats at time `H`: two white diagonals force the two before them white
  (`Z_down`).
* `shift_formula`: if `R j` has period `H`, then `R (j+1) (t + H) = R (j+1) t xor R (j+1) H`.
* `e_step`: **`e_{j+1} = e_j + [R_{j+1}(2^{e_j}) = 1]`**: the period doubles exactly when the cell
  at time `2^{e_j}` on the next diagonal is black (`per_succ_iff`), and then a shift by half the
  new period complements the diagonal (`antiperiod`) and every window of one period is exactly
  half black (`half_black`).
* `S_rule`, `inp_least_period`: for `j ≥ 3` the input `R (j-1) || R (j-2)` of diagonal `j` has
  least period `2^{e_{j-1}}`, and `e_j - e_{j-1}` is the parity of the number of black input
  cells in one such period.
* `no_three`: the period never doubles three times in a row.

**Bounds.**
* `period_gt`: every period of `R j`, `j ≥ 1`, exceeds `⌈j / 2⌉`; `not_per_small`:
  `j < 2^(e_j + 1)`. So the periods are unbounded.
* `per_bound`: `j ≤ 2^(e_j + 1) - 2`, that is `e_j ≥ log₂ (j + 2) - 1`.
* `per_upper`: `e_j ≤ (2j + 1) / 3` for `j ≥ 2`.
* `per_upper_half`: `R j` has period `2 ^ B j`, where `B j = ⌈j / 2⌉ + Q 0 ⌊j / 2⌋`
  (`Rule30RecordCharge.B`) and `Q 0` is the inverse of a tower of twos, so
  `e_j ≤ j / 2 + O(log* j)` (`e_le_B`); at time `2 ^ B n` the diagonals `R 1, …, R n` are white
  again (`wall_return`). Explicitly `e_j ≤ ⌈j / 2⌉ + 3` for `j < 2^22 + 38`
  (`per_upper_half_explicit`), and `B j < (2j + 1) / 3` for every `j ≥ 18`
  (`Rule30RecordCharge.B_lt_two_thirds`), so it is sharper than `per_upper` from there on. The
  proof pairs the diagonals and runs a record-charge account (`Rule30RecordCharge`) whose
  resource is the difference order of a diagonal over one period (`Rule30DifferenceOrder`).
* `per_14`, `per_23`, `not_half_lower`: `e_14 ≤ 6` and `e_23 ≤ 8` (kernel computation of rows
  `64` and `256`), so the guess `e_j ≥ ⌊j/2⌋` is false.

**Rows at powers of two.**
* `per_iff_gap`: `R n` has period `2^k` iff row `2^k` has `n` white cells left of its right
  edge.
* `rows_at_powers_of_two`: for every `k` there is `J` with `k ≤ J ≤ 2^(k+1) - 2` such that the
  diagonals of period `2^k` are exactly `R 0, …, R J`; every row `2^k u`, `u` odd, reads
  `1 0^J 1` leftwards from its right edge (`zero_gap_cell`); and row `2^k - 1` ends in `J + 1`
  black cells preceded by a white one (`last_one`, `last_white`).
* `restart`, `row_restart`, `center_restart`, `column_continuity`: the pattern restarts at the
  right edge. Row `2^k + s` ends with a copy of row `s` (for `2s ≤ J`, all of it).
  Column `2^k u` repeats `c(0), …, c(J)`, and columns `p` and `p + 2^k u` agree `s` steps after
  the right edge reaches them whenever `R s` has period `2^k`.
* `center_black_lt`: a black center cell `c(t)` lies in the first period of its diagonal:
  `t < 2^{e_t}`.

None of this reaches the center column `c(t) = R t t`. It sits on diagonal `t` at time `t`, and
when it is black it lies inside the first period `2^{e_t}` of that diagonal (`center_black_lt`).
The proved bounds leave the growth of the period `2^{e_j}` between linear (`j + 2 ≤ 2^{e_j + 1}`)
and `2^{B j}`, `B j = j / 2 + O(log* j)`; numerically `e_j ≈ 0.43 j`.

The diagonals and their recurrence are in `Rule30Diagonals`.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30RightPeriods

open Rule30Jen Rule30Diagonals

/-! ### Basic facts -/

theorem R_congr {j j' t t' : Nat} (hj : j = j') (ht : t = t') : R j t = R j' t' := by
  subst hj ht; rfl

/-- Outside the light cone the diagonal is white. -/
theorem R_lt {j t : Nat} (h : 2 * t < j) : R j t = false :=
  cell_eq_false_of_lt t _ (by omega)

theorem R_init {j : Nat} (h : 1 ≤ j) : R j 0 = false := R_lt (by omega)

/-- The left edge (or its right neighbour) is black where diagonal `j ≥ 1` enters the light cone. -/
theorem R_half {j : Nat} (h : 1 ≤ j) : R j ((j + 1) / 2) = true := by
  obtain ⟨s, hs⟩ : ∃ s, j = 2 * s ∨ j = 2 * s + 1 := ⟨j / 2, by omega⟩
  rcases hs with rfl | rfl
  · show cell ((2 * s + 1) / 2) ((((2 * s + 1) / 2 : Nat) : Int) - ((2 * s : Nat) : Int)) = true
    rw [show (2 * s + 1) / 2 = s by omega,
      cell_congr (show ((s : Nat) : Int) - ((2 * s : Nat) : Int) = -(s : Int) by omega)]
    exact cell_left_edge s
  · show cell ((2 * s + 1 + 1) / 2) ((((2 * s + 1 + 1) / 2 : Nat) : Int) - ((2 * s + 1 : Nat) : Int))
      = true
    rw [show (2 * s + 1 + 1) / 2 = s + 1 by omega,
      cell_congr (show (((s + 1 : Nat)) : Int) - ((2 * s + 1 : Nat) : Int)
        = ((1 : Nat) : Int) - ((s + 1 : Nat) : Int) by omega)]
    exact D_one s

theorem R_step' {a b c t : Nat} (hb : b = a + 1) (hc : c = a + 2) :
    R c (t + 1) = xor (R c t) (R b t || R a t) := by
  subst hb hc; exact R_step a t

theorem R_one_eq : ∀ t, R 1 t = (t % 2 == 1)
  | 0 => R_init (by omega)
  | t + 1 => by
    rw [R_one_succ, R_one_eq t]
    rcases Nat.mod_two_eq_zero_or_one t with h | h
    · have h' : (t + 1) % 2 = 1 := by omega
      simp [h, h']
    · have h' : (t + 1) % 2 = 0 := by omega
      simp [h, h']

theorem R_two_eq_one : ∀ t, R 2 t = R 1 t
  | 0 => by rw [R_init (by omega), R_init (by omega)]
  | t + 1 => by
    rw [R_step' (a := 0) (b := 1) (c := 2) rfl rfl, R_one_succ, R_zero, R_two_eq_one t]
    cases R 1 t <;> rfl

theorem mod2_add (a b : Nat) : ((a + b) % 2 == 1) = xor (a % 2 == 1) (b % 2 == 1) := by
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
  rcases Nat.mod_two_eq_zero_or_one b with hb | hb
  · have h : (a + b) % 2 = 0 := by omega
    simp [h, ha, hb]
  · have h : (a + b) % 2 = 1 := by omega
    simp [h, ha, hb]
  · have h : (a + b) % 2 = 1 := by omega
    simp [h, ha, hb]
  · have h : (a + b) % 2 = 0 := by omega
    simp [h, ha, hb]

/-! ### Periods -/

/-- `R j` repeats with period `p`. -/
def Per (j p : Nat) : Prop := ∀ t, R j (t + p) = R j t

theorem Per.mul {j p : Nat} (h : Per j p) : ∀ n, Per j (n * p)
  | 0 => fun t => by simp
  | n + 1 => fun t => by
    rw [show t + (n + 1) * p = (t + n * p) + p by rw [Nat.succ_mul]; omega, h, Per.mul h n t]

theorem Per.pow_mono {j a b : Nat} (h : Per j (2 ^ a)) (hab : a ≤ b) : Per j (2 ^ b) := by
  have := h.mul (2 ^ (b - a))
  rwa [← Nat.pow_add, show b - a + a = b by omega] at this

theorem per_zero (p : Nat) : Per 0 p := fun t => by rw [R_zero, R_zero]

theorem per_one (k : Nat) : Per 1 (2 ^ (k + 1)) := fun t => by
  rw [R_one_eq, R_one_eq, Nat.pow_succ]
  have : (t + 2 ^ k * 2) % 2 = t % 2 := by omega
  rw [this]

theorem per_R_periodic (j : Nat) : Per j (2 ^ j) := R_periodic j

/-- A sequence periodic with period `p` and equal to `b` at `0` equals `b` at every multiple of
`p`. -/
theorem Per.at_mul {j p : Nat} (h : Per j p) (n : Nat) : R j (p * n) = R j 0 := by
  have := h.mul n 0
  rwa [Nat.zero_add, Nat.mul_comm] at this

/-- An eventually-white diagonal is impossible: a diagonal `j ≥ 1` with period `1` is constant,
hence white, but it meets the left edge. -/
theorem not_per_one {j : Nat} (hj : 1 ≤ j) : ¬ Per j 1 := by
  intro h
  have hc : ∀ t, R j t = false := by
    intro t
    induction t with
    | zero => exact R_init hj
    | succ t ih => rw [h t, ih]
  have := R_half hj
  rw [hc] at this
  exact absurd this (by decide)

/-! ### Periods of general sequences -/

/-- `f` repeats with period `p` from time `0`. -/
def PerF (f : Nat → Bool) (p : Nat) : Prop := ∀ t, f (t + p) = f t

theorem PerF.mul {f : Nat → Bool} {p : Nat} (h : PerF f p) : ∀ n, PerF f (n * p)
  | 0 => fun t => by rw [Nat.zero_mul, Nat.add_zero]
  | n + 1 => fun t => by
    rw [Nat.add_mul, Nat.one_mul, ← Nat.add_assoc, h, PerF.mul h n t]


theorem PerF.mod {f : Nat → Bool} {p q : Nat} (hp : PerF f p) (hq : PerF f q) :
    PerF f (q % p) := by
  intro t
  have hd : q % p + q / p * p = q := by rw [Nat.mul_comm]; exact Nat.mod_add_div q p
  have e := hp.mul (q / p) (t + q % p)
  rw [Nat.add_assoc, hd, hq] at e
  exact e.symm

/-- Periods `p` and `q` give the period `gcd p q`. -/
theorem PerF.gcd {f : Nat → Bool} (p q : Nat) : PerF f p → PerF f q → PerF f (Nat.gcd p q) := by
  refine Nat.gcd.induction (P := fun p q => PerF f p → PerF f q → PerF f (Nat.gcd p q)) p q ?_ ?_
  · intro n _ hn
    rw [Nat.gcd_zero_left]; exact hn
  · intro m n _ ih hm hn
    rw [Nat.gcd_rec]
    exact ih (hm.mod hn) hm

/-! ### Accumulation -/

/-- A sequence that accumulates a `L`-periodic input shifts by a constant over `L` steps. -/
theorem accum_shift {x g : Nat → Bool} {L : Nat} (hx : ∀ t, x (t + 1) = xor (x t) (g t))
    (hg : ∀ t, g (t + L) = g t) : ∀ t, x (t + L) = xor (x t) (xor (x L) (x 0)) := by
  have hconst : ∀ t, xor (x (t + L)) (x t) = xor (x L) (x 0) := by
    intro t
    induction t with
    | zero => rw [Nat.zero_add]
    | succ t ih =>
      rw [show t + 1 + L = (t + L) + 1 by omega, hx (t + L), hx t, hg t, ← ih]
      cases x (t + L) <;> cases x t <;> cases g t <;> rfl
  intro t
  have h := hconst t
  revert h
  cases x (t + L) <;> cases x t <;> cases xor (x L) (x 0) <;> simp

/-! ### The halving lemma -/

/-- Diagonals `a` and `a + 1` are white at times `H + t`, `t < M`. -/
def Z (H a M : Nat) : Prop := ∀ t, t < M → R a (H + t) = false ∧ R (a + 1) (H + t) = false

/-- Two white diagonals force the two before them to be white one step less long: the `or` in
`R (a+3) (s+1) = R (a+3) s xor (R (a+2) s || R (a+1) s)` is false only if both inputs are. -/
theorem Z_down {H a M : Nat} (h : Z H (a + 2) (M + 1)) : Z H a M := by
  intro t ht
  obtain ⟨h2, h3⟩ := h t (by omega)
  obtain ⟨h2', h3'⟩ := h (t + 1) (by omega)
  have s3 := R_step' (a := a + 1) (b := a + 2) (c := a + 2 + 1) (t := H + t) (by omega) (by omega)
  have s2 := R_step' (a := a) (b := a + 1) (c := a + 2) (t := H + t) rfl rfl
  rw [show H + t + 1 = H + (t + 1) by omega] at s3 s2
  rw [h3', h3, h2] at s3
  rw [h2', h2] at s2
  constructor
  · revert s2; cases R (a + 1) (H + t) <;> cases R a (H + t) <;> simp
  · revert s3; cases R (a + 1) (H + t) <;> simp

theorem Z_iter {H a M : Nat} : ∀ s, Z H (a + 2 * s) (M + s) → Z H a M
  | 0, h => by simpa using h
  | s + 1, h => by
    have h' : Z H ((a + 2) + 2 * s) ((M + 1) + s) := by
      rw [show (a + 2) + 2 * s = a + 2 * (s + 1) by omega,
        show (M + 1) + s = M + (s + 1) by omega]
      exact h
    exact Z_down (Z_iter s h')

theorem Z_mono {H a M M' : Nat} (h : Z H a M) (hM : M' ≤ M) : Z H a M' :=
  fun t ht => h t (by omega)

/-- Descending from `Z H (n+1) ((n+2)/2)`: every diagonal `2 ≤ i ≤ n + 2` is white at time `H`. -/
theorem Z_bottom {H n : Nat} (hZ : Z H (n + 1) ((n + 2) / 2)) :
    ∀ i, 2 ≤ i → i ≤ n + 2 → R i H = false := by
  intro i hi1 hi2
  rcases Nat.mod_two_eq_zero_or_one (n + 2 - i) with hp | hp
  · have hz : Z H ((i - 1) + 2 * ((n + 2 - i) / 2)) (1 + (n + 2 - i) / 2) := by
      rw [show (i - 1) + 2 * ((n + 2 - i) / 2) = n + 1 by omega]
      exact Z_mono hZ (by omega)
    have := (Z_iter _ hz) 0 (by omega)
    rw [Nat.add_zero, show i - 1 + 1 = i by omega] at this
    exact this.2
  · have hz : Z H (i + 2 * ((n + 1 - i) / 2)) (1 + (n + 1 - i) / 2) := by
      rw [show i + 2 * ((n + 1 - i) / 2) = n + 1 by omega]
      exact Z_mono hZ (by omega)
    have := (Z_iter _ hz) 0 (by omega)
    rw [Nat.add_zero] at this
    exact this.1

/-- From the white strip, every diagonal `i ≤ n + 2` has period `H`. -/
theorem halve_of_Z {H n : Nat} (hZ : Z H (n + 1) ((n + 2) / 2)) :
    ∀ i, i ≤ n + 2 → Per i H := by
  have hb := Z_bottom hZ
  have hH : H % 2 = 0 := by
    have h2 := hb 2 (by omega) (by omega)
    rw [R_two_eq_one, R_one_eq] at h2
    rcases Nat.mod_two_eq_zero_or_one H with h | h
    · exact h
    · rw [h] at h2; exact absurd h2 (by decide)
  have pair : ∀ m, (m ≤ n + 2 → Per m H) ∧ (m + 1 ≤ n + 2 → Per (m + 1) H) := by
    intro m
    induction m with
    | zero =>
      refine ⟨fun _ => per_zero H, fun _ => ?_⟩
      intro t
      show R 1 (t + H) = R 1 t
      rw [R_one_eq, R_one_eq, show (t + H) % 2 = t % 2 by omega]
    | succ m ih =>
      refine ⟨ih.2, fun hm => ?_⟩
      have pa : Per m H := ih.1 (by omega)
      have pb : Per (m + 1) H := ih.2 (by omega)
      have sh := accum_shift (x := R (m + 2)) (g := fun t => R (m + 1) t || R m t) (L := H)
        (fun t => R_step m t)
        (fun t => by
          show (R (m + 1) (t + H) || R m (t + H)) = (R (m + 1) t || R m t)
          rw [pa t, pb t])
      intro t
      show R (m + 2) (t + H) = R (m + 2) t
      rw [sh t, R_lt (show 2 * 0 < m + 2 by omega), hb (m + 2) (by omega) (by omega)]
      cases R (m + 2) t <;> rfl
  exact fun i hi => (pair i).1 hi

/-- A period `H` of diagonal `n + 3` yields the white strip. -/
theorem Z_of_per {H n : Nat} (h : Per (n + 3) H) : Z H (n + 1) ((n + 2) / 2) := by
  intro t ht
  have s : R (n + 3) (H + t + 1) = xor (R (n + 3) (H + t))
      (R (n + 2) (H + t) || R (n + 1) (H + t)) := R_step (n + 1) (H + t)
  have e1 : R (n + 3) (H + t + 1) = false := by
    rw [show H + t + 1 = (t + 1) + H by omega, h]
    exact R_lt (by omega)
  have e2 : R (n + 3) (H + t) = false := by
    rw [show H + t = t + H by omega, h]
    exact R_lt (by omega)
  rw [e1, e2] at s
  show R (n + 1) (H + t) = false ∧ R (n + 2) (H + t) = false
  revert s; cases R (n + 1) (H + t) <;> cases R (n + 2) (H + t) <;> simp

/-- **Halving lemma**: a period `H` of diagonal `n + 3` is a period of every diagonal up to
`n + 2`. -/
theorem halve {H n : Nat} (h : Per (n + 3) H) : ∀ i, i ≤ n + 2 → Per i H :=
  halve_of_Z (Z_of_per h)


/-- **Monotonicity**: if diagonal `j + 1` repeats with period `H`, so do all diagonals up to
`j`. In particular `e_j ≤ e_{j+1}`. -/
theorem per_mono_all {j H : Nat} (h : Per (j + 1) H) : ∀ i, i ≤ j → Per i H := by
  rcases j with _ | _ | n
  · intro i hi
    rw [show i = 0 by omega]; exact per_zero H
  · intro i hi
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · exact per_zero H
    · intro t
      have := h t
      rw [R_two_eq_one, R_two_eq_one] at this
      exact this
  · exact halve h

theorem per_mono {j H : Nat} (h : Per (j + 1) H) : Per j H :=
  per_mono_all h j (Nat.le_refl j)

theorem per_mono_le {i j H : Nat} (hij : i ≤ j) (h : Per j H) : Per i H := by
  rcases Nat.eq_or_lt_of_le hij with rfl | hlt
  · exact h
  · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    exact per_mono_all h i (by omega)

/-! ### The shift formula and the doubling criterion -/

/-- **Shift formula**: if diagonal `j` repeats with period `H`, a shift of `H` adds the
constant `R (j+1) H` to diagonal `j + 1`. -/

theorem shift_formula {j H : Nat} (h : Per j H) :
    ∀ t, R (j + 1) (t + H) = xor (R (j + 1) t) (R (j + 1) H) := by
  rcases j with _ | j
  · intro t
    show R 1 (t + H) = xor (R 1 t) (R 1 H)
    rw [R_one_eq, R_one_eq, R_one_eq, mod2_add]
  · have hj : Per j H := per_mono_all h j (Nat.le_refl j)
    have sh := accum_shift (x := R (j + 2)) (g := fun t => R (j + 1) t || R j t) (L := H)
      (fun t => R_step j t)
      (fun t => by
        show (R (j + 1) (t + H) || R j (t + H)) = (R (j + 1) t || R j t)
        rw [h t, hj t])
    rw [R_lt (show 2 * 0 < j + 2 by omega)] at sh
    intro t
    show R (j + 2) (t + H) = xor (R (j + 2) t) (R (j + 2) H)
    rw [sh t]; cases R (j + 2) H <;> cases R (j + 2) t <;> rfl

/-- **Doubling criterion**: given period `H` on diagonal `j`, diagonal `j + 1` keeps the period
`H` exactly when its cell at time `H` is white. -/
theorem per_succ_iff {j H : Nat} (h : Per j H) :
    Per (j + 1) H ↔ R (j + 1) H = false := by
  constructor
  · intro hp
    have := hp 0
    rwa [Nat.zero_add, R_init (by omega)] at this
  · intro h0 t
    rw [shift_formula h t, h0]; cases R (j + 1) t <;> rfl

/-- When the cell at time `H` is black, a shift by `H` complements diagonal `j + 1`. -/
theorem antiperiod_of_black {j H : Nat} (h : Per j H) (hb : R (j + 1) H = true) :
    ∀ t, R (j + 1) (t + H) = !R (j + 1) t := by
  intro t; rw [shift_formula h t, hb]; cases R (j + 1) t <;> rfl

/-- When the period doubles, the diagonal is complemented by a shift of half its period. -/
theorem antiperiod {j H : Nat} (h : Per j H) (hn : ¬ Per (j + 1) H) :
    ∀ t, R (j + 1) (t + H) = !R (j + 1) t := by
  have h1 : R (j + 1) H = true := by
    cases h' : R (j + 1) H
    · exact absurd ((per_succ_iff h).2 h') hn
    · rfl
  exact antiperiod_of_black h h1

/-- **Step**: the period at most doubles from one diagonal to the next (`e_{j+1} ≤ e_j + 1`). -/
theorem per_step {j k : Nat} (h : Per j (2 ^ k)) : Per (j + 1) (2 ^ (k + 1)) := by
  intro t
  rw [Nat.pow_succ, show 2 ^ k * 2 = 2 ^ k + 2 ^ k by omega, ← Nat.add_assoc,
    shift_formula h, shift_formula h]
  cases R (j + 1) t <;> cases R (j + 1) (2 ^ k) <;> rfl

/-! ### The rows at times `2^k u` -/

/-- **Zero gap.** Let `J` be a diagonal with period `2^k` whose successor does not have it. Then
at every time `2^k u` the diagonals `1, …, J` are white and diagonal `J + 1` is black exactly when
`u` is odd. -/
theorem zero_gap {J k : Nat} (hJ : Per J (2 ^ k)) (hJ1 : ¬ Per (J + 1) (2 ^ k)) (u : Nat) :
    (∀ i, 1 ≤ i → i ≤ J → R i (2 ^ k * u) = false) ∧
      R (J + 1) (2 ^ k * u) = (u % 2 == 1) := by
  refine ⟨fun i hi1 hiJ => ?_, ?_⟩
  · rw [(per_mono_le hiJ hJ).at_mul u, R_init hi1]
  · have anti := antiperiod hJ hJ1
    induction u with
    | zero => rw [Nat.mul_zero, R_init (by omega)]; rfl
    | succ u ih =>
      rw [Nat.mul_succ, anti, ih]
      rcases Nat.mod_two_eq_zero_or_one u with h | h
      · have h' : (u + 1) % 2 = 1 := by omega
        simp [h, h']
      · have h' : (u + 1) % 2 = 0 := by omega
        simp [h, h']

/-- The same in terms of cells: row `N = 2^k u` (`u` odd) reads `1 0^J 1` leftwards from its
right edge. -/
theorem zero_gap_cell {J k : Nat} (hJ : Per J (2 ^ k)) (hJ1 : ¬ Per (J + 1) (2 ^ k)) (u : Nat)
    (hu : u % 2 = 1) :
    (∀ i, 1 ≤ i → i ≤ J → cell (2 ^ k * u) ((2 ^ k * u : Nat) - (i : Int)) = false) ∧
      cell (2 ^ k * u) ((2 ^ k * u : Nat) - ((J + 1 : Nat) : Int)) = true := by
  obtain ⟨h1, h2⟩ := zero_gap hJ hJ1 u
  refine ⟨fun i hi1 hiJ => h1 i hi1 hiJ, ?_⟩
  have := h2
  rw [hu] at this
  exact this

/-- **The last cell of every period is black**: if diagonal `j` has period `2^k`, then
`R j (2^k - 1)` is black. So row `2^k - 1` ends in `J + 1` black cells. -/
theorem last_one : ∀ j k, Per j (2 ^ k) → R j (2 ^ k - 1) = true
  | 0, _, _ => R_zero _
  | 1, k, h => by
    rcases k with _ | k
    · exact absurd h (not_per_one (by omega))
    · rw [R_one_eq]
      have : (2 ^ (k + 1) - 1) % 2 = 1 := by
        have := Nat.two_pow_pos k; rw [Nat.pow_succ]; omega
      rw [this]; rfl
  | j + 2, k, h => by
    have hp := Nat.two_pow_pos k
    have hj1 := last_one (j + 1) k (per_mono h)
    have s := R_step j (2 ^ k - 1)
    rw [show 2 ^ k - 1 + 1 = 0 + 2 ^ k by omega, h 0, R_init (by omega), hj1] at s
    revert s; cases R (j + 2) (2 ^ k - 1) <;> simp

/-! ### Restarts at the right edge -/

/-- **Restart.** If diagonal `j` has period `2^k`, it reads the same at times `2^k u + s` and `s`. -/
theorem restart {j k : Nat} (h : Per j (2 ^ k)) (u s : Nat) : R j (2 ^ k * u + s) = R j s := by
  have := h.mul u s
  rwa [show s + u * 2 ^ k = 2 ^ k * u + s by rw [Nat.mul_comm]; omega] at this

/-- **The center column restarts at the right edge**: if diagonal `s` has period `2^k`, the cell
`s` steps below the right-edge cell `(2^k u, 2^k u)` equals `c(s)`. So column `2^k u` repeats
`c(0), …, c(J)` where `J` is the last diagonal of period `2^k`. -/
theorem center_restart {s k : Nat} (h : Per s (2 ^ k)) (u : Nat) :
    cell (2 ^ k * u + s) ((2 ^ k * u : Nat) : Int) = cell s 0 := by
  have := restart h u s
  unfold R at this
  rw [cell_congr (show ((2 ^ k * u + s : Nat) : Int) - (s : Int) = ((2 ^ k * u : Nat) : Int)
      by omega), cell_congr (show ((s : Nat) : Int) - (s : Int) = 0 by omega)] at this
  exact this

/-- **Columns are 2-adically continuous**: if diagonal `s` has period `2^k`, columns `p` and
`p + 2^k u` agree `s` steps after the right edge reaches them. -/
theorem column_continuity {s k : Nat} (h : Per s (2 ^ k)) (p u : Nat) :
    cell (p + 2 ^ k * u + s) ((p + 2 ^ k * u : Nat) : Int) = cell (p + s) (p : Int) := by
  have := h.mul u (p + s)
  unfold R at this
  rw [show p + s + u * 2 ^ k = p + 2 ^ k * u + s by rw [Nat.mul_comm]; omega,
    cell_congr (show ((p + 2 ^ k * u + s : Nat) : Int) - (s : Int) = ((p + 2 ^ k * u : Nat) : Int)
      by omega), cell_congr (show ((p + s : Nat) : Int) - (s : Int) = (p : Int) by omega)] at this
  exact this

/-- **Rows restart at the right edge**: if diagonal `J` has period `2^k`, the right end of row
`2^k + s` copies row `s`: `cell (2^k + s) (2^k + q) = cell s q` for `s - J ≤ q ≤ s`. When
`2s ≤ J` this covers all of row `s`, preceded by white cells. -/
theorem row_restart {J k : Nat} (hJ : Per J (2 ^ k)) (s : Nat) (q : Int)
    (hq0 : (s : Int) - J ≤ q) (hq1 : q ≤ s) :
    cell (2 ^ k + s) (((2 ^ k : Nat) : Int) + q) = cell s q := by
  obtain ⟨j, hj⟩ : ∃ j : Nat, (j : Int) = (s : Int) - q := ⟨((s : Int) - q).toNat, by omega⟩
  have hper : Per j (2 ^ k) := per_mono_le (by omega) hJ
  have e := hper s
  unfold R at e
  rw [show s + 2 ^ k = 2 ^ k + s by omega] at e
  rw [cell_congr (show ((2 ^ k + s : Nat) : Int) - (j : Int) = ((2 ^ k : Nat) : Int) + q by omega),
    cell_congr (show (s : Int) - (j : Int) = q by omega)] at e
  exact e

/-- **A black center cell lies in the first period of its diagonal**: if `c(t)` is black and
diagonal `t` has period `2^k`, then `t < 2^k`. (If `2^k ≤ t`, then `t mod 2^k < t/2`, so by
periodicity `c(t)` equals a cell outside the light cone.) -/
theorem center_black_lt {t k : Nat} (hc : cell t 0 = true) (h : Per t (2 ^ k)) : t < 2 ^ k := by
  have hp := Nat.two_pow_pos k
  apply Nat.lt_of_not_le
  intro hle
  have e := h.mul (t / 2 ^ k) (t % 2 ^ k)
  rw [show t % 2 ^ k + t / 2 ^ k * 2 ^ k = t by
    have := Nat.div_add_mod t (2 ^ k); rw [Nat.mul_comm] at this; omega] at e
  have hmod : t % 2 ^ k < 2 ^ k := Nat.mod_lt _ hp
  have hmod2 : t % 2 ^ k + 2 ^ k ≤ t := by
    have h1 := Nat.div_add_mod t (2 ^ k)
    have h2 : 1 ≤ t / 2 ^ k := (Nat.le_div_iff_mul_le hp).2 (by omega)
    have h3 : 2 ^ k ≤ 2 ^ k * (t / 2 ^ k) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  rw [R_lt (show 2 * (t % 2 ^ k) < t by omega)] at e
  have : R t t = cell t 0 := by
    unfold R; exact cell_congr (by omega)
  rw [this, hc] at e
  exact absurd e (by decide)

/-! ### No three doublings in a row -/

/-- **No three doublings.** If the period doubles from `j` to `j + 1` and again from `j + 1` to
`j + 2`, it stays from `j + 2` to `j + 3`.

With `H = 2^E`: diagonal `j + 1` is complemented by a shift of `H`, diagonal `j + 2` by a shift of
`2H`. The parity that diagonal `j + 3` accumulates over `4H` steps is the number of white cells of
diagonal `j + 1` in `2H` steps, which is `H`, even. -/
theorem no_three {j E : Nat} (hj : 1 ≤ j) (h0 : Per j (2 ^ E)) (h1 : ¬ Per (j + 1) (2 ^ E))
    (h2 : ¬ Per (j + 2) (2 ^ (E + 1))) : Per (j + 3) (2 ^ (E + 2)) := by
  -- `E ≥ 1`, since diagonal `j ≥ 1` is not constant
  have hE : 1 ≤ E := by
    rcases Nat.eq_zero_or_pos E with rfl | h
    · exact absurd h0 (not_per_one hj)
    · exact h
  obtain ⟨E', rfl⟩ : ∃ E', E = E' + 1 := ⟨E - 1, by omega⟩
  obtain ⟨H, hH⟩ : ∃ H, 2 ^ (E' + 1) = H := ⟨_, rfl⟩
  have hH2 : 2 ^ (E' + 1 + 1) = 2 * H := by rw [Nat.pow_succ, hH]; omega
  have hH4 : 2 ^ (E' + 1 + 2) = 4 * H := by
    rw [show E' + 1 + 2 = (E' + 1) + 1 + 1 by omega, Nat.pow_succ, Nat.pow_succ, hH]; omega
  have hHeven : H % 2 = 0 := by rw [← hH, Nat.pow_succ]; omega
  -- antiperiods
  have a1 : ∀ t, R (j + 1) (t + H) = !R (j + 1) t := by
    have := antiperiod h0 h1; rwa [hH] at this
  have p1 : Per (j + 1) (2 ^ (E' + 1 + 1)) := per_step h0
  have a2 : ∀ t, R (j + 2) (t + 2 * H) = !R (j + 2) t := by
    have := antiperiod p1 h2; rwa [hH2] at this
  have p2 : Per (j + 2) (2 ^ (E' + 1 + 2)) := per_step p1
  -- it suffices that diagonal `j + 3` is white at time `4H`
  have key : R (j + 3) (4 * H) = false := by
    let x := R (j + 3)
    have hx : ∀ t, x (t + 1) = xor (x t) (R (j + 2) t || R (j + 1) t) := fun t => R_step (j + 1) t
    -- `u t = x (t + 2H) xor x t` accumulates `not (R (j+1) t)`
    let u := fun t => xor (x (t + 2 * H)) (x t)
    have hu : ∀ t, u (t + 1) = xor (u t) (!R (j + 1) t) := by
      intro t
      show xor (x (t + 1 + 2 * H)) (x (t + 1)) = xor (xor (x (t + 2 * H)) (x t)) (!R (j + 1) t)
      have p1' : R (j + 1) (t + 2 * H) = R (j + 1) t := by
        rw [show t + 2 * H = (t + H) + H by omega, a1, a1]; cases R (j + 1) t <;> rfl
      rw [show t + 1 + 2 * H = (t + 2 * H) + 1 by omega, hx, hx, a2, p1']
      cases x (t + 2 * H) <;> cases x t <;> cases R (j + 2) t <;> cases R (j + 1) t <;> rfl
    -- `v t = u (t + H) xor u t` flips every step
    let v := fun t => xor (u (t + H)) (u t)
    have hv : ∀ t, v (t + 1) = !v t := by
      intro t
      show xor (u (t + 1 + H)) (u (t + 1)) = !(xor (u (t + H)) (u t))
      rw [show t + 1 + H = (t + H) + 1 by omega, hu, hu, a1]
      cases u (t + H) <;> cases u t <;> cases R (j + 1) t <;> rfl
    have hvH : ∀ n, v (n + 2) = v n := fun n => by rw [hv, hv]; cases v n <;> rfl
    have hvper : ∀ n, v (2 * n) = v 0 := by
      intro n; induction n with
      | zero => rfl
      | succ n ih => rw [show 2 * (n + 1) = 2 * n + 2 by omega, hvH, ih]
    have hvH' : v H = v 0 := by
      obtain ⟨m, hm⟩ : ∃ m, H = 2 * m := ⟨H / 2, by omega⟩
      rw [hm]; exact hvper m
    -- assemble
    have ex0 : x 0 = false := R_init (by omega)
    have e1 : x (4 * H) = xor (x (2 * H)) (u (2 * H)) := by
      show x (4 * H) = xor (x (2 * H)) (xor (x (2 * H + 2 * H)) (x (2 * H)))
      rw [show 2 * H + 2 * H = 4 * H by omega]; cases x (4 * H) <;> cases x (2 * H) <;> rfl
    have e2 : x (2 * H) = u 0 := by
      show x (2 * H) = xor (x (0 + 2 * H)) (x 0)
      rw [Nat.zero_add, ex0]; cases x (2 * H) <;> rfl
    have e3 : u (2 * H) = xor (u H) (v H) := by
      show u (2 * H) = xor (u H) (xor (u (H + H)) (u H))
      rw [show H + H = 2 * H by omega]; cases u (2 * H) <;> cases u H <;> rfl
    have e4 : u H = xor (u 0) (v 0) := by
      show u H = xor (u 0) (xor (u (0 + H)) (u 0))
      rw [Nat.zero_add]; cases u H <;> cases u 0 <;> rfl
    show x (4 * H) = false
    rw [e1, e2, e3, e4, hvH']
    cases u 0 <;> cases v 0 <;> rfl
  have p3 := per_succ_iff p2
  rw [hH4] at p3 ⊢
  exact p3.2 key

/-! ### Bounds -/

/-- **Lower bound**: diagonal `j ≥ 1` does not repeat with period `2^k` when `2^(k+1) ≤ j`. So
`j < 2^(e_j + 1)`, and the periods are unbounded. -/
theorem not_per_small {j k : Nat} (hj : 1 ≤ j) (hk : 2 ^ (k + 1) ≤ j) : ¬ Per j (2 ^ k) := by
  intro h
  have hp := Nat.two_pow_pos k
  have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
  have := h ((j + 1) / 2 - 2 ^ k)
  rw [show (j + 1) / 2 - 2 ^ k + 2 ^ k = (j + 1) / 2 by omega, R_half hj,
    R_lt (show 2 * ((j + 1) / 2 - 2 ^ k) < j by omega)] at this
  exact absurd this (by decide)

/-- Three diagonals on, the period grows by a factor at most `4`. -/
theorem per_three {j k : Nat} (hj : 1 ≤ j) (h : Per j (2 ^ k)) : Per (j + 3) (2 ^ (k + 2)) := by
  by_cases h1 : Per (j + 1) (2 ^ k)
  · exact per_step (per_step h1)
  · by_cases h2 : Per (j + 2) (2 ^ (k + 1))
    · exact per_step h2
    · exact no_three hj h h1 h2

/-- **Upper bound**: `e_j ≤ (2j + 1)/3` for `j ≥ 2`. -/
theorem per_upper : ∀ j, 2 ≤ j → Per j (2 ^ ((2 * j + 1) / 3))
  | 0, h => absurd h (by omega)
  | 1, h => absurd h (by omega)
  | 2, _ => by
    show Per 2 (2 ^ 1)
    intro t; rw [R_two_eq_one, R_two_eq_one]; exact per_one 0 t
  | 3, _ => by
    show Per (2 + 1) (2 ^ (1 + 1))
    apply per_step; intro t; rw [R_two_eq_one, R_two_eq_one]; exact per_one 0 t
  | 4, _ => by
    show Per (2 + 1 + 1) (2 ^ (1 + 1 + 1))
    apply per_step; apply per_step; intro t; rw [R_two_eq_one, R_two_eq_one]; exact per_one 0 t
  | j + 5, _ => by
    have ih := per_upper (j + 2) (by omega)
    have := per_three (show 1 ≤ j + 2 by omega) ih
    rw [show j + 2 + 3 = j + 5 by omega,
      show (2 * (j + 2) + 1) / 3 + 2 = (2 * (j + 5) + 1) / 3 by omega] at this
    exact this

/-! ### Periods read off the rows at powers of two -/

/-- **Gap characterization**: diagonal `n` repeats with period `2^k` exactly when row `2^k` has
`n` white cells immediately left of its right edge. So `e_n` is the least `k` such that row `2^k`
ends in `1` preceded by at least `n` white cells. -/
theorem per_iff_gap (k n : Nat) :
    Per n (2 ^ k) ↔ ∀ i, 1 ≤ i → i ≤ n → R i (2 ^ k) = false := by
  constructor
  · intro h i hi1 hin
    have := (per_mono_le hin h).at_mul 1
    rwa [Nat.mul_one, R_init hi1] at this
  · induction n with
    | zero => intro _; exact per_zero _
    | succ n ih =>
      intro h
      have hn := ih (fun i h1 h2 => h i h1 (by omega))
      exact (per_succ_iff hn).2 (h (n + 1) (by omega) (Nat.le_refl _))

/-- Cells of the packed simulation `Rule30Window.row`. -/
theorem R_eq_row (j t K : Nat) (ht : t ≤ K) (hj : j ≤ t + K) :
    R j t = (Rule30Window.row K t).testBit (t + K - j) := by
  rw [Rule30Window.row_testBit K t ht]
  show cell t ((t : Int) - j) = cell t (((t + K - j : Nat) : Int) - K)
  exact cell_congr (by omega)

/-- Row `64` ends in `1` preceded by `14` white cells, so diagonal `14` has period `2^6 = 64`.
In particular `e_14 ≤ 6 < 7 = ⌊14/2⌋`: the guess `e_j ≥ ⌊j/2⌋` is false. -/
theorem per_14 : Per 14 (2 ^ 6) := by
  rw [per_iff_gap]
  intro i hi1 hi
  rw [R_eq_row i (2 ^ 6) 64 (by decide) (by omega)]
  have hall : (List.range 14).all (fun i => !(Rule30Window.row 64 64).testBit (128 - (i + 1)))
      = true := by decide +kernel
  rw [List.all_eq_true] at hall
  have := hall (i - 1) (List.mem_range.2 (by omega))
  rw [show 128 - (i - 1 + 1) = 2 ^ 6 + 64 - i by omega] at this
  revert this; cases (Rule30Window.row 64 64).testBit (2 ^ 6 + 64 - i) <;> simp

/-- Row `256` ends in `1` preceded by `23` white cells: `e_23 ≤ 8 < 11 = ⌊23/2⌋`. -/
theorem per_23 : Per 23 (2 ^ 8) := by
  rw [per_iff_gap]
  intro i hi1 hi
  rw [R_eq_row i (2 ^ 8) 256 (by decide) (by omega)]
  have hall : (List.range 23).all (fun i => !(Rule30Window.row 256 256).testBit (512 - (i + 1)))
      = true := by decide +kernel
  rw [List.all_eq_true] at hall
  have := hall (i - 1) (List.mem_range.2 (by omega))
  rw [show 512 - (i - 1 + 1) = 2 ^ 8 + 256 - i by omega] at this
  revert this; cases (Rule30Window.row 256 256).testBit (2 ^ 8 + 256 - i) <;> simp

/-- `e_j ≥ ⌊j/2⌋` fails: diagonal `14` repeats with a period below `2^7`. -/
theorem not_half_lower : ¬ ∀ j k, Per j (2 ^ k) → j / 2 ≤ k := by
  intro h
  have := h 14 6 per_14
  omega

/-- **Every period of diagonal `j ≥ 1` exceeds `⌈j / 2⌉`**: the diagonal is white before time
`⌈j / 2⌉` and black at that time (the left edge). -/
theorem period_gt {j P : Nat} (hj : 1 ≤ j) (hP : 0 < P) (h : Per j P) : (j + 1) / 2 < P := by
  refine Nat.lt_of_not_le fun hle => ?_
  have e := h ((j + 1) / 2 - P)
  rw [show (j + 1) / 2 - P + P = (j + 1) / 2 by omega, R_half hj,
    R_lt (show 2 * ((j + 1) / 2 - P) < j by omega)] at e
  exact absurd e (by decide)

/-! ### The last diagonal of period `2^k` -/

theorem lt_two_pow' : ∀ k : Nat, k < 2 ^ k
  | 0 => by decide
  | k + 1 => by have := lt_two_pow' k; rw [Nat.pow_succ]; omega

theorem last_search {k : Nat} : ∀ d n, Per n (2 ^ k) → ¬ Per (n + d) (2 ^ k) →
    ∃ J, n ≤ J ∧ Per J (2 ^ k) ∧ ¬ Per (J + 1) (2 ^ k)
  | 0, n, h, hn => absurd h (by simpa using hn)
  | d + 1, n, h, hn => by
    by_cases h1 : Per (n + 1) (2 ^ k)
    · obtain ⟨J, hJ, hJ', hJ''⟩ := last_search d (n + 1) h1
        (by rw [show n + 1 + d = n + (d + 1) by omega]; exact hn)
      exact ⟨J, by omega, hJ', hJ''⟩
    · exact ⟨n, Nat.le_refl _, h, h1⟩

/-- The last diagonal `J_k` of period `2^k` exists and satisfies `k ≤ J_k`. -/
theorem exists_last (k : Nat) : ∃ J, Per J (2 ^ k) ∧ ¬ Per (J + 1) (2 ^ k) ∧ k ≤ J := by
  have hk := lt_two_pow' (k + 1)
  have hnot : ¬ Per (k + (2 ^ (k + 1) - k)) (2 ^ k) := by
    rw [show k + (2 ^ (k + 1) - k) = 2 ^ (k + 1) by omega]
    exact not_per_small (by omega) (Nat.le_refl _)
  obtain ⟨J, h1, h2, h3⟩ := last_search (2 ^ (k + 1) - k) k (per_R_periodic k) hnot
  exact ⟨J, h2, h3, h1⟩

/-- Uniqueness: the set of diagonals with period `2^k` is exactly `{0, …, J}`. -/
theorem per_iff_le_last {J k : Nat} (hJ : Per J (2 ^ k)) (hJ1 : ¬ Per (J + 1) (2 ^ k)) (j : Nat) :
    Per j (2 ^ k) ↔ j ≤ J := by
  constructor
  · intro h; apply Nat.le_of_not_lt; intro hlt
    exact hJ1 (per_mono_le (show J + 1 ≤ j by omega) h)
  · intro h; exact per_mono_le h hJ

/-- Row `2^k - 1` has `J + 1` black cells at its right end (`R 0 … R J`),
then a white cell (`R (J+1)`). -/
theorem last_black_run {J k : Nat} (hJ : Per J (2 ^ k)) :
    ∀ i, i ≤ J → R i (2 ^ k - 1) = true :=
  fun i hi => last_one i k (per_mono_le hi hJ)

theorem last_white {J k : Nat} (hJ : Per J (2 ^ k)) (hJ1 : ¬ Per (J + 1) (2 ^ k)) :
    R (J + 1) (2 ^ k - 1) = false := by
  have h2 := last_one (J + 1) (k + 1) (per_step hJ)
  have a := antiperiod hJ hJ1 (2 ^ k - 1)
  have hp := Nat.two_pow_pos k
  rw [show 2 ^ k - 1 + 2 ^ k = 2 ^ (k + 1) - 1 by rw [Nat.pow_succ]; omega, h2] at a
  revert a; cases R (J + 1) (2 ^ k - 1) <;> simp

/-- Any diagonal with period `2^k` has index at most `2^(k+1) - 2`. -/
theorem per_bound {J k : Nat} (hJ : Per J (2 ^ k)) : J ≤ 2 ^ (k + 1) - 2 := by
  apply Nat.le_of_not_lt
  intro hcon
  have hp := Nat.two_pow_pos k
  have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
  have hi : Per (2 ^ (k + 1) - 1) (2 ^ k) := per_mono_le (by omega) hJ
  have e := hi.at_mul 1
  rw [Nat.mul_one, R_init (by omega)] at e
  have hD : R (2 ^ (k + 1) - 1) (2 ^ k) = D 1 (2 ^ k) := by
    unfold R D; exact cell_congr (by omega)
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ k = m + 1 := ⟨2 ^ k - 1, by omega⟩
  rw [hD, hm, D_one] at e
  exact absurd e (by decide)

/-- **Rows at powers of two.** For every `k` there is `J ≥ k` with `J ≤ 2^(k+1) - 2` such that every
row `2^k u` (`u` odd) reads `0^J 1` leftwards from the cell left of its right edge, and row
`2^k - 1` reads `1^(J+1) 0` leftwards from its right edge. -/
theorem rows_at_powers_of_two (k : Nat) : ∃ J, k ≤ J ∧ J ≤ 2 ^ (k + 1) - 2 ∧
    (∀ j, Per j (2 ^ k) ↔ j ≤ J) ∧
    (∀ u, u % 2 = 1 →
      (∀ i, 1 ≤ i → i ≤ J → R i (2 ^ k * u) = false) ∧ R (J + 1) (2 ^ k * u) = true) ∧
    (∀ i, i ≤ J → R i (2 ^ k - 1) = true) ∧ R (J + 1) (2 ^ k - 1) = false := by
  obtain ⟨J, hJ, hJ1, hk⟩ := exists_last k
  refine ⟨J, hk, per_bound hJ, per_iff_le_last hJ hJ1, fun u hu => ?_, last_black_run hJ,
    last_white hJ hJ1⟩
  obtain ⟨h1, h2⟩ := zero_gap hJ hJ1 u
  refine ⟨h1, ?_⟩
  rw [h2, hu]; rfl


/-! ### The least exponent `e_j` -/

/-- `e` is the least exponent with `R j` of period `2^e`. -/
def IsE (j e : Nat) : Prop := Per j (2 ^ e) ∧ ∀ k, k < e → ¬ Per j (2 ^ k)

theorem IsE.le {j e k : Nat} (he : IsE j e) (hk : Per j (2 ^ k)) : e ≤ k :=
  Nat.le_of_not_lt (fun hlt => he.2 k hlt hk)

theorem IsE.unique {j e e' : Nat} (he : IsE j e) (he' : IsE j e') : e = e' :=
  Nat.le_antisymm (he.le he'.1) (he'.le he.1)

theorem exists_IsE (j : Nat) : ∃ e, IsE j e := by
  have key : ∀ n, Per j (2 ^ n) → ∃ e, IsE j e := by
    intro n
    induction n with
    | zero => intro h; exact ⟨0, h, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
    | succ n ih =>
      intro h
      by_cases hn : Per j (2 ^ n)
      · exact ih hn
      · exact ⟨n + 1, h, fun k hk hpk => hn (Per.pow_mono hpk (by omega))⟩
  exact key j (R_periodic j)

/-- Monotonicity `e_j ≤ e_{j+1}`. -/
theorem e_mono {j e e' : Nat} (he : IsE j e) (he' : IsE (j + 1) e') : e ≤ e' :=
  he.le (per_mono_all he'.1 j (Nat.le_refl j))

/-- **Doubling rule**: `e_{j+1} = e_j + [R_{j+1}(2^{e_j})]`. -/
theorem e_step {j e e' : Nat} (he : IsE j e) (he' : IsE (j + 1) e') :
    e' = e + (if R (j + 1) (2 ^ e) then 1 else 0) := by
  have hmono : e ≤ e' := e_mono he he'
  have sf := shift_formula he.1
  cases hb : R (j + 1) (2 ^ e)
  · have hp : Per (j + 1) (2 ^ e) := fun t => by
      rw [sf t, hb]; cases R (j + 1) t <;> rfl
    have := he'.le hp
    simp; omega
  · have hnp : ¬ Per (j + 1) (2 ^ e) := fun hp => by
      have h0 := hp 0
      rw [Nat.zero_add, hb, R_lt (show 2 * 0 < j + 1 by omega)] at h0
      exact absurd h0 (by decide)
    have hp2 : Per (j + 1) (2 ^ (e + 1)) := fun t => by
      rw [Nat.pow_succ, show 2 ^ e * 2 = 2 ^ e + 2 ^ e by omega, ← Nat.add_assoc, sf, sf, hb]
      cases R (j + 1) t <;> rfl
    have h1 := he'.le hp2
    have h2 : e' ≠ e := fun heq => hnp (heq ▸ he'.1)
    simp; omega


/-- Number of `s ∈ [a, a + n)` with `f s`. -/
def cnt (f : Nat → Bool) (a : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => cnt f a n + (if f (a + n) then 1 else 0)

theorem cnt_add (f : Nat → Bool) (a n : Nat) :
    ∀ m, cnt f a (n + m) = cnt f a n + cnt f (a + n) m
  | 0 => rfl
  | m + 1 => by
    show cnt f a (n + m) + (if f (a + (n + m)) then 1 else 0)
      = cnt f a n + (cnt f (a + n) m + (if f (a + n + m) then 1 else 0))
    rw [cnt_add f a n m, show a + (n + m) = a + n + m by omega, Nat.add_assoc]

theorem cnt_compl {f : Nat → Bool} {L : Nat} (h : ∀ s, f (s + L) = !f s) (a : Nat) :
    ∀ n, cnt f (a + L) n + cnt f a n = n
  | 0 => rfl
  | n + 1 => by
    show (cnt f (a + L) n + (if f (a + L + n) then 1 else 0))
      + (cnt f a n + (if f (a + n) then 1 else 0)) = n + 1
    have ih := cnt_compl h a n
    rw [show a + L + n = (a + n) + L by omega, h (a + n)]
    cases f (a + n) <;> simp <;> omega

/-- When the period doubles, every window of one full period is exactly half black. -/
theorem half_black {j e : Nat} (h : Per j (2 ^ e)) (hb : R (j + 1) (2 ^ e) = true) (a : Nat) :
    cnt (R (j + 1)) a (2 ^ (e + 1)) = 2 ^ e := by
  rw [Nat.pow_succ, show 2 ^ e * 2 = 2 ^ e + 2 ^ e by omega, cnt_add]
  have := cnt_compl (antiperiod_of_black h hb) a (2 ^ e)
  omega

/-! ### The input of a diagonal -/

/-- `inp j` is the input of diagonal `j + 2`: `R (j+2) (t+1) = R (j+2) t xor inp j t`.
Write `g_{j+2} = inp j`. -/
def inp (j t : Nat) : Bool := R (j + 1) t || R j t

theorem inp_step (j t : Nat) : R (j + 2) (t + 1) = xor (R (j + 2) t) (inp j t) := R_step j t

/-- The white strip, assuming only that the input `g_{n+3} = inp (n+1)` has period `H`. -/
theorem Z_of_inp_per {H n : Nat} (h : PerF (inp (n + 1)) H) : Z H (n + 1) ((n + 2) / 2) := by
  intro t ht
  have e : (R (n + 2) (H + t) || R (n + 1) (H + t)) = false := by
    show inp (n + 1) (H + t) = false
    rw [show H + t = t + H by omega, h t]
    show (R (n + 2) t || R (n + 1) t) = false
    rw [R_lt (show 2 * t < n + 2 by omega), R_lt (show 2 * t < n + 1 by omega)]
    rfl
  show R (n + 1) (H + t) = false ∧ R (n + 2) (H + t) = false
  revert e; cases R (n + 1) (H + t) <;> cases R (n + 2) (H + t) <;> simp

/-- The halving lemma with the hypothesis on the input only (any `H`). -/
theorem halve_inp {H n : Nat} (h : PerF (inp (n + 1)) H) : ∀ i, i ≤ n + 2 → Per i H :=
  halve_of_Z (Z_of_inp_per h)

theorem odd_dvd_two_pow : ∀ k c, c % 2 = 1 → c ∣ 2 ^ k → c = 1
  | 0, _, _, h => Nat.eq_one_of_dvd_one h
  | k + 1, c, hc, ⟨q, hq⟩ => by
    have hq2 : q % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one q with h | h
      · exact h
      · exfalso
        have h1 : (c * q) % 2 = 1 := by rw [Nat.mul_mod, hc, h]
        have h2 : 2 ^ (k + 1) % 2 = 0 := by rw [Nat.pow_succ, Nat.mul_mod_left]
        rw [hq] at h2; omega
    obtain ⟨q', rfl⟩ : ∃ q', q = 2 * q' := ⟨q / 2, by omega⟩
    apply odd_dvd_two_pow k c hc
    refine ⟨q', ?_⟩
    rw [Nat.pow_succ, Nat.mul_left_comm] at hq
    omega

theorem dvd_two_pow_succ {d k : Nat} (h : d ∣ 2 ^ (k + 1)) : d = 2 ^ (k + 1) ∨ d ∣ 2 ^ k := by
  obtain ⟨c, hc⟩ := h
  rcases Nat.mod_two_eq_zero_or_one c with h0 | h1
  · right
    obtain ⟨c', rfl⟩ : ∃ c', c = 2 * c' := ⟨c / 2, by omega⟩
    refine ⟨c', ?_⟩
    rw [Nat.pow_succ, Nat.mul_left_comm] at hc
    omega
  · left
    have : c = 1 := odd_dvd_two_pow (k + 1) c h1 ⟨d, by rw [hc, Nat.mul_comm]⟩
    rw [hc, this, Nat.mul_one]

/-- The input of diagonal `n + 3` has period `2^{e_{n+2}}`. -/
theorem inp_period {n e : Nat} (he : IsE (n + 2) e) : PerF (inp (n + 1)) (2 ^ e) := by
  have h2 : Per (n + 2) (2 ^ e) := he.1
  have h1 : Per (n + 1) (2 ^ e) := per_mono_all (j := n + 1) h2 (n + 1) (Nat.le_refl _)
  intro t
  show (R (n + 2) (t + 2 ^ e) || R (n + 1) (t + 2 ^ e)) = (R (n + 2) t || R (n + 1) t)
  rw [h2 t, h1 t]

/-- Every period `p > 0` of the input `g_{n+3}` is a multiple of `2^{e_{n+2}}`; with
`inp_period`, the least period of `g_j` is exactly `2^{e_{j-1}}` for `j = n + 3 ≥ 3`. -/
theorem inp_least_period {n e : Nat} (he : IsE (n + 2) e) {p : Nat}
    (hp : PerF (inp (n + 1)) p) : 2 ^ e ∣ p := by
  have hd := PerF.gcd p (2 ^ e) hp (inp_period he)
  have hdvd : Nat.gcd p (2 ^ e) ∣ 2 ^ e := Nat.gcd_dvd_right p (2 ^ e)
  rcases e with _ | e
  · exact Nat.one_dvd p
  · rcases dvd_two_pow_succ hdvd with heq | hdv
    · rw [← heq]; exact Nat.gcd_dvd_left p (2 ^ (e + 1))
    · exfalso
      obtain ⟨c, hc⟩ := hdv
      have hpe : PerF (inp (n + 1)) (2 ^ e) := by
        rw [hc, Nat.mul_comm]; exact hd.mul c
      have := halve_inp (n := n) hpe (n + 2) (Nat.le_refl _)
      exact he.2 e (Nat.lt_succ_self e) this

/-- The least period, as an inequality: no smaller positive period. -/
theorem inp_no_smaller_period {n e : Nat} (he : IsE (n + 2) e) {p : Nat} (hp0 : 0 < p)
    (hp : PerF (inp (n + 1)) p) : 2 ^ e ≤ p :=
  Nat.le_of_dvd hp0 (inp_least_period he hp)

/-- **Parity rule**: for `j = n + 3`, `e_j = e_{j-1} + parity(g_j on [0, 2^{e_{j-1}}))`, where
`2^{e_{j-1}}` is the least period of `g_j` (`inp_period`, `inp_least_period`). -/
theorem S_rule {n e e' : Nat} (he : IsE (n + 2) e) (he' : IsE (n + 3) e') :
    e' = e + (if (((List.range (2 ^ e)).filter (inp (n + 1))).length % 2 == 1) then 1 else 0) := by
  have h := e_step he he'
  have hp : R (n + 3) (2 ^ e)
      = (((List.range (2 ^ e)).filter (inp (n + 1))).length % 2 == 1) := R_eq_parity (n + 1) (2 ^ e)
  have h' : e' = e + (if R (n + 3) (2 ^ e) then 1 else 0) := h
  rw [hp] at h'
  exact h'

/-! ### The half-rate bound

Pair the diagonals: at pair `i` the source is `s = R (2 i)`, of period `M = 2 ^ e_{2i}`, and
`R (2 i + 2)` integrates `R (2 i + 1) || R (2 i)` (`R_step`). The pair weight is
`e_{2i+2} - e_{2i} ∈ {0, 1, 2}`; by the doubling rule each unit of weight is a complementing shift
(`leastExp_antiperiod`). The resource at pair `i` is the difference order of `s` over one period
(`pairResource`, `Rule30DifferenceOrder.order`). The three laws of `Rule30DifferenceOrder` give the
reset and countdown laws of a record-charge path (`pairPath`), and `Rule30RecordCharge` turns
them into `e_{2d} ≤ d + Q 0 d`. -/

section HalfRate

open Rule30RecordCharge Rule30DifferenceOrder

/-- The least exponent `e_j` as a function: `IsE j (leastExp j)`. -/
noncomputable def leastExp (j : Nat) : Nat := Classical.choose (exists_IsE j)

theorem leastExp_spec (j : Nat) : IsE j (leastExp j) := Classical.choose_spec (exists_IsE j)

theorem leastExp_zero : leastExp 0 = 0 :=
  (leastExp_spec 0).unique ⟨per_zero 1, fun k hk => absurd hk (Nat.not_lt_zero k)⟩

theorem leastExp_succ_cases (j : Nat) :
    leastExp (j + 1) = leastExp j ∨ leastExp (j + 1) = leastExp j + 1 := by
  have h := e_step (leastExp_spec j) (leastExp_spec (j + 1))
  split at h <;> omega

/-- When the exponent grows, a shift by the old period complements the next diagonal. -/
theorem leastExp_antiperiod {j : Nat} (h : leastExp (j + 1) = leastExp j + 1) (t : Nat) :
    R (j + 1) (t + 2 ^ leastExp j) = !R (j + 1) t :=
  antiperiod (leastExp_spec j).1 ((leastExp_spec (j + 1)).2 (leastExp j) (by omega)) t

/-- The resource at pair `i`: the difference order of `R (2 i)` over one period. -/
noncomputable def pairResource (i : Nat) : Nat := order (R (2 * i)) (2 ^ leastExp (2 * i))

theorem pair_step (i t : Nat) :
    R (2 * i + 1 + 1) (t + 1) = xor (R (2 * i + 1 + 1) t) (R (2 * i + 1) t || R (2 * i) t) :=
  R_step (2 * i) t

/-- The pairs of diagonals form a record-charge path with `nu = 0`. -/
noncomputable def pairPath : Path 0 where
  weight i := leastExp (2 * i + 1 + 1) - leastExp (2 * i)
  exponent i := leastExp (2 * i)
  resource := pairResource
  exponent_zero := leastExp_zero
  exponent_step i := by
    have h0 := leastExp_succ_cases (2 * i)
    have h1 := leastExp_succ_cases (2 * i + 1)
    show leastExp (2 * (i + 1)) = _
    rw [show 2 * (i + 1) = 2 * i + 1 + 1 by omega]
    omega
  weight_le_two i := by
    have h0 := leastExp_succ_cases (2 * i)
    have h1 := leastExp_succ_cases (2 * i + 1)
    show leastExp (2 * i + 1 + 1) - leastExp (2 * i) ≤ 2
    omega
  reset_before i hw := by
    have h0 := leastExp_succ_cases (2 * i)
    have h1 := leastExp_succ_cases (2 * i + 1)
    change leastExp (2 * i + 1 + 1) - leastExp (2 * i) = 2 at hw
    have e0 : leastExp (2 * i + 1) = leastExp (2 * i) + 1 := by omega
    have e1 : leastExp (2 * i + 1 + 1) = leastExp (2 * i + 1) + 1 := by omega
    have hanti : ∀ t, R (2 * i + 1 + 1) (t + 2 * 2 ^ leastExp (2 * i)) = !R (2 * i + 1 + 1) t := by
      intro t
      have := leastExp_antiperiod e1 t
      rwa [e0, two_pow_succ'] at this
    exact order_reset_before (leastExp_spec (2 * i)).1 (leastExp_antiperiod e0) (pair_step i) hanti
  reset_after i hw := by
    have h0 := leastExp_succ_cases (2 * i)
    have h1 := leastExp_succ_cases (2 * i + 1)
    change leastExp (2 * i + 1 + 1) - leastExp (2 * i) = 2 at hw
    have e0 : leastExp (2 * i + 1) = leastExp (2 * i) + 1 := by omega
    have e1 : leastExp (2 * i + 1 + 1) = leastExp (2 * i + 1) + 1 := by omega
    have hanti : ∀ t, R (2 * i + 1 + 1) (t + 2 ^ (leastExp (2 * i) + 1)) =
        !R (2 * i + 1 + 1) t := by
      intro t
      have := leastExp_antiperiod e1 t
      rwa [e0] at this
    have hord := order_of_antiperiod hanti
    show order (R (2 * (i + 1))) (2 ^ leastExp (2 * (i + 1))) + 1 =
      2 ^ (0 + leastExp (2 * (i + 1)) - 1)
    rw [show 2 * (i + 1) = 2 * i + 1 + 1 by omega, e1, e0, two_pow_succ' (leastExp (2 * i) + 1),
      hord, show 0 + (leastExp (2 * i) + 1 + 1) - 1 = leastExp (2 * i) + 1 by omega]
    have := Nat.one_le_two_pow (n := leastExp (2 * i) + 1)
    omega
  countdown i hw := by
    have h0 := leastExp_succ_cases (2 * i)
    have h1 := leastExp_succ_cases (2 * i + 1)
    change leastExp (2 * i + 1 + 1) - leastExp (2 * i) = 1 at hw
    show pairResource i ≤ order (R (2 * (i + 1))) (2 ^ leastExp (2 * (i + 1))) + 1
    rw [show 2 * (i + 1) = 2 * i + 1 + 1 by omega]
    unfold pairResource
    rcases h0 with e0 | e0
    · -- the low diagonal keeps its period: the high diagonal is complemented by `M`
      have e1 : leastExp (2 * i + 1 + 1) = leastExp (2 * i) + 1 := by omega
      have hanti : ∀ t, R (2 * i + 1 + 1) (t + 2 ^ leastExp (2 * i)) = !R (2 * i + 1 + 1) t := by
        intro t
        have := leastExp_antiperiod (j := 2 * i + 1) (by omega) t
        rwa [e0] at this
      rw [e1, two_pow_succ', order_of_antiperiod hanti]
      have := order_le (R (2 * i)) (2 ^ leastExp (2 * i))
      omega
    · -- the low diagonal is complemented by `M`: countdown
      have e1 : leastExp (2 * i + 1 + 1) = leastExp (2 * i) + 1 := by omega
      rw [e1, two_pow_succ']
      exact order_countdown (leastExp_spec (2 * i)).1 (leastExp_antiperiod e0) (pair_step i)

/-- `e_{2d} ≤ d + Q 0 d`. -/
theorem leastExp_two_mul_le (d : Nat) : leastExp (2 * d) ≤ d + Q 0 d :=
  exponent_le_Q pairPath d

theorem leastExp_le_B (j : Nat) : leastExp j ≤ B j := by
  unfold B
  obtain ⟨d, rfl | rfl⟩ : ∃ d, j = 2 * d ∨ j = 2 * d + 1 := ⟨j / 2, by omega⟩
  · rw [show (2 * d + 1) / 2 = d by omega, show 2 * d / 2 = d by omega]
    exact leastExp_two_mul_le d
  · rw [show (2 * d + 1 + 1) / 2 = d + 1 by omega, show (2 * d + 1) / 2 = d by omega]
    have := leastExp_two_mul_le d
    rcases leastExp_succ_cases (2 * d) with h | h <;> omega

/-- **Half-rate bound**: `R j` has period `2 ^ B j`, with `B j = ⌈j / 2⌉ + Q 0 ⌊j / 2⌋`, so
`e_j ≤ j / 2 + O(log* j)`. Since `B j < (2 j + 1) / 3` for `j ≥ 18` (`B_lt_two_thirds`), this
sharpens `per_upper` from `j = 18` on. -/
theorem per_upper_half (j : Nat) : Per j (2 ^ B j) :=
  Per.pow_mono (leastExp_spec j).1 (leastExp_le_B j)

/-- Explicitly: `e_j ≤ ⌈j / 2⌉ + 3` for every `j < 2^22 + 38`. -/
theorem per_upper_half_explicit {j : Nat} (hj : j < 2 ^ 22 + 38) : Per j (2 ^ ((j + 1) / 2 + 3)) :=
  Per.pow_mono (per_upper_half j) (B_le_add_three (by omega))

/-- The least exponent form: `e_j ≤ B j`. -/
theorem e_le_B {j e : Nat} (he : IsE j e) : e ≤ B j :=
  he.le (per_upper_half j)

/-- **Return of the wall**: at time `2 ^ B n` the diagonals `R 1, …, R n` are all white again,
as at time `0`. Reading the right edge as the half-line automaton `x ↦ x ⊕ (2x ∨ 4x ∨ 3)`
started from `0` (bit `k` of its state at time `t` is `R (k + 1) t`), this says that after
`2 ^ B n` steps the state is `0` modulo `2 ^ n`. -/
theorem wall_return (n k : Nat) (hk : k < n) : R (k + 1) (2 ^ B n) = false := by
  have h := per_mono_le (show k + 1 ≤ n by omega) (per_upper_half n) 0
  rw [Nat.zero_add] at h
  rw [h]
  exact R_init (Nat.le_add_left 1 k)

/-! ### Stroboscopic alternation, multi-period half-black balance, and periodic wall return -/

/-- **Monotonicity of `leastExp` (`leastExp_mono`):** for `i ≤ j`, `leastExp i ≤ leastExp j`. -/
theorem leastExp_mono {i j : Nat} (hij : i ≤ j) : leastExp i ≤ leastExp j :=
  (leastExp_spec i).le (per_mono_le hij (leastExp_spec j).1)

/-- **Step Formula for `leastExp` (`leastExp_succ_eq`):** for every `j : Nat`,
`leastExp (j + 1) = leastExp j + (if R (j + 1) (2 ^ leastExp j) then 1 else 0)`. -/
theorem leastExp_succ_eq (j : Nat) :
    leastExp (j + 1) = leastExp j + (if R (j + 1) (2 ^ leastExp j) then 1 else 0) :=
  e_step (leastExp_spec j) (leastExp_spec (j + 1))

/-- **Exact Period-Doubling Criterion for `leastExp` (`leastExp_succ_eq_succ_iff`):**
`leastExp (j + 1) = leastExp j + 1` if and only if `R (j + 1) (2 ^ leastExp j) = true`. -/
theorem leastExp_succ_eq_succ_iff (j : Nat) :
    leastExp (j + 1) = leastExp j + 1 ↔ R (j + 1) (2 ^ leastExp j) = true := by
  have h := leastExp_succ_eq j
  cases hb : R (j + 1) (2 ^ leastExp j) <;> simp [hb] at h ⊢ <;> omega

/-- **Exact Period-Preservation Criterion for `leastExp` (`leastExp_succ_eq_self_iff`):**
`leastExp (j + 1) = leastExp j` if and only if `R (j + 1) (2 ^ leastExp j) = false`. -/
theorem leastExp_succ_eq_self_iff (j : Nat) :
    leastExp (j + 1) = leastExp j ↔ R (j + 1) (2 ^ leastExp j) = false := by
  have h := leastExp_succ_eq j
  cases hb : R (j + 1) (2 ^ leastExp j) <;> simp [hb] at h ⊢ <;> omega

/-- **Shifted Stroboscopic Alternation at Period-Doubling Diagonals (`R_add_mul_pow_leastExp_of_succ`):**
whenever `leastExp (j + 1) = leastExp j + 1`, for every `t, m : Nat`,
`R (j + 1) (t + m * 2 ^ leastExp j) = xor (R (j + 1) t) (m % 2 == 1)`. -/
theorem R_add_mul_pow_leastExp_of_succ {j : Nat} (h : leastExp (j + 1) = leastExp j + 1)
    (t : Nat) : ∀ m : Nat,
    R (j + 1) (t + m * 2 ^ leastExp j) = xor (R (j + 1) t) (m % 2 == 1)
  | 0 => by simp
  | m + 1 => by
    rw [Nat.succ_mul, ← Nat.add_assoc, leastExp_antiperiod h,
      R_add_mul_pow_leastExp_of_succ h t m, mod2_add m 1]
    cases R (j + 1) t <;> cases (m % 2 == 1) <;> rfl

/-- **Exact Stroboscopic Alternation from `t = 0` (`R_mul_pow_leastExp_of_succ`):** whenever
`leastExp (j + 1) = leastExp j + 1`, sampling `R (j + 1)` at multiples `m * 2 ^ leastExp j` yields
the alternating sequence `m % 2 == 1`. -/
theorem R_mul_pow_leastExp_of_succ {j : Nat} (h : leastExp (j + 1) = leastExp j + 1)
    (m : Nat) :
    R (j + 1) (m * 2 ^ leastExp j) = (m % 2 == 1) := by
  have h0 := R_add_mul_pow_leastExp_of_succ h 0 m
  rw [Nat.zero_add, R_init (Nat.le_add_left 1 j)] at h0
  simpa using h0

/-- **Single-Period Half-Black Balance for `leastExp` (`cnt_leastExp_period_of_succ`):** whenever
`leastExp (j + 1) = leastExp j + 1`, every window of length `2 ^ leastExp (j + 1)` on `R (j + 1)`
contains exactly `2 ^ leastExp j` black cells. -/
theorem cnt_leastExp_period_of_succ {j : Nat} (h : leastExp (j + 1) = leastExp j + 1)
    (a : Nat) :
    cnt (R (j + 1)) a (2 ^ leastExp (j + 1)) = 2 ^ leastExp j := by
  rw [h]
  exact half_black (leastExp_spec j).1 ((leastExp_succ_eq_succ_iff j).mp h) a

/-- **Multi-Period Phase-Invariant Half-Black Balance (`cnt_leastExp_mul_period_of_succ`):**
whenever `leastExp (j + 1) = leastExp j + 1`, for every start time `a : Nat` and multiple `m : Nat`,
`cnt (R (j + 1)) a (m * 2 ^ leastExp (j + 1)) = m * 2 ^ leastExp j`. -/
theorem cnt_leastExp_mul_period_of_succ {j : Nat} (h : leastExp (j + 1) = leastExp j + 1)
    (a : Nat) : ∀ m : Nat,
    cnt (R (j + 1)) a (m * 2 ^ leastExp (j + 1)) = m * 2 ^ leastExp j
  | 0 => by simp [cnt]
  | m + 1 => by
    rw [Nat.succ_mul, cnt_add, cnt_leastExp_mul_period_of_succ h a m,
      cnt_leastExp_period_of_succ h (a + m * 2 ^ leastExp (j + 1)), Nat.succ_mul]

/-- **Common Half-Rate Period Across All Diagonals `k ≤ n` (`per_prefix_B`):** for every `k ≤ n`,
diagonal `R k` has period `2 ^ B n`. -/
theorem per_prefix_B (n k : Nat) (hk : k ≤ n) : Per k (2 ^ B n) :=
  per_mono_le hk (per_upper_half n)

/-- **Synchronized Multi-Period Shift Invariance of the Right Wall (`wall_shift_mul`):** for every
`k ≤ n` and all `m, t : Nat`, `R k (t + m * 2 ^ B n) = R k t`. -/
theorem wall_shift_mul (n k m t : Nat) (hk : k ≤ n) :
    R k (t + m * 2 ^ B n) = R k t :=
  (per_prefix_B n k hk).mul m t

/-- **Multi-Period Return of the Right Wall (`wall_return_mul`):** at every multiple `2 ^ B n * m`
(`m : Nat`), the diagonals `R 1, …, R n` are simultaneously white (`false`). -/
theorem wall_return_mul (n k m : Nat) (hk : k < n) :
    R (k + 1) (2 ^ B n * m) = false := by
  rw [(per_prefix_B n (k + 1) (by omega)).at_mul m]
  exact R_init (Nat.le_add_left 1 k)

/-- **Explicit Multi-Period Wall Return Below `2 ^ 22 + 38` (`wall_return_explicit_mul`):** for
`n < 2 ^ 22 + 38`, `k < n`, and every multiple `m : Nat`,
`R (k + 1) (2 ^ ((n + 1) / 2 + 3) * m) = false`. -/
theorem wall_return_explicit_mul {n : Nat} (hn : n < 2 ^ 22 + 38) (k m : Nat) (hk : k < n) :
    R (k + 1) (2 ^ ((n + 1) / 2 + 3) * m) = false := by
  have hp : Per (k + 1) (2 ^ ((n + 1) / 2 + 3)) :=
    per_mono_le (show k + 1 ≤ n by omega) (per_upper_half_explicit hn)
  rw [hp.at_mul m]
  exact R_init (Nat.le_add_left 1 k)

end HalfRate

end Rule30RightPeriods
end Ruliology.CellularAutomata
