module

public import Ruliology.CellularAutomata.Rule30Realization
public import Ruliology.CellularAutomata.Rule30ZeroWallDiagonals

/-!
# Near-squares beside a period-2 center column, and the characteristic Sturmian words

Suppose column `0` of a configuration `x0 : Int → Bool` reads the clock `0101…` from some time `T0` on
(`evol x0 t 0 = decide (t % 2 = 1)`, with `Rule30Realization.evol`), and the configuration has a leftmost black
cell, `L ≥ 1` cells left of column `0`. Rule 30 is left-permutive, so the clock determines column `-1` from column
`1`: black at odd times and the complement of column `1` at even times (`col_m1`). Call column `1` at even times the
*visible bits*, `evol x0 (2 * i) 1`.

* `corollary_F`: the visible bits have no near-squares at unbounded scales. There is no `K` with pairs `i < i'`,
  `i' - i` unbounded and `T0 ≤ 2 * i`, such that `evol x0 (2 * (i + s)) 1 = evol x0 (2 * (i' + s)) 1` for every
  `s + K < i'`.
* `characteristic_excluded`, `characteristic_excluded_compl`, `fibonacci_excluded`: for every directive sequence
  `d` with every `d n ≥ 1`, neither the characteristic Sturmian word `cw d` of slope `[0; d 0 + 1, d 1, d 2, …]` nor
  its letter exchange is the sequence of visible bits of a configuration with a leftmost black cell whose center
  reads the clock from time `0`. The Fibonacci word is the case `d n = 1`.
* `characteristic_block_excluded`: the same for every sliding block code of `cw d`.

Supporting statements, each for every configuration with a leftmost black cell:
* `theorem_A3`: Jen's clocked bound, sharpened by a black diagonal. If columns `i` and `i + 1` carry a common block
  of length `n` from the times `a` and `a'`, the leftmost black cell is `L` cells left of column `i`, and the left
  diagonal `b` (the cell `b` right of the moving left edge) is black at time `a'` with `b + a < a'`, then
  `n ≤ L + a' - b`. Without the diagonal this is the window form of Jen's theorem, `n ≤ L + a'` (`theorem_A'`;
  compare `Rule30FiniteMaskedJen.window_jen_col`).
* `blocks_of_visible`: visible bits that agree for `l` steps give columns `-1` and `0` a common block of length
  `2 * l`.
* `infinitely_many_black`, `lemma_B2`: infinitely many left diagonals, measured from the moving edge, are eventually
  black, and no `P ≥ 1` is an eventual period of all of them. These diagonals obey the left-diagonal recurrence from
  time `0` (`tailLeft_D`), so both are instances of the kit's tail-left package
  (`Rule30ZeroWallDiagonals.tail_black_unbounded`, `Rule30ZeroWallDiagonals.tail_profile_bound`).

**Method.** Take an eventually black diagonal `b ≥ L + 2 * K` (`infinitely_many_black`) and a pair `i < i'` with
`i' - i` beyond `b` and its onset. The visible agreement gives columns `-1` and `0` a common block of length
`2 * (i' - K)` from the times `2 * i` and `2 * i'` (`blocks_of_visible`), and `theorem_A3` bounds it by
`(L - 1) + 2 * i' - b ≤ 2 * i' - 2 * K - 1`, strictly below its length. The auxiliary word is `std d 0 = [1]`. Starting with `std d 1 = [0]`,
the words `std d (n + 1)` are prefixes of `cw d`. The two words
`std d (n + 1) ++ std d n` and `std d n ++ std d (n + 1)` agree except in their last two letters (`std_near_comm`).
So `cw d` repeats its prefix of length `|std d (n + 1)|` with slack `2` at every `n` (`cw_near_square`), which are
the near-squares that `corollary_F` forbids. A block code of window `r` keeps them, with slack `2 + r`
(`image_near_square`).

Beside the kit: `Rule30DrivenLeftWindows` bounds a periodic agreement window of column `-1` by its start, and
`Rule30GapRepetitions.psi_not_finite_of_sample_repeats` excludes a finite left row when repeats of the white-tick
readings outlast their second start by unbounded amounts. Here repeats at unbounded lags that fall short of their
second start by a fixed amount already suffice, through the black diagonal.

**Credit.** The clocked bound is Jen's (E. Jen, J. Stat. Phys. 43, 1986). The near-commutation of standard words is
classical (M. Lothaire, *Algebraic Combinatorics on Words*, Chapter 2). The near-square exclusion and the
characteristic words are from the Lean-verified submissions `R30-20261022-91b0b0` and `R30-20261023-0c4a33`.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30ClockNearSquares

open Rule30Realization (evol)

theorem evol_succ (x0 : Int → Bool) (t : Nat) (i : Int) :
    evol x0 (t + 1) i = xor (evol x0 t (i - 1)) (evol x0 t i || evol x0 t (i + 1)) := rfl

theorem edge (x0 : Int → Bool) (e : Int) (he : x0 e = true) (hl : ∀ j < e, x0 j = false) (t : Nat) :
    evol x0 t (e - t) = true ∧ ∀ j < e - t, evol x0 t j = false := by
  induction t with
  | zero => simpa using ⟨he, hl⟩
  | succ t ih =>
    obtain ⟨h1, h2⟩ := ih
    constructor
    · rw [evol_succ]
      have a1 : evol x0 t (e - ↑(t + 1) - 1) = false := h2 _ (by omega)
      have a2 : evol x0 t (e - ↑(t + 1)) = false := h2 _ (by omega)
      have a3 : e - ↑(t + 1) + 1 = e - ↑t := by omega
      rw [a1, a2, a3, h1]; rfl
    · intro j hj
      rw [evol_succ]
      have b1 : evol x0 t (j - 1) = false := h2 _ (by omega)
      have b2 : evol x0 t j = false := h2 _ (by omega)
      have b3 : evol x0 t (j + 1) = false := h2 _ (by omega)
      rw [b1, b2, b3]; rfl

/-- Diagonal k at time t. -/
def D (x0 : Int → Bool) (e : Int) (k : Int) (t : Nat) : Bool := evol x0 t (e - t + k)

theorem D_succ (x0 : Int → Bool) (e j : Int) (t : Nat) :
    D x0 e j (t + 1) = xor (D x0 e (j - 2) t) (D x0 e (j - 1) t || D x0 e j t) := by
  unfold D
  rw [evol_succ]
  rw [show e - ((t + 1 : Nat) : Int) + j - 1 = e - t + (j - 2) by omega,
    show e - ((t + 1 : Nat) : Int) + j = e - t + (j - 1) by omega,
    show e - (t : Int) + (j - 1) + 1 = e - t + j by omega]

/-! ### The diagonals -/

section diagonals
variable (x0 : Int → Bool) (e : Int) (he : x0 e = true) (hl : ∀ j < e, x0 j = false)
include he hl

theorem D0 (t : Nat) : D x0 e 0 t = true := by
  unfold D; simpa using (edge x0 e he hl t).1

theorem Dneg (k : Int) (hk : k < 0) (t : Nat) : D x0 e k t = false := by
  unfold D; exact (edge x0 e he hl t).2 _ (by omega)

theorem D1 (t : Nat) (ht : 1 ≤ t) : D x0 e 1 t = true := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  rw [D_succ, Dneg x0 e he hl _ (by omega), show (1 : Int) - 1 = 0 by omega, D0 x0 e he hl]; rfl

/-- The diagonals from the moving edge obey the left-diagonal recurrence from time `0`: they form a tail-left
array in the sense of `Rule30ZeroWallDiagonals.TailLeft`. -/
theorem tailLeft_D : Rule30ZeroWallDiagonals.TailLeft (fun j t => D x0 e (j : Int) t) where
  zero_black := ⟨0, fun t _ => D0 x0 e he hl t⟩
  one_black := ⟨1, fun t ht => D1 x0 e he hl t ht⟩
  step := fun j => ⟨0, fun t _ => by
    have h := D_succ x0 e ((j + 2 : Nat) : Int) t
    rw [show ((j + 2 : Nat) : Int) - 2 = (j : Int) by omega,
      show ((j + 2 : Nat) : Int) - 1 = ((j + 1 : Nat) : Int) by omega] at h
    exact h⟩

end diagonals

/-! ### Lemma B2: unbounded periods, and infinitely many eventually black diagonals -/

/-- Eventually black. -/
def EvB (x0 : Int → Bool) (e j : Int) : Prop := ∃ T : Nat, ∀ t, T ≤ t → D x0 e j t = true

section band
variable (x0 : Int → Bool) (e : Int) (he : x0 e = true) (hl : ∀ j < e, x0 j = false)
include he hl

/-- Lemma B2: no P ≥ 1 is an eventual period of every diagonal. -/
theorem lemma_B2 (P : Nat) (hP : 1 ≤ P) :
    ¬ ∀ k : Nat, ∃ T : Nat, ∀ t, T ≤ t → D x0 e k (t + P) = D x0 e k t := fun h => by
  have := Rule30ZeroWallDiagonals.tail_profile_bound (tailLeft_D x0 e he hl) (M := 2 ^ (2 * P)) (Q := P)
    (by omega) (fun j _ => h j)
  omega

/-- For every N some diagonal k ≥ N is eventually black. -/
theorem infinitely_many_black (N : Nat) : ∃ k : Nat, N ≤ k ∧ EvB x0 e k := by
  obtain ⟨b, hb, T, hT⟩ := Rule30ZeroWallDiagonals.tail_black_unbounded (tailLeft_D x0 e he hl) N
  exact ⟨b, Nat.le_of_lt hb, T, hT⟩

end band

/-! ### Jen's clocked bound, and its sharpening by a black diagonal -/

/-- Read right to left: x_t(j - 1) from x_(t+1)(j), x_t(j) and x_t(j + 1). -/
theorem step_inv (x0 : Int → Bool) (t : Nat) (j : Int) :
    evol x0 t (j - 1) = xor (evol x0 (t + 1) j) (evol x0 t j || evol x0 t (j + 1)) := by
  rw [evol_succ]
  cases evol x0 t (j - 1) <;> cases (evol x0 t j || evol x0 t (j + 1)) <;> rfl

/-- Equal blocks on columns i and i + 1 at times a .. a + n - 1 and a′ .. a′ + n - 1 make the rows agree: the cell
m to the left of column i agrees at times a + s and a′ + s whenever s + m < n. -/
theorem agree (x0 : Int → Bool) (i : Int) (n a a' : Nat)
    (hblock : ∀ s : Nat, s < n → evol x0 (a + s) i = evol x0 (a' + s) i ∧ evol x0 (a + s) (i + 1) = evol x0 (a' + s) (i + 1)) :
    ∀ m s : Nat, s + m < n → evol x0 (a + s) (i - m) = evol x0 (a' + s) (i - m) := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro s hs
    rcases m with _ | m
    · simpa using (hblock s (by omega)).1
    · -- the cell m + 1 to the left from the cells m and m - 1 to the left (or column i + 1 when m = 0)
      have h1 : evol x0 (a + s + 1) (i - m) = evol x0 (a' + s + 1) (i - m) := by
        have := ih m (by omega) (s + 1) (by omega)
        rwa [show a + (s + 1) = a + s + 1 by omega, show a' + (s + 1) = a' + s + 1 by omega] at this
      have h2 : evol x0 (a + s) (i - m) = evol x0 (a' + s) (i - m) := ih m (by omega) s (by omega)
      have h3 : evol x0 (a + s) (i - m + 1) = evol x0 (a' + s) (i - m + 1) := by
        rcases m with _ | m
        · simpa using (hblock s (by omega)).2
        · have := ih m (by omega) s (by omega)
          rwa [show i - ((m : Nat) : Int) = i - ((m + 1 : Nat) : Int) + 1 by omega] at this
      rw [show i - ((m + 1 : Nat) : Int) = (i - m) - 1 by omega, step_inv x0 (a + s), step_inv x0 (a' + s), h1, h2, h3]

/-- Theorem A′: the window form of Jen's clocked bound. -/
theorem theorem_A' (x0 : Int → Bool) (i : Int) (L : Nat) (hc : x0 (i - L) = true) (hl : ∀ j < i - L, x0 j = false)
    (n a a' : Nat) (haa : a < a')
    (hblock : ∀ s : Nat, s < n → evol x0 (a + s) i = evol x0 (a' + s) i ∧ evol x0 (a + s) (i + 1) = evol x0 (a' + s) (i + 1)) :
    n ≤ L + a' := by
  refine Classical.byContradiction fun h => ?_
  have hag := agree x0 i n a a' hblock (L + a') 0 (by omega)
  simp only [Nat.add_zero] at hag
  have E := edge x0 (i - L) hc hl
  have black : evol x0 a' (i - ((L + a' : Nat) : Int)) = true := by
    have := (E a').1
    rwa [show i - (L : Int) - (a' : Int) = i - ((L + a' : Nat) : Int) by omega] at this
  have white : evol x0 a (i - ((L + a' : Nat) : Int)) = false :=
    (E a).2 _ (by omega)
  rw [white, black] at hag
  exact absurd hag (by decide)

/-- Theorem A‴: row a′ is white at the distances L + a + 1 .. n - 1 left of column i, which are its diagonals
L + a′ - n + 1 .. a′ - a - 1. -/
theorem theorem_A3_white (x0 : Int → Bool) (i : Int) (L : Nat) (hc : x0 (i - L) = true) (hl : ∀ j < i - L, x0 j = false)
    (n a a' : Nat)
    (hblock : ∀ s : Nat, s < n → evol x0 (a + s) i = evol x0 (a' + s) i ∧ evol x0 (a + s) (i + 1) = evol x0 (a' + s) (i + 1)) :
    ∀ δ : Nat, L + a + 1 ≤ δ → δ + 1 ≤ n → evol x0 a' (i - δ) = false := by
  intro δ h1 h2
  have hag := agree x0 i n a a' hblock δ 0 (by omega)
  simp only [Nat.add_zero] at hag
  rw [← hag]
  exact (edge x0 (i - L) hc hl a).2 _ (by omega)

/-- Theorem A‴'s corollary: if diagonal b (the cell b right of the moving left edge) is black at time a′ and
b < a′ - a, then n ≤ L + a′ - b. -/
theorem theorem_A3 (x0 : Int → Bool) (i : Int) (L : Nat) (hc : x0 (i - L) = true) (hl : ∀ j < i - L, x0 j = false)
    (n a a' b : Nat) (hb : b + a < a') (hblack : evol x0 a' (i - L - a' + b) = true)
    (hblock : ∀ s : Nat, s < n → evol x0 (a + s) i = evol x0 (a' + s) i ∧ evol x0 (a + s) (i + 1) = evol x0 (a' + s) (i + 1)) :
    n ≤ L + a' - b := by
  refine Classical.byContradiction fun h => ?_
  have hw := theorem_A3_white x0 i L hc hl n a a' hblock (L + a' - b) (by omega) (by omega)
  rw [show i - ((L + a' - b : Nat) : Int) = i - L - a' + b by omega] at hw
  rw [hw] at hblack
  exact absurd hblack (by decide)

/-! ## Corollary F: near-squares at the start are fatal -/

/-- Column `-1` under the clock: black at odd times, the complement of column `1` at even times. -/
theorem col_m1 (x0 : Int → Bool) (T0 : Nat) (hclock : ∀ t, T0 ≤ t → evol x0 t 0 = decide (t % 2 = 1)) (t : Nat)
    (ht : T0 ≤ t) :
    (t % 2 = 1 → evol x0 t (-1) = true) ∧ (t % 2 = 0 → evol x0 t (-1) = !(evol x0 t 1)) := by
  have h := evol_succ x0 t 0
  simp only [Int.zero_sub, Int.zero_add] at h
  constructor
  · intro ho
    have hA : evol x0 t 0 = true := by rw [hclock t ht]; simp only [decide_eq_true_eq]; omega
    have hB : evol x0 (t + 1) 0 = false := by rw [hclock (t + 1) (by omega)]; simp only [decide_eq_false_iff_not]; omega
    rw [hA, hB] at h
    revert h; cases evol x0 t (-1) <;> simp
  · intro he
    have hA : evol x0 t 0 = false := by rw [hclock t ht]; simp only [decide_eq_false_iff_not]; omega
    have hB : evol x0 (t + 1) 0 = true := by rw [hclock (t + 1) (by omega)]; simp only [decide_eq_true_eq]; omega
    rw [hA, hB] at h
    revert h; cases evol x0 t (-1) <;> cases evol x0 t 1 <;> simp

/-- Visible bits agreeing for `l` steps make columns `-1` and `0` agree for `2l` steps. -/
theorem blocks_of_visible (x0 : Int → Bool) (T0 : Nat) (hclock : ∀ t, T0 ≤ t → evol x0 t 0 = decide (t % 2 = 1))
    (i i' l : Nat) (hi : T0 ≤ 2 * i) (hii : i ≤ i')
    (hvis : ∀ s, s < l → evol x0 (2 * (i + s)) 1 = evol x0 (2 * (i' + s)) 1) :
    ∀ u : Nat, u < 2 * l → evol x0 (2 * i + u) (-1) = evol x0 (2 * i' + u) (-1) ∧
      evol x0 (2 * i + u) 0 = evol x0 (2 * i' + u) 0 := by
  intro u hu
  have h1 : T0 ≤ 2 * i + u := by omega
  have h2 : T0 ≤ 2 * i' + u := by omega
  constructor
  · rcases Nat.mod_two_eq_zero_or_one u with he | ho
    · obtain ⟨s, rfl⟩ : ∃ s, u = 2 * s := ⟨u / 2, by omega⟩
      have e1 := (col_m1 x0 T0 hclock (2 * i + 2 * s) h1).2 (by omega)
      have e2 := (col_m1 x0 T0 hclock (2 * i' + 2 * s) h2).2 (by omega)
      rw [e1, e2, show 2 * i + 2 * s = 2 * (i + s) by omega, show 2 * i' + 2 * s = 2 * (i' + s) by omega,
        hvis s (by omega)]
    · rw [(col_m1 x0 T0 hclock _ h1).1 (by omega), (col_m1 x0 T0 hclock _ h2).1 (by omega)]
  · rw [hclock _ h1, hclock _ h2, show (2 * i + u) % 2 = (2 * i' + u) % 2 by omega]

/-- **Corollary F.** A configuration with a leftmost black cell `L ≥ 1` cells left of column `0`, whose column `0`
reads the clock `0101…` from time `T0`, has no near-squares at unbounded scales in its visible bits
`evol x0 (2 i) 1`: there are no `K` and pairs `i < i′` with `i′ - i` unbounded, `T0 ≤ 2 i`, and
`evol x0 (2 (i + s)) 1 = evol x0 (2 (i′ + s)) 1` for all `s + K < i′`. -/
theorem corollary_F (x0 : Int → Bool) (L : Nat) (hL : 1 ≤ L) (hc : x0 (-(L : Int)) = true)
    (hl : ∀ j < -(L : Int), x0 j = false)
    (T0 : Nat) (hclock : ∀ t, T0 ≤ t → evol x0 t 0 = decide (t % 2 = 1)) (K : Nat)
    (hpairs : ∀ N : Nat, ∃ i i' : Nat, i < i' ∧ N ≤ i' - i ∧ T0 ≤ 2 * i ∧
      ∀ s, s + K < i' → evol x0 (2 * (i + s)) 1 = evol x0 (2 * (i' + s)) 1) : False := by
  obtain ⟨b, hb, tb, htb⟩ := infinitely_many_black x0 (-(L : Int)) hc hl (L + 2 * K)
  obtain ⟨i, i', hii, hN, hT0, hvis⟩ := hpairs (b + tb + 1)
  have hK : K < i' := by omega
  have hblock := blocks_of_visible x0 T0 hclock i i' (i' - K) hT0 (Nat.le_of_lt hii) (fun s hs => hvis s (by omega))
  have hblack : evol x0 (2 * i') ((-1 : Int) - ((L - 1 : Nat) : Int) - ((2 * i' : Nat) : Int) + ((b : Nat) : Int)) = true := by
    have h := htb (2 * i') (by omega)
    unfold D at h
    have e : (-1 : Int) - ((L - 1 : Nat) : Int) - ((2 * i' : Nat) : Int) + ((b : Nat) : Int) =
        -(L : Int) - ((2 * i' : Nat) : Int) + ((b : Nat) : Int) := by omega
    rw [e]; exact h
  have hA3 := theorem_A3 x0 (-1) (L - 1)
    (by rw [show (-1 : Int) - ((L - 1 : Nat) : Int) = -(L : Int) by omega]; exact hc)
    (fun j hj => hl j (by omega)) (2 * (i' - K)) (2 * i) (2 * i') b (by omega) hblack
    (fun s hs => by simpa using hblock s hs)
  omega

/-! ## Standard words and the characteristic Sturmian words -/

/-- `w` repeated `a` times. -/
def wpow (w : List Bool) : Nat → List Bool
  | 0 => []
  | a + 1 => w ++ wpow w a

theorem wpow_succ (w : List Bool) (a : Nat) : wpow w (a + 1) = w ++ wpow w a := rfl

theorem wpow_length (w : List Bool) : ∀ a, (wpow w a).length = a * w.length
  | 0 => by simp [wpow]
  | a + 1 => by rw [wpow_succ, List.length_append, wpow_length w a, Nat.succ_mul, Nat.add_comm]

theorem wpow_comm (w : List Bool) : ∀ a, w ++ wpow w a = wpow w a ++ w
  | 0 => by simp [wpow]
  | a + 1 => by rw [wpow_succ, List.append_assoc, wpow_comm w a]

/-- The standard words of the directive sequence `d`: `std d 0 = [1]`, `std d 1 = [0]`,
`std d (n + 2) = (std d (n + 1))^(d n) ++ std d n`. With every `d n ≥ 1` these are the standard words of the
characteristic Sturmian word of slope `[0; d 0 + 1, d 1, d 2, …]`; exchanging the letters gives the other slopes. -/
def std (d : Nat → Nat) : Nat → List Bool
  | 0 => [true]
  | 1 => [false]
  | n + 2 => wpow (std d (n + 1)) (d n) ++ std d n

theorem std_succ_succ (d : Nat → Nat) (n : Nat) : std d (n + 2) = wpow (std d (n + 1)) (d n) ++ std d n := rfl

theorem std_length_pos (d : Nat → Nat) : ∀ n, 1 ≤ (std d n).length
  | 0 => by simp [std]
  | 1 => by simp [std]
  | n + 2 => by rw [std_succ_succ, List.length_append]; have := std_length_pos d n; omega

/-- With `d n ≥ 1`, `std d (n + 2)` begins with `std d (n + 1)`. -/
theorem std_prefix (d : Nat → Nat) (hd : ∀ n, 1 ≤ d n) (n : Nat) : std d (n + 1) <+: std d (n + 2) := by
  rw [std_succ_succ]
  obtain ⟨a, ha⟩ : ∃ a, d n = a + 1 := ⟨d n - 1, by have := hd n; omega⟩
  rw [ha, wpow_succ, List.append_assoc]
  exact List.prefix_append _ _

theorem std_prefix_le (d : Nat → Nat) (hd : ∀ n, 1 ≤ d n) (n : Nat) : ∀ m, std d (n + 1) <+: std d (n + 1 + m)
  | 0 => List.prefix_rfl
  | m + 1 => by
    have h := std_prefix d hd (n + m)
    rw [show n + m + 1 = n + 1 + m by omega, show n + m + 2 = n + 1 + (m + 1) by omega] at h
    exact (std_prefix_le d hd n m).trans h

theorem std_length_ge (d : Nat → Nat) (hd : ∀ n, 1 ≤ d n) : ∀ n, n + 1 ≤ (std d (n + 1)).length
  | 0 => by simp [std]
  | n + 1 => by
    have h1 := std_length_ge d hd n
    have h2 := std_length_pos d n
    have h3 : (std d (n + 2)).length = d n * (std d (n + 1)).length + (std d n).length := by
      rw [std_succ_succ, List.length_append, wpow_length]
    have h4 : (std d (n + 1)).length ≤ d n * (std d (n + 1)).length := Nat.le_mul_of_pos_left _ (hd n)
    rw [show n + 1 + 1 = n + 2 by omega, h3]
    omega

/-- The characteristic word: position `i` read in `std d (i + 2)`, which is long enough. -/
def cw (d : Nat → Nat) (i : Nat) : Bool := (std d (i + 2)).getD i false

/-- Reading inside the left part of an append. -/
theorem getD_append {α : Type} (l l' : List α) (d : α) (n : Nat) (h : n < l.length) :
    (l ++ l').getD n d = l.getD n d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

/-- Reading inside the right part of an append. -/
theorem getD_append_right {α : Type} (l l' : List α) (d : α) (n : Nat) (h : l.length ≤ n) :
    (l ++ l').getD n d = l'.getD (n - l.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem getD_of_prefix {u v : List Bool} (h : u <+: v) (i : Nat) (hi : i < u.length) :
    v.getD i false = u.getD i false := by
  obtain ⟨t, rfl⟩ := h
  exact getD_append u t false i hi

/-- The characteristic word agrees with every standard word `std d (n + 1)` on its length. -/
theorem cw_eq (d : Nat → Nat) (hd : ∀ n, 1 ≤ d n) (n i : Nat) (hi : i < (std d (n + 1)).length) :
    cw d i = (std d (n + 1)).getD i false := by
  unfold cw
  rcases (Nat.lt_or_ge (i + 2) (n + 1)).symm with h | h
  · obtain ⟨m, hm⟩ : ∃ m, i + 2 = n + 1 + m := ⟨i + 2 - (n + 1), by omega⟩
    rw [hm]; exact getD_of_prefix (std_prefix_le d hd n m) i hi
  · obtain ⟨m, hm⟩ : ∃ m, n + 1 = i + 2 + m := ⟨n + 1 - (i + 2), by omega⟩
    have hi2 : i < (std d (i + 2)).length := by
      have := std_length_ge d hd (i + 1)
      rw [show i + 1 + 1 = i + 2 by omega] at this
      omega
    rw [hm, getD_of_prefix (std_prefix_le d hd (i + 1) m) i hi2]

/-- Agreement of two words on the first `m` positions. -/
def Agree (u v : List Bool) (m : Nat) : Prop := ∀ i, i < m → u.getD i false = v.getD i false

theorem agree_append_left (p u v : List Bool) (m : Nat) (h : Agree u v m) :
    Agree (p ++ u) (p ++ v) (p.length + m) := by
  intro i hi
  rcases Nat.lt_or_ge i p.length with hp | hp
  · rw [getD_append _ _ _ _ hp, getD_append _ _ _ _ hp]
  · rw [getD_append_right _ _ _ _ hp, getD_append_right _ _ _ _ hp]
    exact h _ (by omega)

theorem agree_symm (u v : List Bool) (m : Nat) (h : Agree u v m) : Agree v u m :=
  fun i hi => (h i hi).symm

/-- **Near-commutation of standard words**: `std (n+1) ++ std n` and `std n ++ std (n+1)` agree except on their
last two letters. -/
theorem std_near_comm (d : Nat → Nat) : ∀ n,
    Agree (std d (n + 1) ++ std d n) (std d n ++ std d (n + 1)) ((std d (n + 1)).length + (std d n).length - 2)
  | 0 => by intro i hi; simp [std] at hi
  | n + 1 => by
    rw [show n + 1 + 1 = n + 2 by omega, std_succ_succ]
    -- (wpow s (d n) ++ std n) ++ s  vs  s ++ (wpow s (d n) ++ std n), where s = std (n+1)
    have e1 : wpow (std d (n + 1)) (d n) ++ std d n ++ std d (n + 1) =
        wpow (std d (n + 1)) (d n) ++ (std d n ++ std d (n + 1)) := by rw [List.append_assoc]
    have e2 : std d (n + 1) ++ (wpow (std d (n + 1)) (d n) ++ std d n) =
        wpow (std d (n + 1)) (d n) ++ (std d (n + 1) ++ std d n) := by
      rw [← List.append_assoc, wpow_comm, List.append_assoc]
    rw [e1, e2]
    have ih := agree_symm _ _ _ (std_near_comm d n)
    have h := agree_append_left (wpow (std d (n + 1)) (d n)) _ _ _ ih
    have hl : (wpow (std d (n + 1)) (d n) ++ std d n).length + (std d (n + 1)).length - 2 =
        (wpow (std d (n + 1)) (d n)).length + ((std d (n + 1)).length + (std d n).length - 2) := by
      rw [List.length_append]
      have := std_length_pos d n; have := std_length_pos d (n + 1); omega
    rw [hl]; exact h

theorem prefix_agree (B A W : List Bool) (h : A <+: W) : Agree (B ++ A) (B ++ W) (B.length + A.length) := by
  apply agree_append_left
  intro i hi
  exact (getD_of_prefix h i hi).symm

/-- **The near-square at the start.** For every `n`, the characteristic word agrees with its shift by
`|std d (n + 1)|` on the first `|std d (n + 1)| - 2` positions: a near-square at the pair `(0, |std d (n + 1)|)`
with slack `2`. -/
theorem cw_near_square (d : Nat → Nat) (hd : ∀ n, 1 ≤ d n) (n s : Nat) (hs : s + 2 < (std d (n + 1)).length) :
    cw d s = cw d ((std d (n + 1)).length + s) := by
  have hBpos := std_length_pos d n
  have hleft : cw d s = (std d (n + 1)).getD s false := cw_eq d hd n s (by omega)
  obtain ⟨a, ha⟩ : ∃ a, d n = a + 1 := ⟨d n - 1, by have := hd n; omega⟩
  rcases a with _ | a
  · -- `d n = 1`: `std d (n + 2) = A ++ B`; read the shifted position inside `(A ++ B) ++ W` with `A <+: W`
    have h2 : std d (n + 2) = std d (n + 1) ++ std d n := by
      rw [std_succ_succ, ha, wpow_succ]; simp [wpow]
    obtain ⟨b, hb⟩ : ∃ b, d (n + 1) = b + 1 := ⟨d (n + 1) - 1, by have := hd (n + 1); omega⟩
    have hW : std d (n + 1) <+: wpow (std d (n + 2)) b ++ std d (n + 1) := by
      rcases b with _ | b
      · simp [wpow]
      · rw [wpow_succ, List.append_assoc]
        exact (std_prefix d hd n).trans (List.prefix_append _ _)
    have h3 : std d (n + 3) = (std d (n + 1) ++ std d n) ++ (wpow (std d (n + 2)) b ++ std d (n + 1)) := by
      rw [show n + 3 = (n + 1) + 2 by omega, std_succ_succ, show n + 1 + 1 = n + 2 by omega, hb, wpow_succ,
        List.append_assoc]
      rw (occs := .pos [1]) [h2]
    have hlen : (std d (n + 1)).length + s < (std d (n + 3)).length := by
      rw [h3, List.length_append, List.length_append]
      have := hW.length_le; omega
    rw [cw_eq d hd (n + 2) _ hlen, h3, List.append_assoc,
      getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
      ← prefix_agree (std d n) (std d (n + 1)) _ hW s (by omega),
      ← (std_near_comm d n) s (by omega), getD_append _ _ _ _ (by omega), hleft]
  · -- `d n ≥ 2`: `std d (n + 2) = A ++ (A ++ …)`, the shifted position is in the second copy of `A`
    have h2 : std d (n + 2) = std d (n + 1) ++ (std d (n + 1) ++ (wpow (std d (n + 1)) a ++ std d n)) := by
      rw [std_succ_succ, ha, wpow_succ, wpow_succ]; simp only [List.append_assoc]
    have hlen : (std d (n + 1)).length + s < (std d (n + 2)).length := by
      rw [h2, List.length_append, List.length_append]; omega
    rw [cw_eq d hd (n + 1) _ hlen, h2, getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
      getD_append _ _ _ _ (by omega), hleft]

/-! ## Every characteristic Sturmian word is excluded beside the clock -/

/-- **Every characteristic Sturmian word is excluded.** A configuration with a leftmost black cell, whose column
`0` reads the clock from time `0`, cannot have the characteristic word of any directive sequence `d` (every
`d n ≥ 1`) as its visible bits `evol x0 (2 i) 1`. -/
theorem characteristic_excluded (d : Nat → Nat) (hd : ∀ n, 1 ≤ d n) (x0 : Int → Bool) (L : Nat)
    (hc : x0 (-(L : Int)) = true) (hl : ∀ j < -(L : Int), x0 j = false)
    (hclock : ∀ t, evol x0 t 0 = decide (t % 2 = 1)) (hvis : ∀ i, evol x0 (2 * i) 1 = cw d i) : False := by
  have hL : 1 ≤ L := by
    refine Classical.byContradiction fun h0 => ?_
    have hL0 : L = 0 := by omega
    subst hL0
    have h := hclock 0
    rw [show evol x0 0 0 = x0 0 from rfl] at h
    have hc0 : x0 0 = true := by simpa using hc
    rw [hc0] at h
    exact absurd h (by decide)
  refine corollary_F x0 L hL hc hl 0 (fun t _ => hclock t) 2 (fun N => ?_)
  refine ⟨0, (std d (N + 1)).length, std_length_pos d (N + 1), by have := std_length_ge d hd N; omega,
    by omega, fun s hs => ?_⟩
  rw [hvis, hvis, Nat.zero_add]
  exact cw_near_square d hd N s hs

/-- The same with the letters exchanged (the characteristic words of the other slopes). -/
theorem characteristic_excluded_compl (d : Nat → Nat) (hd : ∀ n, 1 ≤ d n) (x0 : Int → Bool) (L : Nat)
    (hc : x0 (-(L : Int)) = true) (hl : ∀ j < -(L : Int), x0 j = false)
    (hclock : ∀ t, evol x0 t 0 = decide (t % 2 = 1)) (hvis : ∀ i, evol x0 (2 * i) 1 = !cw d i) : False := by
  have hL : 1 ≤ L := by
    refine Classical.byContradiction fun h0 => ?_
    have hL0 : L = 0 := by omega
    subst hL0
    have h := hclock 0
    rw [show evol x0 0 0 = x0 0 from rfl] at h
    have hc0 : x0 0 = true := by simpa using hc
    rw [hc0] at h
    exact absurd h (by decide)
  refine corollary_F x0 L hL hc hl 0 (fun t _ => hclock t) 2 (fun N => ?_)
  refine ⟨0, (std d (N + 1)).length, std_length_pos d (N + 1), by have := std_length_ge d hd N; omega,
    by omega, fun s hs => ?_⟩
  rw [hvis, hvis, Nat.zero_add, cw_near_square d hd N s hs]

/-- The Fibonacci word, `d n = 1` for every `n`, as the first example. -/
theorem fibonacci_excluded (x0 : Int → Bool) (L : Nat) (hc : x0 (-(L : Int)) = true) (hl : ∀ j < -(L : Int), x0 j = false)
    (hclock : ∀ t, evol x0 t 0 = decide (t % 2 = 1)) (hvis : ∀ i, evol x0 (2 * i) 1 = cw (fun _ => 1) i) :
    False :=
  characteristic_excluded (fun _ => 1) (fun _ => Nat.le_refl 1) x0 L hc hl hclock hvis

/-! ## Sliding block codes of the characteristic words are excluded too -/

/-- A sliding block code of window `r`: `image f r c i = f [c i, …, c (i + r - 1)]`. The letter exchange is the
window-`1` code `f = not`; every finite block factor of the word is one of these. -/
def image (f : List Bool → Bool) (r : Nat) (c : Nat → Bool) (i : Nat) : Bool :=
  f ((List.range r).map fun j => c (i + j))

theorem image_congr (f : List Bool → Bool) (r : Nat) (c : Nat → Bool) (i i' : Nat)
    (h : ∀ j, j < r → c (i + j) = c (i' + j)) : image f r c i = image f r c i' := by
  unfold image
  congr 1
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  exact h j hj

/-- A near-square of slack `K` in `c` is a near-square of slack `K + r` in its window-`r` code. -/
theorem image_near_square (f : List Bool → Bool) (r : Nat) (c : Nat → Bool) (K i i' : Nat)
    (hc : ∀ s, s + K < i' → c (i + s) = c (i' + s)) :
    ∀ s, s + (K + r) < i' → image f r c (i + s) = image f r c (i' + s) := by
  intro s hs
  apply image_congr
  intro j hj
  rw [Nat.add_assoc, Nat.add_assoc]
  exact hc (s + j) (by omega)

/-- **Every sliding block code of a characteristic Sturmian word is excluded** as the visible bits beside the
clock. -/
theorem characteristic_block_excluded (d : Nat → Nat) (hd : ∀ n, 1 ≤ d n) (f : List Bool → Bool) (r : Nat)
    (x0 : Int → Bool) (L : Nat) (hc : x0 (-(L : Int)) = true) (hl : ∀ j < -(L : Int), x0 j = false)
    (hclock : ∀ t, evol x0 t 0 = decide (t % 2 = 1))
    (hvis : ∀ i, evol x0 (2 * i) 1 = image f r (cw d) i) : False := by
  have hL : 1 ≤ L := by
    refine Classical.byContradiction fun h0 => ?_
    have hL0 : L = 0 := by omega
    subst hL0
    have h := hclock 0
    rw [show evol x0 0 0 = x0 0 from rfl] at h
    have hc0 : x0 0 = true := by simpa using hc
    rw [hc0] at h
    exact absurd h (by decide)
  refine corollary_F x0 L hL hc hl 0 (fun t _ => hclock t) (2 + r) (fun N => ?_)
  refine ⟨0, (std d (N + 1)).length, std_length_pos d (N + 1), by have := std_length_ge d hd N; omega,
    by omega, fun s hs => ?_⟩
  rw [hvis, hvis]
  exact image_near_square f r (cw d) 2 0 _ (fun s hs => by rw [Nat.zero_add]; exact cw_near_square d hd N s hs) s hs

end Ruliology.CellularAutomata.Rule30ClockNearSquares
