module

public import Ruliology.CellularAutomata.Rule30PeriodTwo

/-!
# Rule 30: the zero-boundary left half (ZBL) and the period-2 question `Q01`

If the center column alternates from some time on, the left half sees the center only through
`c t && c (t + 1)` (`Rule30MaskedJen.effective_step`), which is then white: the left half evolves
as rule 30 on the positions `p ≤ -1` with position `0` held white. This module develops that
system, the **zero-boundary left half** (ZBL), in one encoding: `zrow L t k` is the cell at depth
`k` (position `-k`) and time `t`, depth `0` is the wall, and the start `L` is read at depths
`k ≥ 1`.

**Dynamics and locality.**
* `zrow_inv` (left permutivity), `zrow_shift` (semiflow), `zrow_stripe` (the stripe `…10101` is
  fixed), `zrow_edge` (the last black cell moves out one depth per step).
* `zrow_light_cone`, `zrow_local`, `zrow_translate`; `zrow_aff` and `pivot` (flipping the start at
  depth `t + 1` flips column `-1` at time `t`); `zero_run_local`.
* `complete_near_wall`, `edge_region_barrier`: any far part of the start can be completed near the
  wall so that column `-1` follows any prescribed values up to time `d - 1`.
* `backward_det`, `history_det`: a row is determined by its image and its depth-`1` cell; the
  backward transducer `back`, and `back_fin_iff` (when the preimage is finitely supported).
* `survive_iff`, `col2_doubling`, `col3_of_col2`, `no_two_white`: the forced skeleton of a
  constrained history.

**Realization and the free bits.**
* `recon` (sideways reconstruction from column `-1`), `history_eq_recon`, `realization`: every
  column-`-1` sequence `a` is realized by exactly one start, `lam a`. `zrow_det`, `zrow_pivot`.
* `Theta f = lam (alt f)`: the constrained start (column `-1` black at the even steps) with free bits
  `f`. `inX_iff`, `Theta_unique`: the constrained starts are exactly the image of `Theta`.
  `Theta_inj`, `Theta_dep`, `Theta_inverse_dep`, `Theta_image_closed`, `FW_closed`: `Theta` is a
  homeomorphism onto a closed set. `tri_odd`, `tri_even`: triangular form with a pivot at every
  other depth. `two_step_shift`: two ZBL steps act on the free bits as the full shift.
  `small_identities`.
* `count_constrained`: exactly `2 ^ ⌊W / 2⌋` starts of width `≤ W` satisfy the constraint up to
  time `W - 1`.

**`Q01`.** No finitely supported start keeps column `-1` black at every even step. Open.
* `Q01_iff_Theta` (no `Theta f` is finitely supported), `Q01_iff_any_phase`, `Q01_iff_bounded`
  (bounded white runs of the forced row, via `uniform_death`), `koenig` (compactness of the search
  tree), `Q01_iff_staged` (it is `Rule30PeriodTwo.Q01`), `no_eventual_period_two`.
* `Q01_iff_integer`: read as a natural number `Y` (bit `i` at depth `i + 1`), a finite start
  evolves by `F Y = (Y >>> 1) ^^^ (Y ||| (Y <<< 1))`, and `Q01` holds iff every natural number
  reaches an even number under some iterate of `G = F ∘ F` (`IntegerForm`).

**Jen inside the ZBL.** `jen_clock`: a nonzero finite start with last black cell at depth `m` has no
`P`-periodic window `[T, T + ℓ]` of column `-1` with `ℓ + 2 > T + m + 2 P`;
`col_not_eventually_periodic`, `free_bits_clock`, `free_not_eventuallyPeriodic`,
`constrained_col1_aperiodic`.

**Bridge to rule 30.** `L_eq_zrow` (the ZBL is `Rule30DrivenLeft.L` with the white driver),
`left_half_is_zbl`, `alternating_free_bits_clock`, `left_right_white`,
`alternating_right_col1_clock`, and `free_bits_no00_no11111`: under an alternating center the free
bits `cell (T + 2 k + 1) (-1)` contain neither `00` (`Rule30PeriodTwo.golden`) nor `11111`
(`col1_black_among_five`, a kernel check over the light cone of columns `1..11`).
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30ZeroBoundary

open Rule30Jen Rule30Prize

/-! ### The dynamics -/

/-- The zero-boundary left half (ZBL): rule 30 on the positions `-1, -2, …` with position `0`
held white. `zrow L t k` is the color at time `t` of the cell at depth `k` (position `-k`); depth
`0` is the wall. The start `L` is read at depths `k ≥ 1` (`L 0` is ignored). -/
def zrow (L : Nat → Bool) : Nat → Nat → Bool
  | 0, k => if k = 0 then false else L k
  | t + 1, k => if k = 0 then false else xor (zrow L t (k + 1)) (zrow L t k || zrow L t (k - 1))

theorem zrow_wall (L : Nat → Bool) : ∀ t, zrow L t 0 = false
  | 0 => rfl
  | _ + 1 => rfl

theorem zrow_zero (L : Nat → Bool) (k : Nat) : zrow L 0 (k + 1) = L (k + 1) := rfl

theorem zrow_zero_of_pos (L : Nat → Bool) {k : Nat} (hk : 1 ≤ k) : zrow L 0 k = L k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rfl

theorem zrow_succ (L : Nat → Bool) (t k : Nat) :
    zrow L (t + 1) (k + 1) = xor (zrow L t (k + 2)) (zrow L t (k + 1) || zrow L t k) := rfl

/-- Left-permutive inversion inside the ZBL. -/
theorem zrow_inv (L : Nat → Bool) (t k : Nat) :
    zrow L t (k + 2) = xor (zrow L (t + 1) (k + 1)) (zrow L t (k + 1) || zrow L t k) := by
  rw [zrow_succ]; cases zrow L t (k + 2) <;> cases (zrow L t (k + 1) || zrow L t k) <;> rfl

/-- The ZBL is a semiflow: the row at time `s` restarts the run. -/
theorem zrow_shift (L : Nat → Bool) (s : Nat) : ∀ t k, zrow L (s + t) k = zrow (zrow L s) t k := by
  intro t
  induction t with
  | zero =>
    intro k
    cases k with
    | zero => simp [zrow_wall]
    | succ k => rfl
  | succ t ih =>
    intro k
    cases k with
    | zero => simp [zrow_wall]
    | succ k =>
      rw [show s + (t + 1) = (s + t) + 1 by omega, zrow_succ, zrow_succ, ih, ih, ih]

/-- The row at time `0` is the start with a white wall. -/
theorem zrow_zero_self {L : Nat → Bool} (h : L 0 = false) : zrow L 0 = L := by
  funext k
  cases k with
  | zero => exact h.symm
  | succ k => rfl

/-- The run only sees the start at depths `≥ 1`. -/
theorem zrow_congr {L L' : Nat → Bool} (h : ∀ k, 1 ≤ k → L k = L' k) : ∀ t k, zrow L t k = zrow L' t k := by
  intro t
  induction t with
  | zero =>
    intro k
    cases k with
    | zero => rfl
    | succ k => exact h (k + 1) (by omega)
  | succ t ih =>
    intro k
    cases k with
    | zero => rfl
    | succ k => rw [zrow_succ, zrow_succ, ih, ih, ih]

/-! ### The stripe -/

/-- The stripe `…10101`: black exactly at the odd depths. -/
def stripe (k : Nat) : Bool := k % 2 == 1

theorem stripe_succ (k : Nat) : stripe (k + 1) = !stripe k := by
  unfold stripe
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · have : (k + 1) % 2 = 1 := by omega
    simp [h, this]
  · have : (k + 1) % 2 = 0 := by omega
    simp [h, this]

theorem stripe_add_two (k : Nat) : stripe (k + 2) = stripe k := by
  rw [stripe_succ, stripe_succ]; simp

theorem stripe_or (k : Nat) : (stripe (k + 1) || stripe k) = true := by
  rw [stripe_succ]; cases stripe k <;> rfl

theorem stripe_odd {k : Nat} (h : k % 2 = 1) : stripe k = true := by unfold stripe; simp [h]
theorem stripe_even {k : Nat} (h : k % 2 = 0) : stripe k = false := by unfold stripe; simp [h]

/-- The local rule fixes the stripe. -/
theorem stripe_step (k : Nat) : stripe (k + 1) = xor (stripe (k + 2)) (stripe (k + 1) || stripe k) := by
  rw [stripe_or, stripe_add_two, stripe_succ]; cases stripe k <;> rfl

/-- The stripe is a fixed point of the ZBL. -/
theorem zrow_stripe : ∀ t k, zrow stripe t k = stripe k := by
  intro t
  induction t with
  | zero =>
    intro k
    cases k with
    | zero => rfl
    | succ k => rfl
  | succ t ih =>
    intro k
    cases k with
    | zero => rfl
    | succ k => rw [zrow_succ, ih, ih, ih, ← stripe_step]

/-! ### Finite rows -/

/-- A row is finitely supported: white beyond some depth. -/
def FinSupp (L : Nat → Bool) : Prop := ∃ W, ∀ k, W < k → L k = false

/-- The support grows by at most one depth per step. -/
theorem zrow_fin {L : Nat → Bool} {W : Nat} (h : ∀ k, W < k → L k = false) :
    ∀ t k, W + t < k → zrow L t k = false := by
  intro t
  induction t with
  | zero =>
    intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    exact h _ (by omega)
  | succ t ih =>
    intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [zrow_succ, ih _ (by omega), ih _ (by omega), ih _ (by omega)]
    rfl

/-- **The edge moves out by one depth per step.** If the last black cell of the start is at depth
`m ≥ 1`, the last black cell at time `t` is at depth `m + t`. -/
theorem zrow_edge {L : Nat → Bool} {m : Nat} (hm : 1 ≤ m) (hedge : L m = true)
    (hfin : ∀ k, m < k → L k = false) :
    ∀ t, zrow L t (m + t) = true ∧ ∀ k, m + t < k → zrow L t k = false := by
  intro t
  induction t with
  | zero =>
    refine ⟨?_, fun k hk => ?_⟩
    · rw [Nat.add_zero, zrow_zero_of_pos L hm, hedge]
    · rw [zrow_zero_of_pos L (by omega), hfin k (by omega)]
  | succ t ih =>
    refine ⟨?_, fun k hk => ?_⟩
    · rw [show m + (t + 1) = (m + t) + 1 by omega, zrow_succ, ih.2 (m + t + 2) (by omega),
        ih.2 (m + t + 1) (by omega), ih.1]
      rfl
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [zrow_succ, ih.2 _ (by omega), ih.2 _ (by omega), ih.2 _ (by omega)]
      rfl

/-- A finitely supported row that is black at depth `1` has a last black cell. -/
theorem last_black {L : Nat → Bool} (h1 : L 1 = true) :
    ∀ W, (∀ k, W < k → L k = false) → ∃ m, 1 ≤ m ∧ L m = true ∧ ∀ k, m < k → L k = false := by
  intro W
  induction W with
  | zero => intro hz; exact absurd (hz 1 (by omega)) (by rw [h1]; decide)
  | succ W ih =>
    intro hz
    cases hW : L (W + 1)
    · exact ih fun k hk => by
        rcases Nat.lt_or_ge (W + 1) k with h | h
        · exact hz k h
        · rw [show k = W + 1 by omega]; exact hW
    · exact ⟨W + 1, by omega, hW, fun k hk => hz k hk⟩

/-! ### Locality -/

/-- **Light cone.** The cell at depth `k` and time `t` only depends on the start at depths
`1, …, k + t`. -/
theorem zrow_light_cone {L L' : Nat → Bool} :
    ∀ t k, (∀ i, 1 ≤ i → i ≤ k + t → L i = L' i) → zrow L t k = zrow L' t k := by
  intro t
  induction t with
  | zero =>
    intro k h
    cases k with
    | zero => rfl
    | succ k => exact h (k + 1) (by omega) (by omega)
  | succ t ih =>
    intro k h
    cases k with
    | zero => rfl
    | succ j =>
      rw [zrow_succ, zrow_succ, ih (j + 2) (fun i h1 h2 => h i h1 (by omega)),
        ih (j + 1) (fun i h1 h2 => h i h1 (by omega)), ih j (fun i h1 h2 => h i h1 (by omega))]

/-- **Outer locality.** Starts that agree from depth `a ≥ 1` on agree at time `s` from depth
`a + s` on. -/
theorem zrow_local {L L' : Nat → Bool} {a : Nat} (ha : 1 ≤ a) (h : ∀ k, a ≤ k → L k = L' k) :
    ∀ s k, a + s ≤ k → zrow L s k = zrow L' s k := by
  intro s
  induction s with
  | zero =>
    intro k hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    exact h _ (by omega)
  | succ s ih =>
    intro k hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [zrow_succ, zrow_succ, ih (k' + 2) (by omega), ih (k' + 1) (by omega), ih k' (by omega)]

/-- **Translation away from the wall.** If `L'` is `L` moved out by `d` depths from depth `a ≥ 1`
on, the runs agree (moved out by `d`) at time `t` from depth `a + t` on. -/
theorem zrow_translate {L L' : Nat → Bool} {d a : Nat} (ha : 1 ≤ a)
    (h : ∀ k, a ≤ k → L' (k + d) = L k) : ∀ t k, a + t ≤ k → zrow L' t (k + d) = zrow L t k := by
  intro t
  induction t with
  | zero =>
    intro k hk
    rw [zrow_zero_of_pos L' (by omega), zrow_zero_of_pos L (by omega), h k (by omega)]
  | succ t ih =>
    intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [show j + 1 + d = (j + d) + 1 by omega, zrow_succ, zrow_succ,
      show j + d + 2 = (j + 2) + d by omega, show j + d + 1 = (j + 1) + d by omega,
      ih (j + 2) (by omega), ih (j + 1) (by omega), show j + d = j + d from rfl]
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [show i + 1 + d = (i + 1) + d from rfl, ih (i + 1) (by omega)]

/-- **Pivot, general depth.** If two starts agree at depths `1, …, k + t - 1`, the cells at depth
`k ≥ 1` and time `t` differ exactly when the starts differ at depth `k + t`. -/
theorem zrow_aff : ∀ t (L L' : Nat → Bool) (k : Nat), 1 ≤ k →
    (∀ i, 1 ≤ i → i < k + t → L i = L' i) →
    xor (zrow L t k) (zrow L' t k) = xor (L (k + t)) (L' (k + t)) := by
  intro t
  induction t with
  | zero => intro L L' k hk _; rw [zrow_zero_of_pos L hk, zrow_zero_of_pos L' hk]; rfl
  | succ t ih =>
    intro L L' k hk h
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [zrow_succ, zrow_succ,
      zrow_light_cone t (j + 1) (fun i h1 h2 => h i h1 (by omega)),
      zrow_light_cone t j (fun i h1 h2 => h i h1 (by omega))]
    have key := ih L L' (j + 2) (by omega) (fun i h1 h2 => h i h1 (by omega))
    rw [show j + 1 + (t + 1) = j + 2 + t by omega, ← key]
    generalize zrow L t (j + 2) = a
    generalize zrow L' t (j + 2) = b
    generalize (zrow L' t (j + 1) || zrow L' t j) = c
    cases a <;> cases b <;> cases c <;> rfl

/-- **Pivot.** Two starts that agree at depths `1, …, t` and differ at depth `t + 1` have different
cells at depth `1` at time `t`. -/
theorem pivot {L L' : Nat → Bool} {t : Nat} (hagree : ∀ i, 1 ≤ i → i ≤ t → L i = L' i)
    (hdiff : L (t + 1) ≠ L' (t + 1)) : zrow L t 1 ≠ zrow L' t 1 := by
  have key := zrow_aff t L L' 1 (Nat.le_refl 1) (fun i h1 h2 => hagree i h1 (by omega))
  rw [show 1 + t = t + 1 by omega] at key
  intro he
  apply hdiff
  rw [he] at key
  revert key
  cases zrow L' t 1 <;> cases L (t + 1) <;> cases L' (t + 1) <;> decide

/-- The start cut off below depth `d`: `L` at depths `≤ d`, white beyond. -/
def truncate (L : Nat → Bool) (d : Nat) (k : Nat) : Bool := L k && decide (k ≤ d)

theorem truncate_fin (L : Nat → Bool) (d : Nat) : ∀ k, d < k → truncate L d k = false := by
  intro k hk; simp [truncate]; omega

/-- **Zero-run localization.** If the start is white at depths `d + 1, …, d + n`, column `-1`
agrees with that of the truncation at depth `d` up to time `d + n - 1`. -/
theorem zero_run_local {L : Nat → Bool} {d n : Nat} (hz : ∀ k, d < k → k ≤ d + n → L k = false) :
    ∀ t, t < d + n → zrow L t 1 = zrow (truncate L d) t 1 := by
  intro t ht
  apply zrow_light_cone
  intro i _ hi
  unfold truncate
  by_cases hid : i ≤ d
  · simp [hid]
  · simp [hid, hz i (by omega) (by omega)]

/-- **Near-wall completion.** Any far part `z` (depths `> d`) can be completed at depths `1, …, d`
so that column `-1` follows any prescribed values `c` up to time `d - 1`. -/
theorem complete_near_wall (z c : Nat → Bool) :
    ∀ d, ∃ L : Nat → Bool, (∀ k, d < k → L k = z k) ∧ ∀ t, t < d → zrow L t 1 = c t := by
  intro d
  induction d with
  | zero => exact ⟨z, fun _ _ => rfl, fun t ht => absurd ht (by omega)⟩
  | succ d ih =>
    obtain ⟨L, hLz, hLc⟩ := ih
    by_cases hok : zrow L d 1 = c d
    · exact ⟨L, fun k hk => hLz k (by omega), fun t ht => by
        by_cases htd : t = d
        · subst htd; exact hok
        · exact hLc t (by omega)⟩
    · let L' : Nat → Bool := fun k => if k = d + 1 then !L (d + 1) else L k
      have hagree : ∀ i, 1 ≤ i → i ≤ d → L' i = L i := fun i _ hi => by
        simp [L', show i ≠ d + 1 by omega]
      have hdiff : L' (d + 1) ≠ L (d + 1) := by simp [L']
      have hflip := pivot hagree hdiff
      refine ⟨L', fun k hk => ?_, fun t ht => ?_⟩
      · simp only [L', show k ≠ d + 1 by omega, ite_false]; exact hLz k (by omega)
      · by_cases htd : t = d
        · subst htd
          revert hflip hok
          cases zrow L' t 1 <;> cases zrow L t 1 <;> cases c t <;> simp
        · rw [zrow_light_cone t 1 (fun i h1 h2 => hagree i h1 (by omega))]
          exact hLc t (by omega)

/-- **Edge-region barrier.** Fix any far part `z` and any prescribed column `c`. For every `d` there
is a start that agrees with `z` beyond depth `d` (so its run agrees with that of `z` beyond depth
`d + t` at time `t`, including every left diagonal of the edge region) and whose column `-1`
follows `c` up to time `d - 1`. -/
theorem edge_region_barrier (z c : Nat → Bool) (d : Nat) :
    ∃ L : Nat → Bool, (∀ k, d < k → L k = z k) ∧ (∀ t, t < d → zrow L t 1 = c t) ∧
      ∀ t k, d + 1 + t ≤ k → zrow L t k = zrow z t k := by
  obtain ⟨L, hLz, hLc⟩ := complete_near_wall z c d
  exact ⟨L, hLz, hLc, zrow_local (a := d + 1) (by omega) (fun k hk => hLz k (by omega))⟩

/-! ### Backward determinism -/

/-- **Backward determinism.** Two rows with the same image and the same cell at depth `1` agree.
In a constrained history the depth-`1` cell is forced (black) at every other step. -/
theorem backward_det {L L' : Nat → Bool} {t : Nat} (h : ∀ k, zrow L (t + 1) k = zrow L' (t + 1) k)
    (h1 : zrow L t 1 = zrow L' t 1) : ∀ k, zrow L t k = zrow L' t k := by
  have key : ∀ n, zrow L t n = zrow L' t n ∧ zrow L t (n + 1) = zrow L' t (n + 1) := by
    intro n
    induction n with
    | zero => exact ⟨by rw [zrow_wall, zrow_wall], h1⟩
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [zrow_inv L t n, zrow_inv L' t n, h (n + 1), ih.1, ih.2]
  exact fun k => (key k).1

/-- **A history is determined by its last row and its column `-1`.** -/
theorem history_det {L L' : Nat → Bool} {T : Nat} (hT : ∀ k, zrow L T k = zrow L' T k)
    (h1 : ∀ t, t < T → zrow L t 1 = zrow L' t 1) : ∀ t, t ≤ T → ∀ k, zrow L t k = zrow L' t k := by
  have key : ∀ n, n ≤ T → ∀ k, zrow L (T - n) k = zrow L' (T - n) k := by
    intro n
    induction n with
    | zero => intro _; simpa using hT
    | succ n ih =>
      intro hn
      apply backward_det
      · rw [show T - (n + 1) + 1 = T - n by omega]
        exact ih (by omega)
      · exact h1 _ (by omega)
  intro t ht
  have := key (T - t) (by omega)
  rwa [show T - (T - t) = t by omega] at this

/-- The backward transducer: the unique preimage of the row `y` with depth-`1` cell `b`. -/
def back (b : Bool) (y : Nat → Bool) : Nat → Bool
  | 0 => false
  | 1 => b
  | k + 2 => xor (y (k + 1)) (back b y (k + 1) || back b y k)

theorem zrow_back_zero (b : Bool) (y : Nat → Bool) : zrow (back b y) 0 = back b y :=
  zrow_zero_self rfl

/-- `back b y` is a preimage of `y`. -/
theorem zrow_back (b : Bool) (y : Nat → Bool) : ∀ k, 1 ≤ k → zrow (back b y) 1 k = y k := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [zrow_succ, zrow_back_zero]
  show xor (xor (y (j + 1)) (back b y (j + 1) || back b y j)) (back b y (j + 1) || back b y j) = y (j + 1)
  cases y (j + 1) <;> cases (back b y (j + 1) || back b y j) <;> rfl

/-- Every preimage is given by the backward transducer. -/
theorem eq_back {L y : Nat → Bool} (h : ∀ k, 1 ≤ k → zrow L 1 k = y k) :
    ∀ k, zrow L 0 k = back (L 1) y k := by
  have hstep : ∀ k, zrow L 1 k = zrow (back (L 1) y) 1 k := by
    intro k
    cases k with
    | zero => rw [zrow_wall, zrow_wall]
    | succ k => rw [h (k + 1) (by omega), zrow_back _ _ (k + 1) (by omega)]
  have := backward_det (t := 0) hstep rfl
  intro k
  rw [this k, zrow_back_zero]

/-- **Finite-preimage criterion.** If `y` is white from depth `n ≥ 2` on, its preimage with
depth-`1` cell `b` is finitely supported iff the backward transducer is white at depths `n - 1`
and `n`. -/
theorem back_fin_iff (b : Bool) {y : Nat → Bool} {n : Nat} (hn : 2 ≤ n)
    (hy : ∀ k, n ≤ k → y k = false) :
    FinSupp (back b y) ↔ (back b y (n - 1) = false ∧ back b y n = false) := by
  constructor
  · rintro ⟨M, hM⟩
    have prop : ∀ j, (back b y (n - 1 + j) || back b y (n + j)) = true →
        back b y (n + j + 1) = true := by
      intro j hj
      rw [show n + j + 1 = (n + j - 1) + 2 by omega, back, hy _ (by omega),
        show n + j - 1 + 1 = n + j by omega, show n + j - 1 = n - 1 + j by omega]
      rw [Bool.or_comm] at hj
      simp [hj]
    refine Classical.byContradiction fun hne => ?_
    have h0 : (back b y (n - 1 + 0) || back b y (n + 0)) = true := by
      cases h1 : back b y (n - 1) <;> cases h2 : back b y n <;> simp_all
    have allb : ∀ j, back b y (n + j + 1) = true := by
      intro j
      induction j with
      | zero => exact prop 0 h0
      | succ j ih =>
        apply prop (j + 1)
        simp [show n + (j + 1) = n + j + 1 by omega, ih]
    have := allb M
    rw [hM _ (by omega)] at this
    exact absurd this (by decide)
  · rintro ⟨h1, h2⟩
    refine ⟨n - 1, fun k hk => ?_⟩
    have all : ∀ j, back b y (n - 1 + j) = false ∧ back b y (n + j) = false := by
      intro j
      induction j with
      | zero => exact ⟨h1, h2⟩
      | succ j ih =>
        refine ⟨by rw [show n - 1 + (j + 1) = n + j by omega]; exact ih.2, ?_⟩
        rw [show n + (j + 1) = (n - 1 + j) + 2 by omega, back, hy _ (by omega),
          show n - 1 + j + 1 = n + j by omega, ih.2, ih.1]
        rfl
    have := (all (k - (n - 1))).1
    rwa [show n - 1 + (k - (n - 1)) = k by omega] at this


/-! ### The forced skeleton of a constrained history -/

/-- Two steps after a black depth-`1` cell, depth `1` holds `L 2 xor L 3`. -/
theorem zrow_two_one (L : Nat → Bool) (h1 : L 1 = true) : zrow L 2 1 = xor (L 2) (L 3) := by
  show xor (xor (L 3) (L 2 || L 1)) (xor (L 2) (L 1 || false) || false) = xor (L 2) (L 3)
  rw [h1]; cases L 2 <;> cases L 3 <;> rfl

/-- **One-step survival.** At a forced (black) step, the next forced step is black iff the cells
at depths `2` and `3` differ. -/
theorem survive_iff (L : Nat → Bool) (h1 : L 1 = true) : zrow L 2 1 = true ↔ L 2 ≠ L 3 := by
  rw [zrow_two_one L h1]
  cases L 2 <;> cases L 3 <;> decide

/-- Column `-2` is constant on each forced pair of steps. -/
theorem col2_doubling (L : Nat → Bool) (h1 : L 1 = true) (h2 : zrow L 2 1 = true) :
    zrow L 1 2 = L 2 := by
  have hne := (survive_iff L h1).1 h2
  show xor (L 3) (L 2 || L 1) = L 2
  rw [h1]
  revert hne; cases L 2 <;> cases L 3 <;> simp

/-- Column `-3` is the complement of column `-2` one step later, unless depths `1, 2` are both
white. -/
theorem col3_of_col2 (L : Nat → Bool) (h : (L 1 || L 2) = true) : L 3 = !zrow L 1 2 := by
  show L 3 = !xor (L 3) (L 2 || L 1)
  revert h; cases L 1 <;> cases L 2 <;> cases L 3 <;> decide

/-- No two white cells at depths `1, 2` on either step of a forced pair. -/
theorem no_two_white (L : Nat → Bool) (h1 : L 1 = true) (h2 : zrow L 2 1 = true) :
    (L 1 || L 2) = true ∧ (zrow L 1 1 || zrow L 1 2) = true := by
  have hne := (survive_iff L h1).1 h2
  refine ⟨by rw [h1]; rfl, ?_⟩
  show (xor (L 2) (L 1 || false) || xor (L 3) (L 2 || L 1)) = true
  rw [h1]
  revert hne; cases L 2 <;> cases L 3 <;> simp

/-! ### Reconstruction from column `-1` -/

/-- The sideways reconstruction from a column-`-1` sequence `a` and the white wall: `recon a k t`
is the cell at depth `k` and time `t`. -/
def recon (a : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => false
  | 1, t => a t
  | k + 2, t => xor (recon a (k + 1) (t + 1)) (recon a (k + 1) t || recon a k t)

theorem recon_two (a : Nat → Bool) (k t : Nat) :
    recon a (k + 2) t = xor (recon a (k + 1) (t + 1)) (recon a (k + 1) t || recon a k t) := by
  rw [recon]

/-- The start forced by the column-`-1` sequence `a`. -/
def lam (a : Nat → Bool) (k : Nat) : Bool := recon a k 0

/-- The run of `lam a` is the reconstruction. -/
theorem zrow_lam (a : Nat → Bool) : ∀ t k, zrow (lam a) t k = recon a k t := by
  intro t
  induction t with
  | zero =>
    intro k
    cases k with
    | zero => rfl
    | succ k => rfl
  | succ t ih =>
    intro k
    cases k with
    | zero => rfl
    | succ k =>
      rw [zrow_succ, ih, ih, ih, recon_two]
      cases recon a (k + 1) (t + 1) <;> cases (recon a (k + 1) t || recon a k t) <;> rfl

/-- **Every history is the reconstruction from its own column `-1`.** -/
theorem history_eq_recon (L : Nat → Bool) : ∀ k t, zrow L t k = recon (fun t => zrow L t 1) k t := by
  have key : ∀ k, (∀ t, zrow L t k = recon (fun t => zrow L t 1) k t) ∧
      (∀ t, zrow L t (k + 1) = recon (fun t => zrow L t 1) (k + 1) t) := by
    intro k
    induction k with
    | zero => exact ⟨fun t => zrow_wall L t, fun t => by rw [recon]⟩
    | succ k ih =>
      refine ⟨ih.2, fun t => ?_⟩
      rw [recon_two, ← ih.2 (t + 1), ← ih.2 t, ← ih.1 t]
      exact zrow_inv L t k
  exact fun k t => (key k).1 t

/-- **Realization.** For every column-`-1` sequence `a`, the start `lam a` realizes it, and every
start that realizes it is `lam a` (at every depth `≥ 1`). -/
theorem realization (a : Nat → Bool) :
    (∀ t, zrow (lam a) t 1 = a t) ∧ ∀ L : Nat → Bool, (∀ t, zrow L t 1 = a t) → zrow L 0 = lam a := by
  refine ⟨fun t => by rw [zrow_lam]; rfl, fun L h => ?_⟩
  have ha : (fun t => zrow L t 1) = a := funext h
  funext k
  rw [history_eq_recon L k 0, ha]
  rfl

/-- `recon a k t` only depends on `a` at times `t, …, t + k - 1`. -/
theorem recon_local {a b : Nat → Bool} : ∀ k t, (∀ j, j < k → a (t + j) = b (t + j)) →
    recon a k t = recon b k t := by
  have key : ∀ k, (∀ t, (∀ j, j < k → a (t + j) = b (t + j)) → recon a k t = recon b k t) ∧
      (∀ t, (∀ j, j < k + 1 → a (t + j) = b (t + j)) → recon a (k + 1) t = recon b (k + 1) t) := by
    intro k
    induction k with
    | zero =>
      refine ⟨fun t _ => by rw [recon, recon], fun t h => ?_⟩
      have := h 0 (by omega)
      rw [recon, recon]; simpa using this
    | succ k ih =>
      refine ⟨ih.2, fun t h => ?_⟩
      rw [recon_two, recon_two,
        ih.2 (t + 1) (fun j hj => by
          have := h (j + 1) (by omega); rwa [show t + (j + 1) = t + 1 + j by omega] at this),
        ih.2 t (fun j hj => h j (by omega)), ih.1 t (fun j hj => h j (by omega))]
  exact fun k t h => (key k).1 t h

/-- Shift equivariance of the reconstruction. -/
theorem recon_shift (a : Nat → Bool) (P : Nat) :
    ∀ k t, recon a k (t + P) = recon (fun s => a (s + P)) k t := by
  have key : ∀ k, (∀ t, recon a k (t + P) = recon (fun s => a (s + P)) k t) ∧
      (∀ t, recon a (k + 1) (t + P) = recon (fun s => a (s + P)) (k + 1) t) := by
    intro k
    induction k with
    | zero => exact ⟨fun t => by rw [recon, recon], fun t => by rw [recon, recon]⟩
    | succ k ih =>
      refine ⟨ih.2, fun t => ?_⟩
      rw [recon_two, recon_two, show t + P + 1 = (t + 1) + P by omega, ih.2, ih.2, ih.1]
  exact fun k t => (key k).1 t

/-- **Affine dependence on the newest entry.** `recon a (k + 1) t` is `a (t + k)` xor a function of
`a t, …, a (t + k - 1)`. -/
theorem recon_aff (k : Nat) : ∀ (a b : Nat → Bool) (t : Nat), (∀ j, j < k → a (t + j) = b (t + j)) →
    xor (recon a (k + 1) t) (recon b (k + 1) t) = xor (a (t + k)) (b (t + k)) := by
  induction k with
  | zero => intro a b t _; rw [recon, recon]; rfl
  | succ k ih =>
    intro a b t h
    rw [recon_two, recon_two, recon_local (k + 1) t (fun j hj => h j (by omega)),
      recon_local k t (fun j hj => h j (by omega))]
    have key := ih a b (t + 1) (fun j hj => by
      have := h (j + 1) (by omega); rwa [show t + (j + 1) = t + 1 + j by omega] at this)
    rw [show t + (k + 1) = t + 1 + k by omega, ← key]
    generalize recon a (k + 1) (t + 1) = x
    generalize recon b (k + 1) (t + 1) = y
    generalize (recon b (k + 1) t || recon b k t) = z
    cases x <;> cases y <;> cases z <;> rfl

/-- **Trace determination.** The cell at depth `k` and time `t` only depends on column `-1` at
times `t, …, t + k - 1`. -/
theorem zrow_det (L L' : Nat → Bool) (k t : Nat)
    (h : ∀ i, i < k → zrow L (t + i) 1 = zrow L' (t + i) 1) : zrow L t k = zrow L' t k := by
  rw [history_eq_recon L k t, history_eq_recon L' k t]
  exact recon_local k t h

/-- **Reconstruction pivot.** If column `-1` of two runs agrees at times `t, …, t + k - 1`, their
cells at depth `k + 1` and time `t` differ exactly when column `-1` differs at time `t + k`. -/
theorem zrow_pivot (L L' : Nat → Bool) (k t : Nat)
    (h : ∀ i, i < k → zrow L (t + i) 1 = zrow L' (t + i) 1) :
    xor (zrow L t (k + 1)) (zrow L' t (k + 1)) = xor (zrow L (t + k) 1) (zrow L' (t + k) 1) := by
  rw [history_eq_recon L (k + 1) t, history_eq_recon L' (k + 1) t]
  exact recon_aff k _ _ t h

/-! ### Constrained rows and the free bits -/

/-- Column `-1` of a constrained history: black at the even steps, the free bits `f` at the odd
steps. -/
def alt (f : Nat → Bool) (t : Nat) : Bool := if t % 2 = 0 then true else f (t / 2)

/-- The reconstruction map: the constrained start with free bits `f`. -/
def Theta (f : Nat → Bool) : Nat → Bool := lam (alt f)

/-- Constrained starts: column `-1` is black at every even step. -/
def InX (L : Nat → Bool) : Prop := ∀ s, zrow L (2 * s) 1 = true

theorem Theta_col (f : Nat → Bool) (t : Nat) : zrow (Theta f) t 1 = alt f t :=
  (realization (alt f)).1 t

theorem Theta_inX (f : Nat → Bool) : InX (Theta f) := by
  intro s; rw [Theta_col]; unfold alt; rw [ite_eq_left (by omega)]

theorem Theta_free (f : Nat → Bool) (s : Nat) : zrow (Theta f) (2 * s + 1) 1 = f s := by
  rw [Theta_col]; unfold alt; rw [ite_eq_right (by omega), show (2 * s + 1) / 2 = s by omega]

theorem Theta_wall (f : Nat → Bool) : Theta f 0 = false := rfl

theorem zrow_zero_run (L : Nat → Bool) (t k : Nat) : zrow (zrow L 0) t k = zrow L t k := by
  rw [← zrow_shift, Nat.zero_add]

/-- **The constrained start with prescribed free bits is unique.** -/
theorem Theta_unique {L f : Nat → Bool} (hX : InX L) (hf : ∀ s, zrow L (2 * s + 1) 1 = f s) :
    zrow L 0 = Theta f := by
  refine (realization (alt f)).2 L fun t => ?_
  unfold alt
  by_cases ht : t % 2 = 0
  · rw [ite_eq_left ht]
    have := hX (t / 2)
    rwa [show 2 * (t / 2) = t by omega] at this
  · rw [ite_eq_right ht, ← hf (t / 2), show 2 * (t / 2) + 1 = t by omega]

/-- **The constrained starts are exactly the image of `Theta`.** -/
theorem inX_iff (L : Nat → Bool) : InX L ↔ ∃ f, zrow L 0 = Theta f := by
  constructor
  · intro hX; exact ⟨_, Theta_unique hX fun _ => rfl⟩
  · rintro ⟨f, hf⟩ s
    rw [← zrow_zero_run, hf]
    exact Theta_inX f s

/-- `Theta` is injective. -/
theorem Theta_inj {f g : Nat → Bool} (h : ∀ k, 1 ≤ k → Theta f k = Theta g k) : f = g := by
  funext s
  rw [← Theta_free f s, ← Theta_free g s]
  exact zrow_congr h _ _

/-- **Continuity of `Theta`.** `Theta f k` only depends on the free bits `f s` with `2 s + 2 ≤ k`. -/
theorem Theta_dep (f g : Nat → Bool) (k : Nat) (h : ∀ s, 2 * s + 2 ≤ k → f s = g s) :
    Theta f k = Theta g k := by
  show recon (alt f) k 0 = recon (alt g) k 0
  apply recon_local k 0
  intro j hj
  unfold alt
  by_cases hj2 : (0 + j) % 2 = 0
  · rw [ite_eq_left hj2, ite_eq_left hj2]
  · rw [ite_eq_right hj2, ite_eq_right hj2]; exact h _ (by omega)

/-- **Continuity of the inverse.** The free bit `f s` is determined by `Theta f` at depths
`≤ 2 s + 2`. -/
theorem Theta_inverse_dep (f g : Nat → Bool) (s : Nat)
    (h : ∀ k, k ≤ 2 * s + 2 → Theta f k = Theta g k) : f s = g s := by
  rw [← Theta_free f s, ← Theta_free g s]
  exact zrow_light_cone (2 * s + 1) 1 (fun i _ hi => h i (by omega))

/-- **Triangular form, odd depths.** `Theta f (2 j + 1)` only depends on `f 0, …, f (j - 1)`. -/
theorem tri_odd (f g : Nat → Bool) (j : Nat) (h : ∀ s, s < j → f s = g s) :
    Theta f (2 * j + 1) = Theta g (2 * j + 1) :=
  Theta_dep f g (2 * j + 1) (fun s hs => h s (by omega))

/-- **Triangular form, even depths (pivot at every other depth).** Given `f 0, …, f (j - 1)`,
`Theta f (2 j + 2)` flips exactly with `f j`. -/
theorem tri_even (f g : Nat → Bool) (j : Nat) (h : ∀ s, s < j → f s = g s) :
    xor (Theta f (2 * j + 2)) (Theta g (2 * j + 2)) = xor (f j) (g j) := by
  show xor (recon (alt f) (2 * j + 1 + 1) 0) (recon (alt g) (2 * j + 1 + 1) 0) = xor (f j) (g j)
  rw [recon_aff (2 * j + 1) (alt f) (alt g) 0 (by
    intro i hi
    unfold alt
    by_cases hi2 : (0 + i) % 2 = 0
    · rw [ite_eq_left hi2, ite_eq_left hi2]
    · rw [ite_eq_right hi2, ite_eq_right hi2]; exact h _ (by omega))]
  unfold alt
  rw [ite_eq_right (by omega), ite_eq_right (by omega), show (0 + (2 * j + 1)) / 2 = j by omega]

/-- **Two-step conjugacy.** Two ZBL steps of `Theta f` give `Theta` of the shifted free bits: the
constrained two-step dynamics is the full one-sided shift. -/
theorem two_step_shift (f : Nat → Bool) : zrow (Theta f) 2 = Theta (fun s => f (s + 1)) := by
  have hX : InX (zrow (Theta f) 2) := by
    intro s
    rw [← zrow_shift, show 2 + 2 * s = 2 * (s + 1) by omega]
    exact Theta_inX f (s + 1)
  have e := Theta_unique hX (f := fun s => f (s + 1)) (fun s => by
    rw [← zrow_shift, show 2 + (2 * s + 1) = 2 * (s + 1) + 1 by omega, Theta_free])
  rwa [zrow_zero_self (zrow_wall _ 2)] at e

/-- **The image of `Theta` is closed.** A start all of whose finite windows are windows of
constrained starts is constrained. -/
theorem Theta_image_closed (L : Nat → Bool)
    (h : ∀ n, ∃ f, ∀ k, 1 ≤ k → k ≤ n → L k = Theta f k) : ∃ f, zrow L 0 = Theta f := by
  refine (inX_iff L).1 fun s => ?_
  obtain ⟨f, hf⟩ := h (2 * s + 1)
  rw [zrow_light_cone (L' := Theta f) (2 * s) 1 (fun i h1 h2 => hf i h1 (by omega))]
  exact Theta_inX f s

/-- With column `-1` black at times `0, 2, 4` and `f₀ = zrow L 1 1`, `f₁ = zrow L 3 1`:
`L 2 = !f₀`, `L 3 = f₀`, `L 4 = !f₁`, `L 5 = f₀`. -/
theorem small_identities (L : Nat → Bool) (h0 : zrow L 0 1 = true) (h2 : zrow L 2 1 = true)
    (h4 : zrow L 4 1 = true) :
    L 2 = !zrow L 1 1 ∧ L 3 = zrow L 1 1 ∧ L 4 = !zrow L 3 1 ∧ L 5 = zrow L 1 1 := by
  have i02 := zrow_inv L 0 0
  have i12 := zrow_inv L 1 0
  have i22 := zrow_inv L 2 0
  have i32 := zrow_inv L 3 0
  have i03 := zrow_inv L 0 1
  have i13 := zrow_inv L 1 1
  have i23 := zrow_inv L 2 1
  have i04 := zrow_inv L 0 2
  have i14 := zrow_inv L 1 2
  have i05 := zrow_inv L 0 3
  simp only [zrow_wall, Bool.or_false] at i02 i12 i22 i32
  have l2 : L 2 = zrow L 0 2 := rfl
  have l3 : L 3 = zrow L 0 3 := rfl
  have l4 : L 4 = zrow L 0 4 := rfl
  have l5 : L 5 = zrow L 0 5 := rfl
  rw [l2, l3, l4, l5, i05, i04, i14, i03, i13, i23, i02, i12, i22, i32, h0, h2, h4]
  cases zrow L 1 1 <;> cases zrow L 3 1 <;> decide

/-! ### `Q01` and its equivalent forms -/

/-- **`Q01`**: no finitely supported start keeps column `-1` black at every even step. Open. -/
def Q01 : Prop := ∀ L : Nat → Bool, FinSupp L → ¬ InX L

/-- **`Q01` in forced-row form**: for every choice of free bits the constrained start is not
finitely supported. -/
theorem Q01_iff_Theta : Q01 ↔ ∀ f, ¬ FinSupp (Theta f) := by
  constructor
  · intro hQ f hfin
    exact hQ _ hfin (Theta_inX f)
  · rintro hL L ⟨W, hW⟩ hX
    apply hL (fun s => zrow L (2 * s + 1) 1)
    refine ⟨W, fun k hk => ?_⟩
    rw [← Theta_unique hX (fun _ => rfl), zrow_zero_of_pos L (by omega), hW k hk]

/-- **`Q01` for either phase.** `Q01` holds iff no finitely supported start keeps column `-1` black
at the steps `T, T + 2, T + 4, …` for some `T`. -/
theorem Q01_iff_any_phase :
    Q01 ↔ ∀ (L : Nat → Bool) (T : Nat), FinSupp L → ¬ ∀ s, zrow L (T + 2 * s) 1 = true := by
  constructor
  · rintro hQ L T ⟨W, hW⟩ hc
    refine hQ (zrow L T) ⟨W + T, fun k hk => zrow_fin hW T k hk⟩ fun s => ?_
    rw [← zrow_shift]; exact hc s
  · intro h L hfin hX
    exact h L 0 hfin fun s => by rw [Nat.zero_add]; exact hX s

/-- The row with `L k = l[k - 1]` at depths `1 ≤ k ≤ l.length`, white beyond. -/
def toRow (l : List Bool) (k : Nat) : Bool := if k = 0 then false else (l[k - 1]?).getD false

theorem toRow_fin (l : List Bool) : ∀ k, l.length < k → toRow l k = false := by
  intro k hk
  unfold toRow
  rw [ite_eq_right (by omega), List.getElem?_eq_none (by omega)]
  rfl

/-- Every row supported at depths `1, …, W` is `toRow l` for a list of length `W`. -/
theorem row_is_list (L : Nat → Bool) (W : Nat) (hL : ∀ k, W < k → L k = false) :
    ∃ l : List Bool, l.length = W ∧ ∀ k, 1 ≤ k → toRow l k = L k := by
  refine ⟨(List.range W).map (fun i => L (i + 1)), by simp, fun k hk => ?_⟩
  unfold toRow
  rw [ite_eq_right (by omega)]
  by_cases hkW : k ≤ W
  · rw [List.getElem?_map, List.getElem?_range (by omega)]
    show L (k - 1 + 1) = L k
    rw [show k - 1 + 1 = k by omega]
  · rw [List.getElem?_eq_none (by simp; omega), hL k (by omega)]
    rfl

theorem toRow_mem (L : Nat → Bool) (W : Nat) (hL : ∀ k, W < k → L k = false) :
    ∃ l ∈ allLists W, ∀ k, 1 ≤ k → toRow l k = L k := by
  obtain ⟨l, hl, h⟩ := row_is_list L W hL
  refine ⟨l, ?_, h⟩
  have := mem_allLists l
  rwa [hl] at this

/-- Under `Q01`, finitely many finite starts die by a common time. -/
theorem uniform_death_list (hQ : Q01) : ∀ Ls : List (List Bool), ∃ D, ∀ l ∈ Ls,
    ∃ s, s ≤ D ∧ zrow (toRow l) (2 * s) 1 = false := by
  intro Ls
  induction Ls with
  | nil => exact ⟨0, fun l hl => absurd hl (by simp)⟩
  | cons l Ls ih =>
    obtain ⟨D, hD⟩ := ih
    have : ∃ s, zrow (toRow l) (2 * s) 1 = false := by
      refine Classical.byContradiction fun hn => hQ _ ⟨l.length, toRow_fin l⟩ fun s => ?_
      cases h : zrow (toRow l) (2 * s) 1
      · exact absurd ⟨s, h⟩ hn
      · rfl
    obtain ⟨s₀, hs₀⟩ := this
    refine ⟨max D s₀, fun l' hl' => ?_⟩
    rcases List.mem_cons.1 hl' with rfl | hl'
    · exact ⟨s₀, by omega, hs₀⟩
    · obtain ⟨s, hs, h⟩ := hD l' hl'
      exact ⟨s, by omega, h⟩

/-- **Uniform death.** Under `Q01`, for every support bound `d` there is a common time by which
every start supported at depths `≤ d` has a white cell at depth `1` at an even step. -/
theorem uniform_death (hQ : Q01) (d : Nat) : ∃ D, ∀ L : Nat → Bool, (∀ k, d < k → L k = false) →
    ∃ s, s ≤ D ∧ zrow L (2 * s) 1 = false := by
  obtain ⟨D, hD⟩ := uniform_death_list hQ (allLists d)
  refine ⟨D, fun L hL => ?_⟩
  obtain ⟨l, hl, hlL⟩ := toRow_mem L d hL
  obtain ⟨s, hs, h⟩ := hD l hl
  exact ⟨s, hs, by rw [← zrow_congr hlL]; exact h⟩

/-- **`Q01` as bounded white runs of the forced row.** `Q01` holds iff for every depth `d` there
is a bound `B` such that, whatever the free bits, the constrained start has a black cell at some
depth in `(d, d + B]`. -/
theorem Q01_iff_bounded :
    Q01 ↔ ∀ d, ∃ B, ∀ f : Nat → Bool, ∃ k, d < k ∧ k ≤ d + B ∧ Theta f k = true := by
  constructor
  · intro hQ d
    obtain ⟨D, hD⟩ := uniform_death hQ d
    refine ⟨2 * D + 2, fun f => Classical.byContradiction fun hn => ?_⟩
    have hz : ∀ k, d < k → k ≤ d + (2 * D + 2) → Theta f k = false := by
      intro k h1 h2
      cases h : Theta f k
      · rfl
      · exact absurd ⟨k, h1, h2, h⟩ hn
    obtain ⟨s, hs, hdead⟩ := hD (truncate (Theta f) d) (truncate_fin _ d)
    rw [← zero_run_local hz (2 * s) (by omega), Theta_inX f s] at hdead
    exact absurd hdead (by decide)
  · intro hB
    rw [Q01_iff_Theta]
    rintro f ⟨M, hM⟩
    obtain ⟨B, hB'⟩ := hB M
    obtain ⟨k, hk1, _, hk3⟩ := hB' f
    rw [hM k hk1] at hk3
    exact absurd hk3 (by decide)

/-! ### `Q01` as an integer iteration

Read a start as the natural number `Y` whose bit `i` is the cell at depth `i + 1`. One ZBL step is
then the map `IntegerForm.F Y = (Y >>> 1) ^^^ (Y ||| (Y <<< 1))` on `Nat` (the wall is bit `-1`),
and column `-1` is bit `0`. -/

namespace IntegerForm

/-- One step of the zero-boundary left half (ZBL) on natural numbers:
bit `i` of `Y` represents depth `k = i + 1` (position `-(i + 1)`), with the white wall at bit `-1`. -/
def F (Y : Nat) : Nat := (Y >>> 1) ^^^ (Y ||| (Y <<< 1))

/-- Two steps of the integer ZBL map, `G = F ∘ F`. -/
def G (Y : Nat) : Nat := F (F Y)

/-- Transparent `t`-step iteration of a map on `Nat`. -/
def iter (f : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | t + 1, x => f (iter f t x)

/-- The ZBL row associated with a natural number `Y`: depth `0` is `false` (the wall), and depth
`k + 1` holds bit `k` of `Y`. -/
def rowOfNat (Y : Nat) : Nat → Bool
  | 0 => false
  | k + 1 => Y.testBit k

/-- Bit `0` of `F Y` (depth `1`, beside the wall). -/
theorem testBit_F_zero (Y : Nat) : (F Y).testBit 0 = xor (Y.testBit 1) (Y.testBit 0) := by
  unfold F
  simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_shiftLeft]
  simp

/-- Bit `i + 1` of `F Y`: the rule-30 update of depth `i + 2`. -/
theorem testBit_F_succ (Y i : Nat) :
    (F Y).testBit (i + 1) = xor (Y.testBit (i + 2)) (Y.testBit (i + 1) || Y.testBit i) := by
  unfold F
  simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_shiftLeft,
    show 1 + (i + 1) = i + 2 by omega, ge_iff_le, Nat.le_add_left, decide_true, Bool.true_and,
    Nat.add_sub_cancel]

/-- **One-step conjugation.** One ZBL step on `rowOfNat Y` is `rowOfNat (F Y)`. -/
theorem zrow_rowOfNat_one (Y : Nat) : ∀ k, zrow (rowOfNat Y) 1 k = rowOfNat (F Y) k
  | 0 => rfl
  | 1 => by
    rw [zrow_succ, zrow_wall, Bool.or_false, zrow_zero, zrow_zero]
    exact (testBit_F_zero Y).symm
  | i + 2 => by
    rw [zrow_succ, zrow_zero, zrow_zero, zrow_zero]
    exact (testBit_F_succ Y i).symm

/-- **Multi-step conjugation.** `t` ZBL steps on `rowOfNat Y` equal `rowOfNat (iter F t Y)`. -/
theorem zrow_rowOfNat (Y : Nat) : ∀ t k, zrow (rowOfNat Y) t k = rowOfNat (iter F t Y) k
  | 0, 0 => rfl
  | 0, k + 1 => rfl
  | t + 1, k => by
    rw [show t + 1 = t + 1 from rfl, zrow_shift (rowOfNat Y) t 1 k]
    have hcongr : ∀ j, 1 ≤ j → zrow (rowOfNat Y) t j = rowOfNat (iter F t Y) j :=
      fun j _ => zrow_rowOfNat Y t j
    rw [zrow_congr hcongr 1 k, zrow_rowOfNat_one]
    rfl

/-- Column `-1` at time `t` is bit `0` of `iter F t Y`. -/
theorem zrow_rowOfNat_col1 (Y t : Nat) :
    zrow (rowOfNat Y) t 1 = (iter F t Y).testBit 0 :=
  zrow_rowOfNat Y t 1

theorem testBit_two_mul_add_zero (A b : Nat) (hb : b < 2) :
    (2 * A + b).testBit 0 = decide (b = 1) := by
  rw [Nat.testBit_zero]
  have : (2 * A + b) % 2 = b := by omega
  rw [this]

theorem testBit_two_mul_add_succ (A b i : Nat) (hb : b < 2) :
    (2 * A + b).testBit (i + 1) = A.testBit i := by
  rw [Nat.testBit_succ]
  have : (2 * A + b) / 2 = A := by omega
  rw [this]

/-- `s` iterates of `G` are `2 s` iterates of `F`. -/
theorem iter_G_eq_iter_F_two_mul (Y : Nat) : ∀ s, iter G s Y = iter F (2 * s) Y
  | 0 => rfl
  | s + 1 => by
    rw [show 2 * (s + 1) = (2 * s + 1) + 1 by omega]
    show F (F (iter G s Y)) = F (F (iter F (2 * s) Y))
    rw [iter_G_eq_iter_F_two_mul Y s]

/-- Encoding a finitely supported row `L` of width `≤ W` as a natural number. -/
def natOfRow : (Nat → Bool) → Nat → Nat
  | _, 0 => 0
  | L, W + 1 => 2 * natOfRow (fun k => L (k + 1)) W + (if L 1 then 1 else 0)

/-- Bit `i` of `natOfRow L W` is the cell of `L` at depth `i + 1`, for `i < W`. -/
theorem testBit_natOfRow : ∀ (W : Nat) (L : Nat → Bool) (i : Nat),
    (natOfRow L W).testBit i = (decide (i < W) && L (i + 1))
  | 0, _, i => by simp [natOfRow]
  | W + 1, L, 0 => by
    unfold natOfRow
    have hb : (if L 1 then 1 else 0) < 2 := by cases L 1 <;> decide
    rw [testBit_two_mul_add_zero _ _ hb]
    cases L 1 <;> simp
  | W + 1, L, i + 1 => by
    unfold natOfRow
    have hb : (if L 1 then 1 else 0) < 2 := by cases L 1 <;> decide
    rw [testBit_two_mul_add_succ _ _ i hb,
      testBit_natOfRow W (fun k => L (k + 1)) i]
    have : decide (i < W) = decide (i + 1 < W + 1) := by
      rcases Nat.lt_or_ge i W with h | h <;> simp [h, show i + 1 < W + 1 ↔ i < W by omega]
    rw [this]

/-- A start that is white beyond depth `W` is `rowOfNat (natOfRow L W)` at every depth `k ≥ 1`. -/
theorem rowOfNat_natOfRow {L : Nat → Bool} {W : Nat} (hW : ∀ k, W < k → L k = false) :
    ∀ k, 1 ≤ k → rowOfNat (natOfRow L W) k = L k := by
  intro k hk
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
  show (natOfRow L W).testBit i = L (i + 1)
  rw [testBit_natOfRow]
  rcases Nat.lt_or_ge i W with h | h
  · simp [h]
  · simp [show ¬ i < W by omega, hW (i + 1) (by omega)]

/-- `rowOfNat Y` is finitely supported. -/
theorem finSupp_rowOfNat (Y : Nat) : FinSupp (rowOfNat Y) := by
  refine ⟨Y, fun k hk => ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
  unfold rowOfNat
  apply Nat.testBit_lt_two_pow
  have h1 : Y < 2 ^ Y := Nat.lt_two_pow_self
  have h2 : 2 ^ Y ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
  omega

end IntegerForm

open IntegerForm in
/-- **`Q01` as an integer iteration.** `Q01` holds iff every natural number `Y` reaches an even
number under some iterate of `G = F ∘ F`, where `F Y = (Y >>> 1) ^^^ (Y ||| (Y <<< 1))` is one ZBL
step on the start whose depth `i + 1` holds bit `i` of `Y` (`IntegerForm.zrow_rowOfNat`): column
`-1` at time `2 s` is bit `0` of the `s`-th iterate of `G`, and every finitely supported start is
such a number (`IntegerForm.natOfRow`). -/
theorem Q01_iff_integer :
    Q01 ↔ ∀ Y : Nat, ∃ s, IntegerForm.iter IntegerForm.G s Y % 2 = 0 := by
  constructor
  · intro hQ Y
    refine Classical.byContradiction fun hne => ?_
    apply hQ (rowOfNat Y) (finSupp_rowOfNat Y)
    intro s
    rw [zrow_rowOfNat_col1, ← iter_G_eq_iter_F_two_mul, Nat.testBit_zero, decide_eq_true_iff]
    have h := not_exists.mp hne s
    omega
  · rintro hInt L ⟨W, hW⟩ hX
    obtain ⟨s, hs⟩ := hInt (natOfRow L W)
    have hcol := hX s
    have hcongr := zrow_congr (rowOfNat_natOfRow hW) (2 * s) 1
    rw [← hcongr, zrow_rowOfNat_col1, ← iter_G_eq_iter_F_two_mul, Nat.testBit_zero,
      decide_eq_true_iff] at hcol
    omega

/-! ### Compactness: the sets `F_W` -/

/-- `F_W = {f | Theta f is white beyond depth W}` is closed. -/
theorem FW_closed (W : Nat) (f : Nat → Bool)
    (h : ∀ n, ∃ g, (∀ s, s < n → g s = f s) ∧ ∀ k, W < k → Theta g k = false) :
    ∀ k, W < k → Theta f k = false := by
  intro k hk
  obtain ⟨g, hgf, hg⟩ := h k
  rw [← Theta_dep g f k (fun s hs => hgf s (by omega))]
  exact hg k hk

/-- Depth `d` of the search tree for width `W`: the prefix `f 0, …, f (d - 1)` keeps depths
`W + 1, …, 2 d + 1` white (these depths are determined by that prefix). -/
def Level (W d : Nat) (f : Nat → Bool) : Prop := ∀ k, W < k → k ≤ 2 * d + 1 → Theta f k = false

theorem level_prefix (W d : Nat) (f g : Nat → Bool) (h : ∀ s, s < d → f s = g s) :
    Level W d f → Level W d g := by
  intro hf k h1 h2
  rw [← Theta_dep f g k (fun s hs => h s (by omega))]
  exact hf k h1 h2

def Good (W n : Nat) (g : Nat → Bool) : Prop :=
  ∀ d, ∃ f, (∀ i, i < n → f i = g i) ∧ Level W d f

def extAt (g : Nat → Bool) (n : Nat) (b : Bool) : Nat → Bool := fun i => if i = n then b else g i

theorem good_ext (W n : Nat) (g : Nat → Bool) (hg : Good W n g) :
    Good W (n + 1) (extAt g n false) ∨ Good W (n + 1) (extAt g n true) := by
  apply Classical.byContradiction
  intro hneg
  have hA : ¬ Good W (n + 1) (extAt g n false) := fun h => hneg (Or.inl h)
  have hB : ¬ Good W (n + 1) (extAt g n true) := fun h => hneg (Or.inr h)
  obtain ⟨d0, hd0⟩ := Classical.not_forall.mp hA
  obtain ⟨d1, hd1⟩ := Classical.not_forall.mp hB
  obtain ⟨f, hfg, hf⟩ := hg (max d0 d1)
  have hm0 := Nat.le_max_left d0 d1
  have hm1 := Nat.le_max_right d0 d1
  have hpre : ∀ i, i < n + 1 → f i = extAt g n (f n) i := by
    intro i hi
    unfold extAt
    by_cases hin : i = n
    · rw [ite_eq_left hin, hin]
    · rw [ite_eq_right hin]; exact hfg i (by omega)
  cases hfn : f n with
  | false =>
    rw [hfn] at hpre
    exact hd0 ⟨f, hpre, fun k h1 h2 => hf k h1 (by omega)⟩
  | true =>
    rw [hfn] at hpre
    exact hd1 ⟨f, hpre, fun k h1 h2 => hf k h1 (by omega)⟩

open Classical in
noncomputable def choiceBit (W n : Nat) (g : Nat → Bool) : Bool :=
  if Good W (n + 1) (extAt g n false) then false else true

theorem good_choice (W n : Nat) (g : Nat → Bool) (hg : Good W n g) :
    Good W (n + 1) (extAt g n (choiceBit W n g)) := by
  unfold choiceBit
  by_cases hc : Good W (n + 1) (extAt g n false)
  · rw [ite_eq_left hc]; exact hc
  · rw [ite_eq_right hc]; exact (good_ext W n g hg).resolve_left hc

noncomputable def branch (W : Nat) : Nat → (Nat → Bool)
  | 0 => fun _ => false
  | n + 1 => extAt (branch W n) n (choiceBit W n (branch W n))

theorem branch_good (W : Nat) (h0 : ∀ d, ∃ f, Level W d f) : ∀ n, Good W n (branch W n) := by
  intro n
  induction n with
  | zero =>
    intro d
    obtain ⟨f, hf⟩ := h0 d
    exact ⟨f, fun i hi => absurd hi (Nat.not_lt_zero _), hf⟩
  | succ n ih => exact good_choice W n (branch W n) ih

theorem branch_stable (W i : Nat) : ∀ m, i < m → branch W m i = branch W (i + 1) i := by
  intro m
  induction m with
  | zero => intro hm; exact absurd hm (Nat.not_lt_zero _)
  | succ m ih =>
    intro hm
    by_cases him : i = m
    · subst him; rfl
    · show extAt (branch W m) m (choiceBit W m (branch W m)) i = _
      unfold extAt
      rw [ite_eq_right him]
      exact ih (by omega)

noncomputable def limitF (W : Nat) : Nat → Bool := fun i => branch W (i + 1) i

/-- **König's lemma for the search tree.** `F_W` is nonempty iff every finite level of the search
tree is nonempty. -/
theorem koenig (W : Nat) :
    (∃ f, ∀ k, W < k → Theta f k = false) ↔ ∀ d, ∃ f, Level W d f := by
  constructor
  · rintro ⟨f, hf⟩ d; exact ⟨f, fun k h1 _ => hf k h1⟩
  · intro h0
    refine ⟨limitF W, fun k hk => ?_⟩
    obtain ⟨f, hpre, hf⟩ := branch_good W h0 k k
    have heq : Theta (limitF W) k = Theta f k := by
      apply Theta_dep
      intro s hs
      rw [hpre s (by omega)]
      exact (branch_stable W s k (by omega)).symm
    rw [heq]
    exact hf k hk (by omega)

/-! ### Counting the constrained starts of bounded width -/

/-- The start `toRow l` satisfies the constraint at every even step `t < l.length`. -/
def ok (l : List Bool) : Prop := ∀ t, t < l.length → t % 2 = 0 → zrow (toRow l) t 1 = true

instance (l : List Bool) : Decidable (ok l) := by unfold ok; infer_instance

/-- `cnt n l`: the number of extensions `e` of length `n` with `ok (l ++ e)`. -/
def cnt : Nat → List Bool → Nat
  | 0, l => if ok l then 1 else 0
  | n + 1, l => cnt n (l ++ [false]) + cnt n (l ++ [true])

theorem toRow_snoc_le (l : List Bool) (b : Bool) (i : Nat) (hi : i ≤ l.length) :
    toRow (l ++ [b]) i = toRow l i := by
  unfold toRow
  by_cases h0 : i = 0
  · rw [ite_eq_left h0, ite_eq_left h0]
  · rw [ite_eq_right h0, ite_eq_right h0, List.getElem?_append_left (by omega)]

theorem toRow_snoc_last (l : List Bool) (b : Bool) : toRow (l ++ [b]) (l.length + 1) = b := by
  unfold toRow
  rw [ite_eq_right (by omega), show l.length + 1 - 1 = l.length by omega,
    List.getElem?_append_right (by omega)]
  simp

theorem ok_snoc (l : List Bool) (b : Bool) :
    ok (l ++ [b]) ↔ ok l ∧ (l.length % 2 = 0 → zrow (toRow (l ++ [b])) l.length 1 = true) := by
  have hagree : ∀ t, t < l.length → zrow (toRow (l ++ [b])) t 1 = zrow (toRow l) t 1 := by
    intro t ht
    exact zrow_light_cone t 1 (fun i _ hi => toRow_snoc_le l b i (by omega))
  have hlen : (l ++ [b]).length = l.length + 1 := by simp
  constructor
  · intro h
    refine ⟨fun t ht he => ?_, fun he => h l.length (by omega) he⟩
    rw [← hagree t ht]; exact h t (by omega) he
  · rintro ⟨h1, h2⟩ t ht he
    by_cases htl : t < l.length
    · rw [hagree t htl]; exact h1 t htl he
    · have : t = l.length := by omega
      subst this; exact h2 he

theorem ok_of_snoc (l : List Bool) (b : Bool) (h : ok (l ++ [b])) : ok l := ((ok_snoc l b).mp h).1

/-- The constraint at step `|l|` flips exactly with the appended cell at depth `|l| + 1`. -/
theorem snoc_pivot (l : List Bool) :
    zrow (toRow (l ++ [true])) l.length 1 = !(zrow (toRow (l ++ [false])) l.length 1) := by
  have key := zrow_aff l.length (toRow (l ++ [true])) (toRow (l ++ [false])) 1 (Nat.le_refl 1)
    (fun i _ hi => by rw [toRow_snoc_le l true i (by omega), toRow_snoc_le l false i (by omega)])
  rw [show 1 + l.length = l.length + 1 by omega, toRow_snoc_last, toRow_snoc_last] at key
  revert key
  generalize zrow (toRow (l ++ [true])) l.length 1 = A
  generalize zrow (toRow (l ++ [false])) l.length 1 = B
  cases A <;> cases B <;> decide

theorem cnt_eq (n : Nat) : ∀ l : List Bool,
    cnt n l = if ok l then 2 ^ ((l.length + n) / 2 - l.length / 2) else 0 := by
  induction n with
  | zero =>
    intro l
    rw [cnt, Nat.add_zero, Nat.sub_self, Nat.pow_zero]
  | succ n ih =>
    intro l
    rw [cnt, ih (l ++ [false]), ih (l ++ [true])]
    have hlen0 : (l ++ [false]).length = l.length + 1 := by simp
    have hlen1 : (l ++ [true]).length = l.length + 1 := by simp
    rw [hlen0, hlen1]
    by_cases hl : ok l
    · rw [ite_eq_left hl]
      by_cases hm : l.length % 2 = 0
      · have e0 := ok_snoc l false
        have e1 := ok_snoc l true
        have hp := snoc_pivot l
        by_cases hb : zrow (toRow (l ++ [false])) l.length 1 = true
        · have h0 : ok (l ++ [false]) := e0.mpr ⟨hl, fun _ => hb⟩
          have h1 : ¬ ok (l ++ [true]) := by
            intro h
            have := (e1.mp h).2 hm
            rw [hp, hb] at this
            exact absurd this (by decide)
          rw [ite_eq_left h0, ite_eq_right h1, Nat.add_zero]
          congr 1; omega
        · have h0 : ¬ ok (l ++ [false]) := by
            intro h; exact hb ((e0.mp h).2 hm)
          have hb' : zrow (toRow (l ++ [false])) l.length 1 = false := by
            revert hb; generalize zrow (toRow (l ++ [false])) l.length 1 = B; cases B <;> decide
          have h1 : ok (l ++ [true]) := by
            refine e1.mpr ⟨hl, fun _ => ?_⟩
            rw [hp, hb']; rfl
          rw [ite_eq_right h0, ite_eq_left h1, Nat.zero_add]
          congr 1; omega
      · have h0 : ok (l ++ [false]) := (ok_snoc l false).mpr ⟨hl, fun h => absurd h hm⟩
        have h1 : ok (l ++ [true]) := (ok_snoc l true).mpr ⟨hl, fun h => absurd h hm⟩
        rw [ite_eq_left h0, ite_eq_left h1, ← Nat.two_mul, ← Nat.pow_succ']
        congr 1; omega
    · rw [ite_eq_right hl]
      have h0 : ¬ ok (l ++ [false]) := fun h => hl (ok_of_snoc l false h)
      have h1 : ¬ ok (l ++ [true]) := fun h => hl (ok_of_snoc l true h)
      rw [ite_eq_right h0, ite_eq_right h1]

/-- **Exactly `2 ^ ⌊W / 2⌋` starts of width `≤ W`** (lists of length `W`) satisfy the constraint
at every even step `t ≤ W - 1`. -/
theorem count_constrained (W : Nat) : cnt W [] = 2 ^ (W / 2) := by
  rw [cnt_eq]
  have h : ok [] := fun t ht => absurd ht (Nat.not_lt_zero _)
  rw [ite_eq_left h]
  show 2 ^ ((0 + W) / 2 - 0 / 2) = 2 ^ (W / 2)
  congr 1; omega

theorem toRow_inj (l l' : List Bool) (hlen : l.length = l'.length) (h : ∀ k, 1 ≤ k → toRow l k = toRow l' k) :
    l = l' := by
  apply List.ext_getElem?
  intro i
  have := h (i + 1) (by omega)
  unfold toRow at this
  rw [ite_eq_right (by omega), ite_eq_right (by omega), show i + 1 - 1 = i by omega] at this
  by_cases hi : i < l.length
  · rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (by omega)] at this ⊢
    simp at this
    rw [this]
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-! ### Jen's argument inside the ZBL -/

/-- **Jen with a clock.** Let the last black cell of the start be at depth `m ≥ 1`. If column `-1`
is `P`-periodic on the time window `[T, T + ℓ]`, then `ℓ + 2 ≤ T + m + 2 P`. -/
theorem jen_clock {L : Nat → Bool} {m : Nat} (hm : 1 ≤ m) (hedge : L m = true)
    (hfin : ∀ k, m < k → L k = false) {T ℓ P : Nat} (hP : 0 < P)
    (hper : ∀ t, T ≤ t → t + P ≤ T + ℓ → zrow L (t + P) 1 = zrow L t 1) :
    ℓ + 2 ≤ T + m + 2 * P := by
  refine Nat.le_of_not_lt fun hL => ?_
  have hE := zrow_edge hm hedge hfin
  have hk : zrow L (T + P) (m + (T + P)) = zrow L T (m + (T + P)) := by
    rw [history_eq_recon L _ (T + P), history_eq_recon L _ T, recon_shift]
    exact recon_local _ T (fun j hj => hper (T + j) (by omega) (by omega))
  have h1 := (hE (T + P)).1
  rw [hk, (hE T).2 _ (by omega)] at h1
  exact absurd h1 (by decide)

/-- **Jen for the ZBL.** Column `-1` of a nonzero finitely supported start is never eventually
periodic. -/
theorem col_not_eventually_periodic {L : Nat → Bool} {m : Nat} (hm : 1 ≤ m) (hedge : L m = true)
    (hfin : ∀ k, m < k → L k = false) : ¬ EventuallyPeriodic (fun t => zrow L t 1) := by
  rintro ⟨T, P, hP, h⟩
  have := jen_clock hm hedge hfin (T := T) (ℓ := T + m + 2 * P) hP (fun t ht _ => h t ht)
  omega

/-- Under the constraint, a `p`-periodic stretch `[s₀, s₀ + ℓ]` of the free bits has
`2 ℓ + 2 ≤ 2 s₀ + m + 4 p` (`m` the depth of the last black cell of the start). -/
theorem free_bits_clock {L : Nat → Bool} {m : Nat} (hm : 1 ≤ m) (hedge : L m = true)
    (hfin : ∀ k, m < k → L k = false) (hX : InX L) {s₀ ℓ p : Nat} (hp : 0 < p)
    (hper : ∀ s, s₀ ≤ s → s + p ≤ s₀ + ℓ → zrow L (2 * (s + p) + 1) 1 = zrow L (2 * s + 1) 1) :
    2 * ℓ + 2 ≤ 2 * s₀ + m + 4 * p := by
  have := jen_clock hm hedge hfin (T := 2 * s₀) (ℓ := 2 * ℓ) (P := 2 * p) (by omega)
    (fun t ht htL => by
      by_cases hev : t % 2 = 0
      · rw [show t = 2 * (t / 2) by omega, show 2 * (t / 2) + 2 * p = 2 * (t / 2 + p) by omega,
          hX, hX]
      · have := hper (t / 2) (by omega) (by omega)
        rw [show t = 2 * (t / 2) + 1 by omega,
          show 2 * (t / 2) + 1 + 2 * p = 2 * (t / 2 + p) + 1 by omega]
        exact this)
  omega

/-- A finitely supported constrained start has free bits that are not eventually periodic. -/
theorem free_not_eventuallyPeriodic {L : Nat → Bool} (hfin : FinSupp L) (hX : InX L) :
    ¬ EventuallyPeriodic (fun s => zrow L (2 * s + 1) 1) := by
  rintro ⟨N, P, hP, hper⟩
  obtain ⟨W, hW⟩ := hfin
  obtain ⟨m, hm, hedge, hz⟩ := last_black (show L 1 = true from hX 0) W hW
  refine col_not_eventually_periodic hm hedge hz ⟨2 * N, 2 * P, by omega, fun t ht => ?_⟩
  obtain ⟨s, rfl | rfl⟩ : ∃ s, t = 2 * s ∨ t = 2 * s + 1 := ⟨t / 2, by omega⟩
  · show zrow L (2 * s + 2 * P) 1 = zrow L (2 * s) 1
    rw [show 2 * s + 2 * P = 2 * (s + P) by omega, hX, hX]
  · show zrow L (2 * s + 1 + 2 * P) 1 = zrow L (2 * s + 1) 1
    rw [show 2 * s + 1 + 2 * P = 2 * (s + P) + 1 by omega]
    exact hper s (by omega)

/-- A finitely supported constrained start has column `-1` not eventually periodic. -/
theorem constrained_col1_aperiodic {L : Nat → Bool} (hfin : FinSupp L) (hX : InX L) :
    ¬ EventuallyPeriodic (fun t => zrow L t 1) := by
  obtain ⟨W, hW⟩ := hfin
  obtain ⟨m, hm, hedge, hz⟩ := last_black (show L 1 = true from hX 0) W hW
  exact col_not_eventually_periodic hm hedge hz

/-! ### Bridge to rule 30 -/

/-- The left half driven by the white column (`Rule30DrivenLeft.L (fun _ => false)`) is the ZBL. -/
theorem L_eq_zrow (s : Int → Bool) : ∀ t k : Nat, 1 ≤ k →
    Rule30DrivenLeft.L (fun _ => false) s t (-(k : Int)) = zrow (fun k => s (-(k : Int))) t k := by
  intro t
  induction t with
  | zero =>
    intro k hk
    rw [Rule30DrivenLeft.L_zero (by omega), zrow_zero_of_pos _ hk]
  | succ t ih =>
    intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [Rule30DrivenLeft.L_succ (by omega), zrow_succ,
      show -((j + 1 : Nat) : Int) - 1 = -((j + 2 : Nat) : Int) by omega,
      ih (j + 2) (by omega), ih (j + 1) (by omega)]
    cases j with
    | zero =>
      rw [show -(((0 + 1 : Nat)) : Int) + 1 = 0 by omega, Rule30DrivenLeft.L_col0, zrow_wall]
      rfl
    | succ i =>
      rw [show -(((i + 1 + 1 : Nat)) : Int) + 1 = -((i + 1 : Nat) : Int) by omega,
        ih (i + 1) (by omega)]
      rfl

/-- The left half of rule 30 at time `T`, as a ZBL start. -/
def leftRow (T : Nat) (k : Nat) : Bool := cell T (-(k : Int))

theorem leftRow_fin (T : Nat) : ∀ k, T < k → leftRow T k = false :=
  fun _ hk => cell_eq_false_of_lt T _ (by omega)

/-- **The left half is a ZBL.** While `c t && c (t + 1)` is white, the left half of rule 30 evolves
as the ZBL (`Rule30DrivenLeft.cell_eq_L_effective`). -/
theorem left_half_is_zbl {T : Nat} (hw : ∀ t, T ≤ t → (center t && center (t + 1)) = false) :
    ∀ t k, 1 ≤ k → zrow (leftRow T) t k = cell (T + t) (-(k : Int)) := by
  have hfun : (fun k => center (T + k) && center (T + k + 1)) = fun _ => false :=
    funext fun k => hw (T + k) (by omega)
  intro t k hk
  have e := Rule30DrivenLeft.cell_eq_L_effective T t (-(k : Int)) (by omega)
  rw [hfun, L_eq_zrow _ t k hk] at e
  exact e

/-- **`Q01` is the staged `Rule30PeriodTwo.Q01`.** -/
theorem Q01_iff_staged : Q01 ↔ Rule30PeriodTwo.Q01 := by
  constructor
  · intro hQ m s hm hs0 _ hc
    refine hQ (fun k => s (-(k : Int))) ⟨m, fun k hk => hs0 _ (by omega)⟩ fun k => ?_
    rw [← L_eq_zrow s (2 * k) 1 (Nat.le_refl 1)]
    exact hc k
  · intro hS L ⟨W, hW⟩ hX
    obtain ⟨m, hm, hedge, hfin⟩ := last_black (show L 1 = true from hX 0) W hW
    let s : Int → Bool := fun p => if p < 0 then L (-p).toNat else false
    have hsL : ∀ k : Nat, 1 ≤ k → s (-(k : Int)) = L k := by
      intro k hk
      show (if -(k : Int) < 0 then L (-(-(k : Int))).toNat else false) = L k
      rw [ite_eq_left (by omega), show (-(-(k : Int))).toNat = k by omega]
    refine hS m s (by omega) (fun p hp => ?_) ?_ fun k => ?_
    · show (if p < 0 then L (-p).toNat else false) = false
      rw [ite_eq_left (by omega)]; exact hfin _ (by omega)
    · rw [hsL m hm]; exact hedge
    · rw [show (-1 : Int) = -((1 : Nat) : Int) by rfl, L_eq_zrow s (2 * k) 1 (Nat.le_refl 1),
        zrow_congr (L' := L) hsL]
      exact hX k

/-- **`Q01` excludes an eventually 2-periodic center column**, for every transient
(`Rule30PeriodTwo.not_eventually_period_two_of_Q01`). -/
theorem no_eventual_period_two (hQ : Q01) : ¬ ∃ T0, ∀ t, T0 ≤ t → center (t + 2) = center t :=
  Rule30PeriodTwo.not_eventually_period_two_of_Q01 (Q01_iff_staged.1 hQ)

/-- At a white center step followed by a black one, columns `-1` and `1` are complementary. -/
theorem left_right_white (t : Nat) (h1 : center t = false) (h2 : center (t + 1) = true) :
    cell t 1 = !cell t (-1) := by
  have e := Rule30MaskedJen.left_of_white t 0 h1
  rw [show (0 : Int) - 1 = -1 by rfl, show (0 : Int) + 1 = 1 by rfl] at e
  unfold center at h2
  rw [e, h2]
  cases cell t 1 <;> rfl

/-- **Jen with a clock under an alternating center.** If the center alternates black-first from
`T`, column `-1` at the white steps `T + 2 k + 1` is not `p`-periodic on a window `[k₀, k₀ + ℓ]`
with `2 ℓ + 2 > 2 k₀ + T + 1 + 4 p`; in particular it is not eventually periodic. -/
theorem alternating_free_bits_clock {T : Nat}
    (hT : ∀ k, cell (T + 2 * k) 0 = true ∧ cell (T + 2 * k + 1) 0 = false)
    {k₀ ℓ p : Nat} (hp : 0 < p)
    (hper : ∀ k, k₀ ≤ k → k + p ≤ k₀ + ℓ →
      cell (T + 2 * (k + p) + 1) (-1) = cell (T + 2 * k + 1) (-1)) :
    2 * ℓ + 2 ≤ 2 * k₀ + (T + 1) + 4 * p := by
  have hw : ∀ t, T ≤ t → (center t && center (t + 1)) = false := by
    intro t ht
    obtain ⟨j, rfl | rfl⟩ : ∃ j, t = T + 2 * j ∨ t = T + 2 * j + 1 := ⟨(t - T) / 2, by omega⟩
    · show (cell (T + 2 * j) 0 && cell (T + 2 * j + 1) 0) = false
      rw [(hT j).2]; cases cell (T + 2 * j) 0 <;> rfl
    · show (cell (T + 2 * j + 1) 0 && cell (T + 2 * j + 1 + 1) 0) = false
      rw [(hT j).2]; rfl
  have hz := left_half_is_zbl hw
  have hedge1 : zrow (leftRow T) 1 (T + 1) = true := by
    rw [hz 1 (T + 1) (by omega)]; exact cell_left_edge (T + 1)
  have hfin1 : ∀ k, T + 1 < k → zrow (leftRow T) 1 k = false := by
    intro k hk
    rw [hz 1 k (by omega)]; exact cell_eq_false_of_lt (T + 1) _ (by omega)
  have hcol : ∀ t, zrow (zrow (leftRow T) 1) t 1 = cell (T + 1 + t) (-1) := by
    intro t
    rw [← zrow_shift, hz (1 + t) 1 (Nat.le_refl 1), show T + (1 + t) = T + 1 + t by omega]
    rfl
  have hb : ∀ k, cell (T + 2 * k) (-1) = true := fun k => Rule30PeriodTwo.m1_even hT k
  have := jen_clock (L := zrow (leftRow T) 1) (m := T + 1) (by omega) hedge1 hfin1
    (T := 2 * k₀) (ℓ := 2 * ℓ) (P := 2 * p) (by omega) (fun t ht htL => by
      rw [hcol, hcol]
      by_cases hev : t % 2 = 0
      · have := hper (t / 2) (by omega) (by omega)
        rw [show T + 1 + (t + 2 * p) = T + 2 * (t / 2 + p) + 1 by omega,
          show T + 1 + t = T + 2 * (t / 2) + 1 by omega]
        exact this
      · rw [show T + 1 + (t + 2 * p) = T + 2 * (t / 2 + p + 1) by omega,
          show T + 1 + t = T + 2 * (t / 2 + 1) by omega, hb, hb])
  omega

/-- **Interface for the right half.** If the center alternates black-first from `T`, column `1`
at the white steps is not `p`-periodic on a window `[k₀, k₀ + ℓ]` with
`2 ℓ + 2 > 2 k₀ + T + 1 + 4 p`. -/
theorem alternating_right_col1_clock {T : Nat}
    (hT : ∀ k, cell (T + 2 * k) 0 = true ∧ cell (T + 2 * k + 1) 0 = false)
    {k₀ ℓ p : Nat} (hp : 0 < p)
    (hper : ∀ k, k₀ ≤ k → k + p ≤ k₀ + ℓ → cell (T + 2 * (k + p) + 1) 1 = cell (T + 2 * k + 1) 1) :
    2 * ℓ + 2 ≤ 2 * k₀ + (T + 1) + 4 * p := by
  refine alternating_free_bits_clock hT hp fun k h1 h2 => ?_
  have := hper k h1 h2
  rw [Rule30PeriodTwo.p1_odd hT, Rule30PeriodTwo.p1_odd hT] at this
  revert this
  cases cell (T + 2 * (k + p) + 1) (-1) <;> cases cell (T + 2 * k + 1) (-1) <;> simp

/-! ### The free bits under period 2: no `00` and no `11111` -/

/-- Column `1` is black at one of the steps `0, 2, 4, 6, 8`. -/
def blackAmongFive (v : List Bool) : Bool :=
  v.getD 0 false || v.getD 2 false || v.getD 4 false || v.getD 6 false || v.getD 8 false

/-- Kernel check: with a white-first alternating center, column `1` is black at one of the steps
`0, 2, 4, 6, 8`, for each of the `2 ^ 11` windows of columns `1, …, 11` (the light cone). -/
theorem col1_five_check : (allLists 11).all
    (fun l => blackAmongFive (Rule30PeriodTwo.col1 (Rule30PeriodTwo.alt 9) l)) = true := by
  decide +kernel

/-- **Column `1` under period 2.** If the center alternates black-first from `T`, column `1` is
black at one of any five consecutive white steps. -/
theorem col1_black_among_five {T : Nat}
    (h : ∀ k, cell (T + 2 * k) 0 = true ∧ cell (T + 2 * k + 1) 0 = false) (k : Nat) :
    ∃ i, i < 5 ∧ cell (T + 2 * (k + i) + 1) 1 = true := by
  have hc : ∀ i, i < 9 → center (T + 2 * k + 1 + i) = (i % 2 == 1) := by
    intro i _
    obtain ⟨j, rfl | rfl⟩ : ∃ j, i = 2 * j ∨ i = 2 * j + 1 := ⟨i / 2, by omega⟩
    · show cell (T + 2 * k + 1 + 2 * j) 0 = _
      rw [show T + 2 * k + 1 + 2 * j = T + 2 * (k + j) + 1 by omega, (h (k + j)).2]
      simp [show 2 * j % 2 = 0 by omega]
    · show cell (T + 2 * k + 1 + (2 * j + 1)) 0 = _
      rw [show T + 2 * k + 1 + (2 * j + 1) = T + 2 * (k + j + 1) by omega, (h (k + j + 1)).1]
      simp [show (2 * j + 1) % 2 = 1 by omega]
  have hw := Rule30PeriodTwo.col1_alt (T + 2 * k + 1) 9 hc
  have hmem : Rule30BlackRuns.rowAt (T + 2 * k + 1) 1 (9 + 2) ∈ allLists 11 := by
    have := mem_allLists (Rule30BlackRuns.rowAt (T + 2 * k + 1) 1 (9 + 2))
    rwa [Rule30BlackRuns.length_rowAt] at this
  have hck := List.all_eq_true.1 col1_five_check _ hmem
  rw [hw] at hck
  have hv : ∀ i, i < 9 → ((List.range 9).map (fun i => cell (T + 2 * k + 1 + i) 1)).getD i false =
      cell (T + 2 * k + 1 + i) 1 := by
    intro i hi
    simp [List.getD_eq_getElem?_getD, hi]
  unfold blackAmongFive at hck
  rw [hv 0 (by omega), hv 2 (by omega), hv 4 (by omega), hv 6 (by omega), hv 8 (by omega)] at hck
  simp only [Bool.or_eq_true] at hck
  rcases hck with (((h0 | h2) | h4) | h6) | h8
  · exact ⟨0, by omega, by rw [show T + 2 * (k + 0) + 1 = T + 2 * k + 1 + 0 by omega]; exact h0⟩
  · exact ⟨1, by omega, by rw [show T + 2 * (k + 1) + 1 = T + 2 * k + 1 + 2 by omega]; exact h2⟩
  · exact ⟨2, by omega, by rw [show T + 2 * (k + 2) + 1 = T + 2 * k + 1 + 4 by omega]; exact h4⟩
  · exact ⟨3, by omega, by rw [show T + 2 * (k + 3) + 1 = T + 2 * k + 1 + 6 by omega]; exact h6⟩
  · exact ⟨4, by omega, by rw [show T + 2 * (k + 4) + 1 = T + 2 * k + 1 + 8 by omega]; exact h8⟩

/-- **The free bits under period 2 contain no `00` and no `11111`.** If the center alternates
black-first from `T`, the free bits `cell (T + 2 k + 1) (-1)` never are white twice in a row
(`Rule30PeriodTwo.golden`) and never black five times in a row (`col1_black_among_five`). -/
theorem free_bits_no00_no11111 {T : Nat}
    (h : ∀ k, cell (T + 2 * k) 0 = true ∧ cell (T + 2 * k + 1) 0 = false) (k : Nat) :
    ¬ (cell (T + 2 * k + 1) (-1) = false ∧ cell (T + 2 * (k + 1) + 1) (-1) = false) ∧
    ¬ ∀ i, i < 5 → cell (T + 2 * (k + i) + 1) (-1) = true := by
  refine ⟨fun ⟨h0, h1⟩ => ?_, fun hall => ?_⟩
  · have := Rule30PeriodTwo.golden h k h0
    rw [show T + 2 * k + 3 = T + 2 * (k + 1) + 1 by omega, h1] at this
    exact absurd this (by decide)
  · obtain ⟨i, hi, hb⟩ := col1_black_among_five h k
    rw [Rule30PeriodTwo.p1_odd h (k + i), hall i hi] at hb
    exact absurd hb (by decide)

end Rule30ZeroBoundary
end Ruliology.CellularAutomata
