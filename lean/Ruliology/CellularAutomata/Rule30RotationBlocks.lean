module

public import Ruliology.CellularAutomata.Rule30ClockNearSquares

/-!
# Blocks in the order of an irrational rotation, beside a Rule 30 clock

Turn a circle by a fixed irrational angle and note at each step whether the point is in a fixed arc, starting on the
orbit of either end of the arc. Let each of the two answers stand for a finite block of black and white readings, of
any two lengths, and set the blocks one after the other in the order of the answers. Suppose a row of Rule 30 has a
leftmost black cell and one of its columns eventually reads `0101…`. Then the column to its right, on the white
ticks, does not eventually read such a concatenation. Every irrational angle is covered, every arc, both ends, every
translate along their orbits and every two blocks.

* `arc_long_squares`: for every irrational slope, every second line of that slope and any lengths of the two
  letters, the word of the arc has repeats at unbounded lags, from every start, that are as long as what comes
  before the second place, less a fixed amount, when each letter is counted with its length.
* `blocks_excluded`, `gap_order_excluded`: the exclusion, at any column of a row with a leftmost black cell, for
  blocks and for the gaps between black readings.
* `arc_near_squares`, `arc_excluded`: letters of length one, and sliding block codes of their word.
* `sqrt_line`, `half`, `half_phase`, `silver_blocks_excluded`: the floors of `t √m` for `m` not the square of a
  fraction, the half-circle, and an example: the gaps 3, 5, 5, 5 and 3, 5, 5, 5, 5, 5 in the order of the parities of
  `⌊t √2⌋`.

**What is not new.** The word of the arc itself is excluded without this module, from any start. Beside a column
that alternates two black readings in a row never occur (`Rule30PeriodTwo.golden` for the single cell), and from
sample 35 on black readings come 2, 3, 4 or 5 apart with consecutive gaps among nine pairs, for every right half.
The gaps of one arc are its return times `p`, `q` and `p + q`, and these rules leave only arcs whose ends lie on one
orbit, whose words are block codes of Sturmian words. Blocks of unequal length are not touched by this: the gaps 3
and 5 may follow each other in any order as far as the nine pairs go.

**Not shown.** That a right half reads the word of the example, or of any two blocks that are not powers of one word, for
ever. (Two powers of one word give the same periodic word in every order; the kit's ether reads `1010…`, so it reads
the blocks `10` and `1010` in every order, `Rule30PeriodTwoCoupled`, and those rows have no leftmost black cell.) Finite
computations on a strip of columns with its far edge free show some words impossible for every right half: the
example with one gap 5 fewer in the longer block, at 40 columns.

**No real numbers.** `IrrationalLine g` says that the intervals `[g n / n, (g n + 1) / n]` meet pairwise and that no
rational number lies in all of them. For a real irrational `α`, `g n = ⌊n α⌋` satisfies it, and at positive indices
nothing else does; `g 0` is free. `PhaseLine g f` is a condition on increments: every increment of `f` over `n`
ticks is `g n` or `g n + 1`, as for `f t = ⌊t α + θ⌋` and for `f t = ⌈t α + θ⌉ - 1` with any real `θ`. The arc `[0,
γ)` of the circle of length one contains `t α` exactly when `⌊t α⌋ - ⌊t α - γ⌋ = 1`. `Above g h k` is `h < k α`,
read off one interval.

**Method.** A fraction below `α` and a fraction above it, with determinant one, are Farey neighbours `u / d` and `U
/ D` (`Farey`, in either order). Adding `d` to the time adds `u` to the floor at every time `1 ≤ t < D`
(`Farey.step`), since no lattice vector is nearer the slope before `D` (`bound`). For a second line the same holds
except at failing times, which are at least `D` apart (`Farey.gap`). The mediant replaces one neighbour and keeps
the other (`Farey.mediant`), and neither is kept for ever (`Farey.switch`).

Take a neighbour `u / d` at the last time it is kept, next to `(x + u) / (r + d)` (`Scale`), and write `T n` for the
length of the first `n` blocks. If the second line copies up to `d`, the start repeats. If it first fails at `m <
d`, the letters from `m + 1` repeat up to `r + d`, and this is enough when `T r` is at least `2 T m` less a
constant, which holds when `m + d ≤ r`. If neither holds at two consecutive scales, the second failing time is `m +
d` (`Scale.carry`). If neither holds from some scale on, every later scale has `r' = r + 2 d`, and `T r - 2 T m`
changes by `2 (len c(m + d) - len c(m))`, where `c` takes two values in turn. So it is the same after two scales,
and the repeats fall short by a fixed length.

Then `Rule30ClockNearSquares.corollary_F` applies to the row at a late time.

Beside the kit: `Rule30GapRepetitions` bounds from below how late the order of the gaps 3 and 5 may repeat, by
exponents, and so excludes Sturmian and quasi-Sturmian orders. `Rule30GoldenHalfCircle` has the half-circle words of
one angle. `Rule30ClockNearSquares` has the characteristic Sturmian words.

**Credit.** Farey neighbours and the copying of `⌊t α⌋` up to the next denominator are classical. Interval tests for
the sequences `⌊n α⌋` go back to R. L. Graham, S. Lin and C.-S. Lin, *Spectra of numbers*, Math. Mag. 51 (1978).
That the coding of a rotation by one arc from an end repeats not far from its beginning is in B. Adamczewski, *On
powers of words occurring in binary codings of rotations*, Adv. Appl. Math. 34 (2005).
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30RotationBlocks

/-! ### Integer floors of the multiples of an irrational number -/

/-- The floors of the positive multiples of an irrational number, in integers: the intervals
`[f n / n, (f n + 1) / n]` meet pairwise, and no rational number lies in all of them. -/
structure IrrationalLine (f : Nat → Int) : Prop where
  floors : ∀ m n : Nat, 1 ≤ m → 1 ≤ n → (n : Int) * f m < m * (f n + 1)
  irrational : ∀ (p : Int) (q : Nat), 1 ≤ q →
    ∃ n : Nat, 1 ≤ n ∧ ((n : Int) * p < q * f n ∨ q * (f n + 1) < (n : Int) * p)

/-- `h < k β`, read off one of the intervals. -/
def Above (f : Nat → Int) (h k : Int) : Prop :=
  ∃ n : Nat, 1 ≤ n ∧ (n : Int) * h < k * f n ∧ (n : Int) * h < k * (f n + 1)

variable {f : Nat → Int}

theorem not_above_zero : ¬ Above f 0 0 := by
  rintro ⟨n, _, h, _⟩
  simp at h

theorem floors_refine (hf : IrrationalLine f) (m n : Nat) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (m : Int) * f n ≤ f (m * n) ∧ f (m * n) + 1 ≤ m * (f n + 1) := by
  have hmn : 1 ≤ m * n := Nat.mul_pos hm hn
  have a := hf.floors n (m * n) hn hmn
  have b := hf.floors (m * n) n hmn hn
  have hn0 : (0 : Int) ≤ n := by omega
  rw [Int.natCast_mul] at a b
  have a' : (n : Int) * (m * f n) < n * (f (m * n) + 1) := by grind
  have b' : (n : Int) * f (m * n) < n * (m * (f n + 1)) := by grind
  have := Int.lt_of_mul_lt_mul_left a' hn0
  have := Int.lt_of_mul_lt_mul_left b' hn0
  omega

theorem above_refine (hf : IrrationalLine f) {h k : Int} {n : Nat} (hn : 1 ≤ n) (h₁ : (n : Int) * h < k * f n)
    (h₂ : (n : Int) * h < k * (f n + 1)) (m : Nat) (hm : 1 ≤ m) :
    ((m * n : Nat) : Int) * h < k * f (m * n) ∧ ((m * n : Nat) : Int) * h < k * (f (m * n) + 1) := by
  obtain ⟨lo, hi⟩ := floors_refine hf m n hm hn
  have hm0 : (0 : Int) < m := by omega
  have e₁ := Int.mul_lt_mul_of_pos_left h₁ hm0
  have e₂ := Int.mul_lt_mul_of_pos_left h₂ hm0
  rw [Int.natCast_mul]
  by_cases hk : 0 ≤ k
  · have := Int.mul_le_mul_of_nonneg_left lo hk
    constructor <;> grind
  · have := Int.mul_le_mul_of_nonneg_left hi (show 0 ≤ -k by omega)
    constructor <;> grind

theorem above_add (hf : IrrationalLine f) {h k h' k' : Int} (a : Above f h k) (b : Above f h' k') :
    Above f (h + h') (k + k') := by
  obtain ⟨n, hn, a₁, a₂⟩ := a
  obtain ⟨m, hm, b₁, b₂⟩ := b
  have A := above_refine hf hn a₁ a₂ m hm
  have B := above_refine hf hm b₁ b₂ n hn
  rw [Nat.mul_comm n m] at B
  exact ⟨m * n, Nat.mul_pos hm hn, by grind, by grind⟩

theorem above_smul {u d : Int} (a : Above f u d) {c : Int} (hc : 1 ≤ c) : Above f (c * u) (c * d) := by
  obtain ⟨n, hn, h₁, h₂⟩ := a
  have e₁ := Int.mul_lt_mul_of_pos_left h₁ (show 0 < c by omega)
  have e₂ := Int.mul_lt_mul_of_pos_left h₂ (show 0 < c by omega)
  exact ⟨n, hn, by grind, by grind⟩

theorem above_add_smul (hf : IrrationalLine f) {h k u d : Int} (a : Above f h k) (b : Above f u d) {c : Int}
    (hc : 0 ≤ c) : Above f (h + c * u) (k + c * d) := by
  by_cases h0 : c = 0
  · subst h0; simpa using a
  · exact above_add hf a (above_smul b (by omega))

theorem above_total (hf : IrrationalLine f) (h : Int) (k : Nat) (hk : 1 ≤ k) :
    Above f h k ∨ Above f (-h) (-(k : Int)) := by
  obtain ⟨n, hn, a | a⟩ := hf.irrational h k hk
  · exact Or.inl ⟨n, hn, a, by grind⟩
  · exact Or.inr ⟨n, hn, by grind, by grind⟩

theorem above_absurd (hf : IrrationalLine f) {h k : Int} (a : Above f h k) (b : Above f (-h) (-k)) : False := by
  have c := above_add hf a b
  rw [Int.add_right_neg, Int.add_right_neg] at c
  exact not_above_zero c

theorem le_floor (hf : IrrationalLine f) {h : Int} {t : Nat} (ht : 1 ≤ t) (a : Above f h t) : h ≤ f t := by
  obtain ⟨n, hn, h₁, _⟩ := a
  have b := hf.floors n t hn ht
  have := Int.lt_of_mul_lt_mul_left (show (n : Int) * h < n * (f t + 1) by omega) (by omega)
  omega

theorem floor_lt (hf : IrrationalLine f) {h : Int} {t : Nat} (ht : 1 ≤ t) (a : Above f (-h) (-(t : Int))) :
    f t < h := by
  obtain ⟨n, hn, _, h₂⟩ := a
  have b := hf.floors t n ht hn
  exact Int.lt_of_mul_lt_mul_left (show (n : Int) * f t < n * h by grind) (by omega)

theorem floor_above (hf : IrrationalLine f) {t : Nat} (ht : 1 ≤ t) : Above f (f t) t := by
  rcases above_total hf (f t) t ht with a | a
  · exact a
  · have := floor_lt hf ht a; omega

theorem floor_below (hf : IrrationalLine f) {t : Nat} (ht : 1 ≤ t) : Above f (-(f t + 1)) (-(t : Int)) := by
  rcases above_total hf (f t + 1) t ht with a | a
  · have := le_floor hf ht a; omega
  · exact a

/-- A positive amount outgrows every other. -/
theorem above_arch {a b : Int} (hab : Above f a b) (h k : Int) : ∃ c : Nat, Above f (h + c * a) (k + c * b) := by
  obtain ⟨n, hn, h₁, h₂⟩ := hab
  refine ⟨((n : Int) * h - k * f n).natAbs + ((n : Int) * h - k * (f n + 1)).natAbs + 1, n, hn, ?_, ?_⟩
  · have e : (((n : Int) * h - k * f n).natAbs : Int) ≥ (n : Int) * h - k * f n := by omega
    generalize hc : ((((n : Int) * h - k * f n).natAbs + ((n : Int) * h - k * (f n + 1)).natAbs + 1 : Nat) : Int) = c
    have hc' : (n : Int) * h - k * f n < c := by omega
    have hc0 : 0 ≤ c := by omega
    have := Int.mul_le_mul_of_nonneg_left (show 1 ≤ b * f n - n * a by omega) hc0
    grind
  · generalize hc : ((((n : Int) * h - k * f n).natAbs + ((n : Int) * h - k * (f n + 1)).natAbs + 1 : Nat) : Int) = c
    have hc' : (n : Int) * h - k * (f n + 1) < c := by omega
    have hc0 : 0 ≤ c := by omega
    have := Int.mul_le_mul_of_nonneg_left (show 1 ≤ b * (f n + 1) - n * a by omega) hc0
    grind

/-! ### Farey neighbours -/

/-- `u / d` and `U / D` are Farey neighbours, one on each side of the slope. -/
def Farey (f : Nat → Int) (u : Int) (d : Nat) (U : Int) (D : Nat) : Prop :=
  1 ≤ d ∧ 1 ≤ D ∧
    ((Above f u d ∧ Above f (-U) (-(D : Int)) ∧ U * d - u * D = 1) ∨
      (Above f (-u) (-(d : Int)) ∧ Above f U D ∧ u * D - U * d = 1))

theorem Farey.symm {u U : Int} {d D : Nat} (h : Farey f u d U D) : Farey f U D u d := by
  obtain ⟨a, b, ⟨c, e, g⟩ | ⟨c, e, g⟩⟩ := h
  · exact ⟨b, a, Or.inr ⟨e, c, g⟩⟩
  · exact ⟨b, a, Or.inl ⟨e, c, g⟩⟩

/-- The mediant replaces one of the two neighbours. -/
theorem Farey.mediant (hf : IrrationalLine f) {u U : Int} {d D : Nat} (h : Farey f u d U D) :
    Farey f u d (u + U) (d + D) ∨ Farey f (u + U) (d + D) U D := by
  obtain ⟨a, b, hh⟩ := h
  rcases above_total hf (u + U) (d + D) (by omega) with m | m <;> rcases hh with ⟨c, e, g⟩ | ⟨c, e, g⟩
  · exact Or.inr ⟨by omega, b, Or.inl ⟨m, e, by grind⟩⟩
  · exact Or.inl ⟨a, by omega, Or.inr ⟨c, m, by grind⟩⟩
  · exact Or.inl ⟨a, by omega, Or.inl ⟨c, m, by grind⟩⟩
  · exact Or.inr ⟨by omega, b, Or.inr ⟨m, e, by grind⟩⟩

/-- The basis argument: before the other denominator, every lattice vector is at least as far from the slope as
`u / d`. -/
theorem bound (hf : IrrationalLine f) {u U h t : Int} {d D : Int} (hd : 1 ≤ d) (hD : 1 ≤ D)
    (c : Above f u d) (e : Above f (-U) (-D)) (g : U * d - u * D = 1) (ht : 1 ≤ t) (htD : t < D)
    (lo : Above f (u - h) (d - t)) (hi : Above f (h + u) (t + d)) : False := by
  generalize ha : t * U - h * D = a
  generalize hb : h * d - t * u = b
  have eh : h = a * u + b * U := by subst ha hb; grind
  have et : t = a * d + b * D := by subst ha hb; grind
  by_cases h1 : 1 ≤ b
  · have a0 : a + 1 ≤ 0 := by
      have := Int.mul_le_mul_of_nonneg_right h1 (show 0 ≤ D by omega)
      by_cases hn : 0 ≤ a
      · have := Int.mul_nonneg hn (show 0 ≤ d by omega)
        omega
      · omega
    have s := above_add_smul hf (above_add_smul hf hi c (show 0 ≤ -(a + 1) by omega)) e (show 0 ≤ b by omega)
    rw [show h + u + -(a + 1) * u + b * -U = 0 by grind, show t + d + -(a + 1) * d + b * -D = 0 by grind] at s
    exact not_above_zero s
  · have a0 : 0 ≤ a - 1 := by
      have := Int.mul_nonneg (show 0 ≤ -b by omega) (show 0 ≤ D by omega)
      by_cases hn : 1 ≤ a
      · omega
      · have := Int.mul_nonneg (show 0 ≤ -a by omega) (show 0 ≤ d by omega)
        grind
    have s := above_add_smul hf (above_add_smul hf lo c a0) e (show 0 ≤ -b by omega)
    rw [show u - h + (a - 1) * u + -b * -U = 0 by grind, show d - t + (a - 1) * d + -b * -D = 0 by grind] at s
    exact not_above_zero s

theorem no_crossing (hf : IrrationalLine f) {u U h t : Int} {d D : Int} (hd : 1 ≤ d) (hD : 1 ≤ D)
    (c : Above f u d) (e : Above f (-U) (-D)) (g : U * d - u * D = 1) (ht : 1 ≤ t) (htD : t < D)
    (lo : Above f (-h) (-t)) (hi : Above f (h + u) (t + d)) : False :=
  bound hf hd hD c e g ht htD (by simpa only [Int.sub_eq_add_neg] using above_add hf c lo) hi

/-- The floors of the multiples of the opposite number. -/
theorem IrrationalLine.reflect (hf : IrrationalLine f) : IrrationalLine (fun n => -f n - 1) where
  floors := fun m n hm hn => by have := hf.floors n m hn hm; grind
  irrational := fun p q hq => by
    obtain ⟨n, hn, h | h⟩ := hf.irrational (-p) q hq
    · exact ⟨n, hn, Or.inr (by grind)⟩
    · exact ⟨n, hn, Or.inl (by grind)⟩

theorem above_reflect (f : Nat → Int) (h k : Int) : Above (fun n => -f n - 1) h k ↔ Above f h (-k) := by
  constructor <;> rintro ⟨n, hn, h₁, h₂⟩ <;> exact ⟨n, hn, by grind, by grind⟩

/-- **The step.** Moving by one Farey denominator adds its numerator to the floor, at every positive time before the
other denominator. -/
theorem Farey.step (hf : IrrationalLine f) {u U : Int} {d D : Nat} (h : Farey f u d U D) (t : Nat) (ht : 1 ≤ t)
    (htD : t < D) : f (t + d) = f t + u := by
  obtain ⟨hd, hD, ⟨c, e, g⟩ | ⟨c, e, g⟩⟩ := h
  · have lower := le_floor hf (h := f t + u) (t := t + d) (by omega) (by
      rw [Int.natCast_add]; exact above_add hf (floor_above hf ht) c)
    have upper : f (t + d) < f t + u + 1 := by
      rcases above_total hf (f t + u + 1) (t + d) (by omega) with a | a
      · refine (no_crossing hf (u := u) (U := U) (h := f t + 1) (t := t) (d := d) (D := D) (by omega) (by omega) c e g
          (by omega) (by omega) (floor_below hf ht) ?_).elim
        rw [show f t + 1 + u = f t + u + 1 by omega, ← Int.natCast_add]; exact a
      · exact floor_lt hf (by omega) a
    omega
  · have upper := floor_lt hf (h := f t + 1 + u) (t := t + d) (by omega) (by
      have := above_add hf (floor_below hf ht) c
      rw [show -(f t + 1 + u) = -(f t + 1) + -u by omega,
        show -((t + d : Nat) : Int) = -(t : Int) + -(d : Int) by omega]
      exact this)
    have lower : f t + u ≤ f (t + d) := by
      rcases above_total hf (f t + u) (t + d) (by omega) with a | a
      · exact le_floor hf (by omega) a
      · refine (no_crossing hf.reflect (u := -u) (U := -U) (h := -f t) (t := t) (d := d) (D := D) (by omega) (by omega)
          ?_ ?_ (by grind) (by omega) (by omega) ?_ ?_).elim
        · rw [above_reflect]; exact c
        · rw [above_reflect, Int.neg_neg, Int.neg_neg]; exact e
        · rw [above_reflect, Int.neg_neg, Int.neg_neg]; exact floor_above hf ht
        · rw [above_reflect, show -f t + -u = -(f t + u) by omega,
            show -((t : Int) + d) = -((t + d : Nat) : Int) by omega]
          exact a
    omega

/-- A neighbour is not kept for ever. -/
theorem Farey.switch (hf : IrrationalLine f) {u U : Int} {d D : Nat} (h : Farey f u d U D) :
    ∃ n : Nat, Farey f (u + n * U) (d + n * D) (u + (n + 1) * U) (d + (n + 1) * D) := by
  refine Classical.byContradiction fun no => ?_
  have keep : ∀ n : Nat, Farey f (u + n * U) (d + n * D) U D := by
    intro n
    induction n with
    | zero => simpa using h
    | succ n ih =>
      rcases ih.mediant hf with m | m
      · refine (no ⟨n, ?_⟩).elim
        rw [show u + ((n : Int) + 1) * U = u + n * U + U by grind, show d + (n + 1) * D = d + n * D + D by grind]
        exact m
      · rw [show u + ((n + 1 : Nat) : Int) * U = u + n * U + U by grind, show d + (n + 1) * D = d + n * D + D by grind]
        exact m
  obtain ⟨_, _, ⟨c, e, g⟩ | ⟨c, e, g⟩⟩ := h
  · obtain ⟨n, a⟩ := above_arch e (-u) (-(d : Int))
    obtain ⟨_, _, ⟨c', _, _⟩ | ⟨_, e', _⟩⟩ := keep n
    · refine above_absurd hf c' ?_
      rw [show -(u + (n : Int) * U) = -u + n * -U by grind,
        show -((d + n * D : Nat) : Int) = -(d : Int) + n * -(D : Int) by grind]
      exact a
    · exact above_absurd hf e' e
  · obtain ⟨n, a⟩ := above_arch e u d
    obtain ⟨_, _, ⟨_, e', _⟩ | ⟨c', _, _⟩⟩ := keep n
    · exact above_absurd hf e e'
    · refine above_absurd hf (h := u + n * U) (k := d + n * D) a ?_
      rw [show -((d : Int) + n * D) = -((d + n * D : Nat) : Int) by grind]
      exact c'

/-- Farey neighbours with large denominators on both sides. -/
theorem exists_farey (hf : IrrationalLine f) (M : Nat) :
    ∃ (u : Int) (d : Nat) (U : Int) (D : Nat), M ≤ d ∧ M ≤ D ∧ Farey f u d U D := by
  induction M with
  | zero =>
    refine ⟨f 1, 1, f 1 + 1, 1, by omega, by omega, by omega, by omega, Or.inl ⟨?_, ?_, by omega⟩⟩
    · exact floor_above hf (t := 1) (by omega)
    · exact floor_below hf (t := 1) (by omega)
  | succ M ih =>
    obtain ⟨u, d, U, D, hd, hD, h⟩ := ih
    obtain ⟨n, h₁⟩ := h.switch hf
    obtain ⟨m, h₂⟩ := h₁.symm.switch hf
    have p₁ := h.1
    have p₂ := h.2.1
    have e₁ : d + D ≤ d + (n + 1) * D := by
      have := Nat.mul_le_mul_right D (show 1 ≤ n + 1 by omega); omega
    refine ⟨_, _, _, _, ?_, ?_, h₂⟩
    · exact Nat.le_trans (by omega) (Nat.le_add_right _ _)
    · exact Nat.le_trans (by omega) (Nat.le_add_right _ _)

/-! ### A second line of the same slope -/

/-- Every increment of `f` over `n` ticks is `g n` or `g n + 1`, as for the floors of a line of the slope of `g` with
any phase. -/
def PhaseLine (g f : Nat → Int) : Prop :=
  ∀ t n : Nat, 1 ≤ n → f t + g n ≤ f (t + n) ∧ f (t + n) ≤ f t + g n + 1

variable {g : Nat → Int}

theorem PhaseLine.reflect (hf : PhaseLine g f) : PhaseLine (fun n => -g n - 1) (fun n => -f n - 1) := by
  intro t n hn
  have := hf t n hn
  constructor <;> dsimp only <;> omega

/-- Two lattice points on the two sides of the line, in the order of the slope. -/
theorem PhaseLine.sep (hg : IrrationalLine g) (hf : PhaseLine g f) {t s : Nat} {h k : Int} (ht : h ≤ f t)
    (hs : f s < k) : Above g (h - k) ((t : Int) - s) := by
  rcases Nat.lt_trichotomy t s with lt | rfl | gt
  · obtain ⟨n, rfl⟩ : ∃ n, s = t + n := ⟨s - t, by omega⟩
    have hn : 1 ≤ n := by omega
    rcases above_total hg (k - h) n hn with a | a
    · have := le_floor hg hn a
      have := hf t n hn
      omega
    · rw [show h - k = -(k - h) by omega, show (t : Int) - ((t + n : Nat) : Int) = -(n : Int) by omega]
      exact a
  · exact ⟨1, by omega, by omega, by omega⟩
  · obtain ⟨n, rfl⟩ : ∃ n, t = s + n := ⟨t - s, by omega⟩
    have hn : 1 ≤ n := by omega
    rcases above_total hg (h - k) n hn with a | a
    · rw [show ((s + n : Nat) : Int) - (s : Int) = (n : Int) by omega]
      exact a
    · have := floor_lt hg hn a
      have := hf s n hn
      omega

theorem Farey.reflect {u U : Int} {d D : Nat} (h : Farey g u d U D) : Farey (fun n => -g n - 1) (-u) d (-U) D := by
  obtain ⟨a, b, ⟨c, e, i⟩ | ⟨c, e, i⟩⟩ := h
  · refine ⟨a, b, Or.inr ⟨?_, ?_, by grind⟩⟩
    · rw [above_reflect, Int.neg_neg, Int.neg_neg]; exact c
    · rw [above_reflect]; exact e
  · refine ⟨a, b, Or.inl ⟨?_, ?_, by grind⟩⟩
    · rw [above_reflect]; exact c
    · rw [above_reflect, Int.neg_neg, Int.neg_neg]; exact e

private theorem gap_lower (hg : IrrationalLine g) (hf : PhaseLine g f) {u U : Int} {d D : Nat} (hd : 1 ≤ d)
    (hD : 1 ≤ D) (c : Above g u d) (e : Above g (-U) (-(D : Int))) (i : U * d - u * D = 1) {t s : Nat}
    (ht : f (t + d) ≠ f t + u) (hs : f (s + d) ≠ f s + u) (lt : t < s) : t + D ≤ s := by
  have up (t : Nat) (ht : f (t + d) ≠ f t + u) : f t + 1 + u ≤ f (t + d) := by
    have := le_floor hg hd c
    have := hf t d hd
    omega
  refine Classical.byContradiction fun no => ?_
  have a₁ := hf.sep hg (up s hs) (show f t < f t + 1 by omega)
  have a₂ := hf.sep hg (up t ht) (show f s < f s + 1 by omega)
  refine bound hg (u := u) (U := U) (h := f s - f t) (t := (s : Int) - t) (d := d) (D := D) (by omega) (by omega) c e i
    (by omega) (by omega) ?_ ?_
  · rw [show u - (f s - f t) = f t + 1 + u - (f s + 1) by omega,
      show (d : Int) - ((s : Int) - t) = ((t + d : Nat) : Int) - s by omega]
    exact a₂
  · rw [show f s - f t + u = f s + 1 + u - (f t + 1) by omega,
      show (s : Int) - t + d = ((s + d : Nat) : Int) - t by omega]
    exact a₁

/-- Times at which the second line fails to copy are far apart. -/
theorem Farey.gap (hg : IrrationalLine g) (hf : PhaseLine g f) {u U : Int} {d D : Nat} (h : Farey g u d U D)
    {t s : Nat} (ht : f (t + d) ≠ f t + u) (hs : f (s + d) ≠ f s + u) (lt : t < s) : t + D ≤ s := by
  obtain ⟨hd, hD, ⟨c, e, i⟩ | ⟨c, e, i⟩⟩ := h
  · exact gap_lower hg hf hd hD c e i ht hs lt
  · refine gap_lower hg.reflect hf.reflect (u := -u) (U := -U) hd hD ?_ ?_ (by grind) (by omega) (by omega) lt
    · rw [above_reflect]; exact c
    · rw [above_reflect, Int.neg_neg, Int.neg_neg]; exact e

/-! ### Scales -/

/-- A neighbour `u / d` kept for the last time: the other neighbour has just become `(x + u) / (r + d)`, and that one is
kept next. -/
def Scale (g : Nat → Int) (x : Int) (r : Nat) (u : Int) (d : Nat) : Prop :=
  Farey g x r u d ∧ Farey g u d (x + u) (r + d) ∧ Farey g (u + (x + u)) (d + (r + d)) (x + u) (r + d)

private theorem carry_lower (hg : IrrationalLine g) (hf : PhaseLine g f) {x u : Int} {r d : Nat} (h : Scale g x r u d)
    (c : Above g u d) {m t : Nat} (hm : 1 ≤ m) (hmd : m < d) (bm : f (m + d) ≠ f m + u) (ht : 1 ≤ t) (htD : t < r + d)
    (bt : f (t + (r + d)) ≠ f t + (x + u)) : t = m + d := by
  obtain ⟨h₀, h₁, h₂⟩ := h
  -- the orientation
  obtain ⟨hr, hd, ⟨_, c', _⟩ | ⟨cx, _, i₀⟩⟩ := h₀
  · exact (above_absurd hg c c').elim
  have i₀' : x * d - u * r = 1 := i₀
  obtain ⟨_, _, ⟨_, e, i₁⟩ | ⟨c', _, _⟩⟩ := h₁
  case inr.inr => exact (above_absurd hg c c').elim
  have m₂ : Above g (u + (x + u)) ((d + (r + d) : Nat) : Int) := by
    obtain ⟨_, _, ⟨a, _, _⟩ | ⟨_, a, _⟩⟩ := h₂
    · exact a
    · exact (above_absurd hg a e).elim
  have bt' : f (t + (r + d)) < f t + (x + u) := by
    have := floor_lt hg (t := r + d) (by omega) e
    have := hf t (r + d) (by omega)
    omega
  rcases Nat.lt_or_ge d t with gt | le
  · -- one denominator back it fails too, and there is only one such time
    obtain ⟨s, rfl⟩ : ∃ s, t = s + d := ⟨t - d, by omega⟩
    have bs : f (s + d) ≠ f s + u := by
      intro eq
      have a := hf.sep hg (show f s ≤ f s by omega) bt'
      refine above_absurd hg m₂ ?_
      rw [show -(u + (x + u)) = f s - (f (s + d) + (x + u)) by omega,
        show -((d + (r + d) : Nat) : Int) = (s : Int) - ((s + d + (r + d) : Nat) : Int) by omega]
      exact a
    have F : Farey g u d (x + u) (r + d) := ⟨by omega, by omega, Or.inl ⟨c, e, i₁⟩⟩
    rcases Nat.lt_trichotomy m s with lt | eq | gt'
    · have := F.gap hg hf bm bs lt; omega
    · omega
    · have := F.gap hg hf bs bm gt'; omega
  · -- too early: a lattice vector that is too short
    exfalso
    have up : f m + 1 + u ≤ f (m + d) := by
      have := le_floor hg hd c
      have := hf m d hd
      omega
    have s₁ := hf.sep hg (show f t ≤ f t by omega) (show f m < f m + 1 by omega)
    have s₂ := hf.sep hg up bt'
    have cx' : Above g (-x) (-(r : Int)) := cx
    rcases Nat.lt_trichotomy m t with lt | rfl | gt
    · refine bound hg.reflect (u := -x) (U := -u) (h := -(f t - (f m + 1))) (t := (t : Int) - m) (d := r) (D := d)
        (by omega) (by omega) ?_ ?_ (by grind) (by omega) (by omega) ?_ ?_
      · rw [above_reflect]; exact cx'
      · rw [above_reflect, Int.neg_neg, Int.neg_neg]; exact c
      · rw [above_reflect]
        have := above_add hg s₁ cx'
        rw [show -x - -(f t - (f m + 1)) = f t - (f m + 1) + -x by omega,
          show -((r : Int) - ((t : Int) - m)) = (t : Int) - m + -(r : Int) by omega]
        exact this
      · rw [above_reflect, show -(f t - (f m + 1)) + -x = f m + 1 + u - (f t + (x + u)) by omega,
          show -((t : Int) - m + r) = ((m + d : Nat) : Int) - ((t + (r + d) : Nat) : Int) by omega]
        exact s₂
    · have s₃ := above_add_smul hg (above_add_smul hg s₂ c (show (0 : Int) ≤ r by omega)) cx'
        (show (0 : Int) ≤ (d : Int) - 1 by omega)
      rw [show f m + 1 + u - (f m + (x + u)) + (r : Int) * u + ((d : Int) - 1) * -x = 0 by grind,
        show ((m + d : Nat) : Int) - ((m + (r + d) : Nat) : Int) + (r : Int) * d + ((d : Int) - 1) * -(r : Int) = 0 by
          grind] at s₃
      exact not_above_zero s₃
    · refine bound hg.reflect (u := -x) (U := -u) (h := f t - (f m + 1)) (t := (m : Int) - t) (d := r) (D := d)
        (by omega) (by omega) ?_ ?_ (by grind) (by omega) (by omega) ?_ ?_
      · rw [above_reflect]; exact cx'
      · rw [above_reflect, Int.neg_neg, Int.neg_neg]; exact c
      · rw [above_reflect, show -x - (f t - (f m + 1)) = f m + 1 + u - (f t + (x + u)) by omega,
          show -((r : Int) - ((m : Int) - t)) = ((m + d : Nat) : Int) - ((t + (r + d) : Nat) : Int) by omega]
        exact s₂
      · rw [above_reflect]
        have := above_add hg s₁ cx'
        rw [show f t - (f m + 1) + -x = f t - (f m + 1) + -x by omega,
          show -((m : Int) - t + r) = (t : Int) - m + -(r : Int) by omega]
        exact this

/-- **The carry.** If the second line fails to copy once before `d` at lag `d`, and once before `r + d` at lag `r + d`,
then the second time is the first plus `d`. -/
theorem Scale.carry (hg : IrrationalLine g) (hf : PhaseLine g f) {x u : Int} {r d : Nat} (h : Scale g x r u d)
    {m t : Nat} (hm : 1 ≤ m) (hmd : m < d) (bm : f (m + d) ≠ f m + u) (ht : 1 ≤ t) (htD : t < r + d)
    (bt : f (t + (r + d)) ≠ f t + (x + u)) : t = m + d := by
  rcases above_total hg u d (by omega) with c | c
  · exact carry_lower hg hf h c hm hmd bm ht htD bt
  · refine carry_lower hg.reflect hf.reflect (x := -x) (u := -u) (r := r) ?_ ?_ hm hmd (by omega) ht htD (by omega)
    · obtain ⟨h₀, h₁, h₂⟩ := h
      refine ⟨h₀.reflect, ?_, ?_⟩
      · have := h₁.reflect; rwa [Int.neg_add] at this
      · have := h₂.reflect; rwa [Int.neg_add, Int.neg_add] at this
    · rw [above_reflect]; exact c

/-- The mediant is on one side only. -/
theorem Farey.not_both (hg : IrrationalLine g) {u U : Int} {d D : Nat} (h : Farey g u d (u + U) (d + D))
    (h' : Farey g (u + U) (d + D) U D) : False := by
  obtain ⟨_, _, ⟨_, a, i⟩ | ⟨_, a, i⟩⟩ := h <;> obtain ⟨_, _, ⟨b, _, j⟩ | ⟨b, _, j⟩⟩ := h'
  · exact above_absurd hg b a
  · grind
  · grind
  · exact above_absurd hg a b

/-- How long a neighbour is kept. -/
theorem Farey.kept (hg : IrrationalLine g) {u U : Int} {d D : Nat} (h : Farey g u d U D) :
    ∃ n : Nat, (∀ i : Nat, i ≤ n → Farey g (u + i * U) (d + i * D) U D) ∧
      Farey g (u + n * U) (d + n * D) (u + (n + 1) * U) (d + (n + 1) * D) := by
  obtain ⟨n, hn⟩ := h.switch hg
  -- the least such `n`
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases ex : ∃ k, k < n ∧ Farey g (u + k * U) (d + k * D) (u + (k + 1) * U) (d + (k + 1) * D)
    · obtain ⟨k, hk, hF⟩ := ex
      exact ih k hk hF
    · refine ⟨n, fun i => ?_, hn⟩
      induction i with
      | zero => intro _; simpa using h
      | succ i ihi =>
        intro hi
        rcases (ihi (by omega)).mediant hg with m | m
        · refine (ex ⟨i, by omega, ?_⟩).elim
          rw [show u + ((i : Int) + 1) * U = u + i * U + U by grind, show d + (i + 1) * D = d + i * D + D by grind]
          exact m
        · rw [show u + ((i + 1 : Nat) : Int) * U = u + i * U + U by grind,
            show d + (i + 1) * D = d + i * D + D by grind]
          exact m

theorem scale_of_kept (hg : IrrationalLine g) {u U : Int} {d D : Nat} (h : Farey g u d U D)
    (h' : Farey g (u + U) (d + D) U D) : ∃ k : Nat, Scale g (u + k * U) (d + k * D) U D := by
  obtain ⟨n, keep, last⟩ := h.kept hg
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine (Farey.not_both hg (u := u) (U := U) (d := d) (D := D) ?_ h').elim
    simpa using last
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    refine ⟨k, keep k (by omega), ?_, ?_⟩
    · have := (keep (k + 1) (by omega)).symm
      rw [show u + ((k + 1 : Nat) : Int) * U = u + k * U + U by grind,
        show d + (k + 1) * D = d + k * D + D by grind] at this
      exact this
    · have := last.symm
      rw [show u + ((k + 1 : Nat) : Int) * U = u + k * U + U by grind, show d + (k + 1) * D = d + k * D + D by grind,
        show u + (((k + 1 : Nat) : Int) + 1) * U = U + (u + k * U + U) by grind,
        show d + (k + 1 + 1) * D = D + (d + k * D + D) by grind] at this
      exact this

theorem Scale.next (hg : IrrationalLine g) {x u : Int} {r d : Nat} (h : Scale g x r u d) :
    ∃ k : Nat, Scale g (u + k * (x + u)) (d + k * (r + d)) (x + u) (r + d) :=
  scale_of_kept hg h.2.1 h.2.2

theorem exists_scale (hg : IrrationalLine g) (M : Nat) :
    ∃ (x : Int) (r : Nat) (u : Int) (d : Nat), M ≤ d ∧ Scale g x r u d := by
  obtain ⟨u, d, U, D, hd, hD, h⟩ := exists_farey hg M
  rcases h.mediant hg with m | m
  · have m' := m.symm
    rw [Int.add_comm u U, Nat.add_comm d D] at m'
    obtain ⟨k, hk⟩ := scale_of_kept hg h.symm m'
    exact ⟨_, _, _, _, hd, hk⟩
  · obtain ⟨k, hk⟩ := scale_of_kept hg h m
    exact ⟨_, _, _, _, hD, hk⟩

/-- Scales with both denominators as large as wanted. -/
theorem exists_scale_large (hg : IrrationalLine g) (M : Nat) :
    ∃ (x : Int) (r : Nat) (u : Int) (d : Nat), M ≤ r ∧ M ≤ d ∧ Scale g x r u d := by
  obtain ⟨u, d, U, D, hd, hD, h⟩ := exists_farey hg M
  rcases h.mediant hg with m | m
  · have m' := m.symm
    rw [Int.add_comm u U, Nat.add_comm d D] at m'
    obtain ⟨k, hk⟩ := scale_of_kept hg h.symm m'
    exact ⟨_, _, _, _, Nat.le_trans hD (Nat.le_add_right _ _), hd, hk⟩
  · obtain ⟨k, hk⟩ := scale_of_kept hg h m
    exact ⟨_, _, _, _, Nat.le_trans hd (Nat.le_add_right _ _), hD, hk⟩

/-! ### Sums of lengths -/

/-- The sum of the first `n` terms. -/
def total (w : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => total w n + w n

theorem total_succ (w : Nat → Nat) (n : Nat) : total w (n + 1) = total w n + w n := rfl

theorem total_add_le (w : Nat → Nat) (a n : Nat) : total w a ≤ total w (a + n) := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih => rw [← Nat.add_assoc, total_succ]; omega

theorem total_mono (w : Nat → Nat) {a b : Nat} (h : a ≤ b) : total w a ≤ total w b := by
  have := total_add_le w a (b - a)
  rwa [show a + (b - a) = b by omega] at this

theorem total_shift (w : Nat → Nat) (a b n : Nat) (h : ∀ s, s < n → w (a + s) = w (b + s)) :
    total w (a + n) + total w b = total w (b + n) + total w a := by
  induction n with
  | zero => rw [Nat.add_zero, Nat.add_zero]; omega
  | succ n ih =>
    have := ih (fun s hs => h s (by omega))
    have := h n (by omega)
    rw [← Nat.add_assoc, ← Nat.add_assoc, total_succ, total_succ]
    omega

theorem total_le (w : Nat → Nat) {M : Nat} (hM : ∀ n, w n ≤ M) (a n : Nat) : total w (a + n) ≤ total w a + M * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have := hM (a + n)
    rw [← Nat.add_assoc, total_succ, Nat.mul_succ]
    omega

theorem le_total (w : Nat → Nat) (h : ∀ n, 1 ≤ w n) (a n : Nat) : total w a + n ≤ total w (a + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have := h (a + n)
    show total w a + (n + 1) ≤ total w (a + n) + w (a + n)
    omega

/-! ### Repeats measured in lengths -/

/-- The letters from `i` agree with those from `j` for `l` letters, with `i ≥ H` and `j ≥ i + N`. When each letter `v`
has length `len v`, the `l` letters from `i` are as long as the first `j` letters, less `K`. -/
def LongSquare (c : Nat → Int) (len : Int → Nat) (H K N : Nat) : Prop :=
  ∃ i j l : Nat, H ≤ i ∧ i + N ≤ j ∧ (∀ s, s < l → c (i + s) = c (j + s)) ∧
    total (fun t => len (c t)) j + total (fun t => len (c t)) i ≤ total (fun t => len (c t)) (i + l) + K

/-- The two lines copy together, except at the failing time. -/
theorem Scale.copy (hg : IrrationalLine g) (hf : PhaseLine g f) {x u : Int} {r d m t : Nat} (h : Scale g x r u d)
    (hm : 1 ≤ m) (hmd : m < d) (bm : f (m + d) ≠ f m + u) (ht : 1 ≤ t) (htD : t < r + d) (ne : t ≠ m) :
    f (t + d) - g (t + d) = f t - g t := by
  have s₁ := h.2.1.step hg t ht htD
  have s₂ : f (t + d) = f t + u := by
    refine Classical.byContradiction fun b => ?_
    rcases Nat.lt_trichotomy m t with lt | eq | gt
    · have := h.2.1.gap hg hf bm b lt; omega
    · exact ne eq.symm
    · have := h.2.1.gap hg hf b bm gt; omega
  omega

/-- Lengths of letters. -/
def lens (f g : Nat → Int) (len : Int → Nat) (t : Nat) : Nat := len (f t - g t)

/-- The difference of the two lines takes two values from index one on. -/
theorem PhaseLine.two (hf : PhaseLine g f) {n : Nat} (hn : 1 ≤ n) : f n - g n = f 0 ∨ f n - g n = f 0 + 1 := by
  have := hf 0 n hn
  rw [Nat.zero_add] at this
  omega

theorem lens_bound (hf : PhaseLine g f) (len : Int → Nat) :
    ∃ M, ∀ t, lens f g len t ≤ M := by
  refine ⟨len (f 0 - g 0) + len (f 0) + len (f 0 + 1), fun t => ?_⟩
  unfold lens
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · omega
  · rcases hf.two ht with e | e <;> rw [e] <;> omega

private theorem long_first (hg : IrrationalLine g) {x u : Int} {r d H N M : Nat} (len : Int → Nat)
    (hM : ∀ t, lens f g len t ≤ M) (h : Scale g x r u d) (hN : N ≤ d) (hH : H + 1 ≤ d)
    (no : ∀ t, 1 ≤ t → t < d → f (t + d) = f t + u) :
    LongSquare (fun t => f t - g t) len H (4 * (M * (H + 1))) N := by
  refine ⟨H + 1, H + 1 + d, d - (H + 1), by omega, by omega, fun s hs => ?_, ?_⟩
  · have s₁ := h.2.1.step hg (H + 1 + s) (by omega) (by omega)
    have s₂ := no (H + 1 + s) (by omega) (by omega)
    show f (H + 1 + s) - g (H + 1 + s) = f (H + 1 + d + s) - g (H + 1 + d + s)
    rw [show H + 1 + d + s = H + 1 + s + d by omega, s₁, s₂]
    omega
  · have a := total_le (lens f g len) hM d (H + 1)
    have b := total_le (lens f g len) hM 0 (H + 1)
    rw [Nat.zero_add] at b
    have z : total (lens f g len) 0 = 0 := rfl
    show total (lens f g len) (H + 1 + d) + total (lens f g len) (H + 1) ≤
      total (lens f g len) (H + 1 + (d - (H + 1))) + 4 * (M * (H + 1))
    rw [show H + 1 + (d - (H + 1)) = d by omega, show H + 1 + d = d + (H + 1) by omega]
    omega

/-- The stretch after the failing time, and the stretch one lag later. -/
private theorem shift_one (hg : IrrationalLine g) (hf : PhaseLine g f) {x u : Int} {r d m : Nat} (len : Int → Nat)
    (h : Scale g x r u d) (hm : 1 ≤ m) (hmd : m < d) (bm : f (m + d) ≠ f m + u) (e : Nat) (he : m < e)
    (heD : e ≤ r + d) :
    total (lens f g len) (e + d) + total (lens f g len) (m + 1) =
      total (lens f g len) e + total (lens f g len) (m + 1 + d) := by
  have := total_shift (lens f g len) (m + 1 + d) (m + 1) (e - (m + 1)) fun s hs => by
    unfold lens
    rw [show m + 1 + d + s = m + 1 + s + d by omega, h.copy hg hf hm hmd bm (by omega) (by omega) (by omega)]
  rw [show m + 1 + d + (e - (m + 1)) = e + d by omega, show m + 1 + (e - (m + 1)) = e by omega] at this
  omega

private theorem long_second (hg : IrrationalLine g) (hf : PhaseLine g f) {x u : Int} {r d m H N M S : Nat}
    (len : Int → Nat) (hM : ∀ t, lens f g len t ≤ M) (h : Scale g x r u d) (hN : N ≤ d) (hH : H ≤ r) (hm : 1 ≤ m)
    (hmd : m < d) (bm : f (m + d) ≠ f m + u) (hmr : m < r)
    (hS : 2 * total (lens f g len) m ≤ total (lens f g len) r + S) :
    LongSquare (fun t => f t - g t) len H (S + 2 * M + 2 * (M * H)) N := by
  refine ⟨m + 1 + H, m + 1 + H + d, r + d - (m + 1 + H), by omega, by omega, fun s hs => ?_, ?_⟩
  · have := h.copy hg hf hm hmd bm (t := m + 1 + H + s) (by omega) (by omega) (by omega)
    show f (m + 1 + H + s) - g (m + 1 + H + s) = f (m + 1 + H + d + s) - g (m + 1 + H + d + s)
    rw [show m + 1 + H + d + s = m + 1 + H + s + d by omega, this]
  · have e₁ := shift_one hg hf len h hm hmd bm r hmr (by omega)
    have a := total_le (lens f g len) hM (m + 1 + d) H
    have b := total_le (lens f g len) hM (m + 1) H
    have c := hM m
    have e₂ := total_succ (lens f g len) m
    show total (lens f g len) (m + 1 + H + d) + total (lens f g len) (m + 1 + H) ≤
      total (lens f g len) (m + 1 + H + (r + d - (m + 1 + H))) + (S + 2 * M + 2 * (M * H))
    rw [show m + 1 + H + (r + d - (m + 1 + H)) = r + d by omega, show m + 1 + H + d = m + 1 + d + H by omega]
    omega

/-- If the failing time and the lag fit before `r`, the first `r` letters are twice as long as the first `m`. -/
private theorem fits (hg : IrrationalLine g) (hf : PhaseLine g f) {x u : Int} {r d m M : Nat} (len : Int → Nat)
    (hM : ∀ t, lens f g len t ≤ M) (h : Scale g x r u d) (hm : 1 ≤ m) (hmd : m < d) (bm : f (m + d) ≠ f m + u)
    (hr : m + d ≤ r) : 2 * total (lens f g len) m ≤ total (lens f g len) r + M := by
  have e := total_shift (lens f g len) (1 + d) 1 (m - 1) fun s hs => by
    unfold lens
    rw [show 1 + d + s = 1 + s + d by omega, h.copy hg hf hm hmd bm (by omega) (by omega) (by omega)]
  rw [show 1 + d + (m - 1) = m + d by omega, show 1 + (m - 1) = m by omega] at e
  have a := total_mono (lens f g len) hr
  have b := total_mono (lens f g len) (show m ≤ 1 + d by omega)
  have c := hM 0
  have z : total (lens f g len) 1 = lens f g len 0 := by
    rw [show (1 : Nat) = 0 + 1 by omega, total_succ]; exact Nat.zero_add _
  omega

/-- **Repeats in any lengths.** For every irrational slope, every second line of that slope and any lengths of the two
letters, the word of one arc from an end has repeats at unbounded lags, from every start, that are as long as what comes
before the second place, less a fixed amount, when letters are counted with their lengths. -/
theorem arc_long_squares (hg : IrrationalLine g) (hf : PhaseLine g f) (len : Int → Nat) (hlen : ∀ v, 1 ≤ len v)
    (H : Nat) : ∃ K, ∀ N, LongSquare (fun t => f t - g t) len H K N := by
  obtain ⟨M, hM⟩ := lens_bound hf len
  by_cases all : ∀ N, LongSquare (fun t => f t - g t) len H (4 * (M * (H + 1))) N
  · exact ⟨_, all⟩
  obtain ⟨N₀, no⟩ := Classical.not_forall.mp all
  have pos : ∀ n, 1 ≤ lens f g len n := fun n => hlen _
  -- from here on every scale fails
  have fail {x u : Int} {r d : Nat} (h : Scale g x r u d) (hd : N₀ ≤ d) (hd' : H + 1 ≤ d) (hr : H + M + 1 ≤ r) :
      ∃ m, 1 ≤ m ∧ m < d ∧ f (m + d) ≠ f m + u ∧
        total (lens f g len) r + M < 2 * total (lens f g len) m := by
    obtain ⟨m, hm⟩ : ∃ m, 1 ≤ m ∧ m < d ∧ f (m + d) ≠ f m + u := by
      refine Classical.byContradiction fun nm => no (long_first hg len hM h hd hd' fun t h₁ h₂ => ?_)
      exact Classical.byContradiction fun b => nm ⟨t, h₁, h₂, b⟩
    refine ⟨m, hm.1, hm.2.1, hm.2.2, ?_⟩
    rcases Nat.lt_or_ge (total (lens f g len) r + M) (2 * total (lens f g len) m) with lt | ge
    · exact lt
    · exfalso
      have hmr : m < r := by
        rcases Nat.lt_or_ge m r with lt | le
        · exact lt
        · have a := total_mono (lens f g len) le
          have b := le_total (lens f g len) pos 0 m
          rw [Nat.zero_add] at b
          omega
      have := long_second hg hf (H := H) (S := M) len hM h hd (by omega) hm.1 hm.2.1 hm.2.2 hmr (by omega)
      obtain ⟨i, j, l, h₁, h₂, h₃, h₄⟩ := this
      refine no ⟨i, j, l, h₁, h₂, h₃, ?_⟩
      have : M * (H + 1) = M * H + M := Nat.mul_succ M H
      omega
  -- two scales in a row
  have pair {x u : Int} {r d : Nat} (h : Scale g x r u d) (hd : N₀ ≤ d) (hd' : H + M + 1 ≤ d) (hr : H + M + 1 ≤ r)
      {m : Nat} (hm : 1 ≤ m) (hmd : m < d) (bm : f (m + d) ≠ f m + u) :
      ∃ x' u' : Int, Scale g x' (r + 2 * d) u' (r + d) ∧ m < r ∧ m + d < r + d ∧
        f (m + d + (r + d)) ≠ f (m + d) + u' := by
    have hr1 : 1 ≤ r := h.1.1
    obtain ⟨k, h'⟩ := h.next hg
    have hk0 : d ≤ d + k * (r + d) := Nat.le_add_right _ _
    obtain ⟨m', hm', hmd', bm', lt'⟩ := fail h' (by omega) (by omega) (by omega)
    obtain rfl := h.carry hg hf hm hmd bm hm' hmd' bm'
    have short' : d + k * (r + d) < m + d + (r + d) := by
      rcases Nat.lt_or_ge (d + k * (r + d)) (m + d + (r + d)) with lt | ge
      · exact lt
      · have := fits hg hf len hM h' hm' hmd' bm' ge
        omega
    obtain ⟨k', h''⟩ := h'.next hg
    obtain ⟨m'', hm'', hmd'', bm'', _⟩ := fail h'' (by omega) (by omega) (by
      have : r + d ≤ r + d + k' * (d + k * (r + d) + (r + d)) := Nat.le_add_right _ _
      omega)
    obtain rfl := h'.carry hg hf hm' hmd' bm' hm'' hmd'' bm''
    have hk : k = 1 := by
      rcases Nat.lt_trichotomy k 1 with lt | eq | gt
      · obtain rfl : k = 0 := by omega
        rw [Nat.zero_mul] at hmd''
        omega
      · exact eq
      · have := Nat.mul_le_mul_right (r + d) (show 2 ≤ k by omega)
        omega
    subst hk
    refine ⟨u + ((1 : Nat) : Int) * (x + u), x + u, ?_, by omega, by omega, bm'⟩
    rw [show r + 2 * d = d + 1 * (r + d) by omega]
    exact h'
  -- the shortfall in lengths, over one scale
  have step {x u : Int} {r d m : Nat} (h : Scale g x r u d) (hm : 1 ≤ m) (hmd : m < d) (bm : f (m + d) ≠ f m + u)
      (hmr : m < r) : total (lens f g len) (r + 2 * d) + 2 * total (lens f g len) m + 2 * lens f g len m =
        total (lens f g len) r + 2 * total (lens f g len) (m + d) + 2 * lens f g len (m + d) := by
    have e₁ := shift_one hg hf len h hm hmd bm r hmr (by omega)
    have e₂ := shift_one hg hf len h hm hmd bm (r + d) (by omega) (by omega)
    have e₃ := total_succ (lens f g len) m
    have e₄ := total_succ (lens f g len) (m + d)
    rw [show m + 1 + d = m + d + 1 by omega] at e₁ e₂
    rw [show r + d + d = r + 2 * d by omega] at e₂
    omega
  obtain ⟨x₀, r₀, u₀, d₀, hr₀, hd₀, h₀⟩ := exists_scale_large hg (N₀ + H + M + 1)
  obtain ⟨m₀, hm₀, hmd₀, bm₀, lt₀⟩ := fail h₀ (by omega) (by omega) (by omega)
  obtain ⟨S, hS⟩ : ∃ S, 2 * total (lens f g len) m₀ = total (lens f g len) r₀ + S :=
    ⟨2 * total (lens f g len) m₀ - total (lens f g len) r₀, by omega⟩
  have const : ∀ n : Nat, ∃ (x : Int) (r : Nat) (u : Int) (d m : Nat), n ≤ d ∧ N₀ ≤ d ∧ H + M + 1 ≤ d ∧ H + M + 1 ≤ r ∧
      Scale g x r u d ∧ 1 ≤ m ∧ m < d ∧ f (m + d) ≠ f m + u ∧ m < r ∧
      2 * total (lens f g len) m = total (lens f g len) r + S := by
    intro n
    induction n with
    | zero =>
      obtain ⟨_, _, _, hmr, _, _⟩ := pair h₀ (by omega) (by omega) (by omega) hm₀ hmd₀ bm₀
      exact ⟨x₀, r₀, u₀, d₀, m₀, by omega, by omega, by omega, by omega, h₀, hm₀, hmd₀, bm₀, hmr, hS⟩
    | succ n ih =>
      obtain ⟨x, r, u, d, m, hn, hd, hd', hr, h, hm, hmd, bm, hmr, e⟩ := ih
      obtain ⟨x', u', h', _, hmd', bm'⟩ := pair h hd hd' hr hm hmd bm
      obtain ⟨x'', u'', h'', hmr', hmd'', bm''⟩ := pair h' (by omega) (by omega) (by omega) (by omega) hmd' bm'
      obtain ⟨_, _, _, hmr'', _, _⟩ := pair h'' (by omega) (by omega) (by omega) (by omega) hmd'' bm''
      have l₁ := step h hm hmd bm hmr
      have l₂ := step h' (by omega) hmd' bm' hmr'
      have same : lens f g len (m + d + (r + d)) = lens f g len m := by
        have g₁ := h.2.1.step hg m hm (by omega)
        have g₂ := h'.2.1.step hg (m + d) (by omega) (by omega)
        have v₀ := hf.two hm
        have v₁ := hf.two (n := m + d) (by omega)
        have v₂ := hf.two (n := m + d + (r + d)) (by omega)
        have : f (m + d + (r + d)) - g (m + d + (r + d)) = f m - g m := by omega
        unfold lens
        rw [this]
      refine ⟨x'', _, u'', _, _, ?_, ?_, ?_, ?_, h'', by omega, hmd'', bm'', hmr'', ?_⟩
      · omega
      · omega
      · omega
      · omega
      · omega
  refine ⟨S + 2 * M + 2 * (M * H), fun N => ?_⟩
  obtain ⟨x, r, u, d, m, hn, _, _, hr, h, hm, hmd, bm, hmr, e⟩ := const N
  exact long_second hg hf len hM h hn (by omega) hm hmd bm hmr (by omega)

/-! ### Letters of length one -/

/-- Near-squares of slack `K` and lag at least `N`, from `H` on. -/
def NearSquare (c : Nat → Int) (H K N : Nat) : Prop :=
  ∃ i j : Nat, H ≤ i ∧ i + N ≤ j ∧ ∀ s, s + K < j → c (i + s) = c (j + s)

/-- **Near-squares of one arc.** For every irrational slope and every second line of that slope, the difference of the
floors has near-squares of some fixed slack at unbounded lags, from any start. -/
theorem arc_near_squares (hg : IrrationalLine g) (hf : PhaseLine g f) (H : Nat) :
    ∃ K, ∀ N, NearSquare (fun t => f t - g t) H K N := by
  obtain ⟨K, hK⟩ := arc_long_squares hg hf (fun _ => 1) (fun _ => Nat.le_refl 1) H
  refine ⟨K, fun N => ?_⟩
  obtain ⟨i, j, l, h₁, h₂, h₃, h₄⟩ := hK N
  have one : ∀ n, total (fun _ => 1) n = n := fun n => by
    induction n with
    | zero => rfl
    | succ n ih => rw [total_succ, ih]
  simp only [one] at h₄
  exact ⟨i, j, h₁, h₂, fun s hs => h₃ s (by omega)⟩

/-! ### Beside a clock -/

open Rule30Realization (evol)

/-- The row at time `a`, read from site `i`, evolves as the original row does. -/
theorem evol_frame (x : Int → Bool) (a : Nat) (i : Int) (t : Nat) :
    ∀ j, evol (fun p => evol x a (p + i)) t j = evol x (a + t) (j + i) := by
  induction t with
  | zero => intro j; rfl
  | succ t ih =>
    intro j
    show Rule30Jen.rule _ _ _ = Rule30Jen.rule _ _ _
    rw [ih, ih, ih, show j - 1 + i = j + i - 1 by omega, show j + 1 + i = j + i + 1 by omega]
    rfl

/-- **Corollary F at any column, for block codes.** In a row with a leftmost black cell, column `i` reads `0101…` from
time `a`. If a sequence has near-squares of fixed slack at unbounded lags from every start, then no block code of it is
read, from any index on, by column `i + 1` on the white ticks. -/
theorem no_near_squares (x : Int → Bool) (lo i : Int) (hlo : x lo = true) (hleft : ∀ j < lo, x j = false)
    (c : Nat → Int) (hc : ∀ H, ∃ K, ∀ N, NearSquare c H K N) (a q r : Nat) (φ : (Nat → Int) → Bool)
    (hφ : ∀ v v' : Nat → Int, (∀ s, s < r → v s = v' s) → φ v = φ v')
    (clock : ∀ t, evol x (a + t) i = decide (t % 2 = 1))
    (visible : ∀ t, evol x (a + 2 * t) (i + 1) = φ (fun s => c (t + q + s))) : False := by
  obtain ⟨b, hb⟩ : ∃ b : Nat, lo - ((a + 2 * b : Nat) : Int) < i := ⟨(lo - i).toNat + 1, by omega⟩
  obtain ⟨L, hL⟩ : ∃ L : Nat, lo - ((a + 2 * b : Nat) : Int) = i - (L : Int) :=
    ⟨(i - (lo - ((a + 2 * b : Nat) : Int))).toNat, by omega⟩
  obtain ⟨black, white⟩ := Rule30ClockNearSquares.edge x lo hlo hleft (a + 2 * b)
  have V : ∀ t, evol (fun p => evol x (a + 2 * b) (p + i)) (2 * t) 1 = φ (fun s => c (t + b + q + s)) := by
    intro t
    rw [evol_frame, show a + 2 * b + 2 * t = a + 2 * (t + b) by omega, show (1 : Int) + i = i + 1 by omega, visible]
  obtain ⟨K, hK⟩ := hc (b + q)
  refine Rule30ClockNearSquares.corollary_F (fun p => evol x (a + 2 * b) (p + i)) L (by omega) ?_ ?_ 0 ?_ (r + K) ?_
  · show evol x (a + 2 * b) (-(L : Int) + i) = true
    rw [show -(L : Int) + i = lo - ((a + 2 * b : Nat) : Int) by omega]; exact black
  · intro j hj
    exact white _ (by omega)
  · intro t _
    rw [evol_frame, show a + 2 * b + t = a + (2 * b + t) by omega, show (0 : Int) + i = i by omega, clock,
      show (2 * b + t) % 2 = t % 2 by omega]
  · intro N
    obtain ⟨m, n, h₁, h₂, h₃⟩ := hK (N + 1)
    refine ⟨m - (b + q), n - (b + q), by omega, by omega, by omega, fun s hs => ?_⟩
    rw [V, V]
    apply hφ
    intro k hk
    have := h₃ (s + k) (by omega)
    rw [show m - (b + q) + s + b + q + k = m + (s + k) by omega,
      show n - (b + q) + s + b + q + k = n + (s + k) by omega, this]

/-- **Block codes.** `g` gives the floors of `t α` and `f` those of `t α + θ`, for an irrational `α` and any `θ`, so
`f - g` codes the rotation by `α` by one arc and its complement and starts at an end. No block code of it, from any
index on, is read by the right neighbour of a column that alternates, on its white ticks, in a row with a leftmost
black cell. -/
theorem arc_excluded (x : Int → Bool) (lo i : Int) (hlo : x lo = true) (hleft : ∀ j < lo, x j = false)
    (hg : IrrationalLine g) (hf : PhaseLine g f) (a q r : Nat) (φ : (Nat → Int) → Bool)
    (hφ : ∀ v v' : Nat → Int, (∀ s, s < r → v s = v' s) → φ v = φ v')
    (clock : ∀ t, evol x (a + t) i = decide (t % 2 = 1))
    (visible : ∀ t, evol x (a + 2 * t) (i + 1) = φ (fun s => f (t + q + s) - g (t + q + s))) : False :=
  no_near_squares x lo i hlo hleft (fun t => f t - g t) (arc_near_squares hg hf) a q r φ hφ clock visible

/-- A place in a concatenation lies in one of its blocks. -/
theorem locate (w : Nat → Nat) (a s : Nat) : ∀ l, total w a + s < total w (a + l) →
    ∃ e, e < l ∧ ∃ y, y < w (a + e) ∧ total w a + s = total w (a + e) + y := by
  intro l
  induction l with
  | zero => intro h; rw [Nat.add_zero] at h; omega
  | succ l ih =>
    intro h
    have e : total w (a + (l + 1)) = total w (a + l) + w (a + l) := rfl
    rcases Nat.lt_or_ge (total w a + s) (total w (a + l)) with lt | ge
    · obtain ⟨e, he, y, hy, eq⟩ := ih lt
      exact ⟨e, by omega, y, hy, eq⟩
    · exact ⟨l, by omega, total w a + s - total w (a + l), by omega, by omega⟩

/-- **Blocks in the order of an arc.** Let each letter `v` of the word of one arc from an end stand for a block of
`len v ≥ 1` readings, `β v 0, …, β v (len v - 1)`. No concatenation of these blocks in the order of the word, from any
index `q` on, is read by the right neighbour of a column that alternates, on its white ticks, in a row with a leftmost
black cell. Every irrational angle, every arc, both ends and every translate are covered. -/
theorem blocks_excluded (x : Int → Bool) (lo i : Int) (hlo : x lo = true) (hleft : ∀ j < lo, x j = false)
    (hg : IrrationalLine g) (hf : PhaseLine g f) (len : Int → Nat) (hlen : ∀ v, 1 ≤ len v) (β : Int → Nat → Bool)
    (a q : Nat) (clock : ∀ t, evol x (a + t) i = decide (t % 2 = 1))
    (visible : ∀ n y, y < len (f (q + n) - g (q + n)) →
      evol x (a + 2 * (total (fun k => len (f (q + k) - g (q + k))) n + y)) (i + 1) =
        β (f (q + n) - g (q + n)) y) : False := by
  -- the readings as a sequence of integers
  refine no_near_squares x lo i hlo hleft (fun t => if evol x (a + 2 * t) (i + 1) = true then 1 else 0) ?_ a 0 1
    (fun v => decide (v 0 = 1)) (fun v v' h => by rw [show v 0 = v' 0 from h 0 (by omega)]) clock (fun t => ?_)
  · intro H
    obtain ⟨K, hK⟩ := arc_long_squares hg hf len hlen (q + H)
    refine ⟨K, fun N => ?_⟩
    obtain ⟨m, n, l, h₁, h₂, h₃, h₄'⟩ := hK N
    have h₄ : total (fun t => len (f t - g t)) n + total (fun t => len (f t - g t)) m ≤
      total (fun t => len (f t - g t)) (m + l) + K := h₄'
    clear h₄'
    -- lengths counted from the index q on
    generalize hw : (fun k => len (f (q + k) - g (q + k))) = w at visible
    have pos : ∀ k, 1 ≤ w k := fun k => by rw [← hw]; exact hlen _
    have tail : ∀ k, total (fun t => len (f t - g t)) (q + k) = total (fun t => len (f t - g t)) q + total w k := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        have e : total (fun t => len (f t - g t)) (q + (k + 1)) =
          total (fun t => len (f t - g t)) (q + k) + len (f (q + k) - g (q + k)) := rfl
        have e' : w k = len (f (q + k) - g (q + k)) := by rw [← hw]
        rw [e, ih, total_succ, e']
        omega
    have same : ∀ s, s < l → f (m + s) - g (m + s) = f (n + s) - g (n + s) := h₃
    obtain ⟨m', rfl⟩ : ∃ m', m = q + m' := ⟨m - q, by omega⟩
    obtain ⟨n', rfl⟩ : ∃ n', n = q + n' := ⟨n - q, by omega⟩
    have wsame : ∀ s, s < l → w (m' + s) = w (n' + s) := by
      intro s hs
      have := same s hs
      rw [← hw]
      show len (f (q + (m' + s)) - g (q + (m' + s))) = len (f (q + (n' + s)) - g (q + (n' + s)))
      rw [← Nat.add_assoc, ← Nat.add_assoc, this]
    have t₁ := tail m'
    have t₂ := tail n'
    have t₃ := tail (m' + l)
    rw [← Nat.add_assoc] at t₃
    refine ⟨total w m', total w n', ?_, ?_, fun s hs => ?_⟩
    · have := le_total w pos 0 m'
      rw [Nat.zero_add] at this
      omega
    · have := le_total w pos m' (n' - m')
      rw [show m' + (n' - m') = n' by omega] at this
      omega
    · obtain ⟨e, he, y, hy, eq⟩ := locate w m' s l (by omega)
      have sh := total_shift w m' n' e fun s hs => wsame s (by omega)
      have hy' : y < w (n' + e) := by rw [← wsame e he]; exact hy
      have v₁ := visible (m' + e) y (by rw [← hw] at hy; exact hy)
      have v₂ := visible (n' + e) y (by rw [← hw] at hy'; exact hy')
      have key : evol x (a + 2 * (total w m' + s)) (i + 1) = evol x (a + 2 * (total w n' + s)) (i + 1) := by
        rw [show total w m' + s = total w (m' + e) + y by omega, show total w n' + s = total w (n' + e) + y by omega,
          v₁, v₂]
        have := same e he
        rw [← Nat.add_assoc, ← Nat.add_assoc, this]
      show (if evol x (a + 2 * (total w m' + s)) (i + 1) = true then (1 : Int) else 0) =
        if evol x (a + 2 * (total w n' + s)) (i + 1) = true then (1 : Int) else 0
      rw [key]
  · show evol x (a + 2 * t) (i + 1) =
      decide ((if evol x (a + 2 * (t + 0 + 0)) (i + 1) = true then (1 : Int) else 0) = 1)
    cases evol x (a + 2 * t) (i + 1) <;> simp

/-- **Gaps in the order of an arc.** The black readings of the right neighbour do not come at gaps `gap v` in the order
of the word of one arc from an end. -/
theorem gap_order_excluded (x : Int → Bool) (lo i : Int) (hlo : x lo = true) (hleft : ∀ j < lo, x j = false)
    (hg : IrrationalLine g) (hf : PhaseLine g f) (gap : Int → Nat) (hgap : ∀ v, 1 ≤ gap v) (a q : Nat)
    (clock : ∀ t, evol x (a + t) i = decide (t % 2 = 1))
    (visible : ∀ n y, y < gap (f (q + n) - g (q + n)) →
      evol x (a + 2 * (total (fun k => gap (f (q + k) - g (q + k))) n + y)) (i + 1) = decide (y = 0)) : False :=
  blocks_excluded x lo i hlo hleft hg hf gap hgap (fun _ y => decide (y = 0)) a q clock visible

/-! ### Examples: square roots and half-circles -/

/-- A line and itself, moved. -/
theorem IrrationalLine.moved (hg : IrrationalLine g) (k : Nat) (hk : 1 ≤ k) : PhaseLine g (fun t => g (t + k)) := by
  intro t n hn
  have a := above_add hg (floor_above hg (t := t + k) (by omega)) (floor_above hg hn)
  have b := above_add hg (floor_below hg (t := t + k) (by omega)) (floor_below hg hn)
  rw [← Int.natCast_add] at a
  rw [show -(g (t + k) + 1) + -(g n + 1) = -(g (t + k) + g n + 2) by omega,
    show -((t + k : Nat) : Int) + -(n : Int) = -((t + k + n : Nat) : Int) by omega] at b
  have a' := le_floor hg (by omega) a
  have b' := floor_lt hg (by omega) b
  dsimp only
  rw [show t + n + k = t + k + n by omega]
  omega

/-- The floors of the multiples of half a number. -/
theorem IrrationalLine.half (hf : IrrationalLine f) : IrrationalLine (fun t => f t / 2) where
  floors := fun m n hm hn => by
    have a := hf.floors m n hm hn
    have b := Int.mul_le_mul_of_nonneg_left (show 2 * (f m / 2) ≤ f m by omega) (show (0 : Int) ≤ n by omega)
    have c := Int.mul_le_mul_of_nonneg_left (show f n + 1 ≤ 2 * (f n / 2 + 1) by omega) (show (0 : Int) ≤ m by omega)
    grind
  irrational := fun p q hq => by
    have hq0 : (0 : Int) ≤ q := by omega
    rcases above_total hf (2 * p) q hq with a | a
    · obtain ⟨n, hn, h₁, h₂⟩ := a
      obtain ⟨l₁, _⟩ := above_refine hf hn h₁ h₂ 1 (by omega)
      -- a multiple of n with room for the rounding
      have hm : 1 ≤ q + 1 := by omega
      have lo := (floors_refine hf (q + 1) n hm hn).1
      have e₁ := Int.mul_le_mul_of_nonneg_left (show (n : Int) * (2 * p) + 1 ≤ q * f n by omega)
        (show (0 : Int) ≤ ((q + 1 : Nat) : Int) by omega)
      have e₂ := Int.mul_le_mul_of_nonneg_left lo hq0
      have e₃ := Int.mul_le_mul_of_nonneg_left (show f ((q + 1) * n) ≤ 2 * (f ((q + 1) * n) / 2) + 1 by omega) hq0
      refine ⟨(q + 1) * n, Nat.mul_pos hm hn, Or.inl ?_⟩
      rw [Int.natCast_mul]
      push_cast at e₁ e₂ e₃ ⊢
      grind
    · obtain ⟨n, hn, h₁, h₂⟩ := a
      have hm : 1 ≤ q + 1 := by omega
      have hi := (floors_refine hf (q + 1) n hm hn).2
      have e₁ := Int.mul_le_mul_of_nonneg_left (show (q : Int) * (f n + 1) + 1 ≤ n * (2 * p) by grind)
        (show (0 : Int) ≤ ((q + 1 : Nat) : Int) by omega)
      have e₂ := Int.mul_le_mul_of_nonneg_left hi hq0
      have e₃ := Int.mul_le_mul_of_nonneg_left (show 2 * (f ((q + 1) * n) / 2) ≤ f ((q + 1) * n) by omega) hq0
      refine ⟨(q + 1) * n, Nat.mul_pos hm hn, Or.inr ?_⟩
      rw [Int.natCast_mul]
      push_cast at e₁ e₂ e₃ ⊢
      grind

/-- The second line of the half-circle: with `f` the floors of `t β`, the difference of `(f + 1) / 2` and `f / 2` is the
parity of `f`. -/
theorem IrrationalLine.half_phase (hf : IrrationalLine f) (h₀ : f 0 = 0) :
    PhaseLine (fun t => f t / 2) (fun t => (f t + 1) / 2) := by
  intro t n hn
  dsimp only
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · rw [Nat.zero_add, h₀]
    omega
  · have m := hf.moved t ht 0 n hn
    dsimp only at m
    rw [Nat.zero_add, Nat.zero_add, Nat.add_comm n t] at m
    omega

/-- The integer square root. -/
def isqrt : Nat → Nat
  | 0 => 0
  | n + 1 => if (isqrt n + 1) * (isqrt n + 1) ≤ n + 1 then isqrt n + 1 else isqrt n

theorem isqrt_spec (n : Nat) : isqrt n * isqrt n ≤ n ∧ n < (isqrt n + 1) * (isqrt n + 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    unfold isqrt
    split
    · refine ⟨by assumption, ?_⟩
      grind
    · omega

private theorem lt_of_sq {a b : Nat} (h : a * a < b * b) : a < b := by
  rcases Nat.lt_or_ge a b with h' | h'
  · exact h'
  · have := Nat.mul_le_mul h' h'; omega

/-- The floors of the multiples of the square root of a number that is not the square of a fraction. -/
theorem sqrt_line (m : Nat) (hm : ∀ p q : Nat, 1 ≤ q → p * p ≠ m * (q * q)) :
    IrrationalLine (fun t => (isqrt (m * (t * t)) : Int)) where
  floors := fun s t hs ht => by
    obtain ⟨a, _⟩ := isqrt_spec (m * (s * s))
    obtain ⟨_, b⟩ := isqrt_spec (m * (t * t))
    generalize isqrt (m * (s * s)) = A at *
    generalize isqrt (m * (t * t)) = B at *
    have h : t * A < s * (B + 1) := by
      apply lt_of_sq
      have e₁ := Nat.mul_le_mul_left (t * t) a
      have e₂ := Nat.mul_lt_mul_of_pos_left b (Nat.mul_pos hs hs)
      grind
    exact_mod_cast h
  irrational := fun p q hq => by
    rcases Int.lt_or_le p 0 with hp | hp
    · refine ⟨1, by omega, Or.inl ?_⟩
      have := Int.mul_nonneg (show (0 : Int) ≤ q by omega) (show (0 : Int) ≤ (isqrt (m * (1 * 1)) : Int) by omega)
      omega
    obtain ⟨p, rfl⟩ : ∃ p' : Nat, p = (p' : Int) := ⟨p.toNat, by omega⟩
    refine ⟨2 * p * q + q + 1, by omega, ?_⟩
    generalize hn : 2 * p * q + q + 1 = n
    obtain ⟨a, b⟩ := isqrt_spec (m * (n * n))
    generalize isqrt (m * (n * n)) = A at *
    rcases Nat.lt_or_gt_of_ne (hm p q hq) with h | h
    · left
      have h' : n * p < q * A := by
        rcases Nat.lt_or_ge (n * p) (q * A) with h' | h'
        · exact h'
        exfalso
        -- m (q n)² < (q A + q)² ≤ (n p + q)², and m q² ≥ p² + 1
        have e₁ := Nat.mul_lt_mul_of_pos_left b (Nat.mul_pos hq hq)
        have e₂ : q * A + q ≤ n * p + q := by omega
        have e₃ := Nat.mul_le_mul e₂ e₂
        have e₄ := Nat.mul_le_mul_right (n * n) (show p * p + 1 ≤ m * (q * q) by omega)
        have e₅ : n * n = n * (2 * p * q) + n * q + n := by rw [← hn]; grind
        have e₆ : q * q ≤ n * q := Nat.mul_le_mul_right q (by omega)
        grind
      exact_mod_cast h'
    · right
      have h' : q * (A + 1) < n * p := by
        rcases Nat.lt_or_ge (q * (A + 1)) (n * p) with h' | h'
        · exact h'
        exfalso
        -- (n p - q)² ≤ (q A)² ≤ m (q n)², and m q² + 1 ≤ p²
        have e₁ := Nat.mul_le_mul_left (q * q) a
        have e₄ := Nat.mul_le_mul_right (n * n) (show m * (q * q) + 1 ≤ p * p by omega)
        have e₅ : n * n = n * (2 * p * q) + n * q + n := by rw [← hn]; grind
        have e₇ : n * p * (n * p) ≤ (q * A + q) * (n * p) := Nat.mul_le_mul_right _ (by grind)
        have e₈ : (q * A) * (n * p) ≤ (q * A) * (q * A + q) := Nat.mul_le_mul_left _ (by grind)
        have hA : q * A ≤ n * p := by
          rcases Nat.lt_or_ge (n * p) (q * A) with h'' | h''
          · have := Nat.mul_self_lt_mul_self h''
            grind
          · exact h''
        have e₉ := Nat.mul_le_mul_right q hA
        grind
      exact_mod_cast h'

theorem two_irrational (p q : Nat) (hq : 1 ≤ q) : p * p ≠ 2 * (q * q) := by
  induction q using Nat.strongRecOn generalizing p with
  | ind q ih =>
    intro h
    obtain ⟨k, rfl⟩ : ∃ k, p = 2 * k := by
      rcases Nat.mod_two_eq_zero_or_one p with e | e
      · exact ⟨p / 2, by omega⟩
      · obtain ⟨k, rfl⟩ : ∃ k, p = 2 * k + 1 := ⟨p / 2, by omega⟩
        grind
    have h' : q * q = 2 * (k * k) := by grind
    have hk : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · have := Nat.mul_pos hq hq; omega
      · exact hk
    have hkq : k < q := by
      apply lt_of_sq
      have := Nat.mul_pos hk hk
      omega
    exact ih k hkq q hk h'

/-- An example. Set the two blocks of gaps 3, 5, 5, 5 and 3, 5, 5, 5, 5, 5 in the order of the parities of `⌊t √2⌋`,
from any index `q` on. The right neighbour of a column that alternates does not read this from any tick on, in a row
with a leftmost black cell. -/
theorem silver_blocks_excluded (x : Int → Bool) (lo i : Int) (hlo : x lo = true) (hleft : ∀ j < lo, x j = false)
    (a q : Nat) (clock : ∀ t, evol x (a + t) i = decide (t % 2 = 1)) :
    ¬ ∀ n y, y < (if isqrt (2 * ((q + n) * (q + n))) % 2 = 1 then 28 else 18) →
      evol x (a + 2 * (total (fun k => if isqrt (2 * ((q + k) * (q + k))) % 2 = 1 then 28 else 18) n + y)) (i + 1) =
        decide (y = 0 ∨ y % 5 = 3) := by
  intro visible
  have hs := sqrt_line 2 two_irrational
  have par : ∀ t : Nat, (((isqrt (2 * (t * t)) : Int) + 1) / 2 - (isqrt (2 * (t * t)) : Int) / 2 = 1) ↔
      isqrt (2 * (t * t)) % 2 = 1 := fun t => by omega
  refine blocks_excluded x lo i hlo hleft hs.half (hs.half_phase (by decide)) (fun v => if v = 1 then 28 else 18)
    (fun v => by split <;> omega) (fun _ y => decide (y = 0 ∨ y % 5 = 3)) a q clock (fun n y hy => ?_)
  simp only [par] at hy ⊢
  exact visible n y hy

end Ruliology.CellularAutomata.Rule30RotationBlocks
