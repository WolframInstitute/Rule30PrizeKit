module

public import Ruliology.CellularAutomata.Rule30AgeTwentyFourInverse
public import Ruliology.CellularAutomata.Rule30FiniteConfigs

/-!
# Hughes's two inverse theorems without the wall

For every configuration `x : Int → Bool` of the line with a leftmost black cell at `lo`, under rule 30
(`Rule30Realization.evol`):

* `predecessor_edge_from_age_eight`: if `t ≥ 8`, every predecessor of `evol x t` has its leftmost black
  cell at `lo - t + 1`, the edge of `evol x (t - 1)`.
* `two_step_predecessor_edge_from_age_twenty_four`: if `t ≥ 24`, every two-step predecessor of
  `evol x t` has its leftmost black cell at `lo - t + 2`.

Nothing is assumed of the predecessors: each is an arbitrary configuration, and each is shown to have a
leftmost black cell, at the place of the true one. No wall appears.

* `predecessor_edge_fails_at_age_seven`: the age 8 cannot be lowered. The configuration with black cells
  at `0` and `3` has, at age 7, a predecessor black on `(-∞, -9]` and on `[11, ∞)`: it has no leftmost
  black cell.
* `two_step_predecessor_edge_fails_at_age_twenty_three`, `age_twenty_four_sharp`: the age 24 cannot be
  lowered. The configuration with black cells at `0, 3, 4, 6, 7, 10, 11, 12` and `14` has, at age 23, a
  predecessor of its image with the true edge, and a predecessor of that one which is black on all of
  `(-∞, -24]`: it has no leftmost black cell.
* `one_tick_least_age`, `two_tick_least_age`: so 8 and 24 are the least ages. Each conclusion holds at
  every age from `a` on exactly when `8 ≤ a`, and when `24 ≤ a`.

**The proof is Hughes's** (`Rule30AgeEightInverse`, `Rule30AgeTwentyFourInverse`), read on the line.
The outer cells of a configuration with a leftmost black cell move out by one and update by themselves:
the `w` cells from the edge at time `t + 1` are the kit's band map `R` of the `w` cells from the edge at
time `t` (`band_step`). So the 8 and the 20 cells from the edge are, at ages 8 and 24, among the kit's
good bands (`EdgeGood8`, `EdgeGood20`). This comes from the kit's public `top8_from_age_eight` and
`top20_from_age_twenty_four`, applied to one window through `iter_F_shiftRight`. Beside the white
wall, rows narrower than the band need a separate finite check; on the line there is always a full
band, so there is no such case. Below a good band, the inverse rule `z (p - 1) = y p ⊕ (z p ∨ z (p + 1))`,
run outward from any two cells, ends in two white cells (`prun_reset8`, `prun_reset20`). This is the
kit's pair transducer, restated here because the kit's copy is private, with its tables checked by
`decide`. Outward from two white cells over a white image, the predecessor is white.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30TwoSidedInverse

open Rule30Jen Rule30Realization Rule30FiniteConfigs Rule30ZeroBoundary Rule30ZeroBoundary.IntegerForm
  Rule30LateTwins Rule30AgeEightInverse Rule30AgeTwentyFourInverse

/-! ## Bands -/

/-- The `w` cells of `c` from position `f`, as a number: cell `f + j` is bit `w - 1 - j`. -/
def band (c : Int → Bool) (f : Int) : Nat → Nat
  | 0 => 0
  | w + 1 => 2 * band c f w + (if c (f + w) then 1 else 0)

theorem band_lt (c : Int → Bool) (f : Int) : ∀ w, band c f w < 2 ^ w
  | 0 => by simp [band]
  | w + 1 => by
    have := band_lt c f w
    simp only [band, Nat.pow_succ]
    split <;> omega

theorem testBit_band_ge (c : Int → Bool) (f : Int) (w i : Nat) (h : w ≤ i) :
    (band c f w).testBit i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (band_lt c f w) (Nat.pow_le_pow_right (by decide) h))

theorem testBit_band_lt (c : Int → Bool) (f : Int) : ∀ (w i : Nat), i < w →
    (band c f w).testBit i = c (f + (w : Int) - 1 - (i : Int))
  | 0, i, h => absurd h (by omega)
  | w + 1, 0, _ => by
    rw [show f + ((w + 1 : Nat) : Int) - 1 - ((0 : Nat) : Int) = f + (w : Int) by push_cast; omega]
    simp only [band, Nat.testBit_zero]
    cases hc : c (f + (w : Int))
    · exact decide_eq_false (by simp)
    · exact decide_eq_true (by simp)
  | w + 1, i + 1, h => by
    rw [Nat.testBit_succ]
    have : (band c f (w + 1)) / 2 = band c f w := by simp only [band]; split <;> omega
    rw [this, testBit_band_lt c f w i (by omega)]
    congr 1
    push_cast; omega

theorem band_top (c : Int → Bool) (f : Int) (hf : c f = true) (w : Nat) : 2 ^ w ≤ band c f (w + 1) := by
  apply Nat.le_of_not_lt
  intro hlt
  have h := Nat.testBit_lt_two_pow hlt
  rw [testBit_band_lt c f (w + 1) w (by omega),
    show f + ((w + 1 : Nat) : Int) - 1 - (w : Int) = f by push_cast; omega, hf] at h
  exact absurd h (by decide)

/-- A band reads only its own cells. -/
theorem band_congr {c d : Int → Bool} {f g : Int} : ∀ w, (∀ j : Nat, j < w → c (f + j) = d (g + j)) →
    band c f w = band d g w
  | 0, _ => rfl
  | w + 1, h => by
    simp only [band]
    rw [band_congr w (fun j hj => h j (by omega)), h w (by omega)]

/-! ## The outer cells update by themselves -/

/-- One step of rule 30 on the line. -/
def stepLine (c : Int → Bool) : Int → Bool := fun p => rule (c (p - 1)) (c p) (c (p + 1))

theorem evol_succ (x : Int → Bool) (t : Nat) : evol x (t + 1) = stepLine (evol x t) := rfl

/-- **The band moves out by one and updates by `R`**, for any configuration white to the left of `f`. -/
theorem band_step (c : Int → Bool) (f : Int) (w : Nat) (hw : ∀ p, p < f → c p = false) :
    band (stepLine c) (f - 1) w = R (band c f w) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [R, Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftRight]
  by_cases hi : i < w
  · rw [testBit_band_lt _ _ _ _ hi, testBit_band_lt _ _ _ _ hi]
    simp only [stepLine, rule]
    have e1 : (f - 1 + (w : Int) - 1 - (i : Int)) - 1 = f + (w : Int) - 1 - ((2 + i : Nat) : Int) := by
      push_cast; omega
    have e2 : f - 1 + (w : Int) - 1 - (i : Int) = f + (w : Int) - 1 - ((1 + i : Nat) : Int) := by
      push_cast; omega
    have e3 : f - 1 + (w : Int) - 1 - (i : Int) + 1 = f + (w : Int) - 1 - (i : Int) := by omega
    rw [e3, e1, e2]
    congr 1
    · by_cases h2 : 2 + i < w
      · rw [testBit_band_lt _ _ _ _ h2]
      · rw [testBit_band_ge _ _ _ _ (by omega)]
        exact hw _ (by push_cast; omega)
    · congr 1
      by_cases h1 : 1 + i < w
      · rw [testBit_band_lt _ _ _ _ h1]
      · rw [testBit_band_ge _ _ _ _ (by omega)]
        exact hw _ (by push_cast; omega)
  · rw [testBit_band_ge _ _ _ _ (by omega), testBit_band_ge _ _ _ _ (by omega),
      testBit_band_ge _ _ _ _ (by omega), testBit_band_ge _ _ _ _ (by omega)]
    rfl

theorem iterR_succ' : ∀ (n u : Nat), iterR (n + 1) u = R (iterR n u)
  | 0, _ => rfl
  | n + 1, u => by
    show iterR (n + 1) (R u) = R (iterR (n + 1) u)
    rw [iterR_succ' n (R u)]
    rfl

section Edge

variable {x : Int → Bool} {lo : Int} (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
include hlo hzero

omit hlo in
/-- The `w` cells from the edge at time `t` are `R` applied `t` times to the `w` cells from the edge at time `0`. -/
theorem band_evol (w : Nat) : ∀ t : Nat, band (evol x t) (lo - t) w = iterR t (band x lo w)
  | 0 => by simp [evol, iterR]
  | t + 1 => by
    rw [evol_succ, show lo - ((t + 1 : Nat) : Int) = lo - t - 1 by push_cast; omega,
      band_step _ _ _ (fun p hp => evol_eq_false_of_lt hzero t p hp), band_evol w t, iterR_succ']

theorem good8_of_age (t : Nat) (ht : 8 ≤ t) : EdgeGood8 (band (evol x t) (lo - t) 8) = true := by
  rw [band_evol hzero]
  have hu : 2 ^ 7 ≤ band x lo 8 := band_top x lo hlo 7
  have hu' := band_lt x lo 8
  have hne : band x lo 8 ≠ 0 := by omega
  have hlog : (band x lo 8).log2 = 7 := (Nat.log2_eq_iff hne).2 ⟨hu, hu'⟩
  have h := top8_from_age_eight (band x lo 8) t hne ht
  rw [hlog, show 7 + t - 7 = 0 + t by omega, iter_F_shiftRight] at h
  simpa using h

theorem good20_of_age (t : Nat) (ht : 24 ≤ t) : EdgeGood20 (band (evol x t) (lo - t) 20) = true := by
  rw [band_evol hzero]
  have hu : 2 ^ 19 ≤ band x lo 20 := band_top x lo hlo 19
  have hu' := band_lt x lo 20
  have hne : band x lo 20 ≠ 0 := by omega
  have hlog : (band x lo 20).log2 = 19 := (Nat.log2_eq_iff hne).2 ⟨hu, hu'⟩
  have h := top20_from_age_twenty_four (band x lo 20) t hne ht
  rw [hlog, show 19 + t - 19 = 0 + t by omega, iter_F_shiftRight] at h
  simpa using h

end Edge

/-! ## Below a good band, a predecessor resets -/

/-- One outward step of the inverse rule on two adjacent cells: `(z p, z (p + 1)) ↦ (z (p - 1), z p)`. -/
def pstep (bit : Bool) (s : Bool × Bool) : Bool × Bool := (xor bit (s.1 || s.2), s.1)

/-- The inverse rule run over the bits `0, 1, …` of `u` (from the inner end of the band outward). -/
def prun (u : Nat) (s : Bool × Bool) : Nat → Bool × Bool
  | 0 => s
  | n + 1 => pstep (u.testBit n) (prun u s n)

/-- Under rule 30, a predecessor is fixed leftward by its image: `z (p - 1) = y p ⊕ (z p ∨ z (p + 1))`. -/
theorem left_of (y z : Int → Bool) (hz : ∀ p, stepLine z p = y p) (p : Int) :
    z (p - 1) = xor (y p) (z p || z (p + 1)) := by
  rw [← hz p]
  simp only [stepLine, rule]
  cases z (p - 1) <;> cases z p <;> cases z (p + 1) <;> rfl

theorem prun_spec (y z : Int → Bool) (hz : ∀ p, stepLine z p = y p) (f : Int) (w : Nat) :
    ∀ n, n ≤ w → prun (band y f w) (z (f + w - 1), z (f + w)) n =
      (z (f + (w : Int) - 1 - (n : Int)), z (f + (w : Int) - (n : Int)))
  | 0, _ => by simp [prun]
  | n + 1, hn => by
    rw [prun, prun_spec y z hz f w n (by omega), testBit_band_lt _ _ _ _ (by omega)]
    simp only [pstep]
    have e := left_of y z hz (f + (w : Int) - 1 - (n : Int))
    rw [show f + (w : Int) - 1 - (n : Int) + 1 = f + (w : Int) - (n : Int) by omega] at e
    rw [← e]
    congr 1 <;> congr 1 <;> push_cast <;> omega

theorem prun_reset8 (u : Nat) (h : EdgeGood8 u = true) (a b : Bool) : prun u (a, b) 8 = (false, false) := by
  simp only [EdgeGood8, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | rfl <;> cases a <;> cases b <;> decide

/-- The predecessor's own band, from the cell after the edge: positions `f + 1 + j` are reached after
`18 - j` steps of a run over a 20-cell band. -/
def parentBand (u : Nat) (s : Bool × Bool) : Nat :=
  band (fun q => (prun u s (19 - q.toNat)).1) 1 8

theorem prun_reset20 (u : Nat) (h : EdgeGood20 u = true) (a b : Bool) :
    prun u (a, b) 20 = (false, false) ∧ EdgeGood8 (parentBand u (a, b)) = true := by
  simp only [EdgeGood20, Bool.or_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> cases a <;> cases b <;> decide +kernel

/-- Outward from two white cells over a white image, a predecessor is white; and the image's edge cell
makes the next cell black. -/
theorem edge_of_reset (y z : Int → Bool) (hz : ∀ p, stepLine z p = y p) (f : Int)
    (hy : y f = true) (hw : ∀ p, p < f → y p = false) (h0 : z (f - 1) = false) (h1 : z f = false) :
    z (f + 1) = true ∧ ∀ p, p < f + 1 → z p = false := by
  have hd : ∀ n : Nat, z (f - n) = false ∧ z (f - 1 - n) = false := by
    intro n
    induction n with
    | zero => simpa using And.intro h1 h0
    | succ n ih =>
      refine ⟨by rw [show f - ((n + 1 : Nat) : Int) = f - 1 - n by push_cast; omega]; exact ih.2, ?_⟩
      have e := left_of y z hz (f - 1 - n)
      rw [show f - 1 - (n : Int) - 1 = f - 1 - ((n + 1 : Nat) : Int) by push_cast; omega,
        show f - 1 - (n : Int) + 1 = f - n by omega, ih.1, ih.2, hw _ (by omega)] at e
      simpa using e
  have hle : ∀ p, p ≤ f → z p = false := fun p hp => by
    have := (hd (f - p).toNat).1
    rwa [show f - ((f - p).toNat : Int) = p by omega] at this
  refine ⟨?_, fun p hp => hle p (by omega)⟩
  have e := hz f
  simp only [stepLine, rule, hle (f - 1) (by omega), hle f (Int.le_refl _), hy, Bool.false_xor,
    Bool.false_or] at e
  exact e

/-- **One step.** Below an image whose 8 cells from its edge `f` are good, every predecessor has its
leftmost black cell at `f + 1`. -/
theorem predecessor_edge_of_good8 (y z : Int → Bool) (hz : ∀ p, stepLine z p = y p) (f : Int)
    (hy : y f = true) (hw : ∀ p, p < f → y p = false) (hg : EdgeGood8 (band y f 8) = true) :
    z (f + 1) = true ∧ ∀ p, p < f + 1 → z p = false := by
  have hr := prun_spec y z hz f 8 8 (Nat.le_refl _)
  rw [prun_reset8 _ hg] at hr
  simp only [Prod.mk.injEq] at hr
  refine edge_of_reset y z hz f hy hw ?_ ?_
  · rw [show f - 1 = f + ((8 : Nat) : Int) - 1 - ((8 : Nat) : Int) by push_cast; omega]; exact hr.1.symm
  · rw [show f = f + ((8 : Nat) : Int) - ((8 : Nat) : Int) by push_cast; omega]; exact hr.2.symm

/-- **One step, from a good 20-cell band.** The predecessor's edge is at `f + 1`, and its own 8 cells from
there are good. -/
theorem predecessor_of_good20 (y z : Int → Bool) (hz : ∀ p, stepLine z p = y p) (f : Int)
    (hy : y f = true) (hw : ∀ p, p < f → y p = false) (hg : EdgeGood20 (band y f 20) = true) :
    (z (f + 1) = true ∧ ∀ p, p < f + 1 → z p = false) ∧ EdgeGood8 (band z (f + 1) 8) = true := by
  have hr := fun n hn => prun_spec y z hz f 20 n hn
  obtain ⟨hres, hpar⟩ := prun_reset20 _ hg (z (f + (20 : Nat) - 1)) (z (f + (20 : Nat)))
  have h20 := hr 20 (Nat.le_refl _)
  rw [hres] at h20
  simp only [Prod.mk.injEq] at h20
  refine ⟨edge_of_reset y z hz f hy hw ?_ ?_, ?_⟩
  · rw [show f - 1 = f + ((20 : Nat) : Int) - 1 - ((20 : Nat) : Int) by push_cast; omega]; exact h20.1.symm
  · rw [show f = f + ((20 : Nat) : Int) - ((20 : Nat) : Int) by push_cast; omega]; exact h20.2.symm
  · have e : band z (f + 1) 8 = parentBand (band y f 20) (z (f + (20 : Nat) - 1), z (f + (20 : Nat))) := by
      unfold parentBand
      refine band_congr 8 (fun j hj => ?_)
      have := hr (18 - j) (by omega)
      rw [show ((1 : Int) + (j : Int)).toNat = 1 + j by omega, show 19 - (1 + j) = 18 - j by omega, this]
      congr 1
      push_cast
      omega
    rw [e]
    exact hpar

/-! ## The two theorems -/

section Edge

variable {x : Int → Bool} {lo : Int} (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
include hlo hzero

/-- **Hughes's age-8 inverse, without the wall.** For a configuration with a leftmost black cell at `lo`
and `t ≥ 8`, every predecessor of its image at time `t` has its leftmost black cell at `lo - t + 1`. -/
theorem predecessor_edge_from_age_eight (t : Nat) (ht : 8 ≤ t) (z : Int → Bool)
    (hz : ∀ p, rule (z (p - 1)) (z p) (z (p + 1)) = evol x t p) :
    z (lo - t + 1) = true ∧ ∀ p, p < lo - t + 1 → z p = false :=
  predecessor_edge_of_good8 (evol x t) z hz (lo - t) (evol_left_edge hlo hzero t)
    (fun p hp => evol_eq_false_of_lt hzero t p hp) (good8_of_age hlo hzero t ht)

/-- **Hughes's age-24 inverse, without the wall.** For a configuration with a leftmost black cell at
`lo` and `t ≥ 24`, every two-step predecessor of its image at time `t` has its leftmost black cell at
`lo - t + 2`. -/
theorem two_step_predecessor_edge_from_age_twenty_four (t : Nat) (ht : 24 ≤ t) (w v : Int → Bool)
    (hw : ∀ p, rule (w (p - 1)) (w p) (w (p + 1)) = evol x t p)
    (hv : ∀ p, rule (v (p - 1)) (v p) (v (p + 1)) = w p) :
    v (lo - t + 2) = true ∧ ∀ p, p < lo - t + 2 → v p = false := by
  obtain ⟨⟨hw1, hw0⟩, hg⟩ := predecessor_of_good20 (evol x t) w hw (lo - t) (evol_left_edge hlo hzero t)
    (fun p hp => evol_eq_false_of_lt hzero t p hp) (good20_of_age hlo hzero t ht)
  have h := predecessor_edge_of_good8 w v hv (lo - t + 1) hw1 hw0 hg
  rw [show lo - t + 1 + 1 = lo - t + 2 by omega] at h
  exact h

end Edge

/-! ## Age 8 is sharp -/

/-- On the right, a configuration white beyond `hi` stays white beyond `hi + t`. -/
theorem evol_eq_false_of_gt {x : Int → Bool} {hi : Int} (hz : ∀ p, hi < p → x p = false) :
    ∀ (t : Nat) (p : Int), hi + t < p → evol x t p = false
  | 0, p, h => hz p (by omega)
  | t + 1, p, h => by
    show rule (evol x t (p - 1)) (evol x t p) (evol x t (p + 1)) = false
    rw [evol_eq_false_of_gt hz t (p - 1) (by push_cast at h; omega), evol_eq_false_of_gt hz t p (by push_cast at h; omega),
      evol_eq_false_of_gt hz t (p + 1) (by push_cast at h; omega)]
    rfl

/-- Two black cells, at `0` and `3`. -/
def sharpX (p : Int) : Bool := p == 0 || p == 3

/-- The middle of the witness, on the positions `-8, …, 10`. -/
def sharpMid : List Bool :=
  [false, true, false, false, false, true, false, false, true, false, false, false, false, false, true, true,
    false, false, true]

/-- A predecessor of `evol sharpX 7` that is black on `(-∞, -9]` and on `[11, ∞)`. -/
def sharpZ (p : Int) : Bool := if p ≤ -9 then true else if 11 ≤ p then true else sharpMid.getD (p + 8).toNat false

theorem sharp_middle : ∀ k : Nat, k < 21 →
    rule (sharpZ (-9 + k - 1)) (sharpZ (-9 + k)) (sharpZ (-9 + k + 1)) = evol sharpX 7 (-9 + k) := by
  decide +kernel

/-- **The age 8 is sharp.** At age 7, some configuration with a leftmost black cell has a predecessor of its
image with no leftmost black cell at all. -/
theorem predecessor_edge_fails_at_age_seven :
    sharpX 0 = true ∧ (∀ p, p < 0 → sharpX p = false) ∧
    (∀ p, rule (sharpZ (p - 1)) (sharpZ p) (sharpZ (p + 1)) = evol sharpX 7 p) ∧
    ∀ q : Int, ∃ p, p < q ∧ sharpZ p = true := by
  have hl : ∀ p, p < 0 → sharpX p = false := fun p hp => by
    simp only [sharpX, Bool.or_eq_false_iff, beq_eq_false_iff_ne]; omega
  have hr : ∀ p, (3 : Int) < p → sharpX p = false := fun p hp => by
    simp only [sharpX, Bool.or_eq_false_iff, beq_eq_false_iff_ne]; omega
  refine ⟨by decide, hl, fun p => ?_, fun q => ⟨min (q - 1) (-9), by omega, ?_⟩⟩
  · by_cases h1 : p ≤ -10
    · rw [evol_eq_false_of_lt hl 7 p (by omega)]
      simp only [sharpZ, show p - 1 ≤ -9 by omega, show p ≤ -9 by omega, show p + 1 ≤ -9 by omega,
        ↓reduceIte]
      rfl
    · by_cases h2 : 12 ≤ p
      · rw [evol_eq_false_of_gt hr 7 p (by push_cast; omega)]
        simp only [sharpZ, show ¬ (p - 1 ≤ -9) by omega, show ¬ (p ≤ -9) by omega, show ¬ (p + 1 ≤ -9) by omega,
          show 11 ≤ p - 1 by omega, show 11 ≤ p by omega, show 11 ≤ p + 1 by omega, ↓reduceIte]
        rfl
      · have := sharp_middle (p + 9).toNat (by omega)
        rwa [show -9 + (((p + 9).toNat : Nat) : Int) = p by omega] at this
  · simp only [sharpZ, show min (q - 1) (-9) ≤ -9 by omega, ↓reduceIte]

/-! ## Age 24 is sharp

Age 23 does not suffice for `two_step_predecessor_edge_from_age_twenty_four`. The configuration `X23`, black
at 0, 3, 4, 6, 7, 10, 11, 12 and 14, has at age 23 a predecessor `W23` of its image, and a predecessor `V23`
of `W23` that is black on all of `(-∞, -24]`, so `V23` has no leftmost black cell
(`two_step_predecessor_edge_fails_at_age_twenty_three`, `age_twenty_four_sharp`). `W23` has the true edge,
at `-22`, as the age-8 theorem requires; it is black on `[37, ∞)`, and `V23` repeats `001` from 36 on.

`evol` is computed through rows written as lists (`evol_listRow`): `listRow L lo` is the row whose cell
`lo + i` is entry `i` of `L`, white elsewhere, and `listStep` is one tick on such rows (`step_listRow`).
-/

/-! ### Rows as lists -/

/-- Entry `k` of `L`, white outside `0 ≤ k < L.length`. -/
def listGet (L : List Bool) (k : Int) : Bool := if 0 ≤ k then L.getD k.toNat false else false

/-- The row whose cell `lo + i` is entry `i` of `L`, white elsewhere. -/
def listRow (L : List Bool) (lo : Int) (p : Int) : Bool := listGet L (p - lo)

/-- One tick on a row written as a list; the row moves one cell left and grows by two. -/
def listStep (L : List Bool) : List Bool :=
  (List.range (L.length + 2)).map fun (i : Nat) =>
    rule (listGet L ((i : Int) - 2)) (listGet L ((i : Int) - 1)) (listGet L i)

theorem listGet_neg {L : List Bool} {k : Int} (h : k < 0) : listGet L k = false := by
  simp only [listGet, show ¬ (0 ≤ k) by omega, ↓reduceIte]

theorem listGet_ge {L : List Bool} {k : Int} (h : (L.length : Int) ≤ k) : listGet L k = false := by
  simp only [listGet, show 0 ≤ k by omega, ↓reduceIte]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

theorem length_listStep (L : List Bool) : (listStep L).length = L.length + 2 := by
  simp [listStep]

theorem listGet_listStep {L : List Bool} {k : Int} (h0 : 0 ≤ k) (h1 : k < L.length + 2) :
    listGet (listStep L) k = rule (listGet L (k - 2)) (listGet L (k - 1)) (listGet L k) := by
  have hk : k.toNat < L.length + 2 := by omega
  show (if 0 ≤ k then (listStep L).getD k.toNat false else false) = _
  simp only [h0, ↓reduceIte]
  rw [listStep, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  simp only [Option.map_some, Option.getD_some, Int.toNat_of_nonneg h0]

/-- **One tick on a list row.** -/
theorem step_listRow (L : List Bool) (lo p : Int) :
    rule (listRow L lo (p - 1)) (listRow L lo p) (listRow L lo (p + 1)) = listRow (listStep L) (lo - 1) p := by
  simp only [listRow]
  by_cases h0 : p - (lo - 1) < 0
  · rw [listGet_neg h0, listGet_neg (by omega), listGet_neg (by omega), listGet_neg (by omega)]
    rfl
  · by_cases h1 : p - (lo - 1) < L.length + 2
    · rw [listGet_listStep (by omega) h1, show p - (lo - 1) - 2 = p - 1 - lo by omega,
        show p - (lo - 1) - 1 = p - lo by omega, show p - (lo - 1) = p + 1 - lo by omega]
    · have hs : ((listStep L).length : Int) ≤ p - (lo - 1) := by rw [length_listStep]; push_cast; omega
      rw [listGet_ge hs, listGet_ge (by omega), listGet_ge (by omega), listGet_ge (by omega)]
      rfl

/-- `t` ticks on a list row. -/
def listIter : Nat → List Bool → List Bool
  | 0, L => L
  | t + 1, L => listStep (listIter t L)

/-- **`evol` on a list row**, tick by tick. -/
theorem evol_listRow (L : List Bool) (lo : Int) : ∀ (t : Nat) (p : Int),
    evol (listRow L lo) t p = listRow (listIter t L) (lo - t) p
  | 0, p => by simp [evol, listIter]
  | t + 1, p => by
    show rule (evol (listRow L lo) t (p - 1)) (evol (listRow L lo) t p) (evol (listRow L lo) t (p + 1)) = _
    rw [evol_listRow L lo t, evol_listRow L lo t, evol_listRow L lo t, step_listRow,
      show lo - (t : Int) - 1 = lo - ((t + 1 : Nat) : Int) by push_cast; omega]
    rfl

/-! ### The witness -/

/-- The seed, cells `0, …, 14`. -/
def seed23 : List Bool :=
  [true, false, false, true, true, false, true, true, false, false, true, true, true, false, true]

/-- Black at 0, 3, 4, 6, 7, 10, 11, 12 and 14. -/
def X23 : Int → Bool := listRow seed23 0

/-- Its row at age 23, cells `-23, …, 37`. -/
def R23 : List Bool :=
  [true, true, false, true, true, true, true, false, true, true, false, false, true, true, true, false, false,
    false, false, true, true, true, true, true, false, false, false, false, false, false, false, true, true,
    false, false, false, true, true, true, true, true, false, false, true, true, true, false, true, true, true,
    false, false, true, true, true, true, true, false, false, true, true]

theorem R23_eq : listIter 23 seed23 = R23 := by decide +kernel

/-- The middle of the one-step predecessor, cells `-22, …, 36`. -/
def W23mid : List Bool :=
  [true, false, true, false, false, true, false, true, false, false, false, false, true, false, false, false,
    false, false, false, true, false, false, true, true, true, true, true, true, true, false, true, false, false,
    false, false, false, true, false, false, true, true, true, false, false, true, true, false, false, true,
    true, false, true, false, false, true, false, false, false, false]

/-- A predecessor of `evol X23 23`: white on `(-∞, -23]`, black on `[37, ∞)`. -/
def W23 (p : Int) : Bool := if p ≤ -23 then false else if 37 ≤ p then true else W23mid.getD (p + 22).toNat false

/-- The middle of the two-step predecessor, cells `-23, …, 35`. -/
def V23mid : List Bool :=
  [false, true, false, true, true, false, true, false, true, true, true, true, false, true, true, true, true,
    true, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true,
    true, true, false, true, true, true, false, false, true, true, false, true, false, false, false, false,
    true, false, true, true, true, false, false, false, false]

/-- A predecessor of `W23`: black on `(-∞, -24]`, and `001` repeated from 36 on. -/
def V23 (p : Int) : Bool :=
  if p ≤ -24 then true else if 36 ≤ p then (p - 36) % 3 == 2 else V23mid.getD (p + 23).toNat false

theorem W23_middle : ∀ k : Nat, k < 61 →
    rule (W23 (-23 + k - 1)) (W23 (-23 + k)) (W23 (-23 + k + 1)) = listGet R23 k := by
  decide +kernel

theorem V23_middle : ∀ k : Nat, k < 61 →
    rule (V23 (-24 + k - 1)) (V23 (-24 + k)) (V23 (-24 + k + 1)) = W23 (-24 + k) := by
  decide +kernel

theorem X23_zero : X23 0 = true := by decide

theorem X23_left : ∀ p, p < 0 → X23 p = false := fun _ hp => listGet_neg (by omega)

theorem X23_right : ∀ p, 14 < p → X23 p = false := fun _ hp => listGet_ge (by simp only [seed23]; simp; omega)

theorem evol_X23 (p : Int) : evol X23 23 p = listGet R23 (p + 23) := by
  rw [X23, evol_listRow, R23_eq]
  simp only [listRow]
  congr 1

theorem W23_left {p : Int} (h : p ≤ -23) : W23 p = false := by simp [W23, h]

theorem W23_right {p : Int} (h : 37 ≤ p) : W23 p = true := by
  simp [W23, show ¬ p ≤ -23 by omega, h]

theorem V23_left {p : Int} (h : p ≤ -24) : V23 p = true := by simp [V23, h]

theorem V23_right {p : Int} (h : 36 ≤ p) : V23 p = ((p - 36) % 3 == 2) := by
  simp [V23, show ¬ p ≤ -24 by omega, h]

/-- `W23` is a predecessor of the image at age 23. -/
theorem W23_pred : ∀ p, rule (W23 (p - 1)) (W23 p) (W23 (p + 1)) = evol X23 23 p := by
  intro p
  by_cases h1 : p ≤ -24
  · rw [W23_left (p := p - 1) (by omega), W23_left (p := p) (by omega), W23_left (p := p + 1) (by omega),
      evol_eq_false_of_lt X23_left 23 p (by omega)]
    rfl
  · by_cases h2 : 38 ≤ p
    · rw [W23_right (p := p - 1) (by omega), W23_right (p := p) (by omega), W23_right (p := p + 1) (by omega),
        evol_eq_false_of_gt X23_right 23 p (by omega)]
      rfl
    · have hk := W23_middle (p + 23).toNat (by omega)
      rw [show (-23 : Int) + ((p + 23).toNat : Int) = p by omega] at hk
      rw [hk, evol_X23, Int.toNat_of_nonneg (by omega)]

/-- `V23` is a predecessor of `W23`. -/
theorem V23_pred : ∀ p, rule (V23 (p - 1)) (V23 p) (V23 (p + 1)) = W23 p := by
  intro p
  by_cases h1 : p ≤ -25
  · rw [V23_left (p := p - 1) (by omega), V23_left (p := p) (by omega), V23_left (p := p + 1) (by omega),
      W23_left (by omega)]
    rfl
  · by_cases h2 : 37 ≤ p
    · rw [V23_right (p := p - 1) (by omega), V23_right (p := p) (by omega), V23_right (p := p + 1) (by omega),
        W23_right h2]
      have h3 : (p - 1 - 36) % 3 = 0 ∨ (p - 1 - 36) % 3 = 1 ∨ (p - 1 - 36) % 3 = 2 := by omega
      rcases h3 with h | h | h
      · rw [h, show (p - 36) % 3 = 1 by omega, show (p + 1 - 36) % 3 = 2 by omega]
        rfl
      · rw [h, show (p - 36) % 3 = 2 by omega, show (p + 1 - 36) % 3 = 0 by omega]
        rfl
      · rw [h, show (p - 36) % 3 = 0 by omega, show (p + 1 - 36) % 3 = 1 by omega]
        rfl
    · have hk := V23_middle (p + 24).toNat (by omega)
      rw [show (-24 : Int) + ((p + 24).toNat : Int) = p by omega] at hk
      exact hk

/-- `V23` has no leftmost black cell. -/
theorem V23_no_left_edge : ∀ q : Int, ∃ p, p < q ∧ V23 p = true :=
  fun q => ⟨min (q - 1) (-24), by omega, V23_left (by omega)⟩

/-- `W23` has the true edge, `0 - 23 + 1`. -/
theorem W23_edge : W23 (-22) = true ∧ ∀ p, p < -22 → W23 p = false :=
  ⟨by decide, fun _ hp => W23_left (by omega)⟩

/-- **Age 23 fails.** A configuration with its leftmost black cell at 0 has, at age 23, a two-step
predecessor with no leftmost black cell. -/
theorem two_step_predecessor_edge_fails_at_age_twenty_three :
    X23 0 = true ∧ (∀ p, p < 0 → X23 p = false) ∧
    (∀ p, rule (W23 (p - 1)) (W23 p) (W23 (p + 1)) = evol X23 23 p) ∧
    (∀ p, rule (V23 (p - 1)) (V23 p) (V23 (p + 1)) = W23 p) ∧
    ∀ q : Int, ∃ p, p < q ∧ V23 p = true :=
  ⟨X23_zero, X23_left, W23_pred, V23_pred, V23_no_left_edge⟩

/-- **The age 24 of `two_step_predecessor_edge_from_age_twenty_four` is sharp:** its conclusion fails at 23. -/
theorem age_twenty_four_sharp : ¬ ∀ (x : Int → Bool) (lo : Int), x lo = true → (∀ p, p < lo → x p = false) →
    ∀ w v : Int → Bool, (∀ p, rule (w (p - 1)) (w p) (w (p + 1)) = evol x 23 p) →
      (∀ p, rule (v (p - 1)) (v p) (v (p + 1)) = w p) → ∀ p, p < lo - 23 + 2 → v p = false := by
  intro h
  have h' := h X23 0 X23_zero X23_left W23 V23 W23_pred V23_pred (-24) (by omega)
  rw [V23_left (by omega)] at h'
  exact absurd h' (by decide)

/-! ## The least ages -/

/-- The conclusion of `predecessor_edge_from_age_eight` at age `t`, for every configuration with a leftmost
black cell and every predecessor of its image. -/
def OneTickEdge (t : Nat) : Prop :=
  ∀ (x : Int → Bool) (lo : Int), x lo = true → (∀ p, p < lo → x p = false) →
    ∀ z : Int → Bool, (∀ p, rule (z (p - 1)) (z p) (z (p + 1)) = evol x t p) →
      z (lo - t + 1) = true ∧ ∀ p, p < lo - t + 1 → z p = false

/-- The conclusion of `two_step_predecessor_edge_from_age_twenty_four` at age `t`. -/
def TwoTickEdge (t : Nat) : Prop :=
  ∀ (x : Int → Bool) (lo : Int), x lo = true → (∀ p, p < lo → x p = false) →
    ∀ w v : Int → Bool, (∀ p, rule (w (p - 1)) (w p) (w (p + 1)) = evol x t p) →
      (∀ p, rule (v (p - 1)) (v p) (v (p + 1)) = w p) →
        v (lo - t + 2) = true ∧ ∀ p, p < lo - t + 2 → v p = false

/-- **8 is the least age.** The one-tick conclusion holds at every age from `a` on exactly when `8 ≤ a`. -/
theorem one_tick_least_age (a : Nat) : (∀ t, a ≤ t → OneTickEdge t) ↔ 8 ≤ a := by
  refine ⟨fun h => ?_, fun ha t ht x lo hlo hzero z hz =>
    predecessor_edge_from_age_eight hlo hzero t (by omega) z hz⟩
  rcases Nat.lt_or_ge a 8 with ha | ha
  · obtain ⟨h0, hl, hz, hb⟩ := predecessor_edge_fails_at_age_seven
    obtain ⟨p, hp, hpb⟩ := hb (-6)
    have h' := (h 7 (by omega) sharpX 0 h0 hl sharpZ hz).2 p (by omega)
    rw [hpb] at h'
    exact absurd h' (by decide)
  · exact ha

/-- **24 is the least age.** The two-tick conclusion holds at every age from `a` on exactly when `24 ≤ a`. -/
theorem two_tick_least_age (a : Nat) : (∀ t, a ≤ t → TwoTickEdge t) ↔ 24 ≤ a := by
  refine ⟨fun h => ?_, fun ha t ht x lo hlo hzero w v hw hv =>
    two_step_predecessor_edge_from_age_twenty_four hlo hzero t (by omega) w v hw hv⟩
  rcases Nat.lt_or_ge a 24 with ha | ha
  · have h' := (h 23 (by omega) X23 0 X23_zero X23_left W23 V23 W23_pred V23_pred).2 (-24) (by omega)
    rw [V23_left (p := -24) (by omega)] at h'
    exact absurd h' (by decide)
  · exact ha

end Ruliology.CellularAutomata.Rule30TwoSidedInverse
