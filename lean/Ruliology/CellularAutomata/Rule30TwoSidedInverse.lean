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

end Ruliology.CellularAutomata.Rule30TwoSidedInverse
