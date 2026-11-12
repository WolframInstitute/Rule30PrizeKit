module

public import Ruliology.CellularAutomata.Rule30LateTwins

/-! Age-eight top-band reset for the zero-wall left Rule 30 map. -/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30AgeEightInverse

open Rule30ZeroBoundary Rule30ZeroBoundary.IntegerForm Rule30LateTwins

def EdgeGood8 (u : Nat) : Bool := u == 200 || u == 222

private theorem good_iff {u : Nat} : EdgeGood8 u = true ↔ u = 200 ∨ u = 222 := by
  simp [EdgeGood8, Bool.or_eq_true, beq_iff_eq]

private theorem top8_base (u : Nat) (hlo : 128 ≤ u) (hhi : u < 256) : EdgeGood8 (iterR 8 u) = true := by
  have hc : chk (fun v => EdgeGood8 (iterR 8 v)) 128 7 = true := by decide +kernel
  have h := chk_sound (fun v => EdgeGood8 (iterR 8 v)) 7 128 hc (u - 128) (by omega)
  simpa only [show 128 + (u - 128) = u by omega] using h

private theorem small8_base (u : Nat) (hu : u ≠ 0) (hhi : u < 128) :
    EdgeGood8 ((iter F 8 u) >>> (u.log2 + 1)) = true := by
  have hc : chk (fun v => v == 0 || EdgeGood8 ((iter F 8 v) >>> (v.log2 + 1))) 0 7 = true := by
    decide +kernel
  have h := chk_sound (fun v => v == 0 || EdgeGood8 ((iter F 8 v) >>> (v.log2 + 1))) 7 0 hc u (by omega)
  simpa [EdgeGood8, hu] using h

private theorem EdgeGood8_R {u : Nat} (h : EdgeGood8 u = true) : EdgeGood8 (R u) = true := by
  rcases good_iff.mp h with rfl | rfl <;> decide

private theorem EdgeGood8_iterR {u : Nat} (h : EdgeGood8 u = true) : ∀ d, EdgeGood8 (iterR d u) = true := by
  intro d
  induction d generalizing u with
  | zero => exact h
  | succ d ih => exact ih (EdgeGood8_R h)

private theorem top8_at_age8 (Y : Nat) (hY : Y ≠ 0) :
    EdgeGood8 ((iter F 8 Y) >>> (Y.log2 + 1)) = true := by
  by_cases hsmall : Y < 128
  · exact small8_base Y hY hsmall
  · have h7 : 7 ≤ Y.log2 := (Nat.le_log2 hY).2 (by omega : 2 ^ 7 ≤ Y)
    let q := Y.log2 - 7
    have hq : Y.log2 = q + 7 := by dsimp [q]; omega
    have hp7 : 2 ^ Y.log2 = 128 * 2 ^ q := by
      rw [hq, Nat.pow_add, show (2 : Nat) ^ 7 = 128 by decide, Nat.mul_comm]
    have hp8 : 2 ^ (Y.log2 + 1) = 256 * 2 ^ q := by
      rw [show Y.log2 + 1 = q + 8 by omega, Nat.pow_add,
        show (2 : Nat) ^ 8 = 256 by decide, Nat.mul_comm]
    have hulo : 128 ≤ Y >>> q := by
      rw [Nat.shiftRight_eq_div_pow, Nat.le_div_iff_mul_le (Nat.pow_pos (by decide))]
      rw [← hp7]
      exact Nat.log2_self_le hY
    have huhi : Y >>> q < 256 := by
      rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))]
      rw [← hp8]
      exact Nat.lt_log2_self
    rw [show Y.log2 + 1 = q + 8 by omega, iter_F_shiftRight]
    exact top8_base (Y >>> q) hulo huhi

theorem top8_from_age_eight (Y t : Nat) (hY : Y ≠ 0) (ht : 8 ≤ t) :
    EdgeGood8 ((iter F t Y) >>> (Y.log2 + t - 7)) = true := by
  obtain ⟨d, rfl⟩ : ∃ d, t = 8 + d := ⟨t - 8, by omega⟩
  have htime : Y.log2 + (8 + d) - 7 = (Y.log2 + 1) + d := by omega
  rw [htime, Rule30LateTwins.iter_add F 8 d Y, iter_F_shiftRight]
  exact EdgeGood8_iterR (top8_at_age8 Y hY) d

private theorem image_suffix_bit (Z q i : Nat) :
    rowOfNat Z (q + 1 + i) = (Z >>> q).testBit i := by
  rw [show q + 1 + i = (q + i) + 1 by omega, rowOfNat, Nat.testBit_shiftRight]

theorem back_reset_at_top8 (Z q : Nat) (h : EdgeGood8 (Z >>> q) = true) (b : Bool) :
    back b (rowOfNat Z) (q + 8) = false ∧
    back b (rowOfNat Z) (q + 9) = false := by
  let y := rowOfNat Z
  have hy (i : Nat) : y (q + 1 + i) = (Z >>> q).testBit i := image_suffix_bit Z q i
  rcases good_iff.mp h with hw | hw
  · have h2 : y (q + 3) = false := by simpa [hw, Nat.add_assoc, show (200 : Nat).testBit 2 = false by decide] using hy 2
    have h3 : y (q + 4) = true := by simpa [hw, Nat.add_assoc, show (200 : Nat).testBit 3 = true by decide] using hy 3
    have h4 : y (q + 5) = false := by simpa [hw, Nat.add_assoc, show (200 : Nat).testBit 4 = false by decide] using hy 4
    have h5 : y (q + 6) = false := by simpa [hw, Nat.add_assoc, show (200 : Nat).testBit 5 = false by decide] using hy 5
    have h6 : y (q + 7) = true := by simpa [hw, Nat.add_assoc, show (200 : Nat).testBit 6 = true by decide] using hy 6
    have h7 : y (q + 8) = true := by simpa [hw, Nat.add_assoc, show (200 : Nat).testBit 7 = true by decide] using hy 7
    have hr := reset0 b y (q + 2) (by simpa [Nat.add_assoc] using h2)
      (by simpa [Nat.add_assoc] using h3) (by simpa [Nat.add_assoc] using h4)
    have h6b : back b y (q + 6) = true := by simpa [Nat.add_assoc] using hr.1
    have h7b : back b y (q + 7) = true := by simpa [Nat.add_assoc, h5] using hr.2
    have h8b : back b y (q + 8) = false := by
      rw [show q + 8 = (q + 6) + 2 by omega, back_succ_succ]
      simp [show q + 6 + 1 = q + 7 by omega, h6, h6b, h7b]
    have h9b : back b y (q + 9) = false := by
      rw [show q + 9 = (q + 7) + 2 by omega, back_succ_succ]
      simp [show q + 7 + 1 = q + 8 by omega, h7, h7b, h8b]
    exact ⟨h8b, h9b⟩

  · have h0 : y (q + 1) = false := by simpa [hw, Nat.add_assoc, show (222 : Nat).testBit 0 = false by decide] using hy 0
    have h1 : y (q + 2) = true := by simpa [hw, Nat.add_assoc, show (222 : Nat).testBit 1 = true by decide] using hy 1
    have h2 : y (q + 3) = true := by simpa [hw, Nat.add_assoc, show (222 : Nat).testBit 2 = true by decide] using hy 2
    have h3 : y (q + 4) = true := by simpa [hw, Nat.add_assoc, show (222 : Nat).testBit 3 = true by decide] using hy 3
    have h4 : y (q + 5) = true := by simpa [hw, Nat.add_assoc, show (222 : Nat).testBit 4 = true by decide] using hy 4
    have h5 : y (q + 6) = false := by simpa [hw, Nat.add_assoc, show (222 : Nat).testBit 5 = false by decide] using hy 5
    have h6 : y (q + 7) = true := by simpa [hw, Nat.add_assoc, show (222 : Nat).testBit 6 = true by decide] using hy 6
    have h7 : y (q + 8) = true := by simpa [hw, Nat.add_assoc, show (222 : Nat).testBit 7 = true by decide] using hy 7
    have hr := reset1 b y q (by simpa [Nat.add_assoc] using h0)
      (by simpa [Nat.add_assoc] using h1) (by simpa [Nat.add_assoc] using h2)
      (by simpa [Nat.add_assoc] using h3) (by simpa [Nat.add_assoc] using h4)
      (by simpa [Nat.add_assoc] using h5)
    have h7b : back b y (q + 7) = true := by simpa [Nat.add_assoc] using hr.1
    have h8b : back b y (q + 8) = false := by simpa [Nat.add_assoc, h6] using hr.2
    have h9b : back b y (q + 9) = false := by
      rw [show q + 9 = (q + 7) + 2 by omega, back_succ_succ]
      simp [show q + 7 + 1 = q + 8 by omega, h7, h7b, h8b]
    exact ⟨h8b, h9b⟩

private theorem back_zero_from_top8 (b : Bool) (y : Nat → Bool) (q : Nat)
    (hwhite : ∀ k, q + 9 ≤ k → y k = false)
    (h0 : back b y (q + 8) = false) (h1 : back b y (q + 9) = false) :
    ∀ k, q + 8 ≤ k → back b y k = false := by
  have hp : ∀ d, back b y (q + 8 + d) = false ∧
      back b y (q + 8 + d + 1) = false := by
    intro d
    induction d with
    | zero => simpa using And.intro h0 h1
    | succ d ih =>
        refine ⟨by simpa [Nat.add_assoc] using ih.2, ?_⟩
        rw [show q + 8 + (d + 1) + 1 = (q + 8 + d) + 2 by omega,
          back_succ_succ,
          hwhite (q + 8 + d + 1) (by omega), ih.1, ih.2]
        rfl
  intro k hk
  have he : q + 8 + (k - (q + 8)) = k := by omega
  rw [← he]
  exact (hp (k - (q + 8))).1

/-- Every one-step predecessor of the age-`t` image of a nonzero finite
zero-wall row is finite once `t ≥ 8`. The predecessor is allowed to be an
arbitrary infinite Boolean row before the theorem is applied. -/
theorem aged_image_all_predecessors_finite (Y t : Nat) (hY : Y ≠ 0) (ht : 8 ≤ t)
    (X : Nat → Bool)
    (hpre : ∀ k, 1 ≤ k → zrow X 1 k = rowOfNat (iter F t Y) k) :
    FinSupp X := by
  let m := Y.log2
  let q := m + t - 7
  let Z := iter F t Y
  let y := rowOfNat Z
  have htop : Top Z (m + t) := Top_iter (top_log2 hY) t
  have hwhite : ∀ k, q + 9 ≤ k → y k = false := by
    intro k hk
    obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
    have hi : m + t < i := by dsimp [q] at hk; omega
    exact htop.2 i hi
  have hgood : EdgeGood8 (Z >>> q) = true := top8_from_age_eight Y t hY ht
  have hreset := back_reset_at_top8 Z q hgood (X 1)
  have hfinback : FinSupp (back (X 1) y) :=
    (back_fin_iff (X 1) (n := q + 9) (by omega) hwhite).2
      (by simpa only [show q + 9 - 1 = q + 8 by omega] using hreset)
  obtain ⟨W, hW⟩ := hfinback
  refine ⟨W, ?_⟩
  intro k hk
  have hrec := eq_back (L := X) (y := y) hpre k
  rw [zrow_zero_of_pos X (by omega)] at hrec
  rw [hrec]
  exact hW k hk

/-- The same predecessor has the exact last black depth `Y.log2 + t`.
This uses the true moving edge, rather than merely a support bound. -/
theorem aged_image_predecessor_true_edge (Y t : Nat) (hY : Y ≠ 0) (ht : 8 ≤ t)
    (X : Nat → Bool)
    (hpre : ∀ k, 1 ≤ k → zrow X 1 k = rowOfNat (iter F t Y) k) :
    X (Y.log2 + t) = true ∧
    ∀ k, Y.log2 + t < k → X k = false := by
  let m := Y.log2
  let q := m + t - 7
  let Z := iter F t Y
  let y := rowOfNat Z
  have htop : Top Z (m + t) := Top_iter (top_log2 hY) t
  have hwhite : ∀ k, q + 9 ≤ k → y k = false := by
    intro k hk
    obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
    have hi : m + t < i := by dsimp [q] at hk; omega
    exact htop.2 i hi
  have hgood : EdgeGood8 (Z >>> q) = true := top8_from_age_eight Y t hY ht
  obtain ⟨h0, h1⟩ := back_reset_at_top8 Z q hgood (X 1)
  have hbacktail := back_zero_from_top8 (X 1) y q hwhite h0 h1
  have hXtail : ∀ k, q + 8 ≤ k → X k = false := by
    intro k hk
    have hrec := eq_back (L := X) (y := y) hpre k
    rw [zrow_zero_of_pos X (by omega)] at hrec
    rw [hrec]
    exact hbacktail k hk
  have hq : q + 8 = m + t + 1 := by dsimp [q]; omega
  have hx1 : X (m + t + 1) = false := hXtail _ (by omega)
  have hx2 : X (m + t + 2) = false := hXtail _ (by omega)
  have hyTop : y (m + t + 1) = true := htop.1
  have hz2 : zrow X 0 (m + t + 2) = X (m + t + 2) :=
    zrow_zero_of_pos X (by omega)
  have hz1 : zrow X 0 (m + t + 1) = X (m + t + 1) :=
    zrow_zero_of_pos X (by omega)
  have hz0 : zrow X 0 (m + t) = X (m + t) :=
    zrow_zero_of_pos X (by omega)
  have hstep : zrow X 1 (m + t + 1) =
      xor (X (m + t + 2)) (X (m + t + 1) || X (m + t)) := by
    simpa only [Nat.zero_add, hz2, hz1, hz0] using zrow_succ X 0 (m + t)
  have hedge : X (m + t) = true := by
    have heq := hpre (m + t + 1) (by omega)
    rw [hstep, hx1, hx2] at heq
    have heq2 : X (m + t) = y (m + t + 1) := by simpa using heq
    rw [hyTop] at heq2
    exact heq2
  refine ⟨hedge, ?_⟩
  intro k hk
  exact hXtail k (by omega)

/-- Physical-row form: if `L` has actual last black depth `m`, then every
predecessor of its age-`t` image has actual last black depth `m+t-1` once
`t ≥ 8`. No finiteness assumption is made on the predecessor. -/
theorem finite_row_aged_image_all_predecessors_true_edge
    {L : Nat → Bool} {m t : Nat}
    (hm : 1 ≤ m) (hedge : L m = true)
    (hfin : ∀ k, m < k → L k = false) (ht : 8 ≤ t)
    (X : Nat → Bool) (hpre : ∀ k, 1 ≤ k → zrow X 1 k = zrow L t k) :
    X (m + t - 1) = true ∧ ∀ k, m + t - 1 < k → X k = false := by
  let Y := natOfRow L m
  have hbit : Y.testBit (m - 1) = true := by
    rw [testBit_natOfRow]
    simp [show m - 1 < m by omega, show m - 1 + 1 = m by omega, hedge]
  have hY : Y ≠ 0 := by
    intro hzero
    subst Y
    simp [hzero] at hbit
  have htop : Top Y (m - 1) := by
    refine ⟨hbit, ?_⟩
    intro i hi
    rw [testBit_natOfRow]
    have hge : m ≤ i := by omega
    simp [show ¬ i < m by omega]
  have hlog : Y.log2 = m - 1 := (Top_unique (top_log2 hY) htop)
  have hpreNat : ∀ k, 1 ≤ k → zrow X 1 k = rowOfNat (iter F t Y) k := by
    intro k hk
    have hrow : ∀ j, 1 ≤ j → L j = rowOfNat Y j :=
      fun j hj => (rowOfNat_natOfRow hfin j hj).symm
    calc
      zrow X 1 k = zrow L t k := hpre k hk
      _ = zrow (rowOfNat Y) t k := zrow_congr hrow t k
      _ = rowOfNat (iter F t Y) k := zrow_rowOfNat Y t k
  obtain ⟨he, htail⟩ := aged_image_predecessor_true_edge Y t hY ht X hpreNat
  have hclock : m + t - 1 = Y.log2 + t := by rw [hlog]; omega
  rw [hclock]
  exact ⟨he, htail⟩

#print axioms top8_from_age_eight
#print axioms back_reset_at_top8
#print axioms aged_image_all_predecessors_finite
#print axioms aged_image_predecessor_true_edge
#print axioms finite_row_aged_image_all_predecessors_true_edge

/-! ### Constructive two-branch 1-step predecessors, exact two-branch equivalence, outer synchronization, and unique `InX` predecessor at age 8 -/

/-- **Constructive Two-Branch True-Edge Theorem at Age `8` (`back_aged_image_true_edge`):**
for any finite row `L` with last black cell `m ≥ 1`, any age `t ≥ 8`, and either initial wall bit
`b : Bool`, the backward transducer run `back b (zrow L t)` is a one-step predecessor of `zrow L t`
with exact last black depth `m + t - 1`. -/
theorem back_aged_image_true_edge {L : Nat → Bool} {m t : Nat}
    (hm : 1 ≤ m) (hedge : L m = true) (hfin : ∀ k, m < k → L k = false) (ht : 8 ≤ t) (b : Bool) :
    (∀ k, 1 ≤ k → zrow (back b (zrow L t)) 1 k = zrow L t k) ∧
    back b (zrow L t) (m + t - 1) = true ∧
    ∀ k, m + t - 1 < k → back b (zrow L t) k = false := by
  have hpre : ∀ k, 1 ≤ k → zrow (back b (zrow L t)) 1 k = zrow L t k :=
    fun k hk => zrow_back b (zrow L t) k hk
  exact ⟨hpre,
    finite_row_aged_image_all_predecessors_true_edge hm hedge hfin ht (back b (zrow L t)) hpre⟩

/-- **Exact Two-Branch Characterization of All One-Step Predecessors
(`predecessor_iff_eq_back_false_or_true`):** for any row `y : Nat → Bool` and any sequence
`X : Nat → Bool`, `zrow X 1` agrees with `y` on `k ≥ 1` if and only if `X` agrees on `k ≥ 1`
with either `back false y` or `back true y`. -/
theorem predecessor_iff_eq_back_false_or_true (y X : Nat → Bool) :
    (∀ k, 1 ≤ k → zrow X 1 k = y k) ↔
      (∀ k, 1 ≤ k → X k = back false y k) ∨ (∀ k, 1 ≤ k → X k = back true y k) := by
  constructor
  · intro hpre
    cases hb : X 1
    · left
      intro k hk
      have h := eq_back (L := X) (y := y) hpre k
      rwa [zrow_zero_of_pos X hk, hb] at h
    · right
      intro k hk
      have h := eq_back (L := X) (y := y) hpre k
      rwa [zrow_zero_of_pos X hk, hb] at h
  · rintro (hf | ht) k hk
    · rw [zrow_congr hf 1 k, zrow_back false y k hk]
    · rw [zrow_congr ht 1 k, zrow_back true y k hk]

/-- **Outer Synchronization of `back false` and `back true` From the True Edge Onward
(`back_false_eq_back_true_from_edge`):** for any finite row `L` with last black cell `m ≥ 1` and
age `t ≥ 8`, `back false (zrow L t)` and `back true (zrow L t)` agree at every depth
`k ≥ m + t - 1`. -/
theorem back_false_eq_back_true_from_edge {L : Nat → Bool} {m t : Nat}
    (hm : 1 ≤ m) (hedge : L m = true) (hfin : ∀ k, m < k → L k = false) (ht : 8 ≤ t)
    {k : Nat} (hk : m + t - 1 ≤ k) :
    back false (zrow L t) k = back true (zrow L t) k := by
  have hf := (back_aged_image_true_edge hm hedge hfin ht false).2
  have htr := (back_aged_image_true_edge hm hedge hfin ht true).2
  by_cases heq : k = m + t - 1
  · subst heq; rw [hf.1, htr.1]
  · rw [hf.2 k (by omega), htr.2 k (by omega)]

/-- **Unique `InX` One-Step Predecessor and Exact Edge at Age `8`
(`inX_predecessor_aged_image_unique_and_true_edge`):** if `X` is in `InX` and `zrow X 1` agrees
on `k ≥ 1` with `zrow L t` (`m ≥ 1, t ≥ 8`), then `X k = back true (zrow L t) k` for all `k ≥ 1`
and `X` has exact last black depth `m + t - 1`. -/
theorem inX_predecessor_aged_image_unique_and_true_edge {L X : Nat → Bool} {m t : Nat}
    (hm : 1 ≤ m) (hedge : L m = true) (hfin : ∀ k, m < k → L k = false) (ht : 8 ≤ t)
    (hX : InX X) (hpre : ∀ k, 1 ≤ k → zrow X 1 k = zrow L t k) :
    (∀ k, 1 ≤ k → X k = back true (zrow L t) k) ∧
    X (m + t - 1) = true ∧
    ∀ k, m + t - 1 < k → X k = false := by
  refine ⟨fun k hk => ?_,
    finite_row_aged_image_all_predecessors_true_edge hm hedge hfin ht X hpre⟩
  have h := eq_back (L := X) (y := zrow L t) hpre k
  have hX1 : X 1 = true := by
    have h0 := hX 0
    rwa [Nat.mul_zero, zrow_zero_of_pos X (Nat.le_refl 1)] at h0
  rwa [zrow_zero_of_pos X hk, hX1] at h

end Ruliology.CellularAutomata.Rule30AgeEightInverse
