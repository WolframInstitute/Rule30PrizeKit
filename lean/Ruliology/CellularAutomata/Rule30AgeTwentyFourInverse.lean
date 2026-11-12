module

public import Ruliology.CellularAutomata.Rule30AgeEightInverse

/-! A six-state top-band theorem at age 24 for the fixed-white-wall Rule 30 map.

The edge map, shift theorem, and backward transducer are imported from the
public Rule30LateTwins and pinned Rule30ZeroBoundary modules. The attributed
Rule30LateTwins source is pinned at commit 67283b1e66ca2d86a7c5e479cc2172e59845c96b.
The age-eight top-band result is imported from the separately checked local
Rule30AgeEightInverse module. -/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30AgeTwentyFourInverse

open Rule30ZeroBoundary Rule30ZeroBoundary.IntegerForm Rule30LateTwins Rule30AgeEightInverse

def EdgeGood20 (u : Nat) : Bool :=
  u == 820681 || u == 820683 || u == 822904 ||
  u == 911005 || u == 911007 || u == 912610

private theorem good20_iff {u : Nat} : EdgeGood20 u = true ↔
    u = 820681 ∨ u = 820683 ∨ u = 822904 ∨
    u = 911005 ∨ u = 911007 ∨ u = 912610 := by
  simp [EdgeGood20, Bool.or_eq_true, beq_iff_eq, or_assoc]

private theorem small24_base (Y : Nat) (hY : Y ≠ 0) (hsmall : Y < 2048) :
    EdgeGood20 ((iter F 24 Y) >>> (Y.log2 + 5)) = true := by
  have hc : chk (fun v => v == 0 ||
      EdgeGood20 ((iter F 24 v) >>> (v.log2 + 5))) 0 11 = true := by
    decide +kernel
  have h := chk_sound (fun v => v == 0 ||
    EdgeGood20 ((iter F 24 v) >>> (v.log2 + 5))) 11 0 hc Y (by omega)
  simpa [hY] using h

private theorem large24_base (u : Nat)
    (h8 : EdgeGood8 (u >>> 12) = true) : EdgeGood20 (iterR 16 u) = true := by
  have hc200 : chk (fun b => EdgeGood20 (iterR 16 (200 * 4096 + b))) 0 12 = true := by
    decide +kernel
  have hc222 : chk (fun b => EdgeGood20 (iterR 16 (222 * 4096 + b))) 0 12 = true := by
    decide +kernel
  have hsplit : u = (u >>> 12) * 4096 + u % 4096 := by
    rw [Nat.shiftRight_eq_div_pow]
    omega
  have hb : u % 4096 < 2 ^ 12 := Nat.mod_lt _ (by decide)
  rw [hsplit]
  simp only [EdgeGood8, Bool.or_eq_true, beq_iff_eq] at h8
  rcases h8 with h | h <;> rw [h]
  · simpa using chk_sound _ 12 0 hc200 (u % 4096) hb
  · simpa using chk_sound _ 12 0 hc222 (u % 4096) hb

private theorem EdgeGood20_R {u : Nat} (h : EdgeGood20 u = true) :
    EdgeGood20 (R u) = true := by
  rcases good20_iff.mp h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem EdgeGood20_iterR {u : Nat} (h : EdgeGood20 u = true) :
    ∀ d, EdgeGood20 (iterR d u) = true := by
  intro d
  induction d generalizing u with
  | zero => exact h
  | succ d ih => exact ih (EdgeGood20_R h)

theorem top20_from_age_twenty_four (Y t : Nat) (hY : Y ≠ 0) (ht : 24 ≤ t) :
    EdgeGood20 ((iter F t Y) >>> (Y.log2 + t - 19)) = true := by
  have h24 : EdgeGood20 ((iter F 24 Y) >>> (Y.log2 + 5)) = true := by
    by_cases hsmall : Y < 2048
    · exact small24_base Y hY hsmall
    · have hm : 11 ≤ Y.log2 := (Nat.le_log2 hY).2 (by omega : 2 ^ 11 ≤ Y)
      let q := Y.log2 - 11
      have hq : q + 12 = Y.log2 + 1 := by dsimp [q]; omega
      let X := iter F 8 Y
      have h8 : EdgeGood8 ((X >>> q) >>> 12) = true := by
        rw [← Nat.shiftRight_add, hq]
        exact top8_from_age_eight Y 8 hY (by decide)
      have htime : Y.log2 + 5 = q + 16 := by dsimp [q]; omega
      rw [show (24 : Nat) = 8 + 16 from rfl, iter_add F 8 16 Y, htime,
        iter_F_shiftRight]
      exact large24_base (X >>> q) h8
  obtain ⟨d, rfl⟩ : ∃ d, t = 24 + d := ⟨t - 24, by omega⟩
  have htime : Y.log2 + (24 + d) - 19 = (Y.log2 + 5) + d := by omega
  rw [htime, iter_add F 24 d Y, iter_F_shiftRight]
  exact EdgeGood20_iterR h24 d

/-! The inverse rule, expressed as a four-state transducer on adjacent bits. -/

private def pairStep (bit : Bool) (p : Bool × Bool) : Bool × Bool :=
  (p.2, xor bit (p.1 || p.2))

private def pairRun (word : Nat) (p : Bool × Bool) : Nat → Bool × Bool
  | 0 => p
  | n + 1 => pairStep (word.testBit n) (pairRun word p n)

private def parentProfile (word : Nat) : Nat :=
  if word == 820681 || word == 820683 || word == 822904 then 222 else 200

private theorem parentProfile_good {word : Nat} (h : EdgeGood20 word = true) :
    EdgeGood8 (parentProfile word) = true := by
  rcases good20_iff.mp h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem pairRun20_reset (word : Nat) (h : EdgeGood20 word = true)
    (a c : Bool) : pairRun word (a, c) 20 = (false, false) := by
  rcases good20_iff.mp h with rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases a <;> cases c <;> decide

private theorem pairRun20_parentProfile (word : Nat) (h : EdgeGood20 word = true)
    (a c : Bool) (i : Nat) (hi : i < 8) :
    (pairRun word (a, c) (11 + i)).2 = (parentProfile word).testBit i := by
  have hc : chk (fun j =>
      (pairRun word (a, c) (11 + j)).2 == (parentProfile word).testBit j) 0 3 = true := by
    rcases good20_iff.mp h with rfl | rfl | rfl | rfl | rfl | rfl <;>
      cases a <;> cases c <;> decide +kernel
  have ht := chk_sound _ 3 0 hc i (by omega)
  simpa only [Nat.zero_add, beq_iff_eq] using ht

private theorem pairRun8_reset (word : Nat) (h : EdgeGood8 word = true)
    (a c : Bool) : pairRun word (a, c) 8 = (false, false) := by
  simp only [EdgeGood8, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | rfl <;> cases a <;> cases c <;> decide

private theorem pairRun_back (word q n : Nat) (b : Bool) (y : Nat → Bool)
    (hbits : ∀ i, i < n → y (q + 1 + i) = word.testBit i) :
    pairRun word (back b y q, back b y (q + 1)) n =
      (back b y (q + n), back b y (q + n + 1)) := by
  induction n with
  | zero => simp [pairRun]
  | succ n ih =>
      have hn : ∀ i, i < n → y (q + 1 + i) = word.testBit i :=
        fun i hi => hbits i (by omega)
      rw [pairRun, ih hn]
      have hb : word.testBit n = y (q + n + 1) := by
        simpa only [show q + 1 + n = q + n + 1 by omega] using
          (hbits n (by omega)).symm
      rw [hb]
      simp only [pairStep, show q + (n + 1) = q + n + 1 by omega,
        back_succ_succ]
      rw [Bool.or_comm (back b y (q + n)) (back b y (q + n + 1))]

private theorem image_word_bit (Z q i : Nat) :
    rowOfNat Z (q + 1 + i) = (Z >>> q).testBit i := by
  rw [show q + 1 + i = (q + i) + 1 by omega, rowOfNat,
    Nat.testBit_shiftRight]

private theorem zrow_one_eq (X : Nat → Bool) (k : Nat) (hk : 1 ≤ k) :
    zrow X 1 (k + 1) = xor (X (k + 2)) (X (k + 1) || X k) := by
  have h := zrow_succ X 0 k
  simpa only [Nat.zero_add, zrow_zero_of_pos X (show 1 ≤ k + 2 by omega),
    zrow_zero_of_pos X (show 1 ≤ k + 1 by omega),
    zrow_zero_of_pos X hk] using h

private theorem predecessor_edge_from_reset
    (y X : Nat → Bool) (e : Nat) (he : 2 ≤ e)
    (hpre : ∀ k, 1 ≤ k → zrow X 1 k = y k)
    (hyedge : y e = true) (hywhite : ∀ k, e < k → y k = false)
    (h0 : X e = false) (h1 : X (e + 1) = false) :
    X (e - 1) = true ∧ ∀ k, e - 1 < k → X k = false := by
  have hp : ∀ d, X (e + d) = false ∧ X (e + d + 1) = false := by
    intro d
    induction d with
    | zero => simpa using And.intro h0 h1
    | succ d ih =>
        refine ⟨by simpa [Nat.add_assoc] using ih.2, ?_⟩
        have hstep := hpre (e + d + 1) (by omega)
        rw [show e + d + 1 = (e + d) + 1 by omega,
          zrow_one_eq X (e + d) (by omega), ih.1, ih.2,
          hywhite (e + d + 1) (by omega)] at hstep
        simpa [Nat.add_assoc] using hstep
  have htail : ∀ k, e ≤ k → X k = false := by
    intro k hk
    have heq : e + (k - e) = k := by omega
    rw [← heq]
    exact (hp (k - e)).1
  have hstep : y e = xor (X (e + 1)) (X e || X (e - 1)) := by
    have h := hpre e (by omega)
    rw [show e = (e - 1) + 1 by omega,
      zrow_one_eq X (e - 1) (by omega)] at h
    simpa only [show e - 1 + 2 = e + 1 by omega,
      show e - 1 + 1 = e by omega] using h.symm
  have hedge : X (e - 1) = true := by
    rw [h0, h1, hyedge] at hstep
    simpa using hstep.symm
  exact ⟨hedge, fun k hk => htail k (by omega)⟩

/-- Every two-step predecessor of the age-`t` image of a nonzero finite
zero-wall row has the exact edge two cells behind the image edge, once
`t ≥ 24`. Both intermediate rows may initially be infinite. -/
theorem aged_image_two_step_predecessor_true_edge
    (Y t : Nat) (hY : Y ≠ 0) (ht : 24 ≤ t)
    (X V : Nat → Bool)
    (hX : ∀ k, 1 ≤ k → zrow X 1 k = rowOfNat (iter F t Y) k)
    (hV : ∀ k, 1 ≤ k → zrow V 1 k = X k) :
    V (Y.log2 + t - 1) = true ∧
    ∀ k, Y.log2 + t - 1 < k → V k = false := by
  let m := Y.log2
  let Z := iter F t Y
  let y := rowOfNat Z
  let q := m + t - 19
  let e := m + t + 1
  let word := Z >>> q
  let r := q + 11
  let profile := parentProfile word
  have hq : q + 20 = e := by dsimp [q, e, m]; omega
  have hr : r + 8 = e - 1 := by dsimp [r, q, e, m]; omega
  have he : 2 ≤ e := by dsimp [e, m]; omega
  have he2 : 2 ≤ e - 1 := by omega
  have hgood : EdgeGood20 word = true :=
    top20_from_age_twenty_four Y t hY ht
  have hprofile : EdgeGood8 profile = true := parentProfile_good hgood
  have hbit (i : Nat) : y (q + 1 + i) = word.testBit i :=
    image_word_bit Z q i
  have hXback : ∀ k, 1 ≤ k → X k = back (X 1) y k := by
    intro k hk
    have h := eq_back (L := X) (y := y) hX k
    rwa [zrow_zero_of_pos X hk] at h
  have hVback : ∀ k, 1 ≤ k → V k = back (V 1) X k := by
    intro k hk
    have h := eq_back (L := V) (y := X) hV k
    rwa [zrow_zero_of_pos V hk] at h
  have hpair20 := pairRun20_reset word hgood
    (back (X 1) y q) (back (X 1) y (q + 1))
  have hrun20 := pairRun_back word q 20 (X 1) y
    (fun i _ => hbit i)
  rw [hrun20] at hpair20
  have hXreset : X e = false ∧ X (e + 1) = false := by
    have h0 : back (X 1) y (q + 20) = false := by
      simpa using congrArg Prod.fst hpair20
    have h1 : back (X 1) y (q + 21) = false := by
      simpa using congrArg Prod.snd hpair20
    constructor
    · rw [← hq, hXback (q + 20) (by omega)]
      exact h0
    · rw [show e + 1 = q + 21 by omega, hXback (q + 21) (by omega)]
      exact h1
  have htop : Top Z (m + t) := Top_iter (top_log2 hY) t
  have hyedge : y e = true := by
    simpa only [y, e, m, rowOfNat] using htop.1
  have hywhite : ∀ k, e < k → y k = false := by
    intro k hk
    obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
    have hi : m + t < i := by dsimp [e] at hk; omega
    exact htop.2 i hi
  have hXedge := predecessor_edge_from_reset y X e he hX hyedge hywhite
    hXreset.1 hXreset.2
  have hparentbit : ∀ i, i < 8 → X (r + 1 + i) = profile.testBit i := by
    intro i hi
    have htable := pairRun20_parentProfile word hgood
      (back (X 1) y q) (back (X 1) y (q + 1)) i hi
    have hrun := pairRun_back word q (11 + i) (X 1) y
      (fun j _ => hbit j)
    rw [hrun] at htable
    have hindex : r + 1 + i = q + (11 + i) + 1 := by
      dsimp [r]; omega
    rw [hindex, hXback (q + (11 + i) + 1) (by omega)]
    exact htable
  have hpair8 := pairRun8_reset profile hprofile
    (back (V 1) X r) (back (V 1) X (r + 1))
  have hrun8 := pairRun_back profile r 8 (V 1) X
    (fun i hi => hparentbit i hi)
  rw [hrun8] at hpair8
  have hVreset : V (e - 1) = false ∧ V e = false := by
    constructor
    · rw [← hr, hVback (r + 8) (by omega)]
      simpa using congrArg Prod.fst hpair8
    · rw [show e = r + 9 by omega, hVback (r + 9) (by omega)]
      simpa using congrArg Prod.snd hpair8
  have hVedge := predecessor_edge_from_reset X V (e - 1) he2 hV
    hXedge.1 hXedge.2 hVreset.1 hVreset.2
  have hclock : e - 1 - 1 = m + t - 1 := by dsimp [e, m] <;> omega
  rw [hclock] at hVedge
  exact hVedge

/-- Physical-row version with the original fixed white wall and actual
last black site `m`; the predecessor is arbitrary before the theorem. -/
theorem finite_row_aged_image_two_step_predecessor_true_edge
    {L : Nat → Bool} {m t : Nat}
    (hm : 1 ≤ m) (hedge : L m = true)
    (hfin : ∀ k, m < k → L k = false) (ht : 24 ≤ t)
    (V : Nat → Bool)
    (hpre : ∀ k, 1 ≤ k → zrow V 2 k = zrow L t k) :
    V (m + t - 2) = true ∧
    ∀ k, m + t - 2 < k → V k = false := by
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
  have hlog : Y.log2 = m - 1 := Top_unique (top_log2 hY) htop
  let X := zrow V 1
  have hX : ∀ k, 1 ≤ k → zrow X 1 k = rowOfNat (iter F t Y) k := by
    intro k hk
    have hrow : ∀ j, 1 ≤ j → L j = rowOfNat Y j :=
      fun j hj => (rowOfNat_natOfRow hfin j hj).symm
    calc
      zrow X 1 k = zrow V 2 k := by
        simpa only [X] using (zrow_shift V 1 1 k).symm
      _ = zrow L t k := hpre k hk
      _ = zrow (rowOfNat Y) t k := zrow_congr hrow t k
      _ = rowOfNat (iter F t Y) k := zrow_rowOfNat Y t k
  have hV : ∀ k, 1 ≤ k → zrow V 1 k = X k := by
    intro k _
    rfl
  have hNat := aged_image_two_step_predecessor_true_edge Y t hY ht X V hX hV
  have hclock : m + t - 2 = Y.log2 + t - 1 := by rw [hlog]; omega
  rw [hclock]
  exact hNat

#print axioms top20_from_age_twenty_four
#print axioms aged_image_two_step_predecessor_true_edge
#print axioms finite_row_aged_image_two_step_predecessor_true_edge

/-! ### Top-band cycle structure, sharpening `band_late` to age 26 and `late_twin` to age 25, 2-bit predecessor dichotomy, and backward finite-edge inheritance for `Theta` -/

/-- **Strict Period-`2` Oscillation of `EdgeGood8` Under `R` (`EdgeGood8_period_two`):**
every state `u` with `EdgeGood8 u = true` (`u ∈ {200, 222}`) satisfies `R u ≠ u` and
`iterR 2 u = u`. -/
theorem EdgeGood8_period_two {u : Nat} (h : EdgeGood8 u = true) :
    R u ≠ u ∧ iterR 2 u = u := by
  simp only [EdgeGood8, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | rfl <;> decide

/-- **Two-Step Entry of `EdgeGood20` Into the Four-Cycle `C20` (`EdgeGood20_two_step_inC20`):**
for every `u` with `EdgeGood20 u = true`, two steps `iterR 2 u` lie in the four-cycle `inC20`
(`820683, 822904, 911005, 912610`) and satisfy `R (iterR 2 u) ≠ iterR 2 u` and
`iterR 6 u = iterR 2 u`. -/
theorem EdgeGood20_two_step_inC20 {u : Nat} (h : EdgeGood20 u = true) :
    inC20 (iterR 2 u) = true ∧ R (iterR 2 u) ≠ iterR 2 u ∧ iterR 6 u = iterR 2 u := by
  rcases good20_iff.mp h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- **Sharpened Top-`20` Four-Cycle Settling at Age `26` (`band_from_age_twenty_six`):**
for every nonzero `y` and every `t ≥ 26` (sharpening `Rule30LateTwins.band_late` from `45` down
to `26`), the top twenty cells of `iter F t y` lie on `C20`. -/
theorem band_from_age_twenty_six {y : Nat} (hy : y ≠ 0) {t : Nat} (ht : 26 ≤ t) :
    inC20 (iter F t y >>> (y.log2 + t - 19)) = true := by
  obtain ⟨d, rfl⟩ : ∃ d, t = (24 + d) + 2 := ⟨t - 26, by omega⟩
  have hgood := top20_from_age_twenty_four y (24 + d) hy (by omega)
  have hshift : iter F ((24 + d) + 2) y >>> (y.log2 + ((24 + d) + 2) - 19) =
      iterR 2 (iter F (24 + d) y >>> (y.log2 + (24 + d) - 19)) := by
    rw [iter_add F (24 + d) 2 y,
      show y.log2 + ((24 + d) + 2) - 19 = (y.log2 + (24 + d) - 19) + 2 by omega,
      iter_F_shiftRight]
  rw [hshift]
  exact (EdgeGood20_two_step_inC20 hgood).1

/-- **Stacked Reset Factors Across All Six States of `EdgeGood20` (`chains_edgeGood20`):**
every state `c` with `EdgeGood20 c = true` carries a reset factor in `c` and a deeper reset
factor in `R c`. -/
theorem chains_edgeGood20 (c : Nat) (hc : EdgeGood20 c = true) :
    ∃ i1 k1 i2 k2, Fac c i1 k1 ∧ Fac (R c) i2 k2 ∧ i2 + 3 * k2 + 4 ≤ i1 := by
  rcases good20_iff.mp hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨14, 0, 6, 0, ⟨Or.inl rfl, by decide⟩, ⟨Or.inl rfl, by decide⟩, by decide⟩
  · exact ⟨14, 0, 6, 0, ⟨Or.inl rfl, by decide⟩, ⟨Or.inl rfl, by decide⟩, by decide⟩
  · exact ⟨14, 0, 0, 0, ⟨Or.inl rfl, by decide⟩, ⟨Or.inl rfl, by decide⟩, by decide⟩
  · exact ⟨12, 1, 2, 1, ⟨Or.inr rfl, by decide⟩, ⟨Or.inr rfl, by decide⟩, by decide⟩
  · exact ⟨12, 1, 2, 1, ⟨Or.inr rfl, by decide⟩, ⟨Or.inr rfl, by decide⟩, by decide⟩
  · exact ⟨12, 1, 2, 0, ⟨Or.inr rfl, by decide⟩, ⟨Or.inl rfl, by decide⟩, by decide⟩

/-- **Sharpened Late Twin Existence From Age `25` (`twin_from_age_twenty_five`):**
for every nonzero natural `y` and every `t ≥ 25` (sharpening `Rule30LateTwins.late_twin` from
`46` down to `25`), the row `x = iter F (t - 2) y` has a twin `x' ≠ x` of the same width, with
the same bit `0` and `F (F x') = iter F t y`. -/
theorem twin_from_age_twenty_five {y : Nat} (hy : y ≠ 0) {t : Nat} (ht : 25 ≤ t) :
    ∃ x', x' ≠ iter F (t - 2) y ∧ x'.testBit 0 = (iter F (t - 2) y).testBit 0 ∧
      F (F x') = iter F t y ∧ Top x' (y.log2 + (t - 2)) := by
  have e1 : iter F (t - 1) y = F (iter F (t - 2) y) := by
    rw [show t - 1 = (t - 2) + 1 by omega]; rfl
  have e2 : iter F t y = F (F (iter F (t - 2) y)) := by
    rw [← e1, show t = (t - 1) + 1 by omega]; rfl
  obtain ⟨c, hc⟩ : ∃ c, iter F (t - 1) y >>> (y.log2 + (t - 1) - 19) = c := ⟨_, rfl⟩
  have hin : EdgeGood20 c = true := hc ▸ top20_from_age_twenty_four y (t - 1) hy (by omega)
  obtain ⟨i1, k1, i2, k2, f1, f2, hi⟩ := chains_edgeGood20 c hin
  have b1 : ∀ j, (iter F (t - 1) y).testBit ((y.log2 + (t - 1) - 19) + i1 + j) = c.testBit (i1 + j) := by
    intro j
    rw [← hc, Nat.testBit_shiftRight, Nat.add_assoc]
  have b2 : ∀ j, (F (iter F (t - 1) y)).testBit ((y.log2 + (t - 1) - 19) + 1 + i2 + j) =
      (R c).testBit (i2 + j) := by
    intro j
    rw [← hc, ← F_shiftRight, Nat.testBit_shiftRight, Nat.add_assoc, Nat.add_assoc]
  have g1 := fac_transfer b1 f1
  have g2 := fac_transfer b2 f2
  rw [e1] at g1 g2
  obtain ⟨x', hne, hb0, hF⟩ := twin_of_factors g2 g1 (by omega)
  refine ⟨x', hne, hb0, by rw [hF, e2], ?_⟩
  have hx'0 : x' ≠ 0 := by
    intro h0
    have hT := Top_iter (top_log2 hy) t
    rw [e2, ← hF, h0, IntegerForm.F_zero, IntegerForm.F_zero] at hT
    exact absurd hT.1 (by rw [Nat.zero_testBit]; decide)
  have hT' := Top_iter (top_log2 hx'0) 2
  have hT2 := Top_iter (top_log2 hy) t
  rw [e2, ← hF] at hT2
  have : x'.log2 + 2 = y.log2 + t := Top_unique hT' hT2
  rw [show y.log2 + (t - 2) = x'.log2 by omega]
  exact top_log2 hx'0

/-- **Sharpened Off-Orbit Immortal Twins From Even Age `26` (`twin_off_orbit_from_age_twenty_six`):**
if `y` never reaches an even value under `G` and `t ≥ 26` is even (sharpening
`Rule30LateTwins.late_twin_off_orbit` from `46` down to `26`), there exists `x'` off the `G`-orbit
of `y` (`∀ j, x' ≠ iter G j y`) such that `G x' = iter F t y` and `∀ s, iter G s x' % 2 = 1`. -/
theorem twin_off_orbit_from_age_twenty_six {y : Nat} (hy : ∀ s, iter G s y % 2 = 1)
    {t : Nat} (ht : 26 ≤ t) (he : t % 2 = 0) :
    ∃ x', (∀ s, iter G s x' % 2 = 1) ∧ G x' = iter F t y ∧ ∀ j, x' ≠ iter G j y := by
  have hy0 : y ≠ 0 := by
    intro h
    have := hy 0
    rw [h] at this
    exact absurd this (by decide)
  obtain ⟨x', hne, hb0, hF, hT⟩ := twin_from_age_twenty_five (t := t) hy0 (by omega)
  refine ⟨x', ?_, hF, fun j hj => ?_⟩
  · intro s
    cases s with
    | zero =>
      have h := hy ((t - 2) / 2)
      rw [iter_G_eq_iter_F_two_mul, show 2 * ((t - 2) / 2) = t - 2 by omega] at h
      show x' % 2 = 1
      rw [odd_iff_testBit, hb0, ← odd_iff_testBit]
      exact h
    | succ s =>
      rw [iter_succ']
      have hG : G x' = iter G (t / 2) y := by
        rw [iter_G_eq_iter_F_two_mul, show 2 * (t / 2) = t by omega]
        exact hF
      rw [hG, ← iter_add]
      exact hy _
  · have hTj := Top_iter (top_log2 hy0) (2 * j)
    rw [← iter_G_eq_iter_F_two_mul, ← hj] at hTj
    have : y.log2 + (t - 2) = y.log2 + 2 * j := Top_unique hT hTj
    apply hne
    rw [hj, iter_G_eq_iter_F_two_mul, show 2 * j = t - 2 by omega]

/-- **Unique 1-Bit Parameterization of One-Step Predecessors (`predecessor_unique_of_bit1`):**
if `X` and `X'` are one-step predecessors of the same row `y` on `k ≥ 1` and agree at depth `1`
(`X 1 = X' 1`), then `X k = X' k` for all `k ≥ 1`. -/
theorem predecessor_unique_of_bit1 {y X X' : Nat → Bool}
    (hX : ∀ k, 1 ≤ k → zrow X 1 k = y k)
    (hX' : ∀ k, 1 ≤ k → zrow X' 1 k = y k)
    (h1 : X 1 = X' 1) :
    ∀ k, 1 ≤ k → X k = X' k := by
  intro k hk
  have e1 := eq_back (L := X) (y := y) hX k
  have e2 := eq_back (L := X') (y := y) hX' k
  rw [zrow_zero_of_pos X hk] at e1
  rw [zrow_zero_of_pos X' hk] at e2
  rw [e1, e2, h1]

/-- **Unique 2-Bit Parameterization of Two-Step Predecessors (`two_step_predecessor_unique_of_bits`):**
if `V` and `V'` are two-step predecessors of the same row `y` on `k ≥ 1` (`zrow V 2 k = y k` and
`zrow V' 2 k = y k`) with `V 1 = V' 1` and `zrow V 1 1 = zrow V' 1 1`, then `V k = V' k` for
all `k ≥ 1`. -/
theorem two_step_predecessor_unique_of_bits {y V V' : Nat → Bool}
    (hV : ∀ k, 1 ≤ k → zrow V 2 k = y k)
    (hV' : ∀ k, 1 ≤ k → zrow V' 2 k = y k)
    (h0 : V 1 = V' 1)
    (h1 : zrow V 1 1 = zrow V' 1 1) :
    ∀ k, 1 ≤ k → V k = V' k := by
  have hmid : ∀ k, 1 ≤ k → zrow V 1 k = zrow V' 1 k := by
    refine predecessor_unique_of_bit1 (y := y)
      (fun k hk => ?_) (fun k hk => ?_) h1
    · rw [← zrow_shift V 1 1 k]; exact hV k hk
    · rw [← zrow_shift V' 1 1 k]; exact hV' k hk
  exact predecessor_unique_of_bit1 (y := zrow V' 1) hmid (fun _ _ => rfl) h0

/-- **Backward True-Edge Inheritance for `Theta f` From Any Age-`24` Finite Image
(`theta_true_edge_of_shift_eq_aged_image`):** if `L` has last black cell `m ≥ 1` and for some
`t ≥ 24` the shifted reconstruction `Theta (fun s => f (s + 1))` agrees on `k ≥ 1` with `zrow L t`,
then `Theta f` itself has exact last black cell `m + t - 2` and is finitely supported. -/
theorem theta_true_edge_of_shift_eq_aged_image {L f : Nat → Bool} {m t : Nat}
    (hm : 1 ≤ m) (hedge : L m = true) (hfin : ∀ k, m < k → L k = false) (ht : 24 ≤ t)
    (hshift : ∀ k, 1 ≤ k → Theta (fun s => f (s + 1)) k = zrow L t k) :
    Theta f (m + t - 2) = true ∧
    (∀ k, m + t - 2 < k → Theta f k = false) ∧
    FinSupp (Theta f) := by
  have hpre : ∀ k, 1 ≤ k → zrow (Theta f) 2 k = zrow L t k := by
    intro k hk
    rw [congrFun (two_step_shift f) k]
    exact hshift k hk
  obtain ⟨htrue, htail⟩ :=
    finite_row_aged_image_two_step_predecessor_true_edge hm hedge hfin ht (Theta f) hpre
  exact ⟨htrue, htail, ⟨m + t - 2, htail⟩⟩

/-- **Disjointness of Infinite `Theta f` Starts From Shifted Age-`24` Finite Images
(`not_theta_shift_eq_aged_image_of_not_finSupp`):** if `¬ FinSupp (Theta f)`, then for every
finite row `L` with last black cell `m ≥ 1` and every age `t ≥ 24`, `Theta (fun s => f (s + 1))`
cannot agree with `zrow L t` on `k ≥ 1`. -/
theorem not_theta_shift_eq_aged_image_of_not_finSupp {L f : Nat → Bool} {m t : Nat}
    (hinf : ¬ FinSupp (Theta f)) (hm : 1 ≤ m) (hedge : L m = true)
    (hfin : ∀ k, m < k → L k = false) (ht : 24 ≤ t) :
    ¬ ∀ k, 1 ≤ k → Theta (fun s => f (s + 1)) k = zrow L t k := by
  intro hshift
  exact hinf (theta_true_edge_of_shift_eq_aged_image hm hedge hfin ht hshift).2.2

end Ruliology.CellularAutomata.Rule30AgeTwentyFourInverse
