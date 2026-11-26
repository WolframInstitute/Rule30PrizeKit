module

public import Ruliology.CellularAutomata.Rule30DrivenLeft
public import Ruliology.CellularAutomata.Rule30TwoSidedInverse

/-!
# Inverse ticks beside a prescribed wall

The wall is at site 0, and the driven cells have negative indices. A finite start
whose leftmost black cell is at `-m` has a good eight-cell edge band by age 8
when `m ≥ 2`, and by age 9 when `m = 1`. The wall may follow any Boolean
sequence. In a predecessor its own value at site 0 can be chosen independently.
The corresponding two-tick ages are 24 and 25.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30DrivenLeftInverse

open Rule30Jen Rule30DrivenLeft Rule30TwoSidedInverse Rule30AgeEightInverse
  Rule30AgeTwentyFourInverse Rule30LateTwins

/-- The edge position at age `t` when the initial edge is at depth `m`. -/
def edgePosition (m t : Nat) : Int := -(m : Int) - t

/-- Read a bit of a finite word, edge first, with white outside the word. -/
private def readWord (width u : Nat) (j : Int) : Bool :=
  if 0 ≤ j ∧ j < width then u.testBit (width - 1 - j.toNat) else false

private theorem readWord_band (width : Nat) (f : Int → Bool) {j : Int}
    (hj : 0 ≤ j) (hk : j < width) :
    readWord width (band f 0 width) j = f j := by
  rw [readWord, ite_eq_left ⟨hj, hk⟩, testBit_band_lt _ _ _ _ (by omega)]
  congr 1
  omega

/-- In moving coordinates, keep the cells through the wall and white to its right. -/
private def clip (depth : Nat) (row : Int → Bool) (j : Int) : Bool :=
  if j ≤ depth then row j else false

private def edgeRow (c : Nat → Bool) (s : Int → Bool) (m t : Nat) (j : Int) : Bool :=
  L c s t (edgePosition m t + j)

private def tape (c : Nat → Bool) (s : Int → Bool) (m : Nat) (j : Int) : Bool :=
  if j < m then s (edgePosition m 0 + j) else c (j - m).toNat

private def updateWord (width depth input current : Nat) : Nat :=
  band (fun j => if j < depth then stepLine (readWord width current) (j - 1)
    else if j = depth then readWord width input j else false) 0 width

private def runWord (width m input : Nat) : Nat → Nat
  | 0 => band (clip m (readWord width input)) 0 width
  | t + 1 => updateWord width (m + t + 1) input (runWord width m input t)

private theorem edge_at (c : Nat → Bool) (s : Int → Bool) {m : Nat}
    (hm : 0 < m) (h₀ : ∀ p, p < -(m : Int) → s p = false) (h₁ : s (-(m : Int)) = true)
    (t : Nat) : (∀ p, p < edgePosition m t → L c s t p = false) ∧ L c s t (edgePosition m t) = true := by
  have eq : edgePosition m t = -((m + t : Nat) : Int) := by unfold edgePosition; omega
  rw [eq]
  exact Rule30DrivenLeft.edge (c := c) h₀ h₁ hm t

private theorem runWord_spec (c : Nat → Bool) (s : Int → Bool) {m : Nat}
    (hm : 0 < m) (h₀ : ∀ p, p < -(m : Int) → s p = false) (h₁ : s (-(m : Int)) = true)
    (width t : Nat) :
    runWord width m (band (tape c s m) 0 width) t =
      band (clip (m + t) (edgeRow c s m t)) 0 width := by
  induction t with
  | zero =>
    simp only [runWord, Nat.add_zero]
    apply band_congr
    intro j hj
    simp only [Int.zero_add, clip]
    split
    · rw [readWord_band _ _ (by omega) (by omega)]
      simp only [tape, edgeRow]
      by_cases h : (j : Int) < m
      · rw [ite_eq_left h, L_zero (by unfold edgePosition; omega)]
      · have e : (j : Int) = m := by omega
        rw [e, ite_eq_right (by omega), show (m : Int) - m = 0 by omega,
          show edgePosition m 0 + (m : Int) = 0 by unfold edgePosition; omega, L_col0]
        rfl
    · rfl
  | succ t ih =>
    simp only [runWord, updateWord, ih]
    apply band_congr
    intro j hj
    simp only [Int.zero_add, clip]
    by_cases h : (j : Int) < ↑(m + t + 1)
    · rw [ite_eq_left h, ite_eq_left (by omega)]
      have read (i : Int) (hi : i ≤ j) (hl : j - 2 ≤ i) :
          readWord width (band (clip (m + t) (edgeRow c s m t)) 0 width) i = edgeRow c s m t i := by
        by_cases hp : 0 ≤ i
        · rw [readWord_band _ _ hp (by omega), clip, ite_eq_left (by omega)]
        · rw [readWord, ite_eq_right (by omega), edgeRow,
            (edge_at c s hm h₀ h₁ t).1 _ (by omega)]
      simp only [stepLine, edgeRow] at *
      rw [read _ (by omega) (by omega), read _ (by omega) (by omega), read _ (by omega) (by omega)]
      have hl : edgePosition m (t + 1) + (j : Int) < 0 := by unfold edgePosition; omega
      rw [L_succ hl]
      have hf : edgePosition m (t + 1) = edgePosition m t - 1 := by unfold edgePosition; omega
      rw [hf]
      congr 1 <;> congr 1 <;> omega
    · rw [ite_eq_right h]
      by_cases he : (j : Int) = ↑(m + t + 1)
      · rw [ite_eq_left he, ite_eq_left (by omega), readWord_band _ _ (by omega) (by omega)]
        rw [tape, ite_eq_right (by omega), edgeRow,
          show edgePosition m (t + 1) + (j : Int) = 0 by unfold edgePosition; omega, L_col0]
        congr 1
        omega
      · rw [ite_eq_right he, ite_eq_right (by omega)]

/-- The value of the width-dependent uniform age. -/
def threshold (m : Nat) : Nat := if m = 1 then 9 else 8

private theorem narrowTable :
    ∀ (width : Fin 7) (input : Fin 128),
      EdgeGood8 (runWord 8 (width.val + 1) (128 + input.val) (threshold (width.val + 1))) = true := by
  decide +kernel

private theorem stable (u : Nat) (h : EdgeGood8 u = true) : EdgeGood8 (R u) = true := by
  simp only [EdgeGood8, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | rfl <;> decide

private theorem band_next (c : Nat → Bool) (s : Int → Bool) {m : Nat}
    (hm : 0 < m) (h₀ : ∀ p, p < -(m : Int) → s p = false) (h₁ : s (-(m : Int)) = true)
    (width t : Nat) (wide : width ≤ m + t) :
    band (L c s (t + 1)) (edgePosition m (t + 1)) width = R (band (L c s t) (edgePosition m t) width) := by
  rw [← band_step _ _ _ (edge_at c s hm h₀ h₁ t).1]
  apply band_congr
  intro j hj
  have h : edgePosition m (t + 1) + (j : Int) = edgePosition m t - 1 + (j : Int) := by unfold edgePosition; omega
  rw [h, L_succ (by unfold edgePosition; omega)]
  rfl

private theorem band_interior (c : Nat → Bool) (s : Int → Bool) (m width t : Nat) (h : width ≤ m + t) :
    band (clip (m + t) (edgeRow c s m t)) 0 width = band (L c s t) (edgePosition m t) width := by
  apply band_congr
  intro j hj
  simp only [Int.zero_add, clip, edgeRow]
  rw [ite_eq_left (by omega)]

/-- At the claimed age and every later age, the driven half enters Hughes's good bands. -/
theorem good_band_of_age (c : Nat → Bool) (s : Int → Bool) {m : Nat}
    (hm : 0 < m) (h₀ : ∀ p, p < -(m : Int) → s p = false) (h₁ : s (-(m : Int)) = true)
    (t : Nat) (ht : threshold m ≤ t) :
    EdgeGood8 (band (L c s t) (edgePosition m t) 8) = true := by
  have threshold_ge : 8 ≤ threshold m := by unfold threshold; split <;> omega
  by_cases wide : 8 ≤ m
  · have eq (a : Nat) : band (L c s a) (edgePosition m a) 8 =
        iterR a (band (L c s 0) (edgePosition m 0) 8) := by
      induction a with
      | zero => rfl
      | succ a ih => rw [band_next c s hm h₀ h₁ 8 a (by omega), ih, Rule30LateTwins.iterR_succ']
    rw [eq]
    let u := band (L c s 0) (edgePosition m 0) 8
    have htop : 2 ^ 7 ≤ u := band_top _ _ (edge_at c s hm h₀ h₁ 0).2 7
    have hlt : u < 256 := band_lt _ _ _
    have hne : u ≠ 0 := by omega
    have hlog : u.log2 = 7 := (Nat.log2_eq_iff hne).2 ⟨htop, hlt⟩
    have hh := top8_from_age_eight u t hne (by omega)
    rw [hlog, show 7 + t - 7 = 0 + t by omega, iter_F_shiftRight] at hh
    simpa using hh
  · have tape0 : tape c s m 0 = true := by
      rw [tape, ite_eq_left (by omega), show edgePosition m 0 + 0 = -(m : Int) by unfold edgePosition; omega, h₁]
    let u := band (tape c s m) 0 8
    have hlo : 128 ≤ u := band_top _ _ tape0 7
    have hhi : u < 256 := band_lt _ _ _
    have entry := narrowTable ⟨m - 1, by omega⟩ ⟨u - 128, by omega⟩
    change EdgeGood8 (runWord 8 (m - 1 + 1) (128 + (u - 128)) (threshold (m - 1 + 1))) = true at entry
    rw [show m - 1 + 1 = m by omega, show 128 + (u - 128) = u by omega,
      runWord_spec c s hm h₀ h₁, band_interior c s m 8 _ (by omega)] at entry
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
    clear ht
    induction d with
    | zero => simpa using entry
    | succ d ih =>
      change EdgeGood8 (band (L c s (threshold m + d + 1)) (edgePosition m (threshold m + d + 1)) 8) = true
      rw [band_next c s hm h₀ h₁ 8 _ (by omega)]
      exact stable _ ih

/-- An inverse image on the driven half has the exact left edge from the stated age.
The local equation is required only at negative positions. In particular, the
predecessor's bit at the wall is arbitrary. -/
theorem predecessor_edge (c : Nat → Bool) (s z : Int → Bool) {m t : Nat}
    (hm : 0 < m) (h₀ : ∀ p, p < -(m : Int) → s p = false) (h₁ : s (-(m : Int)) = true)
    (ht : threshold m ≤ t) (hz : ∀ p, p < 0 → stepLine z p = L c s t p) :
    z (-(m : Int) - t + 1) = true ∧ ∀ p, p < -(m : Int) - t + 1 → z p = false := by
  have h8 : 8 ≤ t := by unfold threshold at ht; split at ht <;> omega
  have edge := edge_at c s hm h₀ h₁ t
  have eq : band (stepLine z) (edgePosition m t) 8 = band (L c s t) (edgePosition m t) 8 := by
    apply band_congr
    intro j hj
    exact hz _ (by unfold edgePosition; omega)
  exact predecessor_edge_of_good8 (stepLine z) z (fun _ => rfl) (edgePosition m t)
    (by rw [hz _ (by unfold edgePosition; omega)]; exact edge.2)
    (fun p hp => (hz p (by unfold edgePosition at hp; omega)).trans (edge.1 p hp))
    (by rw [eq]; exact good_band_of_age c s hm h₀ h₁ t ht)

/-! ## Sharpness, including with the prescribed predecessor wall -/

private def exampleDepth (adjacent : Bool) : Nat := if adjacent then 1 else 2

private def exampleAge (adjacent : Bool) : Nat := if adjacent then 8 else 7

private def exampleWall (adjacent : Bool) (t : Nat) : Bool := adjacent && (t == 2)

private def exampleSeed (adjacent : Bool) (p : Int) : Bool := p == -(exampleDepth adjacent : Int)

/-- Both examples have this predecessor. Its west tail is black and its wall bit is white. -/
private def cofinite (p : Int) : Bool :=
  decide (p ≤ -11) || (p == -9) || (p == -5) || (p == -2)

private theorem example_middle : ∀ (adjacent : Bool) (j : Fin 9),
    stepLine cofinite (-9 + (j.val : Int)) =
      L (exampleWall adjacent) (exampleSeed adjacent) (exampleAge adjacent) (-9 + (j.val : Int)) := by
  decide +kernel

private theorem example_predecessor (adjacent : Bool) (p : Int) (hp : p < 0) :
    stepLine cofinite p = L (exampleWall adjacent) (exampleSeed adjacent) (exampleAge adjacent) p := by
  by_cases hlo : p < -9
  · have cf (q : Int) (hq : q ≤ -11) : cofinite q = true := by simp [cofinite, hq]
    have hz : ∀ q, q < -(exampleDepth adjacent : Int) → exampleSeed adjacent q = false := by
      intro q hq
      simp [exampleSeed, show q ≠ -(exampleDepth adjacent : Int) by omega]
    have hb : exampleSeed adjacent (-(exampleDepth adjacent : Int)) = true := by simp [exampleSeed]
    have hm : 0 < exampleDepth adjacent := by cases adjacent <;> decide
    have he : edgePosition (exampleDepth adjacent) (exampleAge adjacent) = -9 := by
      cases adjacent <;> decide
    have hw := (edge_at (exampleWall adjacent) (exampleSeed adjacent) hm hz hb
      (exampleAge adjacent)).1
    rw [he] at hw
    rw [hw p hlo]
    by_cases hh : p ≤ -12
    · rw [stepLine, cf (p - 1) (by omega), cf p (by omega), cf (p + 1) (by omega)]
      rfl
    · have hp' : p = -11 ∨ p = -10 := by omega
      rcases hp' with rfl | rfl <;> decide
  · let j : Fin 9 := ⟨(p + 9).toNat, by omega⟩
    have e : -9 + (j.val : Int) = p := by dsimp [j]; omega
    simpa only [e] using example_middle adjacent j

/-- At the last age below each bound there is a predecessor with no leftmost black
cell, even when its wall bit equals the actual wall at the predecessor's time.
The two cases have initial edge depths 1 and 2, respectively. -/
theorem sharp_examples (adjacent : Bool) :
    ∃ (c : Nat → Bool) (s z : Int → Bool),
      let m : Nat := if adjacent then 1 else 2
      let t : Nat := if adjacent then 8 else 7
      s (-(m : Int)) = true ∧ (∀ p, p < -(m : Int) → s p = false) ∧
      z 0 = c (t - 1) ∧ (∀ p, p < 0 → stepLine z p = L c s t p) ∧
      ∀ q, ∃ p, p < q ∧ z p = true := by
  refine ⟨exampleWall adjacent, exampleSeed adjacent, cofinite, ?_⟩
  change exampleSeed adjacent (-(exampleDepth adjacent : Int)) = true ∧
    (∀ p, p < -(exampleDepth adjacent : Int) → exampleSeed adjacent p = false) ∧
    cofinite 0 = exampleWall adjacent (exampleAge adjacent - 1) ∧
    (∀ p, p < 0 → stepLine cofinite p =
      L (exampleWall adjacent) (exampleSeed adjacent) (exampleAge adjacent) p) ∧
    ∀ q, ∃ p, p < q ∧ cofinite p = true
  refine ⟨by simp [exampleSeed], ?_, ?_, example_predecessor adjacent, ?_⟩
  · intro p hp
    simp [exampleSeed, show p ≠ -(exampleDepth adjacent : Int) by omega]
  · cases adjacent <;> decide
  · intro q
    refine ⟨min (q - 1) (-11), by omega, ?_⟩
    simp [cofinite, show min (q - 1) (-11) ≤ -11 by omega]

/-- The exact one-tick edge at a given initial depth and age, with any forward wall
and with the predecessor also allowed to choose its own wall bit. -/
def EdgeAt (m t : Nat) : Prop :=
  ∀ (c : Nat → Bool) (s z : Int → Bool), s (-(m : Int)) = true →
    (∀ p, p < -(m : Int) → s p = false) →
    (∀ p, p < 0 → stepLine z p = L c s t p) →
    z (edgePosition m t + 1) = true ∧ ∀ p, p < edgePosition m t + 1 → z p = false

/-- Age 8 is the least uniform age for initial depth at least 2. -/
theorem least_age_nonadjacent (a : Nat) :
    (∀ m, 2 ≤ m → ∀ t, a ≤ t → EdgeAt m t) ↔ 8 ≤ a := by
  constructor
  · intro h
    by_cases ha : 8 ≤ a
    · exact ha
    · obtain ⟨c, s, z, hs, hw, _, hz, hb⟩ := sharp_examples false
      obtain ⟨p, hp, hblack⟩ := hb (edgePosition 2 7 + 1)
      have hwhite := (h 2 (by decide) 7 (by omega) c s z hs hw hz).2 p hp
      rw [hblack] at hwhite
      contradiction
  · intro ha m hm t ht c s z hs hw hz
    exact predecessor_edge c s z (by omega) hw hs
      (by unfold threshold; rw [ite_eq_right (by omega)]; omega) hz

/-- Age 9 is the least uniform age for a single black cell next to the wall. -/
theorem least_age_adjacent (a : Nat) :
    (∀ t, a ≤ t → EdgeAt 1 t) ↔ 9 ≤ a := by
  constructor
  · intro h
    by_cases ha : 9 ≤ a
    · exact ha
    · obtain ⟨c, s, z, hs, hw, _, hz, hb⟩ := sharp_examples true
      obtain ⟨p, hp, hblack⟩ := hb (edgePosition 1 8 + 1)
      have hwhite := (h 8 (by omega) c s z hs hw hz).2 p hp
      rw [hblack] at hwhite
      contradiction
  · intro ha t ht c s z hs hw hz
    exact predecessor_edge c s z (by decide) hw hs (by change 9 ≤ t; omega) hz

/-! ## Packed computation of the twenty-cell bands -/

private def keepHigh (u cut : Nat) : Nat := u >>> cut <<< cut

private theorem bit_keepHigh (u cut i : Nat) :
    (keepHigh u cut).testBit i = (decide (cut ≤ i) && u.testBit i) := by
  simp only [keepHigh, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, ge_iff_le]
  by_cases h : cut ≤ i
  · rw [show cut + (i - cut) = i by omega]
  · simp [h]

private theorem band_readWord (width u : Nat) (hu : u < 2 ^ width) :
    band (readWord width u) 0 width = u := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < width
  · rw [testBit_band_lt _ _ _ _ hi, readWord, ite_eq_left ⟨by omega, by omega⟩,
      show width - 1 - (0 + (width : Int) - 1 - (i : Int)).toNat = i by omega]
  · rw [testBit_band_ge _ _ _ _ (by omega)]
    exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hu
      (Nat.pow_le_pow_right (by decide) (by omega)))).symm

private theorem band_clip (width depth : Nat) (row : Int → Bool) :
    band (clip depth row) 0 width = keepHigh (band row 0 width) (width - (depth + 1)) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [bit_keepHigh]
  by_cases hi : i < width
  · rw [testBit_band_lt _ _ _ _ hi, testBit_band_lt _ _ _ _ hi, clip]
    by_cases h : 0 + (width : Int) - 1 - (i : Int) ≤ (depth : Int)
    · rw [ite_eq_left h]; simp [show width - (depth + 1) ≤ i by omega]
    · rw [ite_eq_right h]; simp [show ¬ width - (depth + 1) ≤ i by omega]
  · rw [testBit_band_ge _ _ _ _ (by omega), testBit_band_ge _ _ _ _ (by omega)]
    simp

/-- Clear the inner bits and supply the next wall bit, if it still lies in the band. -/
private def putWall (width depth input row : Nat) : Nat :=
  keepHigh row (width - depth) |||
    (if depth < width then input &&& 2 ^ (width - 1 - depth) else 0)

private theorem band_putWall (width depth : Nat) (row input : Int → Bool) :
    band (fun j => if j < depth then row j else if j = depth then input j else false) 0 width =
      putWall width depth (band input 0 width) (band row 0 width) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [putWall, Nat.testBit_or, bit_keepHigh]
  by_cases hi : i < width
  · rw [testBit_band_lt _ _ _ _ hi, testBit_band_lt _ _ _ _ hi]
    let j := 0 + (width : Int) - 1 - (i : Int)
    change (if j < (depth : Int) then row j else if j = (depth : Int) then input j else false) = _
    have hj : j < width := by dsimp [j]; omega
    have hl : width - depth ≤ i ↔ j < (depth : Int) := by dsimp [j]; omega
    have he (hd : depth < width) : width - 1 - depth = i ↔ j = (depth : Int) := by
      dsimp [j]; omega
    by_cases hd : depth < width
    · rw [ite_eq_left hd, Nat.testBit_and, Nat.testBit_two_pow, testBit_band_lt _ _ _ _ hi]
      by_cases h : j < (depth : Int)
      · simp [h, hl.mpr h, show ¬ width - 1 - depth = i from fun e => (by omega : j ≠ (depth : Int)) ((he hd).mp e)]
        exact congrArg row (by dsimp [j]; omega)
      · by_cases eq : j = (depth : Int)
        · simp [eq, show ¬ width - depth ≤ i from fun e => h (hl.mp e), (he hd).mpr eq]
          exact congrArg input (by dsimp [j] at eq; omega)
        · simp [h, eq, show ¬ width - depth ≤ i from fun e => h (hl.mp e),
            show ¬ width - 1 - depth = i from fun e => eq ((he hd).mp e)]
    · simp [hd, show j < (depth : Int) by omega, show width - depth ≤ i by omega]
      exact congrArg row (by dsimp [j]; omega)
  · rw [testBit_band_ge _ _ _ _ (by omega), testBit_band_ge _ _ _ _ (by omega)]
    by_cases hd : depth < width
    · rw [ite_eq_left hd, Nat.testBit_and, testBit_band_ge _ _ _ _ (by omega)]
      simp
    · simp [hd]

private theorem updateWord_fast (width depth input current : Nat)
    (hi : input < 2 ^ width) (hc : current < 2 ^ width) :
    updateWord width depth input current = putWall width depth input (R current) := by
  unfold updateWord
  rw [band_putWall, band_readWord _ _ hi]
  congr 1
  calc
    _ = band (stepLine (readWord width current)) (-1) width := by
      apply band_congr
      intro j _
      congr 1
      omega
    _ = R current := by
      rw [show (-1 : Int) = 0 - 1 by decide, band_step]
      · rw [band_readWord _ _ hc]
      · intro p hp
        simp [readWord, show ¬ 0 ≤ p by omega]

private def runFast (width depth input : Nat) : Nat → Nat
  | 0 => keepHigh input (width - (depth + 1))
  | t + 1 => putWall width (depth + t + 1) input (R (runFast width depth input t))

private theorem runFast_eq (width depth input : Nat) (hi : input < 2 ^ width) :
    ∀ t, runFast width depth input t = runWord width depth input t
  | 0 => by rw [runFast, runWord, band_clip, band_readWord _ _ hi]
  | t + 1 => by
    rw [runFast, runWord, runFast_eq width depth input hi, updateWord_fast _ _ _ _ hi]
    cases t <;> exact band_lt _ _ _

private theorem runFast_wide (width depth input : Nat) (h : width ≤ depth) :
    ∀ t, runFast width depth input t = iterR t input
  | 0 => by simp [runFast, keepHigh, iterR, show width - (depth + 1) = 0 by omega]
  | t + 1 => by
    rw [runFast, runFast_wide width depth input h t, Rule30LateTwins.iterR_succ']
    simp [putWall, keepHigh, show width - (depth + t + 1) = 0 by omega,
      show ¬ depth + t + 1 < width by omega]

private def checkStage (good : Nat → Bool) (width depth head tailBits time : Nat) : Bool :=
  chk (fun tail => good (runFast width depth (head * 2 ^ tailBits + tail) time)) 0 tailBits

-- Six ticks from either good eight-cell band put the top thirteen cells in C13.
private theorem table13 : ∀ depth : Fin 4,
    (checkStage inC13 13 (depth.val + 10) 200 5 6 &&
     checkStage inC13 13 (depth.val + 10) 222 5 6) = true := by decide +kernel

-- Ten more ticks from C13 give a good twenty-cell band, with every continuation.
private theorem table20 : ∀ depth : Fin 5,
    (checkStage EdgeGood20 20 (depth.val + 16) 6411 7 10 &&
     checkStage EdgeGood20 20 (depth.val + 16) 6428 7 10 &&
     checkStage EdgeGood20 20 (depth.val + 16) 7117 7 10 &&
     checkStage EdgeGood20 20 (depth.val + 16) 7129 7 10) = true := by decide +kernel

private theorem clamp_depth (width depth input time : Nat) :
    runFast width depth input time = runFast width (min depth width) input time := by
  by_cases h : depth ≤ width
  · rw [show min depth width = depth by omega]
  · rw [show min depth width = width by omega, runFast_wide _ _ _ (by omega),
      runFast_wide _ _ _ (by omega)]

private theorem apply_check (good : Nat → Bool) (width depth input head tailBits time : Nat)
    (htop : input >>> tailBits = head)
    (h : checkStage good width depth head tailBits time = true) :
    good (runFast width depth input time) = true := by
  have eq : input = head * 2 ^ tailBits + input % 2 ^ tailBits := by
    rw [← htop, Nat.shiftRight_eq_div_pow, Nat.mul_comm, Nat.div_add_mod]
  calc
    _ = good (runFast width depth (head * 2 ^ tailBits + input % 2 ^ tailBits) time) :=
      congrArg (fun u => good (runFast width depth u time)) eq
    _ = true := by
      simpa only [Nat.zero_add] using
        chk_sound _ tailBits 0 h (input % 2 ^ tailBits) (Nat.mod_lt _ (Nat.two_pow_pos _))

private theorem restart_table13 (depth input : Nat) (hd : 10 ≤ depth)
    (h8 : EdgeGood8 (input >>> 5) = true) :
    inC13 (runFast 13 depth input 6) = true := by
  rw [clamp_depth]
  let d := min depth 13
  have bound : 10 ≤ d ∧ d ≤ 13 := by dsimp [d]; omega
  have hcheck := table13 ⟨d - 10, by omega⟩
  change (checkStage inC13 13 (d - 10 + 10) 200 5 6 &&
    checkStage inC13 13 (d - 10 + 10) 222 5 6) = true at hcheck
  rw [show d - 10 + 10 = d by omega, Bool.and_eq_true] at hcheck
  simp only [EdgeGood8, Bool.or_eq_true, beq_iff_eq] at h8
  rcases h8 with h | h
  · exact apply_check _ _ _ _ _ _ _ h hcheck.1
  · exact apply_check _ _ _ _ _ _ _ h hcheck.2

private theorem restart_table20 (depth input : Nat) (hd : 16 ≤ depth)
    (h13 : inC13 (input >>> 7) = true) :
    EdgeGood20 (runFast 20 depth input 10) = true := by
  rw [clamp_depth]
  let d := min depth 20
  have bound : 16 ≤ d ∧ d ≤ 20 := by dsimp [d]; omega
  have hcheck := table20 ⟨d - 16, by omega⟩
  change (checkStage EdgeGood20 20 (d - 16 + 16) 6411 7 10 &&
    checkStage EdgeGood20 20 (d - 16 + 16) 6428 7 10 &&
    checkStage EdgeGood20 20 (d - 16 + 16) 7117 7 10 &&
    checkStage EdgeGood20 20 (d - 16 + 16) 7129 7 10) = true at hcheck
  rw [show d - 16 + 16 = d by omega] at hcheck
  simp only [Bool.and_eq_true, and_assoc] at hcheck
  simp only [inC13, Bool.or_eq_true, beq_iff_eq, or_assoc] at h13
  rcases h13 with h | h | h | h
  · exact apply_check _ _ _ _ _ _ _ h hcheck.1
  · exact apply_check _ _ _ _ _ _ _ h hcheck.2.1
  · exact apply_check _ _ _ _ _ _ _ h hcheck.2.2.1
  · exact apply_check _ _ _ _ _ _ _ h hcheck.2.2.2

private theorem band_prefix (row : Int → Bool) (f : Int) (width extra : Nat) :
    band row f (width + extra) >>> extra = band row f width := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_shiftRight]
  by_cases hi : i < width
  · rw [testBit_band_lt _ _ _ _ (by omega), testBit_band_lt _ _ _ _ hi]
    congr 1
    omega
  · rw [testBit_band_ge _ _ _ _ (by omega), testBit_band_ge _ _ _ _ (by omega)]

private theorem fast_spec (c : Nat → Bool) (s : Int → Bool) {m : Nat}
    (hm : 0 < m) (h₀ : ∀ p, p < -(m : Int) → s p = false) (h₁ : s (-(m : Int)) = true)
    (width t : Nat) (hw : width ≤ m + t) :
    runFast width m (band (tape c s m) 0 width) t =
      band (L c s t) (edgePosition m t) width := by
  rw [runFast_eq _ _ _ (band_lt _ _ _), runWord_spec c s hm h₀ h₁, band_interior c s m _ _ hw]

private theorem L_restart (c : Nat → Bool) (s : Int → Bool) (a : Nat) :
    ∀ t, L (fun k => c (a + k)) (L c s a) t = L c s (a + t)
  | 0 => by
    funext p
    by_cases hp : p < 0
    · rw [L_zero hp, Nat.add_zero]
    · cases a <;> simp [L, hp]
  | t + 1 => by
    funext p
    by_cases hp : p < 0
    · rw [L_succ hp, L_restart c s a t, ← Nat.add_assoc, L_succ hp]
    · simp [L, hp, Nat.add_assoc]

private theorem restart_stage (good : Nat → Bool) (high extra : Nat)
    (c : Nat → Bool) (s : Int → Bool) {m : Nat}
    (hm : high ≤ m) (hp : 0 < m)
    (h₀ : ∀ p, p < -(m : Int) → s p = false) (h₁ : s (-(m : Int)) = true)
    (usesPrefix : Nat → Bool) (time : Nat) (hw : high + extra ≤ m + time)
    (check : ∀ u, usesPrefix (u >>> extra) = true →
      good (runFast (high + extra) m u time) = true)
    (start : usesPrefix (band (L c s 0) (edgePosition m 0) high) = true) :
    good (band (L c s time) (edgePosition m time) (high + extra)) = true := by
  have hprefix : band (tape c s m) 0 high = band (L c s 0) (edgePosition m 0) high := by
    apply band_congr
    intro j hj
    simp only [Int.zero_add, tape]
    rw [ite_eq_left (by omega), L_zero (by unfold edgePosition; omega)]
  have h := check (band (tape c s m) 0 (high + extra)) (by rw [band_prefix, hprefix]; exact start)
  rwa [fast_spec c s hp h₀ h₁ _ _ hw] at h

private theorem band_after_restart (low high : Nat) (lowState highState : Nat → Bool)
    (c : Nat → Bool) (s : Int → Bool) {m a : Nat}
    (hm : 0 < m) (h₀ : ∀ p, p < -(m : Int) → s p = false) (h₁ : s (-(m : Int)) = true)
    (fit : low ≤ m + a) (time : Nat) (wide : low + high ≤ m + a + time)
    (check : ∀ u, lowState (u >>> high) = true →
      highState (runFast (low + high) (m + a) u time) = true)
    (start : lowState (band (L c s a) (edgePosition m a) low) = true) :
    highState (band (L c s (a + time)) (edgePosition m (a + time)) (low + high)) = true := by
  have he (u : Nat) : edgePosition (m + a) u = edgePosition m (a + u) := by
    unfold edgePosition
    omega
  have hs := edge_at c s hm h₀ h₁ a
  have base := restart_stage highState low high (fun k => c (a + k)) (L c s a) fit
    (by omega) (fun p hp => hs.1 p (by unfold edgePosition; omega))
    (by rw [show -((m + a : Nat) : Int) = edgePosition m a by unfold edgePosition; omega]; exact hs.2)
    lowState time (by omega) check
    (by
      have h := L_restart c s a 0
      rw [h, he, Nat.add_zero]
      exact start)
  rwa [he, L_restart] at base

private theorem stable20 (u : Nat) (h : EdgeGood20 u = true) : EdgeGood20 (R u) = true := by
  simp only [EdgeGood20, Bool.or_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The uniform two-tick age is 25 at the wall and 24 for every greater depth. -/
def twoTickThreshold (m : Nat) : Nat := threshold m + 16

/-- Every driven half enters Hughes's good twenty-cell bands at the two-tick age. -/
theorem good_twenty_band_of_age (c : Nat → Bool) (s : Int → Bool) {m : Nat}
    (hm : 0 < m) (h₀ : ∀ p, p < -(m : Int) → s p = false) (h₁ : s (-(m : Int)) = true)
    (t : Nat) (ht : twoTickThreshold m ≤ t) :
    EdgeGood20 (band (L c s t) (edgePosition m t) 20) = true := by
  have hr : 10 ≤ m + threshold m := by unfold threshold; split <;> omega
  have atStart := good_band_of_age c s hm h₀ h₁ (threshold m) (by omega)
  have at13 := band_after_restart 8 5 EdgeGood8 inC13 c s hm h₀ h₁ (by omega) 6 (by omega)
    (fun u => restart_table13 _ u hr) atStart
  have base := band_after_restart 13 7 inC13 EdgeGood20 c s hm h₀ h₁ (by omega) 10 (by omega)
    (fun u => restart_table20 _ u (by omega)) at13
  rw [show threshold m + 6 + 10 = twoTickThreshold m by unfold twoTickThreshold; omega] at base
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
  clear ht
  induction d with
  | zero => simpa [twoTickThreshold] using base
  | succ d ih =>
    change EdgeGood20 (band (L c s (twoTickThreshold m + d + 1))
      (edgePosition m (twoTickThreshold m + d + 1)) 20) = true
    rw [band_next c s hm h₀ h₁ 20 _ (by unfold twoTickThreshold; omega)]
    exact stable20 _ ih

/-- Two successive inverse images on the driven half have the exact edge.
Only equations at negative sites are required, so both predecessor wall bits are free. -/
theorem two_step_predecessor_edge (c : Nat → Bool) (s w z : Int → Bool) {m t : Nat}
    (hm : 0 < m) (h₀ : ∀ p, p < -(m : Int) → s p = false) (h₁ : s (-(m : Int)) = true)
    (ht : twoTickThreshold m ≤ t)
    (hw : ∀ p, p < 0 → stepLine w p = L c s t p)
    (hz : ∀ p, p < 0 → stepLine z p = w p) :
    z (edgePosition m t + 2) = true ∧ ∀ p, p < edgePosition m t + 2 → z p = false := by
  have ht' : 24 ≤ t := by unfold twoTickThreshold threshold at ht; split at ht <;> omega
  let f := edgePosition m t
  have hf : f ≤ -25 := by dsimp [f, edgePosition]; omega
  have edge := edge_at c s hm h₀ h₁ t
  have eq20 : band (stepLine w) f 20 = band (L c s t) f 20 := by
    apply band_congr
    intro j hj
    exact hw _ (by omega)
  have first := predecessor_of_good20 (stepLine w) w (fun _ => rfl) f
    ((hw _ (by omega)).trans edge.2)
    (fun p hp => (hw p (by omega)).trans (edge.1 p hp))
    (by rw [eq20]; exact good_twenty_band_of_age c s hm h₀ h₁ t ht)
  have eq8 : band (stepLine z) (f + 1) 8 = band w (f + 1) 8 := by
    apply band_congr
    intro j hj
    exact hz _ (by omega)
  have second := predecessor_edge_of_good8 (stepLine z) z (fun _ => rfl) (f + 1)
    ((hz _ (by omega)).trans first.1.1)
    (fun p hp => (hz p (by omega)).trans (first.1.2 p hp))
    (by rw [eq8]; exact first.2)
  rwa [show f + 1 + 1 = edgePosition m t + 2 by dsimp [f]; omega] at second

/-! ## Sharpness at the two-tick ages -/

private def twoExampleDepth (adjacent : Bool) : Nat := if adjacent then 1 else 8

private def twoExampleAge (adjacent : Bool) : Nat := if adjacent then 24 else 23

private def exampleWidth (adjacent : Bool) : Nat :=
  twoExampleDepth adjacent + twoExampleAge adjacent

private def twoExampleWall (adjacent : Bool) (t : Nat) : Bool :=
  adjacent && ((t == 2) || (t == 19) || (t == 20))

/-- A number encoding its negative sites, with white at the wall. -/
private def fromDepth (word : Nat) (p : Int) : Bool :=
  if p < 0 then word.testBit (-p - 1).toNat else false

private def twoExampleSeed (adjacent : Bool) : Int → Bool :=
  fromDepth (if adjacent then 1 else 144)

private def firstCode (adjacent : Bool) : Nat :=
  if adjacent then 10815524 else 692192899

private def firstPred (adjacent : Bool) : Int → Bool := fromDepth (firstCode adjacent)

private def secondPred (adjacent : Bool) (p : Int) : Bool :=
  if p ≤ -((exampleWidth adjacent : Int) + 1) then true
  else fromDepth (if adjacent then 11923384 else 763101946) p

private def exampleTape (adjacent : Bool) : Nat :=
  band (tape (twoExampleWall adjacent) (twoExampleSeed adjacent) (twoExampleDepth adjacent))
    0 (exampleWidth adjacent)

private def exampleImage (adjacent : Bool) : Nat :=
  runFast (exampleWidth adjacent) (twoExampleDepth adjacent)
    (exampleTape adjacent) (twoExampleAge adjacent)

private theorem twoExample_black (adjacent : Bool) :
    twoExampleSeed adjacent (-(twoExampleDepth adjacent : Int)) = true := by
  cases adjacent <;> decide

private theorem twoExample_white (adjacent : Bool) :
    ∀ p, p < -(twoExampleDepth adjacent : Int) → twoExampleSeed adjacent p = false := by
  intro p hp
  have hindex : twoExampleDepth adjacent ≤ (-p - 1).toNat := by omega
  have hcode : (if adjacent then 1 else 144) < 2 ^ twoExampleDepth adjacent := by
    cases adjacent <;> decide
  rw [twoExampleSeed, fromDepth, ite_eq_left (by omega)]
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hcode (Nat.pow_le_pow_right (by decide) hindex))

private theorem firstPred_white (adjacent : Bool) {p : Int} (hp : p ≤ -(exampleWidth adjacent : Int)) :
    firstPred adjacent p = false := by
  have hindex : exampleWidth adjacent - 1 ≤ (-p - 1).toNat := by
    have h : 0 < exampleWidth adjacent := by cases adjacent <;> decide
    omega
  have hcode : firstCode adjacent < 2 ^ (exampleWidth adjacent - 1) := by
    cases adjacent <;> decide
  have hp0 : p < 0 := by
    have h : 0 < exampleWidth adjacent := by cases adjacent <;> decide
    omega
  rw [firstPred, fromDepth, ite_eq_left hp0]
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hcode (Nat.pow_le_pow_right (by decide) hindex))

private theorem twoExample_first_middle :
    ∀ (adjacent : Bool) (j : Fin 31), j.val < exampleWidth adjacent →
      stepLine (firstPred adjacent) (-(exampleWidth adjacent : Int) + j.val) =
        readWord (exampleWidth adjacent) (exampleImage adjacent) j.val := by
  decide +kernel

private theorem twoExample_second_middle :
    ∀ (adjacent : Bool) (j : Fin 32), j.val < exampleWidth adjacent + 1 →
      stepLine (secondPred adjacent) (-(exampleWidth adjacent : Int) - 1 + j.val) =
        firstPred adjacent (-(exampleWidth adjacent : Int) - 1 + j.val) := by
  decide +kernel

private theorem twoExample_first (adjacent : Bool) (p : Int) (hp : p < 0) :
    stepLine (firstPred adjacent) p =
      L (twoExampleWall adjacent) (twoExampleSeed adjacent) (twoExampleAge adjacent) p := by
  have he : edgePosition (twoExampleDepth adjacent) (twoExampleAge adjacent) =
      -(exampleWidth adjacent : Int) := by unfold edgePosition exampleWidth; omega
  have hm : 0 < twoExampleDepth adjacent := by cases adjacent <;> decide
  have hw : exampleWidth adjacent ≤ 31 := by cases adjacent <;> decide
  by_cases hlo : p < -(exampleWidth adjacent : Int)
  · have hew := (edge_at (twoExampleWall adjacent) (twoExampleSeed adjacent) hm
      (twoExample_white adjacent) (twoExample_black adjacent) (twoExampleAge adjacent)).1
    rw [he] at hew
    rw [hew p hlo, stepLine, firstPred_white adjacent (p := p - 1) (by omega),
      firstPred_white adjacent (p := p) (by omega), firstPred_white adjacent (p := p + 1) (by omega)]
    rfl
  · let j : Fin 31 := ⟨(p + exampleWidth adjacent).toNat, by omega⟩
    have hj : j.val < exampleWidth adjacent := by dsimp [j]; omega
    have eq : -(exampleWidth adjacent : Int) + j.val = p := by dsimp [j]; omega
    have h := twoExample_first_middle adjacent j hj
    rw [eq] at h
    rw [h]
    have hs := fast_spec (twoExampleWall adjacent) (twoExampleSeed adjacent) hm
      (twoExample_white adjacent) (twoExample_black adjacent) (exampleWidth adjacent)
      (twoExampleAge adjacent) (by unfold exampleWidth; omega)
    change exampleImage adjacent = _ at hs
    rw [hs, he, readWord, ite_eq_left ⟨by omega, by omega⟩,
      testBit_band_lt _ _ _ _ (by omega)]
    congr 1
    rw [← eq]
    omega

private theorem twoExample_second (adjacent : Bool) (p : Int) (hp : p < 0) :
    stepLine (secondPred adjacent) p = firstPred adjacent p := by
  have hw : exampleWidth adjacent ≤ 31 := by cases adjacent <;> decide
  by_cases hlo : p < -(exampleWidth adjacent : Int) - 1
  · have allBlack (q : Int) (hq : q ≤ -(exampleWidth adjacent : Int) - 1) :
        secondPred adjacent q = true := by
      rw [secondPred, ite_eq_left (by omega)]
    rw [stepLine, allBlack (p - 1) (by omega), allBlack p (by omega), allBlack (p + 1) (by omega),
      firstPred_white adjacent (by omega)]
    rfl
  · let j : Fin 32 := ⟨(p + exampleWidth adjacent + 1).toNat, by omega⟩
    have hj : j.val < exampleWidth adjacent + 1 := by dsimp [j]; omega
    have eq : -(exampleWidth adjacent : Int) - 1 + j.val = p := by dsimp [j]; omega
    simpa only [eq] using twoExample_second_middle adjacent j hj

/-- The ages 23 and 24 fail at initial depths 8 and 1, respectively. Both
predecessors use the prescribed wall at their own time. -/
theorem sharp_two_step_examples (adjacent : Bool) :
    ∃ (c : Nat → Bool) (s w z : Int → Bool),
      let m : Nat := if adjacent then 1 else 8
      let t : Nat := if adjacent then 24 else 23
      s (-(m : Int)) = true ∧ (∀ p, p < -(m : Int) → s p = false) ∧
      w 0 = c (t - 1) ∧ z 0 = c (t - 2) ∧
      (∀ p, p < 0 → stepLine w p = L c s t p) ∧
      (∀ p, p < 0 → stepLine z p = w p) ∧
      ∀ q, ∃ p, p < q ∧ z p = true := by
  refine ⟨twoExampleWall adjacent, twoExampleSeed adjacent, firstPred adjacent, secondPred adjacent,
    twoExample_black adjacent, twoExample_white adjacent, ?_, ?_,
    twoExample_first adjacent, twoExample_second adjacent, ?_⟩
  · cases adjacent <;> decide
  · cases adjacent <;> decide
  · intro q
    refine ⟨min (q - 1) (-(exampleWidth adjacent : Int) - 1), by omega, ?_⟩
    rw [secondPred, ite_eq_left (by omega)]

/-- The exact two-tick conclusion at a given initial depth and age. -/
def TwoTickEdgeAt (m t : Nat) : Prop :=
  ∀ (c : Nat → Bool) (s w z : Int → Bool), s (-(m : Int)) = true →
    (∀ p, p < -(m : Int) → s p = false) →
    (∀ p, p < 0 → stepLine w p = L c s t p) →
    (∀ p, p < 0 → stepLine z p = w p) →
    z (edgePosition m t + 2) = true ∧ ∀ p, p < edgePosition m t + 2 → z p = false

/-- Age 24 is the least uniform two-tick age for initial depth at least 2. -/
theorem two_tick_least_age_nonadjacent (a : Nat) :
    (∀ m, 2 ≤ m → ∀ t, a ≤ t → TwoTickEdgeAt m t) ↔ 24 ≤ a := by
  constructor
  · intro h
    by_cases ha : 24 ≤ a
    · exact ha
    · obtain ⟨c, s, w, z, hs, hl, _, _, hw, hz, hb⟩ := sharp_two_step_examples false
      obtain ⟨p, hp, hpblack⟩ := hb (edgePosition 8 23 + 2)
      have hwhite := (h 8 (by decide) 23 (by omega) c s w z hs hl hw hz).2 p hp
      rw [hpblack] at hwhite
      contradiction
  · intro ha m hm t ht c s w z hs hl hw hz
    exact two_step_predecessor_edge c s w z (by omega) hl hs
      (by unfold twoTickThreshold threshold; rw [ite_eq_right (by omega)]; omega) hw hz

/-- Age 25 is the least uniform two-tick age for an initial edge adjacent to the wall. -/
theorem two_tick_least_age_adjacent (a : Nat) :
    (∀ t, a ≤ t → TwoTickEdgeAt 1 t) ↔ 25 ≤ a := by
  constructor
  · intro h
    by_cases ha : 25 ≤ a
    · exact ha
    · obtain ⟨c, s, w, z, hs, hl, _, _, hw, hz, hb⟩ := sharp_two_step_examples true
      obtain ⟨p, hp, hpblack⟩ := hb (edgePosition 1 24 + 2)
      have hwhite := (h 24 (by omega) c s w z hs hl hw hz).2 p hp
      rw [hpblack] at hwhite
      contradiction
  · intro ha t ht c s w z hs hl hw hz
    exact two_step_predecessor_edge c s w z (by decide) hl hs (by change 25 ≤ t; omega) hw hz

end Ruliology.CellularAutomata.Rule30DrivenLeftInverse
