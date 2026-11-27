module

public import Ruliology.CellularAutomata.Rule30Prize

@[expose] public section

/-!
# Temporal differences of Rule 30 rows

Take the XOR of each singleton row and its translate by a positive time lag.
The exact update has a correction involving the underlying row. The main theorem
rules out any fixed elementary cellular-automaton rule for the difference rows,
even after an arbitrary transient. The proof treats small lags by checked local
patterns and uses light-cone separation for larger lags. This excludes a proposed
transfer from simpler elementary rules to Prize Problem 1.

Contributed by Slash Digital Lab, with OpenAI Codex.
-/

namespace Ruliology.CellularAutomata.Rule30TemporalDifference

open Ruliology.CellularAutomata.Rule30Jen

def diagonal (t : Nat) (j : Int) : Bool := cell t (j - t)

theorem diagonal_next (t : Nat) (j : Int) :
    diagonal (t + 1) j = rule (diagonal t (j - 2)) (diagonal t (j - 1)) (diagonal t j) := by
  unfold diagonal
  rw [cell]
  rw [show j - (t + 1 : Nat) - 1 = j - 2 - t by omega,
    show j - (t + 1 : Nat) = j - 1 - t by omega,
    show j - 1 - t + 1 = j - t by omega]

theorem diagonal_zero (t : Nat) : diagonal t 0 = true := by
  simpa [diagonal] using cell_left_edge t

theorem diagonal_before (t : Nat) (j : Int) (hj : j < 0) : diagonal t j = false :=
  cell_eq_false_of_lt t _ (by omega)

theorem diagonal_one (t : Nat) : diagonal (t + 1) 1 = true := by
  rw [diagonal_next, show (1 : Int) - 2 = -1 by decide,
    show (1 : Int) - 1 = 0 by decide, diagonal_before t (-1) (by decide), diagonal_zero]
  cases diagonal t 1 <;> rfl

theorem diagonal_two (t : Nat) : diagonal (t + 2) 2 = false := by
  rw [show t + 2 = (t + 1) + 1 by omega, diagonal_next,
    show (2 : Int) - 2 = 0 by decide, show (2 : Int) - 1 = 1 by decide,
    diagonal_zero, diagonal_one]
  cases diagonal (t + 1) 2 <;> rfl

def difference (t lag : Nat) (p : Int) : Bool := xor (cell t p) (cell (t + lag) p)

def correction (t lag : Nat) (p : Int) : Bool :=
  xor (cell t p && cell (t + lag) (p + 1)) (cell (t + lag) p && cell t (p + 1))

def rule210 (a b c : Bool) : Bool := xor a (!b && c)

theorem difference_next (t lag : Nat) (p : Int) :
    difference (t + 1) lag p = xor
      (rule (difference t lag (p - 1)) (difference t lag p) (difference t lag (p + 1)))
      (correction t lag p) := by
  simp only [difference, correction, show t + 1 + lag = (t + lag) + 1 by omega, cell, rule]
  generalize cell t (p - 1) = a, cell t p = b, cell t (p + 1) = c,
    cell (t + lag) (p - 1) = d, cell (t + lag) p = e, cell (t + lag) (p + 1) = f
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> rfl

theorem rule210_eq_xor_middle (a b c : Bool) : rule210 a b c = xor (rule a b c) b := by
  cases a <;> cases b <;> cases c <;> rfl

theorem different_rule210_of_correction_ne_middle (t lag : Nat) (p : Int)
    (h : correction t lag p ≠ difference t lag p) :
    difference (t + 1) lag p ≠
      rule210 (difference t lag (p - 1)) (difference t lag p) (difference t lag (p + 1)) := by
  rw [difference_next, rule210_eq_xor_middle]
  generalize rule (difference t lag (p - 1)) (difference t lag p) (difference t lag (p + 1)) = r
  cases r <;> cases he : correction t lag p <;> cases hd : difference t lag p <;> simp_all

theorem correction_before_edge (t lag : Nat) :
    correction t lag (-(t : Int) - 1) = diagonal (t + lag) ((lag : Int) - 1) := by
  unfold correction diagonal
  rw [cell_eq_false_of_lt t _ (by omega), show -(t : Int) - 1 + 1 = -(t : Int) by omega,
    cell_left_edge, show (lag : Int) - 1 - (t + lag : Nat) = -(t : Int) - 1 by omega]
  cases cell (t + lag) (-(t : Int) - 1) <;> rfl

theorem correction_at_edge (t lag : Nat) (ht : 0 < t) :
    correction t lag (-(t : Int)) = xor (diagonal (t + lag) ((lag : Int) + 1))
      (diagonal (t + lag) lag) := by
  have hedge : cell t (-(t : Int) + 1) = true := by
    obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
    simpa [diagonal, Int.sub_eq_add_neg, Int.add_comm] using diagonal_one s
  unfold correction diagonal
  rw [cell_left_edge, hedge, show (lag : Int) + 1 - (t + lag : Nat) = -(t : Int) + 1 by omega,
    show (lag : Int) - (t + lag : Nat) = -(t : Int) by omega]
  cases cell (t + lag) (-(t : Int) + 1) <;> cases cell (t + lag) (-(t : Int)) <;> rfl

/-- The temporal difference of the exact singleton orbit fails the Rule 210 update
at some position at every positive time, for every positive lag. -/
theorem no_rule210_step (t lag : Nat) (ht : 0 < t) (hlag : 0 < lag) :
    ∃ p : Int, difference (t + 1) lag p ≠
      rule210 (difference t lag (p - 1)) (difference t lag p) (difference t lag (p + 1)) := by
  by_cases hs : lag = 1
  · subst lag
    refine ⟨-(t : Int), different_rule210_of_correction_ne_middle _ _ _ ?_⟩
    have htwo : diagonal (t + 1) 2 = false := by
      obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
      simpa only [show (s + 1) + 1 = s + 2 by omega] using diagonal_two s
    rw [correction_at_edge _ _ ht, show ((1 : Nat) : Int) + 1 = 2 by decide, htwo,
      show ((1 : Nat) : Int) = 1 by rfl, diagonal_one]
    have hshift : cell (t + 1) (-(t : Int)) = true := by
      have hblack := diagonal_one t
      unfold diagonal at hblack
      rwa [show (1 : Int) - (t + 1 : Nat) = -(t : Int) by omega] at hblack
    simp [difference, cell_left_edge, hshift]
  · let p : Int := -((t + lag : Nat) : Int)
    refine ⟨p, different_rule210_of_correction_ne_middle _ _ _ ?_⟩
    have hleft := cell_eq_false_of_lt t p (by dsimp [p]; omega)
    have hright := cell_eq_false_of_lt t (p + 1) (by dsimp [p]; omega)
    unfold correction difference
    rw [hleft, hright, show cell (t + lag) p = true from cell_left_edge (t + lag)]
    cases cell (t + lag) (p + 1) <;> decide

theorem no_adjacent_white_window (j start : Nat) :
    ¬ ∀ s : Nat, s ≤ j →
      diagonal (start + s) j = false ∧ diagonal (start + s) (j + 1 : Int) = false := by
  induction j with
  | zero =>
    intro h
    have hh := (h 0 (by omega)).1
    rw [show ((0 : Nat) : Int) = 0 by rfl, diagonal_zero] at hh
    cases hh
  | succ j ih =>
    intro h
    apply ih
    intro s hs
    obtain ⟨ha, hb⟩ := h s (by omega)
    have hn := (h (s + 1) (by omega)).2
    rw [show start + (s + 1) = (start + s) + 1 by omega, diagonal_next,
      show ((j + 1 : Nat) : Int) + 1 - 2 = (j : Int) by omega,
      show ((j + 1 : Nat) : Int) + 1 - 1 = ((j + 1 : Nat) : Int) by omega, ha, hb] at hn
    exact ⟨by simpa [rule] using hn, by simpa using ha⟩

private theorem eq_of_xor_false (a b : Bool) : xor a b = false → a = b := by
  cases a <;> cases b <;> decide

private theorem left_false_of_update_keeps (a c : Bool) : rule a false c = c → a = false := by
  cases a <;> cases c <;> decide

theorem correction_in_every_window (lag start : Nat) (hlag : 0 < lag) (hstart : 0 < start) :
    ∃ s : Nat, s < lag ∧
      (correction (start + s) lag (-((start + s : Nat) : Int) - 1) = true ∨
       correction (start + s) lag (-((start + s : Nat) : Int)) = true) := by
  apply Classical.byContradiction
  intro h
  have hwhite (s : Nat) (hs : s < lag) :
      diagonal (start + s + lag) ((lag : Int) - 1) = false ∧
      diagonal (start + s + lag) ((lag : Int) + 1) = diagonal (start + s + lag) lag := by
    have h0 : correction (start + s) lag (-((start + s : Nat) : Int) - 1) = false := by
      cases hb : correction (start + s) lag (-((start + s : Nat) : Int) - 1)
      · rfl
      · exact False.elim (h ⟨s, hs, Or.inl hb⟩)
    have h1 : correction (start + s) lag (-((start + s : Nat) : Int)) = false := by
      cases hb : correction (start + s) lag (-((start + s : Nat) : Int))
      · rfl
      · exact False.elim (h ⟨s, hs, Or.inr hb⟩)
    rw [correction_before_edge] at h0
    rw [correction_at_edge _ _ (by omega)] at h1
    exact ⟨h0, eq_of_xor_false _ _ h1⟩
  by_cases hone : lag = 1
  · subst lag
    have hh := (hwhite 0 (by omega)).1
    rw [show ((1 : Nat) : Int) - 1 = 0 by decide, diagonal_zero] at hh
    cases hh
  · apply no_adjacent_white_window (lag - 2) (start + lag)
    intro s hs
    obtain ⟨ha, hb⟩ := hwhite s (by omega)
    have hn := (hwhite (s + 1) (by omega)).2
    have ht : diagonal ((start + s + lag) + 1) ((lag : Int) + 1) =
        diagonal (start + s + lag) lag := by
      rw [diagonal_next, show (lag : Int) + 1 - 2 = (lag : Int) - 1 by omega,
        show (lag : Int) + 1 - 1 = (lag : Int) by omega, ha, hb]
      cases diagonal (start + s + lag) lag <;> rfl
    rw [show start + (s + 1) + lag = (start + s + lag) + 1 by omega, ht] at hn
    rw [diagonal_next, ha] at hn
    have hc := left_false_of_update_keeps _ _ hn.symm
    rw [show start + lag + s = start + s + lag by omega,
      show ((lag - 2 : Nat) : Int) = (lag : Int) - 2 by omega,
      show (lag : Int) - 2 + 1 = (lag : Int) - 1 by omega]
    exact ⟨hc, ha⟩

/-! The stable finite fringe gives a check against all radius-one Boolean rules. -/

private def advanceFringe (word : Nat) : Nat :=
  ((word <<< 2) ^^^ ((word <<< 1) ||| word)) % 2 ^ 20

private def fringe : Nat → Nat
  | 0 => 1
  | t + 1 => advanceFringe (fringe t)

private theorem fringe_bit (t i : Nat) (hi : i < 20) :
    (fringe t).testBit i = diagonal t i := by
  induction t generalizing i with
  | zero => cases i <;> simp [fringe, diagonal, cell, Nat.testBit_succ] <;> omega
  | succ t ih =>
    simp only [fringe, advanceFringe, Nat.testBit_mod_two_pow, Nat.testBit_xor, Nat.testBit_or,
      Nat.testBit_shiftLeft, hi, decide_true, Bool.true_and, diagonal_next, rule]
    match i with
    | 0 =>
      change _ = xor (diagonal t (-2)) (diagonal t (-1) || diagonal t 0)
      rw [diagonal_before t (-2) (by decide), diagonal_before t (-1) (by decide)]
      simp [ih 0 (by decide)]
    | 1 =>
      change _ = xor (diagonal t (-1)) (diagonal t 0 || diagonal t 1)
      rw [diagonal_before t (-1) (by decide)]
      simp [ih 0 (by decide), ih 1 (by decide)]
    | i + 2 =>
      have ha : i < 20 := by omega
      have hb : i + 1 < 20 := by omega
      have h2 : i + 2 - 2 = i := by omega
      have h1 : i + 2 - 1 = i + 1 := by omega
      simp only [show 2 ≤ i + 2 by omega, show 1 ≤ i + 2 by omega, decide_true,
        Bool.true_and, h2, h1, ih i ha, ih (i + 1) hb, ih (i + 2) hi]
      rw [show ((i + 2 : Nat) : Int) - 2 = (i : Int) by omega,
        show ((i + 2 : Nat) : Int) - 1 = ((i + 1 : Nat) : Int) by omega]

private theorem fringe_period (t : Nat) (ht : 20 ≤ t) : fringe (t + 4) = fringe t := by
  obtain ⟨k, rfl⟩ : ∃ k : Nat, t = 20 + k := ⟨t - 20, by omega⟩
  induction k with
  | zero => decide
  | succ k ih =>
    change advanceFringe (fringe (20 + k + 4)) = advanceFringe (fringe (20 + k))
    rw [ih (by omega)]

private theorem fringe_reduce (t : Nat) (ht : 20 ≤ t) : fringe t = fringe (20 + t % 4) := by
  induction t using Nat.strongRecOn with
  | ind t ih =>
    by_cases h : t < 24
    · rw [show t = 20 + t % 4 by omega] at ⊢
      rw [show (20 + t % 4) % 4 = t % 4 by omega]
    · have hp := fringe_period (t - 4) (by omega)
      rw [show t - 4 + 4 = t by omega] at hp
      rw [hp, ih (t - 4) (by omega) (by omega), show (t - 4) % 4 = t % 4 by omega]

private def readFringe (t : Nat) (d : Int) : Bool :=
  if d < 0 then false else (fringe t).testBit d.toNat

private theorem readFringe_eq (t : Nat) (d : Int) (hd : d < 20) :
    readFringe t d = diagonal t d := by
  by_cases h : d < 0
  · simp [readFringe, h, diagonal_before t d h]
  · rw [readFringe, ite_eq_right h, fringe_bit t d.toNat (by omega)]
    rw [show (d.toNat : Int) = d by omega]

private theorem readFringe_congr {t u : Nat} (ht : 20 ≤ t) (hu : 20 ≤ u)
    (hm : t % 4 = u % 4) (d : Int) : readFringe t d = readFringe u d := by
  unfold readFringe
  rw [fringe_reduce t ht, fringe_reduce u hu, hm]

private def modelDifference (t lag : Nat) (d : Int) : Bool :=
  xor (readFringe t (d - lag)) (readFringe (t + lag) d)

private theorem modelDifference_eq (t lag : Nat) (d : Int) (hd : d < 20) :
    modelDifference t lag d = difference t lag (d - (t + lag : Nat)) := by
  unfold modelDifference difference
  rw [readFringe_eq t _ (by omega), readFringe_eq (t + lag) d hd]
  unfold diagonal
  rw [show d - lag - t = d - (t + lag : Nat) by omega]

private theorem modelDifference_congr {t u : Nat} (ht : 20 ≤ t) (hu : 20 ≤ u)
    (hm : t % 4 = u % 4) (lag : Nat) (d : Int) :
    modelDifference t lag d = modelDifference u lag d := by
  unfold modelDifference
  rw [readFringe_congr ht hu hm, readFringe_congr (by omega : 20 ≤ t + lag)
    (by omega : 20 ≤ u + lag) (by omega : (t + lag) % 4 = (u + lag) % 4)]

private def tripleCode (a b c : Bool) : Nat :=
  (if a then 1 else 0) + (if b then 2 else 0) + (if c then 4 else 0)

private def tripleWitness (code : Nat) : Nat × Int :=
  [(0, -2), (0, 2), (0, 4), (0, 1), (0, -1), (1, 2), (0, 0), (1, 4)][code]!

private theorem tripleWitness_audit (a b c : Bool) :
    let w := tripleWitness (tripleCode a b c)
    w.1 < 4 ∧ w.2 ≤ 7 ∧
      readFringe (20 + w.1) (w.2 - 1) = a ∧
      readFringe (20 + w.1) w.2 = b ∧
      readFringe (20 + w.1) (w.2 + 1) = c := by
  cases a <;> cases b <;> cases c <;> decide

private def smallLagWitness (lag : Nat) : Int × Int :=
  [(0, 6), (1, 2), (7, 11), (5, 12), (1, 4), (6, 9), (5, 6), (3, 9)][lag - 1]!

private theorem smallLagWitness_audit (lag : Fin 8) :
    let p := lag.val + 1
    let w := smallLagWitness p
    w.1 + 1 < 20 ∧ w.2 + 1 < 20 ∧
      modelDifference 20 p (w.1 - 1) = modelDifference 20 p (w.2 - 1) ∧
      modelDifference 20 p w.1 = modelDifference 20 p w.2 ∧
      modelDifference 20 p (w.1 + 1) = modelDifference 20 p (w.2 + 1) ∧
      modelDifference 21 p (w.1 + 1) ≠ modelDifference 21 p (w.2 + 1) := by
  revert lag
  decide

private theorem no_elementary_rule_small (lag start : Nat) (hlag : 0 < lag) (hsmall : lag < 9)
    (f : Bool → Bool → Bool → Bool)
    (hf : ∀ t, start ≤ t → ∀ p : Int,
      difference (t + 1) lag p = f (difference t lag (p - 1)) (difference t lag p)
        (difference t lag (p + 1))) : False := by
  let t := 4 * (start + 20)
  have hstart : start ≤ t := by dsimp [t]; omega
  have ht : 20 ≤ t := by dsimp [t]; omega
  have hm : t % 4 = 20 % 4 := by dsimp [t]; omega
  have hm' : (t + 1) % 4 = 21 % 4 := by dsimp [t]; omega
  obtain ⟨h1, h2, hL, hM, hR, hO⟩ := smallLagWitness_audit (⟨lag - 1, by omega⟩ : Fin 8)
  simp only [show lag - 1 + 1 = lag by omega] at h1 h2 hL hM hR hO
  let w := smallLagWitness lag
  have hstep (d : Int) (hd : d + 1 < 20) :
      modelDifference 21 lag (d + 1) = f (modelDifference 20 lag (d - 1))
        (modelDifference 20 lag d) (modelDifference 20 lag (d + 1)) := by
    rw [← modelDifference_congr (by omega : 20 ≤ t + 1) (by decide) hm',
      ← modelDifference_congr ht (by decide) hm (d := d - 1),
      ← modelDifference_congr ht (by decide) hm (d := d),
      ← modelDifference_congr ht (by decide) hm (d := d + 1),
      modelDifference_eq _ _ _ hd, modelDifference_eq _ _ _ (by omega),
      modelDifference_eq _ _ _ (by omega), modelDifference_eq _ _ _ hd]
    rw [show d + 1 - (t + 1 + lag : Nat) = d - (t + lag : Nat) by omega,
      show d - 1 - (t + lag : Nat) = d - (t + lag : Nat) - 1 by omega,
      show d + 1 - (t + lag : Nat) = d - (t + lag : Nat) + 1 by omega]
    exact hf t hstart _
  have ha := hstep w.1 h1
  have hb := hstep w.2 h2
  rw [hL, hM, hR] at ha
  exact hO (ha.trans hb.symm)

private theorem no_elementary_rule_large (lag start : Nat) (hlarge : 9 ≤ lag)
    (f : Bool → Bool → Bool → Bool)
    (hf : ∀ t, start ≤ t → ∀ p : Int,
      difference (t + 1) lag p = f (difference t lag (p - 1)) (difference t lag p)
        (difference t lag (p + 1))) : False := by
  have heq (a b c : Bool) : f a b c = rule a b c := by
    let w := tripleWitness (tripleCode a b c)
    obtain ⟨hphase, hd, hL, hM, hR⟩ := tripleWitness_audit a b c
    change w.1 < 4 at hphase
    change w.2 ≤ 7 at hd
    let t := 4 * (start + 20) + w.1 + 4 - lag % 4
    have ht : start ≤ t := by dsimp [t]; omega
    have ht20 : 20 ≤ t := by dsimp [t]; omega
    have hres : (t + lag) % 4 = (20 + w.1) % 4 := by dsimp [t]; omega
    have hcell (d : Int) (hle : d ≤ 8) :
        difference t lag (d - (t + lag : Nat)) = readFringe (20 + w.1) d := by
      unfold difference
      rw [cell_eq_false_of_lt t _ (by omega), ← show diagonal (t + lag) d =
        cell (t + lag) (d - (t + lag : Nat)) from rfl,
        ← readFringe_eq (t + lag) _ (by omega), readFringe_congr (by omega) (by omega) hres]
      cases readFringe (20 + w.1) d <;> rfl
    have hzero : cell (t + 1) (w.2 - (t + lag : Nat)) = false :=
      cell_eq_false_of_lt (t + 1) _ (by omega)
    have h := hf t ht (w.2 - (t + lag : Nat))
    rw [← show w.2 - 1 - (t + lag : Nat) = w.2 - (t + lag : Nat) - 1 by omega,
      ← show w.2 + 1 - (t + lag : Nat) = w.2 - (t + lag : Nat) + 1 by omega,
      hcell _ (by omega), hcell _ (by omega), hcell _ (by omega), hL, hM, hR] at h
    unfold difference at h
    rw [hzero, show t + 1 + lag = t + lag + 1 by omega,
      show cell (t + lag + 1) (w.2 - (t + lag : Nat)) = diagonal (t + lag + 1) (w.2 + 1) from by
        unfold diagonal
        congr 1
        omega,
      diagonal_next, show w.2 + 1 - 2 = w.2 - 1 by omega,
      show w.2 + 1 - 1 = w.2 by omega] at h
    rw [← readFringe_eq _ _ (by omega), ← readFringe_eq _ _ (by omega),
      ← readFringe_eq _ _ (by omega)] at h
    rw [readFringe_congr (by omega) (by omega) hres, readFringe_congr (by omega) (by omega) hres,
      readFringe_congr (by omega) (by omega) hres, hL, hM, hR] at h
    simpa using h.symm
  obtain ⟨s, _, h⟩ := correction_in_every_window lag (start + 1) (by omega) (by omega)
  have contradict_at (p : Int) (hc : correction (start + 1 + s) lag p = true) : False := by
    have h := hf (start + 1 + s) (by omega) p
    rw [difference_next, heq, hc] at h
    generalize rule _ _ _ = r at h
    cases r <;> cases h
  exact h.elim (contradict_at _) (contradict_at _)

/-- The singleton time-shift difference fails every fixed elementary update arbitrarily late. -/
theorem no_eventual_elementary_difference (lag start : Nat) (hlag : 0 < lag)
    (f : Bool → Bool → Bool → Bool) :
    ¬ ∀ t, start ≤ t → ∀ p : Int,
      difference (t + 1) lag p = f (difference t lag (p - 1)) (difference t lag p)
        (difference t lag (p + 1)) := by
  intro hf
  by_cases hsmall : lag < 9
  · exact no_elementary_rule_small lag start hlag hsmall f hf
  · exact no_elementary_rule_large lag start (by omega) f hf


end Ruliology.CellularAutomata.Rule30TemporalDifference
