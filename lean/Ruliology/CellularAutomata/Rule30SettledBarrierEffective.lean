module

public import Ruliology.CellularAutomata.Rule30SettledBarrier
public import Ruliology.CellularAutomata.Rule30FrontLaw

/-!
# Rule30SettledBarrierEffective

Effective thresholds for actual center runs. For a >= 16, black runs obey 5L + 3 log2(log2 a) <= 3a + 21. For a >= 256, white runs obey L + log2(log2 a) <= a + 2. All logarithms are floor logarithms. Earlier threshold constructions are retained as supporting lemmas.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30SettledBarrierEffective

open Ruliology.CellularAutomata
open Rule30Diagonals Rule30Prize Rule30CenterRuns
open Rule30LeftReset Rule30LeftUnbounded Rule30SettledBarrier

theorem periodSum_two_pow : ∀ k, Rule30FrontLaw.periodSum (fun j => 2 ^ j) k = 2 ^ k
  | 0 => rfl
  | k + 1 => by
    show Rule30FrontLaw.periodSum (fun j => 2 ^ j) k + 2 ^ k = 2 ^ (k + 1)
    rw [periodSum_two_pow k, Nat.pow_succ]; omega

theorem frontBound_le_two_pow (k : Nat) : Rule30FrontLaw.frontBound k ≤ 2 ^ k := by
  have h := Rule30FrontLaw.frontBound_le_periodSum (f := fun j => 2 ^ j)
    (fun j => Nat.two_pow_pos j)
    (fun j => ⟨Rule30FrontLaw.frontBound j, Rule30FrontLaw.D_periodic_from_frontBound j⟩) k
  rwa [periodSum_two_pow] at h

theorem D_settled_from_pow {k : Nat} {b : Bool} (h : ∃ T, ∀ t, T ≤ t → D k t = b) :
    ∀ t, 2 ^ k ≤ t → D k t = b := by
  obtain ⟨T, hT⟩ := h
  intro t ht
  have hshift := Rule30FrontLaw.D_shift_mul (j := k) T t
    (Nat.le_trans (frontBound_le_two_pow k) ht)
  have hle : T ≤ t + T * 2 ^ k := by
    have : T ≤ T * 2 ^ k := Nat.le_mul_of_pos_right T (Nat.two_pow_pos k)
    omega
  rw [← hshift]
  exact hT _ hle

theorem wc_le_self : ∀ d, Rule30LeftReset.whiteCount d ≤ d
  | 0 => by simp [Rule30LeftReset.whiteCount]
  | d + 1 => by
    have := wc_le_self d
    simp only [Rule30LeftReset.whiteCount]
    split <;> omega

theorem wc_mono {i d : Nat} (h : i ≤ d) : Rule30LeftReset.whiteCount i ≤ Rule30LeftReset.whiteCount d := by
  induction d with
  | zero => have : i = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ d ih =>
    rcases Nat.lt_or_ge i (d + 1) with hlt | hge
    · have := ih (by omega)
      simp only [Rule30LeftReset.whiteCount]
      split <;> omega
    · have : i = d + 1 := by omega
      subst this; exact Nat.le_refl _

theorem exists_white_at_count : ∀ d n, n < Rule30LeftReset.whiteCount d →
    ∃ i, i ≤ d ∧ EvWhite (D i) ∧ Rule30LeftReset.whiteCount i = n + 1
  | 0, n, h => by simp [Rule30LeftReset.whiteCount] at h
  | d + 1, n, h => by
    by_cases hlt : n < Rule30LeftReset.whiteCount d
    · obtain ⟨i, hi, hw, hc⟩ := exists_white_at_count d n hlt
      exact ⟨i, by omega, hw, hc⟩
    · by_cases hw : EvWhite (D (d + 1))
      · refine ⟨d + 1, Nat.le_refl _, hw, ?_⟩
        have : Rule30LeftReset.whiteCount (d + 1) = Rule30LeftReset.whiteCount d + 1 := by simp [Rule30LeftReset.whiteCount, hw]
        have h' : n < Rule30LeftReset.whiteCount d + 1 := by rw [← this]; exact h
        omega
      · have : Rule30LeftReset.whiteCount (d + 1) = Rule30LeftReset.whiteCount d := by simp [Rule30LeftReset.whiteCount, hw]
        omega

theorem whiteCount_witness (N : Nat) : ∃ d, d ≤ 2 ^ (2 * 2 ^ N) ∧ N < Rule30LeftReset.whiteCount d := by
  obtain ⟨d, hd, hj⟩ := D_period_unbounded (2 ^ N) (Nat.two_pow_pos _)
  refine ⟨d, hd, ?_⟩
  refine Classical.byContradiction fun hc => hj ?_
  have hdv : 2 ^ Rule30LeftReset.whiteCount d ∣ 2 ^ N := Nat.pow_dvd_pow 2 (by omega)
  exact EvPer.of_dvd (D_evper_pow_whiteCount d) hdv

theorem two_white_above (K : Nat) :
    ∃ j k, K < j ∧ j < k ∧ k ≤ 2 ^ (2 * 2 ^ (K + 1)) ∧ EvWhite (D j) ∧ EvWhite (D k) := by
  obtain ⟨d, hd, hc⟩ := whiteCount_witness (K + 1)
  obtain ⟨j, hjd, hwj, hcj⟩ := exists_white_at_count d K (by omega)
  obtain ⟨k, hkd, hwk, hck⟩ := exists_white_at_count d (K + 1) hc
  have hj := wc_le_self j
  refine ⟨j, k, by omega, ?_, by omega, hwj, hwk⟩
  refine Nat.lt_of_not_le fun hkj => ?_
  have := wc_mono hkj
  omega

def wallBound (M : Nat) : Nat := 2 ^ (2 * 2 ^ (M + 19))

def threshold (M : Nat) : Nat := 2 ^ (wallBound M + 3)

theorem pow_le_threshold {M j : Nat} (hj : j ≤ wallBound M + 2) : 2 ^ j ≤ threshold M :=
  Nat.pow_le_pow_right (by decide) (by omega)

theorem wallBound_lt_threshold (M : Nat) : wallBound M + 2 < threshold M := by
  have := Nat.lt_two_pow_self (n := wallBound M + 3)
  unfold threshold; omega

theorem black_run_margin_effective (M a L : Nat) (ha : threshold M ≤ a)
    (h : ∀ i, i < L → center (a + i) = true) : 5 * L + M ≤ 3 * a := by
  obtain ⟨j, k, hj, hjk, hk, hwj, _⟩ := two_white_above (M + 18)
  rw [show M + 18 + 1 = M + 19 by omega] at hk
  have hjB : j ≤ wallBound M := by unfold wallBound; omega
  have hT := wallBound_lt_threshold M
  have hpj : 2 ^ j ≤ 2 ^ wallBound M := Nat.pow_le_pow_right (by decide) hjB
  have hp3 : threshold M = 8 * 2 ^ wallBound M := by
    unfold threshold; rw [Nat.pow_add]; omega
  have hb := black_run_bound_at_white j (2 ^ j) (D_settled_from_pow hwj) a L
    (by omega) (by omega) h
  omega

theorem white_run_margin_effective (M a L : Nat) (ha : threshold M ≤ a)
    (h : ∀ i, i < L → center (a + i) = false) : L + M ≤ a := by
  obtain ⟨j, k, hj, hjk, hk, hwj, hwk⟩ := two_white_above (M + 18)
  rw [show M + 18 + 1 = M + 19 by omega] at hk
  have hkB : k ≤ wallBound M := by unfold wallBound; omega
  have hT := wallBound_lt_threshold M
  have hsj := D_settled_from_pow hwj
  have hsk := D_settled_from_pow hwk
  have hbj := D_settled_from_pow (D_black_after_white hwj)
  have hbk := D_settled_from_pow (D_black_after_white hwk)
  have hb := white_run_bound_two_pairs j k a L hjk (by omega)
    (hsj a (Nat.le_trans (pow_le_threshold (by omega)) ha))
    (hbj a (Nat.le_trans (pow_le_threshold (by omega)) ha))
    (hsk a (Nat.le_trans (pow_le_threshold (by omega)) ha))
    (hbk a (Nat.le_trans (pow_le_threshold (by omega)) ha)) h
  omega

theorem center_run_margins_effective (M : Nat) :
    ∀ a, 2 ^ (2 ^ (2 * 2 ^ (M + 19)) + 3) ≤ a → ∀ L,
      ((∀ i, i < L → center (a + i) = true) → 5 * L + M ≤ 3 * a) ∧
      ((∀ i, i < L → center (a + i) = false) → L + M ≤ a) :=
  fun a ha L => ⟨black_run_margin_effective M a L ha, white_run_margin_effective M a L ha⟩

theorem D_settled_from_frontBound {k : Nat} {b : Bool} (h : ∃ T, ∀ t, T ≤ t → D k t = b) :
    ∀ t, Rule30FrontLaw.frontBound k ≤ t → D k t = b := by
  obtain ⟨T, hT⟩ := h
  intro t ht
  have hshift := Rule30FrontLaw.D_shift_mul (j := k) T t ht
  have hle : T ≤ t + T * 2 ^ k := by
    have : T ≤ T * 2 ^ k := Nat.le_mul_of_pos_right T (Nat.two_pow_pos k)
    omega
  rw [← hshift]
  exact hT _ hle

theorem periodSum_le_of_le {f : Nat → Nat} {Q : Nat} :
    ∀ m, (∀ i, i < m → f i ≤ Q) → Rule30FrontLaw.periodSum f m ≤ 1 + m * Q
  | 0, _ => by simp [Rule30FrontLaw.periodSum]
  | m + 1, h => by
    have ih := periodSum_le_of_le m (fun i hi => h i (by omega))
    have hm := h m (by omega)
    show Rule30FrontLaw.periodSum f m + f m ≤ 1 + (m + 1) * Q
    rw [Nat.succ_mul]; omega

theorem frontBound_le_count {m c : Nat} (hc : ∀ i, i < m → Rule30LeftReset.whiteCount i ≤ c) :
    Rule30FrontLaw.frontBound m ≤ 1 + m * 2 ^ c := by
  have h := Rule30FrontLaw.frontBound_le_periodSum
    (f := fun i => 2 ^ Rule30LeftReset.whiteCount i) (fun i => Nat.two_pow_pos _)
    (fun i => D_evper_pow_whiteCount i) m
  exact Nat.le_trans h (periodSum_le_of_le m fun i hi =>
    Nat.pow_le_pow_right (by decide) (hc i hi))

theorem two_white_settled (K : Nat) :
    ∃ j d, K < j ∧ j < d ∧ d ≤ 2 ^ (2 * 2 ^ (K + 1)) ∧ EvWhite (D j) ∧ EvWhite (D d) ∧
      ∀ i, i ≤ d + 2 → Rule30FrontLaw.frontBound i ≤ 1 + (d + 2) * 2 ^ (K + 2) := by
  obtain ⟨e, he, hc⟩ := whiteCount_witness (K + 1)
  obtain ⟨d, hde, hwd, hcd⟩ := exists_white_at_count e (K + 1) hc
  obtain ⟨j, hjd, hwj, hcj⟩ := exists_white_at_count d K (by omega)
  have hj := wc_le_self j
  have hjd' : j < d := by
    refine Nat.lt_of_not_le fun hdj => ?_
    have := wc_mono hdj
    omega
  have hnw : ¬ EvWhite (D (d + 1)) := fun h => D_no_two_white d ⟨hwd, h⟩
  have hc1 : Rule30LeftReset.whiteCount (d + 1) = K + 2 := by
    simp [Rule30LeftReset.whiteCount, hnw]; omega
  refine ⟨j, d, by omega, hjd', by omega, hwj, hwd, fun i hi => ?_⟩
  have hfb := frontBound_le_count (m := i) (c := K + 2) fun i' hi' => by
    have := wc_mono (show i' ≤ d + 1 by omega); omega
  have : i * 2 ^ (K + 2) ≤ (d + 2) * 2 ^ (K + 2) := Nat.mul_le_mul_right _ hi
  omega

def wallBound2 (M : Nat) : Nat := 2 ^ (2 ^ (M + 20))

def settleTime (M : Nat) : Nat := 1 + (wallBound2 M + 2) * 2 ^ (M + 20)

def threshold2 (M : Nat) : Nat := 5 * settleTime M + wallBound2 M + 2

theorem two_white_settled_M (M : Nat) :
    ∃ j d, M + 18 < j ∧ j < d ∧ d ≤ wallBound2 M ∧ EvWhite (D j) ∧ EvWhite (D d) ∧
      ∀ i, i ≤ d + 2 → Rule30FrontLaw.frontBound i ≤ settleTime M := by
  obtain ⟨j, d, hj, hjd, hd, hwj, hwd, hfb⟩ := two_white_settled (M + 18)
  have hpow : 2 * 2 ^ (M + 18 + 1) = 2 ^ (M + 20) := by
    rw [show M + 20 = (M + 18 + 1) + 1 by omega, Nat.pow_succ]; omega
  rw [hpow] at hd
  refine ⟨j, d, hj, hjd, hd, hwj, hwd, fun i hi => ?_⟩
  have h1 := hfb i hi
  have h2 : (d + 2) * 2 ^ (M + 18 + 2) ≤ (wallBound2 M + 2) * 2 ^ (M + 20) := by
    rw [show M + 18 + 2 = M + 20 by omega]
    exact Nat.mul_le_mul_right _ (by unfold wallBound2; omega)
  unfold settleTime; omega

theorem black_run_margin_effective2 (M a L : Nat) (ha : threshold2 M ≤ a)
    (h : ∀ i, i < L → center (a + i) = true) : 5 * L + M ≤ 3 * a := by
  obtain ⟨j, d, hj, hjd, hd, hwj, _, hfb⟩ := two_white_settled_M M
  have hset : ∀ t, settleTime M ≤ t → D j t = false := fun t ht =>
    D_settled_from_frontBound hwj t (Nat.le_trans (hfb j (by omega)) ht)
  unfold threshold2 at ha
  have hb := black_run_bound_at_white j (settleTime M) hset a L (by omega) (by omega) h
  omega

theorem white_run_margin_effective2 (M a L : Nat) (ha : threshold2 M ≤ a)
    (h : ∀ i, i < L → center (a + i) = false) : L + M ≤ a := by
  obtain ⟨j, d, hj, hjd, hd, hwj, hwd, hfb⟩ := two_white_settled_M M
  unfold threshold2 at ha
  have hT : ∀ i, i ≤ d + 2 → Rule30FrontLaw.frontBound i ≤ a := fun i hi =>
    Nat.le_trans (hfb i hi) (by omega)
  have hb := white_run_bound_two_pairs j d a L hjd (by omega)
    (D_settled_from_frontBound hwj a (hT j (by omega)))
    (D_settled_from_frontBound (D_black_after_white hwj) a (hT (j + 2) (by omega)))
    (D_settled_from_frontBound hwd a (hT d (by omega)))
    (D_settled_from_frontBound (D_black_after_white hwd) a (hT (d + 2) (by omega))) h
  omega

theorem center_run_margins_effective2 (M : Nat) :
    ∀ a, 5 * (1 + (2 ^ (2 ^ (M + 20)) + 2) * 2 ^ (M + 20)) + 2 ^ (2 ^ (M + 20)) + 2 ≤ a →
      ∀ L,
      ((∀ i, i < L → center (a + i) = true) → 5 * L + M ≤ 3 * a) ∧
      ((∀ i, i < L → center (a + i) = false) → L + M ≤ a) :=
  fun a ha L => ⟨black_run_margin_effective2 M a L ha, white_run_margin_effective2 M a L ha⟩

section V3
open Rule30FrontLaw

theorem whiteCount_le_self : ∀ j, Rule30LeftReset.whiteCount j ≤ j := by
  intro j
  induction j with
  | zero => simp [Rule30LeftReset.whiteCount]
  | succ j ih =>
    simp only [Rule30LeftReset.whiteCount]
    split <;> omega

theorem whiteCount_succ_le (j : Nat) : Rule30LeftReset.whiteCount (j + 1) ≤ Rule30LeftReset.whiteCount j + 1 := by
  simp only [Rule30LeftReset.whiteCount]
  split <;> omega

theorem whiteCount_le_of_no_white {m N : Nat} (hm : 1 ≤ m)
    (h : ∀ i, m ≤ i → i ≤ N → ¬ EvWhite (D i)) :
    ∀ j, j ≤ N → Rule30LeftReset.whiteCount j ≤ m - 1 := by
  intro j
  induction j with
  | zero => intro _; simp [Rule30LeftReset.whiteCount]
  | succ j ih =>
    intro hj
    by_cases hlt : j + 1 < m
    · have := whiteCount_le_self (j + 1)
      omega
    · have hnw : ¬ EvWhite (D (j + 1)) := h (j + 1) (by omega) hj
      have := ih (by omega)
      simp only [Rule30LeftReset.whiteCount, hnw, ite_false]
      omega

theorem whiteCount_eq_of_no_white {m N : Nat}
    (h : ∀ i, m < i → i ≤ N → ¬ EvWhite (D i)) :
    ∀ j, m ≤ j → j ≤ N → Rule30LeftReset.whiteCount j = Rule30LeftReset.whiteCount m := by
  intro j
  induction j with
  | zero => intro hm _; have : m = 0 := by omega
            subst this; rfl
  | succ j ih =>
    intro hmj hjN
    by_cases heq : m = j + 1
    · subst heq; rfl
    · have hnw : ¬ EvWhite (D (j + 1)) := h (j + 1) (by omega) hjN
      simp only [Rule30LeftReset.whiteCount, hnw, ite_false]
      exact ih (by omega) (by omega)

theorem white_from_frontBound {w : Nat} (hw : EvWhite (D w)) :
    ∀ t, frontBound w ≤ t → D w t = false := by
  obtain ⟨T, hT⟩ := hw
  intro t ht
  have hle : T ≤ t + T * 2 ^ w := by
    have : T ≤ T * 2 ^ w := Nat.le_mul_of_pos_right T (Nat.pow_pos (by decide : 0 < 2))
    omega
  rw [← D_shift_mul (j := w) T t ht]
  exact hT _ hle

theorem black_from_frontBound {w T : Nat} (hb : ∀ t, T ≤ t → D w t = true) :
    ∀ t, frontBound w ≤ t → D w t = true := by
  intro t ht
  have hle : T ≤ t + T * 2 ^ w := by
    have : T ≤ T * 2 ^ w := Nat.le_mul_of_pos_right T (Nat.pow_pos (by decide : 0 < 2))
    omega
  rw [← D_shift_mul (j := w) T t ht]
  exact hb _ hle

theorem periodSum_le_of_bounded {f : Nat → Nat} {c : Nat} :
    ∀ k, (∀ j, j < k → f j ≤ c) → periodSum f k ≤ 1 + k * c := by
  intro k
  induction k with
  | zero => intro _; simp [periodSum]
  | succ k ih =>
    intro h
    have h1 := ih (fun j hj => h j (by omega))
    have h2 := h k (by omega)
    have e : (k + 1) * c = k * c + c := Nat.succ_mul k c
    simp only [periodSum]
    omega

theorem frontBound_le_of_whiteCount_le {k c : Nat} (h : ∀ j, j < k → Rule30LeftReset.whiteCount j ≤ c) :
    frontBound k ≤ 1 + k * 2 ^ c := by
  have hps := frontBound_le_periodSum (f := fun j => 2 ^ Rule30LeftReset.whiteCount j)
    (fun j => Nat.two_pow_pos _) (fun j => D_evper_pow_whiteCount j) k
  have hb : periodSum (fun j => 2 ^ Rule30LeftReset.whiteCount j) k ≤ 1 + k * 2 ^ c :=
    periodSum_le_of_bounded k (fun j hj => Nat.pow_le_pow_right (by decide) (h j hj))
  omega

theorem exists_white_window (m : Nat) (hm : 1 ≤ m) :
    ∃ w, m ≤ w ∧ w < 2 ^ (2 * 2 ^ (m - 1)) ∧ EvWhite (D w) := by
  by_cases h : ∃ w, m ≤ w ∧ w < 2 ^ (2 * 2 ^ (m - 1)) ∧ EvWhite (D w)
  · exact h
  · exfalso
    have hX : 2 ≤ 2 ^ (2 * 2 ^ (m - 1)) := by
      have : 1 ≤ 2 * 2 ^ (m - 1) := by have := Nat.two_pow_pos (m - 1); omega
      calc 2 = 2 ^ 1 := by rfl
        _ ≤ 2 ^ (2 * 2 ^ (m - 1)) := Nat.pow_le_pow_right (by decide) this
    have hno : ∀ i, m ≤ i → i ≤ 2 ^ (2 * 2 ^ (m - 1)) - 1 → ¬ EvWhite (D i) :=
      fun i hi1 hi2 hw => h ⟨i, hi1, by omega, hw⟩
    have hcount := whiteCount_le_of_no_white hm hno
    have hper : ∀ j, j ≤ (2 ^ (2 * 2 ^ (m - 1)) - 2) + 1 → EvPer (D j) (2 ^ (m - 1)) := by
      intro j hj
      exact EvPer.of_dvd (D_evper_pow_whiteCount j)
        (Nat.pow_dvd_pow 2 (hcount j (by omega)))
    have := D_common_period_bound (m := 2 ^ (2 * 2 ^ (m - 1)) - 2) (Nat.two_pow_pos (m - 1)) hper
    omega

theorem exists_first_white (m : Nat) (hm : 1 ≤ m) :
    ∃ w, m ≤ w ∧ w < 2 ^ (2 * 2 ^ (m - 1)) ∧ EvWhite (D w) ∧
      ∀ j, j < w → Rule30LeftReset.whiteCount j ≤ m - 1 := by
  obtain ⟨w0, hw01, hw02, hw03⟩ := exists_white_window m hm
  obtain ⟨w, ⟨hmw, hwhite⟩, hleast⟩ :=
    exists_least (P := fun w => m ≤ w ∧ EvWhite (D w)) ⟨w0, hw01, hw03⟩
  have hww0 : w ≤ w0 := Nat.le_of_not_lt (fun hlt => hleast w0 hlt ⟨hw01, hw03⟩)
  refine ⟨w, hmw, by omega, hwhite, ?_⟩
  intro j hj
  exact whiteCount_le_of_no_white (N := w - 1) hm
    (fun i hi1 hi2 hw => hleast i (by omega) ⟨hi1, hw⟩) j (by omega)

theorem black_run_effective (m : Nat) (hm : 1 ≤ m) (a L : Nat)
    (ha : 2 ^ (2 ^ m + m) ≤ a)
    (h : ∀ i, i < L → center (a + i) = true) :
    5 * L + 3 * m ≤ 3 * a + 18 := by
  obtain ⟨w, hmw, hwX, hwhite, hcount⟩ := exists_first_white m hm
  have hT : frontBound w ≤ 1 + w * 2 ^ (m - 1) := frontBound_le_of_whiteCount_le hcount
  have hwT := white_from_frontBound hwhite

  have hY : 2 ^ m = 2 ^ (m - 1) * 2 := by
    rw [← Nat.pow_succ]; congr 1; omega
  have hXe : 2 ^ (2 * 2 ^ (m - 1)) = 2 ^ (2 ^ m) := by
    congr 1; rw [hY]; omega
  have hA : 2 ^ (2 ^ m + m) = 2 ^ (2 ^ m) * 2 ^ (m - 1) * 2 := by
    rw [Nat.pow_add, hY, Nat.mul_assoc]
  rw [hXe] at hwX
  have hYpos : 1 ≤ 2 ^ (m - 1) := Nat.two_pow_pos _
  have hXpos : 1 ≤ 2 ^ (2 ^ m) := Nat.two_pow_pos _
  have hmul : (w + 1) * 2 ^ (m - 1) ≤ 2 ^ (2 ^ m) * 2 ^ (m - 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have hmul' : (w + 1) * 2 ^ (m - 1) = w * 2 ^ (m - 1) + 2 ^ (m - 1) := Nat.succ_mul _ _
  have hXle : 2 ^ (2 ^ m) ≤ 2 ^ (2 ^ m) * 2 ^ (m - 1) :=
    Nat.le_mul_of_pos_right _ hYpos
  have hwa : w ≤ a := by omega
  have h5 : 5 * frontBound w ≤ 4 * a + w := by omega
  have := black_run_bound_at_white w (frontBound w) hwT a L hwa h5 h
  omega

theorem black_run_loglog (a L : Nat) (ha : 16 ≤ a)
    (h : ∀ i, i < L → center (a + i) = true) :
    5 * L + 3 * Nat.log2 (Nat.log2 a) ≤ 3 * a + 21 := by
  have hl : 4 ≤ Nat.log2 a := (Nat.le_log2 (by omega)).2 (by simpa using ha)
  have hll : 2 ≤ Nat.log2 (Nat.log2 a) := (Nat.le_log2 (by omega)).2 (by simpa using hl)
  have h3 : 2 ^ Nat.log2 a ≤ a := (Nat.le_log2 (by omega)).1 (Nat.le_refl _)
  generalize hm' : Nat.log2 (Nat.log2 a) = m' at hll ⊢
  have h2 : 2 ^ m' ≤ Nat.log2 a := (Nat.le_log2 (by omega)).1 (Nat.le_of_eq hm'.symm)
  have hpow : 2 ^ (m' - 1) + (m' - 1) ≤ 2 ^ m' := by
    have e : 2 ^ m' = 2 ^ (m' - 1) * 2 := by rw [← Nat.pow_succ]; congr 1; omega
    have : m' - 1 < 2 ^ (m' - 1) := Nat.lt_two_pow_self
    omega
  have hA : 2 ^ (2 ^ (m' - 1) + (m' - 1)) ≤ a :=
    Nat.le_trans (Nat.pow_le_pow_right (by decide) (Nat.le_trans hpow h2)) h3
  have := black_run_effective (m' - 1) (by omega) a L hA h
  omega

theorem exists_two_whites (m : Nat) (hm : 1 ≤ m) :
    ∃ j k, m ≤ j ∧ j < k ∧ k < 2 ^ (2 * 2 ^ m) ∧ EvWhite (D j) ∧ EvWhite (D k) ∧
      ∀ i, i ≤ k + 1 → Rule30LeftReset.whiteCount i ≤ m + 2 := by
  obtain ⟨j, hmj, hjX, hjwhite, hjcount⟩ := exists_first_white m hm
  have hjc : Rule30LeftReset.whiteCount j ≤ m := by
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have := whiteCount_succ_le j'
    have := hjcount j' (by omega)
    omega

  have hX : 2 ≤ 2 ^ (2 * 2 ^ m) := by
    have : 1 ≤ 2 * 2 ^ m := by have := Nat.two_pow_pos m; omega
    calc 2 = 2 ^ 1 := by rfl
      _ ≤ 2 ^ (2 * 2 ^ m) := Nat.pow_le_pow_right (by decide) this
  have hjX' : j < 2 ^ (2 * 2 ^ m) := by
    have : 2 ^ (2 * 2 ^ (m - 1)) ≤ 2 ^ (2 * 2 ^ m) :=
      Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by decide) (by omega)))
    omega
  have hex : ∃ k, j < k ∧ k < 2 ^ (2 * 2 ^ m) ∧ EvWhite (D k) := by
    by_cases h : ∃ k, j < k ∧ k < 2 ^ (2 * 2 ^ m) ∧ EvWhite (D k)
    · exact h
    · exfalso
      have hno : ∀ i, j < i → i ≤ 2 ^ (2 * 2 ^ m) - 1 → ¬ EvWhite (D i) :=
        fun i hi1 hi2 hw => h ⟨i, hi1, by omega, hw⟩
      have hconst := whiteCount_eq_of_no_white hno
      have hcount : ∀ i, i ≤ 2 ^ (2 * 2 ^ m) - 1 → Rule30LeftReset.whiteCount i ≤ m := by
        intro i hi
        by_cases hij : i < j
        · have := hjcount i hij; omega
        · rw [hconst i (by omega) hi]; exact hjc
      have hper : ∀ i, i ≤ (2 ^ (2 * 2 ^ m) - 2) + 1 → EvPer (D i) (2 ^ m) := by
        intro i hi
        exact EvPer.of_dvd (D_evper_pow_whiteCount i) (Nat.pow_dvd_pow 2 (hcount i (by omega)))
      have := D_common_period_bound (m := 2 ^ (2 * 2 ^ m) - 2) (Nat.two_pow_pos m) hper
      omega
  obtain ⟨k, ⟨hjk, hkX, hkwhite⟩, hleast⟩ :=
    exists_least (P := fun k => j < k ∧ k < 2 ^ (2 * 2 ^ m) ∧ EvWhite (D k)) hex
  refine ⟨j, k, hmj, hjk, hkX, hjwhite, hkwhite, ?_⟩

  have hno : ∀ i, j < i → i ≤ k - 1 → ¬ EvWhite (D i) :=
    fun i hi1 hi2 hw => hleast i (by omega) ⟨hi1, by omega, hw⟩
  have hconst := whiteCount_eq_of_no_white hno
  intro i hi
  by_cases hij : i < j
  · have := hjcount i hij; omega
  · by_cases hik : i ≤ k - 1
    · rw [hconst i (by omega) hik]; omega
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hk' : Rule30LeftReset.whiteCount k' ≤ m := by
        by_cases hk'j : k' < j
        · have := hjcount k' hk'j; omega
        · rw [hconst k' (by omega) (by omega)]; exact hjc
      have h1 := whiteCount_succ_le k'
      have h2 := whiteCount_succ_le (k' + 1)
      have : i = k' + 1 ∨ i = k' + 1 + 1 := by omega
      rcases this with rfl | rfl <;> omega

theorem white_run_effective (m : Nat) (hm : 1 ≤ m) (a L : Nat)
    (ha : 2 ^ (2 ^ (m + 1) + m + 3) ≤ a)
    (h : ∀ i, i < L → center (a + i) = false) :
    L + m ≤ a := by
  obtain ⟨j, k, hmj, hjk, hkX, hjw, hkw, hcount⟩ := exists_two_whites m hm
  obtain ⟨Tj, hbj⟩ := D_black_after_white hjw
  obtain ⟨Tk, hbk⟩ := D_black_after_white hkw

  have hc : ∀ n, n ≤ k + 2 → frontBound n ≤ 1 + (k + 2) * 2 ^ (m + 2) := by
    intro n hn
    have := frontBound_le_of_whiteCount_le (k := n) (c := m + 2)
      (fun i hi => hcount i (by omega))
    have : n * 2 ^ (m + 2) ≤ (k + 2) * 2 ^ (m + 2) := Nat.mul_le_mul_right _ hn
    omega

  have hXe : 2 ^ (2 * 2 ^ m) = 2 ^ (2 ^ (m + 1)) := by
    congr 1; rw [Nat.pow_succ]; omega
  have hA : 2 ^ (2 ^ (m + 1) + m + 3) = 2 ^ (2 ^ (m + 1)) * 2 ^ m * 8 := by
    rw [Nat.pow_add, Nat.pow_add]
  have hZ4 : 2 ^ (m + 2) = 2 ^ m * 4 := by
    rw [Nat.pow_add]
  have hXpos : 2 ≤ 2 ^ (2 ^ (m + 1)) := by
    have : 1 ≤ 2 ^ (m + 1) := Nat.two_pow_pos _
    calc 2 = 2 ^ 1 := by rfl
      _ ≤ 2 ^ (2 ^ (m + 1)) := Nat.pow_le_pow_right (by decide) this
  have hZpos : 1 ≤ 2 ^ m := Nat.two_pow_pos _
  have hmul : (k + 2) * 2 ^ (m + 2) ≤ (2 ^ (2 ^ (m + 1)) + 1) * (2 ^ m * 4) := by
    rw [← hZ4]; exact Nat.mul_le_mul_right _ (by omega)
  have e1 : (2 ^ (2 ^ (m + 1)) + 1) * (2 ^ m * 4) = 2 ^ (2 ^ (m + 1)) * 2 ^ m * 4 + 2 ^ m * 4 := by
    rw [Nat.succ_mul, Nat.mul_assoc]
  have hXZ : 2 * 2 ^ m ≤ 2 ^ (2 ^ (m + 1)) * 2 ^ m := Nat.mul_le_mul_right _ hXpos
  have hkX2 : k + 1 ≤ 2 ^ (2 ^ (m + 1)) * 2 ^ m :=
    calc k + 1 ≤ 2 ^ (2 * 2 ^ m) := hkX
      _ = 2 ^ (2 ^ (m + 1)) := hXe
      _ ≤ 2 ^ (2 ^ (m + 1)) * 2 ^ m := Nat.le_mul_of_pos_right _ hZpos
  rw [hA] at ha
  have hsettle : 1 + (k + 2) * 2 ^ (m + 2) ≤ a := by omega
  have hka : k + 2 ≤ a := by omega
  have hwj := white_from_frontBound hjw a (Nat.le_trans (hc j (by omega)) hsettle)
  have hwk := white_from_frontBound hkw a (Nat.le_trans (hc k (by omega)) hsettle)
  have hbj' := black_from_frontBound hbj a (Nat.le_trans (hc (j + 2) (by omega)) hsettle)
  have hbk' := black_from_frontBound hbk a (Nat.le_trans (hc (k + 2) (by omega)) hsettle)
  have := white_run_bound_two_pairs j k a L hjk hka hwj hbj' hwk hbk' h
  omega

theorem white_run_loglog (a L : Nat) (ha : 256 ≤ a)
    (h : ∀ i, i < L → center (a + i) = false) :
    L + Nat.log2 (Nat.log2 a) ≤ a + 2 := by
  have hl : 8 ≤ Nat.log2 a := (Nat.le_log2 (by omega)).2 (by simpa using ha)
  have hll : 3 ≤ Nat.log2 (Nat.log2 a) := (Nat.le_log2 (by omega)).2 (by simpa using hl)
  have h3 : 2 ^ Nat.log2 a ≤ a := (Nat.le_log2 (by omega)).1 (Nat.le_refl _)
  generalize hm' : Nat.log2 (Nat.log2 a) = m' at hll ⊢
  have h2 : 2 ^ m' ≤ Nat.log2 a := (Nat.le_log2 (by omega)).1 (Nat.le_of_eq hm'.symm)

  have hpow : 2 ^ (m' - 2 + 1) + (m' - 2) + 3 ≤ 2 ^ m' := by
    have e : 2 ^ m' = 2 ^ (m' - 2 + 1) * 2 := by rw [← Nat.pow_succ]; congr 1; omega
    have e2 : 2 ^ (m' - 2 + 1) = 2 ^ (m' - 2) * 2 := Nat.pow_succ ..
    have : m' - 2 < 2 ^ (m' - 2) := Nat.lt_two_pow_self
    omega
  have hA : 2 ^ (2 ^ (m' - 2 + 1) + (m' - 2) + 3) ≤ a :=
    Nat.le_trans (Nat.pow_le_pow_right (by decide) (Nat.le_trans hpow h2)) h3
  have := white_run_effective (m' - 2) (by omega) a L hA h
  omega

theorem center_run_margins_effective3 (m : Nat) (hm : 1 ≤ m) (a L : Nat)
    (ha : 2 ^ (2 ^ (m + 1) + m + 3) ≤ a) :
    ((∀ i, i < L → center (a + i) = true) → 5 * L + 3 * m ≤ 3 * a + 18) ∧
    ((∀ i, i < L → center (a + i) = false) → L + m ≤ a) := by
  refine ⟨fun h => black_run_effective m hm a L ?_ h, fun h => white_run_effective m hm a L ha h⟩
  exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (by
    have : 2 ^ m ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega)) ha

/-! ### Exact `whiteCount` Witnesses and Sub-Linear Window Existence of Both Center Colors -/

/-- **Predecessor `whiteCount` at an Eventually White Diagonal (`whiteCount_pred_of_evWhite`):**
if `1 ≤ w` and `EvWhite (D w)`, then `Rule30LeftReset.whiteCount w = Rule30LeftReset.whiteCount (w - 1) + 1`. -/
theorem whiteCount_pred_of_evWhite {w : Nat} (hw0 : 1 ≤ w) (hw : EvWhite (D w)) :
    Rule30LeftReset.whiteCount w = Rule30LeftReset.whiteCount (w - 1) + 1 := by
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
  simp [Rule30LeftReset.whiteCount, hw]

/-- **Exact Bounded Witness for Every `whiteCount` Level (`exists_exact_whiteCount_settled`):** for
every `N : Nat`, there exists a left diagonal `w` with `N + 1 ≤ w ≤ 2 ^ (2 * 2 ^ N)` such that
`EvWhite (D w)`, `Rule30LeftReset.whiteCount w = N + 1`, `∀ j < w, Rule30LeftReset.whiteCount j ≤ N`,
and `frontBound w ≤ 1 + w * 2 ^ N`. -/
theorem exists_exact_whiteCount_settled (N : Nat) :
    ∃ w, N + 1 ≤ w ∧ w ≤ 2 ^ (2 * 2 ^ N) ∧ EvWhite (D w) ∧
      Rule30LeftReset.whiteCount w = N + 1 ∧
      (∀ j, j < w → Rule30LeftReset.whiteCount j ≤ N) ∧
      frontBound w ≤ 1 + w * 2 ^ N := by
  obtain ⟨d, hd, hc⟩ := whiteCount_witness N
  obtain ⟨w, hwd, hww, hcw⟩ := exists_white_at_count d N hc
  have hle : N + 1 ≤ w := by
    have := wc_le_self w
    omega
  have hpred : Rule30LeftReset.whiteCount (w - 1) = N := by
    have hp := whiteCount_pred_of_evWhite (by omega) hww
    omega
  have hjle : ∀ j, j < w → Rule30LeftReset.whiteCount j ≤ N := by
    intro j hj
    have hm := wc_mono (show j ≤ w - 1 by omega)
    omega
  exact ⟨w, hle, by omega, hww, hcw, hjle, frontBound_le_of_whiteCount_le hjle⟩

/-- **Decidability of Bounded All-True Windows (`dec_all_center_true`):** for every `a, L : Nat`,
`(∀ i, i < L → center (a + i) = true) ∨ (∃ i, i < L ∧ center (a + i) = false)`. -/
theorem dec_all_center_true (a : Nat) :
    ∀ L : Nat, (∀ i, i < L → center (a + i) = true) ∨ (∃ i, i < L ∧ center (a + i) = false)
  | 0 => Or.inl (fun _ hi => by omega)
  | L + 1 => by
    rcases dec_all_center_true a L with hall | ⟨i, hi, hfalse⟩
    · cases hc : center (a + L)
      · exact Or.inr ⟨L, by omega, hc⟩
      · refine Or.inl (fun i hi => ?_)
        rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hi) with rfl | hlt
        · exact hc
        · exact hall i hlt
    · exact Or.inr ⟨i, by omega, hfalse⟩

/-- **Decidability of Bounded All-False Windows (`dec_all_center_false`):** for every `a, L : Nat`,
`(∀ i, i < L → center (a + i) = false) ∨ (∃ i, i < L ∧ center (a + i) = true)`. -/
theorem dec_all_center_false (a : Nat) :
    ∀ L : Nat, (∀ i, i < L → center (a + i) = false) ∨ (∃ i, i < L ∧ center (a + i) = true)
  | 0 => Or.inl (fun _ hi => by omega)
  | L + 1 => by
    rcases dec_all_center_false a L with hall | ⟨i, hi, htrue⟩
    · cases hc : center (a + L)
      · refine Or.inl (fun i hi => ?_)
        rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hi) with rfl | hlt
        · exact hc
        · exact hall i hlt
      · exact Or.inr ⟨L, by omega, hc⟩
    · exact Or.inr ⟨i, by omega, htrue⟩

/-- **Effective Sub-Linear Window Existence of a White Center Cell (`exists_white_in_window_effective`):**
for `1 ≤ m`, `2 ^ (2 ^ m + m) ≤ a`, and `3 * a + 18 < 5 * L + 3 * m`, the center window
`[a, a + L)` contains a white cell (`center (a + i) = false`). -/
theorem exists_white_in_window_effective (m : Nat) (hm : 1 ≤ m) (a L : Nat)
    (ha : 2 ^ (2 ^ m + m) ≤ a) (hL : 3 * a + 18 < 5 * L + 3 * m) :
    ∃ i, i < L ∧ center (a + i) = false := by
  rcases dec_all_center_true a L with hall | hex
  · have hb := black_run_effective m hm a L ha hall
    omega
  · exact hex

/-- **Log-Log Sub-Linear Window Existence of a White Center Cell (`exists_white_in_window_loglog`):**
for `16 ≤ a` and `3 * a + 21 < 5 * L + 3 * Nat.log2 (Nat.log2 a)`, the center window `[a, a + L)`
contains a white cell (`center (a + i) = false`). -/
theorem exists_white_in_window_loglog (a L : Nat) (ha : 16 ≤ a)
    (hL : 3 * a + 21 < 5 * L + 3 * Nat.log2 (Nat.log2 a)) :
    ∃ i, i < L ∧ center (a + i) = false := by
  rcases dec_all_center_true a L with hall | hex
  · have hb := black_run_loglog a L ha hall
    omega
  · exact hex

/-- **Effective Window Existence of a Black Center Cell (`exists_black_in_window_effective`):**
for `1 ≤ m`, `2 ^ (2 ^ (m + 1) + m + 3) ≤ a`, and `a < L + m`, the center window `[a, a + L)`
contains a black cell (`center (a + i) = true`). -/
theorem exists_black_in_window_effective (m : Nat) (hm : 1 ≤ m) (a L : Nat)
    (ha : 2 ^ (2 ^ (m + 1) + m + 3) ≤ a) (hL : a < L + m) :
    ∃ i, i < L ∧ center (a + i) = true := by
  rcases dec_all_center_false a L with hall | hex
  · have hw := white_run_effective m hm a L ha hall
    omega
  · exact hex

/-- **Log-Log Window Existence of a Black Center Cell (`exists_black_in_window_loglog`):**
for `256 ≤ a` and `a + 2 < L + Nat.log2 (Nat.log2 a)`, the center window `[a, a + L)` contains a
black cell (`center (a + i) = true`). -/
theorem exists_black_in_window_loglog (a L : Nat) (ha : 256 ≤ a)
    (hL : a + 2 < L + Nat.log2 (Nat.log2 a)) :
    ∃ i, i < L ∧ center (a + i) = true := by
  rcases dec_all_center_false a L with hall | hex
  · have hw := white_run_loglog a L ha hall
    omega
  · exact hex

/-- **Simultaneous Existence of Both Center Colors in Sub-Linear Windows (`exists_both_colors_in_window_effective`):**
for `1 ≤ m`, `2 ^ (2 ^ (m + 1) + m + 3) ≤ a`, and `a < L + m`, the center window `[a, a + L)`
contains both a white cell and a black cell. -/
theorem exists_both_colors_in_window_effective (m : Nat) (hm : 1 ≤ m) (a L : Nat)
    (ha : 2 ^ (2 ^ (m + 1) + m + 3) ≤ a) (hL : a < L + m) :
    (∃ i, i < L ∧ center (a + i) = false) ∧ (∃ j, j < L ∧ center (a + j) = true) := by
  have hm2 : 2 ^ m ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have ha' : 2 ^ (2 ^ m + m) ≤ a :=
    Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) ha
  have hm4 : 4 ≤ 2 ^ (m + 1) := by
    have : 2 ^ 2 ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hm_lt : m + 7 < 2 ^ (2 ^ (m + 1) + m + 3) :=
    Nat.lt_of_le_of_lt (by omega) (@Nat.lt_two_pow_self (2 ^ (m + 1) + m + 3))
  exact ⟨exists_white_in_window_effective m hm a L ha' (by omega),
    exists_black_in_window_effective m hm a L ha hL⟩

/-- **Log-Log Simultaneous Existence of Both Center Colors (`exists_both_colors_in_window_loglog`):**
for `256 ≤ a` and `a + 2 < L + Nat.log2 (Nat.log2 a)`, the center window `[a, a + L)` contains both
a white cell and a black cell. -/
theorem exists_both_colors_in_window_loglog (a L : Nat) (ha : 256 ≤ a)
    (hL : a + 2 < L + Nat.log2 (Nat.log2 a)) :
    (∃ i, i < L ∧ center (a + i) = false) ∧ (∃ j, j < L ∧ center (a + j) = true) := by
  have hpow : 2 ^ Nat.log2 a ≤ a := (Nat.le_log2 (by omega)).1 (Nat.le_refl _)
  have h2k : ∀ k : Nat, 2 * k ≤ 2 ^ k := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      rcases k with _ | k
      · decide
      · rw [Nat.pow_succ]
        have : 2 ^ 1 ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
        omega
  have hk := h2k (Nat.log2 a)
  have hl2 : Nat.log2 (Nat.log2 a) ≤ Nat.log2 a := Nat.log2_le_self (Nat.log2 a)
  exact ⟨exists_white_in_window_loglog a L (by omega) (by omega),
    exists_black_in_window_loglog a L ha hL⟩

end V3

end Ruliology.CellularAutomata.Rule30SettledBarrierEffective
