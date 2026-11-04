module

public import Ruliology.CellularAutomata.Rule30SettledBarrierEffective

/-!
# Rule30WhiteSpacing

Eventually white left diagonals are at least five apart; distance five can only start at index two. Thus 6 whiteCount j <= j + 5, where whiteCount j counts the eventually white left diagonals of index at most j (Rule30LeftReset.whiteCount). For actual center runs this gives 5L + 18 log2(log2 a) <= 3a + 51 when black and a >= 16, and L + 6 log2(log2 a) <= a + 17 when white and a >= 256. There are no period or transient hypotheses.
-/

@[expose] public section

set_option autoImplicit false

namespace Ruliology.CellularAutomata
namespace Rule30WhiteSpacing

open Rule30Prize Rule30Diagonals Rule30LeftReset Rule30LeftUnbounded

def EvBlack (f : Nat → Bool) : Prop := ∃ T, ∀ t, T ≤ t → f t = true

theorem not_white_black {f : Nat → Bool} (hw : EvWhite f) (hb : EvBlack f) : False := by
  obtain ⟨T, hT⟩ := hw
  obtain ⟨S, hS⟩ := hb
  have h := hT (max T S) (by omega)
  rw [hS _ (by omega)] at h
  contradiction

theorem white_index_ge_two {j : Nat} (h : EvWhite (D j)) : 2 ≤ j := by
  obtain ⟨T, hT⟩ := h
  match j with
  | 0 => have := hT T (by omega); rw [D_zero] at this; contradiction
  | 1 => have := hT (T + 1) (by omega); rw [D_one] at this; contradiction
  | j + 2 => omega

theorem white_before_black {j : Nat} (hb : EvBlack (D (j + 2))) : EvWhite (D j) := by
  obtain ⟨T, hT⟩ := hb
  refine ⟨T, fun t ht => ?_⟩
  have hs := D_step j t
  rw [hT t ht, hT (t + 1) (by omega)] at hs
  cases h : D j t <;> simp [h] at hs ⊢

theorem no_black_pair (j : Nat) : ¬ (EvBlack (D (j + 2)) ∧ EvBlack (D (j + 3))) := by
  rintro ⟨h1, h2⟩
  exact D_no_two_white j ⟨white_before_black h1, white_before_black (j := j + 1) h2⟩

theorem no_white_gap_two (j : Nat) : ¬ (EvWhite (D j) ∧ EvWhite (D (j + 2))) := by
  rintro ⟨h1, h2⟩
  exact not_white_black h2 (D_black_after_white h1)

theorem no_white_gap_three (j : Nat) : ¬ (EvWhite (D j) ∧ EvWhite (D (j + 3))) := by
  rintro ⟨hw, ⟨T, hT⟩⟩
  have hj := white_index_ge_two hw
  obtain ⟨S, hS⟩ := D_black_after_white hw
  have hb : EvBlack (D (j + 1)) := by
    refine ⟨max T S, fun t ht => ?_⟩
    rw [D_white_of_eq (j := j + 1) hT t (by omega)]
    exact hS t (by omega)
  have hn := no_black_pair (j - 1)
  have he1 : j - 1 + 2 = j + 1 := by omega
  have he2 : j - 1 + 3 = j + 2 := by omega
  rw [he1, he2] at hn
  exact hn ⟨hb, ⟨S, hS⟩⟩

theorem no_white_gap_four (j : Nat) : ¬ (EvWhite (D j) ∧ EvWhite (D (j + 4))) := by
  rintro ⟨hw, ⟨T, hT⟩⟩
  obtain ⟨S, hS⟩ := D_black_after_white hw
  have hb : EvBlack (D (j + 3)) := by
    refine ⟨max T S, fun t ht => ?_⟩
    rw [← D_white_of_eq (j := j + 2) hT t (by omega)]
    exact hS t (by omega)
  exact no_black_pair j ⟨⟨S, hS⟩, hb⟩

theorem white_spacing {i j : Nat} (hi : EvWhite (D i)) (hj : EvWhite (D j)) (hij : i < j) :
    i + 5 ≤ j := by
  by_cases h : i + 5 ≤ j
  · exact h
  exfalso
  have hcases : j = i + 1 ∨ j = i + 2 ∨ j = i + 3 ∨ j = i + 4 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · exact D_no_two_white i ⟨hi, hj⟩
  · exact no_white_gap_two i ⟨hi, hj⟩
  · exact no_white_gap_three i ⟨hi, hj⟩
  · exact no_white_gap_four i ⟨hi, hj⟩

theorem whiteCount_bound_five (j : Nat) : 5 * whiteCount j ≤ j + 3 := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    cases j with
    | zero => simp [whiteCount]
    | succ j =>
      by_cases hw : EvWhite (D (j + 1))
      · have hcount : whiteCount (j + 1) = whiteCount j + 1 := by
          simp [whiteCount, hw]
        have hj := white_index_ge_two hw
        by_cases hz : whiteCount j = 0
        · omega
        · obtain ⟨i, hij, hiw, hic⟩ :=
            Rule30SettledBarrierEffective.exists_white_at_count j (whiteCount j - 1) (by omega)
          have hb := ih i (by omega)
          have hs := white_spacing hiw hw (by omega)
          omega
      · have hb := ih j (by omega)
        have hc : whiteCount (j + 1) = whiteCount j := by simp [whiteCount, hw]
        omega

theorem gap_five_flip {j : Nat} (hw : EvWhite (D j)) (h5 : EvWhite (D (j + 5))) :
    ∃ T, ∀ t, T ≤ t → D (j + 1) (t + 1) = !(D (j + 1) t) := by
  obtain ⟨B, hB⟩ := D_black_after_white hw
  obtain ⟨U, hU⟩ := h5
  have heq : ∀ t, max B U ≤ t → D (j + 1) t = D (j + 3) t := by
    intro t ht
    have e3 := D_step (j + 1) t
    have e4 := D_step (j + 2) t
    have e0 := D_white_of_eq (j := j + 3) hU t (by omega)
    have e1 := D_white_of_eq (j := j + 3) hU (t + 1) (by omega)
    rw [hB t (by omega)] at e3 e4
    rw [← e0, ← e1] at e4
    cases a : D (j + 1) t <;> cases b : D (j + 3) t <;> simp_all
  refine ⟨max B U, fun t ht => ?_⟩
  have e3 := D_step (j + 1) t
  rw [hB t (by omega), ← heq (t + 1) (by omega)] at e3
  cases a : D (j + 1) t <;> simp_all

theorem gap_five_origin {j : Nat} (hw : EvWhite (D j)) (h5 : EvWhite (D (j + 5))) :
    j = 2 := by
  have hj := white_index_ge_two hw
  by_cases he : j = 2
  · exact he
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 3 := ⟨j - 3, by omega⟩
  obtain ⟨S, hS⟩ := gap_five_flip hw h5
  obtain ⟨T, hT⟩ := hw
  have hb : EvBlack (D (k + 2)) := by
    refine ⟨max S T, fun t ht => ?_⟩
    have e := D_step (k + 2) t
    rw [hT t (by omega), hS t (by omega)] at e
    cases a : D (k + 2) t <;> cases b : D (k + 4) t <;> simp_all
  exact False.elim (no_white_gap_three k ⟨white_before_black hb, ⟨T, hT⟩⟩)

theorem white_spacing_six {i j : Nat} (hi : EvWhite (D i)) (hj : EvWhite (D j))
    (hij : i < j) (hfirst : i ≠ 2) : i + 6 ≤ j := by
  have hs := white_spacing hi hj hij
  by_cases he : j = i + 5
  · subst he
    exact False.elim (hfirst (gap_five_origin hi hj))
  · omega

theorem whiteCount_bound (j : Nat) : 6 * whiteCount j ≤ j + 5 := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    cases j with
    | zero => simp [whiteCount]
    | succ j =>
      by_cases hw : EvWhite (D (j + 1))
      · have hcount : whiteCount (j + 1) = whiteCount j + 1 := by simp [whiteCount, hw]
        have hj := white_index_ge_two hw
        by_cases hz : whiteCount j = 0
        · omega
        · obtain ⟨i, hij, hiw, hic⟩ :=
            Rule30SettledBarrierEffective.exists_white_at_count j (whiteCount j - 1) (by omega)
          have hb := ih i (by omega)
          have hs := white_spacing hiw hw (by omega)
          by_cases he : j + 1 = i + 5
          · have hi2 := gap_five_origin hiw (by simpa [he] using hw)
            have hc5 := whiteCount_bound_five (j + 1)
            omega
          · omega
      · have hb := ih j (by omega)
        have hc : whiteCount (j + 1) = whiteCount j := by simp [whiteCount, hw]
        omega

open Rule30SettledBarrierEffective Rule30FrontLaw Rule30SettledBarrier Rule30CenterRuns

theorem count_le_no_white {m N : Nat} (hm : 1 ≤ m)
    (h : ∀ i, 6 * m - 5 ≤ i → i ≤ N → ¬ EvWhite (D i)) :
    ∀ j, j ≤ N → Rule30LeftReset.whiteCount j ≤ m - 1 := by
  intro j
  induction j with
  | zero => intro _; simp [Rule30LeftReset.whiteCount]
  | succ j ih =>
    intro hj
    by_cases hlt : j + 1 < 6 * m - 5
    · have := whiteCount_bound (j + 1)
      omega
    · have hnw := h (j + 1) (by omega) hj
      have := ih (by omega)
      simp only [Rule30LeftReset.whiteCount, hnw, ite_false]
      omega

theorem exists_white_window_spaced (m : Nat) (hm : 1 ≤ m) :
    ∃ w, 6 * m - 5 ≤ w ∧ w < 2 ^ (2 * 2 ^ (m - 1)) ∧ EvWhite (D w) := by
  by_cases h : ∃ w, 6 * m - 5 ≤ w ∧ w < 2 ^ (2 * 2 ^ (m - 1)) ∧ EvWhite (D w)
  · exact h
  · exfalso
    have hX : 2 ≤ 2 ^ (2 * 2 ^ (m - 1)) := by
      have : 1 ≤ 2 * 2 ^ (m - 1) := by have := Nat.two_pow_pos (m - 1); omega
      calc 2 = 2 ^ 1 := by rfl
        _ ≤ 2 ^ (2 * 2 ^ (m - 1)) := Nat.pow_le_pow_right (by decide) this
    have hno : ∀ i, 6 * m - 5 ≤ i → i ≤ 2 ^ (2 * 2 ^ (m - 1)) - 1 → ¬ EvWhite (D i) :=
      fun i hi1 hi2 hw => h ⟨i, hi1, by omega, hw⟩
    have hcount := count_le_no_white hm hno
    have hper : ∀ j, j ≤ (2 ^ (2 * 2 ^ (m - 1)) - 2) + 1 → EvPer (D j) (2 ^ (m - 1)) := by
      intro j hj
      exact EvPer.of_dvd (D_evper_pow_whiteCount j)
        (Nat.pow_dvd_pow 2 (hcount j (by omega)))
    have := D_common_period_bound (m := 2 ^ (2 * 2 ^ (m - 1)) - 2) (Nat.two_pow_pos (m - 1)) hper
    omega

theorem exists_first_white_spaced (m : Nat) (hm : 1 ≤ m) :
    ∃ w, 6 * m - 5 ≤ w ∧ w < 2 ^ (2 * 2 ^ (m - 1)) ∧ EvWhite (D w) ∧
      ∀ j, j < w → Rule30LeftReset.whiteCount j ≤ m - 1 := by
  obtain ⟨w0, hw01, hw02, hw03⟩ := exists_white_window_spaced m hm
  obtain ⟨w, ⟨hmw, hwhite⟩, hleast⟩ :=
    exists_least (P := fun w => 6 * m - 5 ≤ w ∧ EvWhite (D w)) ⟨w0, hw01, hw03⟩
  have hww0 : w ≤ w0 := Nat.le_of_not_lt (fun hlt => hleast w0 hlt ⟨hw01, hw03⟩)
  refine ⟨w, hmw, by omega, hwhite, ?_⟩
  intro j hj
  exact count_le_no_white (N := w - 1) hm
    (fun i hi1 hi2 hw => hleast i (by omega) ⟨hi1, hw⟩) j (by omega)

theorem black_run_effective_spaced (m : Nat) (hm : 1 ≤ m) (a L : Nat)
    (ha : 2 ^ (2 ^ m + m) ≤ a)
    (h : ∀ i, i < L → center (a + i) = true) :
    5 * L + 18 * m ≤ 3 * a + 33 := by
  obtain ⟨w, hmw, hwX, hwhite, hcount⟩ := exists_first_white_spaced m hm
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

theorem black_run_loglog_spaced (a L : Nat) (ha : 16 ≤ a)
    (h : ∀ i, i < L → center (a + i) = true) :
    5 * L + 18 * Nat.log2 (Nat.log2 a) ≤ 3 * a + 51 := by
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
  have := black_run_effective_spaced (m' - 1) (by omega) a L hA h
  omega

theorem exists_two_whites_spaced (m : Nat) (hm : 1 ≤ m) :
    ∃ j k, 6 * m - 5 ≤ j ∧ j < k ∧ k < 2 ^ (2 * 2 ^ m) ∧ EvWhite (D j) ∧ EvWhite (D k) ∧
      ∀ i, i ≤ k + 1 → Rule30LeftReset.whiteCount i ≤ m + 2 := by
  obtain ⟨j, hmj, hjX, hjwhite, hjcount⟩ := exists_first_white_spaced m hm
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

theorem white_run_effective_spaced (m : Nat) (hm : 1 ≤ m) (a L : Nat)
    (ha : 2 ^ (2 ^ (m + 1) + m + 3) ≤ a)
    (h : ∀ i, i < L → center (a + i) = false) :
    L + 6 * m ≤ a + 5 := by
  obtain ⟨j, k, hmj, hjk, hkX, hjw, hkw, hcount⟩ := exists_two_whites_spaced m hm
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

theorem white_run_loglog_spaced (a L : Nat) (ha : 256 ≤ a)
    (h : ∀ i, i < L → center (a + i) = false) :
    L + 6 * Nat.log2 (Nat.log2 a) ≤ a + 17 := by
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
  have := white_run_effective_spaced (m' - 2) (by omega) a L hA h
  omega

/-! ## Exact Realization of the Unique Gap-Five Pair `(D 2, D 7)` and Sharp `whiteCount` Values Through Index 12 -/

/-- **Diagonal `D 2` Is White from `t = 2` (`D_two_eq_false`):** for every `t ≥ 2`, `D 2 t = false`. -/
theorem D_two_eq_false (t : Nat) (ht : 2 ≤ t) : D 2 t = false := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 2 := ⟨t - 2, by omega⟩
  have hs := D_step 0 (s + 1)
  rw [D_zero (s + 1), D_one s] at hs
  simpa using hs

/-- **Diagonal `D 2` Is Eventually White (`evWhite_D_two`):** `EvWhite (D 2)` holds with cutoff `2`. -/
theorem evWhite_D_two : EvWhite (D 2) :=
  ⟨2, D_two_eq_false⟩

/-- **Diagonal `D 3` Alternates from `t = 2` (`D_three_succ`):** for every `t ≥ 2`,
`D 3 (t + 1) = !D 3 t`. -/
theorem D_three_succ (t : Nat) (ht : 2 ≤ t) : D 3 (t + 1) = !D 3 t := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 2 := ⟨t - 2, by omega⟩
  have hs := D_step 1 (s + 2)
  rw [D_one (s + 1), D_two_eq_false (s + 2) (by omega)] at hs
  simpa using hs

/-- **Diagonal `D 4` Is Black from `t = 3` (`D_four_eq_true`):** for every `t ≥ 3`, `D 4 t = true`. -/
theorem D_four_eq_true : ∀ t : Nat, 3 ≤ t → D 4 t = true
  | 0, ht => by omega
  | 1, ht => by omega
  | 2, ht => by omega
  | 3, _ => by decide
  | t + 4, _ => by
    have hs := D_step 2 (t + 3)
    rw [D_two_eq_false (t + 3) (by omega), D_four_eq_true (t + 3) (by omega)] at hs
    cases D 3 (t + 3) <;> simpa using hs

/-- **Diagonal `D 4` Is Eventually Black (`evBlack_D_four`):** `EvBlack (D 4)` holds with cutoff `3`. -/
theorem evBlack_D_four : EvBlack (D 4) :=
  ⟨3, D_four_eq_true⟩

/-- **Diagonal `D 5` Agrees with `D 3` from `t = 4` (`D_five_eq_D_three`):** for every `t ≥ 4`,
`D 5 t = D 3 t`. -/
theorem D_five_eq_D_three (t : Nat) (ht : 4 ≤ t) : D 5 t = D 3 t := by
  obtain ⟨s, rfl⟩ : ∃ s, t = (s + 3) + 1 := ⟨t - 4, by omega⟩
  have hs := D_step 3 (s + 3)
  have h3 := D_three_succ (s + 3) (by omega)
  rw [D_four_eq_true (s + 3) (by omega)] at hs
  cases D 3 (s + 3) <;> cases D 5 (s + 3) <;> simp_all

/-- **Diagonal `D 6` Agrees with `D 3` from `t = 5` (`D_six_eq_D_three`):** for every `t ≥ 5`,
`D 6 t = D 3 t`. -/
theorem D_six_eq_D_three : ∀ t : Nat, 5 ≤ t → D 6 t = D 3 t
  | 0, ht => by omega
  | 1, ht => by omega
  | 2, ht => by omega
  | 3, ht => by omega
  | 4, ht => by omega
  | 5, _ => by decide
  | t + 6, _ => by
    have hs := D_step 4 (t + 5)
    have h3 := D_three_succ (t + 5) (by omega)
    rw [D_four_eq_true (t + 5) (by omega), D_five_eq_D_three (t + 5) (by omega),
      D_six_eq_D_three (t + 5) (by omega)] at hs
    cases D 3 (t + 5) <;> simp_all

/-- **Diagonal `D 7` Is White from `t = 7` (`D_seven_eq_false`):** for every `t ≥ 7`, `D 7 t = false`. -/
theorem D_seven_eq_false : ∀ t : Nat, 7 ≤ t → D 7 t = false
  | 0, ht => by omega
  | 1, ht => by omega
  | 2, ht => by omega
  | 3, ht => by omega
  | 4, ht => by omega
  | 5, ht => by omega
  | 6, ht => by omega
  | 7, _ => by decide
  | t + 8, _ => by
    have hs := D_step 5 (t + 7)
    rw [D_five_eq_D_three (t + 7) (by omega), D_six_eq_D_three (t + 7) (by omega),
      D_seven_eq_false (t + 7) (by omega)] at hs
    cases D 3 (t + 7) <;> simpa using hs

/-- **Diagonal `D 7` Is Eventually White (`evWhite_D_seven`):** `EvWhite (D 7)` holds with cutoff `7`. -/
theorem evWhite_D_seven : EvWhite (D 7) :=
  ⟨7, D_seven_eq_false⟩

/-- **Exact Characterization of Gap-Five White Pairs (`gap_five_iff_eq_two`):** for every index
`j : Nat`, `EvWhite (D j) ∧ EvWhite (D (j + 5))` holds if and only if `j = 2`. -/
theorem gap_five_iff_eq_two (j : Nat) :
    (EvWhite (D j) ∧ EvWhite (D (j + 5))) ↔ j = 2 := by
  constructor
  · rintro ⟨hw, h5⟩; exact gap_five_origin hw h5
  · rintro rfl; exact ⟨evWhite_D_two, evWhite_D_seven⟩

/-- **No Eventually White Left Diagonals Strictly Between `2` and `7` (`not_evWhite_between_two_and_seven`):**
for `2 < j < 7`, `¬ EvWhite (D j)`. -/
theorem not_evWhite_between_two_and_seven {j : Nat} (h1 : 2 < j) (h2 : j < 7) :
    ¬ EvWhite (D j) := by
  intro hj
  have := white_spacing evWhite_D_two hj h1
  omega

/-- **No Eventually White Left Diagonals Strictly Between `7` and `13` (`not_evWhite_between_seven_and_thirteen`):**
for `7 < j < 13`, `¬ EvWhite (D j)`. -/
theorem not_evWhite_between_seven_and_thirteen {j : Nat} (h1 : 7 < j) (h2 : j < 13) :
    ¬ EvWhite (D j) := by
  intro hj
  have := white_spacing_six evWhite_D_seven hj h1 (by decide)
  omega

/-- **Exact Value `whiteCount 2 = 1` (`whiteCount_two`):** `Rule30LeftReset.whiteCount 2 = 1`. -/
theorem whiteCount_two : Rule30LeftReset.whiteCount 2 = 1 := by
  have h1 : ¬ EvWhite (D 1) := fun h => by have := white_index_ge_two h; omega
  simp [Rule30LeftReset.whiteCount, h1, evWhite_D_two]

/-- **Exact Value of `whiteCount` on `[2, 6]` (`whiteCount_eq_one_of_two_le_le_six`):** for every
`j` with `2 ≤ j ≤ 6`, `Rule30LeftReset.whiteCount j = 1`. -/
theorem whiteCount_eq_one_of_two_le_le_six (j : Nat) (h1 : 2 ≤ j) (h2 : j ≤ 6) :
    Rule30LeftReset.whiteCount j = 1 := by
  have hconst := whiteCount_eq_of_no_white (m := 2) (N := 6)
    (fun i hi1 hi2 => not_evWhite_between_two_and_seven hi1 (by omega))
  rw [hconst j h1 h2, whiteCount_two]

/-- **Exact Value `whiteCount 7 = 2` (`whiteCount_seven`):** `Rule30LeftReset.whiteCount 7 = 2`. -/
theorem whiteCount_seven : Rule30LeftReset.whiteCount 7 = 2 := by
  have hcount : Rule30LeftReset.whiteCount (6 + 1) = Rule30LeftReset.whiteCount 6 + 1 := by
    simp [Rule30LeftReset.whiteCount, evWhite_D_seven]
  rw [show (7 : Nat) = 6 + 1 by rfl, hcount, whiteCount_eq_one_of_two_le_le_six 6 (by omega) (by omega)]

/-- **Exact Value of `whiteCount` on `[7, 12]` (`whiteCount_eq_two_of_seven_le_le_twelve`):** for
every `j` with `7 ≤ j ≤ 12`, `Rule30LeftReset.whiteCount j = 2`. -/
theorem whiteCount_eq_two_of_seven_le_le_twelve (j : Nat) (h1 : 7 ≤ j) (h2 : j ≤ 12) :
    Rule30LeftReset.whiteCount j = 2 := by
  have hconst := whiteCount_eq_of_no_white (m := 7) (N := 12)
    (fun i hi1 hi2 => not_evWhite_between_seven_and_thirteen hi1 (by omega))
  rw [hconst j h1 h2, whiteCount_seven]

/-- **Sharpness of `6 * whiteCount j ≤ j + 5` at `j = 7` (`whiteCount_bound_sharp_at_seven`):** the
upper bound `6 * whiteCount j ≤ j + 5` is attained with equality at `j = 7`. -/
theorem whiteCount_bound_sharp_at_seven : 6 * Rule30LeftReset.whiteCount 7 = 7 + 5 := by
  rw [whiteCount_seven]

end Rule30WhiteSpacing
end Ruliology.CellularAutomata
