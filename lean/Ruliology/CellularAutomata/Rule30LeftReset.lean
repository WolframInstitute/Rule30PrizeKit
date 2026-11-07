module

public import Ruliology.CellularAutomata.Rule30Prize
public import Ruliology.CellularAutomata.Rule30Diagonals

/-!
# Rule30LeftReset

Reset and parity accumulation for left diagonals. The eventual period divides a power of two indexed by the count of eventually white diagonals.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30LeftReset

open Rule30Diagonals

section Generic
variable {x a b : Nat → Bool}

theorem periodic_iter {f : Nat → Bool} {s L : Nat} (hf : ∀ t, s ≤ t → f (t + L) = f t) :
    ∀ k t, s ≤ t → f (t + k * L) = f t := by
  intro k
  induction k with
  | zero => intro t _; simp
  | succ k ih =>
    intro t ht
    rw [show t + (k + 1) * L = (t + k * L) + L by rw [Nat.succ_mul]; omega, hf _ (by omega), ih t ht]

theorem periodic_two {f : Nat → Bool} {s L : Nat} (hf : ∀ t, s ≤ t → f (t + L) = f t) :
    ∀ t, s ≤ t → f (t + 2 * L) = f t := by
  intro t ht
  rw [Nat.two_mul, ← Nat.add_assoc, hf _ (by omega), hf t ht]

theorem reset_periodic {s L : Nat}
    (hx : ∀ t, x (t + 1) = xor (a t) (b t || x t))
    (ha : ∀ t, s ≤ t → a (t + L) = a t) (hb : ∀ t, s ≤ t → b (t + L) = b t)
    {s0 : Nat} (hs : s ≤ s0) (hreset : b s0 = true) :
    ∀ t, s0 + 1 ≤ t → x (t + L) = x t := by
  have key : ∀ n, x (s0 + 1 + n + L) = x (s0 + 1 + n) := by
    intro n
    induction n with
    | zero =>
      rw [show s0 + 1 + 0 + L = (s0 + L) + 1 by omega, show s0 + 1 + 0 = s0 + 1 by omega, hx, hx,
        ha s0 hs, hb s0 hs, hreset]
      simp
    | succ n ih =>
      rw [show s0 + 1 + (n + 1) + L = (s0 + 1 + n + L) + 1 by omega,
        show s0 + 1 + (n + 1) = (s0 + 1 + n) + 1 by omega, hx, hx, ha _ (by omega),
        hb _ (by omega), ih]
  intro t ht
  obtain ⟨n, rfl⟩ : ∃ n, t = s0 + 1 + n := ⟨t - (s0 + 1), by omega⟩
  exact key n

def par (a : Nat → Bool) (t : Nat) : Nat → Bool
  | 0 => false
  | n + 1 => xor (par a t n) (a (t + n))

theorem accum {s : Nat} (hx : ∀ t, x (t + 1) = xor (a t) (b t || x t))
    (hb : ∀ t, s ≤ t → b t = false) :
    ∀ t, s ≤ t → ∀ n, x (t + n) = xor (x t) (par a t n) := by
  intro t ht n
  induction n with
  | zero => simp [par]
  | succ n ih =>
    rw [show t + (n + 1) = (t + n) + 1 by omega, hx, hb _ (by omega), ih]
    simp only [par, Bool.false_or]
    cases a (t + n) <;> cases x t <;> cases par a t n <;> rfl

theorem par_periodic {s L : Nat} (ha : ∀ t, s ≤ t → a (t + L) = a t) :
    ∀ t, s ≤ t → ∀ n, par a (t + L) n = par a t n := by
  intro t ht n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [par]
    rw [ih, show t + L + n = (t + n) + L by omega, ha _ (by omega)]

theorem white_shift {s L : Nat} (hx : ∀ t, x (t + 1) = xor (a t) (b t || x t))
    (hb : ∀ t, s ≤ t → b t = false) :
    ∀ t, s ≤ t → x (t + L) = xor (x t) (par a t L) :=
  fun t ht => accum hx hb t ht L

theorem white_double {s L : Nat} (hx : ∀ t, x (t + 1) = xor (a t) (b t || x t))
    (ha : ∀ t, s ≤ t → a (t + L) = a t) (hb : ∀ t, s ≤ t → b t = false) :
    ∀ t, s ≤ t → x (t + 2 * L) = x t := by
  intro t ht
  rw [Nat.two_mul, ← Nat.add_assoc, white_shift hx hb (t + L) (by omega), white_shift hx hb t ht,
    par_periodic ha t ht L]
  cases x t <;> cases par a t L <;> rfl

theorem white_period_iff {s L : Nat} (hx : ∀ t, x (t + 1) = xor (a t) (b t || x t))
    (hb : ∀ t, s ≤ t → b t = false) :
    ∀ t, s ≤ t → (x (t + L) = x t ↔ par a t L = false) := by
  intro t ht
  rw [white_shift hx hb t ht]
  cases x t <;> cases par a t L <;> simp

theorem period_or_white {s L : Nat} (hx : ∀ t, x (t + 1) = xor (a t) (b t || x t))
    (ha : ∀ t, s ≤ t → a (t + L) = a t) (hb : ∀ t, s ≤ t → b (t + L) = b t) :
    (∀ t, s + L ≤ t → x (t + L) = x t) ∨ (∀ t, s ≤ t → b t = false) := by
  by_cases hL : L = 0
  · left; intro t _; subst hL; simp
  by_cases h : ∃ s0, s ≤ s0 ∧ s0 < s + L ∧ b s0 = true
  · obtain ⟨s0, hs, hlt, hr⟩ := h
    left
    intro t ht
    exact reset_periodic hx ha hb hs hr t (by omega)
  · right
    have hw : ∀ s0, s ≤ s0 → s0 < s + L → b s0 = false := by
      intro s0 h1 h2
      cases hb0 : b s0
      · rfl
      · exact absurd ⟨s0, h1, h2, hb0⟩ h
    intro t ht
    obtain ⟨q, r, hrL, hts⟩ : ∃ q r, r < L ∧ t = s + r + q * L := by
      refine ⟨(t - s) / L, (t - s) % L, Nat.mod_lt _ (Nat.pos_of_ne_zero hL), ?_⟩
      have hdm := Nat.div_add_mod (t - s) L
      generalize (t - s) / L = q at hdm ⊢
      generalize (t - s) % L = r at hdm ⊢
      rw [Nat.mul_comm] at hdm
      generalize q * L = m at hdm ⊢
      omega
    subst hts
    rw [periodic_iter hb q (s + r) (by omega)]
    exact hw _ (by omega) (by omega)

theorem white_forces_eq {s : Nat} (hx : ∀ t, x (t + 1) = xor (a t) (b t || x t))
    (hw : ∀ t, s ≤ t → x t = false) :
    ∀ t, s ≤ t → a t = b t := by
  intro t ht
  have h := hx t
  rw [hw _ (by omega), hw _ ht] at h
  revert h
  cases a t <;> cases b t <;> decide

end Generic

theorem D_period_after_reset {j s L s0 : Nat}
    (ha : ∀ t, s ≤ t → D j (t + L) = D j t) (hb : ∀ t, s ≤ t → D (j + 1) (t + L) = D (j + 1) t)
    (hs : s ≤ s0) (hreset : D (j + 1) s0 = true) :
    ∀ t, s0 + 1 ≤ t → D (j + 2) (t + L) = D (j + 2) t :=
  reset_periodic (x := D (j + 2)) (a := D j) (b := D (j + 1)) (D_step j) ha hb hs hreset

theorem D_white_shift {j s L : Nat} (hb : ∀ t, s ≤ t → D (j + 1) t = false) :
    ∀ t, s ≤ t → D (j + 2) (t + L) = xor (D (j + 2) t) (par (D j) t L) :=
  white_shift (x := D (j + 2)) (a := D j) (b := D (j + 1)) (D_step j) hb

theorem D_white_double {j s L : Nat}
    (ha : ∀ t, s ≤ t → D j (t + L) = D j t) (hb : ∀ t, s ≤ t → D (j + 1) t = false) :
    ∀ t, s ≤ t → D (j + 2) (t + 2 * L) = D (j + 2) t :=
  white_double (x := D (j + 2)) (a := D j) (b := D (j + 1)) (D_step j) ha hb

theorem D_white_period_iff {j s L : Nat} (hb : ∀ t, s ≤ t → D (j + 1) t = false) :
    ∀ t, s ≤ t → (D (j + 2) (t + L) = D (j + 2) t ↔ par (D j) t L = false) :=
  white_period_iff (x := D (j + 2)) (a := D j) (b := D (j + 1)) (D_step j) hb

theorem D_period_or_white {j s L : Nat}
    (ha : ∀ t, s ≤ t → D j (t + L) = D j t) (hb : ∀ t, s ≤ t → D (j + 1) (t + L) = D (j + 1) t) :
    (∀ t, s + L ≤ t → D (j + 2) (t + L) = D (j + 2) t) ∨ (∀ t, s ≤ t → D (j + 1) t = false) :=
  period_or_white (x := D (j + 2)) (a := D j) (b := D (j + 1)) (D_step j) ha hb

theorem D_white_of_eq {j s : Nat} (hw : ∀ t, s ≤ t → D (j + 2) t = false) :
    ∀ t, s ≤ t → D j t = D (j + 1) t :=
  white_forces_eq (x := D (j + 2)) (a := D j) (b := D (j + 1)) (D_step j) hw

def EvPer (f : Nat → Bool) (L : Nat) : Prop := ∃ T, ∀ t, T ≤ t → f (t + L) = f t

def EvWhite (f : Nat → Bool) : Prop := ∃ T, ∀ t, T ≤ t → f t = false

theorem EvPer.two {f : Nat → Bool} {L : Nat} (h : EvPer f L) : EvPer f (2 * L) :=
  let ⟨T, hT⟩ := h
  ⟨T, periodic_two hT⟩

theorem D_evper_or_evwhite {j L : Nat} (h1 : EvPer (D j) L) (h2 : EvPer (D (j + 1)) L) :
    EvPer (D (j + 2)) L ∨ EvWhite (D (j + 1)) := by
  obtain ⟨T1, h1⟩ := h1
  obtain ⟨T2, h2⟩ := h2
  rcases D_period_or_white (s := max T1 T2) (fun t ht => h1 t (by omega))
    (fun t ht => h2 t (by omega)) with h | h
  · exact Or.inl ⟨max T1 T2 + L, h⟩
  · exact Or.inr ⟨max T1 T2, h⟩

theorem D_evper_double {j L : Nat} (h1 : EvPer (D j) L) (hw : EvWhite (D (j + 1))) :
    EvPer (D (j + 2)) (2 * L) := by
  obtain ⟨T1, h1⟩ := h1
  obtain ⟨T2, hw⟩ := hw
  exact ⟨max T1 T2, D_white_double (s := max T1 T2) (fun t ht => h1 t (by omega))
    (fun t ht => hw t (by omega))⟩

theorem D_evwhite_eq {j : Nat} (hw : EvWhite (D (j + 2))) :
    ∃ T, ∀ t, T ≤ t → D j t = D (j + 1) t :=
  let ⟨T, hT⟩ := hw
  ⟨T, D_white_of_eq hT⟩

open Classical in

noncomputable def whiteCount : Nat → Nat
  | 0 => 0
  | j + 1 => whiteCount j + (if EvWhite (D (j + 1)) then 1 else 0)

theorem D_zero_evper (L : Nat) : EvPer (D 0) L :=
  ⟨0, fun t _ => by rw [D_zero, D_zero]⟩

theorem D_one_evper (L : Nat) : EvPer (D 1) L :=
  ⟨1, fun t ht => by
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    rw [show s + 1 + L = (s + L) + 1 by omega, D_one, D_one]⟩

theorem D_evper_pow_whiteCount_pair :
    ∀ j, EvPer (D j) (2 ^ whiteCount j) ∧ EvPer (D (j + 1)) (2 ^ whiteCount j) := by
  intro j
  induction j with
  | zero => exact ⟨D_zero_evper _, D_one_evper _⟩
  | succ j ih =>
    obtain ⟨h1, h2⟩ := ih
    by_cases hw : EvWhite (D (j + 1))
    · have hc : whiteCount (j + 1) = whiteCount j + 1 := by
        simp only [whiteCount, hw, ↓reduceIte]
      rw [hc, Nat.pow_succ, Nat.mul_comm]
      exact ⟨h2.two, D_evper_double h1 hw⟩
    · have hc : whiteCount (j + 1) = whiteCount j := by
        simp only [whiteCount, hw, ↓reduceIte, Nat.add_zero]
      rw [hc]
      rcases D_evper_or_evwhite h1 h2 with h | h
      · exact ⟨h2, h⟩
      · exact absurd h hw

theorem D_evper_pow_whiteCount (j : Nat) : EvPer (D j) (2 ^ whiteCount j) :=
  (D_evper_pow_whiteCount_pair j).1

theorem D_evper_bounded_of_finite_white {N : Nat} (hN : ∀ j, N < j → ¬ EvWhite (D j)) :
    ∀ j, EvPer (D j) (2 ^ whiteCount N) := by
  have hc : ∀ j, N ≤ j → whiteCount j = whiteCount N := by
    intro j hj
    induction j with
    | zero => have : N = 0 := by omega
              subst this; rfl
    | succ j ih =>
      rcases Nat.lt_or_ge N (j + 1) with h | h
      · have : ¬ EvWhite (D (j + 1)) := hN _ h
        simp only [whiteCount, this, ↓reduceIte, Nat.add_zero]
        exact ih (by omega)
      · have : N = j + 1 := by omega
        rw [this]
  intro j
  rcases Nat.lt_or_ge j N with h | h
  ·
    have hmono : ∀ i k, i ≤ k → whiteCount i ≤ whiteCount k := by
      intro i k hik
      induction k with
      | zero => simp at hik; subst hik; exact Nat.le_refl _
      | succ k ih =>
        rcases Nat.lt_or_ge i (k + 1) with h' | h'
        · have := ih (by omega)
          simp only [whiteCount]
          omega
        · have : i = k + 1 := by omega
          subst this; exact Nat.le_refl _
    obtain ⟨T, hT⟩ := D_evper_pow_whiteCount j
    obtain ⟨d, hd⟩ : ∃ d, whiteCount N = whiteCount j + d := ⟨_, (Nat.add_sub_cancel' (hmono j N (by omega))).symm⟩
    refine ⟨T, fun t ht => ?_⟩
    rw [hd, Nat.pow_add]
    have := periodic_iter hT (2 ^ d) t ht
    rwa [Nat.mul_comm] at this
  · rw [← hc j h]; exact D_evper_pow_whiteCount j

/-! ### Half-Depth Bound on `whiteCount` and Square-Root Eventual Period `2 ^ (j / 2)` for `D j` -/

/-- **First Left Diagonal Is Never Eventually White (`D_one_not_evwhite`):** `¬ EvWhite (D 1)`. -/
theorem D_one_not_evwhite : ¬ EvWhite (D 1) := by
  rintro ⟨T, hT⟩
  have h1 := hT (T + 1) (by omega)
  rw [D_one] at h1
  exact Bool.noConfusion h1

/-- **Second Left Diagonal Is Eventually White (`D_two_evwhite`):** `EvWhite (D 2)`. -/
theorem D_two_evwhite : EvWhite (D 2) := by
  refine ⟨2, fun t ht => ?_⟩
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 2 := ⟨t - 2, by omega⟩
  have e : D 2 (u + 2) = xor (D 0 (u + 1)) (D 1 (u + 1) || D 2 (u + 1)) := D_step 0 (u + 1)
  rw [e, D_zero, D_one]
  rfl

/-- **No Two Consecutive Left Diagonals Are Eventually White (`no_two_consecutive_evwhite`):**
for every `j : Nat`, `¬ (EvWhite (D j) ∧ EvWhite (D (j + 1)))`. -/
theorem no_two_consecutive_evwhite : ∀ j, ¬ (EvWhite (D j) ∧ EvWhite (D (j + 1))) := by
  intro j
  induction j with
  | zero =>
    rintro ⟨⟨T, hT⟩, _⟩
    have := hT T (Nat.le_refl T)
    rw [D_zero] at this
    exact Bool.noConfusion this
  | succ j ih =>
    rintro ⟨h1, h2⟩
    apply ih
    refine ⟨?_, h1⟩
    obtain ⟨T2, hT2⟩ := h2
    obtain ⟨T1, hT1⟩ := h1
    refine ⟨max T1 T2, fun t ht => ?_⟩
    rw [D_white_of_eq (s := T2) hT2 t (by omega)]
    exact hT1 t (by omega)

open Classical in
/-- **Exact `whiteCount` Values up to Depth 3 (`whiteCount_one`, `whiteCount_two`, `whiteCount_three`):**
`whiteCount 1 = 0`, `whiteCount 2 = 1`, and `whiteCount 3 = 1`. -/
theorem whiteCount_one : whiteCount 1 = 0 := by
  simp [whiteCount, D_one_not_evwhite]

open Classical in
/-- **Exact `whiteCount` at Depth 2 (`whiteCount_two`):** `whiteCount 2 = 1`. -/
theorem whiteCount_two : whiteCount 2 = 1 := by
  rw [show (2 : Nat) = 1 + 1 by rfl, whiteCount, whiteCount_one]
  simp [D_two_evwhite]

open Classical in
/-- **Exact `whiteCount` at Depth 3 (`whiteCount_three`):** `whiteCount 3 = 1`. -/
theorem whiteCount_three : whiteCount 3 = 1 := by
  have hnot3 : ¬ EvWhite (D 3) := fun h3 => no_two_consecutive_evwhite 2 ⟨D_two_evwhite, h3⟩
  rw [show (3 : Nat) = 2 + 1 by rfl, whiteCount, whiteCount_two]
  simp [hnot3]

open Classical in
/-- **Two-Step Growth Bound on `whiteCount` (`whiteCount_add_two_le`):** because no two consecutive
diagonals can both be eventually white, `whiteCount (j + 2) ≤ whiteCount j + 1` for every `j`. -/
theorem whiteCount_add_two_le (j : Nat) : whiteCount (j + 2) ≤ whiteCount j + 1 := by
  have hno := no_two_consecutive_evwhite (j + 1)
  rw [show j + 2 = (j + 1) + 1 by rfl, whiteCount, whiteCount]
  by_cases h1 : EvWhite (D (j + 1))
  · have h2 : ¬ EvWhite (D (j + 1 + 1)) := fun h => hno ⟨h1, h⟩
    simp [h1, h2]
  · by_cases h2 : EvWhite (D (j + 1 + 1)) <;> simp [h1, h2]

/-- **Half-Depth Upper Bound on `whiteCount` (`whiteCount_le_half`):** for every `j : Nat`,
`whiteCount j ≤ j / 2`. -/
theorem whiteCount_le_half : ∀ j, whiteCount j ≤ j / 2 := by
  have pair : ∀ j, whiteCount j ≤ j / 2 ∧ whiteCount (j + 1) ≤ (j + 1) / 2 := by
    intro j
    induction j with
    | zero =>
      refine ⟨by simp [whiteCount], by rw [whiteCount_one]; decide⟩
    | succ j ih =>
      obtain ⟨h0, h1⟩ := ih
      refine ⟨h1, ?_⟩
      change whiteCount (j + 2) ≤ (j + 2) / 2
      have hstep := whiteCount_add_two_le j
      omega
  exact fun j => (pair j).1

/-- **Half-Rate Eventual Period `2 ^ (j / 2)` for Every Left Diagonal (`D_evper_pow_half`):**
for every `j : Nat`, `EvPer (D j) (2 ^ (j / 2))`. -/
theorem D_evper_pow_half (j : Nat) : EvPer (D j) (2 ^ (j / 2)) := by
  obtain ⟨T, hT⟩ := D_evper_pow_whiteCount j
  have hle := whiteCount_le_half j
  obtain ⟨d, hd⟩ : ∃ d, j / 2 = whiteCount j + d := ⟨j / 2 - whiteCount j, by omega⟩
  refine ⟨T, fun t ht => ?_⟩
  rw [hd, Nat.pow_add, Nat.mul_comm]
  exact periodic_iter hT (2 ^ d) t ht

/-! ### Multi-Step `whiteCount` Growth Bounds, Relative Period Scaling, and `D 1` / `D 2` Separation -/

/-- **Multi-Step Two-Diagonal Growth Bound on `whiteCount` (`whiteCount_add_two_mul_le`):**
for every `j d : Nat`, `whiteCount (j + 2 * d) ≤ whiteCount j + d`. -/
theorem whiteCount_add_two_mul_le (j : Nat) : ∀ d : Nat,
    whiteCount (j + 2 * d) ≤ whiteCount j + d
  | 0 => by simp
  | d + 1 => by
    have ih := whiteCount_add_two_mul_le j d
    have hstep := whiteCount_add_two_le (j + 2 * d)
    rw [show j + 2 * (d + 1) = j + 2 * d + 2 by omega]
    omega

open Classical in
theorem whiteCount_succ_le (j : Nat) : whiteCount (j + 1) ≤ whiteCount j + 1 := by
  simp only [whiteCount]
  split <;> omega

/-- **General Relative Growth Bound on `whiteCount` (`whiteCount_add_le_half_succ`):** for every
`j m : Nat`, `whiteCount (j + m) ≤ whiteCount j + (m + 1) / 2`. -/
theorem whiteCount_add_le_half_succ (j m : Nat) :
    whiteCount (j + m) ≤ whiteCount j + (m + 1) / 2 := by
  obtain ⟨d, rfl | rfl⟩ : ∃ d, m = 2 * d ∨ m = 2 * d + 1 := ⟨m / 2, by omega⟩
  · have h := whiteCount_add_two_mul_le j d
    omega
  · have h1 := whiteCount_succ_le (j + 2 * d)
    have h2 := whiteCount_add_two_mul_le j d
    rw [show j + (2 * d + 1) = j + 2 * d + 1 by omega]
    omega

/-- **Relative Period Scaling Across `2 * d` Left Diagonals
(`D_evper_pow_whiteCount_add_two_mul`):** for every `j d : Nat`,
`EvPer (D (j + 2 * d)) (2 ^ (whiteCount j + d))`. -/
theorem D_evper_pow_whiteCount_add_two_mul (j d : Nat) :
    EvPer (D (j + 2 * d)) (2 ^ (whiteCount j + d)) := by
  obtain ⟨T, hT⟩ := (D_evper_pow_whiteCount_pair (j + 2 * d)).1
  have hle := whiteCount_add_two_mul_le j d
  obtain ⟨q, hq⟩ : ∃ q, whiteCount j + d = whiteCount (j + 2 * d) + q :=
    ⟨whiteCount j + d - whiteCount (j + 2 * d), by omega⟩
  refine ⟨T, fun t ht => ?_⟩
  rw [hq, Nat.pow_add, Nat.mul_comm (2 ^ whiteCount (j + 2 * d)) (2 ^ q)]
  exact periodic_iter hT (2 ^ q) t ht

/-- **Exact Closed Form of `D 2` (`D_two_eq_false_of_two_le`):** for every `t ≥ 2`,
`D 2 t = false`. -/
theorem D_two_eq_false_of_two_le {t : Nat} (ht : 2 ≤ t) : D 2 t = false := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 2 := ⟨t - 2, by omega⟩
  have hstep := D_step 0 (s + 1)
  rw [show s + 1 + 1 = s + 2 by omega, D_zero, D_one, Bool.true_or] at hstep
  exact hstep

/-- **Permanent Separation of `D 1` and `D 2` (`D_one_and_D_two_of_two_le`):** for every `t ≥ 2`,
`D 1 t = true`, `D 2 t = false`, and `D 1 t ≠ D 2 t`. -/
theorem D_one_and_D_two_of_two_le {t : Nat} (ht : 2 ≤ t) :
    D 1 t = true ∧ D 2 t = false ∧ D 1 t ≠ D 2 t := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  have h1 : D 1 (s + 1) = true := D_one s
  have h2 : D 2 (s + 1) = false := D_two_eq_false_of_two_le ht
  refine ⟨h1, h2, ?_⟩
  rw [h1, h2]
  decide

end Rule30LeftReset
end Ruliology.CellularAutomata
