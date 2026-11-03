module

public import Ruliology.CellularAutomata.Rule30LeftReset

/-!
# Rule30LeftUnbounded

Unbounded left-diagonal periods, obtained from injectivity of consecutive periodic profiles. Consequently there are infinitely many eventually white diagonals.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30LeftUnbounded

open Rule30Diagonals Rule30LeftReset

theorem pigeonhole : ∀ (M N : Nat) (f : Nat → Nat), (∀ i, i < N → f i < M) →
    (∀ i j, i < N → j < N → f i = f j → i = j) → N ≤ M := by
  intro M
  induction M with
  | zero =>
    intro N f hb _
    cases N with
    | zero => exact Nat.le_refl 0
    | succ N => exact absurd (hb 0 (by omega)) (Nat.not_lt_zero _)
  | succ M ih =>
    intro N f hb hinj
    by_cases hex : ∃ i0, i0 < N ∧ f i0 = M
    · obtain ⟨i0, hi0, hf0⟩ := hex
      have hgb : ∀ k, k < N - 1 → (fun k => if k < i0 then f k else f (k + 1)) k < M := by
        intro k hk
        dsimp only
        split
        · have h1 := hb k (by omega)
          have h2 : f k ≠ M := fun h => by
            have := hinj k i0 (by omega) hi0 (h.trans hf0.symm); omega
          omega
        · have h1 := hb (k + 1) (by omega)
          have h2 : f (k + 1) ≠ M := fun h => by
            have := hinj (k + 1) i0 (by omega) hi0 (h.trans hf0.symm); omega
          omega
      have hginj : ∀ k l, k < N - 1 → l < N - 1 →
          (fun k => if k < i0 then f k else f (k + 1)) k =
          (fun k => if k < i0 then f k else f (k + 1)) l → k = l := by
        intro k l hk hl hkl
        dsimp only at hkl
        split at hkl <;> split at hkl
        · exact hinj k l (by omega) (by omega) hkl
        · have := hinj k (l + 1) (by omega) (by omega) hkl; omega
        · have := hinj (k + 1) l (by omega) (by omega) hkl; omega
        · have := hinj (k + 1) (l + 1) (by omega) (by omega) hkl; omega
      have := ih (N - 1) _ hgb hginj
      omega
    · have hb' : ∀ i, i < N → f i < M := by
        intro i hi
        have h1 := hb i hi
        have h2 : f i ≠ M := fun h => hex ⟨i, hi, h⟩
        omega
      exact Nat.le_succ_of_le (ih N f hb' hinj)

def code (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => code f n + (if f n then 2 ^ n else 0)

theorem code_lt (f : Nat → Bool) : ∀ n, code f n < 2 ^ n := by
  intro n
  induction n with
  | zero => simp [code]
  | succ n ih =>
    simp only [code, Nat.pow_succ]
    split <;> omega

theorem code_inj (f g : Nat → Bool) : ∀ n, code f n = code g n → ∀ r, r < n → f r = g r := by
  intro n
  induction n with
  | zero => intro _ r hr; omega
  | succ n ih =>
    intro h r hr
    have hf := code_lt f n
    have hg := code_lt g n
    simp only [code] at h
    have key : f n = g n ∧ code f n = code g n := by
      cases hfn : f n <;> cases hgn : g n <;> simp only [hfn, hgn] at h <;> simp at h <;>
        first | omega | exact ⟨rfl, by omega⟩
    rcases Nat.lt_or_ge r n with hlt | hge
    · exact ih key.2 r hlt
    · have : r = n := by omega
      subst this; exact key.1

def win (f : Nat → Bool) (Q S : Nat) : Nat → Bool := fun r => if r < Q then f (S + r) else false

def zero : Nat → Bool := fun _ => false

def Trunc (Q : Nat) (f : Nat → Bool) : Prop := ∀ r, Q ≤ r → f r = false

theorem win_trunc (f : Nat → Bool) (Q S : Nat) : Trunc Q (win f Q S) := by
  intro r hr; simp [win, Nat.not_lt.mpr hr]

theorem zero_trunc (Q : Nat) : Trunc Q zero := fun _ _ => rfl

def B (Q : Nat) (p : (Nat → Bool) × (Nat → Bool)) : (Nat → Bool) × (Nat → Bool) :=
  (fun r => if r < Q then xor (if r + 1 < Q then p.2 (r + 1) else p.2 0) (p.1 r || p.2 r)
    else false, p.1)

def Bpow (Q : Nat) : Nat → (Nat → Bool) × (Nat → Bool) → (Nat → Bool) × (Nat → Bool)
  | 0, p => p
  | k + 1, p => B Q (Bpow Q k p)

theorem B_zero (Q : Nat) : B Q (zero, zero) = (zero, zero) := by
  unfold B
  rw [Prod.mk.injEq]
  refine ⟨funext fun r => ?_, rfl⟩
  simp [zero]

theorem Bpow_zero (Q : Nat) : ∀ k, Bpow Q k (zero, zero) = (zero, zero) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => simp only [Bpow, ih, B_zero]

def Sig (Q S : Nat) : Nat → (Nat → Bool) × (Nat → Bool)
  | 0 => (zero, zero)
  | 1 => (zero, win (D 0) Q S)
  | i + 2 => (win (D i) Q S, win (D (i + 1)) Q S)

theorem Sig_trunc (Q S : Nat) : ∀ i, Trunc Q (Sig Q S i).1 ∧ Trunc Q (Sig Q S i).2
  | 0 => ⟨zero_trunc Q, zero_trunc Q⟩
  | 1 => ⟨zero_trunc Q, win_trunc _ Q S⟩
  | _ + 2 => ⟨win_trunc _ Q S, win_trunc _ Q S⟩

theorem xor_cancel (a b : Bool) : xor (xor a b) b = a := by cases a <;> cases b <;> rfl

theorem B_Sig_succ {m Q S : Nat} (hQ : 0 < Q) (hS : 1 ≤ S)
    (hper : ∀ j, j ≤ m + 1 → ∀ t, S ≤ t → D j (t + Q) = D j t) :
    ∀ i, i ≤ m + 1 → B Q (Sig Q S (i + 1)) = Sig Q S i := by
  intro i hi
  match i with
  | 0 =>
    show B Q (zero, win (D 0) Q S) = (zero, zero)
    unfold B
    rw [Prod.mk.injEq]
    refine ⟨funext fun r => ?_, rfl⟩
    simp only [win, zero, D_zero]
    split
    · split <;> simp [*]
    · rfl
  | 1 =>
    show B Q (win (D 0) Q S, win (D 1) Q S) = (zero, win (D 0) Q S)
    unfold B
    rw [Prod.mk.injEq]
    refine ⟨funext fun r => ?_, rfl⟩
    simp only [win, zero, D_zero]
    split
    · rename_i hr
      have h1 : ∀ x, D 1 (S + x) = true := by
        intro x
        obtain ⟨s, hs⟩ : ∃ s, S + x = s + 1 := ⟨S + x - 1, by omega⟩
        rw [hs, D_one]
      have h1' : D 1 S = true := by have := h1 0; simpa using this
      split <;> simp [*]
    · rfl
  | i + 2 =>
    show B Q (win (D (i + 1)) Q S, win (D (i + 2)) Q S) = (win (D i) Q S, win (D (i + 1)) Q S)
    unfold B
    rw [Prod.mk.injEq]
    refine ⟨funext fun r => ?_, rfl⟩
    simp only [win]
    split
    · rename_i hr
      have hstep := D_step i (S + r)
      rw [show S + r + 1 = S + (r + 1) by omega] at hstep
      try simp only [hr, ↓reduceIte]
      split
      · rename_i hr1
        try simp only [hr1, ↓reduceIte]
        rw [hstep, xor_cancel]
      · rename_i hr1
        try simp only [hQ, ↓reduceIte]
        have hwrap : D (i + 2) (S + 0) = D (i + 2) (S + (r + 1)) := by
          show D (i + 2) S = D (i + 2) (S + (r + 1))
          rw [show S + (r + 1) = S + Q by omega, hper (i + 2) (by omega) S (Nat.le_refl S)]
        first
          | rw [hwrap, hstep, xor_cancel]
          | (rw [Nat.add_zero] at hwrap; rw [hwrap, hstep, xor_cancel])
    · rfl

theorem Bpow_Sig {m Q S : Nat} (hQ : 0 < Q) (hS : 1 ≤ S)
    (hper : ∀ j, j ≤ m + 1 → ∀ t, S ≤ t → D j (t + Q) = D j t) :
    ∀ k i, k ≤ i → i ≤ m + 2 → Bpow Q k (Sig Q S i) = Sig Q S (i - k) := by
  intro k
  induction k with
  | zero => intro i _ _; simp [Bpow]
  | succ k ih =>
    intro i hk hi
    simp only [Bpow]
    rw [ih i (by omega) hi, show i - k = (i - (k + 1)) + 1 by omega,
      B_Sig_succ hQ hS hper (i - (k + 1)) (by omega)]

theorem Sig_inj {m Q S : Nat} (hQ : 0 < Q) (hS : 1 ≤ S)
    (hper : ∀ j, j ≤ m + 1 → ∀ t, S ≤ t → D j (t + Q) = D j t) :
    ∀ a b, a < b → b ≤ m + 2 → Sig Q S a ≠ Sig Q S b := by
  intro a b hab hb heq
  have h1 : Sig Q S 0 = Sig Q S (b - a) := by
    have e1 := Bpow_Sig hQ hS hper a a (Nat.le_refl _) (by omega)
    have e2 := Bpow_Sig hQ hS hper a b (by omega) hb
    rw [Nat.sub_self] at e1
    rw [← e1, heq, e2]
  have h2 : Sig Q S 1 = (zero, zero) := by
    have e3 := Bpow_Sig hQ hS hper (b - a - 1) (b - a) (by omega) (by omega)
    rw [show b - a - (b - a - 1) = 1 by omega] at e3
    rw [← e3, ← h1]
    exact Bpow_zero Q _
  have := congrArg (fun p => p.2 0) h2
  simp [Sig, win, zero, hQ, D_zero] at this

def pairCode (Q : Nat) (p : (Nat → Bool) × (Nat → Bool)) : Nat :=
  code (fun r => if r < Q then p.1 r else p.2 (r - Q)) (2 * Q)

theorem pairCode_lt (Q : Nat) (p : (Nat → Bool) × (Nat → Bool)) :
    pairCode Q p < 2 ^ (2 * Q) := code_lt _ _

theorem pairCode_inj {Q : Nat} {p p' : (Nat → Bool) × (Nat → Bool)}
    (h1 : Trunc Q p.1) (h2 : Trunc Q p.2) (h1' : Trunc Q p'.1) (h2' : Trunc Q p'.2)
    (h : pairCode Q p = pairCode Q p') : p = p' := by
  have key := code_inj _ _ _ h
  obtain ⟨u, v⟩ := p
  obtain ⟨u', v'⟩ := p'
  simp only at h1 h2 h1' h2' key
  rw [Prod.mk.injEq]
  constructor
  · funext r
    by_cases hr : r < Q
    · have := key r (by omega)
      simpa [hr] using this
    · rw [h1 r (by omega), h1' r (by omega)]
  · funext s
    by_cases hs : s < Q
    · have := key (s + Q) (by omega)
      simpa [show ¬ (s + Q < Q) by omega] using this
    · rw [h2 s (by omega), h2' s (by omega)]

theorem left_profile_bound {m Q S : Nat} (hQ : 0 < Q) (hS : 1 ≤ S)
    (hper : ∀ j, j ≤ m + 1 → ∀ t, S ≤ t → D j (t + Q) = D j t) : m + 3 ≤ 2 ^ (2 * Q) := by
  apply pigeonhole (2 ^ (2 * Q)) (m + 3) (fun i => pairCode Q (Sig Q S i))
  · intro i _; exact pairCode_lt Q _
  · intro i j hi hj hij
    have hij' : Sig Q S i = Sig Q S j :=
      pairCode_inj (Sig_trunc Q S i).1 (Sig_trunc Q S i).2 (Sig_trunc Q S j).1 (Sig_trunc Q S j).2
        hij
    rcases Nat.lt_trichotomy i j with h | h | h
    · exact absurd hij' (Sig_inj hQ hS hper i j h (by omega))
    · exact h
    · exact absurd hij'.symm (Sig_inj hQ hS hper j i h (by omega))

theorem common_threshold {Q : Nat} : ∀ m, (∀ j, j ≤ m → EvPer (D j) Q) →
    ∃ S, 1 ≤ S ∧ ∀ j, j ≤ m → ∀ t, S ≤ t → D j (t + Q) = D j t := by
  intro m
  induction m with
  | zero =>
    intro h
    obtain ⟨T, hT⟩ := h 0 (Nat.le_refl _)
    refine ⟨T + 1, by omega, fun j hj t ht => ?_⟩
    have : j = 0 := by omega
    subst this
    exact hT t (by omega)
  | succ m ih =>
    intro h
    obtain ⟨S, hS1, hS⟩ := ih (fun j hj => h j (by omega))
    obtain ⟨T, hT⟩ := h (m + 1) (Nat.le_refl _)
    refine ⟨max S T, by omega, fun j hj t ht => ?_⟩
    rcases Nat.lt_or_ge j (m + 1) with hlt | hge
    · exact hS j (by omega) t (by omega)
    · have : j = m + 1 := by omega
      subst this
      exact hT t (by omega)

theorem D_common_period_bound {m Q : Nat} (hQ : 0 < Q)
    (h : ∀ j, j ≤ m + 1 → EvPer (D j) Q) : m + 3 ≤ 2 ^ (2 * Q) := by
  obtain ⟨S, hS, hper⟩ := common_threshold (m + 1) h
  exact left_profile_bound hQ hS hper

theorem D_period_unbounded (Q : Nat) (hQ : 0 < Q) :
    ∃ j, j ≤ 2 ^ (2 * Q) ∧ ¬ EvPer (D j) Q := by
  by_cases h : ∃ j, j ≤ 2 ^ (2 * Q) ∧ ¬ EvPer (D j) Q
  · exact h
  · exfalso
    have hall : ∀ j, j ≤ 2 ^ (2 * Q) → EvPer (D j) Q := fun j hj =>
      Classical.byContradiction fun hj' => h ⟨j, hj, hj'⟩
    have hpos : 0 < 2 ^ (2 * Q) := Nat.two_pow_pos _
    have := D_common_period_bound hQ (m := 2 ^ (2 * Q) - 1) (fun j hj => hall j (by omega))
    omega

theorem EvPer.of_dvd {f : Nat → Bool} {L M : Nat} (h : EvPer f L) (hd : L ∣ M) : EvPer f M := by
  obtain ⟨T, hT⟩ := h
  obtain ⟨k, hk⟩ := hd
  exact ⟨T, fun t ht => by rw [hk, Nat.mul_comm, periodic_iter hT k t ht]⟩

def lcmAll : Nat → Nat
  | 0 => 1
  | n + 1 => lcmAll n * (n + 1)

theorem lcmAll_pos : ∀ n, 0 < lcmAll n
  | 0 => Nat.one_pos
  | n + 1 => Nat.mul_pos (lcmAll_pos n) (Nat.succ_pos n)

theorem dvd_lcmAll : ∀ n L, 0 < L → L ≤ n → L ∣ lcmAll n := by
  intro n
  induction n with
  | zero => intro L hL hLn; omega
  | succ n ih =>
    intro L hL hLn
    rcases Nat.lt_or_ge L (n + 1) with hlt | hge
    · exact Nat.dvd_trans (ih L hL (by omega)) (Nat.dvd_mul_right _ _)
    · have : L = n + 1 := by omega
      subst this
      exact Nat.dvd_mul_left _ _

theorem D_least_period_unbounded (Q : Nat) :
    ∃ j, ∀ L, 0 < L → L ≤ Q → ¬ EvPer (D j) L := by
  obtain ⟨j, _, hj⟩ := D_period_unbounded (lcmAll Q) (lcmAll_pos Q)
  exact ⟨j, fun L hL hLQ hper => hj (EvPer.of_dvd hper (dvd_lcmAll Q L hL hLQ))⟩

theorem D_infinitely_many_white (N : Nat) : ∃ j, N < j ∧ EvWhite (D j) := by
  by_cases h : ∃ j, N < j ∧ EvWhite (D j)
  · exact h
  · exfalso
    have hN : ∀ j, N < j → ¬ EvWhite (D j) := fun j hj hw => h ⟨j, hj, hw⟩
    have hb := D_evper_bounded_of_finite_white hN
    obtain ⟨j, _, hj⟩ := D_period_unbounded (2 ^ whiteCount N) (Nat.two_pow_pos _)
    exact hj (hb j)

theorem D_whiteCount_unbounded (N : Nat) : ∃ j, N < whiteCount j := by
  obtain ⟨j, _, hj⟩ := D_period_unbounded (2 ^ N) (Nat.two_pow_pos _)
  refine ⟨j, ?_⟩
  by_cases hc : N < whiteCount j
  · exact hc
  · exfalso
    apply hj
    have hd : 2 ^ whiteCount j ∣ 2 ^ N := Nat.pow_dvd_pow 2 (by omega)
    exact EvPer.of_dvd (D_evper_pow_whiteCount j) hd

theorem D_no_two_white : ∀ j, ¬ (EvWhite (D j) ∧ EvWhite (D (j + 1))) := by
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

theorem D_step_white {j t : Nat} (hw : D j t = false) :
    D (j + 2) (t + 1) = (D (j + 1) t || D (j + 2) t) := by
  rw [D_step, hw, Bool.false_xor]

theorem D_black_after_white {j : Nat} (hw : EvWhite (D j)) :
    ∃ T, ∀ t, T ≤ t → D (j + 2) t = true := by
  obtain ⟨T, hT⟩ := hw

  have hnw : ¬ EvWhite (D (j + 1)) := fun h => D_no_two_white j ⟨⟨T, hT⟩, h⟩
  have hex : ∃ t0, T ≤ t0 ∧ D (j + 1) t0 = true := by
    by_cases h : ∃ t0, T ≤ t0 ∧ D (j + 1) t0 = true
    · exact h
    · exfalso
      apply hnw
      refine ⟨T, fun t ht => ?_⟩
      cases hb : D (j + 1) t
      · rfl
      · exact absurd ⟨t, ht, hb⟩ h
  obtain ⟨t0, ht0, hb⟩ := hex
  refine ⟨t0 + 1, fun t ht => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, t = t0 + 1 + n := ⟨t - (t0 + 1), by omega⟩
  induction n with
  | zero => rw [Nat.add_zero, D_step_white (hT t0 ht0), hb]; rfl
  | succ n ih =>
    rw [show t0 + 1 + (n + 1) = (t0 + 1 + n) + 1 by omega,
      D_step_white (hT _ (by omega)), ih (by omega)]
    simp

theorem D_infinitely_many_black (N : Nat) : ∃ j, N < j ∧ ∃ T, ∀ t, T ≤ t → D j t = true := by
  obtain ⟨j, hj, hw⟩ := D_infinitely_many_white N
  exact ⟨j + 2, by omega, D_black_after_white hw⟩

/-! ### Explicit Quantitative Bounds on `whiteCount` and the Next Settled Diagonals -/

open Classical in
/-- **Monotonicity of `whiteCount` (`whiteCount_mono`):** for all `i ≤ k`,
`whiteCount i ≤ whiteCount k`. -/
theorem whiteCount_mono {i k : Nat} (hik : i ≤ k) : whiteCount i ≤ whiteCount k := by
  induction k with
  | zero =>
    have : i = 0 := by omega
    subst this
    exact Nat.le_refl _
  | succ k ih =>
    rcases Nat.lt_or_ge i (k + 1) with hlt | hge
    · have hle := ih (by omega)
      simp only [whiteCount]
      by_cases hw : EvWhite (D (k + 1)) <;> simp [hw] <;> omega
    · have : i = k + 1 := by omega
      subst this
      exact Nat.le_refl _

/-- **Quantitative Lower Bound on `whiteCount` at `2 ^ (2 * 2 ^ N)` (`whiteCount_two_pow_lower_bound`):**
for every `N : Nat`, `N + 1 ≤ whiteCount (2 ^ (2 * 2 ^ N))`. -/
theorem whiteCount_two_pow_lower_bound (N : Nat) :
    N + 1 ≤ whiteCount (2 ^ (2 * 2 ^ N)) := by
  obtain ⟨j, hj_le, hj_nper⟩ := D_period_unbounded (2 ^ N) (Nat.two_pow_pos _)
  have hj_gt : N < whiteCount j := by
    refine Classical.byContradiction fun hle => ?_
    have hd : 2 ^ whiteCount j ∣ 2 ^ N := Nat.pow_dvd_pow 2 (by omega)
    exact hj_nper (EvPer.of_dvd (D_evper_pow_whiteCount j) hd)
  have hmono := whiteCount_mono hj_le
  omega

open Classical in
/-- **Constancy of `whiteCount` Across a White-Free Interval (`whiteCount_eq_of_no_white_range`):**
if no `j` with `N < j ≤ M` satisfies `EvWhite (D j)`, then for every `k` with `N ≤ k ≤ M`,
`whiteCount k = whiteCount N`. -/
theorem whiteCount_eq_of_no_white_range {N M : Nat}
    (hno : ∀ j, N < j → j ≤ M → ¬ EvWhite (D j)) :
    ∀ k, N ≤ k → k ≤ M → whiteCount k = whiteCount N := by
  intro k hNk hkM
  induction k with
  | zero =>
    have : N = 0 := by omega
    subst this
    rfl
  | succ k ih =>
    rcases Nat.lt_or_ge N (k + 1) with hlt | hge
    · have hnw : ¬ EvWhite (D (k + 1)) := hno (k + 1) hlt hkM
      simp only [whiteCount, hnw, ↓reduceIte, Nat.add_zero]
      exact ih (by omega) (by omega)
    · have : N = k + 1 := by omega
      subst this
      rfl

/-- **Explicit Upper Bound on the Next Eventually White Diagonal (`D_next_white_explicit_bound`):**
for every `N : Nat`, there exists `j` with `N < j`, `j ≤ 2 ^ (2 * 2 ^ whiteCount N)`, and
`EvWhite (D j)`. -/
theorem D_next_white_explicit_bound (N : Nat) :
    ∃ j, N < j ∧ j ≤ 2 ^ (2 * 2 ^ whiteCount N) ∧ EvWhite (D j) := by
  by_cases h : ∃ j, N < j ∧ j ≤ 2 ^ (2 * 2 ^ whiteCount N) ∧ EvWhite (D j)
  · exact h
  · exfalso
    have hno : ∀ j, N < j → j ≤ 2 ^ (2 * 2 ^ whiteCount N) → ¬ EvWhite (D j) :=
      fun j h1 h2 hw => h ⟨j, h1, h2, hw⟩
    obtain ⟨j, hj_le, hj_nper⟩ :=
      D_period_unbounded (2 ^ whiteCount N) (Nat.two_pow_pos _)
    rcases Nat.lt_or_ge N j with hgt | hle
    · have hwc := whiteCount_eq_of_no_white_range hno j (by omega) hj_le
      have hper := D_evper_pow_whiteCount j
      rw [hwc] at hper
      exact hj_nper hper
    · have hmono := whiteCount_mono hle
      have hd : 2 ^ whiteCount j ∣ 2 ^ whiteCount N := Nat.pow_dvd_pow 2 hmono
      exact hj_nper (EvPer.of_dvd (D_evper_pow_whiteCount j) hd)

/-- **Explicit Upper Bound on the Next Settled White-Black Diagonal Pair (`D_next_settled_pair_explicit_bound`):**
for every `N : Nat`, there exists `j` with `N < j` and `j ≤ 2 ^ (2 * 2 ^ whiteCount N)` such that
`EvWhite (D j)` and `D (j + 2)` is eventually black. -/
theorem D_next_settled_pair_explicit_bound (N : Nat) :
    ∃ j, N < j ∧ j ≤ 2 ^ (2 * 2 ^ whiteCount N) ∧
      EvWhite (D j) ∧ (∃ T, ∀ t, T ≤ t → D (j + 2) t = true) := by
  obtain ⟨j, hj_gt, hj_le, hw⟩ := D_next_white_explicit_bound N
  exact ⟨j, hj_gt, hj_le, hw, D_black_after_white hw⟩

/-- **Explicit Upper Bound on the Next Eventually Black Diagonal (`D_next_black_explicit_bound`):**
for every `N : Nat`, there exists `j` with `N < j` and `j ≤ 2 ^ (2 * 2 ^ whiteCount N) + 2` such
that `D j` is eventually black (`∃ T, ∀ t, T ≤ t → D j t = true`). -/
theorem D_next_black_explicit_bound (N : Nat) :
    ∃ j, N < j ∧ j ≤ 2 ^ (2 * 2 ^ whiteCount N) + 2 ∧
      ∃ T, ∀ t, T ≤ t → D j t = true := by
  obtain ⟨j, hj_gt, hj_le, _, hb⟩ := D_next_settled_pair_explicit_bound N
  exact ⟨j + 2, by omega, by omega, hb⟩

end Rule30LeftUnbounded
end Ruliology.CellularAutomata
