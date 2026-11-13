module

public import Ruliology.CellularAutomata.Rule30BlackRuns

/-!
# Rule 30: the words `0^r 1 1` with `r ≥ 8`

`Rule30BlackRuns.no_white_run_11` excludes the repeating words `0^r 1 1` with `r ≥ 10`. The same
lemmas give the exclusion for every `r ≥ 8`:

* `no_white_run_11_ge8`: the center column is not eventually periodic with repeating word
  `0^r 1 1`, `r ≥ 8`, whatever the transient.

**Proof.** Column `1` is tracked at the starts of the periods. The `r ≥ 10` proof shows that it
turns black within two periods, outside one exceptional case, and stays black; that uses
`period_lock` at depths up to `r - 8`. Here two classes of period starts are tracked instead:
"column `1` black", which is absorbing (`period_lock` at depth `0`, which needs `r ≥ 8`), and
"column `1` white, column `2` black". A first black cell at depth `≤ r + 1` leads into one of them
in the next period (`period_late`), and depths `r + 2`, `r + 4` and beyond lead into one of them
within two periods (`period_z1`, `period_z3`, `period_z4`). If the remaining case, a first black
cell at depth `r + 3`, holds at every period start, column `1` reads `0^(r+1) 1` in every period
(`period_z2`). Otherwise the period starts eventually stay in the two classes, and column `1`
eventually reads `1^(r+1) 0` or `0 1^r 0` in every period. In each case column `1` is eventually
periodic, and so is column `0`, against Jen's theorem (`Rule30Jen.not_adjacent`).
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30WhiteRunEight

open Rule30Jen Rule30Prize Rule30BlackRuns

/-- **The words `0^r 1 1`, `r ≥ 8`, are excluded**: the center column of rule 30 is not
eventually periodic with repeating word `0^r 1 1`, whatever the transient. -/
theorem no_white_run_11_ge8 (T r t0 : Nat) (hr : 8 ≤ r)
    (hper : ∀ t, T ≤ t → center (t + (r + 2)) = center t) (ht0 : T ≤ t0)
    (hw : ∀ i, i < r → center (t0 + i) = false) (hb1 : center (t0 + r) = true)
    (hb2 : center (t0 + r + 1) = true) : False := by
  generalize hQdef : r + 2 = Q at hper
  have hQ : 0 < Q := by omega
  have hperk : ∀ k t, T ≤ t → center (t + k * Q) = center t := periodic_mul hper
  generalize hAdef : t0 + Q = A
  have hMul : ∀ k, (k + 1) * Q = k * Q + Q := fun k => Nat.succ_mul k Q
  have drvw : ∀ k i, i < r → cell (A + k * Q + i) 0 = false := by
    intro k i hi
    have := hperk (k + 1) (t0 + i) (by omega)
    show center (A + k * Q + i) = false
    rw [hMul k, show t0 + i + (k * Q + Q) = A + k * Q + i by omega] at this
    rw [this]; exact hw i hi
  have drvb1 : ∀ k, cell (A + k * Q + r) 0 = true := by
    intro k
    have := hperk (k + 1) (t0 + r) (by omega)
    show center (A + k * Q + r) = true
    rw [hMul k, show t0 + r + (k * Q + Q) = A + k * Q + r by omega] at this
    rw [this]; exact hb1
  have drvb2 : ∀ k, cell (A + k * Q + r + 1) 0 = true := by
    intro k
    have := hperk (k + 1) (t0 + r + 1) (by omega)
    show center (A + k * Q + r + 1) = true
    rw [hMul k, show t0 + r + 1 + (k * Q + Q) = A + k * Q + r + 1 by omega] at this
    rw [this]; exact hb2
  have hnext : ∀ k, A + k * Q + r + 2 = A + (k + 1) * Q := by intro k; rw [hMul k]; omega
  -- S0 k : column 1 black at the start of period k (class 0); it is absorbing for r ≥ 8
  have s0_step : ∀ k, cell (A + k * Q) 1 = true → cell (A + (k + 1) * Q) 1 = true := by
    intro k hk
    have := (period_lock (A + k * Q) r (drvw k) (drvb1 k) (drvb2 k) hr 0 (by omega)
      (fun p h1 h2 => by omega) (by simpa using hk)).2.2
    rwa [hnext k] at this
  -- first black cell at column ℓ+1 with ℓ ≤ r: next period is in class 0 or class 1
  have late : ∀ k ℓ, ℓ ≤ r → (∀ p : Nat, 1 ≤ p → p ≤ ℓ → cell (A + k * Q) p = false) →
      cell (A + k * Q) ((ℓ + 1 : Nat) : Int) = true →
      cell (A + (k + 1) * Q) 1 = true ∨
        (cell (A + (k + 1) * Q) 1 = false ∧ cell (A + (k + 1) * Q) 2 = true) := by
    intro k ℓ hℓ hwℓ hbℓ
    have := period_late (A + k * Q) r (drvw k) (drvb1 k) (drvb2 k) ℓ hℓ hwℓ hbℓ
    rwa [hnext k] at this
  have s1_step : ∀ k, (cell (A + k * Q) 1 = false ∧ cell (A + k * Q) 2 = true) →
      cell (A + (k + 1) * Q) 1 = true ∨
        (cell (A + (k + 1) * Q) 1 = false ∧ cell (A + (k + 1) * Q) 2 = true) := by
    intro k hk
    exact late k 1 (by omega) (fun p hp1 hp2 => by
      have : p = 1 := by omega
      subst this; simpa using hk.1) (by simpa using hk.2)
  have step01 : ∀ k, (cell (A + k * Q) 1 = true ∨
        (cell (A + k * Q) 1 = false ∧ cell (A + k * Q) 2 = true)) →
      (cell (A + (k + 1) * Q) 1 = true ∨
        (cell (A + (k + 1) * Q) 1 = false ∧ cell (A + (k + 1) * Q) 2 = true)) := by
    intro k h
    rcases h with h | h
    · exact Or.inl (s0_step k h)
    · exact s1_step k h
  let Z2 : Nat → Prop := fun k => (∀ p : Nat, 1 ≤ p → p ≤ r + 2 → cell (A + k * Q) p = false) ∧
    cell (A + k * Q) ((r + 2 + 1 : Nat) : Int) = true
  -- outside the exceptional class r + 2, the state is in class 0 or 1 two periods later
  have two_step : ∀ k, ¬ Z2 k → (cell (A + (k + 2) * Q) 1 = true ∨
        (cell (A + (k + 2) * Q) 1 = false ∧ cell (A + (k + 2) * Q) 2 = true)) := by
    intro k hz
    have hA1 : 1 ≤ A + k * Q := by omega
    obtain ⟨ℓ, hwℓ, hbℓ⟩ := first_black (A + k * Q) hA1
    have via : (cell (A + (k + 1) * Q) 1 = true ∨
        (cell (A + (k + 1) * Q) 1 = false ∧ cell (A + (k + 1) * Q) 2 = true)) →
        (cell (A + (k + 2) * Q) 1 = true ∨
        (cell (A + (k + 2) * Q) 1 = false ∧ cell (A + (k + 2) * Q) 2 = true)) := by
      intro h
      have := step01 (k + 1) h
      rwa [show k + 1 + 1 = k + 2 by omega] at this
    by_cases c2 : ℓ ≤ r
    · exact via (late k ℓ c2 hwℓ hbℓ)
    by_cases c3 : ℓ = r + 1
    · subst c3
      obtain ⟨h1, h2⟩ := period_z1 (A + k * Q) r (drvw k) (drvb1 k) (drvb2 k) hwℓ hbℓ
      rw [hnext k] at h1 h2
      exact via (Or.inr ⟨h1, h2⟩)
    by_cases c4 : ℓ = r + 2
    · subst c4
      exact absurd ⟨hwℓ, hbℓ⟩ hz
    by_cases c5 : ℓ = r + 3
    · subst c5
      obtain ⟨h1, h2, h3⟩ := period_z3 (A + k * Q) r (drvw k) (drvb1 k) (drvb2 k) hwℓ hbℓ
      rw [hnext k] at h1 h2 h3
      have := late (k + 1) 2 (by omega) (fun p hp1 hp2 => by
        by_cases hp : p = 1
        · subst hp; simpa using h1
        · have : p = 2 := by omega
          subst this; simpa using h2) (by simpa using h3)
      rwa [show k + 1 + 1 = k + 2 by omega] at this
    · have hz4 : 4 ≤ ℓ - r := by omega
      obtain ⟨h1, h2⟩ := period_z4 (A + k * Q) r (drvw k) (drvb1 k) (drvb2 k) (ℓ - r) hz4
        (fun p hp1 hp2 => hwℓ p hp1 (by omega)) (by rw [show r + (ℓ - r) + 1 = ℓ + 1 by omega]; exact hbℓ)
      rw [hnext k] at h1 h2
      exact via (Or.inr ⟨h1, h2⟩)
  -- column 1 over one period in each of the three possible eventual classes
  have pattern0 : ∀ k, cell (A + k * Q) 1 = true → ∀ i, i < Q →
      cell (A + k * Q + i) 1 = decide (i ≤ r) := by
    intro k hk i hi
    obtain ⟨hblk, c1, _⟩ := period_lock (A + k * Q) r (drvw k) (drvb1 k) (drvb2 k) hr 0
      (by omega) (fun p h1 h2 => by omega) (by simpa using hk)
    by_cases hir : i ≤ r
    · rw [hblk i (by omega) hir]; simp [hir]
    · have : i = r + 1 := by omega
      subst this; rw [show A + k * Q + (r + 1) = A + k * Q + r + 1 by omega, c1]; simp
  have pattern1 : ∀ k, (cell (A + k * Q) 1 = false ∧ cell (A + k * Q) 2 = true) → ∀ i, i < Q →
      cell (A + k * Q + i) 1 = decide (1 ≤ i ∧ i ≤ r) := by
    intro k hk i hi
    have hw1 : ∀ p : Nat, 1 ≤ p → p ≤ 1 → cell (A + k * Q) p = false := fun p hp1 hp2 => by
      have : p = 1 := by omega
      subst this; simpa using hk.1
    have hb1' : cell (A + k * Q) ((1 + 1 : Nat) : Int) = true := by simpa using hk.2
    have hfront := (front_moves (A + k * Q) 1 r (drvw k) hw1 hb1' 1 (by omega) (Nat.le_refl 1)).2
    rw [show 1 - 1 + 1 = 1 by omega] at hfront
    have hblk : ∀ j, 1 ≤ j → j ≤ r → cell (A + k * Q + j) 1 = true := by
      intro j h1 h2
      have := black_stays (A + k * Q + 1) (r - 1) (fun m hm => by
        have := drvw k (1 + m) (by omega)
        rwa [show A + k * Q + (1 + m) = A + k * Q + 1 + m by omega] at this)
        (by simpa using hfront) (j - 1) (by omega)
      rwa [show A + k * Q + 1 + (j - 1) = A + k * Q + j by omega] at this
    have c1 : cell (A + k * Q + r + 1) 1 = false := by
      show rule (cell (A + k * Q + r) (1 - 1)) (cell (A + k * Q + r) 1) (cell (A + k * Q + r) (1 + 1)) = false
      rw [show (1 : Int) - 1 = 0 by rfl, drvb1 k, hblk r (by omega) (Nat.le_refl r)]
      rfl
    by_cases hi0 : i = 0
    · subst hi0; simpa using hk.1
    by_cases hir : i ≤ r
    · rw [hblk i (by omega) hir]; simp; omega
    · have : i = r + 1 := by omega
      subst this; rw [show A + k * Q + (r + 1) = A + k * Q + r + 1 by omega, c1]; simp
  have z2_pattern : ∀ k, Z2 k → ∀ i, i < Q → cell (A + k * Q + i) 1 = decide (i = r + 1) := by
    intro k hk i hi
    obtain ⟨hw0, c1⟩ := period_z2 (A + k * Q) r (drvw k) (drvb1 k) hk.1 hk.2
    by_cases hir : i ≤ r
    · rw [hw0 i hir]; simp; omega
    · have : i = r + 1 := by omega
      subst this; rw [show A + k * Q + (r + 1) = A + k * Q + r + 1 by omega, c1]; simp
  have h1 : EventuallyPeriodic (fun t => cell t (0 + 1)) := by
    by_cases hall : ∀ k, Z2 k
    · exact periodic_blocks A Q hQ (fun i => decide (i = r + 1)) (fun j i hi => z2_pattern j (hall j) i hi)
    · have hex : ∃ k, ¬ Z2 k := Classical.byContradiction fun hne => hall fun k =>
        Classical.byContradiction fun hk => hne ⟨k, hk⟩
      obtain ⟨k, hk⟩ := hex
      have hU : ∀ j, cell (A + (k + 2 + j) * Q) 1 = true ∨
          (cell (A + (k + 2 + j) * Q) 1 = false ∧ cell (A + (k + 2 + j) * Q) 2 = true) := by
        intro j
        induction j with
        | zero => simpa using two_step k hk
        | succ j ih =>
          rw [show k + 2 + (j + 1) = (k + 2 + j) + 1 by omega]
          exact step01 _ ih
      by_cases hs0 : ∃ j, cell (A + (k + 2 + j) * Q) 1 = true
      · obtain ⟨j0, hj0⟩ := hs0
        have hall0 : ∀ j, cell (A + (k + 2 + j0 + j) * Q) 1 = true := by
          intro j
          induction j with
          | zero => simpa using hj0
          | succ j ih =>
            rw [show k + 2 + j0 + (j + 1) = (k + 2 + j0 + j) + 1 by omega]
            exact s0_step _ ih
        refine periodic_blocks (A + (k + 2 + j0) * Q) Q hQ (fun i => decide (i ≤ r)) (fun j i hi => ?_)
        have := pattern0 (k + 2 + j0 + j) (hall0 j) i hi
        have hm : (k + 2 + j0 + j) * Q = (k + 2 + j0) * Q + j * Q := Nat.add_mul (k + 2 + j0) j Q
        rwa [hm, show A + ((k + 2 + j0) * Q + j * Q) + i = A + (k + 2 + j0) * Q + j * Q + i by omega] at this
      · have hall1 : ∀ j, cell (A + (k + 2 + j) * Q) 1 = false ∧ cell (A + (k + 2 + j) * Q) 2 = true := by
          intro j
          rcases hU j with h | h
          · exact absurd ⟨j, h⟩ hs0
          · exact h
        refine periodic_blocks (A + (k + 2) * Q) Q hQ (fun i => decide (1 ≤ i ∧ i ≤ r)) (fun j i hi => ?_)
        have := pattern1 (k + 2 + j) (hall1 j) i hi
        have hm : (k + 2 + j) * Q = (k + 2) * Q + j * Q := Nat.add_mul (k + 2) j Q
        rwa [hm, show A + ((k + 2) * Q + j * Q) + i = A + (k + 2) * Q + j * Q + i by omega] at this
  have h0 : EventuallyPeriodic (fun t => cell t 0) := ⟨T, Q, hQ, hper⟩
  exact not_adjacent 0 h0 h1

/-! ## Word-form exclusions of `0^r 1 1` and `1 1 0^r` on the center column for `r ≥ 8` -/

/-- **Word-Form Exclusions of `0^r 1 1` and `1 1 0^r` on the Center Column for `r ≥ 8` (`no_white_run_11_word_and_post_ge8`).** -/
theorem no_white_run_11_word_and_post_ge8 (T r : Nat) (hr : 8 ≤ r) :
    (¬ ∀ t, T ≤ t → center t = (List.replicate r false ++ [true, true]).getD ((t - T) % (r + 2)) false) ∧
    (¬ ∀ t, T ≤ t → center t = (true :: true :: List.replicate r false).getD ((t - T) % (r + 2)) false) := by
  have hget1 : ∀ (m k : Nat),
      (List.replicate m false ++ [true, true]).getD k false = decide (k = m ∨ k = m + 1) := by
    intro m
    induction m with
    | zero => rintro (_ | _ | k) <;> rfl
    | succ m ih =>
      rintro (_ | k)
      · rfl
      · rw [List.replicate_succ, List.cons_append, List.getD_cons_succ, ih k]
        exact decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩
  have hget2 : ∀ (m k : Nat), k < m + 2 →
      (true :: true :: List.replicate m false).getD k false = decide (k = 0 ∨ k = 1) := by
    intro m
    rintro (_ | _ | k) hk
    · rfl
    · rfl
    · simp only [List.getD_cons_succ]
      have hrep : ∀ (n j : Nat), (List.replicate n false).getD j false = false := by
        intro n; induction n with
        | zero => intro _; rfl
        | succ n ih =>
          intro j
          cases j with
          | zero => rfl
          | succ j => rw [List.replicate_succ, List.getD_cons_succ]; exact ih j
      rw [hrep]
      exact (decide_eq_false (by omega)).symm
  refine ⟨fun hT => ?_, fun hT => ?_⟩
  · have hper : ∀ t, T ≤ t → center (t + (r + 2)) = center t := by
      intro t ht
      rw [hT (t + (r + 2)) (by omega), hT t ht,
          show t + (r + 2) - T = (t - T) + (r + 2) by omega, Nat.add_mod_right]
    refine no_white_run_11_ge8 T r T hr hper (Nat.le_refl T) (fun i hi => ?_) ?_ ?_
    · rw [hT (T + i) (by omega), show T + i - T = i by omega, Nat.mod_eq_of_lt (by omega), hget1]
      exact decide_eq_false (by omega)
    · rw [hT (T + r) (by omega), show T + r - T = r by omega, Nat.mod_eq_of_lt (by omega), hget1]
      exact decide_eq_true (by omega)
    · rw [hT (T + r + 1) (by omega), show T + r + 1 - T = r + 1 by omega, Nat.mod_eq_of_lt (by omega), hget1]
      exact decide_eq_true (by omega)
  · have hper : ∀ t, T ≤ t → center (t + (r + 2)) = center t := by
      intro t ht
      rw [hT (t + (r + 2)) (by omega), hT t ht,
          show t + (r + 2) - T = (t - T) + (r + 2) by omega, Nat.add_mod_right]
    refine no_white_run_11_ge8 T r (T + 2) hr hper (by omega) (fun i hi => ?_) ?_ ?_
    · rw [hT (T + 2 + i) (by omega), show T + 2 + i - T = i + 2 by omega,
          Nat.mod_eq_of_lt (by omega), hget2 r (i + 2) (by omega)]
      exact decide_eq_false (by omega)
    · rw [hT (T + 2 + r) (by omega), show T + 2 + r - T = 0 + 1 * (r + 2) by omega,
          Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega), hget2 r 0 (by omega)]
      rfl
    · rw [hT (T + 2 + r + 1) (by omega), show T + 2 + r + 1 - T = 1 + 1 * (r + 2) by omega,
          Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega), hget2 r 1 (by omega)]
      rfl

end Rule30WhiteRunEight
end Ruliology.CellularAutomata
