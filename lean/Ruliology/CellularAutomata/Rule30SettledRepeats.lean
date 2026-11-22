module

public import Ruliology.CellularAutomata.Rule30Diagonals
public import Ruliology.CellularAutomata.Rule30ClockNearSquares

/-!
# A length bound for a repeat's white run inside a settled band

Jen's clocked bound in window form (`Rule30ClockNearSquares.theorem_A'`; `Rule30FiniteMaskedJen.window_jen_col` for
any configuration with a leftmost black cell) says: if columns `i` and `i + 1` carry equal blocks of length `n` at
times `a < a'`, and the leftmost black cell is `L` cells left of column `i`, then `n ≤ L + a'`. The reason is a
white run. Row `a'` is white at the distances `L + a + 1 … n - 1` left of column `i`
(`Rule30ClockNearSquares.theorem_A3_white`). Read as left diagonals `D x0 e k t = evol x0 t (e - t + k)` from the
moving edge `e`, these are the diagonals `L + a' - n + 1 … a' - a - 1` at time `a'`. If these diagonals lie in the agreeing band, the white run can have length at most
`2 * P - 1`.

* `lemma_B3_sharp`, `lemma_B3`: if the diagonals `0 … M` agree at times `t - P` and `t` (`1 ≤ P ≤ t`), a white run
  `g + 1 … M'` of row `t` inside them (`M' ≤ M`) whose left neighbour `g` is black has length at most `2 * P - 1`.
* `theorem_A4_sharp`, `theorem_A4`: if, in addition to the block, the diagonals `0 … M` agree at times `a' - P` and
  `a'`, with `1 ≤ P ≤ a'` and `M < a' - a`, then `n ≤ L + a' - M + 2 * P - 1`. When `M ≥ 2 * P`,
  this improves `n ≤ L + a'` by `M - 2 * P + 1`.
* `center_A4_sharp`, `center_A4`: the same for the single seed, with the center column `Rule30Jen.cell t 0` and the
  diagonals `Rule30Diagonals.D`, and `L = 0`: `n ≤ a' - M + 2 * P - 1`.

**Method.** Lemma B3 follows the white run back in time. One step back, a white run bounded on the left by a black
cell is either older (white two cells wider, with a black cell two further left) or newborn (black on
`g - 1 … M' - 2`, and black at `M' - 1` or `M'`) (`back`). Going forward, the portion starting two cells farther right at each step stays
white up to the original right endpoint (`fwd`). Assume the run has length at least `2 * P`. If it were older at all
`P` steps back, the black cell `g` would be white
at time `t - P`, against the agreement. If it was born `s0 + 1` steps back, the run carried forward from time
`t - P` covers both `M' - 1` and `M'` at the birth time, one of which is black. Theorem A⁗ applies Lemma B3 to the run
of Theorem A‴. Its nearest black diagonal on the left exists because diagonal `0`, the edge, is black.

Nothing here decides Problem 1. The diagonals the run reaches have periods up to `2 ^ (a' - a)`, far above
`a' - a`, so the hypothesis `hper` is not known to hold for the center column's own repeats. Beside the kit:
`Rule30SettledBarrier` bounds constant runs of the center by settled white diagonals, and `Rule30DrivenLeftWindows`
bounds periodic agreement windows by their start. This module bounds a repeated block of two adjacent columns by the
width of the settled band.

**Credit.** The clocked bound is Jen's (E. Jen, J. Stat. Phys. 43, 1986). This module is the Lean-verified
submission `R30-20261022-1d5070`.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30SettledRepeats

open Rule30Realization (evol seed evol_seed)
open Rule30Jen (cell)
open Rule30ClockNearSquares (edge D D_succ theorem_A' theorem_A3_white)

/-! ### Lemma B3 -/

/-- A white cell at time τ + 1 forces D_(k-2) = D_(k-1) or D_k at time τ. -/
theorem constraint (x0 : Int → Bool) (e k : Int) (τ : Nat) (h : D x0 e k (τ + 1) = false) :
    D x0 e (k - 2) τ = (D x0 e (k - 1) τ || D x0 e k τ) := by
  rw [D_succ] at h
  revert h
  cases D x0 e (k - 2) τ <;> cases (D x0 e (k - 1) τ || D x0 e k τ) <;> simp

/-- One step back from a white run bounded by a black cell: older (white two wider, black two further left), or
newborn (black on [g - 1, M' - 2], and black at M' - 1 or M'). -/
theorem back (x0 : Int → Bool) (e g M' : Int) (τ : Nat) (hgM : g + 1 ≤ M') (hg : D x0 e g (τ + 1) = true)
    (hw : ∀ k, g + 1 ≤ k → k ≤ M' → D x0 e k (τ + 1) = false) :
    ((∀ k, g - 1 ≤ k → k ≤ M' → D x0 e k τ = false) ∧ D x0 e (g - 2) τ = true) ∨
    ((∀ k, g - 1 ≤ k → k ≤ M' - 2 → D x0 e k τ = true) ∧ (D x0 e (M' - 1) τ = true ∨ D x0 e M' τ = true)) := by
  by_cases hall : ∀ k, g - 1 ≤ k → k ≤ M' → D x0 e k τ = false
  · left
    refine ⟨hall, ?_⟩
    have := hg
    rw [D_succ, hall (g - 1) (Int.le_refl _) (by omega), hall g (by omega) (by omega)] at this
    simpa using this
  · right
    obtain ⟨k0, hk0a, hk0b, hk0⟩ : ∃ k0, g - 1 ≤ k0 ∧ k0 ≤ M' ∧ D x0 e k0 τ ≠ false := by
      refine Classical.byContradiction fun hno => hall fun k h1 h2 => ?_
      cases hD : D x0 e k τ
      · rfl
      · exact absurd ⟨k, h1, h2, by rw [hD]; decide⟩ hno
    have hk0' : D x0 e k0 τ = true := by simpa using hk0
    have top : D x0 e (M' - 1) τ = true ∨ D x0 e M' τ = true := by
      refine Classical.byContradiction fun hn => ?_
      have h1 : D x0 e (M' - 1) τ = false := by
        cases h : D x0 e (M' - 1) τ
        · rfl
        · exact absurd (Or.inl h) hn
      have h2 : D x0 e M' τ = false := by
        cases h : D x0 e M' τ
        · rfl
        · exact absurd (Or.inr h) hn
      have down : ∀ n : Nat, ∀ k, k = M' - n → g - 1 ≤ k → D x0 e k τ = false := by
        intro n
        induction n using Nat.strongRecOn with
        | ind n ih =>
          intro k hk hkg
          rcases n with _ | _ | n
          · rw [hk]; simpa using h2
          · rw [hk]; simpa using h1
          · have c := constraint x0 e (k + 2) τ (hw (k + 2) (by omega) (by omega))
            rw [show k + 2 - 2 = k by omega, show k + 2 - 1 = k + 1 by omega,
              ih (n + 1) (by omega) (k + 1) (by omega) (by omega),
              ih n (by omega) (k + 2) (by omega) (by omega)] at c
            simpa using c
      have := down (M' - k0).toNat k0 (by omega) hk0a
      rw [hk0'] at this; exact absurd this (by decide)
    have downB : ∀ n : Nat, ∀ k, k = M' - 2 - n → g - 1 ≤ k → D x0 e k τ = true := by
      intro n
      induction n with
      | zero =>
        intro k hk hkg
        have c := constraint x0 e (k + 2) τ (hw (k + 2) (by omega) (by omega))
        rw [show k + 2 - 2 = k by omega, show k + 2 - 1 = k + 1 by omega] at c
        rw [c]
        rcases top with h | h
        · rw [show k + 1 = M' - 1 by omega, h]; rfl
        · rw [show k + 2 = M' by omega, h]; simp
      | succ n ih =>
        intro k hk hkg
        have c := constraint x0 e (k + 2) τ (hw (k + 2) (by omega) (by omega))
        rw [show k + 2 - 2 = k by omega, show k + 2 - 1 = k + 1 by omega] at c
        rw [c, ih (k + 1) (by omega) (by omega)]; rfl
    exact ⟨fun k hk1 hk2 => downB (M' - 2 - k).toNat k (by omega) hk1, top⟩

/-- The suffix starting two cells farther right per tick stays white up to the original right endpoint. -/
theorem fwd (x0 : Int → Bool) (e g M' : Int) (τ0 : Nat) (hw : ∀ k, g + 1 ≤ k → k ≤ M' → D x0 e k τ0 = false) :
    ∀ r : Nat, ∀ k, g + 1 + 2 * r ≤ k → k ≤ M' → D x0 e k (τ0 + r) = false := by
  intro r
  induction r with
  | zero => intro k h1 h2; simpa using hw k (by simpa using h1) h2
  | succ r ih =>
    intro k h1 h2
    rw [show τ0 + (r + 1) = (τ0 + r) + 1 by omega, D_succ, ih (k - 2) (by omega) (by omega),
      ih (k - 1) (by omega) (by omega), ih k (by omega) h2]
    rfl

/-- Lemma B3, sharp: the run is at most 2P - 1 long. In the newborn case, the black cell at M' - 1 or M' stops the
forward white range one cell before the black range [g - 2s0 - 1, M' - 2] would. -/
theorem lemma_B3_sharp (x0 : Int → Bool) (e : Int) (t P : Nat) (g M' M : Int) (hP : 1 ≤ P) (htP : P ≤ t) (hgM : g + 1 ≤ M')
    (hM : M' ≤ M) (hper : ∀ k, k ≤ M → D x0 e k (t - P) = D x0 e k t) (hg : D x0 e g t = true)
    (hw : ∀ k, g + 1 ≤ k → k ≤ M' → D x0 e k t = false) : M' - g ≤ 2 * P - 1 := by
  -- the older chain: A s, for s <= P, unless a birth (newborn case) happens first
  let A : Nat → Prop := fun s => (∀ k, g - 2 * s + 1 ≤ k → k ≤ M' → D x0 e k (t - s) = false) ∧
    D x0 e (g - 2 * s) (t - s) = true
  let B : Nat → Prop := fun s0 => (∀ k, g - 2 * s0 - 1 ≤ k → k ≤ M' - 2 → D x0 e k (t - s0 - 1) = true) ∧
    (D x0 e (M' - 1) (t - s0 - 1) = true ∨ D x0 e M' (t - s0 - 1) = true)
  have chain : ∀ s : Nat, s ≤ P → A s ∨ ∃ s0, s0 < s ∧ B s0 := by
    intro s
    induction s with
    | zero => intro _; left; exact ⟨fun k h1 h2 => by simpa using hw k (by simpa using h1) h2, by simpa using hg⟩
    | succ s ih =>
      intro hs
      rcases ih (by omega) with hA | ⟨s0, hs0, hB⟩
      · obtain ⟨hAw, hAb⟩ := hA
        have ht : t - s = (t - s - 1) + 1 := by omega
        rw [ht] at hAw hAb
        rcases back x0 e (g - 2 * s) M' (t - s - 1) (by omega) hAb hAw with ⟨hw2, hb2⟩ | ⟨hB, htop⟩
        · left
          refine ⟨fun k h1 h2 => ?_, ?_⟩
          · rw [show t - (s + 1) = t - s - 1 by omega]; exact hw2 k (by omega) h2
          · rw [show t - (s + 1) = t - s - 1 by omega, show g - 2 * ((s + 1 : Nat) : Int) = g - 2 * s - 2 by
              omega]; exact hb2
        · right
          exact ⟨s, by omega, fun k h1 h2 => hB k (by omega) h2, htop⟩
      · right; exact ⟨s0, by omega, hB⟩
  -- A P contradicts periodicity at the black cell g
  rcases chain P (Nat.le_refl P) with hA | ⟨s0, hs0, hB⟩
  · exfalso
    have := hA.1 g (by omega) (by omega)
    rw [hper g (by omega), hg] at this
    exact absurd this (by decide)
  · -- forward from t - P the run is white on [g + 1 + 2r, M'] at time t - P + r; at the birth time it would
    -- cover both M' - 1 and M', one of which is black
    obtain ⟨-, hBt⟩ := hB
    have hw0 : ∀ k, g + 1 ≤ k → k ≤ M' → D x0 e k (t - P) = false := fun k h1 h2 => by
      rw [hper k (by omega)]; exact hw k h1 h2
    have F := fwd x0 e g M' (t - P) hw0 (P - s0 - 1)
    rw [show t - P + (P - s0 - 1) = t - s0 - 1 by omega] at F
    refine Classical.byContradiction fun hlong => ?_
    rcases hBt with h | h
    · rw [F (M' - 1) (by omega) (by omega)] at h
      exact absurd h (by decide)
    · rw [F M' (by omega) (Int.le_refl _)] at h
      exact absurd h (by decide)

/-- Lemma B3, with the bound 2P, from the sharp form. -/
theorem lemma_B3 (x0 : Int → Bool) (e : Int) (t P : Nat) (g M' M : Int) (hP : 1 ≤ P) (htP : P ≤ t) (hgM : g + 1 ≤ M')
    (hM : M' ≤ M) (hper : ∀ k, k ≤ M → D x0 e k (t - P) = D x0 e k t) (hg : D x0 e g t = true)
    (hw : ∀ k, g + 1 ≤ k → k ≤ M' → D x0 e k t = false) : M' - g ≤ 2 * P := by
  have := lemma_B3_sharp x0 e t P g M' M hP htP hgM hM hper hg hw
  omega

/-! ### Theorem A⁗ -/

/-- Theorem A⁗, sharp (from `lemma_B3_sharp`). -/
theorem theorem_A4_sharp (x0 : Int → Bool) (i : Int) (L : Nat) (hc : x0 (i - L) = true) (hl : ∀ j < i - L, x0 j = false)
    (n a a' P : Nat) (M : Int) (haa : a < a') (hP : 1 ≤ P) (hPa : P ≤ a') (hMa : M < (a' : Int) - a)
    (hblock : ∀ s : Nat, s < n → evol x0 (a + s) i = evol x0 (a' + s) i ∧ evol x0 (a + s) (i + 1) = evol x0 (a' + s) (i + 1))
    (hper : ∀ k, k ≤ M → D x0 (i - L) k (a' - P) = D x0 (i - L) k a') :
    (n : Int) ≤ L + a' - M + 2 * P - 1 := by
  refine Classical.byContradiction fun hlong => ?_
  let e : Int := i - L
  have he : e = i - L := rfl
  -- A′: n ≤ L + a′, so the run's left end x = L + a′ - n + 1 is at least 1
  have hA' := theorem_A' x0 i L hc hl n a a' haa hblock
  -- the white run of A‴ in diagonal coordinates at time a′: diagonals x .. M
  let x : Int := (L : Int) + a' - n + 1
  have hx : x = (L : Int) + a' - n + 1 := rfl
  have white : ∀ k, x ≤ k → k ≤ M → D x0 e k a' = false := by
    intro k h1 h2
    have hk : 0 ≤ (L : Int) + a' - k := by omega
    have := theorem_A3_white x0 i L hc hl n a a' hblock ((L : Int) + a' - k).toNat (by omega) (by omega)
    unfold D
    rw [show e - (a' : Int) + k = i - (((L : Int) + a' - k).toNat : Int) by rw [he, Int.toNat_of_nonneg hk]; omega]
    exact this
  -- the edge diagonal 0 is black at a′
  have black0 : D x0 e 0 a' = true := by
    unfold D; simpa using (edge x0 e (by rw [he]; exact hc) (by rw [he]; exact hl) a').1
  -- the nearest black diagonal g < x
  have hx1 : 1 ≤ x := by omega
  obtain ⟨g, hg0, hgx, hgb, hgw⟩ : ∃ g : Int, 0 ≤ g ∧ g < x ∧ D x0 e g a' = true ∧
      ∀ k, g + 1 ≤ k → k ≤ x - 1 → D x0 e k a' = false := by
    -- search down from x - 1 to 0
    have key : ∀ m : Nat, ∀ y : Int, y = m → y ≤ x - 1 → (∀ k, y + 1 ≤ k → k ≤ x - 1 → D x0 e k a' = false) →
        ∃ g : Int, 0 ≤ g ∧ g < x ∧ D x0 e g a' = true ∧ ∀ k, g + 1 ≤ k → k ≤ x - 1 → D x0 e k a' = false := by
      intro m
      induction m with
      | zero =>
        intro y hy hyx hw
        exact ⟨0, Int.le_refl 0, by omega, black0, fun k h1 h2 => hw k (by omega) h2⟩
      | succ m ih =>
        intro y hy hyx hw
        by_cases hb : D x0 e y a' = true
        · exact ⟨y, by omega, by omega, hb, hw⟩
        · apply ih (y - 1) (by omega) (by omega)
          intro k h1 h2
          rcases (show k = y ∨ y + 1 ≤ k by omega) with h | h
          · subst h; simpa using hb
          · exact hw k h h2
    exact key (x - 1).toNat (x - 1) (by omega) (Int.le_refl _) (fun k h1 h2 => by omega)
  -- Lemma B3 on the run [g + 1, M]
  have hB3 := lemma_B3_sharp x0 e a' P g M M hP hPa (by omega) (Int.le_refl M) hper hgb (fun k h1 h2 => by
    rcases (show k ≤ x - 1 ∨ x ≤ k by omega) with h | h
    · exact hgw k h1 h
    · exact white k h h2)
  omega

/-- Theorem A⁗, with the bound 2P, from the sharp form. -/
theorem theorem_A4 (x0 : Int → Bool) (i : Int) (L : Nat) (hc : x0 (i - L) = true) (hl : ∀ j < i - L, x0 j = false)
    (n a a' P : Nat) (M : Int) (haa : a < a') (hP : 1 ≤ P) (hPa : P ≤ a') (hMa : M < (a' : Int) - a)
    (hblock : ∀ s : Nat, s < n → evol x0 (a + s) i = evol x0 (a' + s) i ∧ evol x0 (a + s) (i + 1) = evol x0 (a' + s) (i + 1))
    (hper : ∀ k, k ≤ M → D x0 (i - L) k (a' - P) = D x0 (i - L) k a') :
    (n : Int) ≤ L + a' - M + 2 * P := by
  have := theorem_A4_sharp x0 i L hc hl n a a' P M haa hP hPa hMa hblock hper
  omega

/-! ## The bridge to the kit's statements: the center column and `Rule30Diagonals.D` -/

theorem seed_leftmost : seed 0 = true ∧ ∀ p : Int, p < 0 → seed p = false := by
  refine ⟨by simp [seed], fun p hp => ?_⟩
  simp only [seed, decide_eq_false_iff_not]; omega

/-- The diagonal `D seed 0 j t` is the kit's `Rule30Diagonals.D j t = cell t (j - t)`. -/
theorem D_seed (j t : Nat) : D seed 0 (j : Int) t = Rule30Diagonals.D j t := by
  simp only [D, Rule30Diagonals.D, evol_seed]
  congr 1; omega

/-- Left of the edge every diagonal is white. -/
theorem D_seed_neg (k : Int) (hk : k < 0) (t : Nat) : D seed 0 k t = false := by
  unfold D
  exact (edge seed 0 seed_leftmost.1 seed_leftmost.2 t).2 _ (by omega)

/-- The periodicity hypothesis of the kit's diagonals, for `0 ≤ k ≤ M`, gives the module's for every `k ≤ M`. -/
theorem per_seed (P a' : Nat) (M : Int)
    (hper : ∀ k : Nat, (k : Int) ≤ M → Rule30Diagonals.D k (a' - P) = Rule30Diagonals.D k a') :
    ∀ k : Int, k ≤ M → D seed 0 k (a' - P) = D seed 0 k a' := by
  intro k hk
  rcases Int.lt_or_le k 0 with hneg | hnn
  · rw [D_seed_neg k hneg, D_seed_neg k hneg]
  · obtain ⟨m, rfl⟩ : ∃ m : Nat, k = m := ⟨k.toNat, by omega⟩
    rw [D_seed, D_seed]; exact hper m hk

/-- **Theorem A⁗ for the center column, sharp.** Equal blocks of length `n` on columns `0` and `1` at times
`a < a′`, and the kit's left diagonals `0 … M` agreeing at times `a′ - P` and `a′` with `M < a′ - a`: then
`n ≤ a′ - M + 2P - 1`. -/
theorem center_A4_sharp (n a a' P : Nat) (M : Int) (haa : a < a') (hP : 1 ≤ P) (hPa : P ≤ a') (hMa : M < (a' : Int) - a)
    (hblock : ∀ s : Nat, s < n → cell (a + s) 0 = cell (a' + s) 0 ∧ cell (a + s) 1 = cell (a' + s) 1)
    (hper : ∀ k : Nat, (k : Int) ≤ M → Rule30Diagonals.D k (a' - P) = Rule30Diagonals.D k a') :
    (n : Int) ≤ a' - M + 2 * P - 1 := by
  have h := theorem_A4_sharp seed 0 0 (by simpa using seed_leftmost.1) (by simpa using seed_leftmost.2)
    n a a' P M haa hP hPa hMa (fun s hs => by simpa [evol_seed] using hblock s hs)
    (by simpa using per_seed P a' M hper)
  simpa using h

/-- **Theorem A⁗ for the center column**, with the bound 2P. -/
theorem center_A4 (n a a' P : Nat) (M : Int) (haa : a < a') (hP : 1 ≤ P) (hPa : P ≤ a') (hMa : M < (a' : Int) - a)
    (hblock : ∀ s : Nat, s < n → cell (a + s) 0 = cell (a' + s) 0 ∧ cell (a + s) 1 = cell (a' + s) 1)
    (hper : ∀ k : Nat, (k : Int) ≤ M → Rule30Diagonals.D k (a' - P) = Rule30Diagonals.D k a') :
    (n : Int) ≤ a' - M + 2 * P := by
  have := center_A4_sharp n a a' P M haa hP hPa hMa hblock hper
  omega

end Ruliology.CellularAutomata.Rule30SettledRepeats
