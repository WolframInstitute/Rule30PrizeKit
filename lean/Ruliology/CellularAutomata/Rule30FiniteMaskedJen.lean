module

public import Ruliology.CellularAutomata.Rule30FiniteConfigs

/-!
# Masked and window forms of Jen's theorem for every finite configuration

`Rule30MaskedJen` sharpens Jen's theorem for the single black cell. Its proofs use the seed only
through the left edge, so, as in `Rule30FiniteConfigs`, they hold for every configuration `x` with
a leftmost black cell `lo`. Column `i` of the evolution is `t ↦ evol x t i`.

* `masked_jen`: if column `i` has period `P` from `T`, column `i + 1` does not have period `P`
  from `T` on the white times of column `i`.
* `orCol_not_eventuallyPeriodic`: if column `i` is eventually periodic, `orCol x i = column i ∨
  column (i + 1)` is not.
* `determine`, `window_jen_col`: **window form, no periodicity assumed.** Two times `t₁ < t₂` never
  carry the same values of column `i` on `[t, t + m]` and of `orCol x i` on `[t, t + m)` (for
  `t = t₁, t₂`) when `i - m = lo - t₂`: the reconstruction would make the cell at `lo - t₂` white
  at time `t₁` and black at time `t₂`, where the left edge is.
* `periodic_window`: if column `i` has period `P` from `T`, every window `[n, n + m)` with
  `n ≥ T + P` and `m = n + i - lo` contains a time `s` at which column `i` is white and column
  `i + 1` breaks period `P`. For the single seed (`lo = 0`, `i = 0`) this is `[n, 2n)`.

Source: E. Jen, *Global properties of cellular automata*, J. Stat. Phys. 43 (1986) 219–242; the
masked and window forms are those of `Rule30MaskedJen`.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30FiniteMaskedJen

open Rule30Jen Rule30Realization Rule30FiniteConfigs

/-- `column i ∨ column (i + 1)`: all that the reconstruction of column `i - 1` uses of column
`i + 1`. -/
def orCol (x : Int → Bool) (i : Int) (t : Nat) : Bool := evol x t i || evol x t (i + 1)

theorem evol_left' (x : Int → Bool) (t : Nat) (i : Int) :
    evol x t (i - 1) = xor (evol x (t + 1) i) (orCol x i t) :=
  evol_left x t i

section Masked
variable {x : Int → Bool} {lo : Int} (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
include hlo hzero

/-- **Masked Jen.** If column `i` has period `P` from time `T`, column `i + 1` does not have
period `P` from `T` on the white times of column `i`. -/
theorem masked_jen (i : Int) {T P : Nat} (hP : 0 < P)
    (h0 : ∀ t, T ≤ t → evol x (t + P) i = evol x t i)
    (h1 : ∀ t, T ≤ t → evol x t i = false → evol x (t + P) (i + 1) = evol x t (i + 1)) :
    False := by
  have hm1 : ∀ t, T ≤ t → evol x (t + P) (i - 1) = evol x t (i - 1) := by
    intro t ht
    rw [evol_left, evol_left x t, show t + P + 1 = (t + 1) + P by omega, h0 (t + 1) (by omega),
      h0 t ht]
    cases hc : evol x t i
    · rw [h1 t ht hc]
    · rfl
  refine not_adjacent hlo hzero (i - 1) ⟨T, P, hP, hm1⟩ ⟨T, P, hP, ?_⟩
  rw [show i - 1 + 1 = i by omega]
  exact h0

/-- **Masked Jen, `or` form.** If column `i` is eventually periodic, `orCol x i` is not. -/
theorem orCol_not_eventuallyPeriodic (i : Int) (hc : EventuallyPeriodic fun t => evol x t i) :
    ¬ EventuallyPeriodic (orCol x i) := by
  intro he
  obtain ⟨T, P, hP, hpc, hpe⟩ := common_period hc he
  refine not_adjacent hlo hzero (i - 1) ⟨T, P, hP, fun t ht => ?_⟩
    (by rw [show i - 1 + 1 = i by omega]; exact hc)
  show evol x (t + P) (i - 1) = evol x t (i - 1)
  rw [evol_left', evol_left', show t + P + 1 = (t + 1) + P by omega]
  have h1 : evol x ((t + 1) + P) i = evol x (t + 1) i := hpc (t + 1) (by omega)
  have h2 : orCol x i (t + P) = orCol x i t := hpe t ht
  rw [h1, h2]

end Masked

/-! ### Window forms: no periodicity assumed -/

/-- **Determination.** If column `i` agrees at times `t₁ + s`, `t₂ + s` for `s ≤ m` and `orCol x i`
agrees for `s < m`, then column `i - k` agrees for `s + k ≤ m`. -/
theorem determine (x : Int → Bool) {t₁ t₂ : Nat} {i : Int} (m : Nat)
    (hc : ∀ s, s ≤ m → evol x (t₁ + s) i = evol x (t₂ + s) i)
    (he : ∀ s, s < m → orCol x i (t₁ + s) = orCol x i (t₂ + s)) :
    ∀ k s, s + k ≤ m → evol x (t₁ + s) (i - k) = evol x (t₂ + s) (i - k) ∧
      (s + k < m → orCol x (i - k) (t₁ + s) = orCol x (i - k) (t₂ + s)) := by
  intro k
  induction k with
  | zero =>
    intro s hs
    rw [show i - ((0 : Nat) : Int) = i by omega]
    exact ⟨hc s (by omega), fun _ => he s (by omega)⟩
  | succ k ih =>
    intro s hs
    have hA : evol x (t₁ + s) (i - ((k + 1 : Nat) : Int)) =
        evol x (t₂ + s) (i - ((k + 1 : Nat) : Int)) := by
      have e : i - ((k + 1 : Nat) : Int) = (i - (k : Int)) - 1 := by omega
      rw [e, evol_left', evol_left', show t₁ + s + 1 = t₁ + (s + 1) by omega,
        show t₂ + s + 1 = t₂ + (s + 1) by omega, (ih (s + 1) (by omega)).1,
        (ih s (by omega)).2 (by omega)]
    refine ⟨hA, fun _ => ?_⟩
    have hB := (ih s (by omega)).1
    unfold orCol
    rw [hA, show i - ((k + 1 : Nat) : Int) + 1 = i - (k : Int) by omega, hB]

section Window
variable {x : Int → Bool} {lo : Int} (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
include hlo hzero

/-- **Window form of Jen's theorem.** Two times `t₁ < t₂` never carry the same (column `i`,
`orCol x i`) window of length `m` when `i - m = lo - t₂`. -/
theorem window_jen_col {t₁ t₂ : Nat} {i : Int} (m : Nat) (h : t₁ < t₂)
    (hm : i - (m : Int) = lo - (t₂ : Int))
    (hc : ∀ s, s ≤ m → evol x (t₁ + s) i = evol x (t₂ + s) i)
    (he : ∀ s, s < m → orCol x i (t₁ + s) = orCol x i (t₂ + s)) : False := by
  have key := (determine x m hc he m 0 (by omega)).1
  simp only [Nat.add_zero] at key
  rw [hm, evol_eq_false_of_lt hzero t₁ (lo - (t₂ : Int)) (by omega),
    evol_left_edge hlo hzero t₂] at key
  exact absurd key (by decide)

/-- **Windows of a periodic column.** If column `i` has period `P` from `T`, every window
`[n, n + m)` with `n ≥ T + P` and `i - m = lo - n` contains a time `s` at which column `i` is white
and column `i + 1` breaks period `P`. -/
theorem periodic_window {i : Int} {T P : Nat} (hP : 0 < P)
    (hc : ∀ t, T ≤ t → evol x (t + P) i = evol x t i) (n m : Nat) (hn : T + P ≤ n)
    (hm : i - (m : Int) = lo - (n : Int)) :
    ∃ s, n ≤ s ∧ s < n + m ∧ evol x s i = false ∧ evol x s (i + 1) ≠ evol x (s - P) (i + 1) := by
  refine Classical.byContradiction fun hne => ?_
  refine window_jen_col hlo hzero (t₁ := n - P) (t₂ := n) m (by omega) hm (fun s _ => ?_)
    (fun s hs => ?_)
  · have := hc (n - P + s) (by omega)
    rw [show n - P + s + P = n + s by omega] at this
    exact this.symm
  · have hper := hc (n - P + s) (by omega)
    rw [show n - P + s + P = n + s by omega] at hper
    unfold orCol
    rw [hper]
    cases h0 : evol x (n - P + s) i
    · have h0' : evol x (n + s) i = false := hper.trans h0
      have h1 : evol x (n + s) (i + 1) = evol x (n + s - P) (i + 1) :=
        Classical.byContradiction fun h1 => hne ⟨n + s, by omega, by omega, h0', h1⟩
      rw [show n + s - P = n - P + s by omega] at h1
      simp only [Bool.false_or, h1]
    · rfl

end Window

/-! ### Finite-configuration (`FinConfig`) masked and window forms of Jen's theorem -/

/-- **Finite-Configuration (`FinConfig`) Masked Jen and `orCol` Non-Periodicity (`masked_jen_and_orCol_finite`).** -/
theorem masked_jen_and_orCol_finite {x : Int → Bool}
    (hfin : Rule30PeriodTwoSideways.FinConfig x) (hne : ∃ p, x p = true) (i : Int) :
    (∀ {T P : Nat}, 0 < P →
      (∀ t, T ≤ t → evol x (t + P) i = evol x t i) →
      ¬ ∀ t, T ≤ t → evol x t i = false → evol x (t + P) (i + 1) = evol x t (i + 1)) ∧
    (EventuallyPeriodic (fun t => evol x t i) → ¬ EventuallyPeriodic (orCol x i)) := by
  obtain ⟨lo, hlo, hzero⟩ := exists_leftmost hfin hne
  exact ⟨fun hP h0 h1 => masked_jen hlo hzero i hP h0 h1,
         orCol_not_eventuallyPeriodic hlo hzero i⟩

/-- **Finite-Configuration (`FinConfig`) Window Form of Jen's Theorem (`window_jen_col_finite`).** -/
theorem window_jen_col_finite {x : Int → Bool}
    (hfin : Rule30PeriodTwoSideways.FinConfig x) (hne : ∃ p, x p = true) (i : Int) :
    ∃ lo : Int, x lo = true ∧ (∀ p, p < lo → x p = false) ∧
      ∀ {t₁ t₂ : Nat} (m : Nat), t₁ < t₂ → i - (m : Int) = lo - (t₂ : Int) →
        (∀ s, s ≤ m → evol x (t₁ + s) i = evol x (t₂ + s) i) →
        (∀ s, s < m → orCol x i (t₁ + s) = orCol x i (t₂ + s)) → False := by
  obtain ⟨lo, hlo, hzero⟩ := exists_leftmost hfin hne
  exact ⟨lo, hlo, hzero, fun m h hm hc he => window_jen_col hlo hzero m h hm hc he⟩

end Rule30FiniteMaskedJen
end Ruliology.CellularAutomata
