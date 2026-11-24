module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryPeriodLanes
public import Ruliology.CellularAutomata.Rule30StripCertificates

/-!
# `QP P` excludes every period-`P` word without two adjacent black cells

`Rule30ZeroBoundaryPeriodLanes.not_eventually_oneBlack_of_QP` excludes the word `0^(P-1) 1` from
`QP P`. The same argument needs only that the eventual center word never has two consecutive black
cells: at a black center step the next center cell is white, so the left neighbour must be black,
and the effective boundary `center t && center (t + 1)` of `Rule30DrivenLeft.cell_eq_L_effective`
is constantly white. A black step `t0` then repeats at `t0 + P * k`, which gives a finitely
supported zero-boundary start keeping column `-1` black at every `P`-th step.

* `not_eventually_isolated_of_QP`: if from some `T` on the center column is `P`-periodic, has no
  two consecutive black cells and has a black cell at some `t0 ≥ T`, then `QP P` fails.
* `not_eventuallyWord_isolated_of_QP`: the same for `Rule30StripCertificates.EventuallyWord w`, for
  every word `w` of length `P ≥ 2` with a black letter and no two cyclically adjacent black letters.

With `Rule30ZeroBoundaryPeriodLanes.QP_of_dvd`, `QP (N !)` for every `N` would exclude all such
words of every period. Nothing here proves any `QP P`.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30IsolatedBlackQP

open Rule30Jen Rule30Prize Rule30DrivenLeft Rule30ZeroBoundaryPeriodLanes

/-- **Isolated black cells.** If the center column is `P`-periodic from `T` on, never has two
consecutive black cells from `T` on, and is black at some `t0 ≥ T`, then `QP P` fails. -/
theorem not_eventually_isolated_of_QP {P : Nat} (hP : 2 ≤ P) (hQ : QP P) :
    ¬ ∃ T t0, T ≤ t0 ∧ center t0 = true ∧ (∀ t, T ≤ t → center (t + P) = center t) ∧
      (∀ t, T ≤ t → (center t && center (t + 1)) = false) := by
  rintro ⟨T, t0', ht0', hb', hper, hiso⟩
  -- one period later, so that the start time is positive
  let t0 := t0' + P
  have ht0 : T ≤ t0 := by simp only [t0]; omega
  have hb : center t0 = true := by simp only [t0]; rw [hper t0' ht0']; exact hb'
  have hperk : ∀ k, center (t0 + P * k) = true := by
    intro k; induction k with
    | zero => simpa using hb
    | succ k ih =>
      rw [show t0 + P * (k + 1) = (t0 + P * k) + P by rw [Nat.mul_succ]; omega,
        hper _ (by omega)]; exact ih
  have hfun : (fun k => center (t0 + k) && center (t0 + k + 1)) = fun _ => false := by
    funext k; exact hiso _ (by omega)
  refine hQ t0 (fun p => cell t0 p) (by simp only [t0]; omega)
    (fun p hp => cell_eq_false_of_lt t0 p hp) (cell_left_edge t0) (fun k => ?_)
  have e := cell_eq_L_effective t0 (P * k) (-1) (by omega)
  rw [hfun] at e
  rw [e]
  have c0 : cell (t0 + P * k) 0 = true := hperk k
  have c1 : cell (t0 + P * k + 1) 0 = false := by
    have h := hiso (t0 + P * k) (by omega)
    rw [hperk k] at h
    have h' : center (t0 + P * k + 1) = false := by simpa using h
    exact h'
  have := cell_left (t0 + P * k) 0
  rw [show (0 : Int) - 1 = -1 by rfl, show (0 : Int) + 1 = 1 by rfl, c0, c1] at this
  rw [this]; rfl

/-- **The reduction, as an eventual word.** For a word `w` of length `P ≥ 2` with a black letter
and no two cyclically adjacent black letters, `QP P` excludes
`Rule30StripCertificates.EventuallyWord w`. -/
theorem not_eventuallyWord_isolated_of_QP {P : Nat} (hP : 2 ≤ P) (hQ : QP P) {w : List Bool}
    (hlen : w.length = P) (hblack : ∃ i, i < P ∧ w.getD i false = true)
    (hiso : ∀ i, i < P → (w.getD i false && w.getD ((i + 1) % P) false) = false) :
    ¬ Rule30StripCertificates.EventuallyWord w := by
  rintro ⟨T, hT⟩
  rw [hlen] at hT
  obtain ⟨i, hi, hwi⟩ := hblack
  have hc : ∀ t, T ≤ t → center t = w.getD ((t - T) % P) false := fun t ht => hT t ht
  refine not_eventually_isolated_of_QP hP hQ ⟨T, T + i, by omega, ?_, fun t ht => ?_,
    fun t ht => ?_⟩
  · rw [hc _ (by omega), show T + i - T = i by omega, Nat.mod_eq_of_lt hi]; exact hwi
  · rw [hc _ (by omega), hc _ ht, show t + P - T = (t - T) + P by omega, Nat.add_mod_right]
  · rw [hc _ ht, hc _ (by omega), show t + 1 - T = (t - T) + 1 by omega,
      Nat.add_mod (t - T) 1 P, Nat.mod_eq_of_lt (show 1 < P by omega)]
    have h := hiso ((t - T) % P) (Nat.mod_lt _ (by omega))
    by_cases hlt : (t - T) % P + 1 < P
    · exact h
    · rw [show (t - T) % P + 1 = P by have := Nat.mod_lt (t - T) (show 0 < P by omega); omega,
        Nat.mod_self] at h ⊢
      exact h

end Rule30IsolatedBlackQP
end Ruliology.CellularAutomata
