module

public import Ruliology.CellularAutomata.Rule30Prize
public import Ruliology.CellularAutomata.Rule30EtherThreeErosion
public import Ruliology.CellularAutomata.Rule30ZeroBoundary

/-!
# Period-three ether erosion with a white right tail

Research extension of Luis Perez Morales and Claude's independently replayed
PR 10 (`f6885abec122a9dcbb3160cb69312323bc075dc1`). Their front certificate and
good-state potential are used unchanged. This file replaces the finite
perturbation's rightmost defect by a linearly bounded witness of a defect.
The dependency is not yet part of the reference kit at 2f63afd.

This concerns an ether-driven right half. It does not exclude a period-three
center column and does not prove any prize problem.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30WhiteTailErosion

open Rule30Jen Rule30Ether Rule30EtherThree Rule30EtherThreeErosion

theorem front_le_witness {F : Nat → Nat → Bool} {j0 s t D R : Nat}
    (hD : Front F j0 s t D)
    (hR : ∃ p, p ≤ R ∧ F t p ≠ eth j0 s p t) : D ≤ R := by
  obtain ⟨p, hp, hne⟩ := hR
  exact Nat.le_of_not_lt fun h => hne (hD.1 p (by omega))

/-- The earlier bad-state argument needs only a defect witness of speed one. -/
theorem run_bad_bounded {F : Nat → Nat → Bool} (hF : IsR30 F) {j0 s t1 R : Nat}
    (h0 : ∀ t, t1 ≤ t → F t 0 = eth j0 s 0 t)
    (hbound : ∀ t, t1 ≤ t → ∃ p, p ≤ R + (t - t1) ∧ F t p ≠ eth j0 s p t) :
    ∀ m t D, t1 ≤ t → 2 ≤ D → Front F j0 s t D → IsB F j0 s t D →
      R + (t - t1) < D + 7 * m →
      ∃ n, n < m ∧ ∃ D', Front F j0 s (t + n + 1) D' ∧
        ¬ IsB F j0 s (t + n + 1) D' ∧ 2 ≤ D' := by
  intro m
  induction m with
  | zero =>
      intro t D ht _ hD _ hRD
      have := front_le_witness hD (hbound t ht)
      omega
  | succ m ih =>
      intro t D ht hD2 hD hB hRD
      obtain ⟨p, hp, hne⟩ := hbound (t + 1) (by omega)
      obtain ⟨D', hD', hle, h | h | h⟩ :=
        front_step hF (h0 (t + 1) (by omega)) hD2 hD ⟨p, hne⟩
      · exact absurd hB h.1
      · exact ⟨0, by omega, D', hD', h.2.1, by omega⟩
      · by_cases hB' : IsB F j0 s (t + 1) D'
        · have c1 := isB_cls hB
          have c2 := isB_cls hB'
          unfold cls at c1 c2
          have h8 : D + 8 ≤ D' := by omega
          obtain ⟨n, hn, D'', h1, h2, h3⟩ :=
            ih (t + 1) D' (by omega) (by omega) hD' hB' (by omega)
          refine ⟨n + 1, by omega, D'', ?_, ?_, h3⟩
          · rw [show t + (n + 1) + 1 = t + 1 + n + 1 by omega]; exact h1
          · rw [show t + (n + 1) + 1 = t + 1 + n + 1 by omega]; exact h2
        · exact ⟨0, by omega, D', hD', hB', by omega⟩

/-- Erosion holds whenever some defect remains below an edge of speed one. -/
theorem erosion_bounded {F : Nat → Nat → Bool} (hF : IsR30 F)
    (j0 s t1 R k : Nat) (hk : 1 ≤ k)
    (h0 : ∀ t, t1 ≤ t → F t 0 = eth j0 s 0 t)
    (hbound : ∀ t, t1 ≤ t → ∃ p, p ≤ R + (t - t1) ∧ F t p ≠ eth j0 s p t) :
    ∃ t, t1 ≤ t ∧ t ≤ t1 + 3 * (R - k) + 6 ∧
      ∃ p, 1 ≤ p ∧ p ≤ k ∧ F t p ≠ eth j0 s p t := by
  have hex : ∀ t, t1 ≤ t → ∃ p, F t p ≠ eth j0 s p t := by
    intro t ht
    obtain ⟨p, _, hp⟩ := hbound t ht
    exact ⟨p, hp⟩
  obtain ⟨p, _, hp⟩ := hbound t1 (Nat.le_refl _)
  obtain ⟨D1, hD1, hmin⟩ :=
    exists_least (P := fun q => F t1 q ≠ eth j0 s q t1) p hp
  have hfr1 : Front F j0 s t1 D1 :=
    ⟨fun q hq => Classical.not_not.1 (hmin q hq), hD1⟩
  have hpos : 1 ≤ D1 := by
    refine Nat.pos_of_ne_zero fun hz => ?_
    subst hz
    exact hD1 (h0 t1 (Nat.le_refl _))
  by_cases hDk : D1 ≤ k
  · exact ⟨t1, by omega, by omega, D1, hpos, hDk, hD1⟩
  have hD1R : D1 ≤ R := by
    simpa only [Nat.sub_self, Nat.add_zero] using front_le_witness hfr1 (hbound t1 (Nat.le_refl _))
  have finish : ∀ t0 D0, t1 ≤ t0 → Front F j0 s t0 D0 → ¬ IsB F j0 s t0 D0 →
      ∃ t, t0 ≤ t ∧ t ≤ t0 + (5 * (D0 - k) + 5) / 2 + 1 ∧
        ∃ p, 1 ≤ p ∧ p ≤ k ∧ F t p ≠ eth j0 s p t := by
    intro t0 D0 ht0 hD0 hB0
    rcases wake_good hF hk h0 hex ((5 * (D0 - k) + 5) / 2 + 1) t0 D0 ht0 hD0 hB0 with
      ⟨t', h1, h2, hp⟩ | ⟨D', hD', _, hpot⟩
    · exact ⟨t', h1, h2, hp⟩
    · have hpsi := psiF_le F j0 s t0 D0
      by_cases hD'k : D' ≤ k
      · refine ⟨t0 + ((5 * (D0 - k) + 5) / 2 + 1), by omega, by omega,
          D', ?_, hD'k, hD'.2⟩
        refine Nat.pos_of_ne_zero fun hz => ?_
        subst hz
        exact hD'.2 (h0 _ (by omega))
      · omega
  by_cases hB1 : IsB F j0 s t1 D1
  · obtain ⟨n, hn, D0, hD0, hB0, _⟩ :=
      run_bad_bounded hF h0 hbound ((R - D1) / 7 + 1) t1 D1
        (Nat.le_refl _) (by omega) hfr1 hB1 (by omega)
    have hD0R := front_le_witness hD0 (hbound (t1 + n + 1) (by omega))
    obtain ⟨t, h1, h2, hp⟩ := finish (t1 + n + 1) D0 (by omega) hD0 hB0
    exact ⟨t, by omega, by omega, hp⟩
  · obtain ⟨t, h1, h2, hp⟩ := finish t1 D1 (Nat.le_refl _) hfr1 hB1
    exact ⟨t, h1, by omega, hp⟩

/-- A white right tail remains white beyond a support bound of speed one. -/
theorem white_tail_evol {F : Nat → Nat → Bool} (hF : IsR30 F) (t1 W : Nat)
    (hW : ∀ p, W < p → F t1 p = false) :
    ∀ n p, W + n < p → F (t1 + n) p = false := by
  intro n
  induction n with
  | zero => simpa only [Nat.add_zero] using hW
  | succ n ih =>
      intro p hp
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      rw [show t1 + (n + 1) = (t1 + n) + 1 by omega, hF,
        ih q (by omega), ih (q + 1) (by omega), ih (q + 2) (by omega)]
      rfl

private theorem black_within_small : ∀ j : Fin 12, ∀ s : Fin 3,
    ∃ r : Fin 12, ether3 (j.val + r.val + 1) s.val = true := by decide +kernel

theorem ether_black_within (j s : Nat) :
    ∃ r, r < 12 ∧ ether3 (j + r + 1) s = true := by
  obtain ⟨r, hr⟩ := black_within_small ⟨j % 12, Nat.mod_lt _ (by decide)⟩
    ⟨s % 3, Nat.mod_lt _ (by decide)⟩
  refine ⟨r.val, r.isLt, ?_⟩
  have hc : ether3 (j + r.val + 1) s = ether3 (j % 12 + r.val + 1) (s % 3) :=
    ether3_congr (by omega) (by omega)
  rw [hc]
  exact hr

/-- A finite white-tailed right half always has a nearby defect from the ether. -/
theorem white_tail_defect {F : Nat → Nat → Bool} (hF : IsR30 F)
    (j0 s t1 W : Nat) (hW : ∀ p, W < p → F t1 p = false) (n : Nat) :
    ∃ p, p ≤ W + 12 + n ∧ F (t1 + n) p ≠ eth j0 s p (t1 + n) := by
  obtain ⟨r, hr, hblack⟩ := ether_black_within (j0 + (W + n)) (t1 + n + s)
  refine ⟨W + n + r + 1, by omega, ?_⟩
  have hf := white_tail_evol hF t1 W hW n (W + n + r + 1) (by omega)
  have he : eth j0 s (W + n + r + 1) (t1 + n) = true := by
    simpa only [eth, Nat.add_assoc] using hblack
  rw [hf, he]
  decide

/-- White tails, an infinite perturbation of the ether, also erode any prefix. -/
theorem white_tail_erosion {F : Nat → Nat → Bool} (hF : IsR30 F)
    (j0 s t1 W k : Nat) (hk : 1 ≤ k)
    (h0 : ∀ t, t1 ≤ t → F t 0 = eth j0 s 0 t)
    (hW : ∀ p, W < p → F t1 p = false) :
    ∃ t, t1 ≤ t ∧ t ≤ t1 + 3 * (W + 12 - k) + 6 ∧
      ∃ p, 1 ≤ p ∧ p ≤ k ∧ F t p ≠ eth j0 s p t := by
  apply erosion_bounded hF j0 s t1 (W + 12) k hk h0
  intro t ht
  have h := white_tail_defect hF j0 s t1 W hW (t - t1)
  simpa only [Nat.add_sub_of_le ht] using h

/-- The first right column departs from the matching ether arbitrarily late. -/
theorem white_tail_often_departs {F : Nat → Nat → Bool} (hF : IsR30 F)
    (j0 s t1 W : Nat)
    (h0 : ∀ t, t1 ≤ t → F t 0 = eth j0 s 0 t)
    (hW : ∀ p, W < p → F t1 p = false) :
    ∀ T, ∃ t, T ≤ t ∧ F t 1 ≠ eth j0 s 1 t := by
  intro T
  obtain ⟨t, ht, _, p, hp, hpk, hne⟩ :=
    white_tail_erosion hF j0 s (t1 + T) (W + T) 1 (by decide)
      (fun t ht => h0 t (by omega)) (white_tail_evol hF t1 W hW T)
  have heq : p = 1 := by omega
  subst heq
  exact ⟨t, by omega, hne⟩

/-! ### Finitely supported `drv` orbits under `ether3` depart from `eth` arbitrarily late -/

/-- **Finitely Supported Right Halves Driven by `ether3` Depart from the Matching Ether Arbitrarily Late (`finSupp_drv_often_departs`).** -/
theorem finSupp_drv_often_departs (x : Nat → Bool) (j0 s : Nat)
    (hfin : Rule30ZeroBoundary.FinSupp x) (T : Nat) :
    ∃ t, T ≤ t ∧
      drv (fun n => ether3 j0 (n + s)) x t 1 ≠ eth j0 s 1 t := by
  obtain ⟨W, hW⟩ := hfin
  have hF : IsR30 (drv (fun n => ether3 j0 (n + s)) x) :=
    drv_isR30 (fun n => ether3 j0 (n + s)) x
  have h0 : ∀ t, 0 ≤ t → drv (fun n => ether3 j0 (n + s)) x t 0 = eth j0 s 0 t := by
    intro t _
    rw [drv_col0]
    unfold eth
    rw [Nat.add_zero]
  have hW0 : ∀ p, W < p → drv (fun n => ether3 j0 (n + s)) x 0 p = false := by
    intro p hp
    rw [drv_init _ _ p (by omega)]
    exact hW p hp
  exact white_tail_often_departs hF j0 s 0 W h0 hW0 T

end Ruliology.CellularAutomata.Rule30WhiteTailErosion
