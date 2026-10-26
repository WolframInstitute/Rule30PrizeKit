module

public import Ruliology.CellularAutomata.Rule30Certificates.StripeTail13Completion
public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFour

/-! Complete four-bit stripe-prefix tails, including every odd prefix
with tail 13, using a sparse 32-state upper return orbit. -/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFourComplete
open Ruliology.CellularAutomata
open Rule30ZeroBoundaryStripeFront Rule30ZeroBoundary
open Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFrontLift Ruliology.CellularAutomata.Rule30Tail13Completion

theorem full_jump (j : Nat) (hj : j < 32) :
    orb 46 65536 (embedding j,0) = (embedding (nextIndex j),0) := by
  have h := run_correct (ALL:=lanes) (p:=j) (K:=34) (s:=state000)
    (lanes_bit j hj) (by decide) (by decide) (by decide) 65536
  rw [run_full, initial_word j hj, endpoint_word j hj] at h
  exact h

theorem prefix_jump (j : Nat) (hj : j < 32) :
    orb 46 61005 (embedding j,0) = (prefixWord j,1) := by
  have h := run_correct (ALL:=lanes) (p:=j) (K:=34) (s:=state000)
    (lanes_bit j hj) (by decide) (by decide) (by decide) 61005
  rw [run_prefix, initial_word j hj] at h
  exact h

theorem compressed_cycle : Cycle 46 45 13 0 2097152 := by
  change Cycle 46 45 (embedding 0) 0 (65536*32)
  apply return_map_cycle_lift (Klo:=34) (Khi:=46) (Slo:=33) (Shi:=45)
    (B:=13) (p:=0) (L:=65536) (N:=32) (u:=0) (q:=32)
    (J:=nextIndex) (embed:=embedding) (E:=fun r => r=61005)
    (by decide) (by decide) (by decide) (by decide) (fun _ _ => rfl)
    (by decide) (by decide) cyc13_period
  · intro r hr hp hne
    exact cyc13_sig r hr hp hne
  · intro v _
    exact Nat.mod_lt (v+1) (by decide)
  · decide
  · exact full_jump
  · decide
  · exact return_cycle
  · intro j hj e _ _ he
    subst e
    rw [iter_index j hj,prefix_jump j hj]
    exact rare_table_sound j hj

theorem compressed_row4_13 (m : Nat) (hq : m%2 = 1) :
    ∃ t, t ≤ m+45 ∧ t%2 = 0 ∧ zrow (row4 m 13) t 1 = false := by
  have hag : ∀ k, 1 ≤ k → k < m+1 → row4 m 13 k = stripe k := by
    intro k _ hk
    unfold row4
    rw [ite_eq_left (by omega)]
  have hwin : pk (fun i => row4 m 13 (m+1+i)) 46 = 13 := by
    have hw : pk (fun i => row4 m 13 (m+1+i)) 46 = pk (tail4 13) 46 :=
      pk_congr _ _ _ fun i _ => by
        unfold row4
        rw [ite_eq_right (by omega), show m+1+i-m-1 = i by omega]
    rw [hw]
    decide +kernel
  have hc : Cycle 46 45 (pk (fun i => row4 m 13 (m+1+i)) 46) ((m+1)%2) 2097152 := by
    rw [hwin, show (m+1)%2 = 0 by omega]
    exact compressed_cycle
  obtain ⟨s, hs, he, hz⟩ := front_sound (row4 m 13) (m+1) 46 45 2097152
    (by omega) hag (by omega) hc
  exact ⟨m+s, by omega, by simpa using he, by simpa using hz⟩


theorem cycle13_complete : Cycle 46 45 13 0 2097152 := compressed_cycle

theorem row4_13_all_odd (m : Nat) (hq : m % 2 = 1) :
    (∀ k, 1 ≤ k → k < m + 1 → row4 m 13 k = stripe k) ∧
      row4 m 13 (m + 1) ≠ stripe (m + 1) ∧
      ∃ t, t ≤ m + 45 ∧ t % 2 = 0 ∧ zrow (row4 m 13) t 1 = false := by
  have hag : ∀ k, 1 ≤ k → k < m + 1 → row4 m 13 k = stripe k := by
    intro k _ hk; unfold row4; rw [ite_eq_left (by omega)]
  have hdev : row4 m 13 (m + 1) ≠ stripe (m + 1) := by
    unfold row4
    rw [ite_eq_right (by omega), show m + 1 - m - 1 = 0 by omega,
      stripe_add_mod m 1 1 hq]
    decide
  have hwin : pk (fun i => row4 m 13 (m + 1 + i)) 46 = 13 := by
    have hw : pk (fun i => row4 m 13 (m + 1 + i)) 46 = pk (tail4 13) 46 :=
      pk_congr _ _ _ fun i _ => by
        unfold row4
        rw [ite_eq_right (by omega), show m + 1 + i - m - 1 = i by omega]
    rw [hw]; decide +kernel
  have hcyc : Cycle 46 45 (pk (fun i => row4 m 13 (m + 1 + i)) 46)
      ((m + 1) % 2) 2097152 := by
    rw [hwin, show (m + 1) % 2 = 0 by omega]
    exact cycle13_complete
  obtain ⟨s, hs, he, hz⟩ := front_sound (row4 m 13) (m + 1) 46 45 2097152
    (by omega) hag (by omega) hcyc
  exact ⟨hag, hdev, m + s, by omega, by simpa using he, by simpa using hz⟩

theorem stripe_four_tail_complete (m : Nat) (v : Fin 16) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 6 ∧
      (∀ k, 1 ≤ k → k < d → row4 m v.val k = stripe k) ∧
      row4 m v.val d ≠ stripe d ∧
      ∃ t, t ≤ d - 1 + 45 ∧ t % 2 = 0 ∧ zrow (row4 m v.val) t 1 = false := by
  by_cases h : v.val ≠ 13 ∨ m % 2 = 0
  · obtain ⟨d, hd, hdm, hag, hdev, t, ht, he, hz⟩ := stripe_four_tail m v h
    exact ⟨d, hd, hdm, hag, hdev, t, by omega, he, hz⟩
  · have hv : v.val = 13 := by omega
    have hq : m % 2 = 1 := by omega
    rw [hv]
    obtain ⟨hag, hdev, t, ht, he, hz⟩ := row4_13_all_odd m hq
    exact ⟨m + 1, by omega, by omega, hag, hdev, t, by omega, he, hz⟩


theorem row5_13_all_odd (m : Nat) (hq : m % 2 = 1) :
    (∀ k, 1 ≤ k → k < m + 1 → row5 m 13 k = stripe k) ∧
      row5 m 13 (m + 1) ≠ stripe (m + 1) ∧
      ∃ t, t ≤ m + 45 ∧ t % 2 = 0 ∧ zrow (row5 m 13) t 1 = false :=
  family5_of_class m 1 1 46 45 45 2097152 13 hq (by omega) (by omega) (by omega)
    (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cycle13_complete))

theorem row5_27_all_even (m : Nat) (hq : m % 2 = 0) :
    (∀ k, 1 ≤ k → k < m + 2 → row5 m 27 k = stripe k) ∧
      row5 m 27 (m + 2) ≠ stripe (m + 2) ∧
      ∃ t, t ≤ m + 1 + 45 ∧ t % 2 = 0 ∧ zrow (row5 m 27) t 1 = false :=
  family5_of_class m 0 2 46 45 45 2097152 27 hq (by omega) (by omega) (by omega)
    (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cycle13_complete))

theorem stripe_five_tail_complete (m : Nat) (v : Fin 32) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 7 ∧
      (∀ k, 1 ≤ k → k < d → row5 m v.val k = stripe k) ∧
      row5 m v.val d ≠ stripe d ∧
      ∃ t, t ≤ d - 1 + 45 ∧ t % 2 = 0 ∧ zrow (row5 m v.val) t 1 = false := by
  by_cases h : (v.val ≠ 13 ∨ m % 2 = 0) ∧ (v.val ≠ 27 ∨ m % 2 = 1)
  · obtain ⟨d, hd, hdm, hag, hdev, t, ht, he, hz⟩ := stripe_five_tail m v h
    exact ⟨d, hd, hdm, hag, hdev, t, by omega, he, hz⟩
  · rcases (show (v.val = 13 ∧ m % 2 = 1) ∨ (v.val = 27 ∧ m % 2 = 0) by omega) with ⟨hv, hq⟩ | ⟨hv, hq⟩
    · rw [hv]
      obtain ⟨hag, hdev, t, ht, he, hz⟩ := row5_13_all_odd m hq
      exact ⟨m + 1, by omega, by omega, hag, hdev, t, by omega, he, hz⟩
    · rw [hv]
      obtain ⟨hag, hdev, t, ht, he, hz⟩ := row5_27_all_even m hq
      exact ⟨m + 2, by omega, by omega, hag, hdev, t, by omega, he, hz⟩

end Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFourComplete

