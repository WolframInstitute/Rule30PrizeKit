module

public import Ruliology.CellularAutomata.Rule30FiniteClockCertificate

/-!
# A clock-sixteen certificate, valid at every finite spatial width

This checks temporal profile closure and shorter-clock detection using the
unchanged Lean kernel. The full clock is fixed at sixteen; no center-column
period or arbitrary-clock theorem is asserted.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30FiniteClockSixteen

open Rule30ControlledResponse Rule30FiniteClockCertificate

def pool16 : List Node := [
  Node.mk 0 0 0 65535,
  Node.mk 65535 0 43690 21845,
  Node.mk 43690 65535 43690 21845,
  Node.mk 21845 65535 43690 21845,
  Node.mk 43690 43690 52428 13107,
  Node.mk 21845 43690 43690 21845,
  Node.mk 43690 21845 43690 21845,
  Node.mk 21845 21845 26214 39321,
  Node.mk 52428 43690 46260 19275,
  Node.mk 13107 43690 53970 11565,
  Node.mk 26214 21845 23130 42405,
  Node.mk 39321 21845 38550 26985,
  Node.mk 46260 52428 43176 22359,
  Node.mk 19275 52428 35466 30069,
  Node.mk 53970 13107 41634 23901,
  Node.mk 11565 13107 10794 54741,
  Node.mk 23130 26214 21588 43947,
  Node.mk 42405 26214 47802 17733,
  Node.mk 38550 39321 60138 5397,
  Node.mk 26985 39321 44718 20817,
  Node.mk 43176 46260 55080 10455,
  Node.mk 22359 46260 42330 23205,
  Node.mk 35466 19275 36210 29325,
  Node.mk 30069 19275 21930 43605,
  Node.mk 41634 53970 41820 23715,
  Node.mk 23901 53970 38250 27285,
  Node.mk 10794 11565 13770 51765,
  Node.mk 54741 11565 43350 22185,
  Node.mk 21588 23130 27540 37995,
  Node.mk 43947 23130 44370 21165,
  Node.mk 47802 42405 54570 10965,
  Node.mk 17733 42405 47430 18105,
  Node.mk 60138 38550 43860 21675,
  Node.mk 5397 38550 58650 6885,
  Node.mk 44718 26985 46410 19125,
  Node.mk 20817 26985 20910 44625,
  Node.mk 55080 43176 21808 43727,
  Node.mk 10455 43176 12458 53077,
  Node.mk 42330 22359 23146 42389,
  Node.mk 23205 22359 38234 27301,
  Node.mk 36210 35466 2732 62803,
  Node.mk 29325 35466 21258 44277,
  Node.mk 21930 30069 42666 22869,
  Node.mk 43605 30069 21926 43609,
  Node.mk 41820 41634 15700 49835,
  Node.mk 23715 41634 21698 43837,
  Node.mk 38250 23901 27050 38485,
  Node.mk 27285 23901 43670 21865,
  Node.mk 13770 10794 54604 10931,
  Node.mk 51765 10794 19498 46037,
  Node.mk 43350 54741 22170 43365,
  Node.mk 22185 54741 25942 39593,
  Node.mk 27540 21588 43672 21863,
  Node.mk 37995 21588 26538 38997,
  Node.mk 44370 43947 13650 51885,
  Node.mk 21165 43947 21194 44341,
  Node.mk 54570 47802 21804 43731,
  Node.mk 10965 47802 11434 54101,
  Node.mk 47430 17733 22138 43397,
  Node.mk 18105 17733 34134 31401,
  Node.mk 43860 60138 19796 45739,
  Node.mk 21675 60138 21682 43853,
  Node.mk 58650 5397 23018 42517,
  Node.mk 6885 5397 60070 5465,
  Node.mk 46410 44718 10932 54603,
  Node.mk 19125 44718 19242 46293,
  Node.mk 20910 20817 40618 24917,
  Node.mk 44625 20817 21918 43617]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem pool16_checked : poolCheck 16 pool16=true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem detection16_checked :
    (List.range 16).all (fun H => detectionCheck 16 H pool16)=true := by decide +kernel

theorem detection16_all_head_clocks (H : Nat) : detectionCheck 16 H pool16=true := by
  have h := List.all_eq_true.mp detection16_checked (H%16)
    (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  simpa only [detectionCheck_mod_clock] using h

/-- No finite-width orbit whose full clock divides sixteen can hide a shorter head clock. -/
theorem period_detected (x : State) (W H : Nat) (hx : ∀ k, W≤k → x k=false)
    (hfull : iterate x 16=x)
    (hhead : ∀ t, iterate x (t+H) 0=iterate x t 0) : iterate x H=x := by
  exact finite_state_clock_detected 16 H (by decide) pool16 pool16_checked
    (detection16_all_head_clocks H) x W hx hfull hhead

theorem period8_detected (x : State) (W : Nat) (hx : ∀ k, W≤k → x k=false)
    (hfull : iterate x 16=x)
    (hhead : ∀ t, iterate x (t+8) 0=iterate x t 0) : iterate x 8=x :=
  period_detected x W 8 hx hfull hhead

theorem period4_detected (x : State) (W : Nat) (hx : ∀ k, W≤k → x k=false)
    (hfull : iterate x 16=x)
    (hhead : ∀ t, iterate x (t+4) 0=iterate x t 0) : iterate x 4=x :=
  period_detected x W 4 hx hfull hhead

theorem period2_detected (x : State) (W : Nat) (hx : ∀ k, W≤k → x k=false)
    (hfull : iterate x 16=x)
    (hhead : ∀ t, iterate x (t+2) 0=iterate x t 0) : iterate x 2=x :=
  period_detected x W 2 hx hfull hhead

theorem period1_detected (x : State) (W : Nat) (hx : ∀ k, W≤k → x k=false)
    (hfull : iterate x 16=x)
    (hhead : ∀ t, iterate x (t+1) 0=iterate x t 0) : iterate x 1=x :=
  period_detected x W 1 hx hfull hhead

theorem eventual_period_detected (x : State) (W H T : Nat) (hx : ∀ k, W≤k → x k=false)
    (hfull : iterate x 16=x)
    (hhead : ∀ t, T≤t → iterate x (t+H) 0=iterate x t 0) : iterate x H=x := by
  exact finite_state_eventual_clock_detected 16 H (by decide) pool16 pool16_checked
    (detection16_all_head_clocks H) x W T hx hfull hhead

/-- A hidden shorter head clock in this full-clock range requires an infinite initial tail. -/
theorem period_loss_requires_infinite_tail (x : State) (H T : Nat)
    (hfull : iterate x 16=x)
    (hhead : ∀ t, T≤t → iterate x (t+H) 0=iterate x t 0)
    (hloss : iterate x H≠x) : ∀ W, ∃ k, W≤k ∧ x k=true := by
  intro W
  apply Classical.byContradiction
  intro hnone
  have hfin : ∀ k, W≤k → x k=false := by
    intro k hk
    cases hb : x k with
    | false => rfl
    | true => exact False.elim (hnone ⟨k,hk,hb⟩)
  exact hloss (eventual_period_detected x W H T hfin hfull hhead)

/-! ## Exact equivalence between eventual head period `H` and full-state period `H` for period-16 finite-width orbits -/

/-- **Exact Equivalence Between Eventual Head Period `H`, Full-State Return `iterate x H = x`, and All-Column Period `H` (`head_period_iff_full_period_of_period16`).** -/
theorem head_period_iff_full_period_of_period16 (x : State) (W H : Nat)
    (hx : ∀ k, W ≤ k → x k = false) (hfull : iterate x 16 = x) :
    ((∃ T, ∀ t, T ≤ t → iterate x (t + H) 0 = iterate x t 0) ↔ iterate x H = x) ∧
    (iterate x H = x ↔ ∀ k t, iterate x (t + H) k = iterate x t k) := by
  refine ⟨⟨fun ⟨T, hT⟩ => eventual_period_detected x W H T hx hfull hT,
           fun hret => ⟨0, fun t _ => congrFun (iterate_period_of_return x H hret t) 0⟩⟩,
          ⟨fun hret k t => congrFun (iterate_period_of_return x H hret t) k,
           fun hall => funext fun k => by simpa only [Nat.zero_add, iterate] using hall k 0⟩⟩

end Ruliology.CellularAutomata.Rule30FiniteClockSixteen
