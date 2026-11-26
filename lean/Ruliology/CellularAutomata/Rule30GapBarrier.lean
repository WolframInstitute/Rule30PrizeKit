module

public import Ruliology.CellularAutomata.Rule30ZeroCoastBridge
public import Ruliology.CellularAutomata.Rule30ZeroBoundaryBarriers
public import Ruliology.CellularAutomata.Rule30GateTrapLadderCore
public import Ruliology.CellularAutomata.Rule30SidewaysLocks

/-!
# Rule 30, period 2: barrier B1 inside the gap clock

`Rule30ZeroBoundaryBarriers` proves barrier B1 (no ranking through a finite abstraction decreases
along all surviving double steps) with the truncated stripes `trunc n`, and
`Rule30PeriodTwoSideways.no_finite_abstract_ranking_coupled` proves its two-sided form with the cut
ether `c7cut`. Both module docstrings note the scope: the free bits of `trunc n` begin with `11111`,
and the column `1` of `c7` has gaps of `2`, so neither witness family runs inside the gate clock of
`Rule30GateTrap.Q01Gap` (gaps `3` and `5`), nor inside `Rule30GateTrapLift.Q01GapCore`.

This module gives B1 inside the gap clock. The witnesses are the finite seeds whose zero-coast
trace (`Rule30ZeroCoastBridge.trace`) is the period-5 gate: white, then nine black, repeated
(`gate5Word`). Every gap of that clock is `5`, so it reads none of the forbidden gap words of the
kit, all of which contain a gap `3`:

* `gate5_twoCoreOK`: the gate `fun s => decide (s % 5 = 0)` satisfies
  `Rule30GateTrapLift.TwoCoreOK` at every step (gaps `3` or `5`, no `33`, no `3553`, no `3535353`).
* `accept_gate5Word`, `survivesTo_of_trace_gate5`: a seed whose trace is `gate5Word n` survives to
  the horizon `10 n` in the sense of `Rule30ZeroCoastBridge.SurvivesTo`.
* `trace_shift_gate5`: ten steps later, a seed that followed `a + b` blocks follows `b` blocks.
* `no_finite_abstract_ranking_gate5`: for every lookahead `n`, no ranking through a finite
  abstraction of seeds decreases over every ten-step block of every seed that follows the period-5
  gate for the next `n + 1` blocks. The witness for a list `Ls` of abstract values is
  `seedOfTrace (gate5Word (Ls.length + n + 1))` and its images every ten steps
  (`Rule30ZeroCoastBridge.seedOfTrace_spec`, `trace_add`), and the pigeonhole is
  `Rule30ZeroBoundaryBarriers.pigeonhole_gen`.

So a proof of `Q01Gap`, `Q01GapWords` or `Q01GapCore` (equivalently of `MassDiverges` and its
restrictions) cannot be a ranking that factors through a finite abstraction, even when the ranking
is only required to fall while the clock keeps its gaps, and even when it may look any fixed number
of blocks ahead. The witnesses are not counterexamples: the period-5 gate is eventually periodic, so
no finite seed follows it forever (`Rule30ZeroBoundary.free_not_eventuallyPeriodic`, the
absorption route). Nothing here decides `Q01Gap`, `Q01GapCore`, `CQ01Empty` or Problem 1.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30GapBarrier

open Rule30ZeroBoundary.IntegerForm
open Rule30ZeroCoastBridge

/-! ### The period-5 gate as a trace -/

/-- One block of the period-5 gate: a white step (the reset), then nine black steps. -/
def gate5Block : List Bool := false :: List.replicate 9 true

/-- `n` blocks of the period-5 gate. -/
def gate5Word : Nat → List Bool
  | 0 => []
  | n + 1 => gate5Block ++ gate5Word n

theorem gate5Word_length (n : Nat) : (gate5Word n).length = 10 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [gate5Word, gate5Block, ih]; omega

theorem gate5Word_add (a b : Nat) : gate5Word (a + b) = gate5Word a ++ gate5Word b := by
  induction a with
  | zero => simp [gate5Word]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp [gate5Word, ih]

/-- Every block is a reset at age `4`, a gap of `5`. -/
theorem acceptRest_block (rest : List Bool) :
    acceptRest true 0 (List.replicate 9 true ++ false :: rest) = acceptRest true 0 rest := by
  rfl

theorem acceptRest_gate5 : ∀ n : Nat,
    acceptRest true 0 (List.replicate 9 true ++ gate5Word n) = true
  | 0 => by decide
  | n + 1 => by
    show acceptRest true 0 (List.replicate 9 true ++ (false :: (List.replicate 9 true ++ gate5Word n))) = true
    rw [acceptRest_block]
    exact acceptRest_gate5 n

/-- The gate clock accepts every number of whole blocks. -/
theorem accept_gate5Word : ∀ n : Nat, accept (gate5Word n) = true
  | 0 => rfl
  | n + 1 => by
    show accept (false :: (List.replicate 9 true ++ gate5Word n)) = true
    simp only [accept, Bool.not_false, Bool.true_and]
    exact acceptRest_gate5 n

/-- A seed whose trace is `n` blocks of the period-5 gate survives to the horizon `10 n`. -/
theorem survivesTo_of_trace_gate5 (y n : Nat) (h : trace y (10 * n) = gate5Word n) :
    SurvivesTo y (10 * n) := by
  unfold SurvivesTo
  rw [h]
  exact accept_gate5Word n

/-- Ten steps later, a seed that followed `a + b` blocks follows `b` blocks. -/
theorem trace_shift_gate5 (y a b : Nat) (h : trace y (10 * (a + b)) = gate5Word (a + b)) :
    trace (iter F (10 * a) y) (10 * b) = gate5Word b := by
  rw [show 10 * (a + b) = 10 * a + 10 * b by omega, trace_add, gate5Word_add] at h
  have hl : (trace y (10 * a)).length = (gate5Word a).length := by
    rw [trace_length, gate5Word_length]
  exact (List.append_inj h hl).2

/-! ### The gate is inside the two-word core -/

theorem gapWord_three_getD (gs : List Nat) :
    (Rule30GateTrapWords.gapWord (3 :: gs)).getD 0 false = true ∧
      (Rule30GateTrapWords.gapWord (3 :: gs)).getD 3 false = true ∧
      3 < (Rule30GateTrapWords.gapWord (3 :: gs)).length := by
  cases gs with
  | nil => exact ⟨rfl, rfl, by decide⟩
  | cons g gs => exact ⟨rfl, rfl, by simp [Rule30GateTrapWords.gapWord]⟩

/-- The period-5 gate never reads a gap word that begins with a gap `3`. -/
theorem gate5_not_reads_three (s : Nat) (gs : List Nat) :
    ¬ Rule30GateTrapWords.Reads (fun r => decide (r % 5 = 0)) s
      (Rule30GateTrapWords.gapWord (3 :: gs)) := by
  intro hr
  obtain ⟨h0, h3, hlen⟩ := gapWord_three_getD gs
  have a := hr 0 (by omega)
  have b := hr 3 hlen
  rw [h0] at a
  rw [h3] at b
  simp only [Nat.add_zero, decide_eq_true_eq] at a b
  omega

/-- **The period-5 gate satisfies `TwoCoreOK` at every step.** -/
theorem gate5_twoCoreOK (s : Nat) :
    Rule30GateTrapLift.TwoCoreOK (fun r => decide (r % 5 = 0)) s := by
  refine ⟨⟨?_, gate5_not_reads_three s [3], gate5_not_reads_three s [5, 5, 3]⟩,
    gate5_not_reads_three s [5, 3, 5, 3, 5, 3]⟩
  intro h
  simp only [decide_eq_true_eq] at h
  right
  simp only [decide_eq_false_iff_not, decide_eq_true_eq]
  omega

/-! ### Barrier B1 inside the gap clock -/

/-- **No ranking through a finite abstraction falls along the period-5 gate.** For every lookahead
`n`, no rank through a finite abstraction `α` of seeds decreases over the ten-step block from every
seed whose trace follows the period-5 gate for the next `n + 1` blocks. -/
theorem no_finite_abstract_ranking_gate5 {A : Type} (Ls : List A) (α : Nat → A)
    (hα : ∀ y, α y ∈ Ls) (rank : A → Nat) (n : Nat) :
    ¬ ∀ y : Nat, trace y (10 * (n + 1)) = gate5Word (n + 1) →
      rank (α (iter F 10 y)) < rank (α y) := by
  intro h
  let N := Ls.length + n + 1
  let Y := seedOfTrace (gate5Word N)
  have hY : trace Y (10 * N) = gate5Word N := by
    have hs := (seedOfTrace_spec (gate5Word N)).2
    rwa [gate5Word_length] at hs
  let z : Nat → Nat := fun j => iter F (10 * j) Y
  have hz : ∀ j, j ≤ Ls.length → trace (z j) (10 * (n + 1)) = gate5Word (n + 1) := by
    intro j hj
    have hsplit : N = (j + (n + 1)) + (Ls.length - j) := by omega
    have htake := trace_take Y (10 * (j + (n + 1))) (10 * N) (by omega)
    rw [hY, hsplit, gate5Word_add] at htake
    have hl : (gate5Word (j + (n + 1)) ++ gate5Word (Ls.length - j)).take (10 * (j + (n + 1))) =
        gate5Word (j + (n + 1)) := by
      rw [← gate5Word_length (j + (n + 1)), List.take_left]
    exact trace_shift_gate5 Y j (n + 1) (htake.symm.trans hl)
  have hstep : ∀ j, iter F 10 (z j) = z (j + 1) := by
    intro j
    show iter F 10 (iter F (10 * j) Y) = iter F (10 * (j + 1)) Y
    rw [← iter_F_add, show 10 * j + 10 = 10 * (j + 1) by omega]
  have hdec : ∀ j, j ≤ Ls.length → rank (α (z (j + 1))) < rank (α (z j)) := by
    intro j hj
    rw [← hstep j]
    exact h (z j) (hz j hj)
  obtain ⟨m, m', hlt, hle, heq⟩ :=
    Rule30ZeroBoundaryBarriers.pigeonhole_gen Ls (fun j => α (z j)) fun j => hα _
  have chain : ∀ k, m + k + 1 ≤ m' → rank (α (z (m + k + 1))) < rank (α (z m)) := by
    intro k
    induction k with
    | zero => intro hk; exact hdec m (by omega)
    | succ k ih =>
      intro hk
      exact Nat.lt_trans (hdec (m + k + 1) (by omega)) (ih (by omega))
  have hc := chain (m' - m - 1) (by omega)
  rw [show m + (m' - m - 1) + 1 = m' by omega] at hc
  exact Nat.lt_irrefl _ (heq ▸ hc)

/-- The witnesses of `no_finite_abstract_ranking_gate5` survive: every seed that follows `n` blocks
of the period-5 gate survives to the horizon `10 n`, and it exists for every `n`
(`Rule30ZeroCoastBridge.seedOfTrace`). -/
theorem gate5_witnesses (n : Nat) :
    seedOfTrace (gate5Word n) < 2 ^ (10 * n) ∧
      SurvivesTo (seedOfTrace (gate5Word n)) (10 * n) := by
  obtain ⟨hlt, htr⟩ := seedOfTrace_spec (gate5Word n)
  rw [gate5Word_length] at hlt htr
  exact ⟨hlt, survivesTo_of_trace_gate5 _ n htr⟩

/-! ### Barrier B1 at every width `W ≥ 16` of the gate-trap ladder (`AcceptLift` and `AcceptLiftCore`) -/

private theorem word5_mod5_eq (k : Nat) :
    Rule30SidewaysLocks.word5.getD (k % 5) false = decide (k % 5 = 0) := by
  have hm : k % 5 < 5 := Nat.mod_lt k (by decide)
  rcases (by omega : k % 5 = 0 ∨ k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4) with
    r | r | r | r | r <;> simp [Rule30SidewaysLocks.word5, r]

private theorem gate5Word_getD (n t : Nat) (ht : t < 10 * n) :
    (gate5Word n).getD t false = decide (t % 10 ≠ 0) := by
  induction n generalizing t with
  | zero => omega
  | succ n ih =>
    match t with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => rfl
    | t + 10 =>
      change (gate5Word n).getD t false = decide ((t + 10) % 10 ≠ 0)
      simpa [Nat.add_mod_right] using ih t (by omega)

/-- **All-width lift realizability of the period-5 gate (`liftPath_gate5_all_widths`):** at every
width `W ≥ 16`, the physical windows of `Rule30SidewaysLocks.rh 28998` from tick `15` form a
`LiftPath W` whose first cells read `decide (k % 5 = 0)`. -/
theorem liftPath_gate5_all_widths {W : Nat} (hW : 16 ≤ W) :
    ∃ ws, Rule30GateTrapLadder.LiftPath W ws ∧ ∀ k, (ws k).headD false = decide (k % 5 = 0) := by
  have htrap : Rule30GateTrap.win (Rule30SidewaysLocks.rh 28998) 15 ∈ Rule30GateTrap.trap :=
    Rule30SidewaysLocks.lock5_win_trap (k := 0) (by decide) Rule30SidewaysLocks.lock5_entry
  refine ⟨fun k => Rule30GateTrapLadder.winW (Rule30SidewaysLocks.rh 28998) W (15 + 2 * k),
    Rule30GateTrapLadder.winW_liftPath (Rule30SidewaysLocks.rh 28998) hW (by decide) htrap, fun k => ?_⟩
  rw [Rule30GateTrapLadder.winW_head (Rule30SidewaysLocks.rh 28998) (by omega) (15 + 2 * k),
    show 15 + 2 * k = 2 * (7 + k) + 1 by omega]
  change Rule30PeriodTwoSideways.u (Rule30SidewaysLocks.rh 28998) (7 + k) = decide (k % 5 = 0)
  rw [Rule30SidewaysLocks.u_28998 k, word5_mod5_eq k]

/-- **All-width core lift acceptance of period-5 gate traces (`acceptLiftCore_of_trace_gate5`):**
every seed `y` whose trace is `gate5Word n` satisfies `AcceptLiftCore W y (10 * n)` for every `W ≥ 16`. -/
theorem acceptLiftCore_of_trace_gate5 {W y n : Nat} (hW : 16 ≤ W)
    (htr : trace y (10 * n) = gate5Word n) :
    Rule30GateTrapLadderCore.AcceptLiftCore W y (10 * n) := by
  obtain ⟨ws, hp, hhead⟩ := liftPath_gate5_all_widths hW
  refine ⟨ws, hp, fun t ht => ?_, fun s _ => ?_⟩
  · have htrD : ∀ H y t, t < H → (trace y H).getD t false = (iter F t y).testBit 0 := by
      intro H
      induction H with
      | zero => intro _ _ ht0; omega
      | succ H ih =>
        intro y t htH
        cases t with
        | zero => rfl
        | succ t =>
          change (trace (F y) H).getD t false = (iter F (t + 1) y).testBit 0
          rw [ih (F y) t (by omega), iter_succ_apply]
    rw [← htrD (10 * n) y t ht, htr, gate5Word_getD n t ht, hhead (t / 2)]
    by_cases hodd : t % 2 = 1
    · simp only [hodd, ↓reduceIte, decide_eq_true_eq]
      omega
    · have hiff : (t / 2 % 5 = 0) ↔ (t % 10 = 0) := by omega
      by_cases h10 : t % 10 = 0 <;> simp [hodd, h10, hiff]
  · exact Rule30GateTrapLadderCore.twoCoreOK_congr (fun i _ => (hhead (s + i)).symm) (gate5_twoCoreOK s)

/-- **Explicit all-width `AcceptLiftCore` witnesses (`gate5_acceptLiftCore_witnesses`):** for every
width `W ≥ 16` and `n : Nat`, `seedOfTrace (gate5Word n) < 2 ^ (10 * n)` is accepted by `AcceptLiftCore W` for `10 * n` steps. -/
theorem gate5_acceptLiftCore_witnesses {W n : Nat} (hW : 16 ≤ W) :
    seedOfTrace (gate5Word n) < 2 ^ (10 * n) ∧
      Rule30GateTrapLadderCore.AcceptLiftCore W (seedOfTrace (gate5Word n)) (10 * n) := by
  obtain ⟨hlt, htr⟩ := seedOfTrace_spec (gate5Word n)
  rw [gate5Word_length] at hlt htr
  exact ⟨hlt, acceptLiftCore_of_trace_gate5 hW htr⟩

/-- **Barrier B1 at every width `W ≥ 16` of `AcceptLiftCore` (`no_finite_abstract_ranking_acceptLiftCore`):**
no finite-abstraction ranking decreases over every ten-step block of every seed accepted by
`AcceptLiftCore W` for `10 * (n + 1)` steps, at any finite width `W ≥ 16`. -/
theorem no_finite_abstract_ranking_acceptLiftCore {A : Type} {W : Nat} (hW : 16 ≤ W)
    (Ls : List A) (α : Nat → A) (hα : ∀ y, α y ∈ Ls) (rank : A → Nat) (n : Nat) :
    ¬ ∀ y : Nat, Rule30GateTrapLadderCore.AcceptLiftCore W y (10 * (n + 1)) →
      rank (α (iter F 10 y)) < rank (α y) := by
  intro hall
  refine no_finite_abstract_ranking_gate5 Ls α hα rank n fun y htr => ?_
  exact hall y (acceptLiftCore_of_trace_gate5 hW htr)

/-- **Barrier B1 at every width `W ≥ 16` of `AcceptLift` (`no_finite_abstract_ranking_acceptLift`):**
the corresponding impossibility for the unrestricted width-`W` lift language `AcceptLift W`. -/
theorem no_finite_abstract_ranking_acceptLift {A : Type} {W : Nat} (hW : 16 ≤ W)
    (Ls : List A) (α : Nat → A) (hα : ∀ y, α y ∈ Ls) (rank : A → Nat) (n : Nat) :
    ¬ ∀ y : Nat, Rule30GateTrapLadder.AcceptLift W y (10 * (n + 1)) →
      rank (α (iter F 10 y)) < rank (α y) := by
  intro hall
  refine no_finite_abstract_ranking_acceptLiftCore hW Ls α hα rank n fun y hac => ?_
  exact hall y hac.acceptLift

end Rule30GapBarrier
end Ruliology.CellularAutomata
