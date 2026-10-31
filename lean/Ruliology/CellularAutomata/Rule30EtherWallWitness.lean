module

public import Ruliology.CellularAutomata.Rule30Ether
public import Ruliology.CellularAutomata.Rule30Coupled
public import Ruliology.CellularAutomata.Rule30Realization
public import Ruliology.CellularAutomata.Rule30PeriodTwoCoupled
public import Ruliology.CellularAutomata.Rule30DrivenLeft

/-!
# Rule 30: a periodic left half cannot replace the finite one

`Rule30Ether.lock_excludes` and `Rule30Ether.absorption_excludes` exclude `w^∞` as a tail of the
center column under hypotheses about the right half only; the finiteness of the left half enters
through Jen's theorem and its masked form (`Rule30Jen.jen`, `Rule30MaskedJen.masked_jen`, stated for
every configuration with a leftmost black cell in `Rule30FiniteConfigs` and
`Rule30FiniteMaskedJen`). That hypothesis cannot be weakened to spatial periodicity, even with a
finite right half. For each word of least period 4 and for the alternating word, some configuration
has a left half of spatial period `7`, a right half that is white beyond some position, and center
column `w^∞` from time `0`. Column `1` of its right half stays on the ether (`drv_col1_ether`), so
that right half has the first property that `Rule30Ether.Lock` asks for.

* `period_four_left_periodic_right_finite`: for each of `0001`, `0011`, `0111`.
* `alt_left_periodic_right_finite`: for the alternating column `1, 0, 1, 0, …` (period 2), and
  `alt_coupled_left_periodic`, the same in the language of `Rule30Coupled`: the coupled question
  `Rule30Coupled.CQ` for that column fails once its finite left half is replaced by a periodic one.
  `Rule30PeriodTwoCoupled.ether_coupled_witness` had both halves infinite.

**Method.** The left half is the ether (`etherL`): driven by an ether column, it stays the ether
(`L_ether`), because the ether is a rule-30 orbit (`Rule30Ether.ether_rule`). The right half is the
kit's finite configuration `Rule30Ether.config`: ether columns, a wall state and then white cells.
Driven by the same column it keeps column `1` on the ether forever
(`Rule30Ether.config_pure_ether`).
So the column, the two halves and the center satisfy the coupled update (`coupled_ether_wall`), and
`Rule30Coupled.center_glue` glues them into one rule-30 evolution (`ether_wall_config`).
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30EtherWallWitness

open Rule30Jen Rule30StripCertificates Rule30Ether Rule30Coupled
open Rule30DrivenLeft (L L_col0 L_succ L_zero)

/-- The left half of the ether at phase `s0` when column `0` is the ether column `j0`: position
`p < 0` carries ether column `j0 + 6 * (-p)`, that is `j0 + p` modulo `7`. -/
def etherL (j0 s0 : Nat) (p : Int) : Bool := ether (j0 + 6 * (-p).toNat) s0

/-- **The left half driven by an ether column, started from the ether, is the ether**, at every
time. -/
theorem L_ether (j0 s0 : Nat) : ∀ (t : Nat) (p : Int), p ≤ 0 →
    L (fun t => ether j0 (t + s0)) (etherL j0 s0) t p = ether (j0 + 6 * (-p).toNat) (t + s0)
  | 0, p, hp => by
    by_cases h : p < 0
    · rw [L_zero h]; unfold etherL; rw [Nat.zero_add]
    · have h0 : p = 0 := by omega
      subst h0
      rw [L_col0]
      simp
  | t + 1, p, hp => by
    by_cases h : p < 0
    · rw [L_succ h, L_ether j0 s0 t (p - 1) (by omega), L_ether j0 s0 t p (by omega),
        L_ether j0 s0 t (p + 1) (by omega)]
      have e1 : ether (j0 + 6 * (-(p - 1)).toNat) (t + s0) =
          ether (j0 + 6 * (-p).toNat + 6) (t + s0) := ether_congr (by omega) rfl
      have e3 : ether (j0 + 6 * (-(p + 1)).toNat) (t + s0) =
          ether (j0 + 6 * (-p).toNat + 1) (t + s0) := ether_congr (by omega) rfl
      rw [e1, e3, show t + 1 + s0 = (t + s0) + 1 by omega,
        ether_rule (j0 + 6 * (-p).toNat) (t + s0)]
    · have h0 : p = 0 := by omega
      subst h0
      rw [L_col0]
      simp

/-- Column `1` of the finite right half `config j0 s k ws`, driven by the ether column `wordAt w`,
is the ether column `j0 + 1` at every time (`Rule30Ether.config_pure_ether` with `b = 1`). -/
theorem drv_col1_ether (w : List Bool) (j0 s k : Nat) (hal : aligned w j0 s = true)
    (hk : (j0 + k) % 7 = 2) (hk1 : 1 ≤ k) (ws : List Bool) (hws : (s % 4, ws) ∈ wallStates)
    (hlen : ws.length = 13) (t : Nat) :
    drv (wordAt w) (config j0 s k ws) t 1 = ether (j0 + 1) (t + s) := by
  have hrow := config_pure_ether w j0 s k 1 hal hk hk1 ws hws hlen t
  simp only [rowOf, etherRow, seg, List.cons.injEq, and_true] at hrow
  rw [hrow]
  exact ether_congr rfl (by omega)

/-- **Coupling.** The ether left half `etherL j0 s`, the ether column `wordAt w` and the finite
right half `config j0 s k ws` satisfy the coupled update `Rule30Coupled.Coupled`. -/
theorem coupled_ether_wall (w : List Bool) (j0 s k : Nat) (hal : aligned w j0 s = true)
    (hk : (j0 + k) % 7 = 2) (hk1 : 1 ≤ k) (ws : List Bool) (hws : (s % 4, ws) ∈ wallStates)
    (hlen : ws.length = 13) :
    Coupled (wordAt w) (etherL j0 s) (config j0 s k ws) := by
  have hω : wordAt w = fun t => ether j0 (t + s) := funext fun t => (aligned_spec hal t).symm
  intro t
  have hL : L (wordAt w) (etherL j0 s) t (-1) = ether (j0 + 6) (t + s) := by
    rw [hω, L_ether j0 s t (-1) (by omega)]
    rfl
  rw [hL, drv_col1_ether w j0 s k hal hk hk1 ws hws hlen t, ← aligned_spec hal (t + 1),
    ← aligned_spec hal t, show t + 1 + s = (t + s) + 1 by omega, ether_rule j0 (t + s)]

/-- **The glued configuration.** Gluing `etherL j0 s`, the cell `wordAt w 0` and
`config j0 s k ws` gives a configuration whose left half has spatial period `7`, which is white
right of position `k + 13`, and whose center column is `wordAt w` at every time. -/
theorem ether_wall_config (w : List Bool) (j0 s k : Nat) (hal : aligned w j0 s = true)
    (hk : (j0 + k) % 7 = 2) (hk1 : 1 ≤ k) (ws : List Bool) (hws : (s % 4, ws) ∈ wallStates)
    (hlen : ws.length = 13) :
    (∀ p : Int, p < 0 → glue (etherL j0 s) (wordAt w 0) (config j0 s k ws) (p - 7) =
        glue (etherL j0 s) (wordAt w 0) (config j0 s k ws) p) ∧
    (∀ p : Int, ((k + 13 : Nat) : Int) < p →
        glue (etherL j0 s) (wordAt w 0) (config j0 s k ws) p = false) ∧
    ∀ t, Rule30Realization.evol (glue (etherL j0 s) (wordAt w 0) (config j0 s k ws)) t 0 =
        wordAt w t := by
  refine ⟨fun p hp => ?_, fun p hp => ?_, fun t => ?_⟩
  · simp only [glue, show p - 7 < 0 by omega, hp, ↓reduceIte]
    unfold etherL
    exact ether_congr (by omega) rfl
  · simp only [glue, show ¬ (p < 0) by omega, show ¬ (p = 0) by omega, ↓reduceIte]
    exact config_finite j0 s k ws p.toNat (by omega)
  · exact center_glue (coupled_ether_wall w j0 s k hal hk hk1 ws hws hlen) t

/-! ### The alternating column `1, 0, 1, 0, …` (black at the even times, as `altCol`) -/

/-- The alternating column as a word of length `4`, black at the even times. -/
def w1010 : List Bool := [true, false, true, false]

theorem aligned_1010_3 : aligned w1010 3 1 = true := by decide

/-- A wall state at phase `1`, the first one of `Rule30Ether.wallStates` at that phase. -/
def wsA : List Bool :=
  [false, true, true, false, false, false, true, true, false, true, false, false, false]

theorem wsA_mem : (1 % 4, wsA) ∈ wallStates := by decide

theorem wordAt_1010 (t : Nat) : wordAt w1010 t = Rule30PeriodTwoCoupled.altCol t := by
  unfold wordAt w1010 Rule30PeriodTwoCoupled.altCol
  have h4 : t % 4 < 4 := Nat.mod_lt _ (by decide)
  have h2 : t % 2 = t % 4 % 2 := by omega
  rw [h2]
  generalize t % 4 = r at h4 ⊢
  rcases r with _ | _ | _ | _ | r
  · rfl
  · rfl
  · rfl
  · rfl
  · omega

/-- **Period 2 with a periodic left half and a finite right half.** Some configuration has a left
half of spatial period `7` (the ether), a right half that is white beyond position `19`, and center
column `1, 0, 1, 0, …` from time `0`. -/
theorem alt_left_periodic_right_finite :
    ∃ y : Int → Bool, (∀ p : Int, p < 0 → y (p - 7) = y p) ∧
      (∃ W : Nat, ∀ p : Int, (W : Int) < p → y p = false) ∧
      ∀ t, Rule30Realization.evol y t 0 = Rule30PeriodTwoCoupled.altCol t := by
  obtain ⟨h1, h2, h3⟩ := ether_wall_config w1010 3 1 6 aligned_1010_3 (by decide) (by decide)
    wsA wsA_mem (by decide)
  exact ⟨_, h1, ⟨6 + 13, h2⟩, fun t => (h3 t).trans (wordAt_1010 t)⟩

/-- **The same in the coupled language.** A left half of spatial period `7` and a finite right
half are coupled to the alternating column: `Rule30Coupled.CQ altCol` fails once its finite left
half is replaced by a periodic one. -/
theorem alt_coupled_left_periodic :
    ∃ (s : Int → Bool) (x : Nat → Bool), (∀ p : Int, p < 0 → s (p - 7) = s p) ∧
      (∃ W : Nat, ∀ p, W < p → x p = false) ∧
      Coupled Rule30PeriodTwoCoupled.altCol s x := by
  refine ⟨etherL 3 1, config 3 1 6 wsA, fun p hp => ?_, ⟨6 + 13, fun p hp =>
    config_finite 3 1 6 wsA p (by omega)⟩, ?_⟩
  · unfold etherL; exact ether_congr (by omega) rfl
  · have h := coupled_ether_wall w1010 3 1 6 aligned_1010_3 (by decide) (by decide) wsA wsA_mem
      (by decide)
    have hω : wordAt w1010 = Rule30PeriodTwoCoupled.altCol := funext wordAt_1010
    rw [hω] at h
    exact h

/-! ### Period 4: the words `0001`, `0011`, `0111` -/

/-- **Least period 4 with a periodic left half and a finite right half.** For each of `0001`,
`0011` and `0111`, some configuration has a left half of spatial period `7` (the ether), a right
half that is white beyond some position, and center column `w^∞` from time `0`. So in
`Rule30Ether.lock_excludes` the finite left half cannot be replaced by a periodic one. -/
theorem period_four_left_periodic_right_finite :
    ∀ w ∈ [w0001, w0011, w0111], ∃ y : Int → Bool,
      (∀ p : Int, p < 0 → y (p - 7) = y p) ∧
      (∃ W : Nat, ∀ p : Int, (W : Int) < p → y p = false) ∧
      ∀ t, Rule30Realization.evol y t 0 = wordAt w t := by
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · obtain ⟨h1, h2, h3⟩ := ether_wall_config w0001 5 0 4 aligned_0001_5 (by decide) (by decide)
      ws0 ws0_mem (by decide)
    exact ⟨_, h1, ⟨4 + 13, h2⟩, h3⟩
  · obtain ⟨h1, h2, h3⟩ := ether_wall_config w0011 0 0 2 aligned_0011_0 (by decide) (by decide)
      ws0 ws0_mem (by decide)
    exact ⟨_, h1, ⟨2 + 13, h2⟩, h3⟩
  · obtain ⟨h1, h2, h3⟩ := ether_wall_config w0111 2 2 7 aligned_0111_2 (by decide) (by decide)
      ws2 ws2_mem (by decide)
    exact ⟨_, h1, ⟨7 + 13, h2⟩, h3⟩

end Ruliology.CellularAutomata.Rule30EtherWallWitness
