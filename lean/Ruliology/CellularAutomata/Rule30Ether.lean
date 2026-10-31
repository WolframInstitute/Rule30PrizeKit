module

public import Ruliology.CellularAutomata.Rule30StripCertificates
public import Ruliology.CellularAutomata.Rule30Diagonals

/-!
# Rule 30, least period 4: the ether and the wall traps of the right half

The *ether* is a spatio-temporally periodic rule-30 pattern of spatial period `7` and temporal
period `4`. Its columns at the phases `0, 1, 2, 3` are

    B1 = 0011, B2 = 0110, B3 = 1101, B4 = 0101, B5 = 0011, c = 0001, c = 0001.

Each of the words `0001`, `0011`, `0111` (and `0101`) is, up to a time shift, an ether column
(`aligned_*`). The *wall* is a set of `109` states of a `13`-cell strip whose left neighbour is a
B3 column; it is closed under every value of the cell to its right, and whenever B3 is white the
first wall cell carries the ether value B4 (`wallOK_true`, a kernel check). So "ether columns
ending in a B3 column, followed by a wall state" is a trap for the right half: once entered, every
ether column keeps its periodic values forever (`trap_invariant`).

* `ether_rule`: the ether is a rule-30 orbit.
* `trap_invariant`: the trap is invariant for every rule-30 evolution on the columns `p ≥ 0`
  whose column `0` is the ether column.
* `ether_wall_trap`, `no_ether_wall_entry`: if the center column is `w^∞` from time `T` and at some
  `t1 ≥ T` columns `1..k` carry the ether (column `k` a B3) and columns `k+1..k+13` a wall state,
  contradiction (masked Jen, `Rule30MaskedJen.masked_jen`). An infinite family of traps.
* `drv`: the right half driven by a prescribed column `0`; `cell_eq_drv`: the true right half
  from time `T` is the half driven by the true center column.
* `never_enters_S0001`, `never_enters_S0011`, `never_enters_S0111`: explicit finitely supported
  right halves that never enter the certified traps `S_w`; they stay in deeper members of
  the family forever (`config_pure_ether`).
* `Absorption` (an open conjecture, stated as a `Prop`), `absorption_excludes` and
  `least_period_four_of_absorption`: absorption into the family for every finite right half
  excludes `w^∞` as a tail of the center column, for every transient.
* `Lock` (an open conjecture, weaker than absorption: `lock_of_absorption`), `lock_excludes` and
  `least_period_four_of_lock`: the exclusion needs much less than absorption. It suffices that
  every finitely supported right half driven by `w^∞` has column `1` eventually periodic at the
  white times of the driver, with a period `4 Q` (then masked Jen applies), or some column
  `q ≥ 1` eventually periodic (then Jen applies). Both use the finiteness of the left half, and
  `Rule30EtherWallWitness` shows that it cannot be replaced by spatial periodicity.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30Ether

open Rule30Jen Rule30StripCertificates

/-! ### The ether -/

/-- Ether columns `B1 B2 B3 B4 B5 c c` at the phases `0, 1, 2, 3`. -/
def etherTable : List (List Bool) :=
  [[false, false, true, true],
   [false, true, true, false],
   [true, true, false, true],
   [false, true, false, true],
   [false, false, true, true],
   [false, false, false, true],
   [false, false, false, true]]

/-- Ether column `j mod 7` at phase `φ mod 4`. -/
def ether (j φ : Nat) : Bool := (etherTable.getD (j % 7) []).getD (φ % 4) false

theorem ether_congr {j j' φ φ' : Nat} (hj : j % 7 = j' % 7) (hφ : φ % 4 = φ' % 4) :
    ether j φ = ether j' φ' := by
  unfold ether; rw [hj, hφ]

theorem ether_rule_small : ∀ j, j < 7 → ∀ φ, φ < 4 →
    ether j (φ + 1) = rule (ether (j + 6) φ) (ether j φ) (ether (j + 1) φ) := by decide

/-- **The ether is a rule-30 orbit.** -/
theorem ether_rule (j φ : Nat) :
    ether j (φ + 1) = rule (ether (j + 6) φ) (ether j φ) (ether (j + 1) φ) := by
  have h := ether_rule_small (j % 7) (Nat.mod_lt _ (by decide)) (φ % 4) (Nat.mod_lt _ (by decide))
  rw [ether_congr (j := j % 7) (j' := j) (φ := φ % 4 + 1) (φ' := φ + 1) (by omega) (by omega),
    ether_congr (j := j % 7 + 6) (j' := j + 6) (φ := φ % 4) (φ' := φ) (by omega) (by omega),
    ether_congr (j := j % 7) (j' := j) (φ := φ % 4) (φ' := φ) (by omega) (by omega),
    ether_congr (j := j % 7 + 1) (j' := j + 1) (φ := φ % 4) (φ' := φ) (by omega) (by omega)] at h
  exact h

theorem ether_period (j φ : Nat) : ether j (φ + 4) = ether j φ :=
  ether_congr rfl (by omega)

/-! ### The wall: 109 states of a 13-cell strip to the right of a B3 column -/

def wallStates : List (Nat × List Bool) := [
  (0, [false, false, false, true, false, true, false, true, false, false, false, false, false]),
  (0, [false, false, false, true, false, true, false, true, false, false, false, false, true]),
  (0, [false, false, false, true, false, true, false, true, false, false, false, true, false]),
  (0, [false, false, false, true, false, true, false, true, false, false, false, true, true]),
  (0, [false, false, false, true, false, true, false, true, false, false, true, false, false]),
  (0, [false, false, false, true, false, true, false, true, false, false, true, false, true]),
  (0, [false, false, false, true, false, true, false, true, false, false, true, true, true]),
  (0, [false, false, false, true, false, true, false, true, true, false, false, false, false]),
  (0, [false, false, false, true, false, true, false, true, true, false, false, false, true]),
  (0, [false, false, false, true, false, true, false, true, true, false, false, true, true]),
  (0, [false, false, false, true, false, true, false, true, true, false, true, true, false]),
  (0, [false, true, false, false, false, false, false, true, false, false, false, false, false]),
  (0, [false, true, false, false, false, false, false, true, false, false, false, false, true]),
  (0, [false, true, false, false, false, false, false, true, false, false, true, false, false]),
  (0, [false, true, false, false, false, false, false, true, false, false, true, false, true]),
  (0, [false, true, false, false, false, false, false, true, false, true, false, false, false]),
  (0, [false, true, false, false, false, false, false, true, false, true, false, false, true]),
  (0, [false, true, false, false, false, false, false, true, false, true, false, true, false]),
  (0, [false, true, false, false, false, false, false, true, false, true, false, true, true]),
  (0, [false, true, false, false, false, false, false, true, false, true, true, false, false]),
  (0, [false, true, false, false, false, false, false, true, false, true, true, false, true]),
  (0, [false, true, false, false, false, false, false, true, false, true, true, true, false]),
  (0, [false, true, false, false, false, false, false, true, false, true, true, true, true]),
  (0, [false, true, false, false, false, false, false, true, true, false, false, false, false]),
  (0, [false, true, false, false, false, false, false, true, true, false, false, false, true]),
  (0, [false, true, false, false, false, false, false, true, true, false, false, true, true]),
  (1, [false, true, true, false, false, false, true, true, false, true, false, false, false]),
  (1, [false, true, true, false, false, false, true, true, false, true, false, false, true]),
  (1, [false, true, true, false, false, false, true, true, false, true, false, true, false]),
  (1, [false, true, true, false, false, false, true, true, false, true, false, true, true]),
  (1, [false, true, true, false, false, false, true, true, false, true, true, false, false]),
  (1, [false, true, true, false, false, false, true, true, false, true, true, false, true]),
  (1, [false, true, true, false, false, false, true, true, false, true, true, true, false]),
  (1, [false, true, true, false, false, false, true, true, false, true, true, true, true]),
  (1, [false, true, true, false, false, false, true, true, true, false, false, false, false]),
  (1, [false, true, true, false, false, false, true, true, true, false, false, false, true]),
  (1, [false, true, true, false, false, false, true, true, true, false, false, true, true]),
  (1, [false, true, true, false, false, false, true, true, true, true, true, false, true]),
  (1, [false, true, true, false, false, false, true, true, true, true, true, true, false]),
  (1, [false, true, true, false, false, false, true, true, true, true, true, true, true]),
  (1, [true, false, true, true, false, true, false, true, false, false, true, false, false]),
  (1, [true, false, true, true, false, true, false, true, false, false, true, false, true]),
  (1, [true, false, true, true, false, true, false, true, false, true, false, false, false]),
  (1, [true, false, true, true, false, true, false, true, false, true, false, false, true]),
  (1, [true, false, true, true, false, true, false, true, false, true, false, true, true]),
  (1, [true, false, true, true, false, true, false, true, false, true, true, true, false]),
  (1, [true, false, true, true, false, true, false, true, true, false, false, false, false]),
  (1, [true, false, true, true, false, true, false, true, true, false, false, false, true]),
  (1, [true, false, true, true, false, true, false, true, true, false, false, true, true]),
  (1, [true, false, true, true, false, true, false, true, true, false, true, true, false]),
  (1, [true, false, true, true, false, true, false, true, true, false, true, true, true]),
  (1, [true, false, true, true, false, true, false, true, true, true, true, false, false]),
  (1, [true, false, true, true, false, true, false, true, true, true, true, false, true]),
  (1, [true, false, true, true, false, true, false, true, true, true, true, true, false]),
  (1, [true, false, true, true, false, true, false, true, true, true, true, true, true]),
  (2, [false, false, true, false, false, true, false, true, false, false, false, false, false]),
  (2, [false, false, true, false, false, true, false, true, false, false, false, false, true]),
  (2, [false, false, true, false, false, true, false, true, false, false, false, true, false]),
  (2, [false, false, true, false, false, true, false, true, false, false, false, true, true]),
  (2, [false, false, true, false, false, true, false, true, false, false, true, false, false]),
  (2, [false, false, true, false, false, true, false, true, false, false, true, false, true]),
  (2, [false, false, true, false, false, true, false, true, false, true, false, false, false]),
  (2, [false, false, true, false, false, true, false, true, false, true, false, false, true]),
  (2, [false, false, true, false, false, true, false, true, false, true, false, true, false]),
  (2, [false, false, true, false, false, true, false, true, false, true, false, true, true]),
  (2, [false, false, true, false, false, true, false, true, false, true, true, false, false]),
  (2, [false, false, true, false, false, true, false, true, false, true, true, false, true]),
  (2, [false, false, true, false, false, true, false, true, false, true, true, true, false]),
  (2, [false, false, true, false, false, true, false, true, false, true, true, true, true]),
  (2, [false, false, true, false, false, true, false, true, true, true, true, false, true]),
  (2, [false, false, true, false, false, true, false, true, true, true, true, true, false]),
  (2, [false, false, true, false, false, true, false, true, true, true, true, true, true]),
  (2, [false, true, false, true, false, true, true, false, false, false, false, false, false]),
  (2, [false, true, false, true, false, true, true, false, false, false, false, false, true]),
  (2, [false, true, false, true, false, true, true, false, false, true, false, false, false]),
  (2, [false, true, false, true, false, true, true, false, false, true, false, false, true]),
  (2, [false, true, false, true, false, true, true, false, false, true, false, true, false]),
  (2, [false, true, false, true, false, true, true, false, false, true, false, true, true]),
  (2, [false, true, false, true, false, true, true, false, false, true, true, false, false]),
  (2, [false, true, false, true, false, true, true, false, false, true, true, false, true]),
  (2, [false, true, false, true, false, true, true, false, false, true, true, true, false]),
  (2, [false, true, false, true, false, true, true, false, false, true, true, true, true]),
  (3, [false, true, true, true, true, true, false, true, false, false, false, false, false]),
  (3, [false, true, true, true, true, true, false, true, false, false, false, false, true]),
  (3, [false, true, true, true, true, true, false, true, false, true, false, false, false]),
  (3, [false, true, true, true, true, true, false, true, false, true, false, false, true]),
  (3, [false, true, true, true, true, true, false, true, false, true, false, true, false]),
  (3, [false, true, true, true, true, true, false, true, false, true, false, true, true]),
  (3, [false, true, true, true, true, true, false, true, false, true, true, false, false]),
  (3, [false, true, true, true, true, true, false, true, false, true, true, false, true]),
  (3, [false, true, true, true, true, true, false, true, false, true, true, true, true]),
  (3, [false, true, true, true, true, true, false, true, true, false, false, false, false]),
  (3, [false, true, true, true, true, true, false, true, true, false, false, false, true]),
  (3, [false, true, true, true, true, true, false, true, true, false, false, true, true]),
  (3, [false, true, true, true, true, true, false, true, true, false, true, true, false]),
  (3, [false, true, true, true, true, true, false, true, true, false, true, true, true]),
  (3, [false, true, true, true, true, true, false, true, true, true, true, false, true]),
  (3, [false, true, true, true, true, true, false, true, true, true, true, true, false]),
  (3, [false, true, true, true, true, true, false, true, true, true, true, true, true]),
  (3, [true, true, false, true, false, true, false, true, false, false, false, false, false]),
  (3, [true, true, false, true, false, true, false, true, false, false, false, false, true]),
  (3, [true, true, false, true, false, true, false, true, false, false, false, true, true]),
  (3, [true, true, false, true, false, true, false, true, true, true, false, false, false]),
  (3, [true, true, false, true, false, true, false, true, true, true, false, false, true]),
  (3, [true, true, false, true, false, true, false, true, true, true, false, true, false]),
  (3, [true, true, false, true, false, true, false, true, true, true, false, true, true]),
  (3, [true, true, false, true, false, true, false, true, true, true, true, false, false]),
  (3, [true, true, false, true, false, true, false, true, true, true, true, false, true]),
  (3, [true, true, false, true, false, true, false, true, true, true, true, true, true])
]

/-- Closure under every right input, the masked output condition, and well-formedness. -/
def wallOK : Bool :=
  wallStates.all fun e =>
    decide (e.1 < 4) && e.2.length == 13 &&
    (ether 2 e.1 || e.2.headD false == ether 3 e.1) &&
    [false, true].all fun x => wallStates.contains ((e.1 + 1) % 4, lin3 (ether 2 e.1 :: (e.2 ++ [x])))

theorem wallOK_true : wallOK = true := by decide

theorem wall_facts {φ : Nat} {s : List Bool} (h : (φ, s) ∈ wallStates) :
    (ether 2 φ = false → s.headD false = ether 3 φ) ∧
    ∀ x : Bool, ((φ + 1) % 4, lin3 (ether 2 φ :: (s ++ [x]))) ∈ wallStates := by
  have hall := wallOK_true
  unfold wallOK at hall
  have h1 := List.all_eq_true.1 hall (φ, s) h
  simp only [Bool.and_eq_true] at h1
  obtain ⟨⟨⟨_, _⟩, h3⟩, h4⟩ := h1
  refine ⟨fun hw => ?_, fun x => ?_⟩
  · rw [hw, Bool.false_or] at h3
    exact beq_iff_eq.1 h3
  · have h5 := List.all_eq_true.1 h4 x (by cases x <;> simp)
    exact List.contains_iff_mem.1 h5


/-! ### The trap invariant for any rule-30 evolution on the columns `p ≥ 0` -/

/-- `F t p` (columns `p ≥ 0`, column `0` arbitrary) evolves by rule 30 on the columns `p ≥ 1`. -/
def IsR30 (F : Nat → Nat → Bool) : Prop :=
  ∀ t p, F (t + 1) (p + 1) = rule (F t p) (F t (p + 1)) (F t (p + 2))

/-- Columns `k + 1, …, k + m` of `F` at time `t`. -/
def rowOf (F : Nat → Nat → Bool) (t k m : Nat) : List Bool := seg (fun i => F t (k + i + 1)) m

theorem rowOf_succ {F : Nat → Nat → Bool} (hF : IsR30 F) (t k b : Nat) :
    rowOf F (t + 1) k b = lin3 (F t k :: (rowOf F t k b ++ [F t (k + b + 1)])) := by
  have e1 : rowOf F t k b ++ [F t (k + b + 1)] = rowOf F t k (b + 1) := by
    unfold rowOf; rw [seg_succ]
  have e2 : F t k :: rowOf F t k (b + 1) = seg (fun i => F t (k + i)) (b + 2) := rfl
  rw [e1, e2, lin3_seg]
  unfold rowOf
  congr 1
  funext i
  exact hF t (k + i)

theorem rowOf_head (F : Nat → Nat → Bool) (t k b : Nat) :
    (rowOf F t k (b + 1)).headD false = F t (k + 1) := rfl

/-- **Trap invariant.** If column `0` is the ether column `j0` from time `t1` on, and at time `t1`
columns `1..k` carry the ether (column `k` a B3) and columns `k+1..k+13` form a wall state, then
this stays true forever. -/
theorem trap_invariant {F : Nat → Nat → Bool} (hF : IsR30 F) (j0 s k t1 : Nat)
    (hk : (j0 + k) % 7 = 2)
    (h0 : ∀ t, t1 ≤ t → F t 0 = ether j0 (t + s))
    (hE : ∀ p, 1 ≤ p → p ≤ k → F t1 p = ether (j0 + p) (t1 + s))
    (hW : ((t1 + s) % 4, rowOf F t1 k 13) ∈ wallStates) :
    ∀ n, (∀ p, p ≤ k → F (t1 + n) p = ether (j0 + p) (t1 + n + s)) ∧
      ((t1 + n + s) % 4, rowOf F (t1 + n) k 13) ∈ wallStates := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun p hp => ?_, by simpa using hW⟩
    rcases Nat.eq_zero_or_pos p with hp0 | hp0
    · subst hp0; simpa using h0 t1 (Nat.le_refl _)
    · simpa using hE p hp0 hp
  | succ n ih =>
    obtain ⟨hE', hW'⟩ := ih
    have hph : t1 + n + 1 + s = (t1 + n + s) + 1 := by omega
    have htt : t1 + (n + 1) = (t1 + n) + 1 := by omega
    refine ⟨fun p hp => ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos p with hp0 | hp0
      · subst hp0; exact h0 (t1 + (n + 1)) (by omega)
      · obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
        rw [htt, hF, hph, ether_rule (j0 + (q + 1)) (t1 + n + s)]
        have hl : F (t1 + n) q = ether (j0 + (q + 1) + 6) (t1 + n + s) := by
          rw [hE' q (by omega)]; exact ether_congr (by omega) rfl
        rw [hl, hE' (q + 1) hp]
        by_cases hpk : q + 1 < k
        · rw [hE' (q + 2) (by omega), show j0 + (q + 2) = j0 + (q + 1) + 1 by omega]
        · have hpk' : q + 1 = k := by omega
          cases hb : ether (j0 + (q + 1)) (t1 + n + s) with
          | true => rfl
          | false =>
            have hw2 : ether 2 ((t1 + n + s) % 4) = false := by
              rw [← hb]; exact ether_congr (by omega) (by omega)
            have hhead := (wall_facts hW').1 hw2
            rw [rowOf_head, ← hpk'] at hhead
            rw [hhead]
            congr 1
            exact ether_congr (by omega) (by omega)
    · rw [htt, rowOf_succ hF, hph]
      have hck : F (t1 + n) k = ether 2 ((t1 + n + s) % 4) := by
        rw [hE' k (Nat.le_refl k)]; exact ether_congr (by omega) (by omega)
      rw [hck]
      have e := (wall_facts hW').2 (F (t1 + n) (k + 13 + 1))
      rwa [show ((t1 + n + s) % 4 + 1) % 4 = (t1 + n + s + 1) % 4 by omega] at e

/-! ### The trap theorem for the true pattern -/

/-- The true right half as an evolution on the columns `p ≥ 0`. -/
def trueRight (t p : Nat) : Bool := cell t (p : Int)

theorem trueRight_isR30 : IsR30 trueRight := by
  intro t p
  show rule (cell t (((p + 1 : Nat) : Int) - 1)) (cell t ((p + 1 : Nat) : Int))
      (cell t (((p + 1 : Nat) : Int) + 1)) =
    rule (cell t (p : Int)) (cell t ((p + 1 : Nat) : Int)) (cell t ((p + 2 : Nat) : Int))
  rw [show ((p + 1 : Nat) : Int) - 1 = (p : Int) by omega,
    show ((p + 1 : Nat) : Int) + 1 = ((p + 2 : Nat) : Int) by omega]

/-- **Ether-and-wall trap.** Suppose the center column is the ether column `j0` (with phase offset
`s`) from time `T` on. If at some time `t1 ≥ T` columns `1..k` carry the ether, column `k` is a B3
(`(j0 + k) % 7 = 2`), and columns `k+1..k+13` form a wall state, we get a contradiction. -/
theorem ether_wall_trap (T t1 j0 s k : Nat) (hk : (j0 + k) % 7 = 2)
    (h0 : ∀ t, T ≤ t → cell t 0 = ether j0 (t - T + s))
    (ht1 : T ≤ t1)
    (hE : ∀ p : Nat, 1 ≤ p → p ≤ k → cell t1 (p : Int) = ether (j0 + p) (t1 - T + s))
    (hW : ((t1 - T + s) % 4, rowOf trueRight t1 k 13) ∈ wallStates) : False := by
  have hph : ∀ t, T ≤ t → (t + (s + 3 * T)) % 4 = (t - T + s) % 4 := by intro t ht; omega
  have inv := trap_invariant trueRight_isR30 j0 (s + 3 * T) k t1 hk
    (fun t ht => by
      show cell t ((0 : Nat) : Int) = _
      rw [show ((0 : Nat) : Int) = 0 by rfl, h0 t (by omega)]
      exact ether_congr rfl (hph t (by omega)).symm)
    (fun p hp1 hpk => by
      show cell t1 (p : Int) = _
      rw [hE p hp1 hpk]
      exact ether_congr rfl (hph t1 ht1).symm)
    (by rw [hph t1 ht1]; exact hW)
  -- column `1` at the white times of column `0` is the ether column `j0 + 1`
  have key : ∀ t, t1 ≤ t → cell t 0 = false → cell t 1 = ether (j0 + 1) (t + (s + 3 * T)) := by
    intro t ht hw
    obtain ⟨hE', hW'⟩ := inv (t - t1)
    rw [show t1 + (t - t1) = t by omega] at hE' hW'
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      have hw2 : ether 2 ((t + (s + 3 * T)) % 4) = false := by
        have e : cell t 0 = ether (j0 + 0) (t + (s + 3 * T)) := hE' 0 (Nat.le_refl 0)
        rw [hw] at e
        rw [e]; exact ether_congr (by omega) (by omega)
      have hhead := (wall_facts hW').1 hw2
      rw [rowOf_head] at hhead
      have e1 : cell t 1 = ether 3 ((t + (s + 3 * T)) % 4) := hhead
      rw [e1]; exact ether_congr (by omega) (by omega)
    · exact hE' 1 hk0
  refine Rule30MaskedJen.masked_jen 0 (P := 4) (T := t1) (by decide) ?_ ?_
  · intro t ht
    rw [h0 (t + 4) (by omega), h0 t (by omega)]
    exact ether_congr rfl (by omega)
  · intro t ht hw
    have hw4 : cell (t + 4) 0 = false := by
      rw [h0 (t + 4) (by omega), ← hw, h0 t (by omega)]
      exact ether_congr rfl (by omega)
    rw [show (0 : Int) + 1 = 1 by rfl, key (t + 4) (by omega) hw4, key t ht hw]
    exact ether_congr rfl (by omega)

/-! ### The words `0001`, `0011`, `0111`, `0101` as ether columns -/

/-- The letter of the 4-periodic word `w` at phase `ψ`. -/
def wordAt (w : List Bool) (ψ : Nat) : Bool := w.getD (ψ % 4) false

def w0001 : List Bool := [false, false, false, true]
def w0011 : List Bool := [false, false, true, true]
def w0111 : List Bool := [false, true, true, true]
def w0101 : List Bool := [false, true, false, true]

/-- `w` is the ether column `j0` shifted by `s` in time: `ether j0 (ψ + s) = w[ψ mod 4]`. -/
def aligned (w : List Bool) (j0 s : Nat) : Bool :=
  (List.range 4).all fun ψ => ether j0 (ψ + s) == wordAt w ψ

theorem aligned_spec {w : List Bool} {j0 s : Nat} (h : aligned w j0 s = true) (ψ : Nat) :
    ether j0 (ψ + s) = wordAt w ψ := by
  have h1 := List.all_eq_true.1 h (ψ % 4) (List.mem_range.2 (Nat.mod_lt _ (by decide)))
  have e1 : ether j0 (ψ + s) = ether j0 (ψ % 4 + s) := ether_congr rfl (by omega)
  have e2 : wordAt w ψ = wordAt w (ψ % 4) := by unfold wordAt; rw [Nat.mod_mod]
  rw [e1, e2]; exact beq_iff_eq.1 h1

theorem aligned_0001_5 : aligned w0001 5 0 = true := by decide
theorem aligned_0001_6 : aligned w0001 6 0 = true := by decide
theorem aligned_0011_0 : aligned w0011 0 0 = true := by decide
theorem aligned_0011_1 : aligned w0011 1 3 = true := by decide
theorem aligned_0011_4 : aligned w0011 4 0 = true := by decide
theorem aligned_0111_2 : aligned w0111 2 2 = true := by decide
theorem aligned_0101_3 : aligned w0101 3 0 = true := by decide

/-- **No entry into the ether-and-wall family.** If the center column equals `w^∞` from time `T`
(phase `(t - T) % 4`) and `w` is the ether column `j0` shifted by `s`, then at no time `t1 ≥ T` do
columns `1..k` carry the ether while columns `k+1..k+13` form a wall state (`(j0 + k) % 7 = 2`). -/
theorem no_ether_wall_entry (w : List Bool) (j0 s : Nat) (hal : aligned w j0 s = true)
    (T : Nat) (hc : ∀ t, T ≤ t → cell t 0 = wordAt w (t - T))
    (t1 k : Nat) (ht1 : T ≤ t1) (hk : (j0 + k) % 7 = 2)
    (hE : ∀ p : Nat, 1 ≤ p → p ≤ k → cell t1 (p : Int) = ether (j0 + p) (t1 - T + s))
    (hW : ((t1 - T + s) % 4, rowOf trueRight t1 k 13) ∈ wallStates) : False :=
  ether_wall_trap T t1 j0 s k hk (fun t ht => by rw [hc t ht, aligned_spec hal]) ht1 hE hW


/-! ### The driven right half: explicit finite configurations that never enter `S_w` -/

/-- Rule 30 on the columns `p ≥ 1` with column `0` prescribed by `c` and initial right half `x`. -/
def drv (c x : Nat → Bool) : Nat → Nat → Bool
  | 0, p => if p = 0 then c 0 else x p
  | t + 1, 0 => c (t + 1)
  | t + 1, p + 1 => rule (drv c x t p) (drv c x t (p + 1)) (drv c x t (p + 2))

theorem drv_isR30 (c x : Nat → Bool) : IsR30 (drv c x) := fun _ _ => rfl

theorem drv_col0 (c x : Nat → Bool) : ∀ t, drv c x t 0 = c t
  | 0 => by simp [drv]
  | _ + 1 => rfl

theorem drv_init (c x : Nat → Bool) (p : Nat) (hp : 1 ≤ p) : drv c x 0 p = x p := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  simp [drv]

theorem seg_congr : ∀ (n : Nat) (f g : Nat → Bool), (∀ i, i < n → f i = g i) → seg f n = seg g n
  | 0, _, _, _ => rfl
  | n + 1, f, g, h => by
    show f 0 :: seg (fun i => f (i + 1)) n = g 0 :: seg (fun i => g (i + 1)) n
    rw [h 0 (by omega), seg_congr n _ _ (fun i hi => h (i + 1) (by omega))]

theorem seg_getD_self : ∀ (l : List Bool), seg (fun i => l.getD i false) l.length = l
  | [] => rfl
  | a :: l => by
    show a :: seg (fun i => (a :: l).getD (i + 1) false) l.length = a :: l
    congr 1
    exact seg_getD_self l

/-- A finite right half: ether columns `1..k` at phase `φ`, a 13-cell state `ws`, white beyond. -/
def config (j0 φ k : Nat) (ws : List Bool) (p : Nat) : Bool :=
  if 1 ≤ p ∧ p ≤ k then ether (j0 + p) φ
  else if k < p ∧ p ≤ k + 13 then ws.getD (p - k - 1) false else false

theorem config_finite (j0 φ k : Nat) (ws : List Bool) (p : Nat) (hp : k + 13 < p) :
    config j0 φ k ws p = false := by
  unfold config
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

/-- Columns `1..b` of the ether at phase `φ`, when column `0` is the ether column `j0`. -/
def etherRow (j0 φ b : Nat) : List Bool := seg (fun i => ether (j0 + (i + 1)) φ) b

/-- **The configuration stays in the ether-and-wall trap forever**, so its columns `1..b`
(`b ≤ k`) are the pure ether at every time. -/
theorem config_pure_ether (w : List Bool) (j0 s k b : Nat) (hal : aligned w j0 s = true)
    (hk : (j0 + k) % 7 = 2) (hb : b ≤ k) (ws : List Bool) (hws : (s % 4, ws) ∈ wallStates)
    (hlen : ws.length = 13) (t : Nat) :
    rowOf (drv (wordAt w) (config j0 s k ws)) t 0 b = etherRow j0 ((t + s) % 4) b := by
  have hF := drv_isR30 (wordAt w) (config j0 s k ws)
  have h0 : ∀ t, 0 ≤ t → drv (wordAt w) (config j0 s k ws) t 0 = ether j0 (t + s) := by
    intro t _; rw [drv_col0, aligned_spec hal]
  have hE : ∀ p, 1 ≤ p → p ≤ k → drv (wordAt w) (config j0 s k ws) 0 p = ether (j0 + p) (0 + s) := by
    intro p hp1 hpk
    rw [drv_init _ _ p hp1, Nat.zero_add]
    unfold config; rw [ite_eq_left ⟨hp1, hpk⟩]
  have hW : ((0 + s) % 4, rowOf (drv (wordAt w) (config j0 s k ws)) 0 k 13) ∈ wallStates := by
    have e : rowOf (drv (wordAt w) (config j0 s k ws)) 0 k 13 = ws := by
      unfold rowOf
      rw [← hlen]
      conv => rhs; rw [← seg_getD_self ws]
      apply seg_congr
      intro i hi
      rw [drv_init _ _ _ (by omega)]
      unfold config
      rw [ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega⟩]
      congr 1
      omega
    rw [e, Nat.zero_add]; exact hws
  obtain ⟨hE', _⟩ := trap_invariant hF j0 s k 0 hk h0 hE hW t
  simp only [Nat.zero_add] at hE'
  unfold rowOf etherRow
  apply seg_congr
  intro i hi
  rw [Nat.zero_add, hE' (i + 1) (by omega)]
  exact ether_congr rfl (by omega)

/-- A certified trap: 109 states of width 16. -/
def S0001 : List (Nat × List Bool) := [
  (0, [false, false, true, false, false, false, true, false, true, false, true, false, false, false, false, false]),
  (0, [false, false, true, false, false, false, true, false, true, false, true, false, false, false, false, true]),
  (0, [false, false, true, false, false, false, true, false, true, false, true, false, false, false, true, false]),
  (0, [false, false, true, false, false, false, true, false, true, false, true, false, false, false, true, true]),
  (0, [false, false, true, false, false, false, true, false, true, false, true, false, false, true, false, false]),
  (0, [false, false, true, false, false, false, true, false, true, false, true, false, false, true, false, true]),
  (0, [false, false, true, false, false, false, true, false, true, false, true, false, false, true, true, true]),
  (0, [false, false, true, false, false, false, true, false, true, false, true, true, false, false, false, false]),
  (0, [false, false, true, false, false, false, true, false, true, false, true, true, false, false, false, true]),
  (0, [false, false, true, false, false, false, true, false, true, false, true, true, false, false, true, true]),
  (0, [false, false, true, false, false, false, true, false, true, false, true, true, false, true, true, false]),
  (0, [false, false, true, false, true, false, false, false, false, false, true, false, false, false, false, false]),
  (0, [false, false, true, false, true, false, false, false, false, false, true, false, false, false, false, true]),
  (0, [false, false, true, false, true, false, false, false, false, false, true, false, false, true, false, false]),
  (0, [false, false, true, false, true, false, false, false, false, false, true, false, false, true, false, true]),
  (0, [false, false, true, false, true, false, false, false, false, false, true, false, true, false, false, false]),
  (0, [false, false, true, false, true, false, false, false, false, false, true, false, true, false, false, true]),
  (0, [false, false, true, false, true, false, false, false, false, false, true, false, true, false, true, false]),
  (0, [false, false, true, false, true, false, false, false, false, false, true, false, true, false, true, true]),
  (0, [false, false, true, false, true, false, false, false, false, false, true, false, true, true, false, false]),
  (0, [false, false, true, false, true, false, false, false, false, false, true, false, true, true, false, true]),
  (0, [false, false, true, false, true, false, false, false, false, false, true, false, true, true, true, false]),
  (0, [false, false, true, false, true, false, false, false, false, false, true, false, true, true, true, true]),
  (0, [false, false, true, false, true, false, false, false, false, false, true, true, false, false, false, false]),
  (0, [false, false, true, false, true, false, false, false, false, false, true, true, false, false, false, true]),
  (0, [false, false, true, false, true, false, false, false, false, false, true, true, false, false, true, true]),
  (1, [false, true, true, false, true, true, false, false, false, true, true, false, true, false, false, false]),
  (1, [false, true, true, false, true, true, false, false, false, true, true, false, true, false, false, true]),
  (1, [false, true, true, false, true, true, false, false, false, true, true, false, true, false, true, false]),
  (1, [false, true, true, false, true, true, false, false, false, true, true, false, true, false, true, true]),
  (1, [false, true, true, false, true, true, false, false, false, true, true, false, true, true, false, false]),
  (1, [false, true, true, false, true, true, false, false, false, true, true, false, true, true, false, true]),
  (1, [false, true, true, false, true, true, false, false, false, true, true, false, true, true, true, false]),
  (1, [false, true, true, false, true, true, false, false, false, true, true, false, true, true, true, true]),
  (1, [false, true, true, false, true, true, false, false, false, true, true, true, false, false, false, false]),
  (1, [false, true, true, false, true, true, false, false, false, true, true, true, false, false, false, true]),
  (1, [false, true, true, false, true, true, false, false, false, true, true, true, false, false, true, true]),
  (1, [false, true, true, false, true, true, false, false, false, true, true, true, true, true, false, true]),
  (1, [false, true, true, false, true, true, false, false, false, true, true, true, true, true, true, false]),
  (1, [false, true, true, false, true, true, false, false, false, true, true, true, true, true, true, true]),
  (1, [false, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false]),
  (1, [false, true, true, true, false, true, true, false, true, false, true, false, false, true, false, true]),
  (1, [false, true, true, true, false, true, true, false, true, false, true, false, true, false, false, false]),
  (1, [false, true, true, true, false, true, true, false, true, false, true, false, true, false, false, true]),
  (1, [false, true, true, true, false, true, true, false, true, false, true, false, true, false, true, true]),
  (1, [false, true, true, true, false, true, true, false, true, false, true, false, true, true, true, false]),
  (1, [false, true, true, true, false, true, true, false, true, false, true, true, false, false, false, false]),
  (1, [false, true, true, true, false, true, true, false, true, false, true, true, false, false, false, true]),
  (1, [false, true, true, true, false, true, true, false, true, false, true, true, false, false, true, true]),
  (1, [false, true, true, true, false, true, true, false, true, false, true, true, false, true, true, false]),
  (1, [false, true, true, true, false, true, true, false, true, false, true, true, false, true, true, true]),
  (1, [false, true, true, true, false, true, true, false, true, false, true, true, true, true, false, false]),
  (1, [false, true, true, true, false, true, true, false, true, false, true, true, true, true, false, true]),
  (1, [false, true, true, true, false, true, true, false, true, false, true, true, true, true, true, false]),
  (1, [false, true, true, true, false, true, true, false, true, false, true, true, true, true, true, true]),
  (2, [true, true, false, false, false, true, false, false, true, false, true, false, false, false, false, false]),
  (2, [true, true, false, false, false, true, false, false, true, false, true, false, false, false, false, true]),
  (2, [true, true, false, false, false, true, false, false, true, false, true, false, false, false, true, false]),
  (2, [true, true, false, false, false, true, false, false, true, false, true, false, false, false, true, true]),
  (2, [true, true, false, false, false, true, false, false, true, false, true, false, false, true, false, false]),
  (2, [true, true, false, false, false, true, false, false, true, false, true, false, false, true, false, true]),
  (2, [true, true, false, false, false, true, false, false, true, false, true, false, true, false, false, false]),
  (2, [true, true, false, false, false, true, false, false, true, false, true, false, true, false, false, true]),
  (2, [true, true, false, false, false, true, false, false, true, false, true, false, true, false, true, false]),
  (2, [true, true, false, false, false, true, false, false, true, false, true, false, true, false, true, true]),
  (2, [true, true, false, false, false, true, false, false, true, false, true, false, true, true, false, false]),
  (2, [true, true, false, false, false, true, false, false, true, false, true, false, true, true, false, true]),
  (2, [true, true, false, false, false, true, false, false, true, false, true, false, true, true, true, false]),
  (2, [true, true, false, false, false, true, false, false, true, false, true, false, true, true, true, true]),
  (2, [true, true, false, false, false, true, false, false, true, false, true, true, true, true, false, true]),
  (2, [true, true, false, false, false, true, false, false, true, false, true, true, true, true, true, false]),
  (2, [true, true, false, false, false, true, false, false, true, false, true, true, true, true, true, true]),
  (2, [true, true, false, false, true, false, true, false, true, true, false, false, false, false, false, false]),
  (2, [true, true, false, false, true, false, true, false, true, true, false, false, false, false, false, true]),
  (2, [true, true, false, false, true, false, true, false, true, true, false, false, true, false, false, false]),
  (2, [true, true, false, false, true, false, true, false, true, true, false, false, true, false, false, true]),
  (2, [true, true, false, false, true, false, true, false, true, true, false, false, true, false, true, false]),
  (2, [true, true, false, false, true, false, true, false, true, true, false, false, true, false, true, true]),
  (2, [true, true, false, false, true, false, true, false, true, true, false, false, true, true, false, false]),
  (2, [true, true, false, false, true, false, true, false, true, true, false, false, true, true, false, true]),
  (2, [true, true, false, false, true, false, true, false, true, true, false, false, true, true, true, false]),
  (2, [true, true, false, false, true, false, true, false, true, true, false, false, true, true, true, true]),
  (3, [true, false, true, false, true, true, true, true, true, false, true, false, false, false, false, false]),
  (3, [true, false, true, false, true, true, true, true, true, false, true, false, false, false, false, true]),
  (3, [true, false, true, false, true, true, true, true, true, false, true, false, true, false, false, false]),
  (3, [true, false, true, false, true, true, true, true, true, false, true, false, true, false, false, true]),
  (3, [true, false, true, false, true, true, true, true, true, false, true, false, true, false, true, false]),
  (3, [true, false, true, false, true, true, true, true, true, false, true, false, true, false, true, true]),
  (3, [true, false, true, false, true, true, true, true, true, false, true, false, true, true, false, false]),
  (3, [true, false, true, false, true, true, true, true, true, false, true, false, true, true, false, true]),
  (3, [true, false, true, false, true, true, true, true, true, false, true, false, true, true, true, true]),
  (3, [true, false, true, false, true, true, true, true, true, false, true, true, false, false, false, false]),
  (3, [true, false, true, false, true, true, true, true, true, false, true, true, false, false, false, true]),
  (3, [true, false, true, false, true, true, true, true, true, false, true, true, false, false, true, true]),
  (3, [true, false, true, false, true, true, true, true, true, false, true, true, false, true, true, false]),
  (3, [true, false, true, false, true, true, true, true, true, false, true, true, false, true, true, true]),
  (3, [true, false, true, false, true, true, true, true, true, false, true, true, true, true, false, true]),
  (3, [true, false, true, false, true, true, true, true, true, false, true, true, true, true, true, false]),
  (3, [true, false, true, false, true, true, true, true, true, false, true, true, true, true, true, true]),
  (3, [true, false, true, true, true, false, true, false, true, false, true, false, false, false, false, false]),
  (3, [true, false, true, true, true, false, true, false, true, false, true, false, false, false, false, true]),
  (3, [true, false, true, true, true, false, true, false, true, false, true, false, false, false, true, true]),
  (3, [true, false, true, true, true, false, true, false, true, false, true, true, true, false, false, false]),
  (3, [true, false, true, true, true, false, true, false, true, false, true, true, true, false, false, true]),
  (3, [true, false, true, true, true, false, true, false, true, false, true, true, true, false, true, false]),
  (3, [true, false, true, true, true, false, true, false, true, false, true, true, true, false, true, true]),
  (3, [true, false, true, true, true, false, true, false, true, false, true, true, true, true, false, false]),
  (3, [true, false, true, true, true, false, true, false, true, false, true, true, true, true, false, true]),
  (3, [true, false, true, true, true, false, true, false, true, false, true, true, true, true, true, true])
]

/-- A certified trap: 188 states of width 16. -/
def S0011 : List (Nat × List Bool) := [
  (0, [false, true, false, false, false, true, false, true, false, true, false, false, false, false, false, false]),
  (0, [false, true, false, false, false, true, false, true, false, true, false, false, false, false, false, true]),
  (0, [false, true, false, false, false, true, false, true, false, true, false, false, false, false, true, false]),
  (0, [false, true, false, false, false, true, false, true, false, true, false, false, false, true, false, false]),
  (0, [false, true, false, false, false, true, false, true, false, true, false, false, false, true, false, true]),
  (0, [false, true, false, false, false, true, false, true, false, true, false, false, false, true, true, false]),
  (0, [false, true, false, false, false, true, false, true, false, true, false, false, false, true, true, true]),
  (0, [false, true, false, false, false, true, false, true, false, true, false, false, true, false, false, false]),
  (0, [false, true, false, false, false, true, false, true, false, true, false, false, true, false, false, true]),
  (0, [false, true, false, false, false, true, false, true, false, true, false, false, true, false, true, true]),
  (0, [false, true, false, false, false, true, false, true, false, true, false, false, true, true, true, false]),
  (0, [false, true, false, false, false, true, false, true, false, true, false, false, true, true, true, true]),
  (0, [false, true, false, false, false, true, false, true, false, true, true, false, false, false, false, false]),
  (0, [false, true, false, false, false, true, false, true, false, true, true, false, false, false, false, true]),
  (0, [false, true, false, false, false, true, false, true, false, true, true, false, false, false, true, true]),
  (0, [false, true, false, false, false, true, false, true, false, true, true, false, false, true, true, false]),
  (0, [false, true, false, false, false, true, false, true, false, true, true, false, true, true, false, false]),
  (0, [false, true, false, false, false, true, false, true, false, true, true, false, true, true, false, true]),
  (0, [false, true, false, true, false, false, false, false, false, true, false, false, false, false, false, false]),
  (0, [false, true, false, true, false, false, false, false, false, true, false, false, false, false, false, true]),
  (0, [false, true, false, true, false, false, false, false, false, true, false, false, false, false, true, false]),
  (0, [false, true, false, true, false, false, false, false, false, true, false, false, false, false, true, true]),
  (0, [false, true, false, true, false, false, false, false, false, true, false, false, true, false, false, false]),
  (0, [false, true, false, true, false, false, false, false, false, true, false, false, true, false, false, true]),
  (0, [false, true, false, true, false, false, false, false, false, true, false, false, true, false, true, false]),
  (0, [false, true, false, true, false, false, false, false, false, true, false, false, true, false, true, true]),
  (0, [false, true, false, true, false, false, false, false, false, true, false, true, false, false, false, false]),
  (0, [false, true, false, true, false, false, false, false, false, true, false, true, false, false, false, true]),
  (0, [false, true, false, true, false, false, false, false, false, true, false, true, false, false, true, false]),
  (0, [false, true, false, true, false, false, false, false, false, true, false, true, false, false, true, true]),
  (0, [false, true, false, true, false, false, false, false, false, true, false, true, false, true, false, false]),
  (0, [false, true, false, true, false, false, false, false, false, true, false, true, false, true, false, true]),
  (0, [false, true, false, true, false, false, false, false, false, true, false, true, false, true, true, false]),
  (0, [false, true, false, true, false, false, false, false, false, true, false, true, false, true, true, true]),
  (0, [false, true, false, true, false, false, false, false, false, true, false, true, true, false, false, false]),
  (0, [false, true, false, true, false, false, false, false, false, true, false, true, true, false, false, true]),
  (0, [false, true, false, true, false, false, false, false, false, true, false, true, true, false, true, true]),
  (0, [false, true, false, true, false, false, false, false, false, true, false, true, true, true, false, false]),
  (0, [false, true, false, true, false, false, false, false, false, true, false, true, true, true, false, true]),
  (0, [false, true, false, true, false, false, false, false, false, true, false, true, true, true, true, false]),
  (0, [false, true, false, true, false, false, false, false, false, true, false, true, true, true, true, true]),
  (0, [false, true, false, true, false, false, false, false, false, true, true, false, false, false, false, false]),
  (0, [false, true, false, true, false, false, false, false, false, true, true, false, false, false, false, true]),
  (0, [false, true, false, true, false, false, false, false, false, true, true, false, false, true, true, false]),
  (0, [false, true, false, true, false, false, false, false, false, true, true, false, false, true, true, true]),
  (1, [true, true, false, true, true, false, false, false, true, true, false, true, false, false, false, false]),
  (1, [true, true, false, true, true, false, false, false, true, true, false, true, false, false, false, true]),
  (1, [true, true, false, true, true, false, false, false, true, true, false, true, false, false, true, false]),
  (1, [true, true, false, true, true, false, false, false, true, true, false, true, false, false, true, true]),
  (1, [true, true, false, true, true, false, false, false, true, true, false, true, false, true, false, false]),
  (1, [true, true, false, true, true, false, false, false, true, true, false, true, false, true, false, true]),
  (1, [true, true, false, true, true, false, false, false, true, true, false, true, false, true, true, false]),
  (1, [true, true, false, true, true, false, false, false, true, true, false, true, false, true, true, true]),
  (1, [true, true, false, true, true, false, false, false, true, true, false, true, true, false, false, false]),
  (1, [true, true, false, true, true, false, false, false, true, true, false, true, true, false, false, true]),
  (1, [true, true, false, true, true, false, false, false, true, true, false, true, true, false, true, true]),
  (1, [true, true, false, true, true, false, false, false, true, true, false, true, true, true, false, false]),
  (1, [true, true, false, true, true, false, false, false, true, true, false, true, true, true, false, true]),
  (1, [true, true, false, true, true, false, false, false, true, true, false, true, true, true, true, false]),
  (1, [true, true, false, true, true, false, false, false, true, true, false, true, true, true, true, true]),
  (1, [true, true, false, true, true, false, false, false, true, true, true, false, false, false, false, false]),
  (1, [true, true, false, true, true, false, false, false, true, true, true, false, false, false, false, true]),
  (1, [true, true, false, true, true, false, false, false, true, true, true, false, false, false, true, true]),
  (1, [true, true, false, true, true, false, false, false, true, true, true, false, false, true, true, false]),
  (1, [true, true, false, true, true, false, false, false, true, true, true, false, false, true, true, true]),
  (1, [true, true, false, true, true, false, false, false, true, true, true, true, true, false, true, false]),
  (1, [true, true, false, true, true, false, false, false, true, true, true, true, true, false, true, true]),
  (1, [true, true, false, true, true, false, false, false, true, true, true, true, true, true, false, false]),
  (1, [true, true, false, true, true, false, false, false, true, true, true, true, true, true, false, true]),
  (1, [true, true, false, true, true, false, false, false, true, true, true, true, true, true, true, true]),
  (1, [true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true]),
  (1, [true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, false]),
  (1, [true, true, true, false, true, true, false, true, false, true, false, false, true, false, true, true]),
  (1, [true, true, true, false, true, true, false, true, false, true, false, true, false, false, false, false]),
  (1, [true, true, true, false, true, true, false, true, false, true, false, true, false, false, false, true]),
  (1, [true, true, true, false, true, true, false, true, false, true, false, true, false, false, true, true]),
  (1, [true, true, true, false, true, true, false, true, false, true, false, true, false, true, true, false]),
  (1, [true, true, true, false, true, true, false, true, false, true, false, true, true, true, false, false]),
  (1, [true, true, true, false, true, true, false, true, false, true, false, true, true, true, false, true]),
  (1, [true, true, true, false, true, true, false, true, false, true, true, false, false, false, false, false]),
  (1, [true, true, true, false, true, true, false, true, false, true, true, false, false, false, false, true]),
  (1, [true, true, true, false, true, true, false, true, false, true, true, false, false, false, true, true]),
  (1, [true, true, true, false, true, true, false, true, false, true, true, false, false, true, true, false]),
  (1, [true, true, true, false, true, true, false, true, false, true, true, false, false, true, true, true]),
  (1, [true, true, true, false, true, true, false, true, false, true, true, false, true, true, false, false]),
  (1, [true, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true]),
  (1, [true, true, true, false, true, true, false, true, false, true, true, false, true, true, true, false]),
  (1, [true, true, true, false, true, true, false, true, false, true, true, false, true, true, true, true]),
  (1, [true, true, true, false, true, true, false, true, false, true, true, true, true, false, false, false]),
  (1, [true, true, true, false, true, true, false, true, false, true, true, true, true, false, false, true]),
  (1, [true, true, true, false, true, true, false, true, false, true, true, true, true, false, true, false]),
  (1, [true, true, true, false, true, true, false, true, false, true, true, true, true, true, false, false]),
  (1, [true, true, true, false, true, true, false, true, false, true, true, true, true, true, false, true]),
  (1, [true, true, true, false, true, true, false, true, false, true, true, true, true, true, true, true]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, false, false, false, false, false]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, false, false, false, false, true]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, false, false, false, true, false]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, false, false, false, true, true]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, false, false, true, false, false]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, false, false, true, false, true]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, false, false, true, true, true]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, false, true, false, false, false]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, false, true, false, false, true]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, false, true, false, true, false]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, false, true, false, true, true]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, true, false, false, false, false]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, true, false, false, false, true]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, true, false, false, true, false]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, true, false, false, true, true]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, true, false, true, false, false]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, true, false, true, false, true]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, true, false, true, true, false]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, true, true, false, false, false]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, true, true, false, false, true]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, true, true, false, true, true]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, true, true, true, false, false]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, true, true, true, false, true]),
  (2, [true, false, false, false, true, false, false, true, false, true, false, true, true, true, true, false]),
  (2, [true, false, false, false, true, false, false, true, false, true, true, true, true, false, true, false]),
  (2, [true, false, false, false, true, false, false, true, false, true, true, true, true, false, true, true]),
  (2, [true, false, false, false, true, false, false, true, false, true, true, true, true, true, true, true]),
  (2, [true, false, false, true, false, true, false, true, true, false, false, false, false, false, false, false]),
  (2, [true, false, false, true, false, true, false, true, true, false, false, false, false, false, false, true]),
  (2, [true, false, false, true, false, true, false, true, true, false, false, false, false, false, true, false]),
  (2, [true, false, false, true, false, true, false, true, true, false, false, false, false, false, true, true]),
  (2, [true, false, false, true, false, true, false, true, true, false, false, true, false, false, false, false]),
  (2, [true, false, false, true, false, true, false, true, true, false, false, true, false, false, false, true]),
  (2, [true, false, false, true, false, true, false, true, true, false, false, true, false, false, true, false]),
  (2, [true, false, false, true, false, true, false, true, true, false, false, true, false, false, true, true]),
  (2, [true, false, false, true, false, true, false, true, true, false, false, true, false, true, false, false]),
  (2, [true, false, false, true, false, true, false, true, true, false, false, true, false, true, false, true]),
  (2, [true, false, false, true, false, true, false, true, true, false, false, true, false, true, true, false]),
  (2, [true, false, false, true, false, true, false, true, true, false, false, true, false, true, true, true]),
  (2, [true, false, false, true, false, true, false, true, true, false, false, true, true, false, false, false]),
  (2, [true, false, false, true, false, true, false, true, true, false, false, true, true, false, false, true]),
  (2, [true, false, false, true, false, true, false, true, true, false, false, true, true, false, true, true]),
  (2, [true, false, false, true, false, true, false, true, true, false, false, true, true, true, false, false]),
  (2, [true, false, false, true, false, true, false, true, true, false, false, true, true, true, false, true]),
  (2, [true, false, false, true, false, true, false, true, true, false, false, true, true, true, true, false]),
  (2, [true, false, false, true, false, true, false, true, true, false, false, true, true, true, true, true]),
  (3, [false, true, false, true, true, true, true, true, false, true, false, false, false, false, false, false]),
  (3, [false, true, false, true, true, true, true, true, false, true, false, false, false, false, true, false]),
  (3, [false, true, false, true, true, true, true, true, false, true, false, false, false, false, true, true]),
  (3, [false, true, false, true, true, true, true, true, false, true, false, true, false, false, false, false]),
  (3, [false, true, false, true, true, true, true, true, false, true, false, true, false, false, false, true]),
  (3, [false, true, false, true, true, true, true, true, false, true, false, true, false, false, true, false]),
  (3, [false, true, false, true, true, true, true, true, false, true, false, true, false, false, true, true]),
  (3, [false, true, false, true, true, true, true, true, false, true, false, true, false, true, false, false]),
  (3, [false, true, false, true, true, true, true, true, false, true, false, true, false, true, false, true]),
  (3, [false, true, false, true, true, true, true, true, false, true, false, true, false, true, true, false]),
  (3, [false, true, false, true, true, true, true, true, false, true, false, true, false, true, true, true]),
  (3, [false, true, false, true, true, true, true, true, false, true, false, true, true, false, false, false]),
  (3, [false, true, false, true, true, true, true, true, false, true, false, true, true, false, false, true]),
  (3, [false, true, false, true, true, true, true, true, false, true, false, true, true, false, true, true]),
  (3, [false, true, false, true, true, true, true, true, false, true, false, true, true, true, true, false]),
  (3, [false, true, false, true, true, true, true, true, false, true, false, true, true, true, true, true]),
  (3, [false, true, false, true, true, true, true, true, false, true, true, false, false, false, false, false]),
  (3, [false, true, false, true, true, true, true, true, false, true, true, false, false, false, false, true]),
  (3, [false, true, false, true, true, true, true, true, false, true, true, false, false, false, true, true]),
  (3, [false, true, false, true, true, true, true, true, false, true, true, false, false, true, true, false]),
  (3, [false, true, false, true, true, true, true, true, false, true, true, false, false, true, true, true]),
  (3, [false, true, false, true, true, true, true, true, false, true, true, false, true, true, false, false]),
  (3, [false, true, false, true, true, true, true, true, false, true, true, false, true, true, false, true]),
  (3, [false, true, false, true, true, true, true, true, false, true, true, false, true, true, true, false]),
  (3, [false, true, false, true, true, true, true, true, false, true, true, false, true, true, true, true]),
  (3, [false, true, false, true, true, true, true, true, false, true, true, true, true, false, true, false]),
  (3, [false, true, false, true, true, true, true, true, false, true, true, true, true, false, true, true]),
  (3, [false, true, false, true, true, true, true, true, false, true, true, true, true, true, false, false]),
  (3, [false, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true]),
  (3, [false, true, false, true, true, true, true, true, false, true, true, true, true, true, true, true]),
  (3, [false, true, true, true, false, true, false, true, false, true, false, false, false, false, false, false]),
  (3, [false, true, true, true, false, true, false, true, false, true, false, false, false, false, false, true]),
  (3, [false, true, true, true, false, true, false, true, false, true, false, false, false, false, true, true]),
  (3, [false, true, true, true, false, true, false, true, false, true, false, false, false, true, true, false]),
  (3, [false, true, true, true, false, true, false, true, false, true, false, false, false, true, true, true]),
  (3, [false, true, true, true, false, true, false, true, false, true, true, true, false, false, false, false]),
  (3, [false, true, true, true, false, true, false, true, false, true, true, true, false, false, false, true]),
  (3, [false, true, true, true, false, true, false, true, false, true, true, true, false, false, true, false]),
  (3, [false, true, true, true, false, true, false, true, false, true, true, true, false, false, true, true]),
  (3, [false, true, true, true, false, true, false, true, false, true, true, true, false, true, false, false]),
  (3, [false, true, true, true, false, true, false, true, false, true, true, true, false, true, false, true]),
  (3, [false, true, true, true, false, true, false, true, false, true, true, true, false, true, true, false]),
  (3, [false, true, true, true, false, true, false, true, false, true, true, true, false, true, true, true]),
  (3, [false, true, true, true, false, true, false, true, false, true, true, true, true, false, false, false]),
  (3, [false, true, true, true, false, true, false, true, false, true, true, true, true, false, false, true]),
  (3, [false, true, true, true, false, true, false, true, false, true, true, true, true, false, true, true]),
  (3, [false, true, true, true, false, true, false, true, false, true, true, true, true, true, true, false]),
  (3, [false, true, true, true, false, true, false, true, false, true, true, true, true, true, true, true])
]

/-- A certified trap: 188 states of width 14. -/
def S0111 : List (Nat × List Bool) := [
  (0, [false, false, true, false, false, true, false, true, false, false, false, false, false, false]),
  (0, [false, false, true, false, false, true, false, true, false, false, false, false, false, true]),
  (0, [false, false, true, false, false, true, false, true, false, false, false, false, true, false]),
  (0, [false, false, true, false, false, true, false, true, false, false, false, false, true, true]),
  (0, [false, false, true, false, false, true, false, true, false, false, false, true, false, false]),
  (0, [false, false, true, false, false, true, false, true, false, false, false, true, false, true]),
  (0, [false, false, true, false, false, true, false, true, false, false, false, true, true, true]),
  (0, [false, false, true, false, false, true, false, true, false, false, true, false, false, false]),
  (0, [false, false, true, false, false, true, false, true, false, false, true, false, false, true]),
  (0, [false, false, true, false, false, true, false, true, false, false, true, false, true, false]),
  (0, [false, false, true, false, false, true, false, true, false, false, true, false, true, true]),
  (0, [false, false, true, false, false, true, false, true, false, true, false, false, false, false]),
  (0, [false, false, true, false, false, true, false, true, false, true, false, false, false, true]),
  (0, [false, false, true, false, false, true, false, true, false, true, false, false, true, false]),
  (0, [false, false, true, false, false, true, false, true, false, true, false, false, true, true]),
  (0, [false, false, true, false, false, true, false, true, false, true, false, true, false, false]),
  (0, [false, false, true, false, false, true, false, true, false, true, false, true, false, true]),
  (0, [false, false, true, false, false, true, false, true, false, true, false, true, true, false]),
  (0, [false, false, true, false, false, true, false, true, false, true, true, false, false, false]),
  (0, [false, false, true, false, false, true, false, true, false, true, true, false, false, true]),
  (0, [false, false, true, false, false, true, false, true, false, true, true, false, true, true]),
  (0, [false, false, true, false, false, true, false, true, false, true, true, true, false, false]),
  (0, [false, false, true, false, false, true, false, true, false, true, true, true, false, true]),
  (0, [false, false, true, false, false, true, false, true, false, true, true, true, true, false]),
  (0, [false, false, true, false, false, true, false, true, true, true, true, false, true, false]),
  (0, [false, false, true, false, false, true, false, true, true, true, true, false, true, true]),
  (0, [false, false, true, false, false, true, false, true, true, true, true, true, true, true]),
  (0, [false, true, false, true, false, true, true, false, false, false, false, false, false, false]),
  (0, [false, true, false, true, false, true, true, false, false, false, false, false, false, true]),
  (0, [false, true, false, true, false, true, true, false, false, false, false, false, true, false]),
  (0, [false, true, false, true, false, true, true, false, false, false, false, false, true, true]),
  (0, [false, true, false, true, false, true, true, false, false, true, false, false, false, false]),
  (0, [false, true, false, true, false, true, true, false, false, true, false, false, false, true]),
  (0, [false, true, false, true, false, true, true, false, false, true, false, false, true, false]),
  (0, [false, true, false, true, false, true, true, false, false, true, false, false, true, true]),
  (0, [false, true, false, true, false, true, true, false, false, true, false, true, false, false]),
  (0, [false, true, false, true, false, true, true, false, false, true, false, true, false, true]),
  (0, [false, true, false, true, false, true, true, false, false, true, false, true, true, false]),
  (0, [false, true, false, true, false, true, true, false, false, true, false, true, true, true]),
  (0, [false, true, false, true, false, true, true, false, false, true, true, false, false, false]),
  (0, [false, true, false, true, false, true, true, false, false, true, true, false, false, true]),
  (0, [false, true, false, true, false, true, true, false, false, true, true, false, true, true]),
  (0, [false, true, false, true, false, true, true, false, false, true, true, true, false, false]),
  (0, [false, true, false, true, false, true, true, false, false, true, true, true, false, true]),
  (0, [false, true, false, true, false, true, true, false, false, true, true, true, true, false]),
  (0, [false, true, false, true, false, true, true, false, false, true, true, true, true, true]),
  (1, [false, true, true, true, true, true, false, true, false, false, false, false, false, false]),
  (1, [false, true, true, true, true, true, false, true, false, false, false, false, true, false]),
  (1, [false, true, true, true, true, true, false, true, false, false, false, false, true, true]),
  (1, [false, true, true, true, true, true, false, true, false, true, false, false, false, false]),
  (1, [false, true, true, true, true, true, false, true, false, true, false, false, false, true]),
  (1, [false, true, true, true, true, true, false, true, false, true, false, false, true, false]),
  (1, [false, true, true, true, true, true, false, true, false, true, false, false, true, true]),
  (1, [false, true, true, true, true, true, false, true, false, true, false, true, false, false]),
  (1, [false, true, true, true, true, true, false, true, false, true, false, true, false, true]),
  (1, [false, true, true, true, true, true, false, true, false, true, false, true, true, false]),
  (1, [false, true, true, true, true, true, false, true, false, true, false, true, true, true]),
  (1, [false, true, true, true, true, true, false, true, false, true, true, false, false, false]),
  (1, [false, true, true, true, true, true, false, true, false, true, true, false, false, true]),
  (1, [false, true, true, true, true, true, false, true, false, true, true, false, true, true]),
  (1, [false, true, true, true, true, true, false, true, false, true, true, true, true, false]),
  (1, [false, true, true, true, true, true, false, true, false, true, true, true, true, true]),
  (1, [false, true, true, true, true, true, false, true, true, false, false, false, false, false]),
  (1, [false, true, true, true, true, true, false, true, true, false, false, false, false, true]),
  (1, [false, true, true, true, true, true, false, true, true, false, false, false, true, true]),
  (1, [false, true, true, true, true, true, false, true, true, false, false, true, true, false]),
  (1, [false, true, true, true, true, true, false, true, true, false, false, true, true, true]),
  (1, [false, true, true, true, true, true, false, true, true, false, true, true, false, false]),
  (1, [false, true, true, true, true, true, false, true, true, false, true, true, false, true]),
  (1, [false, true, true, true, true, true, false, true, true, false, true, true, true, false]),
  (1, [false, true, true, true, true, true, false, true, true, false, true, true, true, true]),
  (1, [false, true, true, true, true, true, false, true, true, true, true, false, true, false]),
  (1, [false, true, true, true, true, true, false, true, true, true, true, false, true, true]),
  (1, [false, true, true, true, true, true, false, true, true, true, true, true, false, false]),
  (1, [false, true, true, true, true, true, false, true, true, true, true, true, false, true]),
  (1, [false, true, true, true, true, true, false, true, true, true, true, true, true, true]),
  (1, [true, true, false, true, false, true, false, true, false, false, false, false, false, false]),
  (1, [true, true, false, true, false, true, false, true, false, false, false, false, false, true]),
  (1, [true, true, false, true, false, true, false, true, false, false, false, false, true, true]),
  (1, [true, true, false, true, false, true, false, true, false, false, false, true, true, false]),
  (1, [true, true, false, true, false, true, false, true, false, false, false, true, true, true]),
  (1, [true, true, false, true, false, true, false, true, true, true, false, false, false, false]),
  (1, [true, true, false, true, false, true, false, true, true, true, false, false, false, true]),
  (1, [true, true, false, true, false, true, false, true, true, true, false, false, true, false]),
  (1, [true, true, false, true, false, true, false, true, true, true, false, false, true, true]),
  (1, [true, true, false, true, false, true, false, true, true, true, false, true, false, false]),
  (1, [true, true, false, true, false, true, false, true, true, true, false, true, false, true]),
  (1, [true, true, false, true, false, true, false, true, true, true, false, true, true, false]),
  (1, [true, true, false, true, false, true, false, true, true, true, false, true, true, true]),
  (1, [true, true, false, true, false, true, false, true, true, true, true, false, false, false]),
  (1, [true, true, false, true, false, true, false, true, true, true, true, false, false, true]),
  (1, [true, true, false, true, false, true, false, true, true, true, true, false, true, true]),
  (1, [true, true, false, true, false, true, false, true, true, true, true, true, true, false]),
  (1, [true, true, false, true, false, true, false, true, true, true, true, true, true, true]),
  (2, [false, false, false, true, false, true, false, true, false, false, false, false, false, false]),
  (2, [false, false, false, true, false, true, false, true, false, false, false, false, false, true]),
  (2, [false, false, false, true, false, true, false, true, false, false, false, false, true, false]),
  (2, [false, false, false, true, false, true, false, true, false, false, false, true, false, false]),
  (2, [false, false, false, true, false, true, false, true, false, false, false, true, false, true]),
  (2, [false, false, false, true, false, true, false, true, false, false, false, true, true, false]),
  (2, [false, false, false, true, false, true, false, true, false, false, false, true, true, true]),
  (2, [false, false, false, true, false, true, false, true, false, false, true, false, false, false]),
  (2, [false, false, false, true, false, true, false, true, false, false, true, false, false, true]),
  (2, [false, false, false, true, false, true, false, true, false, false, true, false, true, true]),
  (2, [false, false, false, true, false, true, false, true, false, false, true, true, true, false]),
  (2, [false, false, false, true, false, true, false, true, false, false, true, true, true, true]),
  (2, [false, false, false, true, false, true, false, true, true, false, false, false, false, false]),
  (2, [false, false, false, true, false, true, false, true, true, false, false, false, false, true]),
  (2, [false, false, false, true, false, true, false, true, true, false, false, false, true, true]),
  (2, [false, false, false, true, false, true, false, true, true, false, false, true, true, false]),
  (2, [false, false, false, true, false, true, false, true, true, false, true, true, false, false]),
  (2, [false, false, false, true, false, true, false, true, true, false, true, true, false, true]),
  (2, [false, true, false, false, false, false, false, true, false, false, false, false, false, false]),
  (2, [false, true, false, false, false, false, false, true, false, false, false, false, false, true]),
  (2, [false, true, false, false, false, false, false, true, false, false, false, false, true, false]),
  (2, [false, true, false, false, false, false, false, true, false, false, false, false, true, true]),
  (2, [false, true, false, false, false, false, false, true, false, false, true, false, false, false]),
  (2, [false, true, false, false, false, false, false, true, false, false, true, false, false, true]),
  (2, [false, true, false, false, false, false, false, true, false, false, true, false, true, false]),
  (2, [false, true, false, false, false, false, false, true, false, false, true, false, true, true]),
  (2, [false, true, false, false, false, false, false, true, false, true, false, false, false, false]),
  (2, [false, true, false, false, false, false, false, true, false, true, false, false, false, true]),
  (2, [false, true, false, false, false, false, false, true, false, true, false, false, true, false]),
  (2, [false, true, false, false, false, false, false, true, false, true, false, false, true, true]),
  (2, [false, true, false, false, false, false, false, true, false, true, false, true, false, false]),
  (2, [false, true, false, false, false, false, false, true, false, true, false, true, false, true]),
  (2, [false, true, false, false, false, false, false, true, false, true, false, true, true, false]),
  (2, [false, true, false, false, false, false, false, true, false, true, false, true, true, true]),
  (2, [false, true, false, false, false, false, false, true, false, true, true, false, false, false]),
  (2, [false, true, false, false, false, false, false, true, false, true, true, false, false, true]),
  (2, [false, true, false, false, false, false, false, true, false, true, true, false, true, true]),
  (2, [false, true, false, false, false, false, false, true, false, true, true, true, false, false]),
  (2, [false, true, false, false, false, false, false, true, false, true, true, true, false, true]),
  (2, [false, true, false, false, false, false, false, true, false, true, true, true, true, false]),
  (2, [false, true, false, false, false, false, false, true, false, true, true, true, true, true]),
  (2, [false, true, false, false, false, false, false, true, true, false, false, false, false, false]),
  (2, [false, true, false, false, false, false, false, true, true, false, false, false, false, true]),
  (2, [false, true, false, false, false, false, false, true, true, false, false, true, true, false]),
  (2, [false, true, false, false, false, false, false, true, true, false, false, true, true, true]),
  (3, [false, true, true, false, false, false, true, true, false, true, false, false, false, false]),
  (3, [false, true, true, false, false, false, true, true, false, true, false, false, false, true]),
  (3, [false, true, true, false, false, false, true, true, false, true, false, false, true, false]),
  (3, [false, true, true, false, false, false, true, true, false, true, false, false, true, true]),
  (3, [false, true, true, false, false, false, true, true, false, true, false, true, false, false]),
  (3, [false, true, true, false, false, false, true, true, false, true, false, true, false, true]),
  (3, [false, true, true, false, false, false, true, true, false, true, false, true, true, false]),
  (3, [false, true, true, false, false, false, true, true, false, true, false, true, true, true]),
  (3, [false, true, true, false, false, false, true, true, false, true, true, false, false, false]),
  (3, [false, true, true, false, false, false, true, true, false, true, true, false, false, true]),
  (3, [false, true, true, false, false, false, true, true, false, true, true, false, true, true]),
  (3, [false, true, true, false, false, false, true, true, false, true, true, true, false, false]),
  (3, [false, true, true, false, false, false, true, true, false, true, true, true, false, true]),
  (3, [false, true, true, false, false, false, true, true, false, true, true, true, true, false]),
  (3, [false, true, true, false, false, false, true, true, false, true, true, true, true, true]),
  (3, [false, true, true, false, false, false, true, true, true, false, false, false, false, false]),
  (3, [false, true, true, false, false, false, true, true, true, false, false, false, false, true]),
  (3, [false, true, true, false, false, false, true, true, true, false, false, false, true, true]),
  (3, [false, true, true, false, false, false, true, true, true, false, false, true, true, false]),
  (3, [false, true, true, false, false, false, true, true, true, false, false, true, true, true]),
  (3, [false, true, true, false, false, false, true, true, true, true, true, false, true, false]),
  (3, [false, true, true, false, false, false, true, true, true, true, true, false, true, true]),
  (3, [false, true, true, false, false, false, true, true, true, true, true, true, false, false]),
  (3, [false, true, true, false, false, false, true, true, true, true, true, true, false, true]),
  (3, [false, true, true, false, false, false, true, true, true, true, true, true, true, true]),
  (3, [true, false, true, true, false, true, false, true, false, false, true, false, false, true]),
  (3, [true, false, true, true, false, true, false, true, false, false, true, false, true, false]),
  (3, [true, false, true, true, false, true, false, true, false, false, true, false, true, true]),
  (3, [true, false, true, true, false, true, false, true, false, true, false, false, false, false]),
  (3, [true, false, true, true, false, true, false, true, false, true, false, false, false, true]),
  (3, [true, false, true, true, false, true, false, true, false, true, false, false, true, true]),
  (3, [true, false, true, true, false, true, false, true, false, true, false, true, true, false]),
  (3, [true, false, true, true, false, true, false, true, false, true, true, true, false, false]),
  (3, [true, false, true, true, false, true, false, true, false, true, true, true, false, true]),
  (3, [true, false, true, true, false, true, false, true, true, false, false, false, false, false]),
  (3, [true, false, true, true, false, true, false, true, true, false, false, false, false, true]),
  (3, [true, false, true, true, false, true, false, true, true, false, false, false, true, true]),
  (3, [true, false, true, true, false, true, false, true, true, false, false, true, true, false]),
  (3, [true, false, true, true, false, true, false, true, true, false, false, true, true, true]),
  (3, [true, false, true, true, false, true, false, true, true, false, true, true, false, false]),
  (3, [true, false, true, true, false, true, false, true, true, false, true, true, false, true]),
  (3, [true, false, true, true, false, true, false, true, true, false, true, true, true, false]),
  (3, [true, false, true, true, false, true, false, true, true, false, true, true, true, true]),
  (3, [true, false, true, true, false, true, false, true, true, true, true, false, false, false]),
  (3, [true, false, true, true, false, true, false, true, true, true, true, false, false, true]),
  (3, [true, false, true, true, false, true, false, true, true, true, true, false, true, false]),
  (3, [true, false, true, true, false, true, false, true, true, true, true, true, false, false]),
  (3, [true, false, true, true, false, true, false, true, true, true, true, true, false, true]),
  (3, [true, false, true, true, false, true, false, true, true, true, true, true, true, true])
]

theorem pure_not_in_S0001 : ∀ φ, φ < 4 → (φ, etherRow 6 ((φ + 0) % 4) 16) ∉ S0001 := by decide
theorem pure_not_in_S0011 : ∀ φ, φ < 4 → (φ, etherRow 0 ((φ + 0) % 4) 16) ∉ S0011 := by decide
theorem pure_not_in_S0111 : ∀ φ, φ < 4 → (φ, etherRow 2 ((φ + 2) % 4) 14) ∉ S0111 := by decide

def ws0 : List Bool := [false, true, false, false, false, false, false, true, false, false, false, false, false]
def ws2 : List Bool := [false, true, false, true, false, true, true, false, false, false, false, false, false]
theorem ws0_mem : (0 % 4, ws0) ∈ wallStates := by decide
theorem ws2_mem : (2 % 4, ws2) ∈ wallStates := by decide

/-- The node of the strip relaxation of width `b` at time `t` (center column `w^∞`, phase `t % 4`). -/
def node (w : List Bool) (x : Nat → Bool) (t b : Nat) : Nat × List Bool :=
  (t % 4, rowOf (drv (wordAt w) x) t 0 b)

theorem never_enters_aux (w : List Bool) (j0 s k b : Nat) (hal : aligned w j0 s = true)
    (hk : (j0 + k) % 7 = 2) (hb : b ≤ k) (ws : List Bool) (hws : (s % 4, ws) ∈ wallStates)
    (hlen : ws.length = 13) (S : List (Nat × List Bool))
    (hS : ∀ φ, φ < 4 → (φ, etherRow j0 ((φ + s) % 4) b) ∉ S) (t : Nat) :
    node w (config j0 s k ws) t b ∉ S := by
  unfold node
  rw [config_pure_ether w j0 s k b hal hk hb ws hws hlen t]
  have e : (t + s) % 4 = (t % 4 + s) % 4 := by omega
  rw [e]
  exact hS (t % 4) (Nat.mod_lt _ (by decide))

/-- **Refutation of fixed-trap entry, w = 0001.** The finite right half `x` (ether columns 1..17,
a wall state in columns 18..30, white beyond) driven by `0001^∞` never enters the trap `S0001`
(width 16). -/
theorem never_enters_S0001 (t : Nat) : node w0001 (config 6 0 17 ws0) t 16 ∉ S0001 :=
  never_enters_aux w0001 6 0 17 16 aligned_0001_6 (by decide) (by decide) ws0 ws0_mem rfl S0001
    pure_not_in_S0001 t

theorem never_enters_S0011 (t : Nat) : node w0011 (config 0 0 16 ws0) t 16 ∉ S0011 :=
  never_enters_aux w0011 0 0 16 16 aligned_0011_0 (by decide) (by decide) ws0 ws0_mem rfl S0011
    pure_not_in_S0011 t

theorem never_enters_S0111 (t : Nat) : node w0111 (config 2 2 14 ws2) t 14 ∉ S0111 :=
  never_enters_aux w0111 2 2 14 14 aligned_0111_2 (by decide) (by decide) ws2 ws2_mem rfl S0111
    pure_not_in_S0111 t


/-! ### The missing piece as a proposition, and why it suffices -/

/-- From time `T` on, the true right half is the driven right half started from the true row at
`T`. -/
theorem cell_eq_drv (T : Nat) : ∀ (t p : Nat),
    cell (T + t) (p : Int) = drv (fun t => cell (T + t) 0) (fun p => cell T (p : Int)) t p
  | 0, 0 => by simp [drv]
  | 0, p + 1 => by simp [drv]
  | t + 1, 0 => rfl
  | t + 1, q + 1 => by
    rw [show T + (t + 1) = (T + t) + 1 by omega]
    show rule (cell (T + t) (((q + 1 : Nat) : Int) - 1)) (cell (T + t) ((q + 1 : Nat) : Int))
        (cell (T + t) (((q + 1 : Nat) : Int) + 1)) = rule (drv _ _ t q) (drv _ _ t (q + 1)) (drv _ _ t (q + 2))
    rw [← cell_eq_drv T t q, ← cell_eq_drv T t (q + 1), ← cell_eq_drv T t (q + 2)]
    have a1 : ((q + 1 : Nat) : Int) - 1 = ((q : Nat) : Int) := by omega
    have a2 : ((q + 1 : Nat) : Int) + 1 = ((q + 2 : Nat) : Int) := by omega
    rw [a1, a2]

/-- The ether-and-wall family condition for an evolution `F` (columns `p ≥ 0`) at time `t1`, with
ether phase `t1 + s`. -/
def InFamily (F : Nat → Nat → Bool) (j0 s t1 : Nat) : Prop :=
  ∃ k, (j0 + k) % 7 = 2 ∧ (∀ p, 1 ≤ p → p ≤ k → F t1 p = ether (j0 + p) (t1 + s)) ∧
    ((t1 + s) % 4, rowOf F t1 k 13) ∈ wallStates

/-- **Absorption conjecture** (open) for a word `w` with a list `A` of ether alignments
`(j0, s)`: every finitely supported right half driven by `w^∞` (any phase `φ`) eventually enters
the ether-and-wall family for one of the alignments. -/
def Absorption (w : List Bool) (A : List (Nat × Nat)) : Prop :=
  ∀ (x : Nat → Bool) (n : Nat), (∀ p, n < p → x p = false) → ∀ φ : Nat,
    ∃ a ∈ A, ∃ t1, InFamily (drv (fun t => wordAt w (t + φ)) x) a.1 (a.2 + φ) t1

/-- **The absorption conjecture for `w` excludes `w^∞` as a tail of the center column.** -/
theorem absorption_excludes (w : List Bool) (A : List (Nat × Nat))
    (hal : ∀ a ∈ A, aligned w a.1 a.2 = true)
    (hA : Absorption w A) : ¬ ∃ T, ∀ t, T ≤ t → cell t 0 = wordAt w (t - T) := by
  rintro ⟨T, hT⟩
  have hc : (fun t => cell (T + t) 0) = (fun t => wordAt w (t + 0)) := by
    funext t; rw [hT (T + t) (by omega)]; congr 1; omega
  have hfin : ∀ p, T < p → (fun p : Nat => cell T (p : Int)) p = false :=
    fun p hp => Rule30Diagonals.cell_eq_false_of_gt T p (by omega)
  obtain ⟨⟨j0, s⟩, ha, t1, k, hk, hE, hW⟩ := hA (fun p => cell T (p : Int)) T hfin 0
  have hal' := hal (j0, s) ha
  rw [← hc] at hE hW
  have hrow : rowOf (drv (fun t => cell (T + t) 0) (fun p => cell T (p : Int))) t1 k 13 =
      rowOf trueRight (T + t1) k 13 := by
    unfold rowOf
    apply seg_congr
    intro i _
    rw [← cell_eq_drv T t1 (k + i + 1)]
    rfl
  rw [hrow] at hW
  refine ether_wall_trap T (T + t1) j0 s k hk (fun t ht => ?_) (by omega) (fun p hp1 hpk => ?_) ?_
  · rw [hT t ht, aligned_spec hal']
  · rw [cell_eq_drv T t1 p, hE p hp1 hpk]
    exact ether_congr rfl (by omega)
  · rw [show T + t1 - T + s = t1 + (s + 0) by omega]; exact hW

/-- The alignments of the three period-4 words (all of them are checked by `aligned_*`). -/
def A0001 : List (Nat × Nat) := [(5, 0), (6, 0)]
def A0011 : List (Nat × Nat) := [(0, 0), (1, 3), (4, 0)]
def A0111 : List (Nat × Nat) := [(2, 2)]

theorem A0001_ok : ∀ a ∈ A0001, aligned w0001 a.1 a.2 = true := by decide
theorem A0011_ok : ∀ a ∈ A0011, aligned w0011 a.1 a.2 = true := by decide
theorem A0111_ok : ∀ a ∈ A0111, aligned w0111 a.1 a.2 = true := by decide

/-- **Least period 4 from the three absorption conjectures.** If absorption holds for `0001`, `0011`
and `0111`, the center column is not eventually equal to any rotation of these words, with any
transient (a rotation of `w` from time `T` is `w` itself from a later time). -/
theorem least_period_four_of_absorption (h1 : Absorption w0001 A0001) (h2 : Absorption w0011 A0011)
    (h3 : Absorption w0111 A0111) :
    (¬ ∃ T, ∀ t, T ≤ t → cell t 0 = wordAt w0001 (t - T)) ∧
    (¬ ∃ T, ∀ t, T ≤ t → cell t 0 = wordAt w0011 (t - T)) ∧
    (¬ ∃ T, ∀ t, T ≤ t → cell t 0 = wordAt w0111 (t - T)) :=
  ⟨absorption_excludes w0001 A0001 A0001_ok h1, absorption_excludes w0011 A0011 A0011_ok h2,
    absorption_excludes w0111 A0111 A0111_ok h3⟩

/-! ### A weaker sufficient condition: `Lock` -/

/-- **Lock** (open) for a word `w`: every finitely supported right half driven by `w^∞` has
column `1` eventually periodic, with a period `4 Q`, at the times where the driver is white, or
some column `q ≥ 1` eventually periodic. -/
def Lock (w : List Bool) : Prop :=
  ∀ (x : Nat → Bool) (n : Nat), (∀ p, n < p → x p = false) →
    (∃ N Q, 0 < Q ∧ ∀ t, N ≤ t → wordAt w t = false →
        drv (wordAt w) x (t + 4 * Q) 1 = drv (wordAt w) x t 1) ∨
    (∃ q, 1 ≤ q ∧ EventuallyPeriodic (fun t => drv (wordAt w) x t q))

/-- `wordAt w` has period `4`. -/
theorem wordAt_period (w : List Bool) (t m : Nat) : wordAt w (t + 4 * m) = wordAt w t := by
  unfold wordAt; rw [Nat.add_mul_mod_self_left]

/-- **`Lock w` excludes `w^∞` as a tail of the center column**, for every transient. From the
time `T` where the tail starts, the true right half is the right half driven by `w^∞`
(`cell_eq_drv`), and it is finitely supported. If its column `1` is eventually periodic at the
white times of the center, masked Jen (`Rule30MaskedJen.masked_jen`) gives a contradiction; if some
column `q ≥ 1` is eventually periodic, Jen (`Rule30Jen.jen`) does, since the center is periodic. -/
theorem lock_excludes (w : List Bool) (hL : Lock w) :
    ¬ ∃ T, ∀ t, T ≤ t → cell t 0 = wordAt w (t - T) := by
  rintro ⟨T, hT⟩
  have hc : (fun t => cell (T + t) 0) = wordAt w := by
    funext t; rw [hT (T + t) (by omega)]; congr 1; omega
  have hfin : ∀ p, T < p → (fun p : Nat => cell T (p : Int)) p = false :=
    fun p hp => Rule30Diagonals.cell_eq_false_of_gt T p (by omega)
  have hcell : ∀ t q : Nat,
      cell (T + t) (q : Int) = drv (wordAt w) (fun p => cell T (p : Int)) t q := by
    intro t q; rw [cell_eq_drv T t q, hc]
  have hper0 : ∀ t, T ≤ t → ∀ m, cell (t + 4 * m) 0 = cell t 0 := by
    intro t ht m
    rw [hT t ht, hT (t + 4 * m) (by omega), show t + 4 * m - T = (t - T) + 4 * m by omega,
      wordAt_period]
  rcases hL _ T hfin with ⟨N, Q, hQ, hN⟩ | ⟨q, hq, hqp⟩
  · refine Rule30MaskedJen.masked_jen 0 (T := T + N) (P := 4 * Q) (by omega)
      (fun t ht => hper0 t (by omega) Q) ?_
    intro t ht hw
    obtain ⟨u, rfl⟩ : ∃ u, t = T + u := ⟨t - T, by omega⟩
    have hwu : wordAt w u = false := by
      rw [hT (T + u) (by omega), show T + u - T = u by omega] at hw; exact hw
    have e1 := hcell (u + 4 * Q) 1
    have e2 := hcell u 1
    rw [show T + (u + 4 * Q) = T + u + 4 * Q by omega] at e1
    show cell (T + u + 4 * Q) ((1 : Nat) : Int) = cell (T + u) ((1 : Nat) : Int)
    rw [e1, e2]
    exact hN u (by omega) hwu
  · apply jen 0 (q : Int) (by omega)
    refine ⟨⟨T, 4, by decide, fun t ht => by simpa using hper0 t ht 1⟩, ?_⟩
    obtain ⟨N, P, hP, hNP⟩ := hqp
    refine ⟨T + N, P, hP, fun t ht => ?_⟩
    obtain ⟨u, rfl⟩ : ∃ u, t = T + u := ⟨t - T, by omega⟩
    show cell (T + u + P) (q : Int) = cell (T + u) (q : Int)
    rw [show T + u + P = T + (u + P) by omega, hcell, hcell]
    exact hNP u (by omega)

/-- **`Absorption` implies `Lock`.** For a list `A` of genuine alignments of `w`, absorption into
the ether-and-wall family gives the first alternative of `Lock w` with period `4`: once the family
is entered, column `1` carries the ether column `j0 + 1` at the white times of the driver (the
first wall cell when `k = 0`, by `wall_facts`), by `trap_invariant`. -/
theorem lock_of_absorption (w : List Bool) (A : List (Nat × Nat))
    (hal : ∀ a ∈ A, aligned w a.1 a.2 = true) (hA : Absorption w A) : Lock w := by
  intro x n hx
  left
  obtain ⟨⟨j0, s⟩, ha, t1, k, hk, hE, hW⟩ := hA x n hx 0
  have hal' := hal (j0, s) ha
  have hcw : (fun t => wordAt w (t + 0)) = wordAt w := rfl
  rw [hcw] at hE hW
  have hF := drv_isR30 (wordAt w) x
  have h0 : ∀ t, t1 ≤ t → drv (wordAt w) x t 0 = ether j0 (t + s) := by
    intro t _; rw [drv_col0, aligned_spec hal']
  have inv := trap_invariant hF j0 s k t1 hk h0 hE hW
  have key : ∀ t, t1 ≤ t → wordAt w t = false →
      drv (wordAt w) x t 1 = ether (j0 + 1) (t + s) := by
    intro t ht hw
    obtain ⟨hE', hW'⟩ := inv (t - t1)
    rw [show t1 + (t - t1) = t by omega] at hE' hW'
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      have hw2 : ether 2 ((t + s) % 4) = false := by
        have e : drv (wordAt w) x t 0 = ether (j0 + 0) (t + s) := hE' 0 (Nat.le_refl 0)
        rw [drv_col0, hw] at e
        rw [e]; exact ether_congr (by omega) (by omega)
      have hhead := (wall_facts hW').1 hw2
      rw [rowOf_head] at hhead
      have e1 : drv (wordAt w) x t 1 = ether 3 ((t + s) % 4) := hhead
      rw [e1]; exact ether_congr (by omega) (by omega)
    · exact hE' 1 hk0
  refine ⟨t1, 1, by decide, fun t ht hw => ?_⟩
  have hw4 : wordAt w (t + 4 * 1) = false := by rw [wordAt_period]; exact hw
  rw [key (t + 4 * 1) (by omega) hw4, key t ht hw]
  exact ether_congr rfl (by omega)

/-- **Least period 4 from the three locks.** If `Lock` holds for `0001`, `0011` and `0111`, the
center column is not eventually equal to any rotation of these words, with any transient. By
`lock_of_absorption` the hypotheses are weaker than those of `least_period_four_of_absorption`. -/
theorem least_period_four_of_lock (h1 : Lock w0001) (h2 : Lock w0011) (h3 : Lock w0111) :
    (¬ ∃ T, ∀ t, T ≤ t → cell t 0 = wordAt w0001 (t - T)) ∧
    (¬ ∃ T, ∀ t, T ≤ t → cell t 0 = wordAt w0011 (t - T)) ∧
    (¬ ∃ T, ∀ t, T ≤ t → cell t 0 = wordAt w0111 (t - T)) :=
  ⟨lock_excludes _ h1, lock_excludes _ h2, lock_excludes _ h3⟩

end Rule30Ether
end Ruliology.CellularAutomata
