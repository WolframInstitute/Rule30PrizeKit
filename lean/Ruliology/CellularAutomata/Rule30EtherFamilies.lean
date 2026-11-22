module

public import Ruliology.CellularAutomata.Rule30Ether
public import Ruliology.CellularAutomata.Rule30PeriodTwoSideways
public import Ruliology.CellularAutomata.Rule30GateTrap

/-!
# Two infinite families of right halves locked into period 2 by the ether-and-wall trap

Drive a right half `R` with the alternating column (`Rule30PeriodTwoCoupled.altCol`). Column `1` at the white ticks
is `Rule30PeriodTwoSideways.u R`, and the sideways row `Psi R` has infinitely many black cells whenever `u R` is
eventually periodic (`Rule30PeriodTwoSideways.not_finSupp_Psi_of_eventuallyPeriodic`). Take `R31`, black at cells
`1..5`, and `R495`, black at cells `1..4` and `6..9` (the row of `R31` at time `4`).

* `CQ01_prefix31`, `CQ01_prefix495`: every right half that agrees with `R31` on cells `1..28`, or with `R495` on
  cells `1..24`, whatever its later cells, has `u R q = (q % 2 == 1)` for every `q`, so `Psi R` has infinitely many
  black cells.
* `Psi_prefix31`, `Psi_prefix495`, `Psi_eq`: all of them have one sideways row, that of `R31`.
* `CQ01_fam`, `fam_injective`: the right halves `fam n`, `R31` with one more black cell at `29 + n`, are finitely
  supported, pairwise distinct, and satisfy `CQ01`.
* `not_move_equivalent`: `R31` and `R495` are not joined by the right-end moves (the inverses of the terminal
  rewrites `011 -> 01` and `101 -> 11`, with the black wall counted as a cell left of cell `1`). So the moves do not
  account for every collision of `R ↦ Psi R`.
* `never_enters_gate_trap31`, `never_enters_gate_trap495`: no member of either family has its window in the
  829-window trap of `Rule30GateTrap` at any odd time.

Column `1` of every member locks into period `2`, beside the locks of periods `5` and `7` in
`Rule30SidewaysLocks`.

**Method.** Column `0` is the ether column `B4` (index `3`) at phase `t + 3` (`altCol_ether`). At time `9` for `R31`,
and `5` for `R495`, columns `1..6` carry the ether at that phase and columns `7..19` form one of the wall states of
`Rule30Ether` (decided). `Rule30Ether.trap_invariant` then keeps columns `1..6` in the ether for ever, so column `1`
is the ether column `B5`, which at the white ticks is the parity of the step. Both entries lie within columns `1..19`,
inside the cones of `28` and `24` cells, so radius-one locality (`drv_prefix_agree`) carries them to every member of
the families. In the gate trap a black cell of `u R` is followed by the next at distance `3` or `5`
(`Rule30GateTrap.gaps_of_entry`), and here the distance is `2`. The moves act on reversed cell lists; every chain has
a computable root that the moves preserve, and the two roots differ. Core Lean has no `Relation.EqvGen`, so the
equivalence closure `EqvGen` is defined here, with the same four constructors.

**Credit.** That such right halves never enter the gate trap is from h3artfield's Lean-verified submission
`R30-20261122-66c410`, for the right halves that agree with `175` (cells `1, 2, 3, 4, 6, 8`) on cells `1..28`. The
proof here follows that entry's.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30EtherFamilies
open Rule30Jen (EventuallyPeriodic)
open Rule30ZeroBoundary (FinSupp)
open Rule30Ether (ether ether_congr trap_invariant rowOf wallStates drv drv_isR30 drv_col0 drv_init seg_congr)
open Rule30PeriodTwoCoupled (altCol)
open Rule30PeriodTwoSideways (u Psi not_finSupp_Psi_of_eventuallyPeriodic)

/-- A finite right half from its cells `1, 2, ...` (column `p` is entry `p - 1`; column `0` is unused). -/
def ofCells (w : List Bool) (p : Nat) : Bool := 1 ≤ p && w.getD (p - 1) false

/-- The cells of the two right halves: black at `1..5`, and black at `1..4, 6..9`. -/
def cells31 : List Bool := [true, true, true, true, true]
def cells495 : List Bool := [true, true, true, true, false, true, true, true, true]

def R31 : Nat → Bool := ofCells cells31
def R495 : Nat → Bool := ofCells cells495

/-- The alternating column is the ether column `B4` (index 3) at phase `t + 3`. -/
theorem altCol_ether (t : Nat) : altCol t = ether 3 (t + 3) := by
  have e : ether 3 (t + 3) = ether 3 (t % 4 + 3) := ether_congr rfl (by omega)
  rw [e]
  rcases (by omega : t % 4 = 0 ∨ t % 4 = 1 ∨ t % 4 = 2 ∨ t % 4 = 3) with h | h | h | h <;>
    · rw [h]; simp [altCol, show t % 2 = t % 4 % 2 by omega, h]; decide

/-- Ether column `B5` (index 4) at phase `2 q + 4` is the parity of `q`. -/
theorem ether4_parity (q : Nat) : ether 4 (2 * q + 4) = (q % 2 == 1) := by
  have e : ether 4 (2 * q + 4) = ether 4 (2 * (q % 2)) := ether_congr rfl (by omega)
  rw [e]
  rcases (by omega : q % 2 = 0 ∨ q % 2 = 1) with h | h <;> · rw [h]; decide

theorem trap31_E : ∀ p, 1 ≤ p → p ≤ 6 → drv altCol R31 9 p = ether (3 + p) (9 + 3) := by
  intro p h1 h2
  rcases (by omega : p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6) with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem trap31_W : ((9 + 3) % 4, rowOf (drv altCol R31) 9 6 13) ∈ wallStates := by decide

theorem col1_R31 : ∀ t, 9 ≤ t → drv altCol R31 t 1 = ether 4 (t + 3) := by
  have inv := trap_invariant (drv_isR30 altCol R31) 3 3 6 9 (by decide)
    (fun t _ => by rw [drv_col0]; exact altCol_ether t) trap31_E trap31_W
  intro t ht
  have h := (inv (t - 9)).1 1 (by decide)
  rw [show 9 + (t - 9) = t by omega] at h
  rw [h]

theorem u_R31 (q : Nat) : u R31 q = (q % 2 == 1) := by
  show drv altCol R31 (2 * q + 1) 1 = _
  rcases (by omega : q < 4 ∨ 4 ≤ q) with h | h
  · rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3) with rfl | rfl | rfl | rfl <;> decide
  · rw [col1_R31 (2 * q + 1) (by omega), show 2 * q + 1 + 3 = 2 * q + 4 by omega]
    exact ether4_parity q

theorem trap495_E : ∀ p, 1 ≤ p → p ≤ 6 → drv altCol R495 5 p = ether (3 + p) (5 + 3) := by
  intro p h1 h2
  rcases (by omega : p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6) with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem trap495_W : ((5 + 3) % 4, rowOf (drv altCol R495) 5 6 13) ∈ wallStates := by decide

theorem col1_R495 : ∀ t, 5 ≤ t → drv altCol R495 t 1 = ether 4 (t + 3) := by
  have inv := trap_invariant (drv_isR30 altCol R495) 3 3 6 5 (by decide)
    (fun t _ => by rw [drv_col0]; exact altCol_ether t) trap495_E trap495_W
  intro t ht
  have h := (inv (t - 5)).1 1 (by decide)
  rw [show 5 + (t - 5) = t by omega] at h
  rw [h]

theorem u_R495 (q : Nat) : u R495 q = (q % 2 == 1) := by
  show drv altCol R495 (2 * q + 1) 1 = _
  rcases (by omega : q < 2 ∨ 2 ≤ q) with h | h
  · rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl <;> decide
  · rw [col1_R495 (2 * q + 1) (by omega), show 2 * q + 1 + 3 = 2 * q + 4 by omega]
    exact ether4_parity q

/-- **The two visible columns coincide**: `u R31 = u R495` (both are the parity of the step). -/
theorem u_eq : u R31 = u R495 := funext fun q => by rw [u_R31, u_R495]

/-- **Equal sideways rows** for two different finite right halves. -/
theorem Psi_eq : Psi R31 = Psi R495 := by
  unfold Psi; rw [u_eq]

theorem R31_ne_R495 : R31 ≠ R495 := fun h => by
  have := congrFun h 6; revert this; decide

theorem u_R31_periodic : EventuallyPeriodic (u R31) :=
  ⟨0, 2, by decide, fun t _ => by rw [u_R31, u_R31]; simp⟩

theorem u_R495_periodic : EventuallyPeriodic (u R495) :=
  ⟨0, 2, by decide, fun t _ => by rw [u_R495, u_R495]; simp⟩

/-- **CQ01 for `R31`**: `Psi R31` has infinitely many black cells. -/
theorem CQ01_R31 : ¬ FinSupp (Psi R31) := not_finSupp_Psi_of_eventuallyPeriodic R31 u_R31_periodic

/-- **CQ01 for `R495`**. -/
theorem CQ01_R495 : ¬ FinSupp (Psi R495) := not_finSupp_Psi_of_eventuallyPeriodic R495 u_R495_periodic

/-! ## The two right halves are not related by the right-end moves

The right-end move `S` (the inverse of the kit's terminal rewrites `011 -> 01` and `101 -> 11`, with the black
wall counted as a black cell left of cell `1`) acts on a nonempty right half written from its LAST black cell leftward:
`1 0 r -> 1 1 0 r`, `1 1 r -> 1 0 1 r`, and the single cell `1 -> 1 0` (the wall black at time `0`). Its inverse `P` undoes exactly
these three shapes, so `P (S a) = a`, and the root of the chain through `a` is invariant under moves. -/

/-- The right-end move on a reversed cell list (head = last cell); the identity off its domain. -/
def S : List Bool → List Bool
  | true :: false :: r => true :: true :: false :: r
  | true :: true :: r => true :: false :: true :: r
  | [true] => [true, false]
  | w => w

/-- The inverse of `S` on its image. -/
def P : List Bool → Option (List Bool)
  | true :: true :: false :: r => some (true :: false :: r)
  | true :: false :: true :: r => some (true :: true :: r)
  | [true, false] => some [true]
  | _ => none

/-- A nonempty right half, reversed: its head is its last black cell. -/
def Valid (w : List Bool) : Prop := w.head? = some true

theorem P_S (a : List Bool) (h : Valid a) : P (S a) = some a := by
  match a, h with
  | true :: false :: r, _ => rfl
  | true :: true :: r, _ => rfl
  | [true], _ => rfl

theorem S_length (a : List Bool) (h : Valid a) : (S a).length = a.length + 1 := by
  match a, h with
  | true :: false :: r, _ => rfl
  | true :: true :: r, _ => rfl
  | [true], _ => rfl

/-- The root of the chain: apply `P` while it applies (fuel: the length, which `P` lowers by one). -/
def rootF : Nat → List Bool → List Bool
  | 0, w => w
  | n + 1, w => match P w with
    | some v => rootF n v
    | none => w

def root (w : List Bool) : List Bool := rootF w.length w

theorem root_S (a : List Bool) (h : Valid a) : root (S a) = root a := by
  unfold root; rw [S_length a h]; show (match P (S a) with | some v => rootF a.length v | none => S a) = _
  rw [P_S a h]

universe u

/-- The equivalence closure of a relation (as Mathlib's `Relation.EqvGen`, which core Lean lacks). -/
inductive EqvGen {α : Type u} (r : α → α → Prop) : α → α → Prop
  | rel : ∀ x y, r x y → EqvGen r x y
  | refl : ∀ x, EqvGen r x x
  | symm : ∀ x y, EqvGen r x y → EqvGen r y x
  | trans : ∀ x y z, EqvGen r x y → EqvGen r y z → EqvGen r x z

/-- One move step: `b = S a` with `a` a nonempty right half. -/
def Move (a b : List Bool) : Prop := Valid a ∧ b = S a

theorem root_of_eqv {a b : List Bool} (h : EqvGen Move a b) : root a = root b := by
  induction h with
  | rel x y hxy => obtain ⟨hv, rfl⟩ := hxy; exact (root_S x hv).symm
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-- **Not move-equivalent**: no chain of right-end moves (either direction) joins the two right halves. -/
theorem not_move_equivalent : ¬ EqvGen Move cells31.reverse cells495.reverse := fun h => by
  have := root_of_eqv h; revert this; decide

/-! ## Infinite families: every right half agreeing with `R31` on cells `1..28`, or with `R495` on cells `1..24`

Radius-one locality: under the common driver, two right halves that agree on cells `1..M` agree at `(t, p)` whenever
`p + t ≤ M`. The trap entry of `R31` (time `9`, columns `1..19`; `19 + 9 = 28`) and of `R495` (time `5`; `19 + 5 = 24`) lies
inside that cone, and so do the early visible samples, so the whole visible column transfers; after the entry the trap
invariant allows any later tail, finite or not. -/

/-- Two right halves agree on cells `1..M`. -/
def AgreesPrefix (M : Nat) (R S : Nat → Bool) : Prop :=
  ∀ p, 1 ≤ p → p ≤ M → R p = S p

/-- **Locality** of the driven right half: agreement on cells `1..M` gives agreement at `(t, p)` when `p + t ≤ M`. -/
theorem drv_prefix_agree (c x y : Nat → Bool) (M : Nat) (h : AgreesPrefix M x y) :
    ∀ t p, p + t ≤ M → drv c x t p = drv c y t p
  | 0, 0, _ => by rw [drv_col0, drv_col0]
  | 0, p + 1, hp => by rw [drv_init c x (p + 1) (by omega), drv_init c y (p + 1) (by omega)]; exact h (p + 1) (by omega) (by omega)
  | t + 1, 0, _ => by rw [drv_col0, drv_col0]
  | t + 1, p + 1, hp => by
    rw [drv_isR30 c x t p, drv_isR30 c y t p, drv_prefix_agree c x y M h t p (by omega),
      drv_prefix_agree c x y M h t (p + 1) (by omega), drv_prefix_agree c x y M h t (p + 2) (by omega)]

/-- **The first family**: every right half agreeing with `R31` on cells `1..28` has the visible column of `R31`. -/
theorem u_prefix31 (R : Nat → Bool) (h : AgreesPrefix 28 R R31) : ∀ q, u R q = (q % 2 == 1) := by
  intro q
  have loc := drv_prefix_agree altCol R R31 28 h
  have hE : ∀ p, 1 ≤ p → p ≤ 6 → drv altCol R 9 p = ether (3 + p) (9 + 3) := fun p h1 h2 => by
    rw [loc 9 p (by omega)]; exact trap31_E p h1 h2
  have hW : ((9 + 3) % 4, rowOf (drv altCol R) 9 6 13) ∈ wallStates := by
    have e : rowOf (drv altCol R) 9 6 13 = rowOf (drv altCol R31) 9 6 13 :=
      seg_congr 13 _ _ fun i hi => loc 9 (6 + i + 1) (by omega)
    rw [e]; exact trap31_W
  have inv := trap_invariant (drv_isR30 altCol R) 3 3 6 9 (by decide)
    (fun t _ => by rw [drv_col0]; exact altCol_ether t) hE hW
  show drv altCol R (2 * q + 1) 1 = _
  rcases (by omega : q < 4 ∨ 4 ≤ q) with hq | hq
  · rw [loc (2 * q + 1) 1 (by omega)]; exact u_R31 q
  · have h1 := (inv (2 * q + 1 - 9)).1 1 (by decide)
    rw [show 9 + (2 * q + 1 - 9) = 2 * q + 1 by omega] at h1
    rw [h1, show 2 * q + 1 + 3 = 2 * q + 4 by omega]; exact ether4_parity q

/-- **The second family**: every right half agreeing with `R495` on cells `1..24` has the visible column of `R495`. -/
theorem u_prefix495 (R : Nat → Bool) (h : AgreesPrefix 24 R R495) : ∀ q, u R q = (q % 2 == 1) := by
  intro q
  have loc := drv_prefix_agree altCol R R495 24 h
  have hE : ∀ p, 1 ≤ p → p ≤ 6 → drv altCol R 5 p = ether (3 + p) (5 + 3) := fun p h1 h2 => by
    rw [loc 5 p (by omega)]; exact trap495_E p h1 h2
  have hW : ((5 + 3) % 4, rowOf (drv altCol R) 5 6 13) ∈ wallStates := by
    have e : rowOf (drv altCol R) 5 6 13 = rowOf (drv altCol R495) 5 6 13 :=
      seg_congr 13 _ _ fun i hi => loc 5 (6 + i + 1) (by omega)
    rw [e]; exact trap495_W
  have inv := trap_invariant (drv_isR30 altCol R) 3 3 6 5 (by decide)
    (fun t _ => by rw [drv_col0]; exact altCol_ether t) hE hW
  show drv altCol R (2 * q + 1) 1 = _
  rcases (by omega : q < 2 ∨ 2 ≤ q) with hq | hq
  · rw [loc (2 * q + 1) 1 (by omega)]; exact u_R495 q
  · have h1 := (inv (2 * q + 1 - 5)).1 1 (by decide)
    rw [show 5 + (2 * q + 1 - 5) = 2 * q + 1 by omega] at h1
    rw [h1, show 2 * q + 1 + 3 = 2 * q + 4 by omega]; exact ether4_parity q

/-- **Equal sideways rows across the first family.** -/
theorem Psi_prefix31 (R : Nat → Bool) (h : AgreesPrefix 28 R R31) : Psi R = Psi R31 := by
  unfold Psi; rw [show u R = u R31 from funext fun q => by rw [u_prefix31 R h, u_R31]]

/-- **Equal sideways rows across the second family.** -/
theorem Psi_prefix495 (R : Nat → Bool) (h : AgreesPrefix 24 R R495) : Psi R = Psi R495 := by
  unfold Psi; rw [show u R = u R495 from funext fun q => by rw [u_prefix495 R h, u_R495]]

/-- **CQ01 across the first family**: `Psi R` has infinitely many black cells for every `R` agreeing with `R31` on `1..28`. -/
theorem CQ01_prefix31 (R : Nat → Bool) (h : AgreesPrefix 28 R R31) : ¬ FinSupp (Psi R) :=
  not_finSupp_Psi_of_eventuallyPeriodic R ⟨0, 2, by decide, fun t _ => by rw [u_prefix31 R h, u_prefix31 R h]; simp⟩

/-- **CQ01 across the second family.** -/
theorem CQ01_prefix495 (R : Nat → Bool) (h : AgreesPrefix 24 R R495) : ¬ FinSupp (Psi R) :=
  not_finSupp_Psi_of_eventuallyPeriodic R ⟨0, 2, by decide, fun t _ => by rw [u_prefix495 R h, u_prefix495 R h]; simp⟩

/-- An explicit infinite family of FINITE right halves in the first class: `R31` with one more black cell at `29 + n`. -/
def fam (n : Nat) (p : Nat) : Bool := R31 p || p == 29 + n

theorem R31_far (p : Nat) (hp : 5 < p) : R31 p = false := by
  unfold R31 ofCells
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [cells31]; omega)]; simp

theorem fam_agree (n : Nat) : AgreesPrefix 28 (fam n) R31 := fun p _ hp => by
  simp only [fam, show (p == 29 + n) = false from by simp; omega, Bool.or_false]

theorem fam_finSupp (n : Nat) : FinSupp (fam n) :=
  ⟨29 + n, fun k hk => by simp only [fam, R31_far k (by omega), show (k == 29 + n) = false from by simp; omega, Bool.or_false]⟩

theorem fam_injective : Function.Injective fam := fun m n hmn => by
  have h := congrFun hmn (29 + n)
  simp [fam, R31_far (29 + n) (by omega)] at h
  omega

/-- **Infinitely many finite CQ01 instances**: the right halves `fam n` are pairwise distinct, each finitely supported, and
each satisfies `CQ01` with the sideways row of `R31`. -/
theorem CQ01_fam (n : Nat) : FinSupp (fam n) ∧ ¬ FinSupp (Psi (fam n)) ∧ Psi (fam n) = Psi R31 :=
  ⟨fam_finSupp n, CQ01_prefix31 (fam n) (fam_agree n), Psi_prefix31 (fam n) (fam_agree n)⟩


/-! ## Outside the gate trap

In the 829-window trap of `Rule30GateTrap`, a black cell of `u R` is followed by the next one at distance `3` or `5`
(`Rule30GateTrap.gaps_of_entry`). In both families `u R` is black at every odd step, so the window of no member is
ever in the trap. -/

/-- A black cell of `u R` two steps after another black cell, after time `t0`, keeps the window of `R` out of the
gate trap at the odd time `t0`. -/
theorem not_trap_of_black_pair (R : Nat → Bool) {t0 : Nat} (h0 : t0 % 2 = 1) (s : Nat) (hs : t0 ≤ 2 * s + 1)
    (h1 : u R s = true) (h2 : u R (s + 2) = true) : Rule30GateTrap.win R t0 ∉ Rule30GateTrap.trap := by
  intro hw
  rcases Rule30GateTrap.gaps_of_entry R h0 hw s hs h1 with g | g
  · rw [h2] at g; exact Bool.noConfusion g.2.1
  · rw [h2] at g; exact Bool.noConfusion g.2.1

/-- **The first family never enters the gate trap.** -/
theorem never_enters_gate_trap31 (R : Nat → Bool) (h : AgreesPrefix 28 R R31) (t : Nat) (ht : t % 2 = 1) :
    Rule30GateTrap.win R t ∉ Rule30GateTrap.trap :=
  not_trap_of_black_pair R ht (2 * t + 1) (by omega)
    (by rw [u_prefix31 R h]; simp only [show (2 * t + 1) % 2 = 1 by omega]; rfl)
    (by rw [u_prefix31 R h]; simp only [show (2 * t + 1 + 2) % 2 = 1 by omega]; rfl)

/-- **The second family never enters the gate trap.** -/
theorem never_enters_gate_trap495 (R : Nat → Bool) (h : AgreesPrefix 24 R R495) (t : Nat) (ht : t % 2 = 1) :
    Rule30GateTrap.win R t ∉ Rule30GateTrap.trap :=
  not_trap_of_black_pair R ht (2 * t + 1) (by omega)
    (by rw [u_prefix495 R h]; simp only [show (2 * t + 1) % 2 = 1 by omega]; rfl)
    (by rw [u_prefix495 R h]; simp only [show (2 * t + 1 + 2) % 2 = 1 by omega]; rfl)

end Ruliology.CellularAutomata.Rule30EtherFamilies
