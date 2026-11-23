module

public import Ruliology.CellularAutomata.Rule30EtherThreeNotAbsorption
public import Ruliology.CellularAutomata.Rule30Certificates.EtherThreeReach20

/-!
# The 15-trap for `001` is closed to ether prefixes and to white prefixes

`Rule30EtherThreeNotAbsorption` refutes `AbsorptionT t001` with a second trap, `trap001fifteen`. Here a set of windows of
twenty cells, one for each phase of the drive, holds that trap's states cut to twenty cells and is closed under
predecessors: if the next window is in the set, so is this one, whatever the cell beyond. No window of the aligned
period-3 ether is in it, and none whose first sixteen cells are white. So a right half that shows either at some tick is
from then on in no state of the trap whose label reads the drive's phase, whatever lies beyond those cells.

* `accR`: membership, a layered automaton that reads a window from cell `20` down to cell `1` (`54,576` windows).
* `chk`, `chk_sound`: one recursion along the automaton that checks closure under predecessors.
* `back`: membership at a tick gives membership at every earlier tick of the drive.
* `no_fifteen_after_ether`, `no_fifteen_after_white`: the two consequences.

Refuting entry by a set of windows closed under predecessors is L. Hallee's method (`lhallee/rule30-open`,
`Columns.ReachRefuted`).
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30EtherThreeNoFifteen

open Rule30Jen Rule30Ether Rule30EtherThree Rule30EtherThreeNotAbsorption
open Rule30EtherThreeReach20

/-- The table of phase `p`. -/
def tab (p : Nat) : Nat := if p == 0 then tab0 else if p == 1 then tab1 else tab2
/-- The root of phase `p`. -/
def root (p : Nat) : Nat := if p == 0 then root0 else if p == 1 then root1 else root2

/-- The successor of node `n` on reading a cell. Node `0` is dead. -/
def nd (T n : Nat) (b : Bool) : Nat := (T >>> (26 * n + cond b 13 0)) % 8192

/-- Reading the cells `k, k - 1, …, 1` from node `q` ends in a live node. -/
def accR (T : Nat) : Nat → Nat → (Nat → Bool) → Bool
  | 0, q, _ => q != 0
  | k + 1, q, f => accR T k (nd T q (f (k + 1))) f

/-- Evaluate `n` before going on. -/
def force (n : Nat) (f : Nat → Bool) : Bool := Nat.rec (f 0) (fun m _ => f (m + 1)) n

theorem force_eq (n : Nat) (f : Nat → Bool) : force n f = f n := by cases n <;> rfl

/-- Closure under predecessors, from cell `k` down: `q` has read the next window, `q'` this one, whose cells `k` and
`k + 1` are `a` and `b`; cell `0` must be `d`. -/
def chk (T1 T0 : Nat) (d : Bool) : Nat → Nat → Bool → Bool → Nat → Bool
  | 0, q, a, _, q' => q == 0 || (a != d || q' != 0)
  | _ + 1, 0, _, _, _ => true
  | k + 1, q + 1, true, _, q' => force (nd T0 q' true) fun m =>
      chk T1 T0 d k (nd T1 (q + 1) false) true true m && chk T1 T0 d k (nd T1 (q + 1) true) false true m
  | k + 1, q + 1, false, b, q' => force (nd T0 q' false) fun m =>
      chk T1 T0 d k (nd T1 (q + 1) false) b false m && chk T1 T0 d k (nd T1 (q + 1) true) (!b) false m

theorem accR_dead {T : Nat} (h : ∀ b, nd T 0 b = 0) (f : Nat → Bool) : ∀ k, accR T k 0 f = false
  | 0 => rfl
  | k + 1 => by unfold accR; rw [h]; exact accR_dead h f k

theorem accR_congr {T : Nat} {f g : Nat → Bool} : ∀ k q, (∀ j, 1 ≤ j → j ≤ k → f j = g j) → accR T k q f = accR T k q g
  | 0, _, _ => rfl
  | k + 1, q, h => by
    unfold accR
    rw [h (k + 1) (by omega) (Nat.le_refl _)]
    exact accR_congr k _ fun j h1 h2 => h j h1 (by omega)

/-- **Soundness.** If the check passes and the next row's window is accepted, so is this row's. -/
theorem chk_sound {T1 T0 : Nat} {d : Bool} (h1 : ∀ b, nd T1 0 b = 0) {x y : Nat → Bool}
    (hy : ∀ j, y (j + 1) = rule (x j) (x (j + 1)) (x (j + 2))) (hx : x 0 = d) :
    ∀ k q q', chk T1 T0 d k q (x k) (x (k + 1)) q' = true → accR T1 k q y = true → accR T0 k q' x = true := by
  intro k
  induction k with
  | zero =>
    intro q q' hc ha
    unfold accR at ha ⊢
    unfold chk at hc
    rw [hx] at hc
    simp_all
  | succ k ih =>
    intro q q' hc ha
    cases q with
    | zero => rw [accR_dead h1] at ha; exact absurd ha (by decide)
    | succ q =>
      have hr := hy k
      unfold accR at ha ⊢
      cases hk : x (k + 1) with
      | true =>
        rw [hk] at hc hr
        unfold chk at hc
        rw [force_eq, Bool.and_eq_true] at hc
        cases hv : y (k + 1) with
        | false =>
          rw [hv] at ha hr
          have hxk : x k = true := by revert hr; unfold rule; cases x k <;> simp
          exact ih _ _ (by rw [hxk, hk]; exact hc.1) ha
        | true =>
          rw [hv] at ha hr
          have hxk : x k = false := by revert hr; unfold rule; cases x k <;> simp
          exact ih _ _ (by rw [hxk, hk]; exact hc.2) ha
      | false =>
        rw [hk] at hc hr
        unfold chk at hc
        rw [force_eq, Bool.and_eq_true] at hc
        cases hv : y (k + 1) with
        | false =>
          rw [hv] at ha hr
          have hxk : x k = x (k + 1 + 1) := by
            revert hr; unfold rule; cases x k <;> cases x (k + 1 + 1) <;> simp
          exact ih _ _ (by rw [hxk, hk]; exact hc.1) ha
        | true =>
          rw [hv] at ha hr
          have hxk : x k = !x (k + 1 + 1) := by
            revert hr; unfold rule; cases x k <;> cases x (k + 1 + 1) <;> simp
          exact ih _ _ (by rw [hxk, hk]; exact hc.2) ha

/-- The check over the last cell and the cell beyond it. -/
def chkAll (T1 r1 T0 r0 : Nat) (d : Bool) : Bool :=
  chk T1 T0 d 20 r1 false false r0 && chk T1 T0 d 20 r1 false true r0 &&
    chk T1 T0 d 20 r1 true false r0 && chk T1 T0 d 20 r1 true true r0

set_option maxRecDepth 4000 in
theorem closed0 : chkAll tab1 root1 tab0 root0 false = true := by decide +kernel
set_option maxRecDepth 4000 in
theorem closed1 : chkAll tab2 root2 tab1 root1 false = true := by decide +kernel
set_option maxRecDepth 4000 in
theorem closed2 : chkAll tab0 root0 tab2 root2 true = true := by decide +kernel

theorem dead0 : ∀ b, nd tab0 0 b = 0 := by decide +kernel
theorem dead1 : ∀ b, nd tab1 0 b = 0 := by decide +kernel
theorem dead2 : ∀ b, nd tab2 0 b = 0 := by decide +kernel

theorem chkAll_sound {T1 r1 T0 r0 : Nat} {d : Bool} (h : chkAll T1 r1 T0 r0 d = true) (h1 : ∀ b, nd T1 0 b = 0)
    {x y : Nat → Bool} (hy : ∀ j, y (j + 1) = rule (x j) (x (j + 1)) (x (j + 2))) (hx : x 0 = d)
    (ha : accR T1 20 r1 y = true) : accR T0 20 r0 x = true := by
  unfold chkAll at h
  simp only [Bool.and_eq_true] at h
  refine chk_sound h1 hy hx 20 r1 r0 ?_ ha
  cases x 20 <;> cases x 21
  · exact h.1.1.1
  · exact h.1.1.2
  · exact h.1.2
  · exact h.2

/-! ### Rows -/

/-- The first twenty cells at tick `t`, at phase `p` of the drive, are in the set. -/
def InReach (F : Nat → Nat → Bool) (t p : Nat) : Prop := accR (tab p) 20 (root p) (F t) = true

theorem back_step {F : Nat → Nat → Bool} (hF : IsR30 F) {t p : Nat} (hp : p < 3) (h0 : F t 0 = wordAt3 w001 p)
    (h : InReach F (t + 1) ((p + 1) % 3)) : InReach F t p := by
  have hy : ∀ j, F (t + 1) (j + 1) = rule (F t j) (F t (j + 1)) (F t (j + 2)) := hF t
  rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2) with rfl | rfl | rfl
  · exact chkAll_sound closed0 dead1 hy h0 h
  · exact chkAll_sound closed1 dead2 hy h0 h
  · exact chkAll_sound closed2 dead0 hy h0 h

/-- **Backwards.** Membership at a tick gives membership at every earlier tick of the drive. -/
theorem back {F : Nat → Nat → Bool} (hF : IsR30 F) {T : Nat} (hc : ∀ t, T ≤ t → F t 0 = wordAt3 w001 (t - T))
    {t0 : Nat} (h0 : T ≤ t0) : ∀ n, InReach F (t0 + n) ((t0 + n - T) % 3) → InReach F t0 ((t0 - T) % 3) := by
  intro n
  induction n with
  | zero => intro h; exact h
  | succ n ih =>
    intro h
    refine ih (back_step hF (Nat.mod_lt _ (by decide)) ?_ ?_)
    · rw [hc (t0 + n) (by omega)]; unfold wordAt3; rw [Nat.mod_mod]
    · rw [show t0 + (n + 1) = t0 + n + 1 by omega] at h
      rw [show ((t0 + n - T) % 3 + 1) % 3 = (t0 + n + 1 - T) % 3 by omega]
      exact h

/-! ### The trap, the ether and the white window -/

theorem trap_all : allBelowT (fun i => accR (tab (trap001fifteen.lab i % 3)) 20 (root (trap001fifteen.lab i % 3))
    (fun j => (trap001fifteen.st i).testBit (j - 1))) 153 = true := by decide +kernel

theorem ether_all : ∀ a ∈ A001, ∀ φ, φ < 3 →
    accR (tab φ) 20 (root φ) (fun j => ether3 (a.1 + j) (φ + a.2)) = false := by decide +kernel

theorem white_all : ∀ φ, φ < 3 → ∀ a b c d : Bool, accR (tab φ) 20 (root φ)
    (fun j => if j ≤ 16 then false else if j = 17 then a else if j = 18 then b else if j = 19 then c else d) = false := by
  decide +kernel

/-- A row in the trap is in the set. -/
theorem trap_in {F : Nat → Nat → Bool} {t i : Nat} (hi : i < 153) (h : EncF F 52 t 0 (trap001fifteen.st i)) :
    InReach F t (trap001fifteen.lab i % 3) := by
  have h1 := allBelowT_spec trap_all i hi
  unfold InReach
  rw [← h1]
  refine accR_congr 20 _ fun j h1 h2 => ?_
  have := h.2 (j - 1) (by omega)
  rw [this]
  congr 1
  omega

/-- A half whose first twenty cells are outside the set at some tick is in no state of the trap from then on. -/
theorem never {F : Nat → Nat → Bool} (hF : IsR30 F) {T : Nat} (hc : ∀ t, T ≤ t → F t 0 = wordAt3 w001 (t - T))
    {t0 : Nat} (h0 : T ≤ t0) (hout : ¬ InReach F t0 ((t0 - T) % 3)) :
    ∀ t, t0 ≤ t → ∀ i, i < 153 → (t - T) % 3 = trap001fifteen.lab i % 3 →
      ¬ EncF F 52 t 0 (trap001fifteen.st i) := by
  intro t ht i hi hph hE
  refine hout (back hF hc h0 (t - t0) ?_)
  rw [show t0 + (t - t0) = t by omega, hph]
  exact trap_in hi hE

/-- **After the ether.** A right half of the `001` drive whose first twenty columns are the aligned period-3 ether at some
tick is from then on in no state of the 15-trap whose label reads the drive's phase, whatever lies beyond them. -/
theorem no_fifteen_after_ether {F : Nat → Nat → Bool} (hF : IsR30 F) {T : Nat}
    (hc : ∀ t, T ≤ t → F t 0 = wordAt3 w001 (t - T)) {t0 j0 s : Nat} (h0 : T ≤ t0) (ha : (j0, s) ∈ A001)
    (he : ∀ p, 1 ≤ p → p ≤ 20 → F t0 p = ether3 (j0 + p) (t0 - T + s)) :
    ∀ t, t0 ≤ t → ∀ i, i < 153 → (t - T) % 3 = trap001fifteen.lab i % 3 →
      ¬ EncF F 52 t 0 (trap001fifteen.st i) := by
  refine never hF hc h0 ?_
  have h := ether_all (j0, s) ha ((t0 - T) % 3) (Nat.mod_lt _ (by decide))
  unfold InReach
  rw [accR_congr (g := fun j => ether3 (j0 + j) ((t0 - T) % 3 + s)) 20 _ fun j h1 h2 => by
    rw [he j h1 h2]; exact ether3_congr rfl (by omega)]
  rw [h]; decide

/-- **After sixteen white cells.** A right half of the `001` drive whose first sixteen cells are white at some tick is from
then on in no state of the 15-trap whose label reads the drive's phase, whatever lies beyond them. -/
theorem no_fifteen_after_white {F : Nat → Nat → Bool} (hF : IsR30 F) {T : Nat}
    (hc : ∀ t, T ≤ t → F t 0 = wordAt3 w001 (t - T)) {t0 : Nat} (h0 : T ≤ t0)
    (hw : ∀ p, 1 ≤ p → p ≤ 16 → F t0 p = false) :
    ∀ t, t0 ≤ t → ∀ i, i < 153 → (t - T) % 3 = trap001fifteen.lab i % 3 →
      ¬ EncF F 52 t 0 (trap001fifteen.st i) := by
  refine never hF hc h0 ?_
  have h := white_all ((t0 - T) % 3) (Nat.mod_lt _ (by decide)) (F t0 17) (F t0 18) (F t0 19) (F t0 20)
  unfold InReach
  rw [accR_congr (g := fun j => if j ≤ 16 then false else if j = 17 then F t0 17 else if j = 18 then F t0 18 else
    if j = 19 then F t0 19 else F t0 20) 20 _ fun j h1 h2 => by
      by_cases h16 : j ≤ 16
      · rw [ite_eq_left h16]; exact hw j h1 h16
      · rw [ite_eq_right h16]
        rcases (by omega : j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20) with rfl | rfl | rfl | rfl <;> rfl]
  rw [h]; decide

end Rule30EtherThreeNoFifteen
end Ruliology.CellularAutomata
