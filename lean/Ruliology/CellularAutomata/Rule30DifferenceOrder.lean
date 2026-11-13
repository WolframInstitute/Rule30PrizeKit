module

public import Ruliology.CellularAutomata.Rule30RecordCharge

/-!
# The difference order of a periodic Boolean stream

For a stream `g : Nat → Bool` write `dif g t = g (t + 1) xor g t` and `difs k g` for the `k`-th
difference. This module is the algebraic half of `Rule30RightPeriods.per_upper_half`; it says
nothing about Rule 30.

**Differences at powers of two.** `difs (2 ^ v) g t = g (t + 2 ^ v) xor g t`
(`difs_two_pow`), because squaring the difference operator over `F₂` squares the shift. So a
stream of period `2 ^ v` has `difs (2 ^ v) g = 0` (`vanish_of_period`).

**The order.** `order g L` is the largest `r ≤ L - 1` with `difs (L - r) g = 0`
(`le_order_iff`). For `L = 2 ^ v` and a stream of period `L` it is the multiplicity of the
factor `1 + z` in `∑_{t < L} g t z^t` over `F₂`, capped at `L - 1`: modulo
`z^L - 1 = (1 + z)^L` the difference operator is multiplication by `z⁻¹ (1 + z)`, and `z⁻¹` is a
unit, so it does not change that multiplicity. No polynomials are used here.

**Three laws.** Let `M = 2 ^ v`, and let `h (t + 1) = h t xor (b t || s t)` where `s` has
period `M` and `b (t + M) = !b t`. Then `difs M h` is the shifted sum `h (t + M) xor h t`, and its
difference is `!s` (`dif_shift_sum`). Hence:

* `order_of_antiperiod`: if `h (t + M) = !h t` then `order h (2 * M) = M - 1`;
* `order_reset_before`: if `h (t + 2 * M) = !h t` then `order s M = 0`;
* `order_countdown`: if `h` has period `2 * M` then `order s M ≤ order h (2 * M) + 1`.

These are the reset and countdown laws of `Rule30RecordCharge.Path`.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30DifferenceOrder

open Rule30RecordCharge

/-- The first difference of a stream over `F₂`. -/
def dif (g : Nat → Bool) (t : Nat) : Bool := xor (g (t + 1)) (g t)

/-- The `k`-th difference. -/
def difs : Nat → (Nat → Bool) → Nat → Bool
  | 0, g => g
  | k + 1, g => dif (difs k g)

theorem difs_succ' (k : Nat) (g : Nat → Bool) : difs (k + 1) g = difs k (dif g) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [difs] at ih ⊢; rw [ih]

theorem difs_add (a b : Nat) (g : Nat → Bool) : difs (a + b) g = difs a (difs b g) := by
  induction a with
  | zero => simp only [Nat.zero_add, difs]
  | succ a ih => rw [Nat.succ_add]; simp only [difs]; rw [ih]

theorem difs_xor (k : Nat) (f g : Nat → Bool) :
    difs k (fun t => xor (f t) (g t)) = fun t => xor (difs k f t) (difs k g t) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext t
    simp only [difs, dif, ih]
    cases difs k f (t + 1) <;> cases difs k g (t + 1) <;> cases difs k f t <;>
      cases difs k g t <;> rfl

theorem difs_shift (k c : Nat) (g : Nat → Bool) :
    difs k (fun t => g (t + c)) = fun t => difs k g (t + c) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext t
    simp only [difs, dif, ih, Nat.add_right_comm t 1 c]

theorem difs_const (k : Nat) (c : Bool) : difs (k + 1) (fun _ => c) = fun _ => false := by
  rw [difs_succ']
  have h : dif (fun _ => c) = fun _ => false := by funext t; cases c <;> rfl
  rw [h]
  induction k with
  | zero => rfl
  | succ k ih => simp only [difs, ih]; rfl

/-- Over `F₂` the `2 ^ v`-th difference is a shift by `2 ^ v` plus the identity. -/
theorem difs_two_pow (v : Nat) (g : Nat → Bool) :
    difs (2 ^ v) g = fun t => xor (g (t + 2 ^ v)) (g t) := by
  induction v generalizing g with
  | zero => rfl
  | succ v ih =>
    rw [Nat.pow_succ, Nat.mul_two, difs_add, ih, ih]
    funext t
    simp only [Nat.add_assoc]
    cases g (t + (2 ^ v + 2 ^ v)) <;> cases g (t + 2 ^ v) <;> cases g t <;> rfl

theorem two_pow_succ' (n : Nat) : 2 ^ (n + 1) = 2 * 2 ^ n := by
  rw [Nat.pow_succ, Nat.mul_comm]

/-! ### Vanishing and the order -/

/-- The `k`-th difference is identically `false`. -/
def Vanish (k : Nat) (g : Nat → Bool) : Prop := ∀ t, difs k g t = false

theorem Vanish.succ {k : Nat} {g : Nat → Bool} (h : Vanish k g) : Vanish (k + 1) g := by
  intro t
  simp only [difs, dif, h (t + 1), h t]
  rfl

theorem Vanish.mono {k m : Nat} {g : Nat → Bool} (h : Vanish k g) (hkm : k ≤ m) : Vanish m g := by
  induction m with
  | zero => rw [Nat.le_zero.mp hkm] at h; exact h
  | succ m ih =>
    rcases Nat.lt_or_eq_of_le hkm with hlt | heq
    · exact (ih (by omega)).succ
    · rw [← heq]; exact h

theorem vanish_of_period {v : Nat} {g : Nat → Bool} (h : ∀ t, g (t + 2 ^ v) = g t) :
    Vanish (2 ^ v) g := by
  intro t
  rw [difs_two_pow]
  show xor (g (t + 2 ^ v)) (g t) = false
  rw [h t]
  cases g t <;> rfl

open Classical in
/-- The largest `r ≤ L - 1` with `Vanish (L - r) g`: the number of `k < L - 1` with
`Vanish (L - 1 - k) g`. -/
noncomputable def order (g : Nat → Bool) (L : Nat) : Nat :=
  countBelow (fun k => Vanish (L - 1 - k) g) (L - 1)

open Classical in
theorem order_le (g : Nat → Bool) (L : Nat) : order g L ≤ L - 1 := countBelow_le _ _

open Classical in
theorem le_order_iff {g : Nat → Bool} {L r : Nat} (hr1 : 1 ≤ r) (hr : r ≤ L - 1) :
    r ≤ order g L ↔ Vanish (L - r) g := by
  have hp : ∀ k, Vanish (L - 1 - (k + 1)) g → Vanish (L - 1 - k) g :=
    fun k h => h.mono (by omega)
  unfold order
  rw [le_countBelow_iff hp (L - 1) r hr]
  constructor
  · intro h
    have := h (r - 1) (by omega)
    rwa [show L - 1 - (r - 1) = L - r by omega] at this
  · intro h k hk
    exact h.mono (by omega)

/-! ### The three laws -/

/-- The difference of the shifted sum `h (t + M) xor h t` is `!s`. -/
theorem dif_shift_sum {s b h : Nat → Bool} {M : Nat}
    (hs : ∀ t, s (t + M) = s t) (hb : ∀ t, b (t + M) = !b t)
    (hh : ∀ t, h (t + 1) = xor (h t) (b t || s t)) :
    dif (fun t => xor (h (t + M)) (h t)) = fun t => !s t := by
  funext t
  simp only [dif]
  rw [Nat.add_right_comm t 1 M, hh (t + M), hh t, hs t, hb t]
  cases h (t + M) <;> cases h t <;> cases b t <;> cases s t <;> rfl

/-- Past the `M`-th difference, `h` behaves like `!s`, hence like `s`. -/
theorem difs_past {s b h : Nat → Bool} {v : Nat}
    (hs : ∀ t, s (t + 2 ^ v) = s t) (hb : ∀ t, b (t + 2 ^ v) = !b t)
    (hh : ∀ t, h (t + 1) = xor (h t) (b t || s t)) (k : Nat) :
    difs (k + 1 + 1 + 2 ^ v) h = difs (k + 1) s := by
  rw [difs_add, difs_two_pow, difs_succ' (k + 1), dif_shift_sum hs hb hh]
  have hn : (fun t => !s t) = fun t => xor ((fun _ => true) t) (s t) := by
    funext t; cases s t <;> rfl
  rw [hn, difs_xor, difs_const]
  funext t
  cases difs (k + 1) s t <;> rfl

/-- A stream that a shift by `M = 2 ^ v` complements has order `M - 1` at length `2 * M`. -/
theorem order_of_antiperiod {h : Nat → Bool} {v : Nat} (hh : ∀ t, h (t + 2 ^ v) = !h t) :
    order h (2 * 2 ^ v) = 2 ^ v - 1 := by
  have hM := Nat.one_le_two_pow (n := v)
  have hconst : difs (2 ^ v) h = fun _ => true := by
    rw [difs_two_pow]; funext t; rw [hh t]; cases h t <;> rfl
  have hnot : ¬ Vanish (2 ^ v) h := fun hv => by
    have := hv 0; rw [hconst] at this; exact Bool.noConfusion this
  have hyes : Vanish (2 ^ v + 1) h := by
    intro t
    rw [Nat.add_comm, difs_add, hconst]
    rfl
  apply Nat.le_antisymm
  · apply Nat.le_of_not_lt
    intro hlt
    have := (le_order_iff (g := h) (L := 2 * 2 ^ v) (r := 2 ^ v) hM (by omega)).mp (by omega)
    rw [show 2 * 2 ^ v - 2 ^ v = 2 ^ v by omega] at this
    exact hnot this
  · rcases Nat.lt_or_ge (2 ^ v - 1) 1 with h0 | h1
    · omega
    · apply (le_order_iff h1 (by omega)).mpr
      rw [show 2 * 2 ^ v - (2 ^ v - 1) = 2 ^ v + 1 by omega]
      exact hyes

/-- Before a step whose shifted sum is complemented by a shift of `2 * M`, the order is `0`. -/
theorem order_reset_before {s b h : Nat → Bool} {v : Nat}
    (hs : ∀ t, s (t + 2 ^ v) = s t) (hb : ∀ t, b (t + 2 ^ v) = !b t)
    (hh : ∀ t, h (t + 1) = xor (h t) (b t || s t))
    (hanti : ∀ t, h (t + 2 * 2 ^ v) = !h t) :
    order s (2 ^ v) = 0 := by
  cases v with
  | zero => have := order_le s (2 ^ 0); omega
  | succ v =>
    have hM : 2 ≤ 2 ^ (v + 1) := by
      rw [Nat.pow_succ]; have := Nat.one_le_two_pow (n := v); omega
    apply Nat.eq_zero_of_not_pos
    intro hpos
    have hv := (le_order_iff (g := s) (L := 2 ^ (v + 1)) (r := 1) (by omega) (by omega)).mp hpos
    have hall : difs (2 * 2 ^ (v + 1)) h = fun _ => true := by
      rw [← two_pow_succ' (v + 1), difs_two_pow]
      funext t
      rw [two_pow_succ' (v + 1), hanti t]
      cases h t <;> rfl
    have hpast := difs_past hs hb hh (2 ^ (v + 1) - 2)
    rw [show 2 ^ (v + 1) - 2 + 1 + 1 + 2 ^ (v + 1) = 2 * 2 ^ (v + 1) by omega, hall,
      show 2 ^ (v + 1) - 2 + 1 = 2 ^ (v + 1) - 1 by omega] at hpast
    have := hv 0
    rw [← hpast] at this
    exact Bool.noConfusion this

/-- A step that returns the shifted sum after `2 * M` lowers the order by at most one. -/
theorem order_countdown {s b h : Nat → Bool} {v : Nat}
    (hs : ∀ t, s (t + 2 ^ v) = s t) (hb : ∀ t, b (t + 2 ^ v) = !b t)
    (hh : ∀ t, h (t + 1) = xor (h t) (b t || s t)) :
    order s (2 ^ v) ≤ order h (2 * 2 ^ v) + 1 := by
  have hle := order_le s (2 ^ v)
  rcases Nat.lt_or_ge (order s (2 ^ v)) 2 with h2 | h2
  · omega
  · have hv := (le_order_iff (g := s) (L := 2 ^ v) (r := order s (2 ^ v)) (by omega) hle).mp
      (Nat.le_refl _)
    have hgoal : order s (2 ^ v) - 1 ≤ order h (2 * 2 ^ v) := by
      apply (le_order_iff (by omega) (by omega)).mpr
      intro t
      have hpast := difs_past hs hb hh (2 ^ v - order s (2 ^ v) - 1)
      rw [show 2 ^ v - order s (2 ^ v) - 1 + 1 + 1 + 2 ^ v =
          2 * 2 ^ v - (order s (2 ^ v) - 1) by omega,
        show 2 ^ v - order s (2 ^ v) - 1 + 1 = 2 ^ v - order s (2 ^ v) by omega] at hpast
      rw [hpast]
      exact hv t
    omega

/-! ### Dyadic periodicity equivalence `Vanish (2 ^ v) g ↔ (∀ t, g (t + 2 ^ v) = g t)` and closure of `Vanish k` -/

/-- **Dyadic Periodicity Equivalence for `Vanish (2 ^ v)` and Closure Under XOR and Shifts (`vanish_two_pow_iff_and_xor_shift`).** -/
theorem vanish_two_pow_iff_and_xor_shift (v k c : Nat) (f g : Nat → Bool) :
    (Vanish (2 ^ v) g ↔ (∀ t, g (t + 2 ^ v) = g t)) ∧
    (Vanish k f → Vanish k g → Vanish k (fun t => xor (f t) (g t))) ∧
    (Vanish k g → Vanish k (fun t => g (t + c))) := by
  refine ⟨⟨fun hv t => ?_, vanish_of_period⟩,
          fun hf hg t => ?_,
          fun hg t => ?_⟩
  · have h := hv t
    rw [difs_two_pow] at h
    change xor (g (t + 2 ^ v)) (g t) = false at h
    revert h; cases g (t + 2 ^ v) <;> cases g t <;> decide
  · rw [difs_xor]
    dsimp only
    rw [hf t, hg t]; rfl
  · rw [difs_shift]
    exact hg (t + c)

end Rule30DifferenceOrder
end Ruliology.CellularAutomata
