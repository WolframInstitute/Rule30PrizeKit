module

public import Ruliology.CellularAutomata.Rule30DifferenceOrder

/-!
# Half-rate prefix clocks for every two-input gate

The right edge of Rule 30, read in the frame moving with it, is the 2-adic map
`x_j ↦ x_j xor (x_(j-1) || x_(j-2))`. `Rule30RightPeriods.per_upper_half` bounds its prefix periods with a
difference identity (`Rule30DifferenceOrder`) and a gate-free resource count (`Rule30RecordCharge.Path`). Here `||` is
replaced by an arbitrary gate, one for each depth.

For a family `g j : Bool → Bool → Bool` and a seed `x : Nat → Bool`, finite or infinite, bit `j` evolves by
`x_j(t+1) = x_j(t) xor g j (x_(j-1)(t)) (x_(j-2)(t))`, with missing bits white (`step`, `orbit`). `col g x (k + 1) t`
is bit `k` at time `t`, and `col g x 0` is a white bit below bit `0`. `prefixExp g x n` lifts the period of the first
`n` bits one bit at a time.

* `prefix_period_iff`: `P` is a period of the first `n` bits iff `2 ^ prefixExp g x n ∣ P`.
* `prefix_window_bound`: `prefixExp g x (a + 2 * m) - prefixExp g x a ≤ m + Q (prefixExp g x a) m ≤ m + Q 0 m`, for
  every window, with the thresholds of `Rule30RecordCharge`.
* `prefix_window_le_B`, `prefixExp_le_B`: a window of `n` bits raises the exponent by at most `B n`, and the first
  `n` bits have period dividing `2 ^ B n`.
* `affine_prefix_bound`: if every gate is affine, the first `n` bits have period dividing `2 ^ r` whenever
  `n + 1 ≤ 2 ^ r`.

The derivative `g true s xor g false s` of a two-input gate in its newer input is constant, `s` or `!s`, so one
more difference removes it (`vanish_comp`, `vanish_past_gate`). The reset and countdown laws
(`order_reset_before_gate`, `order_countdown_gate`) need nothing else, and `GateClock.windowPath` is the kit's `Path`
from any starting depth. The organization follows the prefix clocks of kit pull request 55
(`Rule30RightPrefixBound`); the period lifting is T-function cycle lifting (`Rule30Equivalents.TFunctionCycles`),
reproved here in core Lean. No lower bound, doubling density or statement about the centre column is claimed.

Core Lean 4.35.0. `README.md` maps the modules, names the headline theorems and says how to build.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30GateClocks

open Rule30RecordCharge Rule30DifferenceOrder

/-! ### The gate laws for the difference order -/

/-- A unary Boolean function keeps a vanishing positive difference vanishing. -/
theorem vanish_comp {k : Nat} {s : Nat → Bool} (d : Bool → Bool) (hv : Vanish (k + 1) s) :
    Vanish (k + 1) (fun t => d (s t)) := by
  intro t
  cases h1 : d true <;> cases h0 : d false
  · have hc : (fun t => d (s t)) = fun _ => false := by
      funext u; cases hu : s u <;> simp [h0, h1]
    rw [hc, difs_const]
  · have hc : (fun t => d (s t)) = fun u => xor ((fun _ => true) u) (s u) := by
      funext u; cases hu : s u <;> simp [h0, h1]
    rw [hc, difs_xor, difs_const]
    simp [hv t]
  · have hc : (fun t => d (s t)) = s := by
      funext u; cases hu : s u <;> simp [h0, h1]
    rw [hc]
    exact hv t
  · have hc : (fun t => d (s t)) = fun _ => true := by
      funext u; cases hu : s u <;> simp [h0, h1]
    rw [hc, difs_const]

/-- The derivative of a gate in its first (newer) input. -/
def deriv (g : Bool → Bool → Bool) (s : Bool) : Bool := xor (g true s) (g false s)

theorem xor_shift_deriv (g : Bool → Bool → Bool) (b s x y : Bool) :
    xor (xor (xor x (g (!b) s)) (xor y (g b s))) (xor x y) = deriv g s := by
  unfold deriv
  cases b <;> simp only [Bool.not_false, Bool.not_true] <;>
    cases x <;> cases y <;> cases g true s <;> cases g false s <;> rfl

/-- For any gate, the difference of the shifted sum `h (t + M) xor h t` is the derivative. -/
theorem dif_shift_sum_gate {g : Bool → Bool → Bool} {s b h : Nat → Bool} {M : Nat}
    (hs : ∀ t, s (t + M) = s t) (hb : ∀ t, b (t + M) = !b t)
    (hh : ∀ t, h (t + 1) = xor (h t) (g (b t) (s t))) :
    dif (fun t => xor (h (t + M)) (h t)) = fun t => deriv g (s t) := by
  funext t
  simp only [dif]
  rw [Nat.add_right_comm t 1 M, hh (t + M), hh t, hs t, hb t]
  exact xor_shift_deriv g (b t) (s t) (h (t + M)) (h t)

/-- Past the `M`-th difference, vanishing passes from `s` to `h`, for any gate. -/
theorem vanish_past_gate {g : Bool → Bool → Bool} {s b h : Nat → Bool} {v : Nat}
    (hs : ∀ t, s (t + 2 ^ v) = s t) (hb : ∀ t, b (t + 2 ^ v) = !b t)
    (hh : ∀ t, h (t + 1) = xor (h t) (g (b t) (s t))) {k : Nat} (hv : Vanish (k + 1) s) :
    Vanish (k + 1 + 1 + 2 ^ v) h := by
  intro t
  rw [difs_add, difs_two_pow, difs_succ' (k + 1), dif_shift_sum_gate hs hb hh]
  exact vanish_comp (deriv g) hv t

/-- Reset before a double step, for any gate (`Rule30DifferenceOrder.order_reset_before`). -/
theorem order_reset_before_gate {g : Bool → Bool → Bool} {s b h : Nat → Bool} {v : Nat}
    (hs : ∀ t, s (t + 2 ^ v) = s t) (hb : ∀ t, b (t + 2 ^ v) = !b t)
    (hh : ∀ t, h (t + 1) = xor (h t) (g (b t) (s t)))
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
    have hpast := vanish_past_gate hs hb hh (k := 2 ^ (v + 1) - 2)
      (by rw [show 2 ^ (v + 1) - 2 + 1 = 2 ^ (v + 1) - 1 by omega]; exact hv)
    rw [show 2 ^ (v + 1) - 2 + 1 + 1 + 2 ^ (v + 1) = 2 * 2 ^ (v + 1) by omega] at hpast
    have := hpast 0
    rw [hall] at this
    exact Bool.noConfusion this

/-- Countdown, for any gate (`Rule30DifferenceOrder.order_countdown`). -/
theorem order_countdown_gate {g : Bool → Bool → Bool} {s b h : Nat → Bool} {v : Nat}
    (hs : ∀ t, s (t + 2 ^ v) = s t) (hb : ∀ t, b (t + 2 ^ v) = !b t)
    (hh : ∀ t, h (t + 1) = xor (h t) (g (b t) (s t))) :
    order s (2 ^ v) ≤ order h (2 * 2 ^ v) + 1 := by
  have hle := order_le s (2 ^ v)
  rcases Nat.lt_or_ge (order s (2 ^ v)) 2 with h2 | h2
  · omega
  · have hv := (le_order_iff (g := s) (L := 2 ^ v) (r := order s (2 ^ v)) (by omega) hle).mp
      (Nat.le_refl _)
    have hgoal : order s (2 ^ v) - 1 ≤ order h (2 * 2 ^ v) := by
      apply (le_order_iff (by omega) (by omega)).mpr
      have hpast := vanish_past_gate hs hb hh (k := 2 ^ v - order s (2 ^ v) - 1)
        (by rw [show 2 ^ v - order s (2 ^ v) - 1 + 1 = 2 ^ v - order s (2 ^ v) by omega]; exact hv)
      rwa [show 2 ^ v - order s (2 ^ v) - 1 + 1 + 1 + 2 ^ v =
        2 * 2 ^ v - (order s (2 ^ v) - 1) by omega] at hpast
    omega

/-! ### Gate clocks and their record-charge paths -/

/-- A prefix clock driven by gates: `profile j` has period `2 ^ exponent j`, the exponent grows
by `0` or `1`, a growth complements the next profile, and each profile is a running XOR of a gate
of the two before it. Kit PR #55's `Clock`, with `||` replaced by `gate j`. -/
structure GateClock where
  gate : Nat → Bool → Bool → Bool
  profile : Nat → Nat → Bool
  exponent : Nat → Nat
  exponent_succ_cases : ∀ j, exponent (j + 1) = exponent j ∨ exponent (j + 1) = exponent j + 1
  period : ∀ j t, profile j (t + 2 ^ exponent j) = profile j t
  antiperiod : ∀ {j}, exponent (j + 1) = exponent j + 1 →
    ∀ t, profile (j + 1) (t + 2 ^ exponent j) = !profile (j + 1) t
  recurrence : ∀ j t, profile (j + 2) (t + 1) =
    xor (profile (j + 2) t) (gate j (profile (j + 1) t) (profile j t))

namespace GateClock

variable (C : GateClock)

theorem exponent_mono (a : Nat) : ∀ n, C.exponent a ≤ C.exponent (a + n)
  | 0 => Nat.le_refl _
  | n + 1 => by
    have := exponent_mono a n
    rcases C.exponent_succ_cases (a + n) with h | h <;> rw [← Nat.add_assoc, h] <;> omega

/-- The resource at pair `i` of the window from `a`. -/
noncomputable def resource (a i : Nat) : Nat :=
  order (C.profile (a + 2 * i)) (2 ^ C.exponent (a + 2 * i))

theorem pair_index (a i : Nat) : a + 2 * (i + 1) = a + 2 * i + 1 + 1 := by omega

/-- The pairs of a window from `a` form a record-charge path with `nu = exponent a`. -/
noncomputable def windowPath (a : Nat) : Path (C.exponent a) where
  weight i := C.exponent (a + 2 * i + 1 + 1) - C.exponent (a + 2 * i)
  exponent i := C.exponent (a + 2 * i) - C.exponent a
  resource := C.resource a
  exponent_zero := by simp
  exponent_step i := by
    have h0 := C.exponent_succ_cases (a + 2 * i)
    have h1 := C.exponent_succ_cases (a + 2 * i + 1)
    have hm := C.exponent_mono a (2 * i)
    show C.exponent (a + 2 * (i + 1)) - C.exponent a = _
    rw [pair_index]
    omega
  weight_le_two i := by
    have h0 := C.exponent_succ_cases (a + 2 * i)
    have h1 := C.exponent_succ_cases (a + 2 * i + 1)
    show C.exponent (a + 2 * i + 1 + 1) - C.exponent (a + 2 * i) ≤ 2
    omega
  reset_before i hw := by
    have h0 := C.exponent_succ_cases (a + 2 * i)
    have h1 := C.exponent_succ_cases (a + 2 * i + 1)
    change C.exponent (a + 2 * i + 1 + 1) - C.exponent (a + 2 * i) = 2 at hw
    have e0 : C.exponent (a + 2 * i + 1) = C.exponent (a + 2 * i) + 1 := by omega
    have e1 : C.exponent (a + 2 * i + 1 + 1) = C.exponent (a + 2 * i + 1) + 1 := by omega
    have hanti : ∀ t, C.profile (a + 2 * i + 1 + 1) (t + 2 * 2 ^ C.exponent (a + 2 * i)) =
        !C.profile (a + 2 * i + 1 + 1) t := by
      intro t
      have := C.antiperiod e1 t
      rwa [e0, two_pow_succ'] at this
    exact order_reset_before_gate (C.period (a + 2 * i)) (C.antiperiod e0)
      (C.recurrence (a + 2 * i)) hanti
  reset_after i hw := by
    have h0 := C.exponent_succ_cases (a + 2 * i)
    have h1 := C.exponent_succ_cases (a + 2 * i + 1)
    have hm := C.exponent_mono a (2 * i)
    change C.exponent (a + 2 * i + 1 + 1) - C.exponent (a + 2 * i) = 2 at hw
    have e0 : C.exponent (a + 2 * i + 1) = C.exponent (a + 2 * i) + 1 := by omega
    have e1 : C.exponent (a + 2 * i + 1 + 1) = C.exponent (a + 2 * i + 1) + 1 := by omega
    have hanti : ∀ t, C.profile (a + 2 * i + 1 + 1) (t + 2 ^ (C.exponent (a + 2 * i) + 1)) =
        !C.profile (a + 2 * i + 1 + 1) t := by
      intro t
      have := C.antiperiod e1 t
      rwa [e0] at this
    have hord := order_of_antiperiod hanti
    show order (C.profile (a + 2 * (i + 1))) (2 ^ C.exponent (a + 2 * (i + 1))) + 1 =
      2 ^ (C.exponent a + (C.exponent (a + 2 * (i + 1)) - C.exponent a) - 1)
    rw [pair_index, e1, e0, two_pow_succ' (C.exponent (a + 2 * i) + 1), hord,
      show C.exponent a + (C.exponent (a + 2 * i) + 1 + 1 - C.exponent a) - 1 =
        C.exponent (a + 2 * i) + 1 by omega]
    have := Nat.one_le_two_pow (n := C.exponent (a + 2 * i) + 1)
    omega
  countdown i hw := by
    have h0 := C.exponent_succ_cases (a + 2 * i)
    have h1 := C.exponent_succ_cases (a + 2 * i + 1)
    change C.exponent (a + 2 * i + 1 + 1) - C.exponent (a + 2 * i) = 1 at hw
    show C.resource a i ≤ order (C.profile (a + 2 * (i + 1))) (2 ^ C.exponent (a + 2 * (i + 1))) + 1
    rw [pair_index]
    unfold resource
    rcases h0 with e0 | e0
    · -- the middle profile keeps the period: the last one is complemented by `M`
      have e1 : C.exponent (a + 2 * i + 1 + 1) = C.exponent (a + 2 * i) + 1 := by omega
      have hanti : ∀ t, C.profile (a + 2 * i + 1 + 1) (t + 2 ^ C.exponent (a + 2 * i)) =
          !C.profile (a + 2 * i + 1 + 1) t := by
        intro t
        have := C.antiperiod (j := a + 2 * i + 1) (by omega) t
        rwa [e0] at this
      rw [e1, two_pow_succ', order_of_antiperiod hanti]
      have := order_le (C.profile (a + 2 * i)) (2 ^ C.exponent (a + 2 * i))
      omega
    · -- the middle profile is complemented by `M`: countdown
      have e1 : C.exponent (a + 2 * i + 1 + 1) = C.exponent (a + 2 * i) + 1 := by omega
      rw [e1, two_pow_succ']
      exact order_countdown_gate (C.period (a + 2 * i)) (C.antiperiod e0)
        (C.recurrence (a + 2 * i))

/-- The window bound for a gate clock. -/
theorem window_bound (a m : Nat) :
    C.exponent (a + 2 * m) - C.exponent a ≤ m + Q (C.exponent a) m :=
  exponent_bound_before_threshold (C.windowPath a) m (Q (C.exponent a) m) (Q_spec _ m)

end GateClock

/-! ### The thresholds only grow with `nu` -/

theorem threshold_zero_le (nu : Nat) : ∀ q, threshold 0 q ≤ threshold nu q
  | 0 => Nat.le_refl _
  | q + 1 => by
    have ih := threshold_zero_le nu q
    have hp := Nat.pow_le_pow_right (n := 2) (by decide)
      (show 0 + threshold 0 q + q ≤ nu + threshold nu q + q by omega)
    simp only [threshold]
    omega

theorem Q_le_Q_zero (nu m : Nat) : Q nu m ≤ Q 0 m :=
  (Q_le_iff nu m (Q 0 m)).mpr (Nat.lt_of_lt_of_le (Q_spec 0 m) (threshold_zero_le nu _))

/-! ### The edge map of a gate family and its prefix exponents -/

/-- One step: bit `j` is XORed with `g j` of bits `j - 1` and `j - 2`, missing bits white. -/
def step (g : Nat → Bool → Bool → Bool) (x : Nat → Bool) : Nat → Bool
  | 0 => xor (x 0) (g 0 false false)
  | 1 => xor (x 1) (g 1 (x 0) false)
  | j + 2 => xor (x (j + 2)) (g (j + 2) (x (j + 1)) (x j))

/-- The orbit of a seed. -/
def orbit (g : Nat → Bool → Bool → Bool) (x : Nat → Bool) : Nat → Nat → Bool
  | 0 => x
  | t + 1 => step g (orbit g x t)

/-- Columns: `col g x 0` is a white bit below bit `0`, and `col g x (k + 1) t` is bit `k` at time `t`. -/
def col (g : Nat → Bool → Bool → Bool) (x : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => false
  | k + 1, t => orbit g x t k

/-- The input that drives column `k + 1` (bit `k`). -/
def force (g : Nat → Bool → Bool → Bool) (x : Nat → Bool) (k t : Nat) : Bool :=
  g k (col g x k t) (col g x (k - 1) t)

theorem col_step (g : Nat → Bool → Bool → Bool) (x : Nat → Bool) (k t : Nat) :
    col g x (k + 1) (t + 1) = xor (col g x (k + 1) t) (force g x k t) := by
  match k with
  | 0 => rfl
  | 1 => rfl
  | j + 2 => rfl

/-- XOR of `f t, …, f (t + n - 1)`. -/
def xsum (f : Nat → Bool) (t : Nat) : Nat → Bool
  | 0 => false
  | n + 1 => xor (xsum f t n) (f (t + n))

theorem xsum_add (f : Nat → Bool) (t a : Nat) : ∀ b, xsum f t (a + b) = xor (xsum f t a) (xsum f (t + a) b)
  | 0 => by simp [xsum]
  | b + 1 => by
    rw [← Nat.add_assoc]
    simp only [xsum]
    rw [xsum_add f t a b, Nat.add_assoc t a b]
    cases xsum f t a <;> cases xsum f (t + a) b <;> cases f (t + (a + b)) <;> rfl

theorem xsum_succ_start (f : Nat → Bool) (t : Nat) : ∀ n, xsum f (t + 1) n = xor (xsum f t n) (xor (f t) (f (t + n)))
  | 0 => by simp [xsum]
  | n + 1 => by
    simp only [xsum]
    rw [xsum_succ_start f t n, show t + 1 + n = t + (n + 1) by omega]
    cases xsum f t n <;> cases f t <;> cases f (t + n) <;> cases f (t + (n + 1)) <;> rfl

/-- Over a period of `f`, the XOR does not depend on the start. -/
theorem xsum_period {f : Nat → Bool} {L : Nat} (hf : ∀ t, f (t + L) = f t) : ∀ t, xsum f t L = xsum f 0 L
  | 0 => rfl
  | t + 1 => by
    rw [xsum_succ_start, hf t, xsum_period hf t]
    cases xsum f 0 L <;> cases f t <;> rfl

theorem xsum_mul {f : Nat → Bool} {L : Nat} (hf : ∀ t, f (t + L) = f t) (t : Nat) :
    ∀ q, xsum f t (L * q) = (xsum f 0 L && q % 2 == 1)
  | 0 => by simp [xsum]
  | q + 1 => by
    rw [Nat.mul_succ, xsum_add, xsum_mul hf t q, xsum_period hf (t + L * q)]
    rcases Nat.mod_two_eq_zero_or_one q with h | h
    · have h' : (q + 1) % 2 = 1 := by omega
      rw [h, h']
      cases xsum f 0 L <;> rfl
    · have h' : (q + 1) % 2 = 0 := by omega
      rw [h, h']
      cases xsum f 0 L <;> rfl

theorem col_add (g : Nat → Bool → Bool → Bool) (x : Nat → Bool) (k t : Nat) :
    ∀ n, col g x (k + 1) (t + n) = xor (col g x (k + 1) t) (xsum (force g x k) t n)
  | 0 => by simp [xsum]
  | n + 1 => by
    rw [← Nat.add_assoc, col_step, col_add g x k t n]
    simp only [xsum]
    cases col g x (k + 1) t <;> cases xsum (force g x k) t n <;> cases force g x k (t + n) <;> rfl

/-- The exponent of the least period of the first `n` bits, by lifting one bit at a time. -/
def prefixExp (g : Nat → Bool → Bool → Bool) (x : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => prefixExp g x n + if xsum (force g x n) 0 (2 ^ prefixExp g x n) then 1 else 0

/-- `P` is a period of columns `0 … n`, that is of the first `n` bits. -/
def PrefixPer (g : Nat → Bool → Bool → Bool) (x : Nat → Bool) (n P : Nat) : Prop :=
  ∀ i, i ≤ n → ∀ t, col g x i (t + P) = col g x i t

theorem prefixExp_succ (g : Nat → Bool → Bool → Bool) (x : Nat → Bool) (n : Nat) :
    prefixExp g x (n + 1) =
      prefixExp g x n + if xsum (force g x n) 0 (2 ^ prefixExp g x n) then 1 else 0 := rfl

/-- **Exact prefix periods**: `P` is a period of the first `n` bits iff `2 ^ prefixExp g x n`
divides `P`. -/
theorem prefix_period_iff (g : Nat → Bool → Bool → Bool) (x : Nat → Bool) :
    ∀ n P, PrefixPer g x n P ↔ 2 ^ prefixExp g x n ∣ P
  | 0, P => by
    constructor
    · intro _; simp [prefixExp]
    · intro _ i hi t
      rw [Nat.le_zero.mp hi]
      rfl
  | n + 1, P => by
    have ih := prefix_period_iff g x n
    have hforce : ∀ t, force g x n (t + 2 ^ prefixExp g x n) = force g x n t := by
      have hp := (ih (2 ^ prefixExp g x n)).mpr (Nat.dvd_refl _)
      intro t
      unfold force
      rw [hp n (Nat.le_refl n) t, hp (n - 1) (by omega) t]
    constructor
    · intro hP
      have hlow : PrefixPer g x n P := fun i hi t => hP i (by omega) t
      obtain ⟨q, hq⟩ := (ih P).mp hlow
      have hc := hP (n + 1) (Nat.le_refl _) 0
      rw [col_add, hq, xsum_mul hforce] at hc
      by_cases hx : xsum (force g x n) 0 (2 ^ prefixExp g x n) = true
      · rw [prefixExp_succ, ite_eq_left hx]
        have hq2 : q % 2 = 0 := by
          rcases Nat.mod_two_eq_zero_or_one q with h | h
          · exact h
          · rw [hx, h] at hc
            cases hc0 : col g x (n + 1) 0 <;> rw [hc0] at hc <;> exact absurd hc (by decide)
        obtain ⟨q', rfl⟩ : ∃ q', q = 2 * q' := ⟨q / 2, by omega⟩
        exact ⟨q', by rw [hq, Nat.pow_succ, Nat.mul_assoc]⟩
      · rw [prefixExp_succ, ite_eq_right hx, Nat.add_zero]
        exact ⟨q, hq⟩
    · intro hd i hi t
      have hle : 2 ^ prefixExp g x n ∣ 2 ^ prefixExp g x (n + 1) :=
        Nat.pow_dvd_pow 2 (by rw [prefixExp_succ]; split <;> omega)
      have hlow := (ih P).mpr (Nat.dvd_trans hle hd)
      rcases Nat.lt_or_eq_of_le hi with hi | hi
      · exact hlow i (by omega) t
      · subst hi
        obtain ⟨q, hq⟩ := Nat.dvd_trans hle hd
        rw [col_add, hq, xsum_mul hforce]
        by_cases hx : xsum (force g x n) 0 (2 ^ prefixExp g x n) = true
        · rw [prefixExp_succ, ite_eq_left hx] at hd
          obtain ⟨q2, hq2⟩ := hd
          have hqq : q = 2 * q2 := by
            apply Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos (prefixExp g x n))
            rw [← hq, hq2, Nat.pow_succ, Nat.mul_assoc]
          have h0 : q % 2 = 0 := by omega
          rw [h0]
          cases xsum (force g x n) 0 (2 ^ prefixExp g x n) <;> cases col g x (n + 1) t <;> rfl
        · have hf : xsum (force g x n) 0 (2 ^ prefixExp g x n) = false := by
            cases h : xsum (force g x n) 0 (2 ^ prefixExp g x n)
            · rfl
            · exact absurd h hx
          rw [hf]
          cases col g x (n + 1) t <;> rfl

theorem prefixExp_succ_cases (g : Nat → Bool → Bool → Bool) (x : Nat → Bool) (n : Nat) :
    prefixExp g x (n + 1) = prefixExp g x n ∨ prefixExp g x (n + 1) = prefixExp g x n + 1 := by
  rw [prefixExp_succ]
  split <;> omega

/-- When the exponent grows, a shift by the old period complements the new bit. -/
theorem col_antiperiod (g : Nat → Bool → Bool → Bool) (x : Nat → Bool) {n : Nat}
    (h : prefixExp g x (n + 1) = prefixExp g x n + 1) (t : Nat) :
    col g x (n + 1) (t + 2 ^ prefixExp g x n) = !col g x (n + 1) t := by
  have hp := (prefix_period_iff g x n (2 ^ prefixExp g x n)).mpr (Nat.dvd_refl _)
  have hforce : ∀ t, force g x n (t + 2 ^ prefixExp g x n) = force g x n t := by
    intro t
    unfold force
    rw [hp n (Nat.le_refl n) t, hp (n - 1) (by omega) t]
  have hx : xsum (force g x n) 0 (2 ^ prefixExp g x n) = true := by
    cases hc : xsum (force g x n) 0 (2 ^ prefixExp g x n)
    · rw [prefixExp_succ, hc] at h
      simp at h
    · rfl
  rw [col_add, xsum_period hforce, hx]
  cases col g x (n + 1) t <;> rfl

/-- The columns of an orbit form a gate clock. -/
def gateClock (g : Nat → Bool → Bool → Bool) (x : Nat → Bool) : GateClock where
  gate j := g (j + 1)
  profile := col g x
  exponent := prefixExp g x
  exponent_succ_cases := prefixExp_succ_cases g x
  period j t := (prefix_period_iff g x j _).mpr (Nat.dvd_refl _) j (Nat.le_refl j) t
  antiperiod h t := col_antiperiod g x h t
  recurrence j t := by
    rw [col_step]
    rfl

/-! ### The half-rate bound -/

/-- **Window bound**: for every gate family, seed and window, the prefix exponent grows by at most
`m + Q (prefixExp a) m ≤ m + Q 0 m` over `2 m` further bits. -/
theorem prefix_window_bound (g : Nat → Bool → Bool → Bool) (x : Nat → Bool) (a m : Nat) :
    prefixExp g x (a + 2 * m) - prefixExp g x a ≤ m + Q (prefixExp g x a) m ∧
      prefixExp g x (a + 2 * m) - prefixExp g x a ≤ m + Q 0 m := by
  have h : prefixExp g x (a + 2 * m) - prefixExp g x a ≤ m + Q (prefixExp g x a) m :=
    (gateClock g x).window_bound a m
  have hQ := Q_le_Q_zero (prefixExp g x a) m
  exact ⟨h, by omega⟩

/-- Any window of `n` bits raises the prefix exponent by at most `⌈n/2⌉ + Q 0 ⌊n/2⌋`. -/
theorem prefix_window_le_B (g : Nat → Bool → Bool → Bool) (x : Nat → Bool) (a n : Nat) :
    prefixExp g x (a + n) - prefixExp g x a ≤ B n := by
  unfold B
  obtain ⟨d, rfl | rfl⟩ : ∃ d, n = 2 * d ∨ n = 2 * d + 1 := ⟨n / 2, by omega⟩
  · rw [show (2 * d + 1) / 2 = d by omega, show 2 * d / 2 = d by omega]
    exact (prefix_window_bound g x a d).2
  · rw [show (2 * d + 1 + 1) / 2 = d + 1 by omega, show (2 * d + 1) / 2 = d by omega,
      ← Nat.add_assoc]
    have := (prefix_window_bound g x a d).2
    have hm : prefixExp g x a ≤ prefixExp g x (a + 2 * d) := (gateClock g x).exponent_mono a (2 * d)
    rcases prefixExp_succ_cases g x (a + 2 * d) with h | h <;> omega

/-- **Half-rate bound**: the first `n` bits have period dividing `2 ^ B n`. -/
theorem prefixExp_le_B (g : Nat → Bool → Bool → Bool) (x : Nat → Bool) (n : Nat) :
    prefixExp g x n ≤ B n ∧ PrefixPer g x n (2 ^ B n) := by
  have h := prefix_window_le_B g x 0 n
  rw [Nat.zero_add] at h
  have hz : prefixExp g x 0 = 0 := rfl
  have h0 : prefixExp g x n ≤ B n := by omega
  exact ⟨h0, (prefix_period_iff g x n _).mpr (Nat.pow_dvd_pow 2 h0)⟩

/-! ### Affine gates: logarithmic exponents -/

/-- An affine gate: `g b s = (α && b) xor (β && s) xor γ`. -/
def Affine (g : Bool → Bool → Bool) : Prop :=
  ∃ α β γ : Bool, ∀ b s, g b s = xor (xor (α && b) (β && s)) γ

theorem vanish_xor {k : Nat} {f h : Nat → Bool} (hf : Vanish k f) (hh : Vanish k h) :
    Vanish k (fun t => xor (f t) (h t)) := by
  intro t
  rw [difs_xor]
  simp [hf t, hh t]

theorem vanish_const (k : Nat) (c : Bool) : Vanish (k + 1) (fun _ => c) := by
  intro t
  rw [difs_const]

theorem col_zero_fun (g : Nat → Bool → Bool → Bool) (x : Nat → Bool) :
    col g x 0 = fun _ => false := by
  funext t; rfl

/-- With affine gates, column `k` (bit `k - 1`) has a vanishing `(k + 1)`-th difference. -/
theorem affine_vanish (g : Nat → Bool → Bool → Bool) (x : Nat → Bool) (hg : ∀ j, Affine (g j)) :
    ∀ k, Vanish (k + 1) (col g x k) ∧ Vanish (k + 1 + 1) (col g x (k + 1))
  | 0 => by
    refine ⟨?_, ?_⟩
    · rw [col_zero_fun]; exact vanish_const 0 false
    · have hd : dif (col g x (0 + 1)) = fun _ => g 0 false false := by
        funext t
        simp only [dif]
        rw [col_step]
        show xor (xor (col g x 1 t) (g 0 false false)) (col g x 1 t) = g 0 false false
        cases col g x 1 t <;> cases g 0 false false <;> rfl
      intro t
      rw [difs_succ', hd]
      exact vanish_const 0 _ t
  | k + 1 => by
    obtain ⟨h1, h2⟩ := affine_vanish g x hg k
    refine ⟨h2, ?_⟩
    obtain ⟨α, β, γ, hgk⟩ := hg (k + 1)
    have hd : dif (col g x (k + 1 + 1)) =
        fun t => xor (xor (α && col g x (k + 1) t) (β && col g x k t)) γ := by
      funext t
      simp only [dif]
      rw [col_step]
      unfold force
      rw [hgk, Nat.add_sub_cancel]
      cases col g x (k + 1 + 1) t <;> simp
    intro t
    rw [difs_succ', hd]
    exact vanish_xor (vanish_xor (vanish_comp (fun u => α && u) h2)
      (vanish_comp (fun u => β && u) (h1.mono (by omega)))) (vanish_const _ γ) t

theorem period_of_vanish {f : Nat → Bool} {r : Nat} (hv : Vanish (2 ^ r) f) (t : Nat) :
    f (t + 2 ^ r) = f t := by
  have h := hv t
  rw [difs_two_pow] at h
  change xor (f (t + 2 ^ r)) (f t) = false at h
  cases h1 : f (t + 2 ^ r) <;> cases h2 : f t <;> simp_all

/-- **Affine gates**: if every gate is affine, the first `n` bits have period dividing `2 ^ r`
whenever `n + 1 ≤ 2 ^ r` (unitriangular nilpotency). -/
theorem affine_prefix_bound (g : Nat → Bool → Bool → Bool) (x : Nat → Bool)
    (hg : ∀ j, Affine (g j)) {n r : Nat} (hr : n + 1 ≤ 2 ^ r) :
    PrefixPer g x n (2 ^ r) ∧ prefixExp g x n ≤ r := by
  have hper : PrefixPer g x n (2 ^ r) := fun i hi t =>
    period_of_vanish (((affine_vanish g x hg i).1).mono (by omega)) t
  refine ⟨hper, ?_⟩
  have hd := (prefix_period_iff g x n _).mp hper
  exact (Nat.pow_dvd_pow_iff_le_right (by decide)).mp hd

end Ruliology.CellularAutomata.Rule30GateClocks
