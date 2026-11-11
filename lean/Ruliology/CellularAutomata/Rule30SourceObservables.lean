module

public import Ruliology.CellularAutomata.Rule30Prize

/-!
# Run-end source observables: a temporal density bound and finite recovery

For arbitrary column streams satisfying two neighboring Rule 30 updates,
`density_bound` proves `3*C(T) <= T + 5*A(T) + 3`, where the run-end source
is `source c r = c && !r`. `cell_density_bound` specializes this to every
spatial column and time interval of the official singleton diagram.

`Band.recover` proves that eight consecutive observations of three adjacent
run-end sources determine the four-cell state at time one. Its hypotheses
retain the fifth-cell update; an arbitrary exterior input at both times
would not justify the result. The finite pair-state checks are ingredients
of a theorem about arbitrary streams, not a sampled trajectory claim.

No unconditional asymptotic source-frequency estimate, eventual-nonperiodicity
conclusion, or solution to a prize problem is asserted. Derived finite-left claims
in the accompanying research reports are outside this formal module.
-/

@[expose] public section
namespace Ruliology.CellularAutomata.Rule30SourceObservables
open Rule30Jen (rule cell)

def source (c r : Bool) : Bool := c && !r

def bit (b : Bool) : Int := if b then 1 else 0

def potential (c r s : Bool) : Int :=
  -bit (s && !r) - 2 * bit r - bit (c && r && !s)

theorem potential_bounds (c r s : Bool) :
    -3 ≤ potential c r s ∧ potential c r s ≤ 0 := by
  cases c <;> cases r <;> cases s <;> decide

theorem local_inequality (c r s u nextC : Bool) :
    3 * bit c - 1 - 5 * bit (source c r) ≤
      potential nextC (rule c r s) (rule r s u) - potential c r s := by
  cases c <;> cases r <;> cases s <;> cases u <;> cases nextC <;> decide

def count (f : Nat → Bool) : Nat → Int
  | 0 => 0
  | t+1 => count f t + bit (f t)

theorem telescope (c r s u : Nat → Bool)
    (hr : ∀ t, r (t+1) = rule (c t) (r t) (s t))
    (hs : ∀ t, s (t+1) = rule (r t) (s t) (u t)) (T : Nat) :
    3 * count c T ≤ (T : Int) + 5 * count (fun t => source (c t) (r t)) T
      + potential (c T) (r T) (s T) - potential (c 0) (r 0) (s 0) := by
  induction T with
  | zero => simp [count]
  | succ t ih =>
      have step : 3 * bit (c t) - 1 - 5 * bit (source (c t) (r t)) ≤
          potential (c (t+1)) (r (t+1)) (s (t+1)) - potential (c t) (r t) (s t) := by
        rw [hr t, hs t]
        exact local_inequality (c t) (r t) (s t) (u t) (c (t+1))
      simp only [count]
      omega

theorem density_bound (c r s u : Nat → Bool)
    (hr : ∀ t, r (t+1) = rule (c t) (r t) (s t))
    (hs : ∀ t, s (t+1) = rule (r t) (s t) (u t)) (T : Nat) :
    3 * count c T ≤ (T : Int) + 5 * count (fun t => source (c t) (r t)) T + 3 := by
  have h := telescope c r s u hr hs T
  have hT := potential_bounds (c T) (r T) (s T)
  have h0 := potential_bounds (c 0) (r 0) (s 0)
  omega

theorem count_zero (f : Nat → Bool) (hf : ∀ t, f t = false) (T : Nat) :
    count f T = 0 := by
  induction T with
  | zero => rfl
  | succ t ih => simp [count, hf t, ih, bit]

theorem quiet_bound (c r s u : Nat → Bool)
    (hr : ∀ t, r (t+1) = rule (c t) (r t) (s t))
    (hs : ∀ t, s (t+1) = rule (r t) (s t) (u t))
    (quiet : ∀ t, (source (c t) (r t)) = false) (T : Nat) :
    3 * count c T ≤ (T : Int) + 3 := by
  have h := density_bound c r s u hr hs T
  have hz := count_zero (fun t => source (c t) (r t)) quiet T
  rw [hz] at h
  omega


/-- The density inequality on any finite interval of an actual singleton column. -/
theorem cell_density_bound (i : Int) (N T : Nat) :
    3 * count (fun t => cell (N+t) i) T ≤ (T : Int)
      + 5 * count (fun t => source (cell (N+t) i) (cell (N+t) (i+1))) T + 3 := by
  apply density_bound (fun t => cell (N+t) i)
    (fun t => cell (N+t) (i+1)) (fun t => cell (N+t) (i+2))
    (fun t => cell (N+t) (i+3))
  · intro t
    rw [show N+(t+1) = (N+t)+1 by omega, cell]
    congr 1 <;> congr 1 <;> omega
  · intro t
    rw [show N+(t+1) = (N+t)+1 by omega, cell]
    congr 1 <;> congr 1 <;> omega

namespace Band
set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev State := Fin 16
def bit (x : State) (weight : Nat) : Bool := (x.val / weight) % 2 == 1
def step (x : State) (newC v : Bool) : State :=
  Fin.ofNat 16 (8 * newC.toNat
    + 4 * (rule (bit x 8) (bit x 4) (bit x 2)).toNat
    + 2 * (rule (bit x 4) (bit x 2) (bit x 1)).toNat
    + (rule (bit x 2) (bit x 1) v).toNat)
def obs (x : State) : Nat :=
  4 * (source (bit x 8) (bit x 4)).toNat
    + 2 * (source (bit x 4) (bit x 2)).toNat
    + (source (bit x 2) (bit x 1)).toNat
def code (x y : State) : Nat := 16 * x.val + y.val
def H1 (x y : State) : Prop := code x y ∈
  [0, 1, 15, 16, 17, 31, 34, 46, 51, 68, 76, 77, 85, 102,
   119, 136, 153, 170, 187, 196, 204, 205, 212, 220, 221,
   226, 238, 240, 241, 255]
def H2 (x y : State) : Prop := code x y ∈
  [0, 15, 17, 34, 46, 51, 68, 76, 77, 85, 102, 119, 136,
   153, 170, 187, 196, 204, 212, 221, 226, 238, 240, 255]
def A (x y : State) : Prop := (x = 0 ∧ y = 15) ∨ (x = 15 ∧ y = 0)
def B (x y : State) : Prop := (x = 4 ∧ y = 12) ∨ (x = 12 ∧ y = 4)
def C (x y : State) : Prop := (x = 2 ∧ y = 14) ∨ (x = 14 ∧ y = 2)
def Live (x y : State) : Prop := x = y ∨ A x y ∨ B x y ∨ C x y

instance (x y : State) : Decidable (H1 x y) := inferInstanceAs (Decidable (_ ∈ _))
instance (x y : State) : Decidable (H2 x y) := inferInstanceAs (Decidable (_ ∈ _))
instance (x y : State) : Decidable (A x y) := inferInstanceAs (Decidable (_ ∨ _))
instance (x y : State) : Decidable (B x y) := inferInstanceAs (Decidable (_ ∨ _))
instance (x y : State) : Decidable (C x y) := inferInstanceAs (Decidable (_ ∨ _))
instance (x y : State) : Decidable (Live x y) := inferInstanceAs (Decidable (_ ∨ _))

theorem prune1 : ∀ (x y : State) (a b c d : Bool),
    obs x = obs y → obs (step x a b) = obs (step y c d) → H1 x y := by decide
theorem prune2 : ∀ (x y : State) (a b c d : Bool),
    obs x = obs y → H1 (step x a b) (step y c d) → H2 x y := by decide
theorem prune3 : ∀ (x y : State) (a b c d : Bool),
    obs x = obs y → H2 (step x a b) (step y c d) → Live x y := by decide

theorem into_A : ∀ (x y : State) (a b c d : Bool),
    Live x y → A (step x a b) (step y c d) → C x y := by decide
theorem out_B : ∀ (x y : State) (a b c d : Bool),
    B x y → Live (step x a b) (step y c d) → C (step x a b) (step y c d) := by decide

theorem coupling : ∀ (x y : State) (a b c d e f g h : Bool), C x y →
    Live (step x a b) (step y e f) →
    ¬ Live (step (step x a b) c (rule (bit x 1) b d))
      (step (step y e f) g (rule (bit y 1) f h)) := by decide

theorem recover
    (x y : Nat → State) (cx cy vx vy wx wy : Nat → Bool)
    (hx : ∀ t, x (t+1) = step (x t) (cx t) (vx t))
    (hy : ∀ t, y (t+1) = step (y t) (cy t) (vy t))
    (hvx : ∀ t, vx (t+1) = rule (bit (x t) 1) (vx t) (wx t))
    (hvy : ∀ t, vy (t+1) = rule (bit (y t) 1) (vy t) (wy t))
    (ho : ∀ t, t ≤ 7 → obs (x t) = obs (y t)) : x 1 = y 1 := by
  have live_at (t : Nat) (ht : t ≤ 4) : Live (x t) (y t) := by
    have h1 : H1 (x (t+2)) (y (t+2)) := by
      apply prune1 (x (t+2)) (y (t+2))
        (cx (t+2)) (vx (t+2)) (cy (t+2)) (vy (t+2))
      · exact ho (t+2) (by omega)
      · simpa only [hx (t+2), hy (t+2), Nat.add_assoc] using ho (t+3) (by omega)
    have h2 : H2 (x (t+1)) (y (t+1)) := by
      apply prune2 (x (t+1)) (y (t+1))
        (cx (t+1)) (vx (t+1)) (cy (t+1)) (vy (t+1))
      · exact ho (t+1) (by omega)
      · simpa only [hx (t+1), hy (t+1), Nat.add_assoc] using h1
    apply prune3 (x t) (y t)
      (cx t) (vx t) (cy t) (vy t)
    · exact ho t (by omega)
    · simpa only [hx t, hy t] using h2
  have no_C (t : Nat) (ht : t ≤ 2) : ¬ C (x t) (y t) := by
    intro hc
    have hnext : Live
        (step (x t) (cx t) (vx t))
        (step (y t) (cy t) (vy t)) := by
      simpa only [hx t, hy t] using live_at (t+1) (by omega)
    have hbad := coupling (x t) (y t)
      (cx t) (vx t) (cx (t+1)) (wx t)
      (cy t) (vy t) (cy (t+1)) (wy t) hc hnext
    apply hbad
    have htwo := live_at (t+2) (by omega)
    rw [show t+2 = (t+1)+1 by omega, hx (t+1), hy (t+1), hx t, hy t, hvx t, hvy t] at htwo
    exact htwo
  rcases live_at 1 (by omega) with h | hA | hB | hC
  · exact h
  · have ha : A
        (step (x 0) (cx 0) (vx 0))
        (step (y 0) (cy 0) (vy 0)) := by
      simpa only [hx 0, hy 0] using hA
    exact False.elim (no_C 0 (by omega)
      (into_A (x 0) (y 0) (cx 0) (vx 0) (cy 0) (vy 0)
        (live_at 0 (by omega)) ha))
  · have hl : Live
        (step (x 1) (cx 1) (vx 1))
        (step (y 1) (cy 1) (vy 1)) := by
      simpa only [hx 1, hy 1] using live_at 2 (by omega)
    have hc := out_B (x 1) (y 1) (cx 1) (vx 1) (cy 1) (vy 1) hB hl
    have : C (x 2) (y 2) := by simpa only [hx 1, hy 1] using hc
    exact False.elim (no_C 2 (by omega) this)
  · exact False.elim (no_C 1 (by omega) hC)


end Band
/-! ### Shifted-window density bounds, one-third ceiling under source vanishing, run-end source lower bounds from black-cell excess, and arbitrary-interval state recovery -/

/-- **Zero-One Bounds on `bit` (`bit_bounds`):**
for every `b : Bool`, `0 ≤ bit b ∧ bit b ≤ 1`. -/
theorem bit_bounds (b : Bool) : 0 ≤ bit b ∧ bit b ≤ 1 := by
  cases b <;> decide

/-- **Zero Count When a Predicate Never Fires (`count_eq_zero_of_forall_false`):**
if `∀ t < T, f t = false`, then `count f T = 0`. -/
theorem count_eq_zero_of_forall_false (f : Nat → Bool) :
    ∀ (T : Nat), (∀ t, t < T → f t = false) → count f T = 0
  | 0, _ => rfl
  | T + 1, hf => by
    have ih := count_eq_zero_of_forall_false f T (fun t ht => hf t (by omega))
    have hT : f T = false := hf T (Nat.lt_succ_self T)
    simp [count, ih, hT, bit]

/-- **Additivity of `count` Over Concatenated Time Horizons (`count_add`):**
for any stream `f : Nat → Bool` and horizons `T₀, T : Nat`,
`count f (T₀ + T) = count f T₀ + count (fun t => f (T₀ + t)) T`. -/
theorem count_add (f : Nat → Bool) (T₀ : Nat) :
    ∀ (T : Nat), count f (T₀ + T) = count f T₀ + count (fun t => f (T₀ + t)) T
  | 0 => by simp [count]
  | T + 1 => by
    rw [show T₀ + (T + 1) = (T₀ + T) + 1 by omega]
    simp only [count, count_add f T₀ T]
    omega

/-- **Shifted-Window Run-End Density Bound (`density_bound_window`):**
for any four neighboring Rule 30 columns `(c, r, s, u)`, any start time `T₀`, and any window
length `T`, the run-end density inequality holds over `[T₀, T₀ + T)`. -/
theorem density_bound_window (c r s u : Nat → Bool)
    (hr : ∀ t, r (t + 1) = rule (c t) (r t) (s t))
    (hs : ∀ t, s (t + 1) = rule (r t) (s t) (u t)) (T₀ T : Nat) :
    3 * count (fun t => c (T₀ + t)) T ≤
      (T : Int) + 5 * count (fun t => source (c (T₀ + t)) (r (T₀ + t))) T + 3 := by
  have hr' : ∀ t, r (T₀ + (t + 1)) = rule (c (T₀ + t)) (r (T₀ + t)) (s (T₀ + t)) := by
    intro t
    rw [show T₀ + (t + 1) = (T₀ + t) + 1 by omega]
    exact hr (T₀ + t)
  have hs' : ∀ t, s (T₀ + (t + 1)) = rule (r (T₀ + t)) (s (T₀ + t)) (u (T₀ + t)) := by
    intro t
    rw [show T₀ + (t + 1) = (T₀ + t) + 1 by omega]
    exact hs (T₀ + t)
  exact density_bound (fun t => c (T₀ + t)) (fun t => r (T₀ + t))
    (fun t => s (T₀ + t)) (fun t => u (T₀ + t)) hr' hs' T

/-- **One-Third Black-Cell Ceiling When No Run-End Source Fires (`count_le_of_source_false`):**
if `source (c t) (r t) = false` for all `t < T`, then `3 * count c T ≤ (T : Int) + 3`. -/
theorem count_le_of_source_false (c r s u : Nat → Bool)
    (hr : ∀ t, r (t + 1) = rule (c t) (r t) (s t))
    (hs : ∀ t, s (t + 1) = rule (r t) (s t) (u t))
    {T : Nat} (hzero : ∀ t, t < T → source (c t) (r t) = false) :
    3 * count c T ≤ (T : Int) + 3 := by
  have hd := density_bound c r s u hr hs T
  have hc0 := count_eq_zero_of_forall_false (fun t => source (c t) (r t)) T hzero
  rw [hc0] at hd
  omega

/-- **Quantitative Run-End Source Lower Bound From Black-Cell Count (`source_count_lower_bound`):**
for any four neighboring Rule 30 columns `(c, r, s, u)` and horizon `T`,
`3 * count c T - (T : Int) - 3 ≤ 5 * count (fun t => source (c t) (r t)) T`. -/
theorem source_count_lower_bound (c r s u : Nat → Bool)
    (hr : ∀ t, r (t + 1) = rule (c t) (r t) (s t))
    (hs : ∀ t, s (t + 1) = rule (r t) (s t) (u t)) (T : Nat) :
    3 * count c T - (T : Int) - 3 ≤ 5 * count (fun t => source (c t) (r t)) T := by
  have hd := density_bound c r s u hr hs T
  omega

/-- **Guaranteed Run-End Source Firing Under Black-Cell Excess (`exists_source_true_of_three_count_gt`):**
if `(T : Int) + 3 < 3 * count c T`, then there exists a tick `t < T` at which the run-end source
fires (`source (c t) (r t) = true`, i.e., `c t = true ∧ r t = false`). -/
theorem exists_source_true_of_three_count_gt (c r s u : Nat → Bool)
    (hr : ∀ t, r (t + 1) = rule (c t) (r t) (s t))
    (hs : ∀ t, s (t + 1) = rule (r t) (s t) (u t))
    {T : Nat} (hexcess : (T : Int) + 3 < 3 * count c T) :
    ∃ t, t < T ∧ source (c t) (r t) = true := by
  classical
  apply Classical.byContradiction
  intro hno
  have hzero : ∀ t, t < T → source (c t) (r t) = false := by
    intro t ht
    cases hs_val : source (c t) (r t)
    · rfl
    · exact False.elim (hno ⟨t, ht, hs_val⟩)
  have hle := count_le_of_source_false c r s u hr hs hzero
  omega

namespace Band

/-- **Arbitrary-Onset 8-Tick State Recovery (`Band.recover_at`):**
if two 4-cell band trajectories `x, y` satisfy the band evolution equations and have matching
3-source observations `obs (x (t₀ + t)) = obs (y (t₀ + t))` for the 8 ticks `t ≤ 7` starting at
`t₀`, then `x (t₀ + 1) = y (t₀ + 1)`. -/
theorem recover_at
    (x y : Nat → State) (cx cy vx vy wx wy : Nat → Bool)
    (hx : ∀ t, x (t + 1) = step (x t) (cx t) (vx t))
    (hy : ∀ t, y (t + 1) = step (y t) (cy t) (vy t))
    (hvx : ∀ t, vx (t + 1) = rule (bit (x t) 1) (vx t) (wx t))
    (hvy : ∀ t, vy (t + 1) = rule (bit (y t) 1) (vy t) (wy t))
    (t₀ : Nat)
    (ho : ∀ t, t ≤ 7 → obs (x (t₀ + t)) = obs (y (t₀ + t))) :
    x (t₀ + 1) = y (t₀ + 1) := by
  refine recover (fun t => x (t₀ + t)) (fun t => y (t₀ + t))
    (fun t => cx (t₀ + t)) (fun t => cy (t₀ + t))
    (fun t => vx (t₀ + t)) (fun t => vy (t₀ + t))
    (fun t => wx (t₀ + t)) (fun t => wy (t₀ + t))
    (fun t => ?_) (fun t => ?_) (fun t => ?_) (fun t => ?_) ho
  · rw [show t₀ + (t + 1) = (t₀ + t) + 1 by omega]; exact hx (t₀ + t)
  · rw [show t₀ + (t + 1) = (t₀ + t) + 1 by omega]; exact hy (t₀ + t)
  · rw [show t₀ + (t + 1) = (t₀ + t) + 1 by omega]; exact hvx (t₀ + t)
  · rw [show t₀ + (t + 1) = (t₀ + t) + 1 by omega]; exact hvy (t₀ + t)

/-- **Multi-Tick Sliding-Window State Recovery (`Band.recover_interval`):**
if `obs (x (t₀ + t)) = obs (y (t₀ + t))` holds across `t ≤ N + 7`, then `x (t₀ + 1 + k) = y (t₀ + 1 + k)`
for every `k ≤ N`. -/
theorem recover_interval
    (x y : Nat → State) (cx cy vx vy wx wy : Nat → Bool)
    (hx : ∀ t, x (t + 1) = step (x t) (cx t) (vx t))
    (hy : ∀ t, y (t + 1) = step (y t) (cy t) (vy t))
    (hvx : ∀ t, vx (t + 1) = rule (bit (x t) 1) (vx t) (wx t))
    (hvy : ∀ t, vy (t + 1) = rule (bit (y t) 1) (vy t) (wy t))
    {t₀ N : Nat}
    (ho : ∀ t, t ≤ N + 7 → obs (x (t₀ + t)) = obs (y (t₀ + t))) :
    ∀ k, k ≤ N → x (t₀ + 1 + k) = y (t₀ + 1 + k) := by
  intro k hk
  have hrec := recover_at x y cx cy vx vy wx wy hx hy hvx hvy (t₀ + k) (fun t ht => by
    rw [show t₀ + k + t = t₀ + (k + t) by omega]
    exact ho (k + t) (by omega))
  rwa [show t₀ + k + 1 = t₀ + 1 + k by omega] at hrec

end Band

end Ruliology.CellularAutomata.Rule30SourceObservables
