module

public import Ruliology.CellularAutomata.Rule30RotationBlocks
public import Ruliology.CellularAutomata.Rule30FiniteMaskedJen

/-!
# Blocks in the order of a rotation at every phase, beside a Rule 30 clock

Turn a circle by a fixed irrational angle and note at each step whether the point is in a fixed arc, now from any
starting phase. Let each of the two answers stand for a block of readings, and set the blocks one after another in
the order of the answers. `Rule30RotationBlocks` excludes such a concatenation beside an alternating column when the
start lies on the orbit of an end of the arc. This module treats every phase, for angles with arbitrarily large
Farey neighbours whose denominator ratio is above six by a fixed positive margin.

**No real numbers.** As in `Rule30RotationBlocks`, `IrrationalLine g` stands for the floors of the multiples of the
angle, and `PhaseLine g f` for the floors `⌊θ + t α⌋` of a line of the same slope. The arc `[0, γ)` at phase `θ` is
read off two such lines `f₁ t = ⌊θ + t α⌋` and `f₂ t = ⌊θ + t α - γ⌋`, which differ by one exactly when the point is in
the arc (`arcWord`).

* `three_failures`: a letter that differs from the letter `d` later marks a failure of one of the two lines, and the
  failures of one line are at least `D` apart (`Farey.gap`). So three such letters span at least `D`.
* `repeat_of_span`: then one of three greedy trials finds the word repeating at lag `d` for long enough.
* `above_six_of_envelopes`: if the reading clock of the blocks has linear envelopes as close as the margin over six
  asks, the right neighbour of an alternating column in a row with a leftmost black cell does not read the
  concatenation, at any phase and for any arc. Jen's theorem through one finite window concludes
  (`excludes_blocks`, `visible_window`).
* `equal_envelopes`, `above_six_equal`: blocks of one length have exact envelopes, so they are excluded outright.
* `sixes_line`, `sixes_farey`, `sixes_equal`: the angle `√10 - 3 = [0; 6, 6, …]` has the required neighbours.

**Blocks of different lengths.** The two lines are at most one apart (`between`, the integer form of `0 < γ < 1`).
* `window_drift`, `block_balance`: for a second pair of Farey neighbours `u / b`, `U / d` of the angle, the number of
  steps in the arc among `b` consecutive ones changes by at most two over `d` steps (`Farey.gap` again). So two
  stretches of `n` steps, at most `k d` apart, differ in that number by at most `2 k (n / b) + b`.
* `farey_level`: past some level, for every level `M` the angle has Farey neighbours with denominators at least a
  given bound, at most `M`, and adding to more than `M`.
* `above_six`: with the second pair at the level `q / (8 L gear)`, the imbalance of the readings fits in the surplus.
  So two nonempty blocks of any lengths are excluded, at any phase and for any arc, with no further hypothesis.
* `sixes_excluded`: the same at `√10 - 3`.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30RotationFreePhase

open Rule30RotationBlocks
open Rule30Realization (evol)

/-! ### The arc at any phase -/

/-- The letter of the arc: two lines of one slope, at most one apart, differ by one inside the arc. -/
def arcWord (f₁ f₂ : Nat → Int) (t : Nat) : Bool := decide (f₁ t - f₂ t = 1)

/-- A letter that differs from the letter `d` later marks a failure of one of the two lines to copy over `d`. -/
theorem fails_of_differs {f₁ f₂ : Nat → Int} (u : Int) {d t : Nat}
    (h : arcWord f₁ f₂ (t + d) ≠ arcWord f₁ f₂ t) :
    f₁ (t + d) ≠ f₁ t + u ∨ f₂ (t + d) ≠ f₂ t + u := by
  by_cases h₁ : f₁ (t + d) = f₁ t + u
  · by_cases h₂ : f₂ (t + d) = f₂ t + u
    · exfalso
      apply h
      unfold arcWord
      rw [h₁, h₂, show f₁ t + u - (f₂ t + u) = f₁ t - f₂ t by omega]
    · exact Or.inr h₂
  · exact Or.inl h₁

variable {g f₁ f₂ : Nat → Int}

/-- **Three letters that differ at lag `d` span at least `D`.** Each marks a failure of one of the two lines, and two
failures of one line are at least `D` apart. -/
theorem three_failures (hg : IrrationalLine g) (h₁ : PhaseLine g f₁) (h₂ : PhaseLine g f₂)
    {u U : Int} {d D : Nat} (F : Farey g u d U D) {x y z : Nat} (xy : x < y) (yz : y < z) (short : z < x + D)
    (dx : arcWord f₁ f₂ (x + d) ≠ arcWord f₁ f₂ x)
    (dy : arcWord f₁ f₂ (y + d) ≠ arcWord f₁ f₂ y)
    (dz : arcWord f₁ f₂ (z + d) ≠ arcWord f₁ f₂ z) : False := by
  rcases fails_of_differs u dx with a | a <;> rcases fails_of_differs u dy with b | b <;>
    rcases fails_of_differs u dz with c | c
  · have := Farey.gap hg h₁ F a b xy; omega
  · have := Farey.gap hg h₁ F a b xy; omega
  · have := Farey.gap hg h₁ F a c (by omega); omega
  · have := Farey.gap hg h₂ F b c yz; omega
  · have := Farey.gap hg h₁ F b c yz; omega
  · have := Farey.gap hg h₂ F a c (by omega); omega
  · have := Farey.gap hg h₂ F a b xy; omega
  · have := Farey.gap hg h₂ F a b xy; omega

/-! ### A repeat from three trials -/

/-- If no three letters that differ at lag `q` lie within six times the cutoff, the lag and the surplus, one of three
greedy trials finds the word repeating at lag `q` from a start `a ≥ H` for `a + q + extra` letters. -/
theorem repeat_of_span {α : Type} (c : Nat → α) (H q extra : Nat)
    (separated : ∀ u v z, u < v → v < z → z - u ≤ 6 * (H + q + extra) →
      c (u + q) ≠ c u → c (v + q) ≠ c v → c (z + q) ≠ c z → False) :
    ∃ a, H ≤ a ∧ 2 * a + q + extra ≤ 8 * H + 7 * (q + extra) ∧
      ∀ s, s < a + q + extra → c (a + s) = c (a + q + s) := by
  classical
  apply Classical.byContradiction
  intro noRepeat
  have bad (a : Nat) (ha : H ≤ a) (endFits : 2 * a + q + extra ≤ 8 * H + 7 * (q + extra)) :
      ∃ t, a ≤ t ∧ t < 2 * a + q + extra ∧ c (t + q) ≠ c t := by
    apply Classical.byContradiction
    intro noBreak
    apply noRepeat
    refine ⟨a, ha, endFits, fun s hs => ?_⟩
    apply Classical.byContradiction
    intro different
    apply noBreak
    refine ⟨a + s, by omega, by omega, fun h => different ?_⟩
    rw [show a + q + s = a + s + q by omega]
    exact h.symm
  obtain ⟨u, hu, eu, du⟩ := bad H (by omega) (by omega)
  obtain ⟨v, hv, ev, dv⟩ := bad (u + 1) (by omega) (by omega)
  obtain ⟨z, hz, ez, dz⟩ := bad (v + 1) (by omega) (by omega)
  exact separated u v z (by omega) (by omega) (by omega) du dv dz

/-! ### Jen through one finite window -/

/-- Two equal stretches of readings beside an alternating column, the second starting late enough, contradict the
finite-left masked Jen theorem. -/
theorem visible_window (x : Int → Bool) (lo i : Int) (leftBlack : x lo = true)
    (leftWhite : ∀ j < lo, x j = false) (start a b l : Nat) (ab : a < b)
    (clock : ∀ t, evol x (start + t) i = decide (t % 2 = 1))
    (reachable : 0 ≤ i - lo + ((start + 2 * b : Nat) : Int))
    (long : i - lo + ((start + 2 * b : Nat) : Int) ≤ 2 * (l : Int))
    (same : ∀ s, s < l → evol x (start + 2 * (a + s)) (i + 1) = evol x (start + 2 * (b + s)) (i + 1)) : False := by
  let m := (i - lo + ((start + 2 * b : Nat) : Int)).toNat
  have edge : (m : Int) = i - lo + ((start + 2 * b : Nat) : Int) := Int.toNat_of_nonneg reachable
  apply Rule30FiniteMaskedJen.window_jen_col leftBlack leftWhite (t₁ := start + 2 * a)
    (t₂ := start + 2 * b) (i := i) m (by omega) (by omega)
  · intro s _
    rw [Nat.add_assoc, Nat.add_assoc, clock, clock]
    have parity : (2 * a + s) % 2 = (2 * b + s) % 2 := by omega
    rw [parity]
  · intro s hs
    unfold Rule30FiniteMaskedJen.orCol
    simp only [Nat.add_assoc, clock]
    by_cases parity : s % 2 = 0
    · have ha : (2 * a + s) % 2 = 0 := by omega
      have hb : (2 * b + s) % 2 = 0 := by omega
      simp only [ha, hb, Nat.reduceEqDiff, decide_false, Bool.false_or]
      have e := same (s / 2) (by omega)
      rwa [show 2 * (a + s / 2) = 2 * a + s by omega, show 2 * (b + s / 2) = 2 * b + s by omega] at e
    · have ha : (2 * a + s) % 2 = 1 := by omega
      have hb : (2 * b + s) % 2 = 1 := by omega
      simp [ha, hb]

/-- A coded word whose repeats outlast their second start by any amount, in readings, is not read beside an
alternating column. -/
theorem excludes_blocks {α : Type} (c : Nat → α) (len : α → Nat) (positive : ∀ v, 1 ≤ len v)
    (bits : α → Nat → Bool)
    (reps : ∀ H C : Nat, ∃ a b l, H ≤ a ∧ a < b ∧ C ≤ b - a ∧
      (∀ s, s < l → c (a + s) = c (b + s)) ∧
      total (fun t => len (c t)) a + total (fun t => len (c t)) b + C ≤ total (fun t => len (c t)) (a + l))
    (x : Int → Bool) (lo i : Int) (leftBlack : x lo = true)
    (leftWhite : ∀ j < lo, x j = false) (start cutoff : Nat)
    (clock : ∀ t, evol x (start + t) i = decide (t % 2 = 1))
    (reads : ∀ n y, y < len (c n) → cutoff ≤ total (fun t => len (c t)) n + y →
      evol x (start + 2 * (total (fun t => len (c t)) n + y)) (i + 1) = bits (c n) y) : False := by
  let w := fun t => len (c t)
  have pos : ∀ t, 1 ≤ w t := fun t => positive _
  let C := (lo - i).toNat + (i - lo + (start : Int)).toNat + 1
  obtain ⟨a, b, l, late, ab, lag, agree, room⟩ := reps cutoff C
  have bound (t : Nat) : t ≤ total w t := by simpa [total] using le_total w pos 0 t
  have grows := le_total w pos a (b - a)
  rw [Nat.add_sub_of_le (Nat.le_of_lt ab)] at grows
  change total w a + total w b + C ≤ total w (a + l) at room
  apply visible_window x lo i leftBlack leftWhite start (total w a) (total w b)
    (total w (a + l) - total w a) (by omega) clock
  · have hb := bound b
    dsimp [C] at lag
    omega
  · dsimp [C] at room
    omega
  · intro s hs
    obtain ⟨j, hj, y, hy, offset⟩ := locate w a s l (by omega)
    have eqw (e : Nat) (h : e < l) : w (a + e) = w (b + e) := congrArg len (agree e h)
    have hy' : y < w (b + j) := eqw j hj ▸ hy
    have shift := total_shift w a b j (fun e he => eqw e (by omega))
    have other : total w b + s = total w (b + j) + y := by omega
    have cut := bound a
    rw [offset, other, reads _ _ hy (by change cutoff ≤ total w (a + j) + y; omega),
      reads _ _ hy' (by change cutoff ≤ total w (b + j) + y; omega), agree j hj]

/-! ### Envelopes of the reading clock -/

/-- Linear envelopes for the reading clock: the readings of the first `n` letters lie between lines of slopes
`low / den` and `high / den`, up to `err`, and the slopes differ by at most `1 / (30 gear)` of the lower one. -/
def Envelopes (w : Nat → Nat) (gear : Nat) : Prop :=
  ∃ den low high err : Nat, 0 < den ∧ low ≤ high ∧ 30 * gear * (high - low) ≤ low ∧
    (∀ n, low * n ≤ den * total w n + err) ∧ ∀ n, den * total w n ≤ high * n + err

/-- Envelopes turn a surplus of letters into a surplus of readings. -/
theorem slack_of_envelopes (w : Nat → Nat) {den low high err a b l : Nat}
    (positive : 0 < den)
    (lower : ∀ n, low * n ≤ den * total w n + err)
    (upper : ∀ n, den * total w n ≤ high * n + err)
    (margin : high * (a + b) ≤ low * (a + l)) :
    total w a + total w b ≤ total w (a + l) + 3 * err := by
  have gain : 3 * err ≤ den * (3 * err) := by
    simpa using Nat.mul_le_mul_right (3 * err) (show 1 ≤ den by omega)
  apply Nat.le_of_mul_le_mul_left _ positive
  simp only [Nat.mul_add] at margin ⊢
  have first := upper a
  have second := upper b
  have finish := lower (a + l)
  rw [Nat.mul_add] at finish
  omega

theorem total_const (L n : Nat) : total (fun _ => L) n = L * n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [total_succ, ih, Nat.mul_succ]

/-- Blocks of one length have exact envelopes. -/
theorem equal_envelopes (L gear : Nat) : Envelopes (fun _ => L) gear :=
  ⟨1, L, L, 0, by omega, Nat.le_refl _, by simp, fun n => by rw [total_const]; omega,
    fun n => by rw [total_const]; omega⟩

/-! ### Every phase above ratio six -/

/-- **Every phase, every arc, any two nonempty blocks**, given envelopes of their reading clock. The angle needs, for
one positive `gear`, arbitrarily large Farey neighbours `u / d` and `U / D` with `(6 gear + 16) d ≤ gear D`. -/
theorem above_six_of_envelopes (hg : IrrationalLine g) (h₁ : PhaseLine g f₁) (h₂ : PhaseLine g f₂)
    (len : Bool → Nat) (positive : ∀ b, 1 ≤ len b) (bits : Bool → Nat → Bool)
    {gear : Nat} (gearPos : 0 < gear)
    (env : Envelopes (fun t => len (arcWord f₁ f₂ t)) (2 * gear))
    (approximations : ∀ N, ∃ (u : Int) (d : Nat) (U : Int) (D : Nat),
      N ≤ d ∧ (6 * gear + 16) * d ≤ gear * D ∧ Farey g u d U D)
    (x : Int → Bool) (lo i : Int) (leftBlack : x lo = true)
    (leftWhite : ∀ j < lo, x j = false) (start cutoff : Nat)
    (clock : ∀ t, evol x (start + t) i = decide (t % 2 = 1))
    (reads : ∀ n y, y < len (arcWord f₁ f₂ n) →
      cutoff ≤ total (fun t => len (arcWord f₁ f₂ t)) n + y →
      evol x (start + 2 * (total (fun t => len (arcWord f₁ f₂ t)) n + y)) (i + 1) =
        bits (arcWord f₁ f₂ n) y) : False := by
  let c := arcWord f₁ f₂
  let w := fun t => len (c t)
  obtain ⟨den, low, high, err, denPos, order, accurate, lower, upper⟩ := env
  apply excludes_blocks c len positive bits ?_ x lo i leftBlack leftWhite start cutoff clock reads
  intro H N
  obtain ⟨u, q, U, Q, large, ratio, F⟩ := approximations (N + 8 * gear * H + 2 * gear + gear * (N + 3 * err))
  let extra := q / gear
  have side : 8 * gear * H ≤ q := by omega
  have extraPos : 1 ≤ extra := Nat.div_pos (by omega) gearPos
  have below : gear * extra ≤ q := Nat.mul_div_le q gear
  have above : q ≤ 2 * gear * extra := by
    have decompose : gear * extra + q % gear = q := Nat.div_add_mod q gear
    have rem := Nat.mod_lt q gearPos
    have atLeast := Nat.mul_le_mul_left gear extraPos
    have e : 2 * gear * extra = gear * extra + gear * extra := by grind
    omega
  have span : 6 * (H + q + 2 * extra) < Q := by
    apply Nat.lt_of_mul_lt_mul_left (a := gear)
    have e₁ : gear * (6 * (H + q + 2 * extra)) = 6 * (gear * H) + 6 * (gear * q) + 12 * (gear * extra) := by grind
    have e₂ : (6 * gear + 16) * q = 6 * (gear * q) + 16 * q := by grind
    have e₃ : 8 * gear * H = 8 * (gear * H) := by grind
    omega
  obtain ⟨a, late, finish, agree⟩ := repeat_of_span c H q (2 * extra) (fun u' v z uv vz short =>
    three_failures hg h₁ h₂ F uv vz (by omega))
  refine ⟨a, a + q, a + q + 2 * extra, late, by omega, by omega, agree, ?_⟩
  have startBound : 8 * H ≤ q := by
    have mult := Nat.mul_le_mul_right (8 * H) (show 1 ≤ gear by omega)
    have e : gear * (8 * H) = 8 * gear * H := by grind
    omega
  have endBound : a + (a + q) ≤ 22 * q := by
    have e : extra ≤ q := Nat.div_le_self q gear
    omega
  have gain : (high - low) * (a + (a + q)) ≤ low * extra := by
    have s₁ := Nat.mul_le_mul_left (high - low) endBound
    have s₂ := Nat.mul_le_mul_left (high - low) (Nat.mul_le_mul_left 22 above)
    have s₃ : 30 * (2 * gear) * (high - low) ≤ low := accurate
    have s₄ := Nat.mul_le_mul_right extra s₃
    have e₁ : (high - low) * (22 * (2 * gear * extra)) = 44 * (gear * (high - low)) * extra := by grind
    have e₂ : 30 * (2 * gear) * (high - low) * extra = 60 * (gear * (high - low)) * extra := by grind
    have e₃ : 44 * (gear * (high - low)) * extra ≤ 60 * (gear * (high - low)) * extra :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
    omega
  have margin : high * (a + (a + q)) ≤ low * (a + (a + q + extra)) := by
    have e₁ : high * (a + (a + q)) = (high - low) * (a + (a + q)) + low * (a + (a + q)) := by
      rw [← Nat.add_mul, Nat.sub_add_cancel order]
    have e₂ : low * (a + (a + q + extra)) = low * (a + (a + q)) + low * extra := by
      rw [show a + (a + q + extra) = (a + (a + q)) + extra by omega, Nat.mul_add]
    omega
  have slack := slack_of_envelopes w denPos lower upper margin
  have reserve : N + 3 * err ≤ extra := (Nat.le_div_iff_mul_le gearPos).mpr (by
    rw [Nat.mul_comm]; omega)
  have more := le_total w (fun t => positive (c t)) (a + (a + q + extra)) extra
  rw [show a + (a + q + extra) + extra = a + (a + q + 2 * extra) by omega] at more
  change total w a + total w (a + q) + N ≤ total w (a + (a + q + 2 * extra))
  omega

/-- **Blocks of one length**, at every phase and for every arc, above ratio six. -/
theorem above_six_equal (hg : IrrationalLine g) (h₁ : PhaseLine g f₁) (h₂ : PhaseLine g f₂)
    (L : Nat) (hL : 1 ≤ L) (bits : Bool → Nat → Bool)
    {gear : Nat} (gearPos : 0 < gear)
    (approximations : ∀ N, ∃ (u : Int) (d : Nat) (U : Int) (D : Nat),
      N ≤ d ∧ (6 * gear + 16) * d ≤ gear * D ∧ Farey g u d U D)
    (x : Int → Bool) (lo i : Int) (leftBlack : x lo = true)
    (leftWhite : ∀ j < lo, x j = false) (start cutoff : Nat)
    (clock : ∀ t, evol x (start + t) i = decide (t % 2 = 1))
    (reads : ∀ n y, y < L → cutoff ≤ L * n + y →
      evol x (start + 2 * (L * n + y)) (i + 1) = bits (arcWord f₁ f₂ n) y) : False := by
  apply above_six_of_envelopes hg h₁ h₂ (fun _ => L) (fun _ => hL) bits gearPos (equal_envelopes L _)
    approximations x lo i leftBlack leftWhite start cutoff clock
  intro n y hy hc
  have e : total (fun t => (fun _ => L) (arcWord f₁ f₂ t)) n = L * n := total_const L n
  rw [e] at hc ⊢
  exact reads n y hy hc

/-! ### The angle √10 − 3 -/

theorem ten_irrational (p q : Nat) (hq : 1 ≤ q) : p * p ≠ 10 * (q * q) := by
  induction q using Nat.strongRecOn generalizing p with
  | ind q ih =>
    intro h
    obtain ⟨k, rfl⟩ : ∃ k, p = 2 * k := by
      rcases Nat.mod_two_eq_zero_or_one p with e | e
      · exact ⟨p / 2, by omega⟩
      · obtain ⟨k, rfl⟩ : ∃ k, p = 2 * k + 1 := ⟨p / 2, by omega⟩
        grind
    obtain ⟨m, rfl⟩ : ∃ m, q = 2 * m := by
      rcases Nat.mod_two_eq_zero_or_one q with e | e
      · exact ⟨q / 2, by omega⟩
      · obtain ⟨m, rfl⟩ : ∃ m, q = 2 * m + 1 := ⟨q / 2, by omega⟩
        grind
    have h' : k * k = 10 * (m * m) := by grind
    exact ih m (by omega) k (by omega) h'

/-- The floors of the multiples of `√10 - 3`. -/
def sixesFloor (t : Nat) : Int := (isqrt (10 * (t * t)) : Int) - 3 * t

theorem sixes_line : IrrationalLine sixesFloor := by
  have base := sqrt_line 10 ten_irrational
  exact ⟨fun m n hm hn => by
      have := base.floors m n hm hn
      unfold sixesFloor
      grind,
    fun p q hq => by
      obtain ⟨n, hn, h⟩ := base.irrational (p + 3 * q) q hq
      refine ⟨n, hn, ?_⟩
      unfold sixesFloor
      rcases h with h | h
      · left; grind
      · right; grind⟩

theorem isqrt_eq {n a : Nat} (lo : a * a ≤ n) (hi : n < (a + 1) * (a + 1)) : isqrt n = a := by
  obtain ⟨b₁, b₂⟩ := isqrt_spec n
  rcases Nat.lt_trichotomy (isqrt n) a with h | h | h
  · have : (isqrt n + 1) * (isqrt n + 1) ≤ a * a := Nat.mul_le_mul (by omega) (by omega)
    omega
  · exact h
  · have : (a + 1) * (a + 1) ≤ isqrt n * isqrt n := Nat.mul_le_mul (by omega) (by omega)
    omega

theorem sixes_floor_of {q a : Nat} (lo : a * a ≤ 10 * (q * q)) (hi : 10 * (q * q) < (a + 1) * (a + 1)) :
    sixesFloor q = (a : Int) - 3 * q := by
  unfold sixesFloor
  rw [isqrt_eq lo hi]

/-- Consecutive convergents `p / q` of `√10 - 3`, from `1 / 6` by `(p, q) ↦ (q, 6 q + p)`. The sign of
`(3 q + p)² - 10 q²`, one or minus one, says on which side of the angle `p / q` lies. -/
theorem six_pairs (N : Nat) :
    ∃ p q : Nat, N ≤ q ∧ 1 ≤ p ∧ p ≤ q ∧ q ≤ 7 * p ∧
      ((3 * q + p) * (3 * q + p) + 1 = 10 * (q * q) ∨ (3 * q + p) * (3 * q + p) = 10 * (q * q) + 1) := by
  induction N with
  | zero => exact ⟨1, 6, by omega, by omega, by omega, by omega, Or.inr (by decide)⟩
  | succ N ih =>
    obtain ⟨p, q, large, pos, order, upper, side⟩ := ih
    refine ⟨q, 6 * q + p, by omega, by omega, by omega, by omega, ?_⟩
    rcases side with h | h
    · right; grind
    · left; grind

/-- Large Farey neighbours of `√10 - 3`, with ratio above six by the margin of `gear = 128`. -/
theorem sixes_farey (N : Nat) : ∃ (u : Int) (d : Nat) (U : Int) (D : Nat),
    N ≤ d ∧ (6 * 128 + 16) * d ≤ 128 * D ∧ Farey sixesFloor u d U D := by
  obtain ⟨p, q, large, pos, order, upper, side⟩ := six_pairs N
  refine ⟨p, q, q, 6 * q + p, large, by omega, by omega, by omega, ?_⟩
  rcases side with h | h
  · -- `p / q` below the angle, `q / (6 q + p)` above it
    have hD : (3 * (6 * q + p) + q) * (3 * (6 * q + p) + q) = 10 * ((6 * q + p) * (6 * q + p)) + 1 := by grind
    obtain ⟨a, ha⟩ : ∃ a, 3 * (6 * q + p) + q = a + 1 := ⟨3 * (6 * q + p) + q - 1, by omega⟩
    rw [ha] at hD
    have e₁ : sixesFloor q = p := by
      rw [sixes_floor_of (a := 3 * q + p) (by omega) (by grind)]
      omega
    have e₂ : sixesFloor (6 * q + p) = (q : Int) - 1 := by
      rw [sixes_floor_of (a := a) (by grind) (by omega)]
      omega
    refine Or.inl ⟨?_, ?_, ?_⟩
    · have := floor_above sixes_line (t := q) (by omega)
      rwa [e₁] at this
    · have := floor_below sixes_line (t := 6 * q + p) (by omega)
      rw [e₂, show -((q : Int) - 1 + 1) = -(q : Int) by omega] at this
      exact this
    · have n : q * q = p * (6 * q + p) + 1 := by grind
      have z : ((q * q : Nat) : Int) = ((p * (6 * q + p) + 1 : Nat) : Int) := congrArg _ n
      push_cast at z ⊢
      omega
  · -- `p / q` above the angle, `q / (6 q + p)` below it
    have hD : (3 * (6 * q + p) + q) * (3 * (6 * q + p) + q) + 1 = 10 * ((6 * q + p) * (6 * q + p)) := by grind
    obtain ⟨a, ha⟩ : ∃ a, 3 * q + p = a + 1 := ⟨3 * q + p - 1, by omega⟩
    rw [ha] at h
    have e₁ : sixesFloor q = (p : Int) - 1 := by
      rw [sixes_floor_of (a := a) (by grind) (by omega)]
      omega
    have e₂ : sixesFloor (6 * q + p) = q := by
      rw [sixes_floor_of (a := 3 * (6 * q + p) + q) (by omega) (by grind)]
      omega
    refine Or.inr ⟨?_, ?_, ?_⟩
    · have := floor_below sixes_line (t := q) (by omega)
      rw [e₁, show -((p : Int) - 1 + 1) = -(p : Int) by omega] at this
      exact this
    · have := floor_above sixes_line (t := 6 * q + p) (by omega)
      rwa [e₂] at this
    · have n : p * (6 * q + p) = q * q + 1 := by grind
      have z : ((p * (6 * q + p) : Nat) : Int) = ((q * q + 1 : Nat) : Int) := congrArg _ n
      push_cast at z ⊢
      omega

/-- **The angle `√10 - 3`**: blocks of one length in the order of any arc, from any phase, are not read beside an
alternating column. -/
theorem sixes_equal (h₁ : PhaseLine sixesFloor f₁) (h₂ : PhaseLine sixesFloor f₂)
    (L : Nat) (hL : 1 ≤ L) (bits : Bool → Nat → Bool)
    (x : Int → Bool) (lo i : Int) (leftBlack : x lo = true)
    (leftWhite : ∀ j < lo, x j = false) (start cutoff : Nat)
    (clock : ∀ t, evol x (start + t) i = decide (t % 2 = 1))
    (reads : ∀ n y, y < L → cutoff ≤ L * n + y →
      evol x (start + 2 * (L * n + y)) (i + 1) = bits (arcWord f₁ f₂ n) y) : False :=
  above_six_equal sixes_line h₁ h₂ L hL bits (gear := 128) (by decide) sixes_farey x lo i leftBlack leftWhite
    start cutoff clock reads

/-! ### Window counts at a second scale

For blocks of different lengths the reading clock is not linear. Its rate is read off windows of `b` letters, for a
second Farey pair `u₀ / b`, `U₀ / d` chosen for the scale of the repeat: each line fails to copy over `b` at times at
least `d` apart, so the count of letters inside the arc in a window of `b` moves by at most two per `d` steps. -/

/-- The sum of `φ` over `[x, x + n)`. -/
def isum (φ : Nat → Int) (x : Nat) : Nat → Int
  | 0 => 0
  | n + 1 => isum φ x n + φ (x + n)

theorem isum_add (φ : Nat → Int) (x m n : Nat) : isum φ x (m + n) = isum φ x m + isum φ (x + m) n := by
  induction n with
  | zero => simp [isum]
  | succ n ih =>
    show isum φ x (m + n) + φ (x + (m + n)) = isum φ x m + (isum φ (x + m) n + φ (x + m + n))
    rw [ih, Nat.add_assoc x m n]
    omega

theorem isum_telescope (F : Nat → Int) (x n : Nat) : isum (fun t => F (t + 1) - F t) x n = F (x + n) - F x := by
  induction n with
  | zero => simp [isum]
  | succ n ih =>
    show isum (fun t => F (t + 1) - F t) x n + (F (x + n + 1) - F (x + n)) = F (x + (n + 1)) - F x
    rw [ih, show x + (n + 1) = x + n + 1 by omega]
    omega

theorem isum_sub (φ χ : Nat → Int) (x n : Nat) : isum (fun t => φ t - χ t) x n = isum φ x n - isum χ x n := by
  induction n with
  | zero => simp [isum]
  | succ n ih =>
    show isum (fun t => φ t - χ t) x n + (φ (x + n) - χ (x + n)) = isum φ x n + φ (x + n) - (isum χ x n + χ (x + n))
    rw [ih]
    omega

theorem isum_congr {φ χ : Nat → Int} (h : ∀ t, φ t = χ t) (x n : Nat) : isum φ x n = isum χ x n := by
  rw [show φ = χ from funext h]

theorem isum_bounds (φ : Nat → Int) (h : ∀ t, 0 ≤ φ t ∧ φ t ≤ 1) (x n : Nat) : 0 ≤ isum φ x n ∧ isum φ x n ≤ n := by
  induction n with
  | zero => simp [isum]
  | succ n ih =>
    show 0 ≤ isum φ x n + φ (x + n) ∧ isum φ x n + φ (x + n) ≤ ((n + 1 : Nat) : Int)
    have := h (x + n)
    push_cast
    omega

/-- On an interval shorter than the spacing of its nonzero terms, a sum has at most one nonzero term. -/
theorem isum_chunk (φ : Nat → Int) (s₀ : Nat)
    (sparse : ∀ t t', t < t' → φ t ≠ 0 → φ t' ≠ 0 → t + s₀ ≤ t') (x : Nat) :
    ∀ d, d ≤ s₀ → isum φ x d = 0 ∨ ∃ t, isum φ x d = φ t := by
  intro d
  induction d with
  | zero => intro _; left; rfl
  | succ d ih =>
    intro hd
    have expand : isum φ x (d + 1) = isum φ x d + φ (x + d) := rfl
    rcases Classical.em (φ (x + d) = 0) with z | z
    · rcases ih (by omega) with h | ⟨t, h⟩
      · left; rw [expand, h, z]; rfl
      · right; exact ⟨t, by rw [expand, h, z]; omega⟩
    · right
      refine ⟨x + d, ?_⟩
      rw [expand]
      suffices isum φ x d = 0 by rw [this]; omega
      have early : ∀ e, e ≤ d → isum φ x e = 0 := by
        intro e
        induction e with
        | zero => intro _; rfl
        | succ e ihe =>
          intro he
          show isum φ x e + φ (x + e) = 0
          rw [ihe (by omega)]
          rcases Classical.em (φ (x + e) = 0) with ze | ze
          · rw [ze]; rfl
          · have := sparse (x + e) (x + d) (by omega) ze z; omega
      exact early d (Nat.le_refl _)

/-- **Sparse sums.** Terms between `-1` and `1` whose nonzero ones are `s₀` apart sum, over `k s₀` places, to at
most `k` in size. -/
theorem isum_sparse (φ : Nat → Int) (s₀ : Nat) (bound : ∀ t, -1 ≤ φ t ∧ φ t ≤ 1)
    (sparse : ∀ t t', t < t' → φ t ≠ 0 → φ t' ≠ 0 → t + s₀ ≤ t') :
    ∀ k x d, d ≤ k * s₀ → -(k : Int) ≤ isum φ x d ∧ isum φ x d ≤ k := by
  intro k
  induction k with
  | zero =>
    intro x d hd
    have : d = 0 := by rw [Nat.zero_mul] at hd; omega
    subst this
    simp [isum]
  | succ k ih =>
    intro x d hd
    rcases Nat.le_total d s₀ with h | h
    · rcases isum_chunk φ s₀ sparse x d h with e | ⟨t, e⟩
      · rw [e]; omega
      · rw [e]; have := bound t; omega
    · obtain ⟨r, rfl⟩ : ∃ r, d = s₀ + r := ⟨d - s₀, by omega⟩
      rw [isum_add]
      have rest := ih (x + s₀) r (by rw [Nat.succ_mul] at hd; omega)
      rcases isum_chunk φ s₀ sparse x s₀ (Nat.le_refl _) with e | ⟨t, e⟩
      · rw [e]; omega
      · rw [e]; have := bound t; omega

/-- The floors of the multiples are additive up to one. -/
theorem floor_add (hg : IrrationalLine g) {m n : Nat} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    g m + g n ≤ g (m + n) ∧ g (m + n) ≤ g m + g n + 1 := by
  constructor
  · apply le_floor hg (t := m + n) (by omega)
    have a := above_add hg (floor_above hg hm) (floor_above hg hn)
    rwa [show ((m : Int) + n) = ((m + n : Nat) : Int) by omega] at a
  · have a := above_add hg (floor_below hg hm) (floor_below hg hn)
    rw [show -(g m + 1) + -(g n + 1) = -(g m + g n + 2) by omega,
      show -(m : Int) + -(n : Int) = -((m + n : Nat) : Int) by omega] at a
    have := floor_lt hg (t := m + n) (by omega) a
    omega

/-- The floor at a Farey denominator is its numerator or one less. -/
theorem farey_floor (hg : IrrationalLine g) {u U : Int} {d D : Nat} (F : Farey g u d U D) (hD : 2 ≤ D) :
    u - 1 ≤ g d ∧ g d ≤ u := by
  have step := Farey.step hg F 1 (by omega) (by omega)
  have add := floor_add hg (m := 1) (n := d) (by omega) F.1
  omega

/-- Farey neighbours at the level of a large `M`: both denominators at least `K`, at most `M`, and adding to more
than `M`. -/
theorem farey_level (hg : IrrationalLine g) (K : Nat) :
    ∃ M₀, ∀ M, M₀ ≤ M → ∃ (u : Int) (b : Nat) (U : Int) (d : Nat),
      Farey g u b U d ∧ K ≤ b ∧ K ≤ d ∧ b ≤ M ∧ d ≤ M ∧ M < b + d := by
  obtain ⟨u₀, b₀, U₀, d₀, hb, hd, F₀⟩ := exists_farey hg (K + 1)
  refine ⟨b₀ + d₀, fun M hM => ?_⟩
  have descend : ∀ fuel, ∀ (u : Int) (b : Nat) (U : Int) (d : Nat), Farey g u b U d → K + 1 ≤ b → K + 1 ≤ d →
      b ≤ M → d ≤ M → M + 1 - (b + d) ≤ fuel →
      ∃ (u : Int) (b : Nat) (U : Int) (d : Nat), Farey g u b U d ∧ K ≤ b ∧ K ≤ d ∧ b ≤ M ∧ d ≤ M ∧ M < b + d := by
    intro fuel
    induction fuel with
    | zero => intro u b U d F hb hd bM dM f; exact ⟨u, b, U, d, F, by omega, by omega, bM, dM, by omega⟩
    | succ fuel ih =>
      intro u b U d F hb hd bM dM f
      rcases Nat.lt_or_ge M (b + d) with big | small
      · exact ⟨u, b, U, d, F, by omega, by omega, bM, dM, big⟩
      · rcases F.mediant hg with m | m
        · exact ih u b (u + U) (b + d) m hb (by omega) bM small (by omega)
        · exact ih (u + U) (b + d) U d m (by omega) hd small dM (by omega)
  exact descend (M + 1) u₀ b₀ U₀ d₀ F₀ hb hd (by omega) (by omega) (by omega)

/-- The letters inside the arc among the `n` letters from `x`, as the difference of the two lines. -/
def inside (f₁ f₂ : Nat → Int) (x n : Nat) : Int := isum (fun t => f₁ t - f₂ t) x n

theorem inside_step (f₁ f₂ : Nat → Int) (b t : Nat) :
    inside f₁ f₂ (t + 1) b = inside f₁ f₂ t b + (f₁ (t + b) - f₂ (t + b)) - (f₁ t - f₂ t) := by
  unfold inside
  have e₁ := isum_add (fun t => f₁ t - f₂ t) t 1 b
  have e₂ := isum_add (fun t => f₁ t - f₂ t) t b 1
  rw [Nat.add_comm 1 b] at e₁
  have o₁ : isum (fun t => f₁ t - f₂ t) t 1 = f₁ t - f₂ t := by simp [isum]
  have o₂ : isum (fun t => f₁ t - f₂ t) (t + b) 1 = f₁ (t + b) - f₂ (t + b) := by simp [isum]
  omega

/-- **The drift of a window.** For Farey neighbours `u / b`, `U / d`, the count inside the arc in a window of `b`
letters moves by at most `2 k` between two places at most `k d` apart. -/
theorem window_drift (hg : IrrationalLine g) (h₁ : PhaseLine g f₁) (h₂ : PhaseLine g f₂)
    {u U : Int} {b d : Nat} (F : Farey g u b U d) (hd : 2 ≤ d) (k x y : Nat) (xy : x ≤ y) (near : y - x ≤ k * d) :
    -(2 * k : Int) ≤ inside f₁ f₂ y b - inside f₁ f₂ x b ∧ inside f₁ f₂ y b - inside f₁ f₂ x b ≤ 2 * k := by
  have floor := farey_floor hg F hd
  have hb : 1 ≤ b := F.1
  let ψ₁ : Nat → Int := fun t => f₁ (t + b) - f₁ t - u
  let ψ₂ : Nat → Int := fun t => f₂ (t + b) - f₂ t - u
  have bound (f : Nat → Int) (hf : PhaseLine g f) (t : Nat) : -1 ≤ f (t + b) - f t - u ∧ f (t + b) - f t - u ≤ 1 := by
    have := hf t b hb
    omega
  have sparse (f : Nat → Int) (hf : PhaseLine g f) (t t' : Nat) (lt : t < t')
      (a : f (t + b) - f t - u ≠ 0) (c : f (t' + b) - f t' - u ≠ 0) : t + d ≤ t' :=
    Farey.gap hg hf F (by omega) (by omega) lt
  have s₁ := isum_sparse ψ₁ d (bound f₁ h₁) (sparse f₁ h₁) k x (y - x) near
  have s₂ := isum_sparse ψ₂ d (bound f₂ h₂) (sparse f₂ h₂) k x (y - x) near
  have tel : isum (fun t => inside f₁ f₂ (t + 1) b - inside f₁ f₂ t b) x (y - x) =
      inside f₁ f₂ y b - inside f₁ f₂ x b := by
    have := isum_telescope (fun t => inside f₁ f₂ t b) x (y - x)
    rwa [Nat.add_sub_of_le xy] at this
  have same : isum (fun t => inside f₁ f₂ (t + 1) b - inside f₁ f₂ t b) x (y - x) =
      isum (fun t => ψ₁ t - ψ₂ t) x (y - x) :=
    isum_congr (fun t => by rw [inside_step]; dsimp only [ψ₁, ψ₂]; omega) x (y - x)
  have sub := isum_sub ψ₁ ψ₂ x (y - x)
  omega

/-- **Balance over many windows.** Two stretches of `n` letters at most `k d` apart differ in their count inside the
arc by at most `2 k (n / b) + b`: the drift of each whole window, and one window for the rest. -/
theorem block_balance (hg : IrrationalLine g) (h₁ : PhaseLine g f₁) (h₂ : PhaseLine g f₂)
    (between : ∀ t, f₂ t ≤ f₁ t ∧ f₁ t ≤ f₂ t + 1)
    {u U : Int} {b d : Nat} (F : Farey g u b U d) (hd : 2 ≤ d) (k x y n : Nat) (xy : x ≤ y) (near : y - x ≤ k * d) :
    -((2 * k * (n / b) + b : Nat) : Int) ≤ inside f₁ f₂ y n - inside f₁ f₂ x n ∧
      inside f₁ f₂ y n - inside f₁ f₂ x n ≤ ((2 * k * (n / b) + b : Nat) : Int) := by
  have hb : 1 ≤ b := F.1
  have blocks : ∀ m x y, x ≤ y → y - x ≤ k * d →
      -((2 * k * m : Nat) : Int) ≤ inside f₁ f₂ y (b * m) - inside f₁ f₂ x (b * m) ∧
        inside f₁ f₂ y (b * m) - inside f₁ f₂ x (b * m) ≤ ((2 * k * m : Nat) : Int) := by
    intro m
    induction m with
    | zero => intro x y _ _; simp [inside, isum]
    | succ m ih =>
      intro x y xy near
      have dr := window_drift hg h₁ h₂ F hd k x y xy near
      have rest := ih (x + b) (y + b) (by omega) (by omega)
      unfold inside at dr rest ⊢
      rw [show b * (m + 1) = b + b * m by rw [Nat.mul_succ, Nat.add_comm], isum_add, isum_add, Nat.mul_succ]
      generalize 2 * k * m = B at rest ⊢
      constructor <;> omega
  have whole := blocks (n / b) x y xy near
  have split (z : Nat) : inside f₁ f₂ z n = inside f₁ f₂ z (b * (n / b)) + inside f₁ f₂ (z + b * (n / b)) (n % b) := by
    unfold inside
    rw [← isum_add, Nat.div_add_mod]
  have rem (z : Nat) := isum_bounds (fun t => f₁ t - f₂ t) (fun t => by have := between t; omega) z (n % b)
  have small := Nat.mod_lt n (show 0 < b by omega)
  rw [split x, split y]
  unfold inside at whole ⊢
  have r₁ := rem (x + b * (n / b))
  have r₂ := rem (y + b * (n / b))
  generalize 2 * k * (n / b) = B at whole ⊢
  constructor <;> omega

/-- The readings of `n` letters from `x`, through the count inside the arc. -/
theorem readings (between : ∀ t, f₂ t ≤ f₁ t ∧ f₁ t ≤ f₂ t + 1) (len : Bool → Nat) (x n : Nat) :
    ((total (fun t => len (arcWord f₁ f₂ t)) (x + n) : Nat) : Int) - total (fun t => len (arcWord f₁ f₂ t)) x =
      n * (len false : Int) + ((len true : Int) - len false) * inside f₁ f₂ x n := by
  induction n with
  | zero => simp [inside, isum]
  | succ n ih =>
    have letter : (len (arcWord f₁ f₂ (x + n)) : Int) =
        len false + ((len true : Int) - len false) * (f₁ (x + n) - f₂ (x + n)) := by
      have := between (x + n)
      unfold arcWord
      rcases (by omega : f₁ (x + n) - f₂ (x + n) = 0 ∨ f₁ (x + n) - f₂ (x + n) = 1) with e | e
      · rw [e]; simp
      · rw [e]; simp; omega
    have e : total (fun t => len (arcWord f₁ f₂ t)) (x + (n + 1)) =
        total (fun t => len (arcWord f₁ f₂ t)) (x + n) + len (arcWord f₁ f₂ (x + n)) := by
      rw [← Nat.add_assoc, total_succ]
    have i : inside f₁ f₂ x (n + 1) = inside f₁ f₂ x n + (f₁ (x + n) - f₂ (x + n)) := rfl
    rw [e, i]
    push_cast
    rw [Int.mul_add, Int.add_mul, Int.one_mul]
    omega

theorem mul_ge_neg {A B X Y : Int} (hY : 0 ≤ Y) (a₁ : -X ≤ A) (a₂ : A ≤ X) (b₁ : -Y ≤ B) (b₂ : B ≤ Y) :
    -(X * Y) ≤ A * B := by
  rcases Int.le_total 0 A with hA | hA
  · have e₁ : A * -Y ≤ A * B := Int.mul_le_mul_of_nonneg_left b₁ hA
    have e₂ : A * Y ≤ X * Y := Int.mul_le_mul_of_nonneg_right a₂ hY
    rw [Int.mul_neg] at e₁
    omega
  · have e₁ : A * Y ≤ A * B := Int.mul_le_mul_of_nonpos_left hA b₂
    have e₂ : -X * Y ≤ A * Y := Int.mul_le_mul_of_nonneg_right a₁ hY
    rw [Int.neg_mul] at e₂
    omega

/-- The room the surplus leaves. With the second scale at the level `q / (8 L gear)`, the imbalance of two stretches
and the cutoff fit in `q / gear` letters. -/
theorem rate_room {q gear L N a b d M K m j : Nat} (q1 : 1 ≤ q)
    (hK : 6400 * ((L * gear) * (L * gear)) + 80 * (L * gear) ≤ K)
    (f1 : m * b ≤ a) (f2 : j * d ≤ a) (f3 : a ≤ 10 * q)
    (Kb : K ≤ b) (Kd : K ≤ d) (bM : b ≤ M) (Mbd : M < b + d)
    (f5 : M * (8 * (L * gear)) ≤ q) (f6 : q < M * (8 * (L * gear)) + 8 * (L * gear))
    (f8 : 8 * gear * N ≤ q) :
    gear * (N + L * (2 * (j + 1) * m + b)) ≤ q := by
  generalize hP : L * gear = P at hK f5 f6
  -- one window: 8 P b ≤ q
  have C : 8 * P * b ≤ q := by
    have := Nat.mul_le_mul_right (8 * P) bM
    have e : b * (8 * P) = 8 * P * b := by grind
    omega
  -- the windows of the stretch: 16 P m ≤ 2 q
  have B : 16 * P * m ≤ 2 * q := by
    have e₁ := Nat.mul_le_mul_left m Kb
    have e₂ := Nat.mul_le_mul_left m (show 80 * P ≤ K by omega)
    have e₃ : m * (80 * P) = 5 * (16 * P * m) := by grind
    omega
  -- the drift over the stretch: 16 P (j m) ≤ 4 q
  have A : 16 * P * (j * m) ≤ 4 * q := by
    have XY : (j * m) * (b * d) ≤ 100 * (q * q) := by
      have e : (j * m) * (b * d) = (j * d) * (m * b) := by grind
      have := Nat.mul_le_mul f2 f1
      have := Nat.mul_le_mul f3 f3
      have e₂ : 10 * q * (10 * q) = 100 * (q * q) := by grind
      omega
    have twoY : K * (M + 1) ≤ 2 * (b * d) := by
      have e₁ := Nat.mul_le_mul_left b Kd
      have e₂ := Nat.mul_le_mul_right d Kb
      have e₃ := Nat.mul_le_mul_left K (show M + 1 ≤ b + d by omega)
      have e₄ : K * (b + d) = b * K + K * d := by grind
      have e₆ : 2 * (b * d) = b * d + b * d := by grind
      have e₇ : d * b = b * d := Nat.mul_comm d b
      omega
    have qK : q * K ≤ (M + 1) * (8 * P) * K := by
      have : q ≤ (M + 1) * (8 * P) := by
        have e : (M + 1) * (8 * P) = M * (8 * P) + 8 * P := by grind
        omega
      exact Nat.mul_le_mul_right K this
    have step₁ : (j * m) * (q * K) ≤ (j * m) * (16 * P * (b * d)) := by
      apply Nat.mul_le_mul_left
      have e : (M + 1) * (8 * P) * K = 8 * P * (K * (M + 1)) := by grind
      have := Nat.mul_le_mul_left (8 * P) twoY
      have e₂ : 8 * P * (2 * (b * d)) = 16 * P * (b * d) := by grind
      omega
    have step₂ : (j * m) * (16 * P * (b * d)) ≤ 16 * P * (100 * (q * q)) := by
      have e : (j * m) * (16 * P * (b * d)) = 16 * P * ((j * m) * (b * d)) := by grind
      rw [e]
      exact Nat.mul_le_mul_left _ XY
    have step₃ : ((j * m) * K) * q ≤ (1600 * P * q) * q := by
      have e₁ : (j * m) * (q * K) = ((j * m) * K) * q := by grind
      have e₂ : 16 * P * (100 * (q * q)) = (1600 * P * q) * q := by grind
      omega
    have step₄ : (j * m) * K ≤ 1600 * P * q := Nat.le_of_mul_le_mul_right step₃ (by omega)
    have step₅ : (j * m) * (6400 * (P * P)) ≤ (j * m) * K := Nat.mul_le_mul_left _ (by omega)
    have step₆ : (4 * P * (j * m)) * (1600 * P) ≤ q * (1600 * P) := by
      have e₁ : (j * m) * (6400 * (P * P)) = (4 * P * (j * m)) * (1600 * P) := by grind
      have e₂ : 1600 * P * q = q * (1600 * P) := by grind
      omega
    rcases Nat.eq_zero_or_pos P with hP0 | hP0
    · rw [hP0]; simp
    · have := Nat.le_of_mul_le_mul_right step₆ (by omega)
      have e : 16 * P * (j * m) = 4 * (4 * P * (j * m)) := by grind
      omega
  have e : gear * (N + L * (2 * (j + 1) * m + b)) * 8 = 8 * gear * N + 16 * (L * gear) * (j * m) +
      16 * (L * gear) * m + 8 * (L * gear) * b := by grind
  rw [hP] at e
  omega

/-- **Every phase, every arc, any two nonempty blocks.** The angle needs, for one positive `gear`, arbitrarily large
Farey neighbours `u / d` and `U / D` with `(6 gear + 16) d ≤ gear D`; the arc at phase `θ` is read off two lines
`f₁`, `f₂` of the angle at most one apart. -/
theorem above_six (hg : IrrationalLine g) (h₁ : PhaseLine g f₁) (h₂ : PhaseLine g f₂)
    (between : ∀ t, f₂ t ≤ f₁ t ∧ f₁ t ≤ f₂ t + 1)
    (len : Bool → Nat) (positive : ∀ b, 1 ≤ len b) (bits : Bool → Nat → Bool)
    {gear : Nat} (gearPos : 0 < gear)
    (approximations : ∀ N, ∃ (u : Int) (d : Nat) (U : Int) (D : Nat),
      N ≤ d ∧ (6 * gear + 16) * d ≤ gear * D ∧ Farey g u d U D)
    (x : Int → Bool) (lo i : Int) (leftBlack : x lo = true)
    (leftWhite : ∀ j < lo, x j = false) (start cutoff : Nat)
    (clock : ∀ t, evol x (start + t) i = decide (t % 2 = 1))
    (reads : ∀ n y, y < len (arcWord f₁ f₂ n) →
      cutoff ≤ total (fun t => len (arcWord f₁ f₂ t)) n + y →
      evol x (start + 2 * (total (fun t => len (arcWord f₁ f₂ t)) n + y)) (i + 1) =
        bits (arcWord f₁ f₂ n) y) : False := by
  let c := arcWord f₁ f₂
  let w := fun t => len (c t)
  have pos : ∀ t, 1 ≤ w t := fun t => positive _
  let L := len true + len false
  have lt := positive true
  have lf := positive false
  let K := 6400 * ((L * gear) * (L * gear)) + 80 * (L * gear) + 2
  obtain ⟨M₀, level⟩ := farey_level hg K
  apply excludes_blocks c len positive bits ?_ x lo i leftBlack leftWhite start cutoff clock reads
  intro H N
  let G := 8 * (L * gear)
  have GPos : 0 < G := by have := Nat.mul_pos (show 0 < L by omega) gearPos; omega
  obtain ⟨u, q, U, Q, large, ratio, F⟩ :=
    approximations (N + 8 * gear * H + 8 * gear * N + G * (M₀ + 1) + 2 * gear + 1)
  let extra := q / gear
  have side : 8 * gear * H ≤ q := by omega
  have extraPos : 1 ≤ extra := Nat.div_pos (by omega) gearPos
  have below : gear * extra ≤ q := Nat.mul_div_le q gear
  have span : 6 * (H + q + 2 * extra) < Q := by
    apply Nat.lt_of_mul_lt_mul_left (a := gear)
    have e₁ : gear * (6 * (H + q + 2 * extra)) = 6 * (gear * H) + 6 * (gear * q) + 12 * (gear * extra) := by grind
    have e₂ : (6 * gear + 16) * q = 6 * (gear * q) + 16 * q := by grind
    have e₃ : 8 * gear * H = 8 * (gear * H) := by grind
    omega
  obtain ⟨a, late, finish, agree⟩ := repeat_of_span c H q (2 * extra) (fun u' v z uv vz short =>
    three_failures hg h₁ h₂ F uv vz (by omega))
  refine ⟨a, a + q, a + q + 2 * extra, late, by omega, by omega, agree, ?_⟩
  -- the stretch from `a` is long, and a ≤ 10 q
  have hH : 8 * H ≤ q := by
    have := Nat.mul_le_mul_right (8 * H) (show 1 ≤ gear by omega)
    have e : gear * (8 * H) = 8 * gear * H := by grind
    omega
  have extraLe : extra ≤ q := Nat.div_le_self q gear
  have aBound : a ≤ 10 * q := by omega
  -- the second scale
  have hM : M₀ ≤ q / G := (Nat.le_div_iff_mul_le GPos).mpr (by
    have e : G * (M₀ + 1) = M₀ * G + G := by grind
    omega)
  obtain ⟨u₀, b, U₀, d, F₀, Kb, Kd, bM, dM, Mbd⟩ := level (q / G) hM
  have hd : 2 ≤ d := by omega
  have near : a - 0 ≤ (a / d + 1) * d := by
    have := Nat.lt_div_mul_add (a := a) (show 0 < d by omega)
    have e : (a / d + 1) * d = a / d * d + d := by grind
    omega
  have bal := block_balance hg h₁ h₂ between F₀ hd (a / d + 1) 0 a a (Nat.zero_le _) near
  have r₀ := readings between len 0 a
  have r₁ := readings between len a a
  rw [Nat.zero_add] at r₀
  have shift := total_shift w a (a + q) (a + 2 * extra) (fun s hs => congrArg len (agree s (by omega)))
  have more := le_total w pos (a + a) (2 * extra)
  have room := rate_room (q := q) (gear := gear) (L := L) (N := N) (a := a) (b := b) (d := d) (M := q / G)
    (K := K) (m := a / b) (j := a / d) (by omega) (by omega) (Nat.div_mul_le_self a b) (Nat.div_mul_le_self a d)
    aBound Kb Kd bM Mbd (Nat.div_mul_le_self q G) (Nat.lt_div_mul_add GPos) (by omega)
  have fits : N + L * (2 * (a / d + 1) * (a / b) + b) ≤ extra :=
    (Nat.le_div_iff_mul_le gearPos).mpr (by rw [Nat.mul_comm]; exact room)
  -- the imbalance in readings
  generalize 2 * (a / d + 1) * (a / b) + b = R at bal fits
  have imbalance := mul_ge_neg (A := (len true : Int) - len false)
    (B := inside f₁ f₂ a a - inside f₁ f₂ 0 a) (X := (L : Int))
    (Y := (R : Int)) (by omega) (by omega) (by omega) bal.1 bal.2
  rw [Int.mul_sub] at imbalance
  have zero : total w 0 = 0 := rfl
  change total w a + total w (a + q) + N ≤ total w (a + (a + q + 2 * extra))
  rw [show a + (a + q + 2 * extra) = a + q + (a + 2 * extra) by omega]
  rw [show a + a + 2 * extra = a + (a + 2 * extra) by omega] at more
  change ((total w a : Nat) : Int) - total w 0 = _ at r₀
  change ((total w (a + a) : Nat) : Int) - total w a = _ at r₁
  rw [zero] at r₀
  omega

/-- **The angle `√10 - 3`**: two nonempty blocks of any lengths, in the order of any arc and from any phase, are not
read beside an alternating column. -/
theorem sixes_excluded (h₁ : PhaseLine sixesFloor f₁) (h₂ : PhaseLine sixesFloor f₂)
    (between : ∀ t, f₂ t ≤ f₁ t ∧ f₁ t ≤ f₂ t + 1)
    (len : Bool → Nat) (positive : ∀ b, 1 ≤ len b) (bits : Bool → Nat → Bool)
    (x : Int → Bool) (lo i : Int) (leftBlack : x lo = true)
    (leftWhite : ∀ j < lo, x j = false) (start cutoff : Nat)
    (clock : ∀ t, evol x (start + t) i = decide (t % 2 = 1))
    (reads : ∀ n y, y < len (arcWord f₁ f₂ n) →
      cutoff ≤ total (fun t => len (arcWord f₁ f₂ t)) n + y →
      evol x (start + 2 * (total (fun t => len (arcWord f₁ f₂ t)) n + y)) (i + 1) =
        bits (arcWord f₁ f₂ n) y) : False :=
  above_six sixes_line h₁ h₂ between len positive bits (gear := 128) (by decide) sixes_farey x lo i leftBlack
    leftWhite start cutoff clock reads

end Ruliology.CellularAutomata.Rule30RotationFreePhase
