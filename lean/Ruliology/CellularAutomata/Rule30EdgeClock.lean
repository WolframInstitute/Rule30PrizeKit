module
public import Ruliology.CellularAutomata.Rule30FrozenRuler

/-!
# Quiet-time bounds and two-layer defect escape

In the official `Rule30FrozenRuler.T` edge frame, any code with black digit0
changes each positive digit j within ceil(j/2) updates, from every starting
time (`flip_bound_from`). The bound is attained by the single seed at its
first change of digit j (`seed_at_bound`). No finite-support or periodicity
assumption is required.

For two codes first differing at j+1, agreement of interface digits j+3 and
j+4 over three consecutive rows forces their shared digit j white. The
clock bound therefore forces a defect outside that two-digit band within
ceil(j/2)+2 updates (`two_layer_escape`), recurrently from every starting
time. This includes j=0, where immediate-next-digit excitation has a genuine
exception. It does not establish escape from arbitrary-width bands.

If two codes agree below digit j+1>=2 and differ at that digit, their next
digit is excited in every interval of ceil(j/2)+1 updates
(`recurrent_excitation`). The lowest difference persists by the existing
triangular-map theorem. This is one-layer excitation; it does not establish
escape from an arbitrary damage band. Digit1 is excluded from this
excitation statement: the black edge masks its influence on digit2.

The mechanism uses the OR gate: an unchanged digit forces both lower
drivers white. Iterating this constraint reaches the permanently black
edge. These are bounds at a fixed edge digit; the center reads a moving
digit and its eventual periodicity remains open.
-/

@[expose] public section
set_option autoImplicit false
namespace Ruliology.CellularAutomata.Rule30EdgeClock
open Ruliology.CellularAutomata.Rule30FrozenRuler
abbrev Code := Nat → Bool

theorem freeze_below (x : Code) (j : Nat) (same : T x (j+2)=x (j+2)) :
    x (j+1)=false ∧ x j=false := by
  simp only [T] at same
  cases a:x (j+2) <;> cases b:x (j+1) <;> cases c:x j <;> simp_all

/-- Every non-edge digit changes within ceil(j/2) ticks. The autonomous
prefix period can be much longer; its consecutive quiet stretches cannot. -/
theorem flip_bound (j : Nat) (hj : 0<j) (x : Code) (hx : x 0=true) :
    ∃ t,t≤(j+1)/2 ∧ iter t x j≠x j := by
  induction j using Nat.strongRecOn generalizing x with
  | ind j ih =>
    by_cases one : j=1
    · subst j
      refine ⟨1,by omega,?_⟩
      change xor (x 1) (x 0)≠x 1
      rw [hx];cases x 1 <;> decide
    obtain ⟨k,rfl⟩ : ∃ k,j=k+2 := ⟨j-2,by omega⟩
    apply Classical.byContradiction
    intro none
    have constant : ∀ t,t≤(k+3)/2 → iter t x (k+2)=x (k+2) := by
      intro t ht
      by_cases eq : iter t x (k+2)=x (k+2)
      · exact eq
      · exact False.elim (none ⟨t,ht,eq⟩)
    have lower : ∀ t,t≤(k+1)/2 → iter t x k=false := by
      intro t ht
      have a:=constant t (by omega)
      have b:=constant (t+1) (by omega)
      have eq : T (iter t x) (k+2)=iter t x (k+2) := b.trans a.symm
      exact (freeze_below _ k eq).2
    by_cases zero : k=0
    · subst k
      have wrong:=lower 0 (by omega)
      change x 0=false at wrong
      rw [hx] at wrong
      cases wrong
    obtain ⟨t,ht,ne⟩:=ih k (by omega) (by omega) x hx
    have a:=lower 0 (by omega)
    have b:=lower t ht
    exact ne (b.trans a.symm)

theorem flip_bound_from (j s : Nat) (hj : 0<j) (x : Code) (hx : x 0=true) :
    ∃ t,t≤(j+1)/2 ∧ iter (s+t) x j≠iter s x j := by
  obtain ⟨t,ht,ne⟩:=flip_bound j hj (iter s x) (by simpa only [iter_zero] using hx)
  refine ⟨t,ht,?_⟩
  rw [iter_add]
  exact ne

private theorem seed_before (j t : Nat) (before : 2*t<j) : iter t one j=false := by
  induction t generalizing j with
  | zero => simp only [iter,one,show j≠0 by omega,decide_false]
  | succ t ih =>
    obtain ⟨k,rfl⟩ : ∃ k,j=k+2 := ⟨j-2,by omega⟩
    change T (iter t one) (k+2)=false
    simp only [T,ih (k+2) (by omega),ih (k+1) (by omega),ih k (by omega)]
    rfl

/-- The change bound is sharp: the single seed first changes digit j at
exactly ceil(j/2), for every positive j. -/
theorem seed_at_bound (j : Nat) (hj : 0<j) : iter ((j+1)/2) one j=true := by
  obtain ⟨t,ht,ne⟩:=flip_bound j hj one rfl
  have white : one j=false := by simp only [one,show j≠0 by omega,decide_false]
  have equal : t=(j+1)/2 := by
    by_cases eq : t=(j+1)/2
    · exact eq
    · have past:=seed_before j t (by omega)
      exact False.elim (ne (past.trans white.symm))
  subst t
  rw [white] at ne
  cases a:iter ((j+1)/2) one j <;> simp_all

theorem mask_forces_black (a b c u : Bool) (different : a≠b)
    (same : xor u (a||c)=xor u (b||c)) : c=true := by
  cases a <;> cases b <;> cases c <;> cases u <;> simp_all

/-- A persistent lowest difference at digit j+1 excites its next digit
within ceil(j/2)+1 ticks. This is a one-layer result, not full band escape. -/
theorem higher_excitation (j : Nat) (hj : 0<j) (x y : Code) (hx : x 0=true)
    (below : AgreeBelow (j+1) x y) (different : x (j+1)≠y (j+1)) :
    ∃ t,t≤(j+1)/2+1 ∧ iter t x (j+2)≠iter t y (j+2) := by
  apply Classical.byContradiction
  intro none
  have same : ∀ t,t≤(j+1)/2+1 → iter t x (j+2)=iter t y (j+2) := by
    intro t ht
    by_cases eq : iter t x (j+2)=iter t y (j+2)
    · exact eq
    · exact False.elim (none ⟨t,ht,eq⟩)
  have lower : ∀ t,t≤(j+1)/2 → iter t x j=true := by
    intro t ht
    have currentEq:=same t (by omega)
    have after:=same (t+1) (by omega)
    have low:=iter_agree below t j (by omega)
    have ne:=iter_diff below different t
    have e : xor (iter t y (j+2)) (iter t x (j+1)||iter t y j)=
        xor (iter t y (j+2)) (iter t y (j+1)||iter t y j) := by
      change T (iter t x) (j+2)=T (iter t y) (j+2) at after
      simpa only [T,currentEq,low] using after
    exact low.trans (mask_forces_black _ _ _ _ ne e)
  obtain ⟨t,ht,ne⟩:=flip_bound j hj x hx
  exact ne ((lower t ht).trans (lower 0 (by omega)).symm)

theorem recurrent_excitation (j s : Nat) (hj : 0<j) (x y : Code) (hx : x 0=true)
    (below : AgreeBelow (j+1) x y) (different : x (j+1)≠y (j+1)) :
    ∃ t,t≤(j+1)/2+1 ∧ iter (s+t) x (j+2)≠iter (s+t) y (j+2) := by
  obtain ⟨t,ht,ne⟩:=higher_excitation j hj (iter s x) (iter s y)
    (by simpa only [iter_zero] using hx) (iter_agree below s) (iter_diff below different s)
  exact ⟨t,ht,by simpa only [iter_add] using ne⟩

theorem cancel_xor (u a b : Bool) (h : xor u a=xor u b) : a=b := by
  cases u <;> cases a <;> cases b <;> simp_all

theorem bool_two_stalls (a b p q u c a1 b1 : Bool)
    (ne : a≠b) (ne1 : a1≠b1)
    (h0 : (p||a)=(q||b)) (m0 : (u||p)=(u||q))
    (h1 : (xor p (a||c)||a1)=(xor q (b||c)||b1))
    (m1 : (xor u (p||a)||xor p (a||c))=
          (xor u (p||a)||xor q (b||c))) : c=false := by
  cases a <;> cases b <;> cases p <;> cases q <;> cases u <;>
    cases c <;> cases a1 <;> cases b1 <;> simp_all

/-- If both interface digits agree for three consecutive rows, the common
digit below the persistent lowest difference must currently be white. -/
theorem three_rows_force_white (x y : Code) (j : Nat)
    (below : AgreeBelow (j+1) x y) (different : x (j+1)≠y (j+1))
    (a0 : x (j+3)=y (j+3)) (b0 : x (j+4)=y (j+4))
    (a1 : T x (j+3)=T y (j+3)) (b1 : T x (j+4)=T y (j+4))
    (a2 : T (T x) (j+3)=T (T y) (j+3))
    (b2 : T (T x) (j+4)=T (T y) (j+4)) : x j=false := by
  have low:=below j (by omega)
  have next_ne : T x (j+1)≠T y (j+1) := iter_diff below different 1
  have h0 : (x (j+2)||x (j+1))=(y (j+2)||y (j+1)) := by
    apply cancel_xor (y (j+3))
    simpa only [T,a0] using a1
  have m0 : (x (j+3)||x (j+2))=(x (j+3)||y (j+2)) := by
    apply cancel_xor (y (j+4))
    simpa only [T,b0,←a0] using b1
  have h1 : (T x (j+2)||T x (j+1))=(T y (j+2)||T y (j+1)) := by
    apply cancel_xor (T y (j+3))
    change xor (T x (j+3)) (T x (j+2)||T x (j+1))=
      xor (T y (j+3)) (T y (j+2)||T y (j+1)) at a2
    rw [a1] at a2
    exact a2
  have m1 : (T x (j+3)||T x (j+2))=(T x (j+3)||T y (j+2)) := by
    apply cancel_xor (T y (j+4))
    change xor (T x (j+4)) (T x (j+3)||T x (j+2))=
      xor (T y (j+4)) (T y (j+3)||T y (j+2)) at b2
    rw [b1,←a1] at b2
    exact b2
  apply bool_two_stalls (x (j+1)) (y (j+1)) (x (j+2)) (y (j+2))
    (x (j+3)) (x j) (T x (j+1)) (T y (j+1)) different next_ne h0 m0
  · simpa only [T,low] using h1
  · simpa only [T,low] using m1

/-- Every persistent first difference escapes a band of two digits within
ceil(j/2)+2 ticks, including the exceptional first-difference digit 1. -/
theorem two_layer_escape (j : Nat) (x y : Code) (hx : x 0=true)
    (below : AgreeBelow (j+1) x y) (different : x (j+1)≠y (j+1)) :
    ∃ t,t≤(j+1)/2+2 ∧
      (iter t x (j+3)≠iter t y (j+3) ∨ iter t x (j+4)≠iter t y (j+4)) := by
  apply Classical.byContradiction
  intro none
  have same : ∀ t,t≤(j+1)/2+2 →
      iter t x (j+3)=iter t y (j+3) ∧ iter t x (j+4)=iter t y (j+4) := by
    intro t ht
    constructor
    · by_cases eq : iter t x (j+3)=iter t y (j+3)
      · exact eq
      · exact False.elim (none ⟨t,ht,Or.inl eq⟩)
    · by_cases eq : iter t x (j+4)=iter t y (j+4)
      · exact eq
      · exact False.elim (none ⟨t,ht,Or.inr eq⟩)
  have white : ∀ t,t≤(j+1)/2 → iter t x j=false := by
    intro t ht
    exact three_rows_force_white (iter t x) (iter t y) j
      (iter_agree below t) (iter_diff below different t)
      (same t (by omega)).1 (same t (by omega)).2
      (same (t+1) (by omega)).1 (same (t+1) (by omega)).2
      (same (t+2) (by omega)).1 (same (t+2) (by omega)).2
  by_cases zero : j=0
  · subst j
    have wrong:=white 0 (by omega)
    change x 0=false at wrong
    rw [hx] at wrong;cases wrong
  · obtain ⟨t,ht,ne⟩:=flip_bound j (by omega) x hx
    exact ne ((white t ht).trans (white 0 (by omega)).symm)


/-- The two-layer escape recurs from every starting time; no seed or finite
support hypothesis is imposed. -/
theorem recurrent_two_layer_escape (j s : Nat) (x y : Code) (hx : x 0=true)
    (below : AgreeBelow (j+1) x y) (different : x (j+1)≠y (j+1)) :
    ∃ t,t≤(j+1)/2+2 ∧
      (iter (s+t) x (j+3)≠iter (s+t) y (j+3) ∨
       iter (s+t) x (j+4)≠iter (s+t) y (j+4)) := by
  obtain ⟨t,ht,ne⟩:=two_layer_escape j (iter s x) (iter s y)
    (by simpa only [iter_zero] using hx) (iter_agree below s) (iter_diff below different s)
  exact ⟨t,ht,by simpa only [iter_add] using ne⟩

/-! ### Two-Color Quiet-Window Bounds, Apex Wavefront Laws, Black-Wall Shielding, and 12-State Apex Algebra -/

/-- **White-Tick Window Bound (`white_within`):** for any infinite code `x` with `x 0 = true` and
any positive digit `0 < j`, `iter (s + t) x j = false` holds within `t ≤ (j + 1) / 2` ticks from
every starting time `s`. -/
theorem white_within (j s : Nat) (hj : 0 < j) (x : Code) (hx : x 0 = true) :
    ∃ t, t ≤ (j + 1) / 2 ∧ iter (s + t) x j = false := by
  by_cases white : iter s x j = false
  · exact ⟨0, by omega, white⟩
  · obtain ⟨t, ht, ne⟩ := flip_bound_from j s hj x hx
    have black : iter s x j = true := by cases h : iter s x j <;> simp_all
    refine ⟨t, ht, ?_⟩
    rw [black] at ne
    cases h : iter (s + t) x j <;> simp_all

/-- **Black-Tick Window Bound (`black_within_edge`):** for any infinite code `x` with `x 0 = true`
and any digit `j : Nat`, `iter (s + t) x j = true` holds within `t ≤ (j + 1) / 2` ticks from every
starting time `s`. -/
theorem black_within_edge (j s : Nat) (x : Code) (hx : x 0 = true) :
    ∃ t, t ≤ (j + 1) / 2 ∧ iter (s + t) x j = true := by
  by_cases black : iter s x j = true
  · exact ⟨0, by omega, black⟩
  · by_cases zero : j = 0
    · subst j
      have e : iter s x 0 = true := by simpa only [iter_zero] using hx
      exact False.elim (black e)
    · obtain ⟨t, ht, ne⟩ := flip_bound_from j s (by omega) x hx
      have white : iter s x j = false := by cases h : iter s x j <;> simp_all
      refine ⟨t, ht, ?_⟩
      rw [white] at ne
      cases h : iter (s + t) x j <;> simp_all

/-- **Two-Color Window Law (`both_colors_within`):** every positive digit `0 < j` of any infinite
black-edge code visits both `false` and `true` within every window `[s, s + (j + 1) / 2]`. -/
theorem both_colors_within (j s : Nat) (hj : 0 < j) (x : Code) (hx : x 0 = true) :
    (∃ tw, tw ≤ (j + 1) / 2 ∧ iter (s + tw) x j = false) ∧
    (∃ tb, tb ≤ (j + 1) / 2 ∧ iter (s + tb) x j = true) :=
  ⟨white_within j s hj x hx, black_within_edge j s x hx⟩

/-- **Public Pre-Horizon White Law of the Single Seed (`seed_white_before_horizon`):** for all
`j, t : Nat` with `2 * t < j`, the single seed satisfies `iter t one j = false`. -/
theorem seed_white_before_horizon (j t : Nat) (before : 2 * t < j) : iter t one j = false := by
  induction t generalizing j with
  | zero => simp only [iter, one, show j ≠ 0 by omega, decide_false]
  | succ t ih =>
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
    change T (iter t one) (k + 2) = false
    simp only [T, ih (k + 2) (by omega), ih (k + 1) (by omega), ih k (by omega)]
    rfl

/-- **Exact Even-Digit Horizon Activation of the Single Seed (`seed_even_horizon`):** for every
`t : Nat`, digit `2 * t` of `one` is `true` at step `t` (`iter t one (2 * t) = true`). -/
theorem seed_even_horizon (t : Nat) : iter t one (2 * t) = true := by
  cases t with
  | zero => rfl
  | succ t =>
    have h := seed_at_bound (2 * (t + 1)) (by omega)
    have hdiv : (2 * (t + 1) + 1) / 2 = t + 1 := by omega
    simpa only [hdiv] using h

/-- **Exact Odd-Digit Horizon Activation of the Single Seed (`seed_odd_horizon`):** for every
`t : Nat`, digit `2 * t + 1` of `one` is `true` at step `t + 1` (`iter (t + 1) one (2 * t + 1) = true`). -/
theorem seed_odd_horizon (t : Nat) : iter (t + 1) one (2 * t + 1) = true := by
  have h := seed_at_bound (2 * t + 1) (by omega)
  have hdiv : (2 * t + 1 + 1) / 2 = t + 1 := by omega
  simpa only [hdiv] using h

/-- **Apex Row-1 Symmetric Triad (`seed_row1_triad`):** at `t = 1`, the single seed `one` forms the
three-cell black block at digits `0, 1, 2` and is `false` for all `j > 2`. -/
theorem seed_row1_triad :
    iter 1 one 0 = true ∧ iter 1 one 1 = true ∧ iter 1 one 2 = true ∧
    ∀ j, 2 < j → iter 1 one j = false := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro j hj
  exact seed_white_before_horizon j 1 (by omega)

/-- **Apex Row-2 Two-Block Split (`seed_row2_split`):** at `t = 2`, the nonlinear OR-reset punches
a two-cell white gap at digits `1, 2`, splitting the active cone `0..4` into the edge digit `0 = true`,
the white gap `1, 2 = false`, and the leading pair `3, 4 = true`, with `false` for all `j > 4`. -/
theorem seed_row2_split :
    iter 2 one 0 = true ∧ iter 2 one 1 = false ∧ iter 2 one 2 = false ∧
    iter 2 one 3 = true ∧ iter 2 one 4 = true ∧
    ∀ j, 4 < j → iter 2 one j = false := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_⟩
  intro j hj
  exact seed_white_before_horizon j 2 (by omega)

/-- **Black-Wall Upper-Tail Shielding (`black_wall_shields_upper_tail`):** if `x` and `y` share a
black cell at digit `k + 1` (`x (k + 1) = true` and `y (k + 1) = true`) and agree on all digits
`j ≥ k + 1`, then the OR gate at `k + 2` saturates and masks any disagreement at or below `k`, so
`T x j = T y j` for all `j ≥ k + 2`. -/
theorem black_wall_shields_upper_tail (k : Nat) (x y : Code)
    (hxk : x (k + 1) = true) (hyk : y (k + 1) = true)
    (hagree : ∀ j, k + 1 ≤ j → x j = y j) :
    ∀ j, k + 2 ≤ j → T x j = T y j := by
  intro j hj
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
  rcases Nat.eq_or_lt_of_le (show k ≤ m by omega) with rfl | hlt
  · simp only [T, hagree (k + 2) (by omega), hxk, hyk, Bool.true_or]
  · simp only [T, hagree (m + 2) (by omega), hagree (m + 1) (by omega), hagree m (by omega)]

/-- **Speed-Two Upper-Tail Causality Cone (`upper_cone_speed_two_shield`):** if `x` and `y` agree
on all digits `j ≥ k`, then after `t` updates of `T` they agree on all digits `j ≥ k + 2 * t`
regardless of arbitrary differences on `0 .. k - 1`. -/
theorem upper_cone_speed_two_shield (k t : Nat) (x y : Code)
    (hagree : ∀ j, k ≤ j → x j = y j) :
    ∀ j, k + 2 * t ≤ j → iter t x j = iter t y j := by
  induction t with
  | zero =>
    intro j hj
    exact hagree j (by omega)
  | succ t ih =>
    intro j hj
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
    change T (iter t x) (m + 2) = T (iter t y) (m + 2)
    simp only [T, ih (m + 2) (by omega), ih (m + 1) (by omega), ih m (by omega)]

/-- **Symbolic 3-Cell Apex Seed (`apexSeed`):** places Boolean generators `(u0, u1, u2)` at digits
`(0, 1, 2)` and `false` at all digits `j ≥ 3`. -/
def apexSeed (u0 u1 u2 : Bool) : Code
  | 0 => u0
  | 1 => u1
  | 2 => u2
  | _ + 3 => false

/-- **Row-1 Triad Identity (`apexSeed_ttt_eq_iter_one`):** the `(true, true, true)` apex seed is
extensionally equal to `iter 1 one`. -/
theorem apexSeed_ttt_eq_iter_one (j : Nat) :
    apexSeed true true true j = iter 1 one j := by
  match j with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | m + 3 =>
    have hw := seed_white_before_horizon (m + 3) 1 (by omega)
    exact hw.symm

/-- **One-Step Shielding of `101` by `001` (`apexSeed_101_shields_001_step`):** because `u2 = true`
sits at digit `2`, `black_wall_shields_upper_tail` at `k = 1` guarantees that
`T (apexSeed true false true)` and `T (apexSeed false false true)` agree on all `j ≥ 3`. -/
theorem apexSeed_101_shields_001_step (j : Nat) (hj : 3 ≤ j) :
    T (apexSeed true false true) j = T (apexSeed false false true) j := by
  refine black_wall_shields_upper_tail 1 (apexSeed true false true) (apexSeed false false true) rfl rfl ?_ j hj
  intro i hi
  match i with
  | 0 => omega
  | 1 => omega
  | 2 => rfl
  | m + 3 => rfl

/-- **One-Step Shielding of `110` by `010` (`apexSeed_110_shields_010_step`):** because `u1 = true`
sits at digit `1`, `black_wall_shields_upper_tail` at `k = 0` guarantees that
`T (apexSeed true true false)` and `T (apexSeed false true false)` agree on all `j ≥ 2`. -/
theorem apexSeed_110_shields_010_step (j : Nat) (hj : 2 ≤ j) :
    T (apexSeed true true false) j = T (apexSeed false true false) j := by
  refine black_wall_shields_upper_tail 0 (apexSeed true true false) (apexSeed false true false) rfl rfl ?_ j hj
  intro i hi
  match i with
  | 0 => omega
  | 1 => rfl
  | 2 => rfl
  | m + 3 => rfl

/-- **One-Step Shielding of `111` by `011` (`apexSeed_111_shields_011_step`):** because `u1 = true`
sits at digit `1`, `black_wall_shields_upper_tail` at `k = 0` guarantees that
`T (apexSeed true true true)` and `T (apexSeed false true true)` agree on all `j ≥ 2` (differing
only at digits `0` and `1`). -/
theorem apexSeed_111_shields_011_step (j : Nat) (hj : 2 ≤ j) :
    T (apexSeed true true true) j = T (apexSeed false true true) j := by
  refine black_wall_shields_upper_tail 0 (apexSeed true true true) (apexSeed false true true) rfl rfl ?_ j hj
  intro i hi
  match i with
  | 0 => omega
  | 1 => rfl
  | 2 => rfl
  | m + 3 => rfl

/-- **Universal Interior ANF Polynomial over `F_2[u0, u1, u2]` (`apexInteriorPoly`):** given the
three adjacent standard Rule 30 bits `(A, B, C)` representing `(100, 010, 001)`, evaluates the exact
symbolic polynomial across all 8 seeds `(u0, u1, u2) : Bool`. -/
def apexInteriorPoly (A B C u0 u1 u2 : Bool) : Bool :=
  xor (xor (and A (and u0 (!(and u1 u2))))
           (and B (and (!u0) u1)))
      (xor (and C (and (!u0) (and (!u1) u2)))
           (and (xor C (or B A)) (and u0 (and u1 u2))))

/-- **Exact 8-Seed Evaluation of `apexInteriorPoly` (`apexInteriorPoly_eval_laws`):** verifies that
`apexInteriorPoly A B C` evaluates to `false` on `(0,0,0)`, to `A` on `{100, 110, 101}`, to `B` on
`{010, 011}`, to `C` on `001`, and to the Rule 30 step `xor C (or B A)` on `111`. -/
theorem apexInteriorPoly_eval_laws (A B C : Bool) :
    apexInteriorPoly A B C false false false = false ∧
    apexInteriorPoly A B C true false false = A ∧
    apexInteriorPoly A B C true true false = A ∧
    apexInteriorPoly A B C true false true = A ∧
    apexInteriorPoly A B C false true false = B ∧
    apexInteriorPoly A B C false true true = B ∧
    apexInteriorPoly A B C false false true = C ∧
    apexInteriorPoly A B C true true true = xor C (or B A) := by
  cases A <;> cases B <;> cases C <;> decide

/-- **The 12-Element Closed Apex Polynomial Alphabet (`apexPoly12`):** enumerates the 12 exact
8-bit truth tables (indexed `0..11`, with bit `m` corresponding to `(u0, u1, u2)`) that appear
anywhere in the infinite Rule 30 light cone of `(u0, u1, u2)`. -/
def apexPoly12 (k : Fin 12) (u0 u1 u2 : Bool) : Bool :=
  match k.val with
  | 0  => false
  | 1  => apexInteriorPoly false false true u0 u1 u2
  | 2  => u2
  | 3  => apexInteriorPoly false true false u0 u1 u2
  | 4  => apexInteriorPoly false true true u0 u1 u2
  | 5  => u1
  | 6  => xor u1 u2
  | 7  => apexInteriorPoly true false false u0 u1 u2
  | 8  => apexInteriorPoly true false true u0 u1 u2
  | 9  => xor u0 (or u1 u2)
  | 10 => apexInteriorPoly true true false u0 u1 u2
  | _  => apexInteriorPoly true true true u0 u1 u2

/-- **Membership of All 8 Interior `(A, B, C)` States in `apexPoly12` (`apexInteriorPoly_mem_12`):**
every triple `(A, B, C) : Bool` produces one of the 12 polynomials in `apexPoly12` (`k ∈ {0,1,3,4,7,8,10,11}`). -/
theorem apexInteriorPoly_mem_12 : ∀ A B C : Bool, ∃ k : Fin 12, ∀ u0 u1 u2 : Bool,
    apexInteriorPoly A B C u0 u1 u2 = apexPoly12 k u0 u1 u2 := by decide

/-- **Rule 30 Closure of the 8 Interior Polynomials (`apexInteriorPoly_step_closed`):** applying the
symbolic Rule 30 update `xor P (or Q R)` pointwise to any three interior polynomials with parameters
`(A1, B1, C1)`, `(A2, B2, C2)`, `(A3, B3, C3)` that satisfy the horizontal shift consistency
`B1 = C2`, `A1 = B2`, `B2 = C3`, `A2 = B3` yields an exact interior polynomial in `apexPoly12`! -/
theorem apexInteriorPoly_step_closed :
    ∀ w0 w1 w2 w3 w4 u0 u1 u2 : Bool,
      xor (apexInteriorPoly w2 w1 w0 u0 u1 u2)
          (or (apexInteriorPoly w3 w2 w1 u0 u1 u2)
              (apexInteriorPoly w4 w3 w2 u0 u1 u2)) =
      apexInteriorPoly (xor w2 (or w3 w4)) (xor w1 (or w2 w3)) (xor w0 (or w1 w2)) u0 u1 u2 := by
  decide

/-- **Injectivity of the 8 Interior Polynomials (`apexInteriorPoly_injective`):** distinct 3-bit
windows `(A1, B1, C1)` and `(A2, B2, C2)` produce distinct Boolean polynomials in `F_2[u0, u1, u2]`,
establishing that there are exactly `2^3 = 8` interior states. -/
theorem apexInteriorPoly_injective :
    ∀ A1 B1 C1 A2 B2 C2 : Bool,
      (∀ u0 u1 u2 : Bool, apexInteriorPoly A1 B1 C1 u0 u1 u2 = apexInteriorPoly A2 B2 C2 u0 u1 u2) →
      (A1 = A2 ∧ B1 = B2 ∧ C1 = C2) := by
  decide

/-- **Injectivity of the 16 Interior de Bruijn Pairs (`apexDeBruijnPair_injective`):** every 4-bit
word `(w0, w1, w2, w3)` is uniquely determined by the adjacent interior polynomial pair
`(apexInteriorPoly w2 w1 w0, apexInteriorPoly w3 w2 w1)`, establishing the 16-edge de Bruijn core. -/
theorem apexDeBruijnPair_injective :
    ∀ w0 w1 w2 w3 v0 v1 v2 v3 : Bool,
      (∀ u0 u1 u2 : Bool,
        apexInteriorPoly w2 w1 w0 u0 u1 u2 = apexInteriorPoly v2 v1 v0 u0 u1 u2 ∧
        apexInteriorPoly w3 w2 w1 u0 u1 u2 = apexInteriorPoly v3 v2 v1 u0 u1 u2) →
      (w0 = v0 ∧ w1 = v1 ∧ w2 = v2 ∧ w3 = v3) := by
  decide

/-- **Exact Rule 30 Closure of the Right-Boundary Collar (`apexBoundaryCollar_closed`):** the
right-boundary collar transitions `(2,0,0) -> 2`, `(5,2,0) -> 6`, `(6,2,0) -> 5`, `(7,5,2) -> 9`,
and `(9,6,2) -> 7` hold identically across all 8 seeds `(u0, u1, u2)` in `apexPoly12`. -/
theorem apexBoundaryCollar_closed :
    ∀ u0 u1 u2 : Bool,
      xor (apexPoly12 ⟨2, by decide⟩ u0 u1 u2)
          (or (apexPoly12 ⟨0, by decide⟩ u0 u1 u2) (apexPoly12 ⟨0, by decide⟩ u0 u1 u2)) =
        apexPoly12 ⟨2, by decide⟩ u0 u1 u2 ∧
      xor (apexPoly12 ⟨5, by decide⟩ u0 u1 u2)
          (or (apexPoly12 ⟨2, by decide⟩ u0 u1 u2) (apexPoly12 ⟨0, by decide⟩ u0 u1 u2)) =
        apexPoly12 ⟨6, by decide⟩ u0 u1 u2 ∧
      xor (apexPoly12 ⟨6, by decide⟩ u0 u1 u2)
          (or (apexPoly12 ⟨2, by decide⟩ u0 u1 u2) (apexPoly12 ⟨0, by decide⟩ u0 u1 u2)) =
        apexPoly12 ⟨5, by decide⟩ u0 u1 u2 ∧
      xor (apexPoly12 ⟨7, by decide⟩ u0 u1 u2)
          (or (apexPoly12 ⟨5, by decide⟩ u0 u1 u2) (apexPoly12 ⟨2, by decide⟩ u0 u1 u2)) =
        apexPoly12 ⟨9, by decide⟩ u0 u1 u2 ∧
      xor (apexPoly12 ⟨9, by decide⟩ u0 u1 u2)
          (or (apexPoly12 ⟨6, by decide⟩ u0 u1 u2) (apexPoly12 ⟨2, by decide⟩ u0 u1 u2)) =
        apexPoly12 ⟨7, by decide⟩ u0 u1 u2 := by
  decide

end Ruliology.CellularAutomata.Rule30EdgeClock
