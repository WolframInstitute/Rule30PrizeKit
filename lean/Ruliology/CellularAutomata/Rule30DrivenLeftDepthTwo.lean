module

public import Ruliology.CellularAutomata.Rule30DrivenLeft
public import Ruliology.CellularAutomata.Rule30EveryKLine

/-!
# Inverse ticks beside a prescribed wall: depth two decides every start

The driven half `Rule30DrivenLeft.L wall s` has its wall at site 0 and an arbitrary wall column.
Write `ExactAt k m t` for: whatever the wall, every start whose leftmost black cell is at `-m`
has, at age `t`, every `k`-th predecessor exact. That is, each of `k` successive rows satisfies
the Rule 30 equation at every negative site, with its own bit at site 0 free, and the `k`-th has
its leftmost black cell at `-m - t + k`.

* `L_column`: west of any column `j ≤ 0`, the driven half from time `a` on is the half driven by
  that column. Since the wall is arbitrary, any column of a driven half is itself a wall.
* `exactAt_of_two`: if every start at depth two passes at age `T`, then every start at depth
  `m ≥ 1` passes at every age `t ≥ T` with `m + t ≥ T + 2`. Restart at time `t - T` and use the
  column two sites east of the leftmost black cell as the wall.
* `exactAt_two_of_one`: a start at depth two at age `T ≥ 2` is a start at depth one at age `T + 1`,
  under another wall. At depth one the first tick makes the cells at `-2` and `-1` black, and at
  age 2 the two depth-two starts give the same rows.
* `two_classes`: for every `k` and every `T ≥ 2`, the statements "every start at depth at least
  two passes at every age from `T`" and "the adjacent start passes at every age from `T + 1`" are
  each equivalent to `ExactAt k 2 T`. The offset pairs the cutoffs `T` and `T + 1` in this range.
  It accounts for Hughes's ages 8 and 9, and 24 and 25. At zero inverse ticks both unrestricted
  least ages are zero.

For each `k`, `ExactAt k 2 T` is then one finite check: every row at age `T` of a depth-two start
under any wall, against all `4^k` choices of the predecessors' bits at sites `-1` and `0`.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30DrivenLeftDepthTwo

open Rule30Jen Rule30DrivenLeft Rule30EveryKLine

/-- **A column as the wall.** West of column `j ≤ 0`, the driven half from time `a` on is the half
driven by that column, from the row at time `a` read with site `p` at `p + j`. -/
theorem L_column (c : Nat → Bool) (s : Int → Bool) (a : Nat) {j : Int} (hj : j ≤ 0) :
    ∀ (τ : Nat) (p : Int), p ≤ 0 →
      L (fun τ => L c s (a + τ) j) (fun p => L c s a (p + j)) τ p = L c s (a + τ) (p + j) := by
  intro τ
  induction τ with
  | zero =>
    intro p hp
    by_cases h : p < 0
    · rw [L_zero h, Nat.add_zero]
    · rw [show p = 0 by omega, L_col0, Nat.add_zero, Int.zero_add]
  | succ τ ih =>
    intro p hp
    by_cases h : p < 0
    · rw [L_succ h, ih (p - 1) (by omega), ih p (by omega), ih (p + 1) (by omega),
        show a + (τ + 1) = (a + τ) + 1 by omega, L_succ (show p + j < 0 by omega),
        show p - 1 + j = p + j - 1 by omega, show p + 1 + j = p + j + 1 by omega]
    · rw [show p = 0 by omega, L_col0, Int.zero_add]

/-- The driven half sees its start only at negative sites. -/
theorem L_congr_start (c : Nat → Bool) {s s' : Int → Bool} (h : ∀ p, p < 0 → s p = s' p) :
    ∀ (t : Nat) (p : Int), L c s t p = L c s' t p := by
  intro t
  induction t with
  | zero =>
    intro p
    by_cases hp : p < 0
    · rw [L_zero hp, L_zero hp, h p hp]
    · simp [L, hp]
  | succ t ih =>
    intro p
    by_cases hp : p < 0
    · rw [L_succ hp, L_succ hp, ih, ih, ih]
    · simp [L, hp]

/-- The driven half sees its wall only up to the current time. -/
theorem L_congr_wall {c c' : Nat → Bool} (s : Int → Bool) {T : Nat} (h : ∀ τ, τ ≤ T → c τ = c' τ) :
    ∀ (t : Nat), t ≤ T → ∀ p, L c s t p = L c' s t p := by
  intro t
  induction t with
  | zero =>
    intro _ p
    by_cases hp : p < 0
    · rw [L_zero hp, L_zero hp]
    · simp only [L, hp, ↓reduceIte]; exact h 0 (by omega)
  | succ t ih =>
    intro ht p
    by_cases hp : p < 0
    · rw [L_succ hp, L_succ hp, ih (by omega), ih (by omega), ih (by omega)]
    · simp only [L, hp, ↓reduceIte]; exact h (t + 1) ht

/-- Every `k`-th predecessor of the age-`t` row of a start at depth `m` has its leftmost black cell
at `-m - t + k`, whatever the wall. Each predecessor satisfies the Rule 30 equation at every
negative site; its bit at site `0` is free. -/
def ExactAt (k m t : Nat) : Prop :=
  ∀ (wall : Nat → Bool) (s : Int → Bool) (x : Nat → Int → Bool),
    s (-(m : Int)) = true → (∀ p, p < -(m : Int) → s p = false) →
    (∀ p, p < 0 → x 0 p = L wall s t p) →
    (∀ i, i < k → ∀ p, p < 0 → stepLine (x (i + 1)) p = x i p) →
    x k (-(m : Int) - t + k) = true ∧ ∀ p, p < -(m : Int) - t + k → x k p = false

/-- **Depth two at age `T` gives every start from age `T`.** If every start at depth two passes at
age `T`, then every start at depth `m ≥ 1` passes at every age `t ≥ T` with `m + t ≥ T + 2`. -/
theorem exactAt_of_two {k T : Nat} (h : ExactAt k 2 T) {m t : Nat} (hm : 1 ≤ m) (ht : T ≤ t)
    (hmt : T + 2 ≤ m + t) : ExactAt k m t := by
  intro wall s x hs1 hs0 hx0 hx
  obtain ⟨a, rfl⟩ : ∃ a, t = T + a := ⟨t - T, by omega⟩
  have hedge := edge (c := wall) hs0 hs1 (by omega) a
  let j : Int := -((m + a : Nat) : Int) + 2
  have hj : j ≤ 0 := by simp only [j]; omega
  have key := h (fun τ => L wall s (a + τ) j) (fun p => L wall s a (p + j)) (fun i p => x i (p + j))
    (by
      show L wall s a (-((2 : Nat) : Int) + j) = true
      rw [show -((2 : Nat) : Int) + j = -((m + a : Nat) : Int) by simp only [j]; omega]
      exact hedge.2)
    (fun p hp => by
      show L wall s a (p + j) = false
      exact hedge.1 _ (by simp only [j] at *; omega))
    (fun p hp => by
      show x 0 (p + j) = L (fun τ => L wall s (a + τ) j) (fun p => L wall s a (p + j)) T p
      rw [L_column wall s a hj T p (by omega), hx0 (p + j) (by omega), Nat.add_comm a T])
    (fun i hi p hp => by
      show rule (x (i + 1) (p - 1 + j)) (x (i + 1) (p + j)) (x (i + 1) (p + 1 + j)) = x i (p + j)
      rw [← hx i hi (p + j) (by omega)]
      simp only [stepLine]
      rw [show p - 1 + j = p + j - 1 by omega, show p + 1 + j = p + j + 1 by omega])
  obtain ⟨k1, k2⟩ := key
  refine ⟨?_, fun p hp => ?_⟩
  · have e : -((2 : Nat) : Int) - (T : Int) + (k : Int) + j = -(m : Int) - ((T + a : Nat) : Int) + k := by
      simp only [j]; omega
    rw [← e]; exact k1
  · have := k2 (p - j) (by simp only [j] at *; omega)
    simpa [show p - j + j = p by omega] using this

/-- The canonical start at depth two: black at `-2`, `b` at `-1`, white elsewhere at negative sites. -/
def start2 (b : Bool) (p : Int) : Bool := decide (p = -2) || (b && decide (p = -1))

/-- The canonical start at depth one. -/
def start1 (p : Int) : Bool := decide (p = -1)

theorem start2_cells (b : Bool) : start2 b (-2) = true ∧ start2 b (-1) = b ∧
    ∀ p, p < -2 → start2 b p = false := by
  refine ⟨by simp [start2], by cases b <;> simp [start2], fun p hp => ?_⟩
  simp [start2, show p ≠ -2 by omega, show p ≠ -1 by omega]

/-- A start at depth two is, on the negative sites, the canonical one with its own bit at `-1`. -/
theorem start_eq_start2 {s : Int → Bool} (hs1 : s (-2) = true) (hs0 : ∀ p, p < -2 → s p = false) :
    ∀ p, p < 0 → s p = start2 (s (-1)) p := by
  intro p hp
  by_cases h2 : p = -2
  · subst h2; simp [start2, hs1]
  by_cases h1 : p = -1
  · subst h1; cases h : s (-1) <;> simp [start2]
  · rw [hs0 p (by omega)]; simp [start2, h2, h1]

/-- After one tick, the start at depth one is the start at depth two with `-1` black. -/
theorem one_tick_start1 (c : Nat → Bool) : ∀ p, p < 0 → L c start1 1 p = start2 true p := by
  intro p hp
  rw [show (1 : Nat) = 0 + 1 from rfl, L_succ hp]
  by_cases h1 : p = -1
  · subst h1
    rw [L_zero (by omega), L_zero (by omega), show (-1 : Int) + 1 = 0 by rfl, L_col0]
    simp [start1, start2, rule]
  by_cases h2 : p = -2
  · subst h2
    rw [L_zero (by omega), L_zero (by omega), L_zero (by omega)]
    simp [start1, start2, rule]
  · rw [L_zero (by omega), L_zero hp]
    by_cases h3 : p + 1 < 0
    · rw [L_zero h3]
      simp [start1, start2, rule, show p - 1 ≠ -1 by omega, h1, show p + 1 ≠ -1 by omega, h2]
    · omega

/-- At age two, the depth-two start with `-1` white equals the one with `-1` black under a
modified wall: the second wall bit becomes `!c 0 || c 1`. -/
def wallB (c : Nat → Bool) (τ : Nat) : Bool := if τ = 1 then (!c 0 || c 1) else c τ

theorem age_two_start2 (c : Nat → Bool) :
    ∀ p, p < 0 → L c (start2 false) 2 p = L (wallB c) (start2 true) 2 p := by
  have r1 : ∀ (d : Nat → Bool) (b : Bool) (q : Int), q < 0 →
      L d (start2 b) 1 q = rule (start2 b (q - 1)) (start2 b q) (if q + 1 = 0 then d 0 else start2 b (q + 1)) := by
    intro d b q hq
    rw [show (1 : Nat) = 0 + 1 from rfl, L_succ hq, L_zero (by omega), L_zero hq]
    by_cases h : q + 1 = 0
    · simp only [h, ↓reduceIte, L_col0]
    · simp only [h, ↓reduceIte]; rw [L_zero (by omega)]
  have r2 : ∀ (d : Nat → Bool) (b : Bool) (q : Int), q < 0 →
      L d (start2 b) 2 q = rule (L d (start2 b) 1 (q - 1)) (L d (start2 b) 1 q)
        (if q + 1 = 0 then d 1 else L d (start2 b) 1 (q + 1)) := by
    intro d b q hq
    rw [show (2 : Nat) = 1 + 1 from rfl, L_succ hq]
    by_cases h : q + 1 = 0
    · simp only [h, ↓reduceIte, L_col0]
    · simp only [h, ↓reduceIte]
  have w0 : wallB c 0 = c 0 := by simp [wallB]
  have w1 : wallB c 1 = (!c 0 || c 1) := by simp [wallB]
  intro p hp
  rw [r2 c false p hp, r2 (wallB c) true p hp, r1 c false (p - 1) (by omega), r1 c false p hp,
    r1 (wallB c) true (p - 1) (by omega), r1 (wallB c) true p hp, w0]
  by_cases h1 : p = -1
  · subst h1
    simp only [show (-1 : Int) + 1 = 0 by rfl, ↓reduceIte, w1]
    cases c 0 <;> cases c 1 <;> simp [start2, rule]
  · have hp1 : p + 1 < 0 := by omega
    have e : ¬ (p + 1 = 0) := by omega
    simp only [e, ↓reduceIte]
    rw [r1 c false (p + 1) hp1, r1 (wallB c) true (p + 1) hp1, w0]
    by_cases h2 : p = -2
    · subst h2; cases c 0 <;> simp [start2, rule]
    by_cases h3 : p = -3
    · subst h3; simp [start2, rule]
    by_cases h4 : p = -4
    · subst h4; simp [start2, rule]
    · have e1 : ¬ (p - 1 + 1 = 0) := by omega
      have e3 : ¬ (p + 1 + 1 = 0) := by omega
      simp only [e1, e3, ↓reduceIte]
      simp [start2, rule, show p - 1 - 1 ≠ -2 by omega, show p - 1 - 1 ≠ -1 by omega,
        show p - 1 ≠ -2 by omega, show p - 1 ≠ -1 by omega, h2, h1, show p + 1 ≠ -2 by omega,
        show p + 1 ≠ -1 by omega, show p + 1 + 1 ≠ -2 by omega, show p + 1 + 1 ≠ -1 by omega]

/-- The shifted wall of a time shift. -/
theorem L_shift (c : Nat → Bool) (s : Int → Bool) (a t : Nat) :
    ∀ p, p ≤ 0 → L c s (a + t) p = L (fun τ => c (a + τ)) (L c s a) t p :=
  L_add c s a t

/-- **The adjacent start at age `T + 1` covers depth two at age `T ≥ 2`.** -/
theorem exactAt_two_of_one {k T : Nat} (hT : 2 ≤ T) (h : ExactAt k 1 (T + 1)) : ExactAt k 2 T := by
  intro wall s x hs1 hs0 hx0 hx
  have hs := start_eq_start2 hs1 hs0
  -- the depth-two row under `wall`, as the depth-one row under a delayed wall
  let w1 : Nat → Bool := fun τ => if s (-1) then wall τ else wallB wall τ
  let c1 : Nat → Bool := fun τ => if τ = 0 then false else w1 (τ - 1)
  have row : ∀ p, p < 0 → L wall s T p = L c1 start1 (1 + T) p := by
    intro p hp
    rw [L_shift c1 start1 1 T p (by omega)]
    have hc1 : (fun τ => c1 (1 + τ)) = w1 := by
      funext τ; simp only [c1, show 1 + τ ≠ 0 by omega, ↓reduceIte, show 1 + τ - 1 = τ by omega]
    rw [hc1, L_congr_start w1 (one_tick_start1 c1) T p, L_congr_start wall hs T p]
    cases hb : s (-1)
    · -- `-1` white: pass through age two
      have hw : w1 = wallB wall := by funext τ; simp [w1, hb]
      rw [hw]
      obtain ⟨u, rfl⟩ : ∃ u, T = 2 + u := ⟨T - 2, by omega⟩
      rw [L_shift wall _ 2 u p (by omega), L_shift (wallB wall) _ 2 u p (by omega)]
      have hwall : (fun τ => wall (2 + τ)) = (fun τ => wallB wall (2 + τ)) := by
        funext τ; simp [wallB, show 2 + τ ≠ 1 by omega]
      rw [hwall]
      exact L_congr_start _ (age_two_start2 wall) u p
    · have hw : w1 = wall := by funext τ; simp [w1, hb]
      rw [hw]
  have key := h c1 start1 x (by simp [start1]) (fun p hp => by simp [start1, show p ≠ -1 by omega])
    (fun p hp => by rw [hx0 p hp, row p hp, Nat.add_comm]) hx
  obtain ⟨k1, k2⟩ := key
  refine ⟨?_, fun p hp => k2 p (by push_cast at *; omega)⟩
  rw [show -((2 : Nat) : Int) - (T : Int) + (k : Int) = -((1 : Nat) : Int) - ((T + 1 : Nat) : Int) + k by
    push_cast; omega]
  exact k1

/-- **Two classes, one statement.** For every number `k` of inverse ticks and every `T ≥ 2`, each of
"every start at depth at least two passes at every age from `T`" and "the adjacent start passes
at every age from `T + 1`" is equivalent to the single statement at depth two and age `T`. -/
theorem two_classes (k T : Nat) (hT : 2 ≤ T) :
    ((∀ m t, 2 ≤ m → T ≤ t → ExactAt k m t) ↔ ExactAt k 2 T) ∧
    ((∀ t, T + 1 ≤ t → ExactAt k 1 t) ↔ ExactAt k 2 T) :=
  ⟨⟨fun h => h 2 T (Nat.le_refl _) (Nat.le_refl _), fun h m t hm ht => exactAt_of_two h (by omega) ht (by omega)⟩,
   ⟨fun h => exactAt_two_of_one hT (h (T + 1) (Nat.le_refl _)),
    fun h t ht => exactAt_of_two h (Nat.le_refl _) (by omega) (by omega)⟩⟩

/-! ### Wall-absorption capped edge-band engine, sideways verifier, and sharp cutoffs through `k = 3` -/

open Rule30UniversalLeftSide

/-- **Base Case `k = 0` and Age Monotonicity of `ExactAt` (`exactAt_zero_and_age_mono`).** -/
theorem exactAt_zero_and_age_mono :
    (∀ m t : Nat, 1 ≤ m → ExactAt 0 m t) ∧
    (∀ k T₁ T₂ : Nat, 2 ≤ T₁ → T₁ ≤ T₂ → ExactAt k 2 T₁ → ExactAt k 2 T₂) := by
  refine ⟨fun m t hm wall s x hs1 hs0 hx0 _ => ?_, fun k T₁ T₂ _ hle h => ?_⟩
  · have hedge := edge (c := wall) hs0 hs1 (by omega) t
    have hp0 : -(m : Int) - (t : Int) + (0 : Nat) < 0 := by omega
    refine ⟨?_, fun p hp => ?_⟩
    · rw [hx0 _ hp0, show -(m : Int) - (t : Int) + (0 : Nat) = -((m + t : Nat) : Int) by omega]
      exact hedge.2
    · rw [hx0 p (by omega)]
      exact hedge.1 p (by omega)
  · exact exactAt_of_two h (by omega) hle (by omega)

/-- `mask` encodes the leftmost `len` cells from `-((t + 2) : Int)` inward. -/
def MatchesBand (f : Int → Bool) (t len mask : Nat) : Prop :=
  mask < 2 ^ len ∧
  mask.testBit 0 = true ∧
  ∀ j, j < len → mask.testBit j = f (-((t + 2 : Nat) : Int) + (j : Int))

private theorem testBit_add_cond_two_pow {core len : Nat} (hlt : core < 2 ^ len) (c : Bool) (j : Nat) :
    (core + (if c then 2 ^ len else 0)).testBit j =
      if j < len then core.testBit j else if j = len then c else false := by
  cases c
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    by_cases hj : j < len
    · simp [hj]
    · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) (by omega)))]
      simp [hj]
  · simp only [↓reduceIte]
    rcases Nat.lt_trichotomy j len with hj | rfl | hj
    · rw [Nat.add_comm, Nat.testBit_two_pow_add_gt hj]; simp [hj]
    · rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]; simp
    · have hlt2 : core + 2 ^ len < 2 ^ (len + 1) := by rw [Nat.pow_succ]; omega
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt2 (Nat.pow_le_pow_right (by decide) (by omega)))]
      simp [show ¬ j < len by omega, show j ≠ len by omega]

def stepBandOne (bCap t len mask : Nat) : List Nat :=
  let core := stepK len mask
  if len = t + 2 ∧ len < bCap then
    let bm2 := mask.testBit (len - 2)
    if mask.testBit (len - 1) then
      [core + (if !bm2 then 2 ^ len else 0)]
    else
      [core + (if bm2 then 2 ^ len else 0), core + (if !bm2 then 2 ^ len else 0)]
  else
    [core]

def insertUniq (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x = y then y :: ys else y :: insertUniq x ys

def dedupNat : List Nat → List Nat
  | [] => []
  | x :: xs => insertUniq x (dedupNat xs)

private theorem mem_insertUniq (x z : Nat) (ys : List Nat) :
    z ∈ insertUniq x ys ↔ z = x ∨ z ∈ ys := by
  induction ys with
  | nil => simp [insertUniq]
  | cons y ys ih =>
    unfold insertUniq
    by_cases hxy : x = y
    · subst hxy; simp
    · simp [hxy, ih, or_left_comm]

private theorem mem_dedupNat (z : Nat) (xs : List Nat) :
    z ∈ dedupNat xs ↔ z ∈ xs := by
  induction xs with
  | nil => simp [dedupNat]
  | cons x xs ih => simp [dedupNat, mem_insertUniq, ih]

def reachableBands (bCap : Nat) : Nat → List Nat
  | 0 => if 2 ≤ bCap then [1, 3] else [1]
  | t + 1 =>
    let len := min (t + 2) bCap
    dedupNat ((reachableBands bCap t).flatMap (stepBandOne bCap t len))

private theorem stepK_matches_L {wall : Nat → Bool} {b : Bool} {t len mask : Nat}
    (hlen2 : 2 ≤ len) (hlen_t : len ≤ t + 2)
    (hm : MatchesBand (L wall (start2 b) t) t len mask) :
    stepK len mask < 2 ^ len ∧
    (stepK len mask).testBit 0 = true ∧
    ∀ j, j < len →
      (stepK len mask).testBit j = L wall (start2 b) (t + 1) (-((t + 3 : Nat) : Int) + (j : Int)) := by
  have hs_cells := start2_cells b
  have hedge := edge (c := wall) hs_cells.2.2 hs_cells.1 (by decide) t
  have h2t : (2 + t : Nat) = t + 2 := by omega
  have hwhite : ∀ p : Int, p < -((t + 2 : Nat) : Int) → L wall (start2 b) t p = false := by
    intro p hp; apply hedge.1; rw [h2t]; exact hp
  have hlt : stepK len mask < 2 ^ len := Nat.mod_lt _ (Nat.two_pow_pos len)
  have hb0 : (stepK len mask).testBit 0 = true := by
    rw [stepK_bit_zero (by omega)]; exact hm.2.1
  refine ⟨hlt, hb0, fun j hj => ?_⟩
  have hp_neg : -((t + 3 : Nat) : Int) + (j : Int) < 0 := by omega
  rw [L_succ hp_neg]
  simp only [stepK, Nat.testBit_mod_two_pow, decide_eq_true hj, Bool.true_and,
    Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases h2 : 2 ≤ j
  · have p1 : -((t + 3 : Nat) : Int) + (j : Int) - 1 = -((t + 2 : Nat) : Int) + ((j - 2 : Nat) : Int) := by omega
    have p2 : -((t + 3 : Nat) : Int) + (j : Int) = -((t + 2 : Nat) : Int) + ((j - 1 : Nat) : Int) := by omega
    have p3 : -((t + 3 : Nat) : Int) + (j : Int) + 1 = -((t + 2 : Nat) : Int) + (j : Int) := by omega
    rw [p3, p1, p2, ← hm.2.2 (j - 2) (by omega), ← hm.2.2 (j - 1) (by omega), ← hm.2.2 j hj]
    simp [show 2 ≤ j by omega, show 1 ≤ j by omega, rule]
  · by_cases h1 : j = 1
    · subst h1
      have hleft : L wall (start2 b) t (-((t + 3 : Nat) : Int) + ((1 : Nat) : Int) - 1) = false := hwhite _ (by omega)
      have p2 : -((t + 3 : Nat) : Int) + ((1 : Nat) : Int) = -((t + 2 : Nat) : Int) + ((0 : Nat) : Int) := by omega
      have p3 : -((t + 3 : Nat) : Int) + ((1 : Nat) : Int) + 1 = -((t + 2 : Nat) : Int) + ((1 : Nat) : Int) := by omega
      rw [p3, hleft, p2, ← hm.2.2 0 (by omega), ← hm.2.2 1 (by omega)]
      simp [rule]
    · have h0 : j = 0 := by omega
      subst h0
      have hleft : L wall (start2 b) t (-((t + 3 : Nat) : Int) + ((0 : Nat) : Int) - 1) = false := hwhite _ (by omega)
      have hmid : L wall (start2 b) t (-((t + 3 : Nat) : Int) + ((0 : Nat) : Int)) = false := hwhite _ (by omega)
      have p3 : -((t + 3 : Nat) : Int) + ((0 : Nat) : Int) + 1 = -((t + 2 : Nat) : Int) + ((0 : Nat) : Int) := by omega
      rw [p3, hleft, hmid, ← hm.2.2 0 (by omega)]
      simp [rule]

private theorem matchesBand_zero {bCap : Nat} (hbCap : 2 ≤ bCap) (wall : Nat → Bool) (b : Bool) :
    MatchesBand (L wall (start2 b) 0) 0 (min 2 bCap) (if b then 3 else 1) := by
  rw [Nat.min_eq_left hbCap]
  cases b
  · refine ⟨by decide, by decide, fun j hj => ?_⟩
    have hjc : j = 0 ∨ j = 1 := by omega
    rcases hjc with rfl | rfl <;> (rw [L_zero (by omega)]; decide)
  · refine ⟨by decide, by decide, fun j hj => ?_⟩
    have hjc : j = 0 ∨ j = 1 := by omega
    rcases hjc with rfl | rfl <;> (rw [L_zero (by omega)]; decide)

private theorem stepBandOne_step {bCap : Nat} (hbCap : 2 ≤ bCap) (wall : Nat → Bool) (b : Bool) (t mask : Nat)
    (hm : MatchesBand (L wall (start2 b) t) t (min (t + 2) bCap) mask) :
    ∃ cand ∈ stepBandOne bCap t (min (t + 2) bCap) mask,
      MatchesBand (L wall (start2 b) (t + 1)) (t + 1) (min (t + 1 + 2) bCap) cand := by
  have hlen2 : 2 ≤ min (t + 2) bCap := Nat.le_min.mpr ⟨by omega, hbCap⟩
  have hlen_t : min (t + 2) bCap ≤ t + 2 := Nat.min_le_left _ _
  obtain ⟨hcore_lt, hcore_b0, hcore⟩ := stepK_matches_L hlen2 hlen_t hm
  by_cases hgrow : min (t + 2) bCap = t + 2 ∧ min (t + 2) bCap < bCap
  · obtain ⟨hlen_eq, hlt_cap⟩ := hgrow
    have hlt_t : t + 2 < bCap := by omega
    have hnext_min : min (t + 1 + 2) bCap = (t + 2) + 1 := by omega
    rw [hlen_eq] at hcore_lt hcore_b0 hcore hm ⊢
    rw [hnext_min]
    have hm1_val : L wall (start2 b) (t + 1) (-1) =
        xor (mask.testBit t) (mask.testBit (t + 1) || wall t) := by
      have p1 : (-1 : Int) - 1 = -((t + 2 : Nat) : Int) + (t : Int) := by omega
      have p2 : (-1 : Int) = -((t + 2 : Nat) : Int) + ((t + 1 : Nat) : Int) := by omega
      have p3 : (-1 : Int) + 1 = 0 := by omega
      rw [L_succ (by omega), p3, L_col0, p1, p2,
          ← hm.2.2 t (by omega), ← hm.2.2 (t + 1) (by omega)]
      rfl
    let extBit : Bool := xor (mask.testBit t) (mask.testBit (t + 1) || wall t)
    let cand : Nat := stepK (t + 2) mask + (if extBit then 2 ^ (t + 2) else 0)
    refine ⟨cand, ?_, ?_, ?_, fun j hj => ?_⟩
    · unfold stepBandOne
      have hcond : (t + 2 = t + 2 ∧ t + 2 < bCap) := ⟨rfl, hlt_t⟩
      rw [ite_eq_left hcond]
      have hsub2 : t + 2 - 2 = t := by omega
      have hsub1 : t + 2 - 1 = t + 1 := by omega
      rw [hsub2, hsub1]
      by_cases hbm1 : mask.testBit (t + 1) = true
      · simp [cand, extBit, hbm1]
      · have hbm1_f : mask.testBit (t + 1) = false := Bool.eq_false_iff.mpr hbm1
        simp only [cand, extBit, hbm1_f, Bool.false_eq_true, ↓reduceIte, Bool.false_or]
        cases wall t <;> simp
    · rw [Nat.pow_succ]; dsimp [cand]; split <;> omega
    · dsimp [cand]; rw [testBit_add_cond_two_pow hcore_lt extBit 0]; simp [hcore_b0]
    · dsimp [cand]; rw [testBit_add_cond_two_pow hcore_lt extBit j]
      by_cases hjl : j < t + 2
      · simp only [hjl, ↓reduceIte]; exact hcore j hjl
      · have hjeq : j = t + 2 := by omega
        subst hjeq
        simp only [Nat.lt_irrefl, ↓reduceIte]
        exact hm1_val.symm.trans (by congr 1; omega)
  · have hnext_min : min (t + 1 + 2) bCap = min (t + 2) bCap := by omega
    rw [hnext_min]
    refine ⟨stepK (min (t + 2) bCap) mask, ?_, hcore_lt, hcore_b0, hcore⟩
    unfold stepBandOne; rw [ite_eq_right hgrow]; simp

def stepCovers (bCap t : Nat) (cur nxt : List Nat) : Bool :=
  let len := min (t + 2) bCap
  cur.all fun m => (stepBandOne bCap t len m).all fun c => nxt.contains c

def validTraceAux (bCap t : Nat) : List (List Nat) → Bool
  | [] => false
  | [_] => true
  | cur :: nxt :: rest => stepCovers bCap t cur nxt && validTraceAux bCap (t + 1) (nxt :: rest)

def validBandTrace (bCap : Nat) (tr : List (List Nat)) : Bool :=
  match tr with
  | [] => false
  | init :: _ => init.contains 1 && init.contains 3 && validTraceAux bCap 0 tr

def trace20 : List (List Nat) := [[0x1, 0x3], [0x7, 0x3], [0x3, 0xb], [0xb, 0x1b, 0x13], [0x33, 0x13, 0x3b], [0x3b, 0x7b, 0x13], [0x93, 0x13, 0x7b, 0xfb], [0x1fb, 0x7b, 0x17b, 0x113, 0x13], [0x13, 0x113, 0x313, 0x213, 0x37b, 0x7b, 0x27b], [0x7b, 0x47b, 0x77b, 0x37b, 0x67b, 0x213, 0x113, 0x513, 0x713], [0x113, 0x913, 0xd13, 0x213, 0xa13, 0x713, 0xe7b, 0x67b, 0x77b, 0xf7b, 0xb7b, 0x37b], [0x77b, 0x177b, 0x1f7b, 0xb7b, 0xe7b, 0x1e7b, 0x167b, 0x137b, 0x37b, 0x713, 0x1713, 0x1213, 0x213, 0xa13, 0x1a13], [0x1213, 0x3213, 0x2213, 0x213, 0x2713, 0x713, 0x3a13, 0xa13, 0x2a13, 0x137b, 0x337b, 0x237b, 0x3e7b, 0xe7b, 0x2e7b, 0x367b, 0x167b], [0x7e7b, 0x3e7b, 0x6e7b, 0xe7b, 0x4e7b, 0x737b, 0x137b, 0x537b, 0x167b, 0x367b, 0x767b, 0x567b, 0x7a13, 0x3a13, 0x6a13, 0x713, 0x2713, 0x6713, 0x4713], [0x713, 0x8713, 0x4713, 0x2713, 0xa713, 0xe713, 0x3a13, 0x7a13, 0xfa13, 0xba13, 0x6713, 0x167b, 0x967b, 0x567b, 0x137b, 0x937b, 0xf37b, 0x737b, 0xd37b], [0x137b, 0x1137b, 0x1937b, 0x1d37b, 0xd37b, 0xf37b, 0x1f37b, 0x1737b, 0x737b, 0x967b, 0x1967b, 0x1167b, 0x167b, 0x6713, 0x16713, 0x1e713, 0x1a713, 0xa713, 0x7a13, 0x17a13, 0x1fa13, 0x3a13, 0x13a13, 0xba13], [0x7a13, 0x27a13, 0x37a13, 0x1fa13, 0xba13, 0x2ba13, 0x23a13, 0x3a13, 0x13a13, 0x33a13, 0x3e713, 0x1e713, 0x36713, 0x6713, 0x26713, 0x1737b, 0x3737b, 0x2737b, 0x737b, 0x1167b, 0x3167b, 0x2167b, 0x167b, 0x967b, 0x2967b, 0x3967b], [0x1167b, 0x5167b, 0x7167b, 0x2167b, 0x4167b, 0x167b, 0x3167b, 0x6967b, 0x967b, 0x4967b, 0x7967b, 0x3967b, 0x737b, 0x4737b, 0x2737b, 0x1737b, 0x5737b, 0x7737b, 0x63a13, 0x23a13, 0x73a13, 0x13a13, 0x53a13, 0x76713, 0x36713, 0x66713, 0x6713, 0x46713, 0x3e713, 0x7e713, 0x5e713, 0x1e713], [0x76713, 0xf6713, 0xb6713, 0x36713, 0xe6713, 0x66713, 0xc6713, 0x6713, 0x86713, 0x5e713, 0x3e713, 0xbe713, 0xfe713, 0x1e713, 0x9e713, 0x13a13, 0x93a13, 0xd3a13, 0xf3a13, 0x73a13, 0x63a13, 0xe3a13, 0xa3a13, 0x23a13, 0x6967b, 0xe967b, 0x3967b, 0x7967b, 0xf967b, 0xb967b, 0x2737b, 0xa737b, 0x7737b, 0x1737b, 0x9737b, 0xd737b, 0x8737b, 0x737b, 0x4737b, 0xc737b], [0x2737b, 0xa737b, 0x7737b, 0xd737b, 0x1737b, 0x9737b, 0x8737b, 0x737b, 0x4737b, 0xc737b, 0x7967b, 0xf967b, 0xb967b, 0x3967b, 0x6967b, 0xe967b, 0x5e713, 0x9e713, 0x1e713, 0xf3a13, 0x73a13, 0x23a13, 0x63a13, 0xe3a13, 0xa3a13, 0x93a13, 0x13a13, 0xd3a13], [0xf3a13, 0x73a13, 0x23a13, 0xa3a13, 0x63a13, 0xe3a13, 0x93a13, 0x13a13, 0xd3a13, 0x1e713, 0x9e713, 0x5e713, 0x8737b, 0xc737b, 0x4737b, 0x3967b, 0xe967b, 0x6967b, 0xf967b, 0x7967b, 0xb967b], [0x3967b, 0xe967b, 0x6967b, 0xf967b, 0x7967b, 0xb967b, 0x4737b, 0xc737b, 0x8737b, 0x93a13, 0xd3a13, 0x9e713, 0x5e713, 0x1e713], [0x9e713, 0x5e713, 0x1e713, 0xd3a13, 0x93a13, 0xf967b, 0xb967b, 0xc737b, 0x8737b, 0x4737b], [0xc737b, 0x8737b, 0x4737b, 0xb967b, 0xf967b, 0x1e713, 0xd3a13, 0x93a13], [0xd3a13, 0x93a13, 0x1e713, 0x4737b, 0xb967b, 0xf967b]]
def trace28 : List (List Nat) := [[0x1, 0x3], [0x7, 0x3], [0x3, 0xb], [0xb, 0x1b, 0x13], [0x33, 0x13, 0x3b], [0x3b, 0x7b, 0x13], [0x93, 0x13, 0x7b, 0xfb], [0x1fb, 0x7b, 0x17b, 0x113, 0x13], [0x13, 0x113, 0x313, 0x213, 0x37b, 0x7b, 0x27b], [0x7b, 0x47b, 0x77b, 0x37b, 0x67b, 0x213, 0x113, 0x513, 0x713], [0x113, 0x913, 0xd13, 0x213, 0xa13, 0x713, 0xe7b, 0x67b, 0x77b, 0xf7b, 0xb7b, 0x37b], [0x77b, 0x177b, 0x1f7b, 0xb7b, 0xe7b, 0x1e7b, 0x167b, 0x137b, 0x37b, 0x713, 0x1713, 0x1213, 0x213, 0xa13, 0x1a13], [0x1213, 0x3213, 0x2213, 0x213, 0x2713, 0x713, 0x3a13, 0xa13, 0x2a13, 0x137b, 0x337b, 0x237b, 0x3e7b, 0xe7b, 0x2e7b, 0x367b, 0x167b], [0x7e7b, 0x3e7b, 0x6e7b, 0xe7b, 0x4e7b, 0x737b, 0x137b, 0x537b, 0x167b, 0x367b, 0x767b, 0x567b, 0x7a13, 0x3a13, 0x6a13, 0x713, 0x2713, 0x6713, 0x4713], [0x713, 0x8713, 0x4713, 0x2713, 0xa713, 0xe713, 0x3a13, 0x7a13, 0xfa13, 0xba13, 0x6713, 0x167b, 0x967b, 0x567b, 0x137b, 0x937b, 0xf37b, 0x737b, 0xd37b], [0x137b, 0x1137b, 0x1937b, 0x1d37b, 0xd37b, 0xf37b, 0x1f37b, 0x1737b, 0x737b, 0x967b, 0x1967b, 0x1167b, 0x167b, 0x6713, 0x16713, 0x1e713, 0x1a713, 0xa713, 0x7a13, 0x17a13, 0x1fa13, 0x3a13, 0x13a13, 0xba13], [0x7a13, 0x27a13, 0x37a13, 0x1fa13, 0xba13, 0x2ba13, 0x23a13, 0x3a13, 0x13a13, 0x33a13, 0x3e713, 0x1e713, 0x36713, 0x6713, 0x26713, 0x1737b, 0x3737b, 0x2737b, 0x737b, 0x1167b, 0x3167b, 0x2167b, 0x167b, 0x967b, 0x2967b, 0x3967b], [0x1167b, 0x5167b, 0x7167b, 0x2167b, 0x4167b, 0x167b, 0x3167b, 0x6967b, 0x967b, 0x4967b, 0x7967b, 0x3967b, 0x737b, 0x4737b, 0x2737b, 0x1737b, 0x5737b, 0x7737b, 0x63a13, 0x23a13, 0x73a13, 0x13a13, 0x53a13, 0x76713, 0x36713, 0x66713, 0x6713, 0x46713, 0x3e713, 0x7e713, 0x5e713, 0x1e713], [0x76713, 0xf6713, 0xb6713, 0x36713, 0xe6713, 0x66713, 0xc6713, 0x6713, 0x86713, 0x5e713, 0x3e713, 0xbe713, 0xfe713, 0x1e713, 0x9e713, 0x13a13, 0x93a13, 0xd3a13, 0xf3a13, 0x73a13, 0x63a13, 0xe3a13, 0xa3a13, 0x23a13, 0x6967b, 0xe967b, 0x3967b, 0x7967b, 0xf967b, 0xb967b, 0x2737b, 0xa737b, 0x7737b, 0x1737b, 0x9737b, 0xd737b, 0x8737b, 0x737b, 0x4737b, 0xc737b], [0x12737b, 0x2737b, 0xa737b, 0x1a737b, 0x7737b, 0x17737b, 0xd737b, 0x1737b, 0x11737b, 0x19737b, 0x18737b, 0x8737b, 0x10737b, 0x737b, 0x4737b, 0x14737b, 0x1c737b, 0x7967b, 0x17967b, 0x1f967b, 0xb967b, 0x3967b, 0x13967b, 0x16967b, 0x6967b, 0xe967b, 0x1e967b, 0x15e713, 0x5e713, 0x9e713, 0x19e713, 0x11e713, 0x1e713, 0xf3a13, 0x1f3a13, 0x173a13, 0x123a13, 0x23a13, 0x63a13, 0x163a13, 0x1e3a13, 0xa3a13, 0x193a13, 0x13a13, 0x113a13, 0x1d3a13, 0xd3a13], [0x3f3a13, 0xf3a13, 0x2f3a13, 0x373a13, 0x173a13, 0x123a13, 0x323a13, 0x223a13, 0x2a3a13, 0xa3a13, 0x63a13, 0x263a13, 0x363a13, 0x1e3a13, 0x193a13, 0x393a13, 0x313a13, 0x13a13, 0x213a13, 0x1d3a13, 0x3d3a13, 0x2d3a13, 0xd3a13, 0x11e713, 0x31e713, 0x21e713, 0x1e713, 0x9e713, 0x29e713, 0x39e713, 0x25e713, 0x15e713, 0x35e713, 0x5e713, 0x28737b, 0x18737b, 0x38737b, 0x3c737b, 0x1c737b, 0x34737b, 0x4737b, 0x24737b, 0x23967b, 0x3967b, 0x3e967b, 0xe967b, 0x2e967b, 0x16967b, 0x36967b, 0x26967b, 0x6967b, 0x1f967b, 0x7967b, 0x27967b, 0x37967b, 0xb967b, 0x2b967b], [0x3967b, 0x23967b, 0x63967b, 0x43967b, 0x7e967b, 0x3e967b, 0x6e967b, 0x56967b, 0x36967b, 0x76967b, 0x16967b, 0x26967b, 0x46967b, 0x6967b, 0x5f967b, 0x1f967b, 0x37967b, 0x7967b, 0x47967b, 0x67967b, 0x4b967b, 0xb967b, 0x2b967b, 0x6b967b, 0x74737b, 0x34737b, 0x64737b, 0x4737b, 0x44737b, 0x3c737b, 0x7c737b, 0x5c737b, 0x1c737b, 0x78737b, 0x68737b, 0x28737b, 0x18737b, 0x58737b, 0x593a13, 0x193a13, 0xd3a13, 0x4d3a13, 0x2d3a13, 0x1d3a13, 0x5d3a13, 0x7d3a13, 0x69e713, 0x9e713, 0x49e713, 0x5e713, 0x25e713, 0x65e713, 0x45e713, 0x75e713, 0x15e713, 0x55e713, 0x41e713, 0x1e713, 0x11e713, 0x51e713, 0x71e713, 0x21e713, 0x31e713], [0x9e713, 0x89e713, 0xe9e713, 0x69e713, 0xc9e713, 0x5e713, 0x85e713, 0x45e713, 0xa5e713, 0x25e713, 0x65e713, 0xe5e713, 0xf5e713, 0x75e713, 0xd5e713, 0x15e713, 0x95e713, 0x81e713, 0x41e713, 0xc1e713, 0xa1e713, 0x21e713, 0x11e713, 0x91e713, 0xd1e713, 0x71e713, 0xf1e713, 0x31e713, 0xb1e713, 0x51e713, 0x2d3a13, 0xad3a13, 0x7d3a13, 0x1d3a13, 0x9d3a13, 0xdd3a13, 0x8d3a13, 0xd3a13, 0x4d3a13, 0xcd3a13, 0x193a13, 0x593a13, 0xd93a13, 0x993a13, 0x9f967b, 0x5f967b, 0xdf967b, 0x2b967b, 0xab967b, 0xeb967b, 0xcb967b, 0x4b967b, 0x8b967b, 0xb967b, 0x5c737b, 0x3c737b, 0xbc737b, 0xfc737b, 0x18737b, 0x98737b, 0xf8737b, 0x78737b, 0xd8737b, 0x28737b, 0x68737b, 0xe8737b, 0xa8737b, 0xc4737b, 0x4737b, 0x84737b, 0x74737b, 0xf4737b, 0xb4737b, 0x34737b, 0xe4737b, 0x64737b], [0x3c737b, 0x13c737b, 0x1bc737b, 0x5c737b, 0x15c737b, 0xfc737b, 0x18737b, 0x118737b, 0x198737b, 0x1d8737b, 0xd8737b, 0x178737b, 0xf8737b, 0x1f8737b, 0x78737b, 0x28737b, 0x128737b, 0xa8737b, 0x68737b, 0x168737b, 0x1e8737b, 0x184737b, 0x1c4737b, 0xc4737b, 0x164737b, 0xe4737b, 0x1e4737b, 0x74737b, 0x174737b, 0x1f4737b, 0xb4737b, 0x134737b, 0x34737b, 0x1b4737b, 0xcb967b, 0x1cb967b, 0x14b967b, 0x10b967b, 0xb967b, 0x4b967b, 0x8b967b, 0x1ab967b, 0x2b967b, 0x12b967b, 0x1eb967b, 0xeb967b, 0x5f967b, 0x15f967b, 0x19f967b, 0x9f967b, 0x1df967b, 0x1c1e713, 0x181e713, 0x81e713, 0xd1e713, 0x1d1e713, 0x151e713, 0x51e713, 0xf1e713, 0x1f1e713, 0x1b1e713, 0x31e713, 0x131e713, 0x18d3a13, 0x8d3a13, 0x10d3a13, 0xd3a13, 0x593a13, 0x1593a13, 0x1d93a13, 0x193a13, 0x1193a13, 0x993a13, 0xd93a13, 0xdd3a13, 0x1d3a13, 0x11d3a13, 0x19d3a13, 0x12d3a13, 0x2d3a13, 0xad3a13, 0x1ad3a13, 0x7d3a13, 0x17d3a13], [0x8d3a13, 0x28d3a13, 0x38d3a13, 0x10d3a13, 0x18d3a13, 0x20d3a13, 0xd3a13, 0x593a13, 0x2593a13, 0x3593a13, 0x1d93a13, 0x993a13, 0x2993a13, 0x2193a13, 0x193a13, 0x1193a13, 0x3193a13, 0xd93a13, 0x2d93a13, 0x3d93a13, 0x1593a13, 0x19d3a13, 0xdd3a13, 0x2dd3a13, 0x27d3a13, 0x7d3a13, 0x12d3a13, 0x32d3a13, 0x22d3a13, 0x2d3a13, 0x3ad3a13, 0xad3a13, 0x2ad3a13, 0x2f1e713, 0xf1e713, 0x331e713, 0x31e713, 0x231e713, 0x1f1e713, 0x3f1e713, 0x3b1e713, 0x1b1e713, 0x151e713, 0xd1e713, 0x2d1e713, 0x3d1e713, 0x51e713, 0x251e713, 0x181e713, 0x381e713, 0x281e713, 0x1c1e713, 0x3c1e713, 0x81e713, 0xc4737b, 0x184737b, 0x384737b, 0x2b4737b, 0xb4737b, 0x1b4737b, 0x3b4737b, 0x234737b, 0x34737b, 0x134737b, 0x1ab967b, 0x3ab967b, 0x32b967b, 0x2b967b, 0x22b967b, 0x19f967b, 0x39f967b, 0x29f967b, 0x9f967b, 0x5f967b, 0x25f967b, 0x35f967b, 0x3df967b, 0x1df967b, 0x28b967b, 0x8b967b, 0x4b967b, 0x24b967b, 0x34b967b, 0x1cb967b, 0x3cb967b, 0xcb967b, 0x2cb967b, 0x14b967b, 0x10b967b, 0x30b967b, 0x20b967b], [0x3ab967b, 0x7ab967b, 0x5ab967b, 0x1ab967b, 0x72b967b, 0x32b967b, 0x62b967b, 0x2b967b, 0x42b967b, 0x19f967b, 0x59f967b, 0x79f967b, 0x29f967b, 0x49f967b, 0x9f967b, 0x3df967b, 0x7df967b, 0x5df967b, 0x65f967b, 0x5f967b, 0x45f967b, 0x75f967b, 0x35f967b, 0x69f967b, 0x5cb967b, 0x1cb967b, 0x28b967b, 0x68b967b, 0x48b967b, 0x70b967b, 0x10b967b, 0x50b967b, 0x7cb967b, 0x3cb967b, 0x6cb967b, 0xcb967b, 0x4cb967b, 0x14b967b, 0x34b967b, 0x74b967b, 0x54b967b, 0x434737b, 0x234737b, 0x634737b, 0x3b4737b, 0xb4737b, 0x4b4737b, 0x6b4737b, 0x34737b, 0x134737b, 0x534737b, 0x2b4737b, 0x1b4737b, 0x5b4737b, 0x7b4737b, 0x584737b, 0x184737b, 0x4c4737b, 0xc4737b, 0x384737b, 0x784737b, 0x2dd3a13, 0x6dd3a13, 0x59d3a13, 0x19d3a13, 0x52d3a13, 0x32d3a13, 0x72d3a13, 0x12d3a13, 0x6ad3a13, 0xad3a13, 0x4ad3a13, 0x7ad3a13, 0x3ad3a13, 0x551e713, 0x151e713, 0x3d1e713, 0xd1e713, 0x4d1e713, 0x6d1e713, 0x5c1e713, 0x1c1e713, 0x3c1e713, 0x7c1e713, 0x181e713, 0x581e713, 0x781e713, 0x281e713, 0x81e713, 0x481e713, 0x5b1e713, 0x3b1e713, 0x7b1e713, 0x1f1e713, 0x5f1e713, 0x7f1e713, 0x2f1e713, 0x4f1e713, 0xf1e713, 0x6f1e713, 0x731e713, 0x331e713, 0x631e713], [0x951e713, 0x151e713, 0x551e713, 0xd51e713, 0x3d1e713, 0xbd1e713, 0x6d1e713, 0xd1e713, 0x8d1e713, 0xcd1e713, 0x5c1e713, 0xdc1e713, 0x9c1e713, 0x1c1e713, 0xfc1e713, 0x3c1e713, 0xbc1e713, 0x881e713, 0x81e713, 0x781e713, 0x181e713, 0x981e713, 0xd81e713, 0x281e713, 0xa81e713, 0x8f1e713, 0x4f1e713, 0xcf1e713, 0xdb1e713, 0x5b1e713, 0xfb1e713, 0x331e713, 0x731e713, 0xf31e713, 0xb31e713, 0xf1e713, 0x2f1e713, 0xaf1e713, 0xef1e713, 0x6f1e713, 0xcad3a13, 0xead3a13, 0x6ad3a13, 0x92d3a13, 0x12d3a13, 0x32d3a13, 0xb2d3a13, 0xf2d3a13, 0x52d3a13, 0xad3a13, 0x8ad3a13, 0x7ad3a13, 0xfad3a13, 0xbad3a13, 0xd2d3a13, 0x99d3a13, 0x59d3a13, 0xd9d3a13, 0xedd3a13, 0x2dd3a13, 0xadd3a13, 0x19d3a13, 0xc8b967b, 0x48b967b, 0x9cb967b, 0x5cb967b, 0xdcb967b, 0xbcb967b, 0x3cb967b, 0x7cb967b, 0xfcb967b, 0x54b967b, 0x34b967b, 0xb4b967b, 0xf4b967b, 0x14b967b, 0x94b967b, 0xab4737b, 0x6b4737b, 0xeb4737b, 0x8b4737b, 0xb4737b, 0x2b4737b, 0x4b4737b, 0x8c4737b, 0x4c4737b, 0xcc4737b, 0xc4737b, 0x584737b, 0xd84737b, 0x984737b, 0x184737b, 0x384737b, 0xb84737b, 0xf84737b, 0x934737b, 0x134737b, 0x434737b, 0xc34737b, 0x834737b, 0x34737b, 0xe34737b, 0x234737b, 0xa34737b, 0x3b4737b, 0xbb4737b], [0xeb4737b, 0x6b4737b, 0xab4737b, 0x8b4737b, 0xb4737b, 0x4b4737b, 0x2b4737b, 0x8c4737b, 0xcc4737b, 0x4c4737b, 0xc4737b, 0xb84737b, 0x384737b, 0x184737b, 0x584737b, 0xd84737b, 0x984737b, 0xa34737b, 0xe34737b, 0x934737b, 0x134737b, 0xbb4737b, 0x3b4737b, 0x234737b, 0xc34737b, 0x434737b, 0xf4b967b, 0x54b967b, 0xfcb967b, 0x7cb967b, 0xbcb967b, 0x3cb967b, 0x34b967b, 0xb4b967b, 0x14b967b, 0xdcb967b, 0x9cb967b, 0x48b967b, 0xc8b967b, 0x5cb967b, 0xfb1e713, 0xcf1e713, 0x8f1e713, 0xf1e713, 0xaf1e713, 0x2f1e713, 0x6f1e713, 0xef1e713, 0x52d3a13, 0xb2d3a13, 0x32d3a13, 0xd2d3a13, 0xf2d3a13, 0xadd3a13, 0xedd3a13, 0x2dd3a13, 0x99d3a13, 0xd9d3a13, 0x59d3a13, 0x19d3a13, 0xfad3a13, 0x7ad3a13, 0xcad3a13, 0x8ad3a13, 0xad3a13, 0x6ad3a13, 0xead3a13, 0x92d3a13, 0x12d3a13], [0x52d3a13, 0xb2d3a13, 0x32d3a13, 0xf2d3a13, 0xd2d3a13, 0xadd3a13, 0xedd3a13, 0x2dd3a13, 0x19d3a13, 0x99d3a13, 0x59d3a13, 0xd9d3a13, 0x6ad3a13, 0xfad3a13, 0x7ad3a13, 0x12d3a13, 0x92d3a13, 0xead3a13, 0xcad3a13, 0x2f1e713, 0xaf1e713, 0xf1e713, 0x8f1e713, 0x6f1e713, 0xcf1e713, 0xfb1e713, 0x134737b, 0xe34737b, 0xa34737b, 0x234737b, 0x434737b, 0xc34737b, 0xbcb967b, 0x3cb967b, 0x48b967b, 0xc8b967b, 0xdcb967b, 0x9cb967b, 0x5cb967b, 0x14b967b, 0xf4b967b, 0xb4b967b, 0x34b967b, 0x54b967b, 0xfcb967b, 0x7cb967b], [0xbcb967b, 0x3cb967b, 0x48b967b, 0xc8b967b, 0x5cb967b, 0xdcb967b, 0x9cb967b, 0x54b967b, 0x14b967b, 0x7cb967b, 0xfcb967b, 0xf4b967b, 0xc34737b, 0x434737b, 0x234737b, 0xa34737b, 0xe34737b, 0x134737b, 0x7ad3a13, 0x6ad3a13, 0xead3a13, 0xcad3a13, 0xf1e713, 0x8f1e713, 0xfb1e713, 0xcf1e713, 0x6f1e713, 0x2f1e713, 0xaf1e713], [0xf1e713, 0x8f1e713, 0xfb1e713, 0xcf1e713, 0xaf1e713, 0x6f1e713, 0x2f1e713, 0xcad3a13, 0xead3a13, 0x6ad3a13, 0x7ad3a13, 0x14b967b, 0x54b967b, 0xf4b967b, 0x234737b, 0xa34737b, 0x134737b, 0xe34737b, 0x434737b, 0xc34737b], [0x234737b, 0xa34737b, 0x134737b, 0xe34737b, 0x434737b, 0xc34737b, 0xf4b967b, 0x54b967b, 0x14b967b, 0x6f1e713, 0xaf1e713, 0x2f1e713, 0xead3a13, 0x6ad3a13, 0x7ad3a13, 0xcad3a13]]

private theorem validTraceAux_mem {bCap : Nat} (hbCap : 2 ≤ bCap) (wall : Nat → Bool) (b : Bool) :
    ∀ (tr : List (List Nat)) (t₀ idx : Nat),
      idx < tr.length →
      validTraceAux bCap t₀ tr = true →
      (∃ m0 ∈ tr.getD 0 [], MatchesBand (L wall (start2 b) t₀) t₀ (min (t₀ + 2) bCap) m0) →
      ∃ m ∈ tr.getD idx [], MatchesBand (L wall (start2 b) (t₀ + idx)) (t₀ + idx) (min (t₀ + idx + 2) bCap) m
  | [], _, _, hlt, _, _ => by simp at hlt
  | [cur], t₀, idx, hlt, _, h0 => by
    have hi0 : idx = 0 := by simp at hlt; omega
    subst hi0; simpa using h0
  | cur :: nxt :: rest, t₀, 0, _, _, h0 => by simpa using h0
  | cur :: nxt :: rest, t₀, idx + 1, hlt, hv, h0 => by
    simp only [validTraceAux, Bool.and_eq_true] at hv
    obtain ⟨m0, hm0_mem, hm0_match⟩ := h0
    simp only [List.getD_cons_zero] at hm0_mem
    obtain ⟨cand, hcand_step, hcand_match⟩ := stepBandOne_step hbCap wall b t₀ m0 hm0_match
    unfold stepCovers at hv
    have hall1 := List.all_eq_true.mp hv.1 m0 hm0_mem
    have hcontains := List.all_eq_true.mp hall1 cand hcand_step
    have hcand_mem : cand ∈ nxt := List.contains_iff_mem.mp hcontains
    have ih := validTraceAux_mem hbCap wall b (nxt :: rest) (t₀ + 1) idx (by simp at hlt ⊢; omega) hv.2
      ⟨cand, by simpa using hcand_mem, hcand_match⟩
    simpa [List.getD_cons_succ, show t₀ + 1 + idx = t₀ + (idx + 1) by omega] using ih

/-- **Completeness of OR-Gate Wall-Absorbed Capped Edge Bands (`reachableBands_complete`).** -/
theorem reachableBands_complete :
    (∀ {bCap : Nat}, 2 ≤ bCap → ∀ (wall : Nat → Bool) (b : Bool) (t : Nat),
      ∃ mask ∈ reachableBands bCap t,
        MatchesBand (L wall (start2 b) t) t (min (t + 2) bCap) mask) ∧
    validBandTrace 28 trace28 = true ∧ (trace28.getD 31 []).length = 16 := by
  refine ⟨fun {bCap} hbCap wall b t => ?_, by decide +kernel, by decide +kernel⟩
  induction t with
  | zero =>
    refine ⟨if b then 3 else 1, ?_, matchesBand_zero hbCap wall b⟩
    simp only [reachableBands, hbCap, ↓reduceIte]; cases b <;> simp
  | succ t ih =>
    obtain ⟨mask, hmem, hm⟩ := ih
    obtain ⟨cand, hstep, hcm⟩ := stepBandOne_step hbCap wall b t mask hm
    exact ⟨cand, by simp only [reachableBands, mem_dedupNat, List.mem_flatMap]; exact ⟨mask, hmem, hstep⟩, hcm⟩

private theorem testBit_bit_add_two_mul (b : Bool) (m : Nat) :
    ((if b then 1 else 0) + 2 * m).testBit 0 = b ∧
    ∀ j, ((if b then 1 else 0) + 2 * m).testBit (j + 1) = m.testBit j := by
  refine ⟨?_, fun j => ?_⟩
  · cases b <;> simp [Nat.testBit_zero, Nat.add_mul_mod_self_left]
  · cases b <;> simp [Nat.testBit_succ, Nat.add_mul_div_left _ _ (by decide : 0 < 2)]

def revMaskAux (mask : Nat) : Nat → Nat
  | 0 => 0
  | rem + 1 => (if mask.testBit rem then 1 else 0) + 2 * revMaskAux mask rem

private theorem testBit_revMaskAux (mask : Nat) :
    ∀ (len idx : Nat), (revMaskAux mask len).testBit idx = (decide (idx < len) && mask.testBit (len - 1 - idx))
  | 0, idx => by simp [revMaskAux]
  | rem + 1, 0 => by unfold revMaskAux; rw [(testBit_bit_add_two_mul _ _).1]; simp
  | rem + 1, idx + 1 => by
    unfold revMaskAux
    rw [(testBit_bit_add_two_mul _ _).2 idx, testBit_revMaskAux mask rem idx]
    have hsub : rem - 1 - idx = rem + 1 - 1 - (idx + 1) := by omega
    rw [hsub]; simp [Nat.succ_lt_succ_iff]

def invRay (r : Nat → Bool) (b0 br : Bool) : Nat → Bool
  | 0 => b0
  | 1 => xor (r 0) (b0 || br)
  | idx + 2 => xor (r (idx + 1)) (invRay r b0 br (idx + 1) || invRay r b0 br idx)

/-- Strict `match` on `xor` forces `Bool` WHNF before recursing, preventing Fibonacci thunk blowup. -/
def invRayPack (rMask : Nat) : Nat → Nat → Bool → Bool → Nat
  | 0, _, _, _ => 0
  | rem + 1, off, bCur, bPrev =>
    match xor (rMask.testBit off) (bCur || bPrev) with
    | true => 1 + 2 * invRayPack rMask rem (off + 1) true bCur
    | false => 2 * invRayPack rMask rem (off + 1) false bCur

def buildInvRayMask (nBits : Nat) (b0 br : Bool) (rMask : Nat) : Nat :=
  (if b0 then 1 else 0) + 2 * invRayPack rMask nBits 0 b0 br

private theorem invRayPack_testBit (r : Nat → Bool) (b0 br : Bool) (rMask : Nat) :
    ∀ (rem off : Nat) (bCur bPrev : Bool),
      (∀ u, off ≤ u → u < off + rem → rMask.testBit u = r u) →
      bCur = invRay r b0 br off →
      ((off = 0 ∧ bPrev = br) ∨ (∃ k, off = k + 1 ∧ bPrev = invRay r b0 br k)) →
      ∀ i, i < rem → (invRayPack rMask rem off bCur bPrev).testBit i = invRay r b0 br (off + 1 + i)
  | 0, _, _, _, _, _, _, i, hi => by omega
  | rem + 1, off, bCur, bPrev, hrs, hCur, hPrev, i, hi => by
    have hr0 : rMask.testBit off = r off := hrs off (Nat.le_refl _) (by omega)
    have hnxt : xor (rMask.testBit off) (bCur || bPrev) = invRay r b0 br (off + 1) := by
      rcases hPrev with ⟨rfl, rfl⟩ | ⟨k, rfl, rfl⟩ <;> (rw [hr0, hCur]; rfl)
    unfold invRayPack
    cases hscrut : xor (rMask.testBit off) (bCur || bPrev)
    · simp only
      have h0_eq : 2 * invRayPack rMask rem (off + 1) false bCur =
          (if false then 1 else 0) + 2 * invRayPack rMask rem (off + 1) false bCur := (Nat.zero_add _).symm
      rw [h0_eq]
      cases i with
      | zero =>
        rw [(testBit_bit_add_two_mul _ _).1, Nat.add_zero, ← hnxt, hscrut]
      | succ j =>
        rw [(testBit_bit_add_two_mul _ _).2 j]
        have ih := invRayPack_testBit r b0 br rMask rem (off + 1) false bCur
          (fun u hu1 hu2 => hrs u (by omega) (by omega))
          (hscrut.symm.trans hnxt) (Or.inr ⟨off, rfl, hCur⟩) j (by omega)
        rw [ih]; congr 1; omega
    · simp only
      have h1_eq : 1 + 2 * invRayPack rMask rem (off + 1) true bCur =
          (if true then 1 else 0) + 2 * invRayPack rMask rem (off + 1) true bCur := rfl
      rw [h1_eq]
      cases i with
      | zero =>
        rw [(testBit_bit_add_two_mul _ _).1, Nat.add_zero, ← hnxt, hscrut]
      | succ j =>
        rw [(testBit_bit_add_two_mul _ _).2 j]
        have ih := invRayPack_testBit r b0 br rMask rem (off + 1) true bCur
          (fun u hu1 hu2 => hrs u (by omega) (by omega))
          (hscrut.symm.trans hnxt) (Or.inr ⟨off, rfl, hCur⟩) j (by omega)
        rw [ih]; congr 1; omega

private theorem buildInvRayMask_testBit (r : Nat → Bool) (nBits : Nat) (b0 br : Bool) (rMask : Nat)
    (hrs : ∀ u, u < nBits → rMask.testBit u = r u) :
    ∀ idx, idx < nBits + 1 → (buildInvRayMask nBits b0 br rMask).testBit idx = invRay r b0 br idx := by
  intro idx hidx; unfold buildInvRayMask
  cases idx with
  | zero => rw [(testBit_bit_add_two_mul _ _).1]; rfl
  | succ j =>
    rw [(testBit_bit_add_two_mul _ _).2 j]
    have hp := invRayPack_testBit r b0 br rMask nBits 0 b0 br
      (fun u _ hu => hrs u (by omega)) rfl (Or.inl ⟨rfl, rfl⟩) j (by omega)
    simpa [show 0 + 1 + j = j + 1 by omega] using hp

private theorem ray_eq_invRay {y z : Int → Bool} {p₀ : Int}
    (hstep : ∀ p, p ≤ p₀ → stepLine z p = y p) :
    ∀ idx : Nat, z (p₀ - (idx : Int)) = invRay (fun j => y (p₀ - (j : Int))) (z p₀) (z (p₀ + 1)) idx := by
  intro idx
  induction idx using Nat.strongRecOn with
  | ind idx ih =>
    rcases idx with _ | _ | idx
    · simp [invRay]
    · have hs := hstep p₀ (Int.le_refl _)
      unfold stepLine rule at hs
      have hp1 : p₀ - ((1 : Nat) : Int) = p₀ - 1 := by omega
      have hp0 : p₀ - ((0 : Nat) : Int) = p₀ := by omega
      rw [hp1]; unfold invRay; rw [hp0, ← hs]
      cases z (p₀ - 1) <;> cases (z p₀ || z (p₀ + 1)) <;> rfl
    · have hs := hstep (p₀ - ((idx + 1 : Nat) : Int)) (by omega)
      unfold stepLine rule at hs
      have e1 : p₀ - ((idx + 1 : Nat) : Int) - 1 = p₀ - ((idx + 2 : Nat) : Int) := by omega
      have e2 : p₀ - ((idx + 1 : Nat) : Int) + 1 = p₀ - (idx : Int) := by omega
      rw [e1, e2] at hs; unfold invRay
      rw [← ih (idx + 1) (by omega), ← ih idx (by omega), ← hs]
      cases z (p₀ - ((idx + 2 : Nat) : Int)) <;>
        cases (z (p₀ - ((idx + 1 : Nat) : Int)) || z (p₀ - (idx : Int))) <;> rfl

private theorem invRay_zero_tail {r : Nat → Bool} {b0 br : Bool} {M : Nat}
    (hr : ∀ j, M ≤ j → r j = false)
    (hM0 : invRay r b0 br M = false)
    (hM1 : invRay r b0 br (M + 1) = false) :
    ∀ j, M ≤ j → invRay r b0 br j = false := by
  intro j hj
  obtain ⟨d, rfl⟩ : ∃ d, j = M + d := ⟨j - M, by omega⟩
  induction d using Nat.strongRecOn with
  | ind d ih =>
    rcases d with _ | _ | d
    · simpa using hM0
    · exact hM1
    · rw [show M + (d + 2) = (M + d) + 2 by omega]; unfold invRay
      have hr_z : r (M + d + 1) = false := hr (M + d + 1) (by omega)
      have hi1 : invRay r b0 br (M + d + 1) = false := by
        simpa [show M + (d + 1) = M + d + 1 by omega] using ih (d + 1) (by omega) (by omega)
      have hi0 : invRay r b0 br (M + d) = false := ih d (by omega) (by omega)
      rw [hr_z, hi1, hi0]; rfl

def checkPredBranch (cont : Nat → Bool) (edgeM rMask : Nat) (b0 br : Bool) : Bool :=
  let nxt := buildInvRayMask (edgeM + 1) b0 br rMask
  !(nxt.testBit (edgeM - 1)) && !(nxt.testBit edgeM) && !(nxt.testBit (edgeM + 1)) && cont nxt

def checkPredLayersNat : Nat → Nat → Nat → Bool
  | 0, edgeM, rMask => rMask.testBit (edgeM - 1)
  | rem + 1, edgeM, rMask =>
    let cont := checkPredLayersNat rem (edgeM - 1)
    checkPredBranch cont edgeM rMask false false &&
    checkPredBranch cont edgeM rMask false true &&
    checkPredBranch cont edgeM rMask true false &&
    checkPredBranch cont edgeM rMask true true

def bandForcesK (k len mask : Nat) : Bool :=
  decide (k + 2 ≤ len) && checkPredLayersNat k len (revMaskAux mask len)

private theorem checkPredLayersNat_sound : ∀ (rem edgeM rMask : Nat)
    (chain : Nat → Int → Bool) (p₀ : Int),
    rem + 1 ≤ edgeM →
    (∀ idx, idx ≤ edgeM + 1 → rMask.testBit idx = chain 0 (p₀ - (idx : Int))) →
    (∀ j, edgeM ≤ j → chain 0 (p₀ - (j : Int)) = false) →
    (∀ i, i < rem → ∀ p, p ≤ p₀ → stepLine (chain (i + 1)) p = chain i p) →
    checkPredLayersNat rem edgeM rMask = true →
    chain rem (p₀ - ((edgeM - rem - 1 : Nat) : Int)) = true ∧
      ∀ j, edgeM - rem ≤ j → chain rem (p₀ - (j : Int)) = false
  | 0, edgeM, rMask, chain, p₀, hle, hmatch, htail, _, hchk => by
    simp only [checkPredLayersNat, Nat.sub_zero] at hchk ⊢
    rw [← hmatch (edgeM - 1) (by omega)]; exact ⟨hchk, htail⟩
  | rem + 1, edgeM, rMask, chain, p₀, hle, hmatch, htail, hsteps, hchk => by
    unfold checkPredLayersNat at hchk
    simp only [Bool.and_eq_true] at hchk
    obtain ⟨⟨⟨hc00, hc01⟩, hc10⟩, hc11⟩ := hchk
    have hbr : checkPredBranch (checkPredLayersNat rem (edgeM - 1)) edgeM rMask (chain 1 p₀) (chain 1 (p₀ + 1)) = true := by
      cases chain 1 p₀ <;> cases chain 1 (p₀ + 1)
      · exact hc00
      · exact hc01
      · exact hc10
      · exact hc11
    unfold checkPredBranch at hbr
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hbr
    obtain ⟨⟨⟨hz1, hz2⟩, hz3⟩, hrec⟩ := hbr
    let nxt := buildInvRayMask (edgeM + 1) (chain 1 p₀) (chain 1 (p₀ + 1)) rMask
    have hray1 := ray_eq_invRay (hsteps 0 (by omega))
    have hnxt_match : ∀ idx, idx ≤ edgeM + 1 → nxt.testBit idx = chain 1 (p₀ - (idx : Int)) := by
      intro idx hidx; dsimp [nxt]
      rw [buildInvRayMask_testBit (fun j => chain 0 (p₀ - (j : Int))) (edgeM + 1) (chain 1 p₀) (chain 1 (p₀ + 1)) rMask
        (fun u hu => hmatch u (by omega)) idx (by omega), hray1 idx]
    have h1_m1 : chain 1 (p₀ - ((edgeM - 1 : Nat) : Int)) = false := by rw [← hnxt_match (edgeM - 1) (by omega)]; exact hz1
    have h1_m0 : chain 1 (p₀ - (edgeM : Int)) = false := by rw [← hnxt_match edgeM (by omega)]; exact hz2
    have h1_p1 : chain 1 (p₀ - ((edgeM + 1 : Nat) : Int)) = false := by rw [← hnxt_match (edgeM + 1) (by omega)]; exact hz3
    have htail_ge : ∀ j, edgeM ≤ j → chain 1 (p₀ - (j : Int)) = false := by
      intro j hj; rw [hray1 j]
      exact invRay_zero_tail htail (by rw [← hray1 edgeM]; exact h1_m0)
        (by rw [← hray1 (edgeM + 1)]; exact h1_p1) j hj
    have htail1 : ∀ j, edgeM - 1 ≤ j → chain 1 (p₀ - (j : Int)) = false := by
      intro j hj
      by_cases hje : j = edgeM - 1
      · subst hje; exact h1_m1
      · exact htail_ge j (by omega)
    have ih := checkPredLayersNat_sound rem (edgeM - 1) nxt (fun i => chain (i + 1)) p₀
      (by omega) (fun idx hidx => hnxt_match idx (by omega)) htail1
      (fun i hi => hsteps (i + 1) (by omega)) hrec
    simpa [show edgeM - 1 - rem - 1 = edgeM - (rem + 1) - 1 by omega,
           show edgeM - 1 - rem = edgeM - (rem + 1) by omega] using ih

private theorem exactAt_of_bandList {k bCap T : Nat} {bands : List Nat} (_hbCap : 2 ≤ bCap)
    (hcov : ∀ (wall : Nat → Bool) (b : Bool),
      ∃ mask ∈ bands, MatchesBand (L wall (start2 b) T) T (min (T + 2) bCap) mask)
    (hok : bands.all (bandForcesK k (min (T + 2) bCap)) = true) : ExactAt k 2 T := by
  intro wall s x hs1 hs0 hx0 hx
  have hs_eq := start_eq_start2 hs1 hs0
  let b := s (-1)
  obtain ⟨mask, hmem, hm⟩ := hcov wall b
  let len := min (T + 2) bCap
  have hbf := List.all_eq_true.mp hok mask hmem
  unfold bandForcesK at hbf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hbf
  obtain ⟨hklen, hchk⟩ := hbf
  have hlen_le : len ≤ T + 2 := Nat.min_le_left _ _
  let p₀ : Int := -((T + 2 : Nat) : Int) + ((len - 1 : Nat) : Int)
  have hs_cells := start2_cells b
  have hedge := edge (c := wall) hs_cells.2.2 hs_cells.1 (by decide) T
  have h2T : (2 + T : Nat) = T + 2 := by omega
  have hwhite : ∀ p : Int, p < -((T + 2 : Nat) : Int) → L wall (start2 b) T p = false := by
    intro p hp; apply hedge.1; rw [h2T]; exact hp
  have hx0_L : ∀ p, p < 0 → x 0 p = L wall (start2 b) T p := by
    intro p hp; rw [hx0 p hp, L_congr_start wall hs_eq T p]
  have hr0_match : ∀ idx, idx ≤ len + 1 → (revMaskAux mask len).testBit idx = x 0 (p₀ - (idx : Int)) := by
    intro idx _
    rw [testBit_revMaskAux, hx0_L (p₀ - (idx : Int)) (by dsimp [p₀, len] at *; omega)]
    by_cases hlt : idx < len
    · simp only [hlt, decide_true, Bool.true_and]
      rw [hm.2.2 (len - 1 - idx) (by omega)]; congr 1; dsimp [p₀]; omega
    · simp only [hlt, decide_false, Bool.false_and]
      exact (hwhite (p₀ - (idx : Int)) (by dsimp [p₀]; omega)).symm
  have htail0 : ∀ j, len ≤ j → x 0 (p₀ - (j : Int)) = false := by
    intro j hj
    rw [hx0_L (p₀ - (j : Int)) (by dsimp [p₀, len] at *; omega)]
    exact hwhite (p₀ - (j : Int)) (by dsimp [p₀]; omega)
  have hmain := checkPredLayersNat_sound k len (revMaskAux mask len) x p₀ (by dsimp [len] at hklen ⊢; omega) hr0_match htail0
    (fun i hi p hp => hx i hi p (by dsimp [p₀, len] at *; omega)) hchk
  refine ⟨?_, fun p hp => ?_⟩
  · have heq : p₀ - ((len - k - 1 : Nat) : Int) = -((2 : Nat) : Int) - (T : Int) + (k : Int) := by
      dsimp [p₀, len] at hklen ⊢; omega
    rw [← heq]; exact hmain.1
  · let j : Nat := (p₀ - p).toNat
    have hj_eq : p₀ - (j : Int) = p := by dsimp [j, p₀, len] at *; omega
    rw [← hj_eq]; exact hmain.2 j (by dsimp [j, p₀, len] at *; omega)

/-- **Soundness of the Capped Band + Sideways Predecessor Verifier (`bandForcesK_sound`).** -/
theorem bandForcesK_sound {k bCap T : Nat} (hbCap : 2 ≤ bCap)
    (hok : (reachableBands bCap T).all (bandForcesK k (min (T + 2) bCap)) = true) :
    ExactAt k 2 T :=
  exactAt_of_bandList hbCap (fun wall b => reachableBands_complete.1 hbCap wall b T) hok

private theorem exactAt_of_validTrace {k bCap T : Nat} {tr : List (List Nat)} (hbCap : 2 ≤ bCap)
    (hT : T < tr.length) (hv : validBandTrace bCap tr = true)
    (hok : (tr.getD T []).all (bandForcesK k (min (T + 2) bCap)) = true) : ExactAt k 2 T := by
  refine exactAt_of_bandList hbCap (fun wall b => ?_) hok
  cases tr with
  | nil => simp at hT
  | cons init rest =>
    unfold validBandTrace at hv
    simp only [Bool.and_eq_true] at hv
    have hm0 : ∃ m0 ∈ (init :: rest).getD 0 [], MatchesBand (L wall (start2 b) 0) 0 (min 2 bCap) m0 := by
      refine ⟨if b then 3 else 1, ?_, matchesBand_zero hbCap wall b⟩
      simp only [List.getD_cons_zero]
      cases b
      · exact List.contains_iff_mem.mp hv.1.1
      · exact List.contains_iff_mem.mp hv.1.2
    simpa using validTraceAux_mem hbCap wall b (init :: rest) 0 T hT hv.2 hm0

def stepSingleWall (len mask : Nat) (wb : Bool) : Nat :=
  stepK len mask + (if xor (mask.testBit (len - 2)) (mask.testBit (len - 1) || wb) then 2 ^ len else 0)

def evalWallMask (wallMask : Nat) : Nat → Nat
  | 0 => 1
  | t + 1 => stepSingleWall (t + 2) (evalWallMask wallMask t) (wallMask.testBit t)

private theorem evalWallMask_matches (wallMask t : Nat) :
    MatchesBand (L (fun τ => wallMask.testBit τ) (start2 false) t) t (t + 2) (evalWallMask wallMask t) := by
  induction t with
  | zero =>
    refine ⟨by simp [evalWallMask], by simp [evalWallMask], fun j hj => ?_⟩
    have hjc : j = 0 ∨ j = 1 := by omega
    rcases hjc with rfl | rfl <;> (rw [L_zero (by omega)]; simp [evalWallMask]; decide)
  | succ t ih =>
    obtain ⟨hc_lt, hc_b0, hcore⟩ := stepK_matches_L (hlen2 := by omega) (hlen_t := Nat.le_refl _) ih
    let extB := xor ((evalWallMask wallMask t).testBit t) ((evalWallMask wallMask t).testBit (t + 1) || wallMask.testBit t)
    have hdef : evalWallMask wallMask (t + 1) = stepK (t + 2) (evalWallMask wallMask t) + (if extB then 2 ^ (t + 2) else 0) := by
      simp [evalWallMask, stepSingleWall, extB]
    have hpow : 2 ^ (t + 1 + 2) = 2 * 2 ^ (t + 2) := by
      rw [show t + 1 + 2 = (t + 2) + 1 by omega, Nat.pow_succ]; omega
    rw [hdef]
    refine ⟨by rw [hpow]; split <;> omega,
            by rw [testBit_add_cond_two_pow hc_lt extB 0]; simp [hc_b0], fun j hj => ?_⟩
    rw [testBit_add_cond_two_pow hc_lt extB j]
    by_cases hjl : j < t + 2
    · simp only [hjl, ↓reduceIte]; exact hcore j hjl
    · have hjeq : j = t + 2 := by omega
      subst hjeq
      simp only [Nat.lt_irrefl, ↓reduceIte]
      have p0 : -((t + 1 + 2 : Nat) : Int) + ((t + 2 : Nat) : Int) = -1 := by omega
      have p1 : (-1 : Int) - 1 = -((t + 2 : Nat) : Int) + (t : Int) := by omega
      have p2 : (-1 : Int) = -((t + 2 : Nat) : Int) + ((t + 1 : Nat) : Int) := by omega
      have p3 : (-1 : Int) + 1 = 0 := by omega
      rw [p0, L_succ (by omega), p3, L_col0, p1, p2, ← ih.2.2 t (by omega), ← ih.2.2 (t + 1) (by omega)]
      rfl

def applyPairsNat : List (Bool × Bool) → Nat → Nat → Nat
  | [], _, rMask => rMask
  | (b0, br) :: rest, nBits, rMask => applyPairsNat rest (nBits + 1) (buildInvRayMask nBits b0 br rMask)

def evalBadBit (wallMask T : Nat) (pairs : List (Bool × Bool)) (idx : Nat) : Bool :=
  let mask := evalWallMask wallMask T
  let r0 := revMaskAux mask (T + 2)
  (applyPairsNat pairs (T + 2) r0).testBit idx

def backPairBits (b0 br : Bool) (y : Int → Bool) : Nat → Bool
  | 0 => br
  | 1 => b0
  | n + 2 => xor (y (-(n : Int) - 1)) (backPairBits b0 br y (n + 1) || backPairBits b0 br y n)

def backPair (b0 br : Bool) (y : Int → Bool) (p : Int) : Bool :=
  if 0 < p then false else backPairBits b0 br y (-p).toNat

private theorem stepLine_backPair (b0 br : Bool) (y : Int → Bool) (p : Int) (hp : p < 0) :
    stepLine (backPair b0 br y) p = y p := by
  let n := (-p - 1).toNat
  have a : ¬ (0 : Int) < p - 1 ∧ (-(p - 1)).toNat = n + 2 := by omega
  have b : ¬ (0 : Int) < p ∧ (-p).toNat = n + 1 := by omega
  have c : ¬ (0 : Int) < p + 1 ∧ (-(p + 1)).toNat = n := by omega
  simp only [stepLine, backPair, a.1, b.1, c.1, ↓reduceIte, a.2, b.2, c.2,
    backPairBits, show -(n : Int) - 1 = p by omega, rule]
  cases y p <;> cases backPairBits b0 br y (n + 1) <;> cases backPairBits b0 br y n <;> rfl

def buildBadChain (wallMask T : Nat) (pairs : List (Bool × Bool)) : Nat → Int → Bool
  | 0 => L (fun τ => wallMask.testBit τ) (start2 false) T
  | i + 1 =>
    let pr := pairs.getD i (false, false)
    backPair pr.1 pr.2 (buildBadChain wallMask T pairs i)

private theorem buildBadChain_step (wallMask T : Nat) (pairs : List (Bool × Bool))
    (i : Nat) (p : Int) (hp : p < 0) :
    stepLine (buildBadChain wallMask T pairs (i + 1)) p = buildBadChain wallMask T pairs i p := by
  simp only [buildBadChain]; exact stepLine_backPair _ _ _ p hp

private theorem applyPairsNat_matches (pairs : List (Bool × Bool)) (nBits rMask : Nat) (y : Int → Bool)
    (hmatch : ∀ idx, idx < nBits → rMask.testBit idx = y (-1 - (idx : Int))) :
    ∀ idx, idx < nBits + pairs.length →
      (applyPairsNat pairs nBits rMask).testBit idx =
        (pairs.foldl (fun cur pr => backPair pr.1 pr.2 cur) y) (-1 - (idx : Int)) := by
  induction pairs generalizing nBits rMask y with
  | nil => intro idx hidx; simp only [applyPairsNat, List.foldl_nil]; exact hmatch idx (by simpa using hidx)
  | cons pr rest ih =>
    intro idx hidx; simp only [applyPairsNat, List.foldl_cons]
    have hray := ray_eq_invRay (z := backPair pr.1 pr.2 y) (y := y) (p₀ := -1)
      (fun p hp => stepLine_backPair pr.1 pr.2 y p (by omega))
    have hb0 : backPair pr.1 pr.2 y (-1) = pr.1 := rfl
    have hbr : backPair pr.1 pr.2 y ((-1 : Int) + 1) = pr.2 := rfl
    refine ih (nBits + 1) (buildInvRayMask nBits pr.1 pr.2 rMask) (backPair pr.1 pr.2 y) (fun j hj => ?_) idx
      (by simp at hidx; omega)
    rw [buildInvRayMask_testBit (fun u => y (-1 - (u : Int))) nBits pr.1 pr.2 rMask hmatch j hj, ← hb0, ← hbr]
    exact (hray j).symm

private theorem buildBadChain_eq_foldl (wallMask T : Nat) (pairs : List (Bool × Bool)) :
    ∀ k, k ≤ pairs.length →
      buildBadChain wallMask T pairs k =
        (pairs.take k).foldl (fun cur pr => backPair pr.1 pr.2 cur) (buildBadChain wallMask T pairs 0)
  | 0, _ => rfl
  | k + 1, hk => by
    have htake : pairs.take (k + 1) = pairs.take k ++ [pairs.getD k (false, false)] := by
      have hlt : k < pairs.length := by omega
      rw [List.take_add_one, List.getElem?_eq_getElem hlt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; simp
    rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil, ← buildBadChain_eq_foldl wallMask T pairs k (by omega)]
    rfl

private theorem evalBadBit_eq_chain (wallMask T : Nat) (pairs : List (Bool × Bool)) (idx : Nat)
    (hidx : idx < T + 2 + pairs.length) :
    evalBadBit wallMask T pairs idx = buildBadChain wallMask T pairs pairs.length (-1 - (idx : Int)) := by
  unfold evalBadBit
  have hm := evalWallMask_matches wallMask T
  let mask := evalWallMask wallMask T
  have hr0_match : ∀ j, j < T + 2 → (revMaskAux mask (T + 2)).testBit j = buildBadChain wallMask T pairs 0 (-1 - (j : Int)) := by
    intro j hj
    rw [testBit_revMaskAux, decide_eq_true hj, Bool.true_and, hm.2.2 (T + 2 - 1 - j) (by omega)]
    simp only [buildBadChain]; congr 1; omega
  rw [applyPairsNat_matches pairs (T + 2) (revMaskAux mask (T + 2)) (buildBadChain wallMask T pairs 0) hr0_match idx hidx,
      buildBadChain_eq_foldl wallMask T pairs pairs.length (Nat.le_refl _), List.take_length]

private theorem not_exactAt_of_evalBadBit {k T wallMask : Nat} (pairs : List (Bool × Bool))
    (hlen : pairs.length = k) (hk : k ≤ T + 1)
    (hfalse : evalBadBit wallMask T pairs (T + 1 - k) = false) : ¬ ExactAt k 2 T := by
  intro h
  have hs := start2_cells false
  have hres := h (fun τ => wallMask.testBit τ) (start2 false) (buildBadChain wallMask T pairs)
    hs.1 hs.2.2 (fun _ _ => rfl) (fun i _ p hp => buildBadChain_step wallMask T pairs i p hp)
  have heq := evalBadBit_eq_chain wallMask T pairs (T + 1 - k) (by omega)
  rw [hlen, show (-1 : Int) - ((T + 1 - k : Nat) : Int) = -((2 : Nat) : Int) - (T : Int) + (k : Int) by omega] at heq
  rw [← heq, hfalse] at hres
  exact Bool.noConfusion hres.1

/-- **Sharp `k = 1` `(8, 9)` and `k = 2` `(24, 25)` Cutoffs for `ExactAt` (`exactAt_one_eight_and_two_twentyFour_sharp`).** -/
theorem exactAt_one_eight_and_two_twentyFour_sharp :
    (ExactAt 1 2 8 ∧ ExactAt 1 1 9 ∧ ¬ ExactAt 1 2 7 ∧ ¬ ExactAt 1 1 8) ∧
    (ExactAt 2 2 24 ∧ ExactAt 2 1 25 ∧ ¬ ExactAt 2 2 23 ∧ ¬ ExactAt 2 1 24) := by
  have hv28 := reachableBands_complete.2.1
  have h1 : ExactAt 1 2 8 := exactAt_of_validTrace (bCap := 28) (by decide) (by decide) hv28 (by decide +kernel)
  have h2 : ExactAt 2 2 24 := exactAt_of_validTrace (bCap := 20) (tr := trace20) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have hn1 : ¬ ExactAt 1 2 7 := not_exactAt_of_evalBadBit (wallMask := 0) [(false, false)] rfl (by decide) (by decide +kernel)
  have hn2 : ¬ ExactAt 2 2 23 := not_exactAt_of_evalBadBit (wallMask := 0xc0000) [(false, false), (false, false)] rfl (by decide) (by decide +kernel)
  refine ⟨⟨h1, exactAt_of_two h1 (by decide) (by decide) (by decide),
           hn1, fun hc => hn1 (exactAt_two_of_one (by decide) hc)⟩,
          ⟨h2, exactAt_of_two h2 (by decide) (by decide) (by decide),
           hn2, fun hc => hn2 (exactAt_two_of_one (by decide) hc)⟩⟩

/-- **First Proof and Sharpness of the `k = 3` Cutoff Pair `(31, 32)` (`exactAt_three_thirtyOne_sharp`).** -/
theorem exactAt_three_thirtyOne_sharp :
    ExactAt 3 2 31 ∧ ExactAt 3 1 32 ∧ ¬ ExactAt 3 2 30 ∧ ¬ ExactAt 3 1 31 := by
  have hv28 := reachableBands_complete.2.1
  have h3 : ExactAt 3 2 31 := exactAt_of_validTrace (bCap := 28) (by decide) (by decide) hv28 (by decide +kernel)
  have hn3 : ¬ ExactAt 3 2 30 := not_exactAt_of_evalBadBit (wallMask := 0x10004000)
    [(true, false), (false, false), (false, false)] rfl (by decide) (by decide +kernel)
  exact ⟨h3, exactAt_of_two h3 (by decide) (by decide) (by decide),
         hn3, fun hc => hn3 (exactAt_two_of_one (by decide) hc)⟩

end Rule30DrivenLeftDepthTwo
end Ruliology.CellularAutomata
