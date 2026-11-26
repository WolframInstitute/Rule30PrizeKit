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

end Rule30DrivenLeftDepthTwo
end Ruliology.CellularAutomata
