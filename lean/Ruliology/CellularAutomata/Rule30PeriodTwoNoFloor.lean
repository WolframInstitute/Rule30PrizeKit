module

public import Ruliology.CellularAutomata.Rule30ZeroBoundary

@[expose] public section

/-!
# Rule 30: no uniform density floor; eternal sparse rows beside periodic center patterns

**The driven left half.** Fix a center pattern `c : Nat → Bool`. The left half-row is read by
depth: bit `i` is the cell at depth `i + 1` (position `-1-i`). One exact rule 30 step with
center value `b` is `x' i = x (i+1) xor (x i or x (i-1))`, with `x (-1) := b`. The wall trace
is `a t` (depth `1`), the **kick** is `d t = a t xor c t xor c (t+1)`, and the kick rules are

* K1  `d t → c t = false`;
* K2  `d t → c (t+1) = false → d (t+1)`;
* K3  `d t → c (t+1) = true → ¬ d (t+2)`.

In a genuine configuration whose center column is `c`, the kick is the cell at `+1` at a white
center time, and the left half satisfies K1–K3 at every time. `GValid c X H` is the prefix form
for a finite seed `X : Nat` (`orb`, `tr`, `kick`); `Eternal c x` is the infinite form for an
infinite row `x : Nat → Bool` (`orbF`, `kickF`, `KRules`).

**The theorems.** `c9` is the center word of period `72` read beside a single black cell on a
ring of `9` cells (`c9_ring`), and `c14` the word of period `1428` read at the black cell of a
ring of `14` (`c14_ring`). Then:

* `eternal_row_c9`: the infinite row black exactly at depths `8, 17, 26, …` satisfies the kick
  rules beside `c9` at every time; `eternal_row_c14`: the same for depths `14, 28, 42, …`
  beside `c14`.
* `weight_row9`, `weight_row14`: their weights below depth `H` are `(H + 1) / 9` and `H / 14`.
* `trunc_valid_c9`, `trunc_valid_c14`: hence every truncation is a finite `GValid` word of
  every length `H` with that weight.
* `no_floor_c9`, `no_floor_c14`: no floor `H ≤ q·A + d` with `q < 9` (resp. `q < 14`) holds on
  the finite `GValid` words of these patterns. A density floor that is the same for all periodic
  patterns is at most `1/14`; the per-pattern floors are untouched.

**The proof.** Read sideways, rule 30 determines column `d + 2` from columns `d + 1` and `d`
(`u`). If the center column and the wall trace are both `Q`-periodic and the pair of columns at
depth `n` equals the pair at depth `0`, the whole space-time is `Q`-periodic in time and
`n`-periodic in depth (`u_time_periodic`, `u_depth_periodic`); the row at time `0` is a genuine
driven evolution (`orbF_sideways`). Validity for ever then reduces to one period, and the column
pair at depth `n` to one comparison of natural numbers, both checked by kernel evaluation. The
`9`-ring enters its cycle at time `1`, so its row at time `0` is joined to the periodic system by
one step (`step_row9`).
-/

namespace Ruliology.CellularAutomata
namespace Rule30PeriodTwoNoFloor
open Ruliology.CellularAutomata.Rule30ZeroBoundary.IntegerForm
  (testBit_two_mul_add_zero testBit_two_mul_add_succ)

/-! ## The finite model (natural-number seeds) -/

/-- One exact rule 30 step of the left half-row `X` when the center cell is `b`. -/
def L (b : Bool) (X : Nat) : Nat := (X >>> 1) ^^^ (X ||| (2 * X + (if b then 1 else 0)))

/-- The left half-row after `t` steps beside the center pattern `c`. -/
def orb (c : Nat → Bool) (X : Nat) : Nat → Nat
  | 0 => X
  | t + 1 => L (c t) (orb c X t)

/-- The wall trace (depth `1`). -/
def tr (c : Nat → Bool) (X t : Nat) : Bool := (orb c X t).testBit 0

/-- The kick `d t = a t xor c t xor c (t+1)`. -/
def kick (c : Nat → Bool) (X t : Nat) : Bool := xor (xor (tr c X t) (c t)) (c (t + 1))

/-- The kick rules K1–K3 on the prefix of length `H`. -/
def GValid (c : Nat → Bool) (X H : Nat) : Prop :=
  ∀ t, t < H →
    (kick c X t = true → c t = false) ∧
    (kick c X t = true → c (t + 1) = false → t + 1 < H → kick c X (t + 1) = true) ∧
    (kick c X t = true → c (t + 1) = true → t + 2 < H → kick c X (t + 2) = false)

/-- `cnt f n`: the number of `i < n` with `f i`. -/
def cnt (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => cnt f n + (if f n then 1 else 0)

/-- Seed weight: the number of ones of `X` below `H`. -/
def A (X H : Nat) : Nat := cnt X.testBit H

/-- The right neighbour of bit `i`: the center value `b` for `i = 0`. -/
def rn (b : Bool) (X : Nat) : Nat → Bool
  | 0 => b
  | i + 1 => X.testBit i

theorem testBit_L (b : Bool) (X i : Nat) :
    (L b X).testBit i = xor (X.testBit (i + 1)) (X.testBit i || rn b X i) := by
  unfold L
  rw [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftRight, Nat.add_comm 1 i]
  cases i with
  | zero =>
    rw [testBit_two_mul_add_zero _ _ (by split <;> decide)]
    cases b <;> simp [rn]
  | succ j => rw [testBit_two_mul_add_succ _ _ _ (by split <;> decide)]; rfl

/-! ## The infinite model (rows as Boolean functions) -/

/-- One step of an infinite left half-row. -/
def stepF (b : Bool) (x : Nat → Bool) : Nat → Bool
  | 0 => xor (x 1) (x 0 || b)
  | i + 1 => xor (x (i + 2)) (x (i + 1) || x i)

/-- The infinite left half-row after `t` steps beside `c`. -/
def orbF (c : Nat → Bool) (x : Nat → Bool) : Nat → Nat → Bool
  | 0 => x
  | t + 1 => stepF (c t) (orbF c x t)

def kickF (c : Nat → Bool) (x : Nat → Bool) (t : Nat) : Bool :=
  xor (xor (orbF c x t 0) (c t)) (c (t + 1))

/-- The kick rules at time `t`. -/
def KRules (c : Nat → Bool) (x : Nat → Bool) (t : Nat) : Prop :=
  (kickF c x t = true → c t = false) ∧
  (kickF c x t = true → c (t + 1) = false → kickF c x (t + 1) = true) ∧
  (kickF c x t = true → c (t + 1) = true → kickF c x (t + 2) = false)

/-- The infinite row `x` satisfies the kick rules beside `c` at every time. -/
def Eternal (c : Nat → Bool) (x : Nat → Bool) : Prop := ∀ t, KRules c x t

/-- Agreement of a finite seed with an infinite row below `N` persists below `N - t`. -/
theorem orb_agree (c : Nat → Bool) (X : Nat) (x : Nat → Bool) :
    ∀ t N, (∀ i, i < N → X.testBit i = x i) →
      ∀ i, i + t < N → (orb c X t).testBit i = orbF c x t i := by
  intro t
  induction t with
  | zero => intro N h i hi; exact h i (by omega)
  | succ t ih =>
    intro N h i hi
    have e := ih N h
    show (L (c t) (orb c X t)).testBit i = stepF (c t) (orbF c x t) i
    rw [testBit_L]
    cases i with
    | zero =>
      show _ = xor (orbF c x t 1) (orbF c x t 0 || c t)
      rw [e 1 (by omega), e 0 (by omega)]; rfl
    | succ j =>
      show xor _ (_ || (orb c X t).testBit j) =
        xor (orbF c x t (j + 2)) (orbF c x t (j + 1) || orbF c x t j)
      rw [e (j + 2) (by omega), e (j + 1) (by omega), e j (by omega)]

/-- An eternal row gives valid finite words: any seed that agrees with it below `H` is a `GValid`
word of length `H`. -/
theorem gvalid_of_eternal {c : Nat → Bool} {x : Nat → Bool} (hx : Eternal c x) (X H : Nat)
    (h : ∀ i, i < H → X.testBit i = x i) : GValid c X H := by
  have hk : ∀ t, t < H → kick c X t = kickF c x t := by
    intro t ht
    unfold kick kickF tr
    rw [orb_agree c X x t H h 0 (by omega)]
  intro t ht
  obtain ⟨k1, k2, k3⟩ := hx t
  refine ⟨fun hd => k1 (by rw [← hk t ht]; exact hd), fun hd h1 h2 => ?_, fun hd h1 h2 => ?_⟩
  · rw [hk _ h2]; exact k2 (by rw [← hk t ht]; exact hd) h1
  · rw [hk _ h2]; exact k3 (by rw [← hk t ht]; exact hd) h1

/-! ## Counting -/

theorem cnt_congr {f g : Nat → Bool} {N : Nat} (h : ∀ i, i < N → f i = g i) :
    ∀ n, n ≤ N → cnt f n = cnt g n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih => intro hn; simp only [cnt]; rw [ih (by omega), h n (by omega)]

/-- the natural number with bits `f 0, …, f (n-1)`. -/
def enc (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => (if f n then 2 ^ n else 0) + enc f n

theorem enc_lt (f : Nat → Bool) : ∀ n, enc f n < 2 ^ n
  | 0 => by simp [enc]
  | n + 1 => by
    have := enc_lt f n
    simp only [enc]
    split <;> rw [Nat.pow_succ] <;> omega

theorem testBit_enc (f : Nat → Bool) : ∀ n i, (enc f n).testBit i = (decide (i < n) && f i)
  | 0, i => by simp [enc]
  | n + 1, i => by
    have ih := testBit_enc f n
    have hlt := enc_lt f n
    simp only [enc]
    rcases Nat.lt_trichotomy i n with h | h | h
    · split
      · rw [Nat.testBit_two_pow_add_gt h, ih]; simp [h, show i < n + 1 by omega]
      · rw [Nat.zero_add, ih]; simp [h, show i < n + 1 by omega]
    · subst h
      split
      · next hf => rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]; simp [hf]
      · next hf => rw [Nat.zero_add, Nat.testBit_lt_two_pow hlt]; simp [hf]
    · have h2 : (if f n then 2 ^ n else 0) + enc f n < 2 ^ i := by
        have : 2 ^ (n + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) h
        split <;> rw [Nat.pow_succ] at this <;> omega
      rw [Nat.testBit_lt_two_pow h2]; simp; omega

/-- The truncation of an infinite row to its first `H` depths, as a finite seed. -/
def trunc (x : Nat → Bool) (H : Nat) : Nat := enc x H

theorem trunc_lt (x : Nat → Bool) (H : Nat) : trunc x H < 2 ^ H := enc_lt x H

theorem testBit_trunc (x : Nat → Bool) (H i : Nat) (h : i < H) : (trunc x H).testBit i = x i := by
  unfold trunc; rw [testBit_enc]; simp [h]

theorem A_trunc (x : Nat → Bool) (H : Nat) : A (trunc x H) H = cnt x H :=
  cnt_congr (fun i hi => testBit_trunc x H i hi) H (Nat.le_refl _)

/-! ## Sideways reconstruction -/

/-- The space-time read sideways from the center column `c` (depth `0`) and the wall trace `s`
(depth `1`): `u d t` is the cell at depth `d` and time `t`. -/
def u (c s : Nat → Bool) : Nat → Nat → Bool
  | 0 => c
  | 1 => s
  | d + 2 => fun t => xor (u c s (d + 1) (t + 1)) (u c s (d + 1) t || u c s d t)

theorem u_step (c s : Nat → Bool) (d t : Nat) :
    u c s (d + 1) (t + 1) = xor (u c s (d + 2) t) (u c s (d + 1) t || u c s d t) := by
  show _ = xor (xor (u c s (d + 1) (t + 1)) (u c s (d + 1) t || u c s d t)) _
  cases u c s (d + 1) (t + 1) <;> cases (u c s (d + 1) t || u c s d t) <;> rfl

/-- **The sideways space-time is a genuine driven evolution** of its row at time `0`. -/
theorem orbF_sideways (c s : Nat → Bool) :
    ∀ t i, orbF c (fun i => u c s (i + 1) 0) t i = u c s (i + 1) t := by
  intro t
  induction t with
  | zero => intro i; rfl
  | succ t ih =>
    intro i
    cases i with
    | zero =>
      show xor (orbF c _ t 1) (orbF c _ t 0 || c t) = _
      rw [ih 1, ih 0, u_step c s 0 t]; rfl
    | succ j =>
      show xor (orbF c _ t (j + 2)) (orbF c _ t (j + 1) || orbF c _ t j) = _
      rw [ih (j + 2), ih (j + 1), ih j, u_step c s (j + 1) t]

theorem periodic_mod {f : Nat → Bool} {Q : Nat} (hf : ∀ t, f (t + Q) = f t) :
    ∀ t, f t = f (t % Q) := by
  have hk : ∀ k t, f (t + Q * k) = f t := by
    intro k
    induction k with
    | zero => intro t; rfl
    | succ k ih => intro t; rw [Nat.mul_succ, ← Nat.add_assoc, hf, ih]
  intro t
  have := hk (t / Q) (t % Q)
  rw [Nat.mod_add_div] at this
  exact this

theorem u_time_periodic (c s : Nat → Bool) (Q : Nat) (hc : ∀ t, c (t + Q) = c t)
    (hs : ∀ t, s (t + Q) = s t) : ∀ d, (∀ t, u c s d (t + Q) = u c s d t) ∧
      (∀ t, u c s (d + 1) (t + Q) = u c s (d + 1) t) := by
  intro d
  induction d with
  | zero => exact ⟨hc, hs⟩
  | succ d ih =>
    refine ⟨ih.2, fun t => ?_⟩
    show xor (u c s (d + 1) (t + Q + 1)) (u c s (d + 1) (t + Q) || u c s d (t + Q)) =
      xor (u c s (d + 1) (t + 1)) (u c s (d + 1) t || u c s d t)
    rw [show t + Q + 1 = (t + 1) + Q by omega, ih.2, ih.2, ih.1]

theorem u_depth_periodic (c s : Nat → Bool) (n : Nat) (h0 : ∀ t, u c s n t = c t)
    (h1 : ∀ t, u c s (n + 1) t = s t) : ∀ d, (∀ t, u c s (d + n) t = u c s d t) ∧
      (∀ t, u c s (d + 1 + n) t = u c s (d + 1) t) := by
  intro d
  induction d with
  | zero => exact ⟨fun t => by rw [Nat.zero_add]; exact h0 t, fun t => by
      rw [show 0 + 1 + n = n + 1 by omega]; exact h1 t⟩
  | succ d ih =>
    refine ⟨ih.2, fun t => ?_⟩
    rw [show d + 1 + 1 + n = (d + n) + 2 by omega]
    show xor (u c s (d + n + 1) (t + 1)) (u c s (d + n + 1) t || u c s (d + n) t) =
      xor (u c s (d + 1) (t + 1)) (u c s (d + 1) t || u c s d t)
    rw [show d + n + 1 = d + 1 + n by omega, ih.2, ih.2, ih.1]

/-! ### Columns over a finite time window, as natural numbers -/

/-- Column `d + 2` from columns `d` (`P`) and `d + 1` (`B`), bit `t` = time `t`. -/
def sw (P B : Nat) : Nat := (B >>> 1) ^^^ (B ||| P)

/-- The pair of columns at depths `d`, `d + 1`. -/
def cols (P B : Nat) : Nat → Nat × Nat
  | 0 => (P, B)
  | d + 1 => ((cols P B d).2, sw (cols P B d).1 (cols P B d).2)

theorem testBit_sw (P B t : Nat) :
    (sw P B).testBit t = xor (B.testBit (t + 1)) (B.testBit t || P.testBit t) := by
  unfold sw
  rw [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftRight, Nat.add_comm 1 t]

theorem cols_spec (c s : Nat → Bool) (T P B : Nat) (hP : ∀ t, t < T → P.testBit t = c t)
    (hB : ∀ t, t < T → B.testBit t = s t) : ∀ d,
      (∀ t, t + d < T → (cols P B d).1.testBit t = u c s d t) ∧
      (∀ t, t + d + 1 < T → (cols P B d).2.testBit t = u c s (d + 1) t) := by
  intro d
  induction d with
  | zero => exact ⟨fun t ht => hP t (by omega), fun t ht => hB t (by omega)⟩
  | succ d ih =>
    refine ⟨fun t ht => ih.2 t (by omega), fun t ht => ?_⟩
    show (sw (cols P B d).1 (cols P B d).2).testBit t = _
    rw [testBit_sw, ih.2 (t + 1) (by omega), ih.2 t (by omega), ih.1 t (by omega)]
    rfl

theorem testBit_of_mod_eq {X Y Q t : Nat} (h : X % 2 ^ Q = Y % 2 ^ Q) (ht : t < Q) :
    X.testBit t = Y.testBit t := by
  have h1 := Nat.testBit_mod_two_pow X Q t
  have h2 := Nat.testBit_mod_two_pow Y Q t
  rw [h] at h1
  rw [h1] at h2
  simpa [ht] using h2

/-- **Crystal criterion.** If `c` and `s` are `Q`-periodic and, over a window of length
`T ≥ Q + n + 1`, the column pair at depth `n` agrees with the pair at depth `0` on one period,
then the sideways space-time is `n`-periodic in depth. -/
theorem crystal (c s : Nat → Bool) (n Q T P B : Nat) (hQ : 0 < Q) (hT : Q + n + 1 ≤ T)
    (hc : ∀ t, c (t + Q) = c t) (hs : ∀ t, s (t + Q) = s t)
    (hP : ∀ t, t < T → P.testBit t = c t) (hB : ∀ t, t < T → B.testBit t = s t)
    (h1 : (cols P B n).1 % 2 ^ Q = P % 2 ^ Q) (h2 : (cols P B n).2 % 2 ^ Q = B % 2 ^ Q) :
    ∀ d t, u c s (d + n) t = u c s d t := by
  have hcs := cols_spec c s T P B hP hB n
  have hper := u_time_periodic c s Q hc hs
  have e0 : ∀ t, u c s n t = c t := by
    intro t
    rw [periodic_mod (hper n).1 t, periodic_mod hc t]
    have ht : t % Q < Q := Nat.mod_lt _ hQ
    rw [← hcs.1 _ (by omega), testBit_of_mod_eq h1 ht, hP _ (by omega)]
  have e1 : ∀ t, u c s (n + 1) t = s t := by
    intro t
    rw [periodic_mod (hper n).2 t, periodic_mod hs t]
    have ht : t % Q < Q := Nat.mod_lt _ hQ
    rw [← hcs.2 _ (by omega), testBit_of_mod_eq h2 ht, hB _ (by omega)]
  exact fun d => (u_depth_periodic c s n e0 e1 d).1

/-- Rows that agree on one period of a periodic pattern agree everywhere. -/
theorem row_ext {x y : Nat → Bool} {n : Nat} (hn : 0 < n) (hx : ∀ i, x (i + n) = x i)
    (hy : ∀ i, y (i + n) = y i) (h : ∀ i, i < n → x i = y i) : ∀ i, x i = y i := by
  intro i
  rw [periodic_mod hx i, periodic_mod hy i]
  exact h _ (Nat.mod_lt _ hn)

/-- The kick rules at one time, from the pattern and the trace at the next few times. -/
def KRv (c0 c1 c2 c3 s0 s1 s2 : Bool) : Bool :=
  let k0 := xor (xor s0 c0) c1
  let k1 := xor (xor s1 c1) c2
  let k2 := xor (xor s2 c2) c3
  (!k0 || !c0) && (!k0 || c1 || k1) && (!k0 || !c1 || !k2)

/-- The kick rules at time `t` only see the trace and the pattern at `t, …, t + 3`. -/
def KR (c s : Nat → Bool) (t : Nat) : Bool :=
  KRv (c t) (c (t + 1)) (c (t + 2)) (c (t + 3)) (s t) (s (t + 1)) (s (t + 2))

theorem krules_of_KR {c x : Nat → Bool} {s : Nat → Bool} (hs : ∀ t, orbF c x t 0 = s t) (t : Nat)
    (h : KR c s t = true) : KRules c x t := by
  have ek : ∀ t, kickF c x t = xor (xor (s t) (c t)) (c (t + 1)) := fun t => by
    unfold kickF; rw [hs]
  have e0 : kickF c x t = xor (xor (s t) (c t)) (c (t + 1)) := ek t
  have e1 : kickF c x (t + 1) = xor (xor (s (t + 1)) (c (t + 1))) (c (t + 2)) := ek (t + 1)
  have e2 : kickF c x (t + 2) = xor (xor (s (t + 2)) (c (t + 2))) (c (t + 3)) := ek (t + 2)
  unfold KRules
  rw [e0, e1, e2]
  unfold KR at h
  revert h
  generalize c t = a0; generalize c (t + 1) = a1; generalize c (t + 2) = a2
  generalize c (t + 3) = a3; generalize s t = b0; generalize s (t + 1) = b1
  generalize s (t + 2) = b2
  revert a0 a1 a2 a3 b0 b1 b2
  decide

/-- Eternal validity from one period of the kick rules. -/
theorem eternal_of_period {c x s : Nat → Bool} {Q : Nat} (hQ : 0 < Q) (hc : ∀ t, c (t + Q) = c t)
    (hsp : ∀ t, s (t + Q) = s t) (hs : ∀ t, orbF c x t 0 = s t)
    (h : ∀ t, t < Q → KR c s t = true) : Eternal c x := by
  have hKR : ∀ t, KR c s (t + Q) = KR c s t := by
    intro t; unfold KR
    rw [show t + Q + 1 = (t + 1) + Q by omega, show t + Q + 2 = (t + 2) + Q by omega,
      show t + Q + 3 = (t + 3) + Q by omega, hc, hc, hc, hc, hsp, hsp, hsp]
  intro t
  apply krules_of_KR hs
  have : ∀ t, KR c s t = KR c s (t % Q) := by
    intro t
    have hk : ∀ k t, KR c s (t + Q * k) = KR c s t := by
      intro k
      induction k with
      | zero => intro t; rfl
      | succ k ih => intro t; rw [Nat.mul_succ, ← Nat.add_assoc, hKR, ih]
    have := hk (t / Q) (t % Q)
    rw [Nat.mod_add_div] at this
    exact this
  rw [this]; exact h _ (Nat.mod_lt _ hQ)

/-! ## The ring patterns -/

/-- The ring of `n` cells, bit `j` = the cell `j` places to the left of the center cell `0`;
one rule 30 step (rotations by one place). -/
def ringStep (n R : Nat) : Nat :=
  ((R >>> 1) ||| ((R % 2) <<< (n - 1))) ^^^ (R ||| (((R <<< 1) % 2 ^ n) ||| (R >>> (n - 1))))

/-- `T` steps from `R`: the final ring and the word read at cell `0`. -/
def ringRun (n : Nat) : Nat → Nat → Nat × Nat
  | R, 0 => (R, 0)
  | R, T + 1 => ((ringRun n (ringStep n R) T).1, R % 2 + 2 * (ringRun n (ringStep n R) T).2)

/-! ### The 9-ring, period 72 -/

/-- The word of period `72` read at the left neighbour of a single black cell on a ring of `9`
cells. -/
def W9 : Nat := 4305985432940904591782

def c9 (t : Nat) : Bool := W9.testBit (t % 72)

/-- `c9` is the ring word (the ring starts from the single black cell `2^8`, which is the right
neighbour of cell `0`), and the ring is periodic from time `1` with period `72`. -/
theorem c9_ring : (ringRun 9 256 72).2 = W9 ∧ (ringRun 9 256 73).1 = ringStep 9 256 := by
  decide +kernel

theorem c9_period (t : Nat) : c9 (t + 72) = c9 t := by
  unfold c9; rw [Nat.add_mod_right]

/-- The row at time `0`: black exactly at depths `8, 17, 26, …`. -/
def row9 (i : Nat) : Bool := i % 9 == 7

/-- The periodic system from time `1`: the shifted pattern and its trace. -/
def W9s : Nat := 2152992716470452295891
def S9s : Nat := 3664891428301968733366
def c9s (t : Nat) : Bool := W9s.testBit (t % 72)
def s9s (t : Nat) : Bool := S9s.testBit (t % 72)

theorem c9s_eq (t : Nat) : c9s t = c9 (t + 1) := by
  have h1 : ∀ t, c9s (t + 72) = c9s t := fun t => by unfold c9s; rw [Nat.add_mod_right]
  have h2 : ∀ t, c9 (t + 1 + 72) = c9 (t + 1) := fun t => by
    rw [show t + 1 + 72 = (t + 1) + 72 by omega, c9_period]
  exact row_ext (x := c9s) (y := fun t => c9 (t + 1)) (by decide) h1 h2
    (by intro i hi; revert i; decide +kernel) t

/-- The row at time `1`: black exactly at depths `≡ 7, 8, 0 (mod 9)`. -/
def row9s (i : Nat) : Bool := decide (6 ≤ i % 9)

theorem row9s_sideways : ∀ i, u c9s s9s (i + 1) 0 = row9s i := by
  have hd := crystal c9s s9s 9 72 82 (W9s ||| (W9s <<< 72)) (S9s ||| (S9s <<< 72)) (by decide)
    (by decide) (fun t => by unfold c9s; rw [Nat.add_mod_right])
    (fun t => by unfold s9s; rw [Nat.add_mod_right])
    (by intro t ht; revert t; decide +kernel) (by intro t ht; revert t; decide +kernel)
    (by decide +kernel) (by decide +kernel)
  apply row_ext (by decide : 0 < 9)
  · intro i; rw [show i + 9 + 1 = (i + 1) + 9 by omega]; exact hd (i + 1) 0
  · intro i; unfold row9s; rw [Nat.add_mod_right]
  · have hP : ∀ t, t < 82 → (W9s ||| (W9s <<< 72)).testBit t = c9s t := by
      intro t ht; revert t; decide +kernel
    have hB : ∀ t, t < 82 → (S9s ||| (S9s <<< 72)).testBit t = s9s t := by
      intro t ht; revert t; decide +kernel
    have hcs := cols_spec c9s s9s 82 _ _ hP hB
    intro i hi
    rw [← (hcs (i + 1)).1 0 (by omega)]
    revert i; decide +kernel

/-- One step joins the row at time `0` to the periodic system. -/
theorem step_row9 : stepF (c9 0) row9 = row9s := by
  funext i
  cases i with
  | zero => decide
  | succ j =>
    show xor (row9 (j + 2)) (row9 (j + 1) || row9 j) = row9s (j + 1)
    have h1 : ∀ j, xor (row9 (j + 9 + 2)) (row9 (j + 9 + 1) || row9 (j + 9)) =
        xor (row9 (j + 2)) (row9 (j + 1) || row9 j) := by
      intro j; unfold row9
      rw [show j + 9 + 2 = (j + 2) + 9 by omega, show j + 9 + 1 = (j + 1) + 9 by omega,
        Nat.add_mod_right, Nat.add_mod_right, Nat.add_mod_right]
    have h2 : ∀ j, row9s (j + 9 + 1) = row9s (j + 1) := by
      intro j; unfold row9s; rw [show j + 9 + 1 = (j + 1) + 9 by omega, Nat.add_mod_right]
    exact row_ext (x := fun j => xor (row9 (j + 2)) (row9 (j + 1) || row9 j))
      (y := fun j => row9s (j + 1)) (by decide) h1 h2 (by decide) j

theorem orbF_shift (c x : Nat → Bool) :
    ∀ t, orbF c x (t + 1) = orbF (fun t => c (t + 1)) (stepF (c 0) x) t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih => show stepF (c (t + 1)) (orbF c x (t + 1)) = _; rw [ih]; rfl

theorem orbF_row9 (t : Nat) : orbF c9 row9 (t + 1) = orbF c9s row9s t := by
  rw [orbF_shift, step_row9]
  have : (fun t => c9 (t + 1)) = c9s := funext fun t => (c9s_eq t).symm
  rw [this]

/-- **The eternal sparse row beside `c9`**: the infinite row black exactly at depths
`8, 17, 26, …` satisfies the kick rules at every time. -/
theorem eternal_row_c9 : Eternal c9 row9 := by
  have hrow : (fun i => u c9s s9s (i + 1) 0) = row9s := funext row9s_sideways
  have hs : ∀ t, orbF c9s row9s t 0 = s9s t := by
    intro t; rw [← hrow, orbF_sideways]; rfl
  have hes : Eternal c9s row9s :=
    eternal_of_period (by decide : 0 < 72) (fun t => by unfold c9s; rw [Nat.add_mod_right])
      (fun t => by unfold s9s; rw [Nat.add_mod_right]) hs
      (by intro t ht; revert t; decide +kernel)
  intro t
  cases t with
  | zero =>
    have e1 : kickF c9 row9 1 = kickF c9s row9s 0 := by
      unfold kickF; rw [orbF_row9, c9s_eq, c9s_eq]
    have e2 : kickF c9 row9 2 = kickF c9s row9s 1 := by
      unfold kickF; rw [orbF_row9, c9s_eq, c9s_eq]
    have h1 : kickF c9s row9s 1 = xor (xor (s9s 1) (c9s 1)) (c9s 2) := by
      unfold kickF; rw [hs]
    refine ⟨fun _ => by decide, fun _ h => absurd h (by decide), fun _ _ => ?_⟩
    rw [e2, h1]; decide
  | succ t =>
    have ek : ∀ t, kickF c9 row9 (t + 1) = kickF c9s row9s t := by
      intro t; unfold kickF; rw [orbF_row9, c9s_eq, c9s_eq]
    obtain ⟨k1, k2, k3⟩ := hes t
    refine ⟨fun h => ?_, fun h h1 => ?_, fun h h1 => ?_⟩
    · rw [ek] at h; rw [← c9s_eq]; exact k1 h
    · rw [ek] at h; rw [show t + 1 + 1 = (t + 1) + 1 from rfl, ek]
      exact k2 h (by rw [c9s_eq]; exact h1)
    · rw [ek] at h; rw [show t + 1 + 2 = (t + 2) + 1 by omega, ek]
      exact k3 h (by rw [c9s_eq]; exact h1)

theorem cnt_row9 : ∀ H, cnt row9 H = (H + 1) / 9 := by
  intro H
  induction H with
  | zero => rfl
  | succ H ih =>
    simp only [cnt, ih, row9]
    by_cases h : H % 9 = 7
    · simp [h]; omega
    · simp [h]; omega

/-- **Weight of the row**: `(H + 1) / 9` blacks among the first `H` depths. -/
theorem weight_row9 (H : Nat) : A (trunc row9 H) H = (H + 1) / 9 := by
  rw [A_trunc, cnt_row9]

/-- **Every truncation is a valid finite word of its length.** -/
theorem trunc_valid_c9 (H : Nat) : GValid c9 (trunc row9 H) H :=
  gvalid_of_eternal eternal_row_c9 _ H (fun i hi => testBit_trunc row9 H i hi)

/-- **No floor with `q < 9`** on the finite valid words of `c9`: for every `q < 9` and `d`,
some finite seed `X < 2^H` is `GValid` beside `c9` with `q · A + d < H`. -/
theorem no_floor_c9 (q d : Nat) (hq : q < 9) :
    ¬ ∀ H X, X < 2 ^ H → GValid c9 X H → H ≤ q * A X H + d := by
  intro h
  have := h (9 * (d + 2) - 1) _ (trunc_lt _ _) (trunc_valid_c9 _)
  rw [weight_row9, show (9 * (d + 2) - 1 + 1) / 9 = d + 2 by omega] at this
  have : q * (d + 2) ≤ 8 * (d + 2) := Nat.mul_le_mul_right _ (by omega)
  omega

/-! ### The 14-ring, period 1428 -/

/-- The word of period `1428` read at the single black cell of a ring of `14` cells. -/
def W14 : Nat := 7279963326518917374881119218579835797241273937427669905165229552923598254329790372197075067939336437210203085396934029918679273212362490699066945313768554644044880141566992943545279983744127997974437136206820707075719102222572857343268438538700524587876652312069376832738268056867071563216107103900169195267507464095189388632579404291020166416426759839284488017174801132588296382116118254439251145320180218537536858045418778813243

/-- The wall trace of the eternal row (one period). -/
def S14 : Nat := 192008019358207537594445215092237283763415369921647273125793890837374617033670591376996690001133713277370455926157238175945735640870139934975841080949218432635771720329291733772410245054448734748710491406692570952692667656841113017475033842874369633050893314079307851063576656215913944656788765682432625469661831410161405705668931375128430834028397341887415583880523850614056943668986558804137490353435087584237462619556472475302

def c14 (t : Nat) : Bool := W14.testBit (t % 1428)
def s14 (t : Nat) : Bool := S14.testBit (t % 1428)

/-- `c14` is the ring word, and the ring is periodic from time `0` with period `1428`. -/
theorem c14_ring : ringRun 14 1 1428 = (1, W14) := by decide +kernel

theorem c14_period (t : Nat) : c14 (t + 1428) = c14 t := by
  unfold c14; rw [Nat.add_mod_right]

/-- The row at time `0`: black exactly at depths `14, 28, 42, …`. -/
def row14 (i : Nat) : Bool := i % 14 == 13

theorem row14_sideways : ∀ i, u c14 s14 (i + 1) 0 = row14 i := by
  have hP : ∀ t, t < 1444 → (W14 ||| (W14 <<< 1428)).testBit t = c14 t := by
    intro t ht; revert t; decide +kernel
  have hB : ∀ t, t < 1444 → (S14 ||| (S14 <<< 1428)).testBit t = s14 t := by
    intro t ht; revert t; decide +kernel
  have hd := crystal c14 s14 14 1428 1444 _ _ (by decide) (by decide)
    (fun t => by unfold c14; rw [Nat.add_mod_right]) (fun t => by unfold s14; rw [Nat.add_mod_right])
    hP hB (by decide +kernel) (by decide +kernel)
  apply row_ext (by decide : 0 < 14)
  · intro i; rw [show i + 14 + 1 = (i + 1) + 14 by omega]; exact hd (i + 1) 0
  · intro i; unfold row14; rw [Nat.add_mod_right]
  · have hcs := cols_spec c14 s14 1444 _ _ hP hB
    intro i hi
    rw [← (hcs (i + 1)).1 0 (by omega)]
    revert i; decide +kernel

/-- **The eternal sparse row beside `c14`**: the infinite row black exactly at depths
`14, 28, 42, …` satisfies the kick rules at every time. -/
theorem eternal_row_c14 : Eternal c14 row14 := by
  have hrow : (fun i => u c14 s14 (i + 1) 0) = row14 := funext row14_sideways
  have hs : ∀ t, orbF c14 row14 t 0 = s14 t := by
    intro t; rw [← hrow, orbF_sideways]; rfl
  exact eternal_of_period (by decide : 0 < 1428) c14_period
    (fun t => by unfold s14; rw [Nat.add_mod_right]) hs
    (by intro t ht; revert t; decide +kernel)

theorem cnt_row14 : ∀ H, cnt row14 H = H / 14 := by
  intro H
  induction H with
  | zero => rfl
  | succ H ih =>
    simp only [cnt, ih, row14]
    by_cases h : H % 14 = 13
    · simp [h]; omega
    · simp [h]; omega

/-- **Weight of the row**: `H / 14` blacks among the first `H` depths. -/
theorem weight_row14 (H : Nat) : A (trunc row14 H) H = H / 14 := by
  rw [A_trunc, cnt_row14]

theorem trunc_valid_c14 (H : Nat) : GValid c14 (trunc row14 H) H :=
  gvalid_of_eternal eternal_row_c14 _ H (fun i hi => testBit_trunc row14 H i hi)

/-- **No floor with `q < 14`** on the finite valid words of `c14`. -/
theorem no_floor_c14 (q d : Nat) (hq : q < 14) :
    ¬ ∀ H X, X < 2 ^ H → GValid c14 X H → H ≤ q * A X H + d := by
  intro h
  have := h (14 * (d + 2)) _ (trunc_lt _ _) (trunc_valid_c14 _)
  rw [weight_row14, show 14 * (d + 2) / 14 = d + 2 by omega] at this
  have : q * (d + 2) ≤ 13 * (d + 2) := Nat.mul_le_mul_right _ (by omega)
  omega

/-- **No uniform floor above `1/14`.** A floor `H ≤ q·A + d` on the finite valid words that holds
for every periodic pattern, with `q < 14`, fails already for `c14`; with `q < 9` it fails for
`c9` too. -/
theorem no_uniform_floor (q d : Nat) (hq : q < 14) :
    ¬ ∀ (c : Nat → Bool), (∃ P, 0 < P ∧ ∀ t, c (t + P) = c t) →
      ∀ H X, X < 2 ^ H → GValid c X H → H ≤ q * A X H + d := by
  intro h
  exact no_floor_c14 q d hq (h c14 ⟨1428, by decide, c14_period⟩)

/-! ## Multi-period spatial invariance and exact block weights for `row9` and `row14` -/

/-- **Multi-Period Spatial Invariance and Exact Block Weights for `row9` and `row14` (`row9_row14_period_mul_and_exact_block_weights`).** -/
theorem row9_row14_period_mul_and_exact_block_weights (i k : Nat) :
    row9 (i + 9 * k) = row9 i ∧
    row14 (i + 14 * k) = row14 i ∧
    A (trunc row9 (9 * k)) (9 * k) = k ∧
    A (trunc row14 (14 * k)) (14 * k) = k := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold row9
    rw [show i + 9 * k = i + k * 9 by omega, Nat.add_mul_mod_self_right]
  · unfold row14
    rw [show i + 14 * k = i + k * 14 by omega, Nat.add_mul_mod_self_right]
  · rw [weight_row9]
    omega
  · rw [weight_row14]
    omega

end Rule30PeriodTwoNoFloor
end Ruliology.CellularAutomata
