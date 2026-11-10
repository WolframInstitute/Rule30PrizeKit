module

public import Ruliology.CellularAutomata.Rule30PeriodTwo
public import Ruliology.CellularAutomata.Rule30RecordCharge

/-!
# Rule 30: period 2 of the center column and the Mean Ladder Law

**The model.** The left half-row of rule 30 is a natural number `X` (bit `i` = cell `-1 - i`),
and `orb c X t` is its evolution with the center column prescribed by `c` (`L b X` is one exact
step with center `b`). The wall trace is `tr c X t` (column `-1`), the kick is
`kick c X t = tr c X t xor c t xor c (t + 1)`, and `GValid c X H` imposes on the first `H` steps
the three kick rules K1-K3 that the real pattern satisfies beside a center equal to `c`
(`gvalid_rowNat`: the official left half-row at any time `T` is valid for ever with `c` the
official center from `T` on). `NoSeed c`: no nonzero finite seed is valid for ever.

**Connection to the kit.** For the period-2 pattern `p01` (`c t = t mod 2`):
* `orb_zero_eq_L`: the model's zero-driven left half is `Rule30DrivenLeft.L (fun _ => false)` on
  finite starts, and `orb_p01_eq_orb_zero`: a seed valid for ever evolves as the zero-driven half.
* `noSeed01_of_Q01`: `Rule30PeriodTwo.Q01` implies `NoSeed p01`.
* `not_eventually_period_two_of_noSeed01`: `NoSeed p01` excludes an eventual period 2 of the
  official center column (through `Rule30PeriodTwo.normalize`).

**The Mean Ladder Law.** Counts are `Rule30RecordCharge.countBelow` (the number of `k < N` with a
property) and sums are `sumBelow`. `S n l` counts the seeds of bitlength exactly `n` that stay
valid `l` steps past `n`, and `V n = S n 0`.
* `orb_flip`, `kick_flip`, `gvalid_flip`: adding `2^t` to a seed flips exactly the cells on the
  antidiagonal `i + s = t` below it (left permutivity, the triangular trace-seed bijection).
* `pair_count`: the two seeds `Z`, `2^H + Z` together contribute exactly the transition count of
  the fair-coin chain at tick `H`.
* `mean_ladder`, `fill_eq`: over all `2^l` fillings `y` of the next `l` seed digits, the number of
  seeds `X0 + 2^n y` valid to `n + l` is exactly the number of legal kick words of the coin chain.
* `card_valid`: there are exactly `fib ((H + 1) / 2 + 2)` valid seeds below `2^H` (`fib` is the
  Fibonacci sequence `0, 1, 1, 2, 3, …`).
* `ladder_average`, `S_le_Scoin`: the coin ladder `Scoin n l` is the sum over all `2^l` digit
  blocks; the true ladder `S n l` is the single zero block.

**What would close period 2.** `noSeed_iff_S_eventually_zero`: `NoSeed p01` holds if and only if,
for every bitlength `n ≥ 1`, `S n l = 0` for some `l`. So a geometric ladder bound
`S n (2 j) ≤ C V(n) θ^j` with rational `C`, `θ` and `0 ≤ θ < 1` gives `NoSeed p01`
(`noSeed_of_geometric_ladder_bound`), and with it
`not_eventually_period_two_of_geometric_ladder_bound`;
`noSeed_of_half_ladder_bound` and `not_eventually_period_two_of_ladder_bound` are the form
`S n (2 j) 2^j ≤ C V(n)` in natural numbers.

`NoSeed p01` and the ladder bounds are **open**. The Mean Ladder Law is exact for the average over
all digit blocks; a finite seed is the all-zero block, about which the average says nothing.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30PeriodTwoLadder

/-! ## Finite sums and the Fibonacci numbers -/

/-- `sumBelow f N = f 0 + ⋯ + f (N - 1)`. -/
def sumBelow (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumBelow f n + f n

/-- The Fibonacci numbers `0, 1, 1, 2, 3, 5, …`. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

theorem fib_add_two (n : Nat) : fib (n + 2) = fib n + fib (n + 1) := rfl

section Sums
open Rule30RecordCharge

theorem sumBelow_congr {f g : Nat → Nat} : ∀ n, (∀ k, k < n → f k = g k) →
    sumBelow f n = sumBelow g n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [sumBelow]
    rw [sumBelow_congr n (fun k hk => h k (by omega)), h n (by omega)]

theorem sumBelow_add_distrib (f g : Nat → Nat) : ∀ n,
    sumBelow (fun k => f k + g k) n = sumBelow f n + sumBelow g n
  | 0 => rfl
  | n + 1 => by
    simp only [sumBelow]
    rw [sumBelow_add_distrib f g n]; omega

theorem sumBelow_mul_right (f : Nat → Nat) (a : Nat) : ∀ n,
    sumBelow (fun k => f k * a) n = sumBelow f n * a
  | 0 => by simp [sumBelow]
  | n + 1 => by
    simp only [sumBelow]
    rw [sumBelow_mul_right f a n, Nat.add_mul]

theorem sumBelow_append (f : Nat → Nat) (m : Nat) : ∀ n,
    sumBelow f (m + n) = sumBelow f m + sumBelow (fun k => f (m + k)) n
  | 0 => rfl
  | n + 1 => by
    rw [show m + (n + 1) = (m + n) + 1 by omega]
    simp only [sumBelow]
    rw [sumBelow_append f m n]; omega

theorem sumBelow_comm (f : Nat → Nat → Nat) (N : Nat) : ∀ M,
    sumBelow (fun y => sumBelow (fun X => f y X) N) M =
      sumBelow (fun X => sumBelow (fun y => f y X) M) N
  | 0 => by
    simp only [sumBelow]
    have : ∀ n, sumBelow (fun _ => 0) n = 0 := by
      intro n; induction n with
      | zero => rfl
      | succ n ih => simp [sumBelow, ih]
    exact (this N).symm
  | M + 1 => by
    simp only [sumBelow]
    rw [sumBelow_comm f N M, ← sumBelow_add_distrib]

theorem le_sumBelow (f : Nat → Nat) {k : Nat} : ∀ n, k < n → f k ≤ sumBelow f n
  | 0, h => absurd h (Nat.not_lt_zero k)
  | n + 1, h => by
    simp only [sumBelow]
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
    · have := le_sumBelow f n h; omega
    · subst h; omega

theorem countBelow_eq_sumBelow (p : Nat → Prop) [DecidablePred p] : ∀ n,
    countBelow p n = sumBelow (fun k => if p k then 1 else 0) n
  | 0 => rfl
  | n + 1 => by
    simp only [countBelow, sumBelow]
    rw [countBelow_eq_sumBelow p n]

theorem countBelow_congr {p q : Nat → Prop} [DecidablePred p] [DecidablePred q] (n : Nat)
    (h : ∀ k, k < n → (p k ↔ q k)) : countBelow p n = countBelow q n := by
  rw [countBelow_eq_sumBelow, countBelow_eq_sumBelow]
  apply sumBelow_congr n
  intro k hk
  by_cases hp : p k
  · rw [ite_eq_left hp, ite_eq_left ((h k hk).1 hp)]
  · rw [ite_eq_right hp, ite_eq_right (fun hq => hp ((h k hk).2 hq))]

theorem countBelow_eq_zero (p : Nat → Prop) [DecidablePred p] : ∀ n,
    countBelow p n = 0 ↔ ∀ k, k < n → ¬ p k
  | 0 => ⟨fun _ k hk => absurd hk (Nat.not_lt_zero k), fun _ => rfl⟩
  | n + 1 => by
    simp only [countBelow]
    rw [Nat.add_eq_zero_iff, countBelow_eq_zero p n]
    constructor
    · rintro ⟨h1, h2⟩ k hk hpk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
      · exact h1 k hk hpk
      · subst hk; rw [ite_eq_left hpk] at h2; exact absurd h2 (by decide)
    · intro h
      refine ⟨fun k hk => h k (by omega), ?_⟩
      rw [ite_eq_right (h n (by omega))]

end Sums

/-! ## The model: the left half-row as a natural number, driven by a center pattern -/

section Model

/-- One exact Rule 30 step of the left half-row `X` (bit `i` = cell `-1-i`) when the center
cell is `b`. -/
def L (b : Bool) (X : Nat) : Nat := (X >>> 1) ^^^ (X ||| ((X <<< 1) ||| b.toNat))

/-- The right neighbour of bit `i` of the left half-row: the center bit `b` for `i = 0`. -/
def rn (b : Bool) (X : Nat) : Nat → Bool
  | 0 => b
  | i + 1 => X.testBit i

/-- The left half-row after `t` steps, driven by the center pattern `c`. -/
def orb (c : Nat → Bool) (X : Nat) : Nat → Nat
  | 0 => X
  | t + 1 => L (c t) (orb c X t)

/-- The wall trace `a_t` (column `-1`). -/
def tr (c : Nat → Bool) (X t : Nat) : Bool := (orb c X t).testBit 0

/-- The kick `d_t = a_t xor c_t xor c_{t+1}`. -/
def kick (c : Nat → Bool) (X t : Nat) : Bool := tr c X t ^^ c t ^^ c (t + 1)

/-- The language `G_c` on prefixes of length `H` (kick rules K1–K3, prefix semantics). -/
def GValid (c : Nat → Bool) (X H : Nat) : Prop :=
  ∀ t, t < H →
    (kick c X t = true → c t = false) ∧
    (kick c X t = true → c (t + 1) = false → t + 1 < H → kick c X (t + 1) = true) ∧
    (kick c X t = true → c (t + 1) = true → t + 2 < H → kick c X (t + 2) = false)

instance instDecidableGValid (c : Nat → Bool) (X H : Nat) : Decidable (GValid c X H) := by
  unfold GValid; infer_instance

/-- **The weakest hypothesis for one pattern `c`**: no nonzero finite natural left seed has an
infinite `G_c` trace. -/
def NoSeed (c : Nat → Bool) : Prop := ∀ X : Nat, X ≠ 0 → ¬ ∀ H, GValid c X H

/-! ### Basic lemmas -/

theorem testBit_L (b : Bool) (X i : Nat) :
    (L b X).testBit i = (X.testBit (i + 1) ^^ (X.testBit i || rn b X i)) := by
  unfold L
  rw [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_or, Nat.testBit_shiftRight,
    Nat.testBit_shiftLeft, Nat.testBit_bool_toNat, Nat.add_comm 1 i]
  cases i with
  | zero => cases b <;> simp [rn]
  | succ j => simp [rn]

theorem orb_succ (c : Nat → Bool) (X t : Nat) : orb c X (t + 1) = L (c t) (orb c X t) := rfl

/-! ### Causality: the trace prefix of length `H` depends only on `X mod 2^H` -/

theorem L_agree {b : Bool} {X X' N : Nat} (h : ∀ i < N, X.testBit i = X'.testBit i) :
    ∀ i, i + 1 < N → (L b X).testBit i = (L b X').testBit i := by
  intro i hi
  rw [testBit_L, testBit_L, h (i + 1) hi, h i (by omega)]
  cases i with
  | zero => rfl
  | succ j => simp only [rn]; rw [h j (by omega)]

theorem orb_agree (c : Nat → Bool) {X X' : Nat} : ∀ t N, (∀ i < N, X.testBit i = X'.testBit i) →
    ∀ i, i + t < N → (orb c X t).testBit i = (orb c X' t).testBit i := by
  intro t
  induction t with
  | zero => intro N h i hi; exact h i (by omega)
  | succ t ih =>
    intro N h i hi
    rw [orb_succ, orb_succ]
    have := ih N h
    exact L_agree (N := N - t) (fun j hj => this j (by omega)) i (by omega)

end Model

/-! ## The official pattern in the model -/

section Official
open Rule30Jen Rule30Prize

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

/-- the left half of the official row at time `t` (bit `i` = cell `-1-i`). -/
def rowNat (t : Nat) : Nat := enc (fun i => cell t (-1 - (i : Int))) (t + 1)

theorem testBit_rowNat (t i : Nat) : (rowNat t).testBit i = cell t (-1 - (i : Int)) := by
  unfold rowNat
  rw [testBit_enc]
  by_cases h : i < t + 1
  · simp [h]
  · simp only [h, decide_false, Bool.false_and]
    exact (cell_eq_false_of_lt t _ (by omega)).symm

theorem cell_succ (t : Nat) (p : Int) :
    cell (t + 1) p = (cell t (p - 1) ^^ (cell t p || cell t (p + 1))) := rfl

/-- one official step of the left half-row is the model step `L` with the official center. -/
theorem rowNat_succ (t : Nat) : rowNat (t + 1) = L (center t) (rowNat t) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_L, testBit_rowNat, testBit_rowNat, testBit_rowNat, cell_succ,
    show (-1 - (i : Int) - 1) = -1 - ((i + 1 : Nat) : Int) by omega]
  cases i with
  | zero =>
    simp only [rn, center]
    rw [show (-1 - ((0 : Nat) : Int) + 1) = 0 by omega]
  | succ k =>
    simp only [rn]
    rw [testBit_rowNat, show (-1 - ((k + 1 : Nat) : Int) + 1) = -1 - (k : Int) by omega]

/-- the `c`-driven model from the official row at time `T` is the official evolution. -/
theorem orb_rowNat (T : Nat) (c : Nat → Bool) (hc : ∀ s, center (T + s) = c s) :
    ∀ s, orb c (rowNat T) s = rowNat (T + s) := by
  intro s
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [orb_succ, ih, ← hc s, ← rowNat_succ]; rfl

theorem tr_rowNat (T : Nat) (c : Nat → Bool) (hc : ∀ s, center (T + s) = c s) (s : Nat) :
    tr c (rowNat T) s = cell (T + s) (-1) := by
  unfold tr
  rw [orb_rowNat T c hc s, testBit_rowNat]; simp

/-- the kick in the real pattern: `d_s = r_s ∧ ¬ c_s`, with `r_s` = column `1`. -/
theorem kick_rowNat (T : Nat) (c : Nat → Bool) (hc : ∀ s, center (T + s) = c s) (s : Nat) :
    kick c (rowNat T) s = (cell (T + s) 1 && !cell (T + s) 0) := by
  unfold kick
  rw [tr_rowNat T c hc, ← hc s, ← hc (s + 1)]
  unfold center
  rw [show T + (s + 1) = (T + s) + 1 by omega, cell_succ]
  simp only [show (0 : Int) - 1 = -1 by rfl, show (0 : Int) + 1 = 1 by rfl]
  cases cell (T + s) (-1) <;> cases cell (T + s) 0 <;> cases cell (T + s) 1 <;> rfl

/-- **Validity of the official row**: for ANY `c` that the official center follows from time `T`
on, the official left half-row at time `T` is a finite seed whose `G_c` trace is valid forever. -/
theorem gvalid_rowNat (T : Nat) (c : Nat → Bool) (hc : ∀ s, center (T + s) = c s) :
    ∀ H, GValid c (rowNat T) H := by
  intro H t _
  have hk := kick_rowNat T c hc
  have c0 : ∀ s, c s = cell (T + s) 0 := fun s => (hc s).symm
  -- the official step for column 1 at times `T+t` and `T+t+1`
  have r1 : cell (T + (t + 1)) 1 = (cell (T + t) 0 ^^ (cell (T + t) 1 || cell (T + t) 2)) := by
    rw [show T + (t + 1) = (T + t) + 1 by omega, cell_succ]; rfl
  have r2 : cell (T + (t + 2)) 1 =
      (cell (T + (t + 1)) 0 ^^ (cell (T + (t + 1)) 1 || cell (T + (t + 1)) 2)) := by
    rw [show T + (t + 2) = (T + (t + 1)) + 1 by omega, cell_succ]; rfl
  refine ⟨fun h => ?_, fun h h1 _ => ?_, fun h h1 _ => ?_⟩
  · rw [hk, Bool.and_eq_true] at h
    rw [c0]; simpa using h.2
  · rw [hk, Bool.and_eq_true] at h
    rw [c0] at h1
    rw [hk, Bool.and_eq_true, r1, h1]
    simp only [Bool.not_eq_true'] at h
    rw [h.1, h.2]; simp
  · rw [hk, Bool.and_eq_true] at h
    rw [c0] at h1
    rw [hk, r2, h1, r1]
    simp only [Bool.not_eq_true'] at h
    rw [h.1, h.2]; simp

/-- the official left half-row is nonzero from time `1` on (its left edge is black). -/
theorem rowNat_ne_zero (T : Nat) (hT : 1 ≤ T) : rowNat T ≠ 0 := by
  intro h0
  have := testBit_rowNat T (T - 1)
  rw [h0, Nat.zero_testBit, show (-1 - ((T - 1 : Nat) : Int)) = -(T : Int) by omega,
    cell_left_edge] at this
  exact absurd this (by decide)

/-- the weakest hypothesis for one `c` excludes `center (T + s) = c s` for every `T ≥ 1`. -/
theorem not_center_eventually_of_noSeed (c : Nat → Bool) (h : NoSeed c) :
    ¬ ∃ T, 1 ≤ T ∧ ∀ s, center (T + s) = c s := by
  rintro ⟨T, hT, hc⟩
  exact h (rowNat T) (rowNat_ne_zero T hT) (gvalid_rowNat T c hc)

end Official

/-! ## The Mean Ladder Law -/

section Ladder
open Rule30RecordCharge

/-! ### The flip lemma (triangular bijection) -/

theorem agree_pow (X t : Nat) : ∀ i < t, (2 ^ t + X).testBit i = X.testBit i :=
  fun _ hi => Nat.testBit_two_pow_add_gt hi X

theorem orb_flip_lt (c : Nat → Bool) (X t s i : Nat) (h : i + s < t) :
    (orb c (2 ^ t + X) s).testBit i = (orb c X s).testBit i :=
  orb_agree c s t (agree_pow X t) i h

theorem orb_flip (c : Nat → Bool) (X t : Nat) :
    ∀ s i, i + s = t → (orb c (2 ^ t + X) s).testBit i = !(orb c X s).testBit i := by
  intro s
  induction s with
  | zero =>
    intro i hi
    simp only [orb, Nat.add_zero] at hi ⊢
    subst hi
    exact Nat.testBit_two_pow_add_eq X i
  | succ s ih =>
    intro i hi
    rw [orb_succ, orb_succ, testBit_L, testBit_L, ih (i + 1) (by omega),
      orb_flip_lt c X t s i (by omega)]
    have hr : rn (c s) (orb c (2 ^ t + X) s) i = rn (c s) (orb c X s) i := by
      cases i with
      | zero => rfl
      | succ j => simp only [rn]; exact orb_flip_lt c X t s j (by omega)
    rw [hr]
    cases (orb c X s).testBit (i + 1) <;> simp

theorem tr_flip (c : Nat → Bool) (X t : Nat) : tr c (2 ^ t + X) t = !tr c X t :=
  orb_flip c X t t 0 (by omega)

theorem tr_flip_lt (c : Nat → Bool) (X t s : Nat) (h : s < t) : tr c (2 ^ t + X) s = tr c X s :=
  orb_flip_lt c X t s 0 (by omega)

theorem kick_flip (c : Nat → Bool) (X t : Nat) : kick c (2 ^ t + X) t = !kick c X t := by
  unfold kick; rw [tr_flip]; cases tr c X t <;> cases c t <;> cases c (t + 1) <;> rfl

theorem kick_flip_lt (c : Nat → Bool) (X t s : Nat) (h : s < t) :
    kick c (2 ^ t + X) s = kick c X s := by
  unfold kick; rw [tr_flip_lt c X t s h]

/-- the kicks before time `H` depend only on the seed bits `< H`: adding `2^H` does not change
the validity of the prefix of length `H`. -/
theorem gvalid_flip (c : Nat → Bool) (X H : Nat) : GValid c (2 ^ H + X) H ↔ GValid c X H := by
  unfold GValid
  constructor
  · intro h t ht
    have := h t ht
    rw [kick_flip_lt c X H t ht] at this
    refine ⟨this.1, fun h1 h2 h3 => ?_, fun h1 h2 h3 => ?_⟩
    · have := this.2.1 h1 h2 h3; rwa [kick_flip_lt c X H _ h3] at this
    · have := this.2.2 h1 h2 h3; rwa [kick_flip_lt c X H _ h3] at this
  · intro h t ht
    have := h t ht
    rw [← kick_flip_lt c X H t ht] at this
    refine ⟨this.1, fun h1 h2 h3 => ?_, fun h1 h2 h3 => ?_⟩
    · have := this.2.1 h1 h2 h3; rwa [← kick_flip_lt c X H _ h3] at this
    · have := this.2.2 h1 h2 h3; rwa [← kick_flip_lt c X H _ h3] at this

/-! ### The pattern 01 and the one-tick extension of GValid -/

/-- the period-2 pattern `c_t = t mod 2`. -/
def p01 (t : Nat) : Bool := t % 2 == 1

theorem p01_odd {t : Nat} (h : t % 2 = 1) : p01 t = true := by simp [p01, h]
theorem p01_even {t : Nat} (h : t % 2 = 0) : p01 t = false := by simp [p01, h]

/-- the flag: was there a kick at the last even tick before `H`? -/
def kf (X : Nat) : Nat → Bool
  | 0 => false
  | H + 1 => if H % 2 = 0 then kick p01 X H else kf X H

theorem kf_even_succ (X m : Nat) : kf X (2 * m + 2) = kick p01 X (2 * m) := by
  simp only [kf]
  rw [ite_eq_right (by omega), ite_eq_left (by omega)]

/-- position `H` is forced (only the no-kick trace value is legal). -/
def forced (X H : Nat) : Prop := H % 2 = 1 ∨ kf X H = true

theorem gvalid_succ (X H : Nat) :
    GValid p01 X (H + 1) ↔ GValid p01 X H ∧ (forced X H → kick p01 X H = false) := by
  constructor
  · intro h
    refine ⟨fun t ht => ?_, fun hf => ?_⟩
    · obtain ⟨a, b, c⟩ := h t (by omega)
      exact ⟨a, fun h1 h2 h3 => b h1 h2 (by omega), fun h1 h2 h3 => c h1 h2 (by omega)⟩
    · rcases hf with hodd | hk
      · cases hk : kick p01 X H
        · rfl
        · have := (h H (by omega)).1 hk; rw [p01_odd hodd] at this; exact absurd this (by simp)
      · -- H even, H ≥ 2, kick at H - 2
        obtain ⟨m, hm | hm⟩ : ∃ m, H = 2 * m ∨ H = 2 * m + 1 := ⟨H / 2, by omega⟩
        · cases m with
          | zero => subst hm; simp [kf] at hk
          | succ m =>
            have e : H = 2 * m + 2 := by omega
            subst e
            rw [kf_even_succ] at hk
            have := (h (2 * m) (by omega)).2.2 hk (p01_odd (by omega)) (by omega)
            simpa using this
        · subst hm
          cases hk2 : kick p01 X (2 * m + 1)
          · rfl
          · have := (h (2 * m + 1) (by omega)).1 hk2
            rw [p01_odd (by omega)] at this; exact absurd this (by simp)
  · rintro ⟨h, hnew⟩ t ht
    have hodd_nokick : ∀ s, s < H + 1 → s % 2 = 1 → kick p01 X s = false := by
      intro s hs hso
      rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | hs
      · cases hk : kick p01 X s
        · rfl
        · have := (h s hs).1 hk; rw [p01_odd hso] at this; exact absurd this (by simp)
      · subst hs; exact hnew (Or.inl hso)
    refine ⟨fun hk => ?_, fun hk h2 h3 => ?_, fun hk h2 h3 => ?_⟩
    · rcases Nat.mod_two_eq_zero_or_one t with he | ho
      · exact p01_even he
      · rw [hodd_nokick t ht ho] at hk; exact absurd hk (by simp)
    · -- K2 is vacuous for 01: c (t+1) = false means t odd, but odd ticks never kick
      rcases Nat.mod_two_eq_zero_or_one t with he | ho
      · rw [p01_odd (by omega)] at h2; exact absurd h2 (by simp)
      · rw [hodd_nokick t ht ho] at hk; exact absurd hk (by simp)
    · rcases Nat.lt_or_ge (t + 2) H with hlt | hge
      · exact (h t (by omega)).2.2 hk h2 hlt
      · have e : t + 2 = H := by omega
        rcases Nat.mod_two_eq_zero_or_one t with he | ho
        · obtain ⟨m, hm⟩ : ∃ m, t = 2 * m := ⟨t / 2, by omega⟩
          subst hm
          subst e
          apply hnew
          right
          rw [kf_even_succ]; exact hk
        · rw [hodd_nokick t ht ho] at hk; exact absurd hk (by simp)

/-! ### The coin chain -/

/-- number of legal moves at tick `H` from flag `k` to flag `k'`. -/
def trans (H : Nat) (k k' : Bool) : Nat :=
  if H % 2 = 1 then (if k = k' then 1 else 0)
  else if k then (if k' then 0 else 1) else 1

/-- `coin n k0 ℓ k'`: number of legal kick words of length `ℓ` starting at tick `n` with flag `k0`
and ending with flag `k'` (the exact fair-coin chain, counted). -/
def coin (n : Nat) (k0 : Bool) : Nat → Bool → Nat
  | 0, k' => if k0 = k' then 1 else 0
  | ℓ + 1, k' =>
    coin n k0 ℓ false * trans (n + ℓ) false k' + coin n k0 ℓ true * trans (n + ℓ) true k'

theorem kf_flip (Z H : Nat) : kf (2 ^ H + Z) H = kf Z H := by
  have : ∀ m, m ≤ H → kf (2 ^ H + Z) m = kf Z m := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      simp only [kf]
      rw [kick_flip_lt p01 Z H m (by omega), ih (by omega)]
  exact this H (Nat.le_refl H)

theorem kf_succ_flip (Z H : Nat) : kf (2 ^ H + Z) (H + 1) =
    if H % 2 = 0 then !kick p01 Z H else kf Z H := by
  simp only [kf]
  split
  · exact kick_flip p01 Z H
  · exact kf_flip Z H

theorem kf_succ (Z H : Nat) : kf Z (H + 1) = if H % 2 = 0 then kick p01 Z H else kf Z H := rfl

/-- the pointwise one-tick identity: the two seeds `Z`, `2^H + Z` (they differ only in seed bit `H`
from below, i.e. in the trace value at tick `H`) together contribute exactly `trans`. -/
theorem pair_count (Z H : Nat) (k' : Bool) :
    (if GValid p01 Z (H + 1) ∧ kf Z (H + 1) = k' then 1 else 0) +
      (if GValid p01 (2 ^ H + Z) (H + 1) ∧ kf (2 ^ H + Z) (H + 1) = k' then 1 else 0) =
    if GValid p01 Z H then trans H (kf Z H) k' else 0 := by
  simp only [gvalid_succ, gvalid_flip, kf_succ, kick_flip, forced, kf_flip]
  by_cases hv : GValid p01 Z H
  · simp only [hv, true_and, ite_true]
    unfold trans
    rcases Nat.mod_two_eq_zero_or_one H with he | ho
    · simp only [he, show ¬ (0 = 1) from by omega, false_or, ite_true, ite_false]
      cases kf Z H <;> cases kick p01 Z H <;> cases k' <;> simp
    · simp only [ho, show ¬ (1 = 0) from by omega, true_or, ite_true, ite_false, forall_const]
      cases kf Z H <;> cases kick p01 Z H <;> cases k' <;> simp
  · simp [hv]

/-! ### The Mean Ladder Law -/

/-- number of fillings `y < 2^ℓ` of the next `ℓ` seed digits that keep `X0 + 2^n y` valid to
`n + ℓ`, refined by the final flag. -/
def fill (X0 n ℓ : Nat) (k' : Bool) : Nat :=
  countBelow (fun y => GValid p01 (X0 + 2 ^ n * y) (n + ℓ) ∧ kf (X0 + 2 ^ n * y) (n + ℓ) = k')
    (2 ^ ℓ)

theorem fill_eq (X0 n : Nat) : ∀ ℓ k', fill X0 n ℓ k' =
    if GValid p01 X0 n then coin n (kf X0 n) ℓ k' else 0 := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro k'
    simp only [fill, Nat.pow_zero, Nat.add_zero, coin, countBelow, Nat.mul_zero, Nat.zero_add]
    by_cases hv : GValid p01 X0 n <;> by_cases hk : kf X0 n = k' <;> simp [hv, hk]
  | succ ℓ ih =>
    intro k'
    have hsplit : fill X0 n (ℓ + 1) k' = sumBelow (fun y =>
        (if GValid p01 (X0 + 2 ^ n * y) (n + ℓ + 1) ∧ kf (X0 + 2 ^ n * y) (n + ℓ + 1) = k'
            then 1 else 0) +
         (if GValid p01 (2 ^ (n + ℓ) + (X0 + 2 ^ n * y)) (n + ℓ + 1) ∧
            kf (2 ^ (n + ℓ) + (X0 + 2 ^ n * y)) (n + ℓ + 1) = k' then 1 else 0)) (2 ^ ℓ) := by
      simp only [fill]
      rw [countBelow_eq_sumBelow, show 2 ^ (ℓ + 1) = 2 ^ ℓ + 2 ^ ℓ by rw [Nat.pow_succ]; omega,
        sumBelow_append, sumBelow_add_distrib]
      have e : ∀ y, X0 + 2 ^ n * (2 ^ ℓ + y) = 2 ^ (n + ℓ) + (X0 + 2 ^ n * y) := by
        intro y; rw [Nat.mul_add, Nat.pow_add]; omega
      simp only [e, show n + (ℓ + 1) = n + ℓ + 1 by omega]
    rw [hsplit]
    simp only [pair_count]
    have hpt : ∀ y, (if GValid p01 (X0 + 2 ^ n * y) (n + ℓ) then
          trans (n + ℓ) (kf (X0 + 2 ^ n * y) (n + ℓ)) k' else 0) =
        (if GValid p01 (X0 + 2 ^ n * y) (n + ℓ) ∧ kf (X0 + 2 ^ n * y) (n + ℓ) = false
          then 1 else 0) * trans (n + ℓ) false k' +
        (if GValid p01 (X0 + 2 ^ n * y) (n + ℓ) ∧ kf (X0 + 2 ^ n * y) (n + ℓ) = true
          then 1 else 0) * trans (n + ℓ) true k' := by
      intro y
      by_cases hv : GValid p01 (X0 + 2 ^ n * y) (n + ℓ)
      · cases hk : kf (X0 + 2 ^ n * y) (n + ℓ) <;> simp [hv]
      · simp [hv]
    have hcount : ∀ k : Bool, sumBelow (fun y =>
        if GValid p01 (X0 + 2 ^ n * y) (n + ℓ) ∧ kf (X0 + 2 ^ n * y) (n + ℓ) = k then 1 else 0)
        (2 ^ ℓ) = fill X0 n ℓ k := by
      intro k; simp only [fill]; rw [countBelow_eq_sumBelow]
    rw [sumBelow_congr _ (fun y _ => hpt y), sumBelow_add_distrib, sumBelow_mul_right,
      sumBelow_mul_right, hcount false, hcount true, ih false, ih true]
    by_cases hv : GValid p01 X0 n
    · simp only [hv, ite_true, coin]
    · simp [hv]

/-- **Mean Ladder Law.**  Over all `2^ℓ` fillings of the next `ℓ` seed digits, the number that keep
the beat to `n + ℓ` is exactly the coin count of legal kick words from the state at `n`. -/
theorem mean_ladder (X0 n ℓ : Nat) :
    countBelow (fun y => GValid p01 (X0 + 2 ^ n * y) (n + ℓ)) (2 ^ ℓ) =
      if GValid p01 X0 n then coin n (kf X0 n) ℓ false + coin n (kf X0 n) ℓ true else 0 := by
  have h : ∀ y, (if GValid p01 (X0 + 2 ^ n * y) (n + ℓ) then 1 else 0) =
      (if GValid p01 (X0 + 2 ^ n * y) (n + ℓ) ∧ kf (X0 + 2 ^ n * y) (n + ℓ) = false
        then 1 else 0) +
      (if GValid p01 (X0 + 2 ^ n * y) (n + ℓ) ∧ kf (X0 + 2 ^ n * y) (n + ℓ) = true
        then 1 else 0) := by
    intro y
    by_cases hv : GValid p01 (X0 + 2 ^ n * y) (n + ℓ)
    · cases hk : kf (X0 + 2 ^ n * y) (n + ℓ) <;> simp [hv]
    · simp [hv]
  rw [countBelow_eq_sumBelow, sumBelow_congr _ (fun y _ => h y), sumBelow_add_distrib]
  have e := fun k => fill_eq X0 n ℓ k
  simp only [fill, countBelow_eq_sumBelow] at e
  rw [e false, e true]
  split <;> rfl

/-! ### The global count: Fibonacci -/

theorem coin0 (m : Nat) :
    coin 0 false (2 * m) false = fib (m + 1) ∧ coin 0 false (2 * m) true = fib m ∧
    coin 0 false (2 * m + 1) false = fib (m + 2) ∧
      coin 0 false (2 * m + 1) true = fib (m + 1) := by
  induction m with
  | zero => simp [coin, trans, fib]
  | succ m ih =>
    obtain ⟨_, _, h3, h4⟩ := ih
    have a : coin 0 false (2 * (m + 1)) false = fib (m + 2) := by
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, coin, h3, h4]
      simp [trans]
    have b : coin 0 false (2 * (m + 1)) true = fib (m + 1) := by
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, coin, h3, h4]
      simp [trans]
    refine ⟨a, b, ?_, ?_⟩
    · rw [coin, a, b]
      simp [trans]
      have e1 : fib (m + 1 + 2) = fib (m + 1) + fib (m + 2) := rfl
      have e2 : fib (m + 1 + 1) = fib (m + 2) := rfl
      have e3 : fib (m + 3) = fib (m + 1 + 2) := rfl
      omega
    · rw [coin, a, b]
      simp [trans]

/-- **The exact count of valid seeds** (Exact Half-Coin Law, global form):
`#{X < 2^H : GValid 01 X H} = fib(⌈H/2⌉ + 2)`. -/
theorem card_valid (H : Nat) :
    countBelow (fun X => GValid p01 X H) (2 ^ H) = fib ((H + 1) / 2 + 2) := by
  have h := mean_ladder 0 0 H
  rw [countBelow_congr (q := fun X => GValid p01 X H) _
    (fun X _ => by rw [Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.zero_add])] at h
  rw [h]
  have hv : GValid p01 0 0 := fun t ht => absurd ht (by omega)
  simp only [hv, ite_true, kf]
  obtain ⟨m, hm | hm⟩ : ∃ m, H = 2 * m ∨ H = 2 * m + 1 := ⟨H / 2, by omega⟩
  · subst hm
    obtain ⟨a, b, _, _⟩ := coin0 m
    rw [a, b, show (2 * m + 1) / 2 + 2 = m + 2 by omega, fib_add_two]; omega
  · subst hm
    obtain ⟨_, _, a, b⟩ := coin0 m
    rw [a, b, show (2 * m + 1 + 1) / 2 + 2 = m + 3 by omega]
    have e1 : fib (m + 3) = fib (m + 1) + fib (m + 2) := rfl
    have e2 : fib (m + 1 + 1) = fib (m + 2) := rfl
    omega

/-! ### The ladder as an average over translates -/

/-- `S n ℓ`: the number of seeds of bitlength exactly `n` (`2^(n-1) ≤ X < 2^n`) valid to `n + ℓ`. -/
def S (n ℓ : Nat) : Nat :=
  countBelow (fun X => 2 ^ (n - 1) ≤ X ∧ GValid p01 X (n + ℓ)) (2 ^ n)

/-- the exact coin ladder: every seed of bitlength `n` alive at `n`, weighted by its exact coin
count of legal continuations of length `ℓ` (divide by `2^ℓ` for the coin prediction). -/
def Scoin (n ℓ : Nat) : Nat :=
  sumBelow (fun X => if 2 ^ (n - 1) ≤ X ∧ GValid p01 X n then
    coin n (kf X n) ℓ false + coin n (kf X n) ℓ true else 0) (2 ^ n)

/-- **Ladder = translate of the coin ladder.**  Summed over all `2^ℓ` blocks `y` of the next `ℓ`
seed digits, the survivor counts equal the exact coin ladder `Scoin n ℓ`; the true ladder `S n ℓ` is
the single term `y = 0`.  So `S n ℓ ≤ C · 2^(-ℓ) · Scoin n ℓ` (the coin-ladder conjecture) says
exactly that the zero block is at most `C` times the average block. -/
theorem ladder_average (n ℓ : Nat) :
    sumBelow (fun y =>
      countBelow (fun X => 2 ^ (n - 1) ≤ X ∧ GValid p01 (X + 2 ^ n * y) (n + ℓ)) (2 ^ n)) (2 ^ ℓ)
      = Scoin n ℓ := by
  simp only [countBelow_eq_sumBelow]
  rw [sumBelow_comm]
  unfold Scoin
  apply sumBelow_congr
  intro X _
  have h := mean_ladder X n ℓ
  rw [countBelow_eq_sumBelow] at h
  by_cases hX : 2 ^ (n - 1) ≤ X
  · simp only [hX, true_and]
    rw [h]
  · simp only [hX, false_and, ite_false]
    clear h
    induction 2 ^ ℓ with
    | zero => rfl
    | succ k ih => simp only [sumBelow, ih]

theorem S_eq_zero_block (n ℓ : Nat) :
    S n ℓ = countBelow (fun X => 2 ^ (n - 1) ≤ X ∧ GValid p01 (X + 2 ^ n * 0) (n + ℓ)) (2 ^ n) := by
  simp only [S, Nat.mul_zero, Nat.add_zero]

/-- the trivial consequence: the true ladder never exceeds the summed coin ladder. -/
theorem S_le_Scoin (n ℓ : Nat) : S n ℓ ≤ Scoin n ℓ := by
  rw [← ladder_average, S_eq_zero_block]
  exact le_sumBelow (fun y => countBelow (fun X => 2 ^ (n - 1) ≤ X ∧
    GValid p01 (X + 2 ^ n * y) (n + ℓ)) (2 ^ n)) (2 ^ ℓ) (Nat.two_pow_pos ℓ)

end Ladder

/-! ## Connection to the kit's zero-driven left half -/

section KitBridge

/-- The left start whose cell `-1 - i` is bit `i` of `Y` (cells `p ≥ 0` are irrelevant). -/
def startOf (Y : Nat) : Int → Bool := fun p => if p < 0 then Y.testBit (-1 - p).toNat else false

/-- **Bridge.** The model's zero-driven left half is the kit's
`Rule30DrivenLeft.L (fun _ => false)`: from the finite start `startOf X`, cell `p < 0` at time `t`
is bit `-1 - p` of `orb (fun _ => false) X t`. -/
theorem orb_zero_eq_L (X : Nat) : ∀ (t : Nat) (p : Int), p < 0 →
    Rule30DrivenLeft.L (fun _ => false) (startOf X) t p =
      (orb (fun _ => false) X t).testBit (-1 - p).toNat := by
  intro t
  induction t with
  | zero => intro p hp; simp [Rule30DrivenLeft.L_zero hp, startOf, hp, orb]
  | succ t ih =>
    intro p hp
    rw [Rule30DrivenLeft.L_succ hp, ih (p - 1) (by omega), orb_succ, testBit_L, ih p hp,
      show (-1 - (p - 1)).toNat = (-1 - p).toNat + 1 by omega]
    unfold Rule30Jen.rule
    by_cases hp1 : p = -1
    · subst hp1
      rw [show (-1 : Int) + 1 = 0 by omega, Rule30DrivenLeft.L_col0]
      simp [rn]
    · rw [ih (p + 1) (by omega)]
      obtain ⟨k, hk⟩ : ∃ k, (-1 - p).toNat = k + 1 := ⟨(-1 - p).toNat - 1, by omega⟩
      rw [hk, show (-1 - (p + 1)).toNat = k by omega]
      rfl

/-- If the center bit `b` is black only when bit `0` is black, the step is the zero-driven step. -/
theorem L_eq_L_false (b : Bool) (Y : Nat) (h : b = true → Y.testBit 0 = true) :
    L b Y = L false Y := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_L, testBit_L]
  cases i with
  | zero =>
    simp only [rn]
    cases b
    · rfl
    · rw [h rfl]; rfl
  | succ j => rfl

/-- A seed valid for ever beside the pattern `p01` evolves as the zero-driven left half: by K1 its
wall cell is black whenever the center is. -/
theorem orb_p01_eq_orb_zero (X : Nat) (hX : ∀ H, GValid p01 X H) :
    ∀ t, orb p01 X t = orb (fun _ => false) X t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [orb_succ, orb_succ, L_eq_L_false]
    · rw [ih]
    · intro hc
      have hk : kick p01 X t = false := by
        cases hk : kick p01 X t
        · rfl
        · have := (hX (t + 1) t (by omega)).1 hk
          rw [hc] at this; exact absurd this (by simp)
      have ho : t % 2 = 1 := by
        rcases Nat.mod_two_eq_zero_or_one t with h0 | h1
        · rw [p01_even h0] at hc; exact absurd hc (by decide)
        · exact h1
      have hc1 : p01 (t + 1) = false := p01_even (by omega)
      unfold kick tr at hk
      rw [hc, hc1] at hk
      cases hb : (orb p01 X t).testBit 0
      · rw [hb] at hk; exact absurd hk (by decide)
      · rfl

theorem orb_zero_shift (X : Nat) :
    ∀ t, orb (fun _ => false) (L false X) t = orb (fun _ => false) X (t + 1) := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih => rw [orb_succ, ih]; rfl

/-- **The kit's `Q01` implies `NoSeed p01`.** A seed valid for ever beside `p01` is, one step later,
a finite start of the kit's zero-driven left half whose column `-1` is black at every even step. -/
theorem noSeed01_of_Q01 (hQ : Rule30PeriodTwo.Q01) : NoSeed p01 := by
  intro X _ hX
  have hz := orb_p01_eq_orb_zero X hX
  have hodd : ∀ k, (orb (fun _ => false) X (2 * k + 1)).testBit 0 = true := by
    intro k
    have hc : p01 (2 * k + 1) = true := p01_odd (by omega)
    have hk : kick p01 X (2 * k + 1) = false := by
      cases hk : kick p01 X (2 * k + 1)
      · rfl
      · have := (hX (2 * k + 2) (2 * k + 1) (by omega)).1 hk
        rw [hc] at this; exact absurd this (by simp)
    have hc1 : p01 (2 * k + 1 + 1) = false := p01_even (by omega)
    unfold kick tr at hk
    rw [hc, hc1, hz] at hk
    cases hb : (orb (fun _ => false) X (2 * k + 1)).testBit 0
    · rw [hb] at hk; exact absurd hk (by decide)
    · rfl
  have hY : L false X ≠ 0 := by
    intro h0
    have := hodd 0
    rw [show orb (fun _ => false) X (2 * 0 + 1) = L false X from rfl, h0, Nat.zero_testBit] at this
    exact absurd this (by decide)
  refine hQ (Nat.log2 (L false X) + 1) (startOf (L false X)) (by omega) (fun p hp => ?_) ?_
    (fun k => ?_)
  · have hp0 : p < 0 := by omega
    simp only [startOf, hp0, ite_true]
    apply Nat.testBit_lt_two_pow
    exact Nat.lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by decide) (by omega))
  · have hn : -((Nat.log2 (L false X) + 1 : Nat) : Int) < 0 := by omega
    simp only [startOf, hn, ite_true]
    rw [show (-1 - -((Nat.log2 (L false X) + 1 : Nat) : Int)).toNat = Nat.log2 (L false X) by omega]
    exact Nat.testBit_log2 hY
  · rw [orb_zero_eq_L (L false X) (2 * k) (-1) (by omega), orb_zero_shift]
    simpa using hodd k

/-- **`NoSeed p01` excludes period 2.** Beside an alternating center from `T` (kit's `normalize`),
the official center from `T + 1` on is `p01`, and the official left half-row there is a nonzero
seed valid for ever (`gvalid_rowNat`, `rowNat_ne_zero`). -/
theorem not_eventually_period_two_of_noSeed01 (h : NoSeed p01) :
    ¬ ∃ T0, ∀ t, T0 ≤ t → Rule30Prize.center (t + 2) = Rule30Prize.center t := by
  rintro ⟨T0, hp⟩
  obtain ⟨T, hT⟩ := Rule30PeriodTwo.normalize hp
  apply not_center_eventually_of_noSeed p01 h
  refine ⟨T + 1, by omega, fun s => ?_⟩
  obtain ⟨j, rfl | rfl⟩ : ∃ j, s = 2 * j ∨ s = 2 * j + 1 := ⟨s / 2, by omega⟩
  · rw [show T + 1 + 2 * j = T + 2 * j + 1 by omega]
    unfold Rule30Prize.center
    rw [(hT j).2]; simp [p01]
  · rw [show T + 1 + (2 * j + 1) = T + 2 * (j + 1) by omega]
    unfold Rule30Prize.center
    rw [(hT (j + 1)).1]; simp [p01]

end KitBridge

/-! ## Ladder bounds and `NoSeed p01` -/

section LadderBound
open Rule30RecordCharge

/-- `V n`: the seeds of bitlength exactly `n` valid to `n`. -/
def V (n : Nat) : Nat := S n 0

theorem gvalid_mono (c : Nat → Bool) (X : Nat) {H H' : Nat} (hle : H' ≤ H) (h : GValid c X H) :
    GValid c X H' := by
  intro t ht
  obtain ⟨a, b, d⟩ := h t (by omega)
  exact ⟨a, fun h1 h2 h3 => b h1 h2 (by omega), fun h1 h2 h3 => d h1 h2 (by omega)⟩

/-- finitely many seeds that each die eventually all die by one common time. -/
theorem common_death (P : Nat → Prop) (n : Nat) :
    ∀ N, (∀ X, X < N → P X → ∃ H, ¬ GValid p01 X H) →
      ∃ l, ∀ X, X < N → P X → ¬ GValid p01 X (n + l)
  | 0, _ => ⟨0, fun _ hX => absurd hX (Nat.not_lt_zero _)⟩
  | N + 1, h => by
    obtain ⟨l, hl⟩ := common_death P n N (fun X hX hP => h X (by omega) hP)
    by_cases hP : P N
    · obtain ⟨H, hH⟩ := h N (by omega) hP
      refine ⟨l + H, fun X hX hPX hv => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hX with hX | hX
      · exact hl X hX hPX (gvalid_mono p01 X (by omega) hv)
      · subst hX; exact hH (gvalid_mono p01 _ (by omega) hv)
    · refine ⟨l, fun X hX hPX => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hX with hX | hX
      · exact hl X hX hPX
      · subst hX; exact absurd hPX hP

/-- **`NoSeed p01` is the qualitative ladder statement**: it holds if and only if, for every
bitlength `n ≥ 1`, the ladder `S n l` reaches `0`. -/
theorem noSeed_iff_S_eventually_zero :
    NoSeed p01 ↔ ∀ n, 1 ≤ n → ∃ l, S n l = 0 := by
  constructor
  · intro h n _
    obtain ⟨l, hl⟩ := common_death (fun X => 2 ^ (n - 1) ≤ X) n (2 ^ n) (fun X _ hX => by
      have hX0 : X ≠ 0 := by have : 0 < 2 ^ (n - 1) := Nat.two_pow_pos _; omega
      exact Classical.not_forall.mp (h X hX0))
    exact ⟨l, (countBelow_eq_zero _ _).2 (fun X hX hv => hl X hX hv.1 hv.2)⟩
  · intro h X hX hall
    obtain ⟨l, hl⟩ := h (Nat.log2 X + 1) (by omega)
    unfold S at hl
    rw [countBelow_eq_zero] at hl
    exact hl X Nat.lt_log2_self ⟨by rw [Nat.add_sub_cancel]; exact Nat.log2_self_le hX, hall _⟩

/-- **The half ladder bound** (open): `S n (2 j) * 2^j ≤ C * V n` for all `n`, `j` implies
`NoSeed p01`. -/
theorem noSeed_of_half_ladder_bound (C : Nat) (h : ∀ n j, S n (2 * j) * 2 ^ j ≤ C * V n) :
    NoSeed p01 := by
  rw [noSeed_iff_S_eventually_zero]
  intro n _
  refine ⟨2 * (C * V n), ?_⟩
  have h1 := h n (C * V n)
  have h2 : C * V n < 2 ^ (C * V n) := Nat.lt_two_pow_self
  apply Classical.byContradiction
  intro hne
  have : 1 ≤ S n (2 * (C * V n)) := Nat.one_le_iff_ne_zero.mpr hne
  have : 2 ^ (C * V n) ≤ S n (2 * (C * V n)) * 2 ^ (C * V n) := by
    calc 2 ^ (C * V n) = 1 * 2 ^ (C * V n) := (Nat.one_mul _).symm
      _ ≤ _ := Nat.mul_le_mul_right _ this
  omega

/-- Bernoulli's inequality in the form `θ^j (1 + j (1 - θ)) ≤ 1` for `0 ≤ θ ≤ 1`. -/
theorem rat_pow_mul_bernoulli_le (θ : Rat) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∀ j : Nat, θ ^ j * (1 + (j : Rat) * (1 - θ)) ≤ 1 := by
  intro j
  induction j with
  | zero =>
    show θ ^ 0 * (1 + ((0 : Nat) : Rat) * (1 - θ)) ≤ 1
    rw [Rat.pow_zero]; grind
  | succ j ih =>
    have hp : 0 ≤ θ ^ j := Rat.pow_nonneg hθ0
    have hj : (0 : Rat) ≤ (j : Rat) + 1 := by
      have := Rat.natCast_nonneg (a := j); grind
    have h1 : (0 : Rat) ≤ 1 - θ := by grind
    have hq : 0 ≤ θ ^ j * (((j : Rat) + 1) * ((1 - θ) * (1 - θ))) :=
      Rat.mul_nonneg hp (Rat.mul_nonneg hj (Rat.mul_nonneg h1 h1))
    rw [Rat.pow_succ, show ((j + 1 : Nat) : Rat) = (j : Rat) + 1 by grind]
    grind

/-- **A geometric ladder bound with any rate `θ < 1`** (open) implies `NoSeed p01`:
`S n (2 j) ≤ C * V n * θ^j` for all `n`, `j`, with rational `C` and `θ`. -/
theorem noSeed_of_geometric_ladder_bound (C θ : Rat) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (h : ∀ n j, (S n (2 * j) : Rat) ≤ C * V n * θ ^ j) : NoSeed p01 := by
  rw [noSeed_iff_S_eventually_zero]
  intro n _
  -- a time `j` with `C * V n * θ^j < 1`
  have hlt : ∃ j : Nat, C * V n * θ ^ j < 1 := by
    have hV : (0 : Rat) ≤ (V n : Rat) := Rat.natCast_nonneg
    by_cases hC : C ≤ 0
    · refine ⟨0, ?_⟩
      have : C * (V n : Rat) ≤ 0 := by
        have := Rat.mul_le_mul_of_nonneg_right hC hV; grind
      grind
    · have hε : (0 : Rat) < 1 - θ := by grind
      -- an integer time beyond `C * V n / (1 - θ)`
      have hex : ∃ j : Nat, C * (V n : Rat) / (1 - θ) < (j : Rat) := by
        refine ⟨(Rat.floor (C * (V n : Rat) / (1 - θ)) + 1).toNat, ?_⟩
        have h1 := Rat.lt_floor_add_one (C * (V n : Rat) / (1 - θ))
        have h2 : (Rat.floor (C * (V n : Rat) / (1 - θ)) + 1 : Int) ≤
            (((Rat.floor (C * (V n : Rat) / (1 - θ)) + 1).toNat : Nat) : Int) := Int.self_le_toNat _
        have h3 := Rat.intCast_le_intCast.mpr h2
        rw [Rat.intCast_natCast] at h3
        grind
      obtain ⟨j, hM⟩ := hex
      refine ⟨j, ?_⟩
      have hCV : C * (V n : Rat) < (j : Rat) * (1 - θ) := by
        have := Rat.mul_lt_mul_of_pos_right hM hε
        rwa [Rat.div_mul_cancel (Rat.ne_of_lt hε).symm] at this
      have hB := rat_pow_mul_bernoulli_le θ hθ0 (Rat.le_of_lt hθ1) j
      have hp : 0 ≤ θ ^ j := Rat.pow_nonneg hθ0
      rcases Rat.le_iff_lt_or_eq.mp hp with hpos | hzero
      · have := Rat.mul_lt_mul_of_pos_right hCV hpos
        grind
      · rw [← hzero]; grind
  obtain ⟨j, hj⟩ := hlt
  refine ⟨2 * j, ?_⟩
  have h4 : (S n (2 * j) : Rat) < 1 := by have := h n j; grind
  have : S n (2 * j) < 1 := Rat.natCast_lt_natCast.mp (by simpa using h4)
  omega

/-- **The ladder bound excludes period 2**: if `S n (2 j) * 2^j ≤ C * V n` for all `n`, `j`, the
official center column is not eventually 2-periodic. -/
theorem not_eventually_period_two_of_ladder_bound (C : Nat)
    (h : ∀ n j, S n (2 * j) * 2 ^ j ≤ C * V n) :
    ¬ ∃ T0, ∀ t, T0 ≤ t → Rule30Prize.center (t + 2) = Rule30Prize.center t :=
  not_eventually_period_two_of_noSeed01 (noSeed_of_half_ladder_bound C h)

/-- The same with any rational geometric rate `θ < 1`. -/
theorem not_eventually_period_two_of_geometric_ladder_bound (C θ : Rat) (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) (h : ∀ n j, (S n (2 * j) : Rat) ≤ C * V n * θ ^ j) :
    ¬ ∃ T0, ∀ t, T0 ≤ t → Rule30Prize.center (t + 2) = Rule30Prize.center t :=
  not_eventually_period_two_of_noSeed01 (noSeed_of_geometric_ladder_bound C θ hθ0 hθ1 h)

end LadderBound

/-! ## Two-step matrix commutation (`I_2 * F_2 = F_2 * I_2 = F_2`), all-phase Fibonacci coin counts, and the coin-ladder reduction -/

section CoinMatrix
open Rule30RecordCharge

/-- **Two-Tick Transfer Matrix Commutation (`trans_two_step_comm`):**
because `trans` at odd ticks is the `2 × 2` identity matrix `I_2` and at even ticks is the
Fibonacci matrix `F_2 = ((1, 1), (1, 0))`, the 2-step matrix product across any two consecutive
ticks `(H, H + 1)` equals `F_2 = trans 0`, regardless of the parity of `H`. -/
theorem trans_two_step_comm (H : Nat) (k0 k' : Bool) :
    trans H k0 false * trans (H + 1) false k' + trans H k0 true * trans (H + 1) true k' =
      trans 0 k0 k' := by
  rcases Nat.mod_two_eq_zero_or_one H with he | ho
  · have ho1 : (H + 1) % 2 = 1 := by omega
    cases k0 <;> cases k' <;> simp [trans, he, ho1]
  · have he1 : (H + 1) % 2 = 0 := by omega
    cases k0 <;> cases k' <;> simp [trans, ho, he1]

/-- **Two-Step Recurrence for `coin` (`coin_add_two`):**
advancing `coin n k0` by `2` ticks from `ℓ` to `ℓ + 2` applies the parity-independent Fibonacci
transfer matrix `trans 0`. -/
theorem coin_add_two (n : Nat) (k0 : Bool) (ℓ : Nat) (k' : Bool) :
    coin n k0 (ℓ + 2) k' =
      coin n k0 ℓ false * trans 0 false k' + coin n k0 ℓ true * trans 0 true k' := by
  rw [show ℓ + 2 = (ℓ + 1) + 1 by omega]
  simp only [coin]
  have h0 := trans_two_step_comm (n + ℓ) false k'
  have h1 := trans_two_step_comm (n + ℓ) true k'
  rw [show n + (ℓ + 1) = n + ℓ + 1 by omega, ← h0, ← h1]
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc]
  omega

/-- **Universal Starting-Tick Invariance of Even-Length Coin Counts (`coin_two_mul_eq_coin_zero`):**
for every starting tick `n : Nat`, initial flag `k0 : Bool`, half-length `j : Nat`, and final flag
`k' : Bool`, `coin n k0 (2 * j) k' = coin 0 k0 (2 * j) k'`. -/
theorem coin_two_mul_eq_coin_zero (n : Nat) (k0 : Bool) :
    ∀ (j : Nat) (k' : Bool), coin n k0 (2 * j) k' = coin 0 k0 (2 * j) k'
  | 0, k' => rfl
  | j + 1, k' => by
    rw [show 2 * (j + 1) = 2 * j + 2 by omega,
        coin_add_two n k0 (2 * j) k',
        coin_add_two 0 k0 (2 * j) k',
        coin_two_mul_eq_coin_zero n k0 j false,
        coin_two_mul_eq_coin_zero n k0 j true]

/-- **Exact Fibonacci Evaluation of `coin n true (2 * j)` (`coin_true_two_mul`):**
starting from flag `k0 = true` at any tick `n`, for every `j : Nat`,
`coin n true (2 * (j + 1)) false = fib (j + 1)` and `coin n true (2 * (j + 1)) true = fib j`. -/
theorem coin_true_two_mul (n : Nat) :
    ∀ j : Nat,
      coin n true (2 * (j + 1)) false = fib (j + 1) ∧
      coin n true (2 * (j + 1)) true = fib j
  | 0 => by
    rw [coin_two_mul_eq_coin_zero n true 1 false, coin_two_mul_eq_coin_zero n true 1 true]
    decide
  | j + 1 => by
    rcases coin_true_two_mul n j with ⟨hf, ht⟩
    have hstep_f := coin_add_two n true (2 * (j + 1)) false
    have hstep_t := coin_add_two n true (2 * (j + 1)) true
    rw [show 2 * (j + 1) + 2 = 2 * (j + 1 + 1) by omega] at hstep_f hstep_t
    rw [hstep_f, hstep_t, hf, ht]
    change (fib (j + 1) * 1 + fib j * 1 = fib (j + 2)) ∧ (fib (j + 1) * 1 + fib j * 0 = fib (j + 1))
    rw [fib_add_two j]
    omega

/-- **Exact Fibonacci Row Sums of `coin n k0 (2 * j)` (`coin_two_mul_sum_false`, `coin_two_mul_sum_true`):**
for every starting tick `n : Nat` and `j : Nat`, the row sum from `k0 = false` is `fib (j + 2)` and
from `k0 = true` is `fib (j + 1)`. -/
theorem coin_two_mul_sum_false (n j : Nat) :
    coin n false (2 * j) false + coin n false (2 * j) true = fib (j + 2) := by
  rw [coin_two_mul_eq_coin_zero n false j false,
      coin_two_mul_eq_coin_zero n false j true,
      (coin0 j).1, (coin0 j).2.1, fib_add_two j]
  omega

theorem coin_two_mul_sum_true (n : Nat) :
    ∀ j : Nat, coin n true (2 * j) false + coin n true (2 * j) true = fib (j + 1)
  | 0 => rfl
  | j + 1 => by
    rcases coin_true_two_mul n j with ⟨hf, ht⟩
    rw [hf, ht]
    change fib (j + 1) + fib j = fib (j + 2)
    rw [fib_add_two j]
    omega

theorem fib_mono_succ : ∀ k : Nat, fib k ≤ fib (k + 1)
  | 0 => by decide
  | 1 => by decide
  | k + 2 => Nat.le_add_left (fib (k + 2)) (fib (k + 1))

/-- **Universal Fibonacci Sandwich for All-Phase Even-Length Coin Sums (`coin_two_mul_sum_bounds`):**
for every `n : Nat`, `k0 : Bool`, and `j : Nat`,
`fib (j + 1) ≤ coin n k0 (2 * j) false + coin n k0 (2 * j) true ≤ fib (j + 2)`. -/
theorem coin_two_mul_sum_bounds (n : Nat) (k0 : Bool) (j : Nat) :
    fib (j + 1) ≤ coin n k0 (2 * j) false + coin n k0 (2 * j) true ∧
      coin n k0 (2 * j) false + coin n k0 (2 * j) true ≤ fib (j + 2) := by
  cases k0
  · rw [coin_two_mul_sum_false]
    exact ⟨fib_mono_succ (j + 1), Nat.le_refl _⟩
  · rw [coin_two_mul_sum_true]
    exact ⟨Nat.le_refl _, fib_mono_succ (j + 1)⟩

/-- **Exact Fibonacci-to-Power-of-Two Upper Bound (`fib_add_two_le_two_pow`):**
for every `j : Nat`, `fib (j + 2) ≤ 2 ^ j`. -/
theorem fib_add_two_le_two_pow : ∀ j : Nat, fib (j + 2) ≤ 2 ^ j
  | 0 => by decide
  | 1 => by decide
  | j + 2 => by
    have ih0 := fib_add_two_le_two_pow j
    have ih1 := fib_add_two_le_two_pow (j + 1)
    have hpow : 2 ^ j ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    change fib ((j + 2) + 2) ≤ 2 ^ ((j + 1) + 1)
    rw [fib_add_two (j + 2), Nat.pow_succ]
    change fib (j + 2) + fib ((j + 1) + 2) ≤ 2 ^ (j + 1) * 2
    omega

theorem sumBelow_le_sumBelow {f g : Nat → Nat} :
    ∀ N : Nat, (∀ k < N, f k ≤ g k) → sumBelow f N ≤ sumBelow g N
  | 0, _ => Nat.le_refl 0
  | N + 1, h => by
    simp only [sumBelow]
    have ih := sumBelow_le_sumBelow N (fun k hk => h k (by omega))
    have hN := h N (by omega)
    omega

theorem V_eq_sumBelow (n : Nat) :
    V n = sumBelow (fun X => if 2 ^ (n - 1) ≤ X ∧ GValid p01 X n then 1 else 0) (2 ^ n) := by
  unfold V S
  rw [Nat.add_zero, countBelow_eq_sumBelow]

/-- **Exact Fibonacci Sandwich on the Coin Ladder `Scoin n (2 * j)` (`Scoin_two_mul_bounds`):**
for every bitlength `n : Nat` and half-horizon `j : Nat`,
`V n * fib (j + 1) ≤ Scoin n (2 * j) ∧ Scoin n (2 * j) ≤ V n * fib (j + 2)`. -/
theorem Scoin_two_mul_bounds (n j : Nat) :
    V n * fib (j + 1) ≤ Scoin n (2 * j) ∧ Scoin n (2 * j) ≤ V n * fib (j + 2) := by
  unfold Scoin
  rw [V_eq_sumBelow n, ← sumBelow_mul_right, ← sumBelow_mul_right]
  refine ⟨sumBelow_le_sumBelow (2 ^ n) (fun X _ => ?_),
          sumBelow_le_sumBelow (2 ^ n) (fun X _ => ?_)⟩
  · by_cases hv : 2 ^ (n - 1) ≤ X ∧ GValid p01 X n
    · simp only [hv, and_self, ite_true, Nat.one_mul]
      exact (coin_two_mul_sum_bounds n (kf X n) j).1
    · simp only [hv, ite_false, Nat.zero_mul, Nat.le_refl]
  · by_cases hv : 2 ^ (n - 1) ≤ X ∧ GValid p01 X n
    · simp only [hv, and_self, ite_true, Nat.one_mul]
      exact (coin_two_mul_sum_bounds n (kf X n) j).2
    · simp only [hv, ite_false, Nat.zero_mul, Nat.le_refl]

/-- **Unconditional `V n * 2 ^ j` Upper Bound on the Coin Ladder (`Scoin_two_mul_le_V_mul_two_pow`):**
for every `n, j : Nat`, `Scoin n (2 * j) ≤ V n * 2 ^ j`. -/
theorem Scoin_two_mul_le_V_mul_two_pow (n j : Nat) :
    Scoin n (2 * j) ≤ V n * 2 ^ j :=
  Nat.le_trans (Scoin_two_mul_bounds n j).2 (Nat.mul_le_mul_left (V n) (fib_add_two_le_two_pow j))

/-- **The Coin-Ladder Bound Implies `NoSeed p01` (`noSeed_of_coin_ladder_bound`):**
if the zero block `S n (2 * j)` is at most `C` times the average block `Scoin n (2 * j) / 2 ^ (2 * j)`
(`∀ n j, S n (2 * j) * 2 ^ (2 * j) ≤ C * Scoin n (2 * j)`), then `NoSeed p01` holds. -/
theorem noSeed_of_coin_ladder_bound (C : Nat)
    (h : ∀ n j, S n (2 * j) * 2 ^ (2 * j) ≤ C * Scoin n (2 * j)) :
    NoSeed p01 := by
  apply noSeed_of_half_ladder_bound C
  intro n j
  have h1 := h n j
  have h2 : C * Scoin n (2 * j) ≤ C * (V n * 2 ^ j) :=
    Nat.mul_le_mul_left C (Scoin_two_mul_le_V_mul_two_pow n j)
  have h3 : S n (2 * j) * 2 ^ j * 2 ^ j ≤ C * V n * 2 ^ j := by
    calc S n (2 * j) * 2 ^ j * 2 ^ j
      _ = S n (2 * j) * (2 ^ j * 2 ^ j) := Nat.mul_assoc _ _ _
      _ = S n (2 * j) * 2 ^ (2 * j) := by rw [← Nat.pow_add, show j + j = 2 * j by omega]
      _ ≤ C * Scoin n (2 * j) := h1
      _ ≤ C * (V n * 2 ^ j) := h2
      _ = C * V n * 2 ^ j := (Nat.mul_assoc C (V n) (2 ^ j)).symm
  exact Nat.le_of_mul_le_mul_right h3 (Nat.two_pow_pos j)

/-- **The Coin-Ladder Bound Excludes Eventual Period 2 (`not_eventually_period_two_of_coin_ladder_bound`):**
if `S n (2 * j) * 2 ^ (2 * j) ≤ C * Scoin n (2 * j)` for all `n, j : Nat`, the official center column
is not eventually 2-periodic. -/
theorem not_eventually_period_two_of_coin_ladder_bound (C : Nat)
    (h : ∀ n j, S n (2 * j) * 2 ^ (2 * j) ≤ C * Scoin n (2 * j)) :
    ¬ ∃ T0, ∀ t, T0 ≤ t → Rule30Prize.center (t + 2) = Rule30Prize.center t :=
  not_eventually_period_two_of_noSeed01 (noSeed_of_coin_ladder_bound C h)

end CoinMatrix

end Rule30PeriodTwoLadder
end Ruliology.CellularAutomata
