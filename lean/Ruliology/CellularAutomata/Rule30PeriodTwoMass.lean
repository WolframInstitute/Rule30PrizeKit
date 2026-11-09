module

public import Ruliology.CellularAutomata.Rule30ZeroBoundary
public import Ruliology.CellularAutomata.Rule30Certificates.PeriodTwoMass

@[expose] public section

/-!
# Rule 30: a sharp mass conjecture for period 2, its certificate, and the tail law

If the center column of rule 30 were eventually `1, 0, 1, 0, …`, the left half-row at a late white
time would be a finite natural number `X` (bit `i` = cell `-1-i`) evolving by the kit's zero-wall
map `IntegerForm.F Y = (Y >>> 1) ^^^ (Y ||| (Y <<< 1))`, and its wall trace `tr X t` (bit `0` of
`F^t X`) would lie in the language **G** at every length: `tr X 0` white, every odd time black,
no two consecutive even times white (the kit's `m1_even` and `golden`).

**Part 1 (the chain).** `not_eventually_period_two_of_massbound`: any linear bound
`Z ≤ c·A + d` on the finite G words (`Z` the number of white even times, `A` the seed weight)
excludes an eventual period 2 of the official center column. `not_eventually_period_two_of_floor`:
the same from any positive linear floor `H ≤ q·A + d`.

**Part 2 (Conjecture S).** `ConjS`: every G word of length `H ≥ 2` has seed weight
`7·A ≥ H + 4`; `ConjSEven` is the form `7·A ≥ H + 5` at even `H`, which implies it
(`ConjS_of_even`). Both are **open**. `not_eventually_period_two_of_S`: S excludes period 2.
`S_upto_90`: S holds for every `H ≤ 90`, by a kernel-checked exhaustive search: the kernel
evaluates the search `fdfs` of `Rule30Certificates.PeriodTwoMass` (`fcert90`), `fdfs_dfs` turns it
into the plain search `dfs` (`cert90`), and `dfs_sound` reads off the bound. `sharp_86`,
`sharp_198`, `sharp_310`: the constant is attained.
Exhaustive computation beyond `H = 90` (to `H = 300`) supports S but is not checked here.

**Part 3 (the tail law).** The preimage transducer of the zero-wall map has 4 states; the
composites along nonempty words lie in an explicit list of 40 maps (`comp_mem`), all of whose cycles have
length 1, 2 or 3 (`cyc_div6`, `no_four_cycle`); two preimage runs of one word that never share
a state carry at least `2n` ones on every `3n` consecutive positions (`mass_two_thirds`).
-/

namespace Ruliology.CellularAutomata
namespace Rule30PeriodTwoMass
open Rule30Jen Rule30Prize Rule30PeriodTwo
open Rule30ZeroBoundary.IntegerForm (F iter testBit_F_zero testBit_F_succ)

/-! ## Part 1. Definitions and the chain -/

/-- The wall trace: bit `0` of `F^t Y`. -/
def tr (Y t : Nat) : Bool := (iter F t Y).testBit 0

/-- `cnt f n`: the number of `i < n` with `f i`. -/
def cnt (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => cnt f n + (if f n then 1 else 0)

/-- Seed weight: the number of ones of `Y` below `H`. -/
def wt (H Y : Nat) : Nat := cnt Y.testBit H

/-- The G rule at time `t`: white at `0`, black at odd times, no two consecutive white even
times. -/
def gstep (b : Nat → Bool) (t : Nat) : Bool :=
  if t = 0 then !b 0 else if t % 2 = 1 then b t else (b (t - 2) || b t)

/-- `b` is a G word of length `H`. -/
def GWord (b : Nat → Bool) (H : Nat) : Prop := ∀ t, t < H → gstep b t = true

/-- The number of white even times below `H`. -/
def zc (b : Nat → Bool) (H : Nat) : Nat := cnt (fun t => t % 2 == 0 && !b t) H

/-- A linear mass bound on the finite G words of even length. -/
def MassBound (c d : Nat) : Prop :=
  ∀ m Y : Nat, Y < 2 ^ (2 * m) → GWord (tr Y) (2 * m) → zc (tr Y) (2 * m) ≤ c * wt (2 * m) Y + d

/-- A positive linear floor on the seed weight of the finite G words. -/
def MassFloor (q d : Nat) : Prop :=
  ∀ H Y : Nat, Y < 2 ^ H → GWord (tr Y) H → H ≤ q * wt H Y + d

/-- **Conjecture S** (open): every G word of length `H ≥ 2` has seed weight at least
`(H + 4) / 7`. -/
def ConjS : Prop :=
  ∀ H Y : Nat, 2 ≤ H → Y < 2 ^ H → GWord (tr Y) H → H + 4 ≤ 7 * wt H Y

/-- **Conjecture S, even form** (open): at even length `H = 2m ≥ 2` the weight is at least
`(H + 5) / 7`. Equality at `H = 2, 86, 198`. -/
def ConjSEven : Prop :=
  ∀ m Y : Nat, 1 ≤ m → Y < 2 ^ (2 * m) → GWord (tr Y) (2 * m) → 2 * m + 5 ≤ 7 * wt (2 * m) Y

theorem cnt_le (f : Nat → Bool) : ∀ n, cnt f n ≤ n
  | 0 => Nat.le_refl 0
  | n + 1 => by have := cnt_le f n; simp only [cnt]; split <;> omega

theorem cnt_mono (f : Nat → Bool) {n m : Nat} (h : n ≤ m) : cnt f n ≤ cnt f m := by
  induction m with
  | zero => have : n = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ m ih =>
    rcases Nat.eq_or_lt_of_le h with e | lt
    · rw [e]; exact Nat.le_refl _
    · have := ih (by omega); simp only [cnt]; split <;> omega

theorem cnt_congr {f g : Nat → Bool} {N : Nat} (h : ∀ i, i < N → f i = g i) :
    ∀ n, n ≤ N → cnt f n = cnt g n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih => intro hn; simp only [cnt]; rw [ih (by omega), h n (by omega)]

theorem cnt_stable (f : Nat → Bool) {N : Nat} (h : ∀ i, N ≤ i → f i = false) :
    ∀ m, N ≤ m → cnt f m = cnt f N := by
  intro m
  induction m with
  | zero => intro hm; have : N = 0 := by omega
            subst this; rfl
  | succ m ih =>
    intro hm
    rcases Nat.eq_or_lt_of_le hm with e | lt
    · rw [e]
    · simp only [cnt]; rw [ih (by omega), h m (by omega)]; rfl

theorem eventually_false_of_cnt_bdd (f : Nat → Bool) (B : Nat) (h : ∀ n, cnt f n ≤ B) :
    ∃ T, ∀ t, T ≤ t → f t = false := by
  refine Classical.byContradiction fun hno => ?_
  have hno' : ∀ T, ∃ t, T ≤ t ∧ f t = true := by
    intro T
    refine Classical.byContradiction fun h2 => ?_
    apply hno
    refine ⟨T, fun t ht => ?_⟩
    cases hf : f t
    · rfl
    · exact absurd ⟨t, ht, hf⟩ h2
  have grow : ∀ k, ∃ n, k ≤ cnt f n := by
    intro k
    induction k with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ k ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨t, ht, hft⟩ := hno' n
      refine ⟨t + 1, ?_⟩
      simp only [cnt, hft, ite_true]
      have := cnt_mono f ht
      omega
  obtain ⟨n, hn⟩ := grow (B + 1)
  have := h n
  omega

/-! ### Causality of the zero-wall map -/

theorem testBit_F (Y i : Nat) :
    (F Y).testBit i =
      xor (Y.testBit (i + 1)) (Y.testBit i || (decide (1 ≤ i) && Y.testBit (i - 1))) := by
  cases i with
  | zero => rw [testBit_F_zero]; simp
  | succ j => rw [testBit_F_succ]; simp

theorem F_agree {Y Y' N : Nat} (h : ∀ i, i < N → Y.testBit i = Y'.testBit i) :
    ∀ i, i + 1 < N → (F Y).testBit i = (F Y').testBit i := by
  intro i hi
  rw [testBit_F, testBit_F, h (i + 1) hi, h i (by omega)]
  by_cases h1 : 1 ≤ i
  · rw [h (i - 1) (by omega)]
  · simp [h1]

theorem iter_succ (Y t : Nat) : iter F (t + 1) Y = F (iter F t Y) := rfl

theorem iter_agree {Y Y' : Nat} : ∀ t N, (∀ i, i < N → Y.testBit i = Y'.testBit i) →
    ∀ i, i + t < N → (iter F t Y).testBit i = (iter F t Y').testBit i := by
  intro t
  induction t with
  | zero => intro N h i hi; exact h i (by omega)
  | succ t ih =>
    intro N h i hi
    rw [iter_succ, iter_succ]
    have := ih N h
    exact F_agree (N := N - t) (fun j hj => this j (by omega)) i (by omega)

/-- The trace through time `H - 1` depends only on `X mod 2^H`. -/
theorem tr_mod (X H t : Nat) (ht : t < H) : tr (X % 2 ^ H) t = tr X t := by
  unfold tr
  apply iter_agree t H _ 0 (by omega)
  intro i hi
  simp [Nat.testBit_mod_two_pow, hi]

theorem wt_mod (X H : Nat) : wt H (X % 2 ^ H) = wt H X :=
  cnt_congr (fun i hi => by simp [Nat.testBit_mod_two_pow, hi]) H (Nat.le_refl _)

theorem wt_mono (X : Nat) {H H' : Nat} (h : H ≤ H') : wt H X ≤ wt H' X := cnt_mono _ h

theorem wt_le_total (X H : Nat) : wt H X ≤ wt X X := by
  have hz : ∀ i, X ≤ i → X.testBit i = false := fun i hi =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le Nat.lt_two_pow_self
      (Nat.pow_le_pow_right (by decide) hi))
  rcases Nat.le_total H X with h | h
  · exact cnt_mono _ h
  · unfold wt; rw [cnt_stable _ hz H h]; exact Nat.le_refl _

theorem GWord_mono {b : Nat → Bool} {H H' : Nat} (h : H' ≤ H) (hb : GWord b H) : GWord b H' :=
  fun t ht => hb t (by omega)

theorem gstep_congr {b b' : Nat → Bool} {t : Nat} (h : ∀ s, s ≤ t → b s = b' s) :
    gstep b t = gstep b' t := by
  unfold gstep
  split
  · rw [h 0 (by omega)]
  · split
    · rw [h t (by omega)]
    · rw [h t (by omega), h (t - 2) (by omega)]

theorem GWord_mod (X H : Nat) : GWord (tr (X % 2 ^ H)) H ↔ GWord (tr X) H := by
  constructor
  · intro hg t ht
    rw [← hg t ht]; symm
    exact gstep_congr (fun s hs => tr_mod X H s (by omega))
  · intro hg t ht
    rw [← hg t ht]
    exact gstep_congr (fun s hs => tr_mod X H s (by omega))

/-! ### Finite edge: a trace that is eventually all black is impossible -/

/-- cells of the space-time diagram -/
def x (X j t : Nat) : Bool := (iter F t X).testBit j

theorem x_rec0 (X t : Nat) : x X 1 t = xor (x X 0 (t + 1)) (x X 0 t) := by
  unfold x
  rw [iter_succ, testBit_F_zero]
  cases (iter F t X).testBit 0 <;> cases (iter F t X).testBit 1 <;> rfl

theorem x_rec (X j t : Nat) :
    x X (j + 2) t = xor (x X (j + 1) (t + 1)) (x X (j + 1) t || x X j t) := by
  unfold x
  rw [iter_succ, testBit_F_succ]
  cases (iter F t X).testBit (j + 2) <;> cases (iter F t X).testBit (j + 1) <;>
    cases (iter F t X).testBit j <;> rfl

theorem stripe_of_const (X T : Nat) (h : ∀ t, T ≤ t → x X 0 t = true) :
    ∀ j, (∀ t, T ≤ t → x X j t = (j % 2 == 0)) ∧
      (∀ t, T ≤ t → x X (j + 1) t = ((j + 1) % 2 == 0)) := by
  intro j
  induction j with
  | zero =>
    refine ⟨fun t ht => by simpa using h t ht, fun t ht => ?_⟩
    rw [x_rec0, h t ht, h (t + 1) (by omega)]; rfl
  | succ j ih =>
    refine ⟨ih.2, fun t ht => ?_⟩
    rw [x_rec, ih.2 t ht, ih.2 (t + 1) (by omega), ih.1 t ht]
    rcases Nat.mod_two_eq_zero_or_one j with hj | hj
    · have h1 : (j + 1) % 2 = 1 := by omega
      have h2 : (j + 1 + 1) % 2 = 0 := by omega
      simp [h1, h2, hj]
    · have h1 : (j + 1) % 2 = 0 := by omega
      have h2 : (j + 1 + 1) % 2 = 1 := by omega
      simp [h1, h2, hj]

theorem not_eventually_const (X T : Nat) : ¬ ∀ t, T ≤ t → tr X t = true := by
  intro h
  have hs := (stripe_of_const X T (fun t ht => h t ht) (2 * iter F T X)).1 T (Nat.le_refl _)
  have hlt : iter F T X < 2 ^ (2 * iter F T X) :=
    Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by decide) (by omega))
  have hf := Nat.testBit_lt_two_pow hlt
  unfold x at hs
  rw [hf] at hs
  simp at hs

/-- **No finite G seed from a mass bound.** -/
theorem no_seed_of_massbound (c d : Nat) (hyp : MassBound c d) (X : Nat) :
    ¬ ∀ H, GWord (tr X) H := by
  intro hX
  have hbound : ∀ m, zc (tr X) (2 * m) ≤ c * wt X X + d := by
    intro m
    have hY : X % 2 ^ (2 * m) < 2 ^ (2 * m) := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hg : GWord (tr (X % 2 ^ (2 * m))) (2 * m) := (GWord_mod X _).2 (hX _)
    have hZ : zc (tr (X % 2 ^ (2 * m))) (2 * m) = zc (tr X) (2 * m) :=
      cnt_congr (fun t ht => by simp only [tr_mod X _ t ht]) _ (Nat.le_refl _)
    have := hyp m _ hY hg
    rw [hZ, wt_mod] at this
    have hW := wt_le_total X (2 * m)
    have := Nat.mul_le_mul_left c hW
    omega
  have hall : ∀ n, zc (tr X) n ≤ c * wt X X + d := fun n =>
    Nat.le_trans (cnt_mono _ (by omega : n ≤ 2 * n)) (hbound n)
  obtain ⟨T, hT⟩ := eventually_false_of_cnt_bdd _ _ hall
  apply not_eventually_const X (2 * T)
  intro t ht
  rcases Nat.mod_two_eq_zero_or_one t with he | ho
  · have := hT t (by omega)
    simp only [he, Bool.and_eq_false_iff] at this
    cases hb : tr X t
    · simp [hb] at this
    · rfl
  · have := hX (t + 1) t (by omega)
    unfold gstep at this
    rw [ite_eq_right (by omega), ite_eq_left ho] at this
    exact this

/-! ### Bridge: rows of the official pattern as natural numbers -/

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

/-- one step of the official pattern on the left half is the zero-wall map `F`, whenever a
black center comes with a black column `-1`. -/
theorem rowNat_succ (t : Nat) (h : center t = true → cell t (-1) = true) :
    rowNat (t + 1) = F (rowNat t) := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases i with
  | zero =>
    rw [testBit_F_zero, testBit_rowNat, testBit_rowNat, testBit_rowNat]
    show cell (t + 1) (-1) = xor (cell t (-2)) (cell t (-1))
    rw [step' t (-1) (-2) (-1) 0 (by decide) rfl (by decide)]
    have hc : (cell t (-1) || cell t 0) = cell t (-1) := by
      cases h0 : cell t 0
      · simp
      · have := h h0; simp [this]
    simp only [rule]
    rw [hc]
  | succ j =>
    rw [testBit_F_succ, testBit_rowNat, testBit_rowNat, testBit_rowNat, testBit_rowNat]
    rw [step' t (-1 - ((j + 1 : Nat) : Int)) (-1 - ((j + 1 + 1 : Nat) : Int))
      (-1 - ((j + 1 : Nat) : Int)) (-1 - (j : Int)) (by omega) rfl (by omega)]
    rfl

theorem rowNat_iter (T : Nat) (h : ∀ s, center (T + s) = true → cell (T + s) (-1) = true) :
    ∀ s, iter F s (rowNat T) = rowNat (T + s) := by
  intro s
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [iter_succ, ih, ← rowNat_succ _ (h s), show T + (s + 1) = T + s + 1 by omega]

theorem tr_rowNat (T : Nat) (h : ∀ s, center (T + s) = true → cell (T + s) (-1) = true)
    (s : Nat) : tr (rowNat T) s = cell (T + s) (-1) := by
  unfold tr
  rw [rowNat_iter T h s, testBit_rowNat]; rfl

/-- alternating center from `T` (the kit's normal form). -/
def AltFrom (T : Nat) : Prop := ∀ k, cell (T + 2 * k) 0 = true ∧ cell (T + 2 * k + 1) 0 = false

theorem alt_guard {T : Nat} (hT : AltFrom T) (k0 : Nat) :
    ∀ s, center (T + 2 * k0 + 1 + s) = true → cell (T + 2 * k0 + 1 + s) (-1) = true := by
  intro s hs
  rcases Nat.mod_two_eq_zero_or_one s with he | ho
  · exfalso
    have := (hT (k0 + s / 2)).2
    unfold center at hs
    rw [show T + 2 * k0 + 1 + s = T + 2 * (k0 + s / 2) + 1 by omega, this] at hs
    exact absurd hs (by decide)
  · rw [show T + 2 * k0 + 1 + s = T + 2 * (k0 + s / 2 + 1) by omega]
    exact m1_even hT _

theorem alt_guard0 {T : Nat} (hT : AltFrom T) :
    ∀ s, center (T + s) = true → cell (T + s) (-1) = true := by
  intro s hs
  rcases Nat.mod_two_eq_zero_or_one s with he | ho
  · rw [show T + s = T + 2 * (s / 2) by omega]; exact m1_even hT _
  · exfalso
    have := (hT (s / 2)).2
    unfold center at hs
    rw [show T + s = T + 2 * (s / 2) + 1 by omega, this] at hs
    exact absurd hs (by decide)

/-- The actual left traces, read from a white time of column `-1` after an alternating center,
are G words of every length (the kit's `m1_even` and `golden`). -/
theorem lang_G {T : Nat} (hT : AltFrom T) (k0 : Nat) (hw : cell (T + 2 * k0 + 1) (-1) = false) :
    ∀ H, GWord (fun s => cell (T + 2 * k0 + 1 + s) (-1)) H := by
  intro H t _
  unfold gstep
  split
  · next h0 => subst h0; simpa using hw
  · split
    · next _ ho =>
      show cell (T + 2 * k0 + 1 + t) (-1) = true
      rw [show T + 2 * k0 + 1 + t = T + 2 * (k0 + t / 2 + 1) by omega]
      exact m1_even hT _
    · next h0 he =>
      show (cell (T + 2 * k0 + 1 + (t - 2)) (-1) || cell (T + 2 * k0 + 1 + t) (-1)) = true
      rw [show T + 2 * k0 + 1 + (t - 2) = T + 2 * (k0 + (t - 2) / 2) + 1 by omega,
        show T + 2 * k0 + 1 + t = T + 2 * (k0 + (t - 2) / 2) + 3 by omega]
      cases hc : cell (T + 2 * (k0 + (t - 2) / 2) + 1) (-1)
      · rw [golden hT _ hc]; rfl
      · rfl

/-- **The chain.** No finite seed with an infinite G trace excludes an eventual period 2 of the
official center column. -/
theorem not_eventually_period_two_of_noSeed (hno : ∀ X : Nat, ¬ ∀ H, GWord (tr X) H) :
    ¬ ∃ T0, ∀ t, T0 ≤ t → center (t + 2) = center t := by
  intro ⟨T0, hp⟩
  obtain ⟨T, hT⟩ := normalize hp
  have hwhite : ∃ k0, cell (T + 2 * k0 + 1) (-1) = false := by
    refine Classical.byContradiction fun hno' => ?_
    apply not_eventually_const (rowNat T) 0
    intro t _
    rw [tr_rowNat T (alt_guard0 hT) t]
    rcases Nat.mod_two_eq_zero_or_one t with he | ho
    · rw [show T + t = T + 2 * (t / 2) by omega]; exact m1_even hT _
    · rw [show T + t = T + 2 * (t / 2) + 1 by omega]
      cases hc : cell (T + 2 * (t / 2) + 1) (-1)
      · exact absurd ⟨t / 2, hc⟩ hno'
      · rfl
  obtain ⟨k0, hw⟩ := hwhite
  apply hno (rowNat (T + 2 * k0 + 1))
  intro H
  have hfun : tr (rowNat (T + 2 * k0 + 1)) = fun s => cell (T + 2 * k0 + 1 + s) (-1) :=
    funext (tr_rowNat _ (alt_guard hT k0))
  rw [hfun]
  exact lang_G hT k0 hw H

/-- **Any linear mass bound on the finite G words excludes period 2.** -/
theorem not_eventually_period_two_of_massbound (c d : Nat) (hyp : MassBound c d) :
    ¬ ∃ T0, ∀ t, T0 ≤ t → center (t + 2) = center t :=
  not_eventually_period_two_of_noSeed (no_seed_of_massbound c d hyp)

theorem massbound_of_floor (q d : Nat) (h : MassFloor q d) : MassBound q d := by
  intro m Y hY hg
  have := h (2 * m) Y hY hg
  have := cnt_le (fun t => t % 2 == 0 && !tr Y t) (2 * m)
  unfold zc; omega

/-- **Any positive linear floor on the seed weight of G words excludes period 2.** -/
theorem not_eventually_period_two_of_floor (q d : Nat) (h : MassFloor q d) :
    ¬ ∃ T0, ∀ t, T0 ≤ t → center (t + 2) = center t :=
  not_eventually_period_two_of_massbound q d (massbound_of_floor q d h)

/-! ## Part 2. Conjecture S -/

theorem gword_short (Y : Nat) (hg : GWord (tr Y) 1) : tr Y 0 = false := by
  have := hg 0 (by decide); simpa [gstep] using this

/-- S gives the floor `H ≤ 7·A + 1` (the case `H = 1` is the `+1`). -/
theorem floor_of_S (hS : ConjS) : MassFloor 7 1 := by
  intro H Y hY hg
  rcases Nat.lt_or_ge H 2 with h | h
  · omega
  · have := hS H Y h hY hg; omega

/-- **Conjecture S excludes period 2.** -/
theorem not_eventually_period_two_of_S (hS : ConjS) :
    ¬ ∃ T0, ∀ t, T0 ≤ t → center (t + 2) = center t :=
  not_eventually_period_two_of_floor 7 1 (floor_of_S hS)

/-- The even form implies S: at odd `H = 2m+1` the even prefix of length `2m` already carries
`2m + 5 = H + 4`. -/
theorem ConjS_of_even (hE : ConjSEven) : ConjS := by
  intro H Y hH hY hg
  rcases Nat.mod_two_eq_zero_or_one H with he | ho
  · have := hE (H / 2) Y (by omega) (by rw [show 2 * (H / 2) = H by omega]; exact hY)
      (by rw [show 2 * (H / 2) = H by omega]; exact hg)
    rw [show 2 * (H / 2) = H by omega] at this; omega
  · let m := H / 2
    have hm : H = 2 * m + 1 := by omega
    have hg' : GWord (tr (Y % 2 ^ (2 * m))) (2 * m) :=
      (GWord_mod Y _).2 (GWord_mono (by omega) hg)
    have := hE m (Y % 2 ^ (2 * m)) (by omega) (Nat.mod_lt _ (Nat.two_pow_pos _)) hg'
    rw [wt_mod] at this
    have := wt_mono Y (show 2 * m ≤ H by omega)
    omega

/-! ### A kernel-checked certificate of S for `H ≤ 90` -/

/-- Bound check at a node of length `k`. -/
def okB (k Y : Nat) : Bool :=
  if k < 2 then true else if k % 2 = 0 then decide (k + 5 ≤ 7 * wt k Y)
  else decide (k + 4 ≤ 7 * wt k Y)

/-- Exhaustive search over seeds, one bit at a time: node `(k, Y)` with `Y < 2^k` whose trace is
a G word of length `k`; its children are `Y` and `Y + 2^k`, kept when their trace passes the G
rule at time `k`. A node whose weight already gives `7·A ≥ N + 5` is not expanded: the weight of
its extensions can only grow (`wt_mono`, `wt_mod`). The kernel evaluates the faster `fdfs`,
which implies this search (`fdfs_dfs`). -/
def dfs (N : Nat) : Nat → Nat → Nat → Bool
  | 0, _, _ => true
  | f + 1, k, Y =>
    decide (N + 5 ≤ 7 * wt k Y) ||
    (okB k Y && (!(gstep (tr Y) k) || dfs N f (k + 1) Y) &&
      (!(gstep (tr (Y + 2 ^ k)) k) || dfs N f (k + 1) (Y + 2 ^ k)))

theorem mod_succ_cases (Z k : Nat) :
    Z % 2 ^ (k + 1) = Z % 2 ^ k ∨ Z % 2 ^ (k + 1) = Z % 2 ^ k + 2 ^ k := by
  rw [Nat.mod_pow_succ]
  have : Z / 2 ^ k % 2 < 2 := Nat.mod_lt _ (by decide)
  rcases (by omega : Z / 2 ^ k % 2 = 0 ∨ Z / 2 ^ k % 2 = 1) with h | h <;> rw [h] <;> simp

theorem mod_mod_succ (Z k : Nat) : Z % 2 ^ (k + 1) % 2 ^ k = Z % 2 ^ k :=
  Nat.mod_mod_of_dvd Z (Nat.pow_dvd_pow 2 (Nat.le_succ k))

/-- **Soundness of the search.** -/
theorem dfs_sound (N : Nat) : ∀ f k Y, dfs N f k Y = true → ∀ j Z, j < f → k + j ≤ N →
    Z < 2 ^ (k + j) → Z % 2 ^ k = Y → GWord (tr Z) (k + j) → okB (k + j) Z = true := by
  intro f
  induction f with
  | zero => intro k Y _ j Z hj; omega
  | succ f ih =>
    intro k Y hd j Z hj hkN hZ hZY hg
    simp only [dfs, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hd
    rcases hd with hpr | hd
    · have hw : wt k Y ≤ wt (k + j) Z := by
        rw [← hZY, wt_mod]; exact wt_mono Z (by omega)
      have := of_decide_eq_true hpr
      unfold okB
      split
      · rfl
      · split <;> (apply decide_eq_true; omega)
    obtain ⟨⟨hok, h0⟩, h1⟩ := hd
    cases j with
    | zero =>
      have : Z % 2 ^ k = Z := Nat.mod_eq_of_lt (by simpa using hZ)
      rw [this] at hZY; subst hZY; simpa using hok
    | succ j =>
      have hZ' : Z % 2 ^ (k + 1) % 2 ^ k = Y := by rw [mod_mod_succ]; exact hZY
      have hgk : gstep (tr (Z % 2 ^ (k + 1))) k = true := by
        have := (GWord_mod Z (k + 1)).2 (GWord_mono (by omega) hg)
        exact this k (by omega)
      have hrec : dfs N f (k + 1) (Z % 2 ^ (k + 1)) = true := by
        rcases mod_succ_cases Z k with e | e
        · rw [e, hZY] at hgk ⊢
          rcases h0 with h0 | h0
          · rw [h0] at hgk; exact absurd hgk (by decide)
          · exact h0
        · rw [e, hZY] at hgk ⊢
          rcases h1 with h1 | h1
          · rw [h1] at hgk; exact absurd hgk (by decide)
          · exact h1
      have := ih (k + 1) _ hrec j Z (by omega) (by omega) (by rw [show k + 1 + j = k + (j + 1) by omega]; exact hZ)
        rfl (by rw [show k + 1 + j = k + (j + 1) by omega]; exact hg)
      rwa [show k + 1 + j = k + (j + 1) by omega] at this

/-! ### The kernel-checked search implies the plain search -/

/-- Raising bit `k` of a seed flips bit `k - t` of its `t`-th iterate and keeps the bits below. -/
theorem iter_top (Y k : Nat) : ∀ t i, i + t ≤ k →
    (iter F t (Y + 2 ^ k)).testBit i = xor ((iter F t Y).testBit i) (decide (i + t = k)) := by
  intro t
  induction t with
  | zero =>
    intro i hi
    show (Y + 2 ^ k).testBit i = xor (Y.testBit i) (decide (i + 0 = k))
    rw [Nat.add_comm Y]
    rcases Nat.lt_or_ge i k with h | h
    · rw [Nat.testBit_two_pow_add_gt h, show decide (i + 0 = k) = false by simp; omega,
        Bool.xor_false]
    · rw [show i = k by omega, Nat.testBit_two_pow_add_eq]; simp
  | succ t ih =>
    intro i hi
    rw [iter_succ, iter_succ, testBit_F, testBit_F, ih (i + 1) (by omega), ih i (by omega),
      ih (i - 1) (by omega), show decide (i + t = k) = false by simp; omega,
      show decide (i - 1 + t = k) = false by simp; omega, Bool.xor_false, Bool.xor_false,
      show i + 1 + t = i + (t + 1) by omega, Bool.xor_right_comm]

/-- The trace of `Y + 2 ^ k` at time `k` is the opposite of that of `Y`. -/
theorem tr_top (Y k : Nat) : tr (Y + 2 ^ k) k = !tr Y k := by
  unfold tr; rw [iter_top Y k k 0 (by omega)]; simp

/-- Before time `k` the traces of `Y + 2 ^ k` and `Y` agree. -/
theorem tr_low (Y k t : Nat) (ht : t < k) : tr (Y + 2 ^ k) t = tr Y t := by
  unfold tr
  rw [iter_top Y k t 0 (by omega), show decide (0 + t = k) = false by simp; omega,
    Bool.xor_false]

theorem trPair_snd (k Y : Nat) : (trPair k Y).2 = tr Y k := by
  unfold trPair pairOf tr
  split
  · next h => rw [show k - 2 = 0 by omega]; rfl
  · next h =>
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    rw [Nat.add_sub_cancel]; rfl

theorem trPair_fst (k Y : Nat) (hk : 2 ≤ k) : (trPair k Y).1 = tr Y (k - 2) := by
  unfold trPair pairOf tr
  rw [ite_eq_right (by omega)]

theorem gstep_trPair (k Y : Nat) : gstep (tr Y) k = gs k (trPair k Y).1 (trPair k Y).2 := by
  rw [trPair_snd]
  unfold gstep gs
  by_cases h0 : k = 0
  · subst h0; rfl
  · rw [ite_eq_right h0, ite_eq_right h0]
    by_cases h1 : k % 2 = 1
    · rw [ite_eq_left h1, ite_eq_left h1]
    · rw [ite_eq_right h1, ite_eq_right h1, trPair_fst k Y (by omega)]

theorem gstep_top (k Y : Nat) :
    gstep (tr (Y + 2 ^ k)) k = gs k (trPair k Y).1 (!(trPair k Y).2) := by
  rw [gstep_trPair, trPair_snd, trPair_snd, tr_top]
  by_cases h : 2 ≤ k
  · rw [trPair_fst _ _ h, trPair_fst _ _ h, tr_low Y k (k - 2) (by omega)]
  · unfold gs
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> rfl

theorem wt_succ_low (k Y : Nat) (hY : Y < 2 ^ k) : wt (k + 1) Y = wt k Y := by
  unfold wt; simp only [cnt, Nat.testBit_lt_two_pow hY]; rfl

theorem wt_succ_top (k Y : Nat) (hY : Y < 2 ^ k) : wt (k + 1) (Y + 2 ^ k) = wt k Y + 1 := by
  unfold wt; simp only [cnt]
  rw [cnt_congr (g := Y.testBit) (fun i hi => by
      rw [Nat.add_comm Y]; exact Nat.testBit_two_pow_add_gt hi Y) k (Nat.le_refl _),
    Nat.add_comm Y, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hY]; rfl

/-- **The kernel-checked search implies the plain search**: `fdfs` carries the weight `w` of the
seed and computes both children's trace bits from one iteration (`gstep_trPair`, `gstep_top`). -/
theorem fdfs_dfs (N : Nat) : ∀ f k Y w, Y < 2 ^ k → w = wt k Y → fdfs N f k Y w = true →
    dfs N f k Y = true := by
  intro f
  induction f with
  | zero => intro _ _ _ _ _ _; rfl
  | succ f ih =>
    intro k Y w hY hw hd
    subst hw
    have i1 := ih (k + 1) Y (wt k Y) (by rw [Nat.pow_succ]; omega) (wt_succ_low k Y hY).symm
    have i2 := ih (k + 1) (Y + 2 ^ k) (wt k Y + 1) (by rw [Nat.pow_succ]; omega)
      (wt_succ_top k Y hY).symm
    simp only [fdfs, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hd
    simp only [dfs, gstep_top k Y, gstep_trPair k Y, Bool.and_eq_true, Bool.or_eq_true,
      Bool.not_eq_true']
    rcases hd with h | ⟨⟨ho, h1⟩, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨⟨ho, h1.imp_right i1⟩, h2.imp_right i2⟩

/-- The search to length `90` succeeds: the kernel check `fcert90` through `fdfs_dfs`. -/
theorem cert90 : dfs 90 91 0 0 = true := fdfs_dfs 90 91 0 0 0 (by decide) rfl fcert90

/-- **S holds for every length `H ≤ 90`**, in its even form at even `H` (kernel-checked
exhaustive search). -/
theorem S_upto_90 : ∀ H Y, 2 ≤ H → H ≤ 90 → Y < 2 ^ H → GWord (tr Y) H →
    (H % 2 = 0 → H + 5 ≤ 7 * wt H Y) ∧ H + 4 ≤ 7 * wt H Y := by
  intro H Y h2 h40 hY hg
  have := dfs_sound 90 91 0 0 cert90 H Y (by omega) (by omega) (by simpa using hY) (by rw [Nat.pow_zero, Nat.mod_one])
    (by simpa using hg)
  simp only [Nat.zero_add, okB] at this
  rw [ite_eq_right (by omega)] at this
  split at this
  · next he => have := of_decide_eq_true this; exact ⟨fun _ => this, by omega⟩
  · next ho => have := of_decide_eq_true this; exact ⟨fun h => absurd h ho, this⟩

/-- Sharpness at `H = 2`: the seed `2` (black at depth `2`) is a G word of length `2` with
`7·A = H + 5`. -/
theorem sharp_two : GWord (tr 2) 2 ∧ 7 * wt 2 2 = 2 + 5 := by
  refine ⟨fun t ht => ?_, by decide⟩
  match t, ht with
  | 0, _ => decide
  | 1, _ => decide

/-- The extremal seeds at `H = 86, 198, 310` (truncations of the ether seeds with the last block
changed); bit `i` is the cell at depth `i + 1`. -/
def Y86 : Nat := 2379775235461868454166
def Y198 : Nat := 12356499479107639298889349258282807905713298119023690006
def Y310 : Nat := 64158613427857829488769942942027658615794280115462559075154029900925395268136589171130646

/-- **Sharpness at `H = 86` and `87`**: `7·A = H + 5` and `7·A = H + 4`. -/
theorem sharp_86 : Y86 < 2 ^ 86 ∧ GWord (tr Y86) 87 ∧ 7 * wt 86 Y86 = 86 + 5 ∧
    7 * wt 87 Y86 = 87 + 4 := by
  refine ⟨by decide +kernel, fun t ht => ?_, by decide +kernel, by decide +kernel⟩
  revert t; decide +kernel

/-- **Sharpness at `H = 198` and `199`.** -/
theorem sharp_198 : Y198 < 2 ^ 198 ∧ GWord (tr Y198) 199 ∧ 7 * wt 198 Y198 = 198 + 5 ∧
    7 * wt 199 Y198 = 199 + 4 := by
  refine ⟨by decide +kernel, fun t ht => ?_, by decide +kernel, by decide +kernel⟩
  revert t; decide +kernel

/-- **Sharpness at `H = 310` and `311`** (beyond the certified range). -/
theorem sharp_310 : Y310 < 2 ^ 310 ∧ GWord (tr Y310) 311 ∧ 7 * wt 310 Y310 = 310 + 5 ∧
    7 * wt 311 Y310 = 311 + 4 := by
  refine ⟨by decide +kernel, fun t ht => ?_, by decide +kernel, by decide +kernel⟩
  revert t; decide +kernel

/-! ## Part 3. The tail law: the preimage transducer of the zero-wall map -/

/-- One step of the inverse transducer: a preimage `y` of `z` satisfies
`y (i+1) = z i xor (y i or y (i-1))`; the state `(y i, y (i-1))` is encoded as `a + 2 b`. -/
def mm (z : Bool) (s : Fin 4) : Fin 4 :=
  match z, s with
  | false, 0 => 0 | false, 1 => 3 | false, 2 => 1 | false, 3 => 3
  | true, 0 => 1  | true, 1 => 2  | true, 2 => 0  | true, 3 => 2

/-- apply a stored map -/
def ap (f : List (Fin 4)) (s : Fin 4) : Fin 4 := f.getD s.val 0

/-- post-compose with one step -/
def post (z : Bool) (f : List (Fin 4)) : List (Fin 4) := f.map (mm z)

def idm : List (Fin 4) := [0, 1, 2, 3]

/-- the composite along a word read left to right -/
def comp (w : List Bool) : List (Fin 4) := w.foldl (fun f z => post z f) idm

/-- The 40 composite maps. -/
def S40 : List (List (Fin 4)) := [
  [0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 2, 0], [0, 0, 3, 0], [0, 1, 0, 1], [0, 1, 1, 1],
  [0, 1, 2, 1], [0, 2, 0, 2], [0, 2, 2, 2], [0, 3, 0, 3], [0, 3, 1, 3], [0, 3, 3, 3],
  [1, 0, 0, 0], [1, 0, 1, 0], [1, 0, 3, 0], [1, 1, 0, 1], [1, 1, 1, 1], [1, 1, 2, 1],
  [1, 1, 3, 1], [1, 2, 0, 2], [1, 2, 1, 2], [1, 2, 2, 2], [1, 3, 1, 3], [1, 3, 3, 3],
  [2, 0, 0, 0], [2, 0, 1, 0], [2, 0, 2, 0], [2, 1, 1, 1], [2, 1, 2, 1], [2, 2, 0, 2],
  [2, 2, 1, 2], [2, 2, 2, 2], [3, 0, 0, 0], [3, 0, 3, 0], [3, 1, 0, 1], [3, 1, 1, 1],
  [3, 1, 3, 1], [3, 3, 0, 3], [3, 3, 1, 3], [3, 3, 3, 3]]

theorem S40_length : S40.length = 40 := by decide

theorem closed : ∀ f ∈ S40, ∀ z : Bool, post z f ∈ S40 := by decide

theorem foldl_mem : ∀ (w : List Bool) (f : List (Fin 4)), f ∈ S40 →
    w.foldl (fun f z => post z f) f ∈ S40
  | [], _, hf => hf
  | z :: w, f, hf => foldl_mem w (post z f) (closed f hf z)

/-- **The composite along any nonempty word is one of the 40 maps.** -/
theorem comp_mem : ∀ w : List Bool, w ≠ [] → comp w ∈ S40
  | [], h => absurd rfl h
  | z :: w, _ => by
    unfold comp
    rw [List.foldl_cons]
    exact foldl_mem w _ (by cases z <;> decide)

/-- `itr f n` is the `n`-fold iterate of `f`. -/
def itr (f : Fin 4 → Fin 4) : Nat → Fin 4 → Fin 4
  | 0, s => s
  | n + 1, s => itr f n (f s)

theorem itr_add (f : Fin 4 → Fin 4) : ∀ a b s, itr f (a + b) s = itr f b (itr f a s)
  | 0, b, s => by simp [itr]
  | a + 1, b, s => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [itr]
    exact itr_add f a b (f s)

/-- **Every cycle of every composite has length dividing 6**: `f^6 (f^4 s) = f^4 s`. -/
theorem cyc_div6 : ∀ f ∈ S40, ∀ s : Fin 4, itr (ap f) 6 (itr (ap f) 4 s) = itr (ap f) 4 s := by
  decide

/-- **No composite has a cycle of length 4**: `f^4 s = s` already gives `f^2 s = s`. -/
theorem no_four_cycle (w : List Bool) (hw : w ≠ []) (s : Fin 4)
    (h4 : itr (ap (comp w)) 4 s = s) : itr (ap (comp w)) 2 s = s := by
  have h := cyc_div6 _ (comp_mem w hw) s
  rw [h4] at h
  have e : itr (ap (comp w)) 6 s = itr (ap (comp w)) 2 (itr (ap (comp w)) 4 s) := by
    rw [← itr_add]
  rw [e, h4] at h
  exact h

/-! ### Two preimage runs of the same word -/

section Runs
variable {z y y' : Nat → Bool}

/-- `y` is a preimage run of `z`. -/
def Run (z y : Nat → Bool) : Prop := ∀ i, y (i + 2) = xor (z (i + 1)) (y (i + 1) || y i)

/-- the states `(y (i+1), y i)` never coincide -/
def Apart (y y' : Nat → Bool) : Prop := ∀ i, (y (i + 1), y i) ≠ (y' (i + 1), y' i)

theorem agree_zero (hy : Run z y) (hy' : Run z y') (ha : Apart y y') (i : Nat)
    (h : y (i + 1) = y' (i + 1)) : y (i + 1) = false := by
  cases h1 : y (i + 1)
  · rfl
  · have h2 : y' (i + 1) = true := by rw [← h]; exact h1
    exfalso
    apply ha (i + 1)
    rw [hy i, hy' i, h1, h2]
    simp

theorem agree_next (hy : Run z y) (hy' : Run z y') (ha : Apart y y') (i : Nat)
    (h : y (i + 1) = y' (i + 1)) : y (i + 2) ≠ y' (i + 2) ∧ y (i + 3) ≠ y' (i + 3) := by
  have h0 := agree_zero hy hy' ha i h
  have h0' : y' (i + 1) = false := by rw [← h]; exact h0
  have hi : y i ≠ y' i := by
    intro e; apply ha i; rw [h, e]
  have e2 : y (i + 2) = xor (z (i + 1)) (y i) := by rw [hy i, h0]; simp
  have e2' : y' (i + 2) = xor (z (i + 1)) (y' i) := by rw [hy' i, h0']; simp
  have d2 : y (i + 2) ≠ y' (i + 2) := by
    rw [e2, e2']; intro e; apply hi
    cases hz : z (i + 1) <;> cases h3 : y i <;> cases h4 : y' i <;> simp_all
  refine ⟨d2, ?_⟩
  have e3 : y (i + 3) = xor (z (i + 2)) (y (i + 2)) := by rw [hy (i + 1), h0]; simp
  have e3' : y' (i + 3) = xor (z (i + 2)) (y' (i + 2)) := by rw [hy' (i + 1), h0']; simp
  rw [e3, e3']; intro e; apply d2
  cases hz : z (i + 2) <;> cases h3 : y (i + 2) <;> cases h4 : y' (i + 2) <;> simp_all

/-- the mass of the two runs at one position -/
def pm (y y' : Nat → Bool) (i : Nat) : Nat := (if y i then 1 else 0) + (if y' i then 1 else 0)

theorem pos_mass (hy : Run z y) (hy' : Run z y') (ha : Apart y y') (i : Nat) :
    pm y y' (i + 1) = if y (i + 1) = y' (i + 1) then 0 else 1 := by
  unfold pm
  by_cases e : y (i + 1) = y' (i + 1)
  · have h0 := agree_zero hy hy' ha i e
    have h0' : y' (i + 1) = false := by rw [← e]; exact h0
    simp [e, h0']
  · rw [ite_eq_right e]
    cases h1 : y (i + 1) <;> cases h2 : y' (i + 1) <;> simp_all

theorem block_mass (hy : Run z y) (hy' : Run z y') (ha : Apart y y') (p : Nat) :
    2 ≤ pm y y' (p + 1) + pm y y' (p + 2) + pm y y' (p + 3) := by
  have m1 := pos_mass hy hy' ha p
  have m2 := pos_mass hy hy' ha (p + 1)
  have m3 := pos_mass hy hy' ha (p + 2)
  have n1 := agree_next hy hy' ha p
  have n2 := agree_next hy hy' ha (p + 1)
  rw [m1, m2, m3]
  by_cases a1 : y (p + 1) = y' (p + 1)
  · have := n1 a1; simp_all
  · by_cases a2 : y (p + 2) = y' (p + 2)
    · have := n2 a2; simp_all
    · simp only [a1, a2, ite_false]; split <;> omega

/-- the total mass of the two runs on positions `q+1, …, q+n` -/
def mass (y y' : Nat → Bool) (q : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => mass y y' q n + pm y y' (q + 1 + n)

/-- **Disagreement lemma**: two preimage runs of the same word that never share a state carry at
least `2n` ones on any `3n` consecutive positions. -/
theorem mass_two_thirds (hy : Run z y) (hy' : Run z y') (ha : Apart y y') (q : Nat) :
    ∀ n, 2 * n ≤ mass y y' q (3 * n) := by
  intro n
  induction n with
  | zero => simp [mass]
  | succ n ih =>
    have e : mass y y' q (3 * (n + 1)) = mass y y' q (3 * n) + pm y y' (q + 1 + 3 * n) +
        pm y y' (q + 1 + (3 * n + 1)) + pm y y' (q + 1 + (3 * n + 1 + 1)) := by
      rw [show 3 * (n + 1) = 3 * n + 1 + 1 + 1 by omega]; rfl
    rw [e]
    have hb := block_mass hy hy' ha (q + 3 * n)
    rw [show q + 3 * n + 1 = q + 1 + 3 * n by omega, show q + 3 * n + 2 = q + 1 + (3 * n + 1) by omega,
      show q + 3 * n + 3 = q + 1 + (3 * n + 1 + 1) by omega] at hb
    omega

end Runs

end Rule30PeriodTwoMass
end Ruliology.CellularAutomata
