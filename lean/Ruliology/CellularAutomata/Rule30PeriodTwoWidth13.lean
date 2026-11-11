module

public import Ruliology.CellularAutomata.Rule30PeriodTwo
public import Ruliology.CellularAutomata.Rule30GateTrap
public import Ruliology.CellularAutomata.Rule30GateTrapWords
public import Ruliology.CellularAutomata.Rule30Certificates.PeriodTwoWidth13

/-!
# Rule 30: period 2, the right half forces the left trace into a nine-pair gap language

Suppose the center column of rule 30 were eventually 2-periodic. By `Rule30PeriodTwo.normalize` it
alternates black, white from some time `T` (`AltFrom T`), column `-1` is black at the black times
(`Rule30PeriodTwo.m1_even`), and the left half evolves as the zero-driven half-line, which on finite
starts is the integer map `Rule30ZeroBoundary.IntegerForm.F`; `tr Y` is column `-1` of the start
`Y` (bit `i` is cell `-1 - i`). The kit reduces period 2 to the open `Rule30PeriodTwo.Q01`. This
module uses the right half as well, but only through a theorem that holds for every right half,
finite or not.

* **The left language** `GE2 b m`, on the first `2 m` values of a left trace `b` (column `-1` read
  from a white time of column `-1`): column `-1` is black at the black center times (`GValid`),
  the white cells of column `-1` at the white center times are `2`, `3`, `4` or `5` pairs of steps
  apart, and consecutive gaps form one of the nine pairs `22 24 25 33 35 45 52 53 55`, so `23 32 34
  42 43 44 54` never occur (`E2Run`).
* `lang_GE2`: under an alternating center, the left traces read from every late white time of
  column `-1` are in `GE2` for every length. The columns `1..13` and the center form a strip of
  `16384` nodes with column `14` free (any right half). The kernel checks a rank certificate of
  its condensation and, inside its two recurrent levels, an inductive set of states of a gap
  automaton (`certOK_true`, data in `Rule30Certificates.PeriodTwoWidth13`). One level is the E2
  language; the other (gap `4` only) would make column `-1` eventually 8-periodic, which a finite
  left half excludes (`tr_not_eventually_periodic`, Jen in the half-line). More generally the kicks
  (column `1` at the white times) are never eventually periodic (`kicks_not_eventually_periodic`).
* `NoSeedGE2` (**open**): no finite left seed `X` has all its trace prefixes in `GE2`.
  `not_eventually_period_two_of_noSeed_GE2`: it excludes an eventual period 2 of the center column,
  for every transient.
* `noSeed_GE2_of_Q01`: the kit's `Q01` implies `NoSeedGE2`, through the bridge `L_zero_eq_iterate`
  (the kit's zero-driven left half `L (fun _ => false)` is `F` iterated on finite starts). So
  `NoSeedGE2` is a weakening of `Q01` that still excludes period 2
  (`not_eventually_period_two_of_Q01_via_E2`).
* Mass bounds: if the even-time zeros of the finite `GE2` words (`Zc`) are bounded by a function of
  the seed weight (`wtH`), then `NoSeedGE2` holds (`noSeed_GE2_of_massBoundFun`) and period 2 is
  excluded (`not_eventually_period_two_of_E2_fun`; the linear form is
  `not_eventually_period_two_of_E2`). By Kőnig's lemma the function form is equivalent to
  `NoSeedGE2`; only the direction used here is formalized.
* `CQ01_of_RD_of_Q01Gap`: for the kit's coupled question `Rule30PeriodTwoCoupled.CQ01`, an open
  right dichotomy `RD` (every finite right half enters the gate trap `Rule30GateTrap.trap` at a
  white time or has eventually periodic column `1` at the white times) together with the kit's open
  `Rule30GateTrap.Q01Gap` gives `CQ01`; `no_eventual_period_two_of_RD_of_Q01Gap` is the
  single-seed corollary.

`Rule30PeriodTwoWidth5` and `Rule30PeriodTwoWidth6` forbid finitely many column-`1` words at strip
widths `5` and `6`; at width `13` the certificate pins the gaps between kicks to the nine-pair
language. `NoSeedGE2`, `RD`, `Q01Gap` and `Q01` are open, and nothing here excludes period 2.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30PeriodTwoWidth13

open Rule30ZeroBoundary.IntegerForm (F iter)

section ZeroWall

/-! ## The zero-driven left half as an integer map

A finite left half is a natural number `Y`, bit `i` being cell `-1 - i`; one step of the left half
beside a white wall is the kit's `Rule30ZeroBoundary.IntegerForm.F`, and `tr Y` is column `-1`. -/

/-- `iter F (t + 1) Y = iter F t (F Y)`. -/
theorem iter_succ_right (t Y : Nat) : iter F (t + 1) Y = iter F t (F Y) := by
  induction t with
  | zero => rfl
  | succ t ih => show F (iter F (t + 1) Y) = F (iter F t (F Y)); rw [ih]

theorem iter_succ (t Y : Nat) : iter F (t + 1) Y = F (iter F t Y) := rfl

/-- The trace of the finite left half `Y`: column `-1` (bit `0`) at time `t`. -/
def tr (Y : Nat) (t : Nat) : Bool := (iter F t Y).testBit 0

/-- `G` on a prefix of `m` pairs (all references are at times `< 2 m`): white at time `0`, black at
the odd times, and no two consecutive whites at the even times. -/
def GValid (b : Nat → Bool) (m : Nat) : Prop :=
  (0 < m → b 0 = false) ∧ (∀ j < m, b (2 * j + 1) = true) ∧
    (∀ j, j + 1 < m → (b (2 * j) || b (2 * j + 2)) = true)

/-- The number of even-time zeros among `b 0, b 2, …, b (2 m - 2)`, that is, of the `j < m` with
`b (2 * j) = false` (`Zc_eq_countP`). -/
def Zc (b : Nat → Bool) : Nat → Nat
  | 0 => 0
  | m + 1 => Zc b m + (if b (2 * m) = false then 1 else 0)

/-- The number of black bits of `Y` below position `H`, that is, of the `i < H` with
`Y.testBit i = true` (`wtH_eq_countP`). -/
def wtH : Nat → Nat → Nat
  | 0, _ => 0
  | H + 1, Y => wtH H Y + (if Y.testBit H = true then 1 else 0)

theorem Zc_eq_countP (b : Nat → Bool) (m : Nat) :
    Zc b m = (List.range m).countP (fun j => b (2 * j) == false) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.countP_append, ← ih]
    simp only [Zc]
    cases h : b (2 * m) <;> simp [h]

theorem wtH_eq_countP (H Y : Nat) :
    wtH H Y = (List.range H).countP (fun i => Y.testBit i) := by
  induction H with
  | zero => rfl
  | succ H ih =>
    rw [List.range_succ, List.countP_append, ← ih]
    simp only [wtH]
    cases h : Y.testBit H <;> simp [h]

/-- The (linear form of the) mass bound, for finite words of `G`. -/
def MassBound (c d : Nat) : Prop :=
  ∀ m Y : Nat, Y < 2 ^ (2 * m) → GValid (tr Y) m → Zc (tr Y) m ≤ c * wtH (2 * m) Y + d

theorem testBit_F (Y i : Nat) :
    (F Y).testBit i = (Y.testBit (i + 1) ^^ (Y.testBit i || (decide (i ≥ 1) && Y.testBit (i - 1)))) := by
  rw [show F Y = (Y >>> 1) ^^^ (Y ||| (Y <<< 1)) from rfl]
  simp [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_shiftLeft,
    Nat.add_comm]

/-- One step of causality: agreement below `N` gives agreement of `F` below `N - 1`. -/
theorem F_agree {Y Y' N : Nat} (h : ∀ i < N, Y.testBit i = Y'.testBit i) :
    ∀ i, i + 1 < N → (F Y).testBit i = (F Y').testBit i := by
  intro i hi
  rw [testBit_F, testBit_F, h (i + 1) hi, h i (by omega)]
  by_cases h1 : i ≥ 1
  · rw [h (i - 1) (by omega)]
  · simp [h1]

theorem iter_agree {Y Y' : Nat} : ∀ t N, (∀ i < N, Y.testBit i = Y'.testBit i) →
    ∀ i, i + t < N → (iter F t Y).testBit i = (iter F t Y').testBit i := by
  intro t
  induction t with
  | zero => intro N h i hi; exact h i (by omega)
  | succ t ih =>
    intro N h i hi
    rw [iter_succ, iter_succ]
    have := ih N h
    exact F_agree (N := N - t) (fun j hj => this j (by omega)) i (by omega)

/-- Causality: the trace through time `H - 1` depends only on `Y % 2 ^ H`. -/
theorem tr_mod (X H t : Nat) (ht : t < H) : tr (X % 2 ^ H) t = tr X t := by
  unfold tr
  apply iter_agree t H _ 0 (by omega)
  intro i hi
  simp [Nat.testBit_mod_two_pow, hi]

theorem wtH_congr {Y Y' : Nat} : ∀ H, (∀ i < H, Y.testBit i = Y'.testBit i) → wtH H Y = wtH H Y'
  | 0, _ => rfl
  | H + 1, h => by
    simp only [wtH]
    rw [wtH_congr H (fun i hi => h i (by omega)), h H (by omega)]

theorem wtH_mod (X H : Nat) : wtH H (X % 2 ^ H) = wtH H X :=
  wtH_congr H (fun i hi => by rw [Nat.testBit_mod_two_pow]; simp [hi])

theorem wtH_mono (X : Nat) {H H' : Nat} (h : H ≤ H') : wtH H X ≤ wtH H' X := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    have := ih (by omega)
    rw [show H + (d + 1) = (H + d) + 1 by omega]
    simp only [wtH]
    omega

/-- Above the highest black bit the count stops growing. -/
theorem wtH_stable {Y H : Nat} (hz : ∀ i, H ≤ i → Y.testBit i = false) :
    ∀ d, wtH (H + d) Y = wtH H Y
  | 0 => rfl
  | d + 1 => by
    rw [show H + (d + 1) = (H + d) + 1 by omega]
    simp only [wtH]
    rw [wtH_stable hz d, hz (H + d) (by omega)]
    rfl

theorem Zc_succ (b : Nat → Bool) (m : Nat) :
    Zc b (m + 1) = Zc b m + (if b (2 * m) = false then 1 else 0) := rfl

theorem Zc_congr {b b' : Nat → Bool} : ∀ m, (∀ j < m, b (2 * j) = b' (2 * j)) → Zc b m = Zc b' m
  | 0, _ => rfl
  | m + 1, h => by
    rw [Zc_succ, Zc_succ, Zc_congr m (fun j hj => h j (by omega)), h m (by omega)]

theorem Zc_mono (b : Nat → Bool) {m m' : Nat} (h : m ≤ m') : Zc b m ≤ Zc b m' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    have := ih (by omega)
    rw [show m + (d + 1) = (m + d) + 1 by omega, Zc_succ]
    omega

/-- A bounded zero count means eventually no even-time zeros. -/
theorem eventually_no_zero (b : Nat → Bool) (B : Nat) (hB : ∀ m, Zc b m ≤ B) :
    ∃ T, ∀ j, T ≤ j → b (2 * j) = true := by
  obtain ⟨k, hk, hmin⟩ :=
    Rule30DrivenLeft.exists_least_nat (P := fun k => ∀ m, Zc b m ≤ k) ⟨B, hB⟩
  by_cases h0 : k = 0
  · refine ⟨0, fun j _ => ?_⟩
    have := hk (j + 1)
    rw [Zc_succ] at this
    cases hbj : b (2 * j) <;> simp_all
  · have : ¬ ∀ m, Zc b m ≤ k - 1 := hmin (k - 1) (by omega)
    obtain ⟨m0, hm0⟩ := Classical.not_forall.mp this
    have hm0 : k - 1 < Zc b m0 := Nat.lt_of_not_le hm0
    refine ⟨m0, fun j hj => ?_⟩
    have h1 := hk (j + 1)
    have h2 := Zc_mono b hj
    rw [Zc_succ] at h1
    cases hbj : b (2 * j)
    · rw [hbj] at h1; simp at h1; omega
    · rfl

/-- `n` is even or odd. -/
theorem exists_half (n : Nat) : ∃ k, n = 2 * k ∨ n = 2 * k + 1 := ⟨n / 2, by omega⟩

/-- cells of the space-time diagram -/
def x (X : Nat) (j t : Nat) : Bool := (iter F t X).testBit j

theorem x_rec0 (X t : Nat) : x X 1 t = (x X 0 (t + 1) ^^ x X 0 t) := by
  unfold x
  rw [iter_succ, testBit_F]
  cases (iter F t X).testBit 0 <;> cases (iter F t X).testBit 1 <;> simp

theorem x_rec (X j t : Nat) :
    x X (j + 2) t = (x X (j + 1) (t + 1) ^^ (x X (j + 1) t || x X j t)) := by
  unfold x
  rw [iter_succ, testBit_F]
  simp only [show j + 1 + 1 = j + 2 by omega, show j + 1 - 1 = j by omega,
    show (decide (j + 1 ≥ 1)) = true by simp, Bool.true_and]
  cases (iter F t X).testBit (j + 2) <;> cases (iter F t X).testBit (j + 1) <;>
    cases (iter F t X).testBit j <;> simp

/-- finite-edge step: an eventually constant-one trace forces the stripe on a whole row -/
theorem stripe_of_const (X T : Nat) (h : ∀ t, T ≤ t → x X 0 t = true) :
    ∀ j t, T ≤ t → x X j t = (j % 2 == 0) := by
  intro j
  induction j using Nat.strongRecOn with
  | ind j ih =>
    intro t ht
    match j, ih with
    | 0, _ => simpa using h t ht
    | 1, _ => rw [x_rec0, h t ht, h (t + 1) (by omega)]; rfl
    | j + 2, ih =>
      rw [x_rec, ih (j + 1) (by omega) t ht, ih (j + 1) (by omega) (t + 1) (by omega),
        ih j (by omega) t ht]
      rcases Nat.mod_two_eq_zero_or_one j with hj | hj
      · have : (j + 1) % 2 = 1 := by omega
        have h2 : (j + 2) % 2 = 0 := by omega
        simp [this, hj, h2]
      · have : (j + 1) % 2 = 0 := by omega
        have h2 : (j + 2) % 2 = 1 := by omega
        simp [this, hj, h2]

theorem not_eventually_const (X T : Nat) : ¬ ∀ t, T ≤ t → tr X t = true := by
  intro h
  have hs := stripe_of_const X T (fun t ht => h t ht) (2 * iter F T X) T (Nat.le_refl _)
  have hlt : iter F T X < 2 ^ (2 * iter F T X) := by
    calc iter F T X < 2 ^ (iter F T X) := Nat.lt_two_pow_self
      _ ≤ 2 ^ (2 * iter F T X) := Nat.pow_le_pow_right (by decide) (by omega)
  have hf := Nat.testBit_lt_two_pow hlt
  unfold x at hs
  rw [hf] at hs
  simp at hs


end ZeroWall

section Chain
open Rule30Jen Rule30Prize Rule30PeriodTwo

/-! ### A language-generic mass reduction (white-wall model) -/

/-- `P b m` depends only on `b` below time `2m`. -/
def PrefixDet (P : (Nat → Bool) → Nat → Prop) : Prop :=
  ∀ b b' m, (∀ t, t < 2 * m → b t = b' t) → P b m → P b' m

/-- linear mass bound on the finite words (seeds `Y < 2^(2m)`) of the language `P`. -/
def MassBoundP (P : (Nat → Bool) → Nat → Prop) (c d : Nat) : Prop :=
  ∀ m Y : Nat, Y < 2 ^ (2 * m) → P (tr Y) m → Zc (tr Y) m ≤ c * wtH (2 * m) Y + d

theorem wtH_le_total (X m : Nat) : wtH (2 * m) X ≤ wtH X X := by
  by_cases hle : 2 * m ≤ X
  · exact wtH_mono X hle
  · have hz : ∀ i, X ≤ i → X.testBit i = false := fun i hi =>
      Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by decide) hi))
    have := wtH_stable hz (2 * m - X)
    rw [show X + (2 * m - X) = 2 * m by omega] at this
    omega

/-- Language-generic step: a linear mass bound on a prefix-determined language
inside G excludes a finite seed all of whose trace prefixes lie in the language. -/
theorem no_finite_seed_P (P : (Nat → Bool) → Nat → Prop) (hP : PrefixDet P)
    (hPG : ∀ b m, P b m → GValid b m) (c d : Nat) (hyp : MassBoundP P c d) (X : Nat) :
    ¬ ∀ m, P (tr X) m := by
  intro hX
  have hbound : ∀ m, Zc (tr X) m ≤ c * wtH X X + d := by
    intro m
    have hY : X % 2 ^ (2 * m) < 2 ^ (2 * m) := Nat.mod_lt _ (Nat.two_pow_pos _)
    have htr : ∀ t, t < 2 * m → tr (X % 2 ^ (2 * m)) t = tr X t := fun t ht => tr_mod X _ t ht
    have hPY : P (tr (X % 2 ^ (2 * m))) m := hP _ _ m (fun t ht => (htr t ht).symm) (hX m)
    have hZ : Zc (tr (X % 2 ^ (2 * m))) m = Zc (tr X) m := by
      exact Zc_congr m (fun j hj => htr _ (by omega))
    have := hyp m _ hY hPY
    rw [hZ, wtH_mod] at this
    have hW := wtH_le_total X m
    calc Zc (tr X) m ≤ c * wtH (2 * m) X + d := this
      _ ≤ c * wtH X X + d := by have := Nat.mul_le_mul_left c hW; omega
  obtain ⟨T, hT⟩ := eventually_no_zero (tr X) _ hbound
  apply not_eventually_const X (2 * T)
  intro t ht
  rcases exists_half t with ⟨j, rfl | rfl⟩
  · exact hT j (by omega)
  · exact (hPG _ (j + 1) (hX (j + 1))).2.1 j (by omega)

/-! ### Rows of the official pattern as natural numbers -/

/-- the natural number with bits `f 0, …, f (n-1)`. -/
def enc (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => (if f n then 2 ^ n else 0) + enc f n

theorem enc_lt (f : Nat → Bool) : ∀ n, enc f n < 2 ^ n
  | 0 => by simp [enc]
  | n + 1 => by
    have := enc_lt f n
    simp only [enc]
    rw [Nat.pow_succ]
    cases f n <;> simp <;> omega

theorem testBit_enc (f : Nat → Bool) : ∀ n i, (enc f n).testBit i = (decide (i < n) && f i)
  | 0, i => by simp [enc]
  | n + 1, i => by
    have ih := testBit_enc f n
    have hlt := enc_lt f n
    simp only [enc]
    rcases Nat.lt_trichotomy i n with h | h | h
    · cases hf : f n
      · rw [ite_eq_right (by simp), Nat.zero_add, ih]; simp [h, show i < n + 1 by omega]
      · rw [ite_eq_left rfl, Nat.testBit_two_pow_add_gt h, ih]
        simp [h, show i < n + 1 by omega]
    · subst h
      cases hf : f i
      · rw [ite_eq_right (by simp), Nat.zero_add, Nat.testBit_lt_two_pow hlt]; simp
      · rw [ite_eq_left rfl, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]; simp
    · have h2 : (if f n then 2 ^ n else 0) + enc f n < 2 ^ i := by
        have : 2 ^ (n + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) h
        rw [Nat.pow_succ] at this
        cases f n <;> simp <;> omega
      rw [Nat.testBit_lt_two_pow h2, decide_eq_false (show ¬ i < n + 1 by omega)]
      rfl

/-- the left half of the official row at time `t` (bit `i` = cell `-1-i`). -/
def rowNat (t : Nat) : Nat := enc (fun i => cell t (-1 - (i : Int))) (t + 1)

theorem testBit_rowNat (t i : Nat) : (rowNat t).testBit i = cell t (-1 - (i : Int)) := by
  unfold rowNat
  rw [testBit_enc]
  by_cases h : i < t + 1
  · simp [h]
  · simp only [h, decide_false, Bool.false_and]
    exact (cell_eq_false_of_lt t _ (by omega)).symm

/-- one step of the official pattern on the left half is the white-wall map `F`,
whenever a black center comes with a black column `-1`. -/
theorem rowNat_succ (t : Nat) (h : center t = true → cell t (-1) = true) :
    rowNat (t + 1) = F (rowNat t) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_F, testBit_rowNat, testBit_rowNat, testBit_rowNat]
  rw [step' t (-1 - (i : Int)) (-1 - ((i + 1 : Nat) : Int)) (-1 - (i : Int)) (-(i : Int)) (by omega)
    rfl (by omega)]
  cases i with
  | zero =>
    have hc : (cell t (-1) || cell t 0) = cell t (-1) := by
      cases h0 : cell t 0
      · simp
      · have := h h0; simp [this]
    simp [rule, hc]
  | succ j =>
    rw [testBit_rowNat]
    simp only [rule, show decide (j + 1 ≥ 1) = true by simp, Bool.true_and,
      show j + 1 - 1 = j by omega]
    rw [show (-((j + 1 : Nat) : Int)) = -1 - (j : Int) by omega]

theorem rowNat_iter (T : Nat) (h : ∀ s, center (T + s) = true → cell (T + s) (-1) = true) :
    ∀ s, iter F s (rowNat T) = rowNat (T + s) := by
  intro s
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [iter_succ, ih, ← rowNat_succ _ (h s), show T + (s + 1) = T + s + 1 by omega]

theorem tr_rowNat (T : Nat) (h : ∀ s, center (T + s) = true → cell (T + s) (-1) = true) (s : Nat) :
    tr (rowNat T) s = cell (T + s) (-1) := by
  unfold tr
  rw [rowNat_iter T h s, testBit_rowNat]; simp

/-! ### Period 2: the language-generic theorem -/

/-- alternating center from `T` (kit normal form). -/
def AltFrom (T : Nat) : Prop := ∀ k, cell (T + 2 * k) 0 = true ∧ cell (T + 2 * k + 1) 0 = false

theorem alt_guard {T : Nat} (hT : AltFrom T) (k0 : Nat) :
    ∀ s, center (T + 2 * k0 + 1 + s) = true → cell (T + 2 * k0 + 1 + s) (-1) = true := by
  intro s hs
  rcases exists_half s with ⟨j, rfl | rfl⟩
  · exfalso
    have := (hT (k0 + j)).2
    unfold center at hs
    rw [show T + 2 * k0 + 1 + 2 * j = T + 2 * (k0 + j) + 1 by omega] at hs
    rw [this] at hs; exact absurd hs (by simp)
  · rw [show T + 2 * k0 + 1 + (2 * j + 1) = T + 2 * (k0 + j + 1) by omega]
    exact m1_even hT _

theorem alt_guard0 {T : Nat} (hT : AltFrom T) :
    ∀ s, center (T + s) = true → cell (T + s) (-1) = true := by
  intro s hs
  rcases exists_half s with ⟨j, rfl | rfl⟩
  · exact m1_even hT j
  · exfalso
    have := (hT j).2
    unfold center at hs
    rw [show T + (2 * j + 1) = T + 2 * j + 1 by omega, this] at hs
    exact absurd hs (by simp)

/-- Language-generic theorem (period 2).  For any prefix-determined language `P ⊆ G` containing
the actual left traces read from any late white time of column `-1`, a linear mass bound on
the finite words of `P` excludes an eventual period 2 of the official center column. -/
theorem not_eventually_period_two_of_lang (P : (Nat → Bool) → Nat → Prop) (hP : PrefixDet P)
    (hPG : ∀ b m, P b m → GValid b m) (c d : Nat) (hyp : MassBoundP P c d)
    (hlang : ∀ T, AltFrom T → ∃ K, ∀ k0, K ≤ k0 → cell (T + 2 * k0 + 1) (-1) = false →
      ∀ m, P (fun s => cell (T + 2 * k0 + 1 + s) (-1)) m) :
    ¬ ∃ T0, ∀ t, T0 ≤ t → center (t + 2) = center t := by
  rintro ⟨T0, hp⟩
  obtain ⟨T, hT⟩ := normalize hp
  obtain ⟨K, hK⟩ := hlang T hT
  -- a white of column -1 at an odd offset beyond K
  have hwhite : ∃ k0, K ≤ k0 ∧ cell (T + 2 * k0 + 1) (-1) = false := by
    refine Classical.byContradiction fun hno' => ?_
    have hno : ∀ k0, K ≤ k0 → cell (T + 2 * k0 + 1) (-1) ≠ false :=
      fun k0 hk hc => hno' ⟨k0, hk, hc⟩
    apply not_eventually_const (rowNat T) (T + 2 * K)
    intro t ht
    rw [tr_rowNat T (alt_guard0 hT) t]
    rcases exists_half t with ⟨j, rfl | rfl⟩
    · exact m1_even hT j
    · rw [show T + (2 * j + 1) = T + 2 * j + 1 by omega]
      cases hc : cell (T + 2 * j + 1) (-1)
      · exact absurd hc (hno j (by omega))
      · rfl
  obtain ⟨k0, hk0, hw⟩ := hwhite
  apply no_finite_seed_P P hP hPG c d hyp (rowNat (T + 2 * k0 + 1))
  intro m
  have hfun : tr (rowNat (T + 2 * k0 + 1)) = fun s => cell (T + 2 * k0 + 1 + s) (-1) :=
    funext (tr_rowNat _ (alt_guard hT k0))
  rw [hfun]
  exact hK k0 hk0 hw m

/-! ### The instance P = G -/

theorem prefixDet_G : PrefixDet GValid := by
  intro b b' m h ⟨h0, h1, h2⟩
  refine ⟨fun hm => by rw [← h 0 (by omega)]; exact h0 hm, fun j hj => ?_, fun j hj => ?_⟩
  · rw [← h _ (by omega)]; exact h1 j hj
  · rw [← h _ (by omega), ← h _ (by omega)]; exact h2 j hj

theorem lang_G : ∀ T, AltFrom T → ∃ K, ∀ k0, K ≤ k0 → cell (T + 2 * k0 + 1) (-1) = false →
    ∀ m, GValid (fun s => cell (T + 2 * k0 + 1 + s) (-1)) m := by
  intro T hT
  refine ⟨0, fun k0 _ hw m => ⟨fun _ => by simpa using hw, fun j _ => ?_, fun j _ => ?_⟩⟩
  · show cell (T + 2 * k0 + 1 + (2 * j + 1)) (-1) = true
    rw [show T + 2 * k0 + 1 + (2 * j + 1) = T + 2 * (k0 + j + 1) by omega]
    exact m1_even hT _
  · show (cell (T + 2 * k0 + 1 + 2 * j) (-1) || cell (T + 2 * k0 + 1 + (2 * j + 2)) (-1)) = true
    rw [show T + 2 * k0 + 1 + 2 * j = T + 2 * (k0 + j) + 1 by omega,
      show T + 2 * k0 + 1 + (2 * j + 2) = T + 2 * (k0 + j) + 3 by omega]
    cases hc : cell (T + 2 * (k0 + j) + 1) (-1)
    · rw [golden hT _ hc]; rfl
    · rfl

/-- Period 2 from a linear mass bound on the finite G words. -/
theorem not_eventually_period_two_of_massbound_G (c d : Nat) (hyp : MassBound c d) :
    ¬ ∃ T0, ∀ t, T0 ≤ t → center (t + 2) = center t :=
  not_eventually_period_two_of_lang GValid prefixDet_G (fun _ _ h => h) c d hyp lang_G

end Chain

/-- **The width-13 strip certificate.** The check `certOK` of
`Rule30Certificates.PeriodTwoWidth13` holds at all `16384` nodes of the strip (kernel check). -/
theorem certOK_true : certOK = true := certOK_kernel

section Strip
open Rule30Jen Rule30Prize Rule30PeriodTwo

/-! ## Facts extracted from the kernel check -/

theorem nodeOK_of_lt {u : Nat} (hu : u < NN) : nodeOK u = true := by
  have h := certOK_true
  unfold certOK at h
  exact List.all_eq_true.1 h u (List.mem_range.2 hu)

theorem rk_lt (v : Nat) : rk v < 16384 := Nat.mod_lt _ (by decide)

theorem succN_lt (v f : Nat) : succN v f < NN := by
  unfold succN NN
  have h1 : (((v % M ||| (f <<< J)) <<< 1 ||| v / M) ^^^ ((v % M ||| (f <<< J)) ||| ((v % M ||| (f <<< J)) >>> 1))) % M < M :=
    Nat.mod_lt _ (Nat.two_pow_pos J)
  have h2 : M * (1 - v / M) ≤ M := by
    rcases Nat.eq_zero_or_pos (1 - v / M) with h | h
    · rw [h]; simp
    · have h1 : 1 - v / M = 1 := by generalize v / M = c at h ⊢; omega
      rw [h1, Nat.mul_one]
      exact Nat.le_refl _
  generalize M * (1 - v / M) = A at h2 ⊢
  omega

theorem edge_facts {u : Nat} (hu : u < NN) (f : Nat) (hf : f = 0 ∨ f = 1) :
    rk u ≤ rk (succN u f) ∧ (rk u = rk (succN u f) → md u ≠ 0 ∧ md (succN u f) = md u ∧
      levelOK (md u) (kick (succN u f)) (lab u) (lab (succN u f)) = true) := by
  have h := nodeOK_of_lt hu
  simp only [nodeOK, nodeOK', Bool.and_eq_true] at h
  obtain ⟨⟨_, h0⟩, h1⟩ := h
  have he : edgeOK' (rk u) (md u) (lab u) (succN u f) = true := by
    rcases hf with rfl | rfl
    · exact h0
    · exact h1
  unfold edgeOK' at he
  simp only [Bool.and_eq_true, Nat.ble_eq, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at he
  obtain ⟨hle, hr⟩ := he
  refine ⟨hle, fun heq => ?_⟩
  rcases hr with hr | ⟨⟨hm, hmw⟩, hl⟩
  · exact absurd heq hr
  · exact ⟨hm, hmw, hl⟩

theorem lab0 {u : Nat} (hu : u < NN) (hm : md u ≠ 0) : (lab u).testBit 0 = true := by
  have h := nodeOK_of_lt hu
  simp only [nodeOK, nodeOK', Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  rcases h.1.1 with h | h
  · exact absurd h hm
  · exact h

theorem levelOK_spec {m : Nat} {k : Bool} {Lu Lw : Nat} (h : levelOK m k Lu Lw = true) {q : Nat}
    (hq : q < 60) (hb : Lu.testBit q = true) : ∃ q', delta m q k = some q' ∧ Lw.testBit q' = true := by
  have h' := List.all_eq_true.1 h q (List.mem_range.2 hq)
  simp only [hb, Bool.not_true, Bool.false_or] at h'
  unfold stOK at h'
  cases hd : delta m q k with
  | none => rw [hd] at h'; exact absurd h' (by simp)
  | some q' => rw [hd] at h'; exact ⟨q', rfl, h'⟩

theorem delta_lt (m q : Nat) (k : Bool) (q' : Nat) (h : delta m q k = some q') : q' < 60 := by
  unfold delta at h
  repeat' split at h
  all_goals first
    | (simp only [reduceCtorEq] at h)
    | (simp only [Option.some.injEq] at h; omega)

/-! ## Every infinite strip path is eventually accepted by one level's automaton -/

/-- the gap automaton in mode `m`, started in `q0` at time `0`, fed `k 1, k 2, …`. -/
def run (m : Nat) (k : Nat → Bool) (q0 : Nat) : Nat → Option Nat
  | 0 => some q0
  | j + 1 => (run m k q0 j).bind (fun q => delta m q (k (j + 1)))

theorem run_succ (m : Nat) (k : Nat → Bool) (q0 j : Nat) :
    run m k q0 (j + 1) = (run m k q0 j).bind (fun q => delta m q (k (j + 1))) := rfl

/-- A choice of the states of a run that never fails. -/
theorem choose_states {R : Nat → Option Nat} (h : ∀ j, ∃ q, R j = some q ∧ q < 60) :
    ∃ qs : Nat → Nat, ∀ j, R j = some (qs j) ∧ qs j < 60 :=
  ⟨fun j => (h j).choose, fun j => (h j).choose_spec⟩

theorem eventually_const_of_mono (r : Nat → Nat) (B : Nat) (hB : ∀ n, r n < B)
    (hm : ∀ n, r n ≤ r (n + 1)) : ∃ n0, ∀ n, n0 ≤ n → r n = r n0 := by
  have mono : ∀ a b, a ≤ b → r a ≤ r b := by
    intro a b hab
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
    induction d with
    | zero => exact Nat.le_refl _
    | succ d ih => exact Nat.le_trans (ih (by omega)) (hm (a + d))
  refine Classical.byContradiction fun hne0 => ?_
  have hne : ∀ n0, ∃ n, n0 ≤ n ∧ r n ≠ r n0 := fun n0 =>
    Classical.byContradiction fun h => hne0 ⟨n0, fun n hn =>
      Classical.byContradiction fun h' => h ⟨n, hn, h'⟩⟩
  have key : ∀ k, ∃ n, k ≤ r n := by
    intro k
    induction k with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ k ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨n', hn', hne'⟩ := hne n
      have := mono _ _ hn'
      exact ⟨n', by omega⟩
  obtain ⟨n, hn⟩ := key B
  have := hB n
  omega

theorem path_run (π : Nat → Nat) (h0 : π 0 < NN)
    (hs : ∀ n, ∃ b : Bool, π (n + 1) = succN (π n) (if b then 1 else 0)) :
    ∃ n0 m, m ≠ 0 ∧ ∀ j, ∃ q, run m (fun j => kick (π (n0 + j))) 0 j = some q ∧ q < 60 := by
  have hlt : ∀ n, π n < NN := by
    intro n
    induction n with
    | zero => exact h0
    | succ n _ => obtain ⟨b, hb⟩ := hs n; rw [hb]; exact succN_lt _ _
  have hedge : ∀ n, rk (π n) ≤ rk (π (n + 1)) ∧ (rk (π n) = rk (π (n + 1)) → md (π n) ≠ 0 ∧
      md (π (n + 1)) = md (π n) ∧
      levelOK (md (π n)) (kick (π (n + 1))) (lab (π n)) (lab (π (n + 1))) = true) := by
    intro n
    obtain ⟨b, hb⟩ := hs n
    rw [hb]
    exact edge_facts (hlt n) _ (by cases b <;> simp)
  obtain ⟨n0, hn0⟩ := eventually_const_of_mono (fun n => rk (π n)) 16384 (fun n => rk_lt _)
    (fun n => (hedge n).1)
  have hsame : ∀ j, rk (π (n0 + j)) = rk (π (n0 + j + 1)) := by
    intro j
    have a : rk (π (n0 + j)) = rk (π n0) := hn0 (n0 + j) (by omega)
    have b : rk (π (n0 + j + 1)) = rk (π n0) := hn0 (n0 + j + 1) (by omega)
    rw [a, b]
  have hmd : ∀ j, md (π (n0 + j)) = md (π n0) := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [← Nat.add_assoc, ((hedge (n0 + j)).2 (hsame j)).2.1, ih]
  have hm0 : md (π n0) ≠ 0 := by
    have := ((hedge (n0 + 0)).2 (hsame 0)).1
    simpa using this
  refine ⟨n0, md (π n0), hm0, ?_⟩
  have inv : ∀ j, ∃ q, run (md (π n0)) (fun j => kick (π (n0 + j))) 0 j = some q ∧ q < 60 ∧
      (lab (π (n0 + j))).testBit q = true := by
    intro j
    induction j with
    | zero => exact ⟨0, rfl, by decide, by simpa using lab0 (hlt n0) hm0⟩
    | succ j ih =>
      obtain ⟨q, hq, hq60, hqb⟩ := ih
      obtain ⟨_, _, hl⟩ := (hedge (n0 + j)).2 (hsame j)
      rw [hmd j] at hl
      obtain ⟨q', hd, hb'⟩ := levelOK_spec hl hq60 hqb
      refine ⟨q', ?_, delta_lt _ _ _ _ hd, by rw [← Nat.add_assoc]; exact hb'⟩
      rw [run_succ, hq]
      simp only [Option.bind_some]
      rw [← Nat.add_assoc]
      exact hd
  intro j
  obtain ⟨q, h1, h2, _⟩ := inv j
  exact ⟨q, h1, h2⟩

/-! ## Finite facts about the gap automaton (decided) -/

theorem delta_mode (m q : Nat) (k : Bool) (hm : m ≠ 1) : delta m q k = delta 2 q k := by
  have h1 : (m == 1) = false := by simpa using hm
  simp only [delta, gapOK, pairOK, h1]
  rfl

/-- The s-field of a state: steps since the last kick (or since entering). -/
def sf (q : Nat) : Nat := if q < 10 then q else (q - 10) % 10

/-- one-step facts for the pure-4 automaton. -/
theorem p4_facts : ∀ q, q < 60 →
    (∀ q', delta 2 q false = some q' → sf q' = sf q + 1 ∧ (q' < 10 ↔ q < 10)) ∧
    (∀ q', delta 2 q true = some q' → 10 ≤ q' ∧ sf q' = 0 ∧ (q < 10 ∨ sf q = 7)) ∧
    (10 ≤ q → 8 ≤ sf q → delta 2 q true = none) ∧
    (10 ≤ q → sf q = 9 → delta 2 q false = none) := by
  decide

/-- simulation fact: forgetting the previous gap only makes the E2 automaton more permissive. -/
def simB (q : Nat) (k : Bool) : Bool :=
  match delta 1 q k with
  | none => true
  | some q' => (delta 1 (10 + (q - 10) % 10) k == some q') ||
      (decide (10 ≤ q') && decide (q' < 60) && delta 1 (10 + (q - 10) % 10) k == some (10 + (q' - 10) % 10))

theorem simB_true : ∀ q, q < 60 → 10 ≤ q → ∀ k : Bool, simB q k = true := by decide

theorem sim_fact (q : Nat) (hq : q < 60) (h10 : 10 ≤ q) (k : Bool) {q' : Nat} (hd : delta 1 q k = some q') :
    delta 1 (10 + (q - 10) % 10) k = some q' ∨
      (10 ≤ q' ∧ q' < 60 ∧ delta 1 (10 + (q - 10) % 10) k = some (10 + (q' - 10) % 10)) := by
  have h := simB_true q hq h10 k
  unfold simB at h
  rw [hd] at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  rcases h with h | ⟨⟨a, b⟩, c⟩
  · exact Or.inl h
  · exact Or.inr ⟨a, b, c⟩

def krB (q : Nat) : Bool :=
  match delta 1 q true with
  | none => true
  | some q' => decide (10 ≤ q') && (q' - 10) % 10 == 0

theorem krB_true : ∀ q, q < 60 → krB q = true := by decide

theorem kick_result (q : Nat) (hq : q < 60) (q' : Nat) (h : delta 1 q true = some q') :
    10 ≤ q' ∧ (q' - 10) % 10 = 0 := by
  have hk := krB_true q hq
  unfold krB at hk
  rw [h] at hk
  simpa using hk

def Sim (q0 q : Nat) : Prop := q0 = q ∨ (10 ≤ q ∧ q < 60 ∧ q0 = 10 + (q - 10) % 10)

theorem sim_step {q0 q : Nat} (hs : Sim q0 q) (k : Bool) {q' : Nat} (hd : delta 1 q k = some q')
    (hq : q < 60) : ∃ q0', delta 1 q0 k = some q0' ∧ Sim q0' q' := by
  rcases hs with rfl | ⟨h10, h60, rfl⟩
  · exact ⟨q', hd, Or.inl rfl⟩
  · rcases sim_fact q h60 h10 k hd with h | ⟨a, b, c⟩
    · exact ⟨q', h, Or.inl rfl⟩
    · exact ⟨_, c, Or.inr ⟨a, b, rfl⟩⟩

/-! ## Pure-4 level: kicks are 8-periodic -/

theorem p4_periodic (m : Nat) (hm : m ≠ 1) (k : Nat → Bool)
    (hrun : ∀ j, ∃ q, run m k 0 j = some q ∧ q < 60) :
    ∃ j1, ∀ j, j1 ≤ j → k (j + 8) = k j := by
  have hd : ∀ q b, delta m q b = delta 2 q b := fun q b => delta_mode m q b hm
  -- states
  obtain ⟨qs, hqs⟩ := choose_states hrun
  have hq60 := fun j => (hqs j).2
  replace hqs := fun j => (hqs j).1
  have hstep : ∀ j, delta 2 (qs j) (k (j + 1)) = some (qs (j + 1)) := by
    intro j
    have := hqs (j + 1)
    rw [run_succ, hqs j] at this
    simpa [hd] using this
  -- Claim A: a state ≥ 10 is reached by step 10
  have hA : ∃ j1, 10 ≤ qs j1 := by
    refine Classical.byContradiction fun hno' => ?_
    have hno : ∀ j, qs j < 10 := fun j => Nat.lt_of_not_le fun h => hno' ⟨j, h⟩
    have : ∀ j, qs j = j := by
      intro j
      induction j with
      | zero =>
        have := hqs 0
        simp only [run, Option.some.injEq] at this
        exact this.symm
      | succ j ih =>
        have f := p4_facts (qs j) (hq60 j)
        cases hk : k (j + 1)
        · have := (f.1 _ (by rw [← hk]; exact hstep j)).1
          have h1 := hno j; have h2 := hno (j + 1)
          simp only [sf, show qs j < 10 from h1, show qs (j + 1) < 10 from h2, ite_true] at this
          omega
        · have := (f.2.1 _ (by rw [← hk]; exact hstep j)).1
          have := hno (j + 1)
          omega
    have hq10 := hno 10
    rw [this 10] at hq10
    omega
  obtain ⟨j1, hj1⟩ := hA
  -- Claim B: stays ≥ 10
  have hB : ∀ i, 10 ≤ qs (j1 + i) := by
    intro i
    induction i with
    | zero => exact hj1
    | succ i ih =>
      have f := p4_facts (qs (j1 + i)) (hq60 _)
      have e := hstep (j1 + i)
      rw [← Nat.add_assoc]
      cases hk : k (j1 + i + 1)
      · rw [hk] at e
        have := (f.1 _ e).2
        refine Classical.byContradiction fun hc => ?_
        have : qs (j1 + i + 1) < 10 := by omega
        have := (f.1 _ e).2.1 this
        omega
      · rw [hk] at e
        exact (f.2.1 _ e).1
  -- Claim C: sf ≤ 7 from j1 on
  have hC : ∀ i, sf (qs (j1 + i)) ≤ 7 := by
    intro i
    have hb := hB i
    have h1 := hB (i + 1)
    refine Classical.byContradiction fun hc' => ?_
    have hc : 7 < sf (qs (j1 + i)) := Nat.lt_of_not_le hc'
    have f := p4_facts (qs (j1 + i)) (hq60 _)
    have e1 := hstep (j1 + i)
    cases hk : k (j1 + i + 1)
    · rw [hk] at e1
      have hs1 := (f.1 _ e1).1
      -- sf (qs (j1+i)) ≥ 8 so sf of next ≥ 9; but sf ≤ 9 for states < 60 with q ≥ 10
      have : sf (qs (j1 + i + 1)) ≤ 9 := by
        have := hB (i + 1); unfold sf; rw [ite_eq_right (by rw [← Nat.add_assoc] at this; omega)]; omega
      have h9 : sf (qs (j1 + i + 1)) = 9 := by omega
      have f2 := p4_facts (qs (j1 + i + 1)) (hq60 _)
      have e2 := hstep (j1 + i + 1)
      have h10 : 10 ≤ qs (j1 + i + 1) := by rw [← Nat.add_assoc] at h1; exact h1
      cases hk2 : k (j1 + i + 1 + 1)
      · rw [hk2, f2.2.2.2 h10 h9] at e2; exact absurd e2 (by simp)
      · rw [hk2, f2.2.2.1 h10 (by omega)] at e2; exact absurd e2 (by simp)
    · rw [hk, (f.2.2.1 hb (by omega))] at e1; exact absurd e1 (by simp)
  -- Claim D/E: kick iff sf = 7, and sf advances mod 8
  have hD : ∀ i, (k (j1 + i + 1) = true ↔ sf (qs (j1 + i)) = 7) ∧
      sf (qs (j1 + i + 1)) = (sf (qs (j1 + i)) + 1) % 8 := by
    intro i
    have f := p4_facts (qs (j1 + i)) (hq60 _)
    have e := hstep (j1 + i)
    have hc := hC i
    have hc1 := hC (i + 1)
    rw [← Nat.add_assoc] at hc1
    cases hk : k (j1 + i + 1)
    · rw [hk] at e
      have := (f.1 _ e).1
      refine ⟨by simp; omega, by omega⟩
    · rw [hk] at e
      have := f.2.1 _ e
      have h10 := hB i
      rcases this.2.2 with h | h
      · omega
      · exact ⟨by simp [h], by omega⟩
  have hsf : ∀ i, sf (qs (j1 + i)) = (sf (qs j1) + i) % 8 := by
    intro i
    induction i with
    | zero => have := hC 0; simp at this ⊢; omega
    | succ i ih => rw [← Nat.add_assoc, (hD i).2, ih]; omega
  refine ⟨j1 + 1, fun j hj => ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, j = j1 + i + 1 := ⟨j - j1 - 1, by omega⟩
  have a := (hD i).1
  have b := (hD (i + 8)).1
  rw [show j1 + (i + 8) + 1 = j1 + i + 1 + 8 by omega, hsf (i + 8)] at b
  rw [hsf i] at a
  rw [show (sf (qs j1) + (i + 8)) % 8 = (sf (qs j1) + i) % 8 by omega] at b
  cases h1 : k (j1 + i + 1 + 8) <;> cases h2 : k (j1 + i + 1) <;> simp_all

/-! ## A finite left seed never has an eventually periodic trace -/

theorem F_top (Y k : Nat) (hY : Y < 2 ^ (k + 1)) (hb : Y.testBit k = true) :
    F Y < 2 ^ (k + 2) ∧ (F Y).testBit (k + 1) = true := by
  have hz : ∀ i, k + 1 ≤ i → Y.testBit i = false := fun i hi =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hY (Nat.pow_le_pow_right (by decide) hi))
  constructor
  · apply Nat.lt_pow_two_of_testBit
    intro i hi
    rw [testBit_F, hz (i + 1) (by omega), hz i (by omega)]
    have : decide (i ≥ 1) = true := by simp; omega
    rw [this, hz (i - 1) (by omega)]; rfl
  · rw [testBit_F, hz (k + 1 + 1) (by omega), hz (k + 1) (by omega)]
    simp [hb]

theorem iter_top (X : Nat) (hX : X ≠ 0) : ∀ t, iter F t X < 2 ^ (Nat.log2 X + t + 1) ∧
    (iter F t X).testBit (Nat.log2 X + t) = true := by
  intro t
  induction t with
  | zero =>
    exact ⟨Nat.lt_log2_self (n := X), Nat.testBit_log2 hX⟩
  | succ t ih =>
    rw [iter_succ]
    have := F_top _ _ ih.1 ih.2
    exact ⟨by simpa [Nat.add_assoc] using this.1, by simpa [Nat.add_assoc] using this.2⟩

theorem col_periodic (X T p : Nat) (h : ∀ t, T ≤ t → tr X (t + p) = tr X t) :
    ∀ j t, T ≤ t → x X j (t + p) = x X j t := by
  intro j
  induction j using Nat.strongRecOn with
  | ind j ih =>
    intro t ht
    match j, ih with
    | 0, _ => exact h t ht
    | 1, _ =>
      rw [x_rec0, x_rec0, show t + p + 1 = (t + 1) + p by omega]
      have a := h (t + 1) (by omega)
      have b := h t ht
      unfold tr at a b; unfold x
      rw [a, b]
    | j + 2, ih =>
      rw [x_rec, x_rec, show t + p + 1 = (t + 1) + p by omega,
        ih (j + 1) (by omega) (t + 1) (by omega), ih (j + 1) (by omega) t ht, ih j (by omega) t ht]

/-- **Jen in the half-line.** The trace of a nonzero finite left half `X` beside the white wall is
not eventually periodic: an eventual period `p` of column `-1` spreads to every column
(`col_periodic`), but the highest black cell moves one column left at each step (`iter_top`).
Compare `Rule30DrivenLeft.col_neg_one_not_periodic`. -/
theorem tr_not_eventually_periodic (X : Nat) (hX : X ≠ 0) (T p : Nat) (hp : 0 < p) :
    ¬ ∀ t, T ≤ t → tr X (t + p) = tr X t := by
  intro h
  have hc := col_periodic X T p h (Nat.log2 X + T + p) T (Nat.le_refl _)
  have a := (iter_top X hX (T + p)).2
  have b : (iter F T X).testBit (Nat.log2 X + T + p) = false :=
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (iter_top X hX T).1
      (Nat.pow_le_pow_right (by decide) (by omega)))
  unfold x at hc
  rw [show Nat.log2 X + (T + p) = Nat.log2 X + T + p by omega] at a
  rw [a, b] at hc
  exact absurd hc (by simp)

/-! ## Bridge: the right half of the official orbit is a strip path -/

theorem yb_lt (x f : Nat) {k : Nat} (hk : k < J) : (x ||| f <<< J).testBit k = x.testBit k := by
  rw [Nat.testBit_or, Nat.testBit_shiftLeft]
  have : ¬ (k ≥ J) := by omega
  simp [this]

theorem yb_J (x f : Nat) (hx : x < M) : (x ||| f <<< J).testBit J = f.testBit 0 := by
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_lt_two_pow hx]
  simp

theorem step_bit (x ph f : Nat) (hx : x < M) (hph : ph ≤ 1) (i : Nat) (hi : i < J) :
    ((((x ||| f <<< J) <<< 1) ||| ph) ^^^ ((x ||| f <<< J) ||| ((x ||| f <<< J) >>> 1))).testBit i =
    ((if i = 0 then ph.testBit 0 else x.testBit (i - 1)) ^^
      (x.testBit i || (if i + 1 < J then x.testBit (i + 1) else f.testBit 0))) := by
  rw [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    yb_lt x f hi, show 1 + i = i + 1 by omega]
  rcases Nat.eq_zero_or_pos i with rfl | hp
  · rw [yb_lt x f (show 0 + 1 < J by decide), ite_eq_left rfl, ite_eq_left (show 0 + 1 < J by decide)]
    simp
  · have hph' : ph.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_le_of_lt hph (by
        calc 1 < 2 ^ 1 := by decide
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hp))
    rw [hph', ite_eq_right (show i ≠ 0 by omega), yb_lt x f (show i - 1 < J by omega)]
    have h1 : decide (i ≥ 1) = true := by simp; omega
    rw [h1, Bool.true_and, Bool.or_false]
    by_cases h3 : i + 1 < J
    · rw [yb_lt x f h3, ite_eq_left h3]
    · rw [show i + 1 = J by omega, yb_J x f hx, ite_eq_right (by omega)]

/-- columns `1..J` of the official row at time `t`. -/
def stripX (t : Nat) : Nat := enc (fun i => cell t ((i : Int) + 1)) J
def node (t : Nat) : Nat := stripX t + M * (if center t then 1 else 0)
theorem stripX_lt (t : Nat) : stripX t < M := enc_lt _ _
theorem testBit_stripX (t i : Nat) : (stripX t).testBit i = (decide (i < J) && cell t ((i : Int) + 1)) :=
  testBit_enc _ _ _

theorem kick_node (t : Nat) : kick (node t) = (!center t && cell t 1) := by
  have h0 : (stripX t).testBit 0 = cell t 1 := by rw [testBit_stripX]; simp [J]
  unfold kick
  cases hc : center t
  · have e : node t = stripX t := by simp [node, hc]
    rw [e, decide_eq_true (stripX_lt t), ← h0, Nat.testBit_zero, Bool.eq_iff_iff]
    simp
  · have : ¬ node t < M := by unfold node; rw [hc]; simp
    simp [this]

theorem node_div (t : Nat) : node t / M = (if center t then 1 else 0) := by
  unfold node
  have := stripX_lt t
  have hM : 0 < M := Nat.two_pow_pos J
  rw [Nat.add_mul_div_left _ _ hM, Nat.div_eq_of_lt this]; simp

theorem node_mod (t : Nat) : node t % M = stripX t := by
  unfold node
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (stripX_lt t)]

theorem node_succ (t : Nat) (hc : center (t + 1) = !center t) :
    node (t + 1) = succN (node t) (if cell t ((J : Int) + 1) then 1 else 0) := by
  unfold succN
  rw [node_div, node_mod]
  have hph : (if center (t + 1) then 1 else 0) = 1 - (if center t then 1 else 0) := by
    rw [hc]; cases center t <;> rfl
  unfold node
  rw [hph]
  congr 1
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_stripX, show M = 2 ^ J from rfl, Nat.testBit_mod_two_pow]
  by_cases hi : i < J
  · rw [step_bit _ _ _ (stripX_lt t) (by split <;> omega) i hi]
    simp only [hi, decide_true, Bool.true_and]
    rw [step' t ((i : Int) + 1) (i : Int) ((i : Int) + 1) ((i : Int) + 2) (by omega) rfl (by omega)]
    unfold rule
    simp only [testBit_stripX, decide_eq_true hi, Bool.true_and]
    rcases Nat.eq_zero_or_pos i with rfl | hp
    · rw [ite_eq_left rfl, ite_eq_left (show 0 + 1 < J by decide), decide_eq_true (show 0 + 1 < J by decide), Bool.true_and]
      have e0 : ((if center t then 1 else 0 : Nat)).testBit 0 = cell t ((0 : Nat) : Int) := by
        show _ = cell t 0
        unfold center; cases cell t 0 <;> rfl
      rw [e0]; congr 3
    · rw [ite_eq_right (show i ≠ 0 by omega), decide_eq_true (show i - 1 < J by omega), Bool.true_and,
        show ((i - 1 : Nat) : Int) + 1 = (i : Int) by omega]
      by_cases h3 : i + 1 < J
      · rw [ite_eq_left h3, decide_eq_true h3, Bool.true_and, show ((i + 1 : Nat) : Int) + 1 = (i : Int) + 2 by omega]
      · rw [ite_eq_right h3]
        have hJ1 : i + 1 = J := by omega
        have h12 : (i : Int) + 2 = (J : Int) + 1 := by omega
        rw [h12]
        cases cell t ((J : Int) + 1) <;> rfl
  · simp [hi]

theorem node_lt (t : Nat) : node t < NN := by
  have := stripX_lt t
  unfold node NN
  split <;> omega

/-! ## Assembly -/

section
variable {T : Nat} (hT : AltFrom T)
include hT

theorem center_flip (n : Nat) : center (T + n + 1) = !center (T + n) := by
  rcases exists_half n with ⟨k, rfl | rfl⟩
  · have := hT k
    unfold center
    rw [this.1, show T + 2 * k + 1 = T + 2 * k + 1 from rfl, this.2]; rfl
  · have a := (hT k).2
    have b := (hT (k + 1)).1
    unfold center
    rw [show T + (2 * k + 1) = T + 2 * k + 1 by omega, a,
      show T + 2 * k + 1 + 1 = T + 2 * (k + 1) by omega, b]; rfl

/-- column −1 of the official orbit, from `T` on, is the negated kick bit of the strip node. -/
theorem cell_m1_eq (n : Nat) : cell (T + n) (-1) = !kick (node (T + n)) := by
  rw [kick_node]
  rcases exists_half n with ⟨k, rfl | rfl⟩
  · rw [m1_even hT k]
    have : center (T + 2 * k) = true := (hT k).1
    rw [this]; rfl
  · rw [show T + (2 * k + 1) = T + 2 * k + 1 by omega]
    have : center (T + 2 * k + 1) = false := (hT k).2
    rw [this, p1_odd hT k]
    simp

theorem kick_parity (n : Nat) (h : kick (node (T + n)) = true) : n % 2 = 1 := by
  rcases exists_half n with ⟨k, rfl | rfl⟩
  · rw [kick_node, show center (T + 2 * k) = true from (hT k).1] at h
    simp at h
  · omega

theorem strip_path : ∀ n, ∃ b : Bool, node (T + n + 1) = succN (node (T + n)) (if b then 1 else 0) :=
  fun n => ⟨_, node_succ (T + n) (center_flip hT n)⟩

/-- the pure-4 level is impossible: it makes the finite left half's trace periodic. -/
theorem not_pure4 (n0 m : Nat) (hm : m ≠ 1)
    (hrun : ∀ j, ∃ q, run m (fun j => kick (node (T + (n0 + j)))) 0 j = some q ∧ q < 60) : False := by
  obtain ⟨j1, hj1⟩ := p4_periodic m hm _ hrun
  have htr : ∀ s, tr (rowNat T) s = cell (T + s) (-1) := tr_rowNat T (alt_guard0 hT)
  have hX : rowNat T ≠ 0 := by
    intro h0
    have := htr 0
    rw [h0] at this
    unfold tr at this
    simp [iter] at this
    have m := m1_even hT 0
    simp at m
    rw [m] at this; exact absurd this (by simp)
  apply tr_not_eventually_periodic (rowNat T) hX (n0 + j1) 8 (by decide)
  intro t ht
  rw [htr, htr, cell_m1_eq hT, cell_m1_eq hT]
  have := hj1 (t - n0) (by omega)
  rw [show n0 + (t - n0 + 8) = t + 8 by omega, show n0 + (t - n0) = t by omega] at this
  rw [this]

end

/-! ### The left language G ∩ E2 -/

/-- E2 on a prefix of `m` pairs: the E2 gap automaton, started at the zero at time 0,
does not fail on the even-time zeros of `b` before time `2m`. -/
def E2Run (b : Nat → Bool) (m : Nat) : Prop :=
  ∀ j, j < 2 * m → (run 1 (fun s => s % 2 == 0 && !b s) 10 j).isSome = true

def GE2 (b : Nat → Bool) (m : Nat) : Prop := GValid b m ∧ E2Run b m

theorem run_congr (mm : Nat) (k k' : Nat → Bool) (q0 : Nat) :
    ∀ j, (∀ i, i ≤ j → k i = k' i) → run mm k q0 j = run mm k' q0 j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro h
    rw [run_succ, run_succ, ih (fun i hi => h i (by omega)), h (j + 1) (Nat.le_refl _)]

theorem prefixDet_GE2 : PrefixDet GE2 := by
  intro b b' m h ⟨hg, he⟩
  refine ⟨prefixDet_G b b' m h hg, fun j hj => ?_⟩
  rw [run_congr 1 _ (fun s => s % 2 == 0 && !b s) 10 j (fun i hi => by rw [h i (by omega)])]
  exact he j hj

/-- **The left language.** If the center column alternates black, white from `T` (`AltFrom T`),
then from some `K` on, the trace of column `-1` read from any white time `T + 2 k0 + 1` of column
`-1` (`k0 ≥ K`) lies in `GE2` for every length. No hypothesis on the right half: the strip of
columns `1..13` with column `14` free is a path of the certificate `certOK_true`, so it is
eventually inside one recurrent level, and the pure-gap-4 level is excluded by
`tr_not_eventually_periodic`; the E2 automaton read from a kick is then simulated on the left trace,
because column `-1` is the complement of the kicks at the white times. -/
theorem lang_GE2 : ∀ T, AltFrom T → ∃ K, ∀ k0, K ≤ k0 → cell (T + 2 * k0 + 1) (-1) = false →
    ∀ m, GE2 (fun s => cell (T + 2 * k0 + 1 + s) (-1)) m := by
  intro T hT
  obtain ⟨K0, hG⟩ := lang_G T hT
  have hp := path_run (fun n => node (T + n)) (node_lt _) (fun n => by
    simpa [Nat.add_assoc] using strip_path hT n)
  obtain ⟨n0, mm, hmm, hrun⟩ := hp
  have h1 : mm = 1 := Classical.byContradiction fun h1 => not_pure4 hT n0 mm h1 hrun
  subst h1
  refine ⟨K0 + n0, fun k0 hk0 hw m => ⟨hG k0 (by omega) hw m, ?_⟩⟩
  -- the right run at index j* = 2k0+1-n0 ≥ 1 is in a kick-result state
  obtain ⟨js, hjs⟩ : ∃ js, js = 2 * k0 + 1 - n0 := ⟨_, rfl⟩
  have hjs1 : 1 ≤ js := by omega
  obtain ⟨qs, hqs⟩ := choose_states hrun
  have hq60 := fun j => (hqs j).2
  replace hqs := fun j => (hqs j).1
  have hkick : kick (node (T + (n0 + js))) = true := by
    have e := cell_m1_eq hT (2 * k0 + 1)
    rw [show T + (2 * k0 + 1) = T + 2 * k0 + 1 by omega, hw] at e
    rw [show n0 + js = 2 * k0 + 1 by omega, show T + (2 * k0 + 1) = T + 2 * k0 + 1 by omega]
    cases h : kick (node (T + 2 * k0 + 1))
    · rw [h] at e; exact absurd e (by decide)
    · rfl
  have hstep : ∀ j, delta 1 (qs j) (kick (node (T + (n0 + (j + 1))))) = some (qs (j + 1)) := by
    intro j
    have := hqs (j + 1)
    rw [run_succ, hqs j] at this
    simpa using this
  have hform : 10 ≤ qs js ∧ (qs js - 10) % 10 = 0 := by
    obtain ⟨j', hj'⟩ : ∃ j', js = j' + 1 := ⟨js - 1, by omega⟩
    rw [hj'] at hkick ⊢
    have := hstep j'
    rw [hkick] at this
    exact kick_result _ (hq60 _) _ this
  -- the left inputs are the right kicks shifted by js
  have hinp : (fun s => s % 2 == 0 && !cell (T + 2 * k0 + 1 + s) (-1)) =
      (fun s => kick (node (T + (n0 + (js + s))))) := by
    funext s
    rw [show n0 + (js + s) = 2 * k0 + 1 + s by omega, show T + 2 * k0 + 1 + s = T + (2 * k0 + 1 + s) by omega,
      cell_m1_eq hT, Bool.not_not]
    cases hk : kick (node (T + (2 * k0 + 1 + s)))
    · simp
    · have := kick_parity hT _ hk
      simp only [Bool.and_true, beq_iff_eq]
      omega
  intro j _
  -- simulation
  have sim : ∀ i, ∃ p, run 1 (fun s => kick (node (T + (n0 + (js + s))))) 10 i = some p ∧ Sim p (qs (js + i)) := by
    intro i
    induction i with
    | zero =>
      simp only [Nat.add_zero]
      exact ⟨10, rfl, Or.inr ⟨hform.1, hq60 _, by omega⟩⟩
    | succ i ih =>
      obtain ⟨p, hp, hs⟩ := ih
      have e := hstep (js + i)
      rw [show n0 + (js + i + 1) = n0 + (js + (i + 1)) by omega] at e
      obtain ⟨p', hp', hs'⟩ := sim_step hs _ e (hq60 _)
      refine ⟨p', ?_, by rw [show js + (i + 1) = js + i + 1 by omega]; exact hs'⟩
      rw [run_succ, hp]
      simpa using hp'
  obtain ⟨p, hp, _⟩ := sim j
  show (run 1 (fun s => s % 2 == 0 && !cell (T + 2 * k0 + 1 + s) (-1)) 10 j).isSome = true
  rw [hinp, hp]; rfl

/-- **A linear mass bound on `GE2` excludes period 2.** If, on the finite `GE2` words, the number of
even-time zeros is at most `c` times the seed weight plus `d` (`MassBoundP GE2 c d`, open), the
center column is not eventually 2-periodic. -/
theorem not_eventually_period_two_of_E2 (c d : Nat) (hyp : MassBoundP GE2 c d) :
    ¬ ∃ T0, ∀ t, T0 ≤ t → center (t + 2) = center t :=
  not_eventually_period_two_of_lang GE2 prefixDet_GE2 (fun _ _ h => h.1) c d hyp lang_GE2

end Strip

section Fun
open Rule30Jen Rule30Prize Rule30PeriodTwo

/-- zeros bounded by an arbitrary function of the seed weight, on the finite words of `P`. -/
def MassBoundFunP (P : (Nat → Bool) → Nat → Prop) (g : Nat → Nat) : Prop :=
  ∀ m Y : Nat, Y < 2 ^ (2 * m) → P (tr Y) m → Zc (tr Y) m ≤ g (wtH (2 * m) Y)

theorem massBoundFun_of_linear (P : (Nat → Bool) → Nat → Prop) (c d : Nat) (h : MassBoundP P c d) :
    MassBoundFunP P (fun a => c * a + d) := h

/-- `g 0 + … + g (n - 1)`. -/
def sumBelow (g : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumBelow g n + g n

theorem le_sumBelow (g : Nat → Nat) : ∀ n i, i < n → g i ≤ sumBelow g n
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, i, h => by
    simp only [sumBelow]
    rcases Nat.lt_or_ge i n with h' | h'
    · have := le_sumBelow g n i h'; omega
    · rw [show i = n by omega]; omega

theorem no_finite_seed_fun (P : (Nat → Bool) → Nat → Prop) (hP : PrefixDet P)
    (hPG : ∀ b m, P b m → GValid b m) (g : Nat → Nat) (hyp : MassBoundFunP P g) (X : Nat) :
    ¬ ∀ m, P (tr X) m := by
  intro hX
  have hbound : ∀ m, Zc (tr X) m ≤ sumBelow g (wtH X X + 1) := by
    intro m
    have hY : X % 2 ^ (2 * m) < 2 ^ (2 * m) := Nat.mod_lt _ (Nat.two_pow_pos _)
    have htr : ∀ t, t < 2 * m → tr (X % 2 ^ (2 * m)) t = tr X t := fun t ht => tr_mod X _ t ht
    have hPY : P (tr (X % 2 ^ (2 * m))) m := hP _ _ m (fun t ht => (htr t ht).symm) (hX m)
    have hZ : Zc (tr (X % 2 ^ (2 * m))) m = Zc (tr X) m := by
      exact Zc_congr m (fun j hj => htr _ (by omega))
    have := hyp m _ hY hPY
    rw [hZ, wtH_mod] at this
    have hW := wtH_le_total X m
    calc Zc (tr X) m ≤ g (wtH (2 * m) X) := this
      _ ≤ sumBelow g (wtH X X + 1) := le_sumBelow g _ _ (by omega)
  obtain ⟨T, hT⟩ := eventually_no_zero (tr X) _ hbound
  apply not_eventually_const X (2 * T)
  intro t ht
  rcases exists_half t with ⟨j, rfl | rfl⟩
  · exact hT j (by omega)
  · exact (hPG _ (j + 1) (hX (j + 1))).2.1 j (by omega)

/-- The language-generic theorem with an arbitrary bounding function. -/
theorem not_eventually_period_two_of_lang_fun (P : (Nat → Bool) → Nat → Prop) (hP : PrefixDet P)
    (hPG : ∀ b m, P b m → GValid b m) (g : Nat → Nat) (hyp : MassBoundFunP P g)
    (hlang : ∀ T, AltFrom T → ∃ K, ∀ k0, K ≤ k0 → cell (T + 2 * k0 + 1) (-1) = false →
      ∀ m, P (fun s => cell (T + 2 * k0 + 1 + s) (-1)) m) :
    ¬ ∃ T0, ∀ t, T0 ≤ t → center (t + 2) = center t := by
  rintro ⟨T0, hp⟩
  obtain ⟨T, hT⟩ := normalize hp
  obtain ⟨K, hK⟩ := hlang T hT
  have hwhite : ∃ k0, K ≤ k0 ∧ cell (T + 2 * k0 + 1) (-1) = false := by
    refine Classical.byContradiction fun hno' => ?_
    have hno : ∀ k0, K ≤ k0 → cell (T + 2 * k0 + 1) (-1) ≠ false :=
      fun k0 hk hc => hno' ⟨k0, hk, hc⟩
    apply not_eventually_const (rowNat T) (T + 2 * K)
    intro t ht
    rw [tr_rowNat T (alt_guard0 hT) t]
    rcases exists_half t with ⟨j, rfl | rfl⟩
    · exact m1_even hT j
    · rw [show T + (2 * j + 1) = T + 2 * j + 1 by omega]
      cases hc : cell (T + 2 * j + 1) (-1)
      · exact absurd hc (hno j (by omega))
      · rfl
  obtain ⟨k0, hk0, hw⟩ := hwhite
  apply no_finite_seed_fun P hP hPG g hyp (rowNat (T + 2 * k0 + 1))
  intro m
  have hfun : tr (rowNat (T + 2 * k0 + 1)) = fun s => cell (T + 2 * k0 + 1 + s) (-1) :=
    funext (tr_rowNat _ (alt_guard hT k0))
  rw [hfun]
  exact hK k0 hk0 hw m

/-- **A function mass bound on `GE2` excludes period 2.** If, on the finite `GE2` words, the number
of even-time zeros is bounded by some function `g` of the seed weight (`MassBoundFunP GE2 g`,
open), the center column is not eventually 2-periodic. From a late white time of column `-1` the
left half is a finite seed whose trace prefixes are in `GE2` (`lang_GE2`); the bound caps its
even-time zeros, so its trace is eventually black, which `not_eventually_const` excludes. -/
theorem not_eventually_period_two_of_E2_fun (g : Nat → Nat) (hyp : MassBoundFunP GE2 g) :
    ¬ ∃ T0, ∀ t, T0 ≤ t → center (t + 2) = center t :=
  not_eventually_period_two_of_lang_fun GE2 prefixDet_GE2 (fun _ _ h => h.1) g hyp lang_GE2

/-- **The kicks are not eventually periodic.** If the center column alternates from `T`, the kick
sequence of the strip (white center and black column `1`) is not eventually periodic: column `-1`
is its complement from `T` on (`cell_m1_eq`), and it is the trace of the finite left half
`rowNat T` (`tr_not_eventually_periodic`). So no periodic regime of the right half occurs. -/
theorem kicks_not_eventually_periodic {T : Nat} (hT : AltFrom T) (n1 p : Nat) (hp : 0 < p) :
    ¬ ∀ n, n1 ≤ n → kick (node (T + (n + p))) = kick (node (T + n)) := by
  intro h
  have htr : ∀ s, tr (rowNat T) s = cell (T + s) (-1) := tr_rowNat T (alt_guard0 hT)
  have hX : rowNat T ≠ 0 := by
    intro h0
    have := htr 0
    rw [h0] at this
    unfold tr at this
    simp [iter] at this
    have m := m1_even hT 0
    simp at m
    rw [m] at this; exact absurd this (by simp)
  apply tr_not_eventually_periodic (rowNat T) hX n1 p hp
  intro t ht
  rw [htr, htr, cell_m1_eq hT, cell_m1_eq hT, h t ht]

end Fun

/-! ## The bridge to the kit's zero-driven left half -/

section KitBridge
open Rule30Jen Rule30DrivenLeft

/-- The left start whose cell `-1 - i` is bit `i` of `Y` (cells `p ≥ 0` are irrelevant to `L`). -/
def startOf (Y : Nat) : Int → Bool := fun p => if p < 0 then Y.testBit (-1 - p).toNat else false

/-- **Bridge.** The kit's zero-driven left half `L (fun _ => false)` from the finite start
`startOf Y` is the integer map `F` iterated on `Y`: cell `p < 0` at time `t` is bit `-1 - p` of
`iter F t Y`. -/
theorem L_zero_eq_iterate (Y : Nat) : ∀ (t : Nat) (p : Int), p < 0 →
    L (fun _ => false) (startOf Y) t p = (iter F t Y).testBit (-1 - p).toNat := by
  intro t
  induction t with
  | zero => intro p hp; simp [L_zero hp, startOf, hp, iter]
  | succ t ih =>
    intro p hp
    rw [L_succ hp, ih (p - 1) (by omega), iter_succ, testBit_F, ih p hp,
      show (-1 - (p - 1)).toNat = (-1 - p).toNat + 1 by omega]
    unfold rule
    by_cases hp1 : p = -1
    · subst hp1
      rw [show (-1 : Int) + 1 = 0 by omega, L_col0]
      simp
    · rw [ih (p + 1) (by omega), show (-1 - (p + 1)).toNat = (-1 - p).toNat - 1 by omega,
        show decide ((-1 - p).toNat ≥ 1) = true by simp; omega, Bool.true_and]

end KitBridge

/-! ## The one-sided hypothesis `NoSeedGE2` -/

section NoSeed
open Rule30Jen Rule30Prize Rule30PeriodTwo Rule30DrivenLeft

/-- **`NoSeedGE2`** (open): no finite left seed `X` (a natural number, bit `i` = cell `-1 - i`)
has every trace prefix in the language `GE2`. -/
def NoSeedGE2 : Prop := ∀ X : Nat, ¬ ∀ m, GE2 (tr X) m

/-- **`NoSeedGE2` excludes period 2.** If no finite left seed stays in `G ∩ E2` for ever, the
official center column is not eventually 2-periodic, for every transient. No hypothesis on the
right half: the right side enters only through the theorem `lang_GE2`. -/
theorem not_eventually_period_two_of_noSeed_GE2 (h : NoSeedGE2) :
    ¬ ∃ T0, ∀ t, T0 ≤ t → center (t + 2) = center t := by
  rintro ⟨T0, hp⟩
  obtain ⟨T, hT⟩ := normalize hp
  obtain ⟨K, hK⟩ := lang_GE2 T hT
  have hwhite : ∃ k0, K ≤ k0 ∧ cell (T + 2 * k0 + 1) (-1) = false := by
    refine Classical.byContradiction fun hno' => ?_
    have hno : ∀ k0, K ≤ k0 → cell (T + 2 * k0 + 1) (-1) ≠ false :=
      fun k0 hk hc => hno' ⟨k0, hk, hc⟩
    apply not_eventually_const (rowNat T) (T + 2 * K)
    intro t ht
    rw [tr_rowNat T (alt_guard0 hT) t]
    rcases exists_half t with ⟨j, rfl | rfl⟩
    · exact m1_even hT j
    · rw [show T + (2 * j + 1) = T + 2 * j + 1 by omega]
      cases hc : cell (T + 2 * j + 1) (-1)
      · exact absurd hc (hno j (by omega))
      · rfl
  obtain ⟨k0, hk0, hw⟩ := hwhite
  apply h (rowNat (T + 2 * k0 + 1))
  intro m
  have hfun : tr (rowNat (T + 2 * k0 + 1)) = fun s => cell (T + 2 * k0 + 1 + s) (-1) :=
    funext (tr_rowNat _ (alt_guard hT k0))
  rw [hfun]
  exact hK k0 hk0 hw m

/-- **The kit's `Q01` implies `NoSeedGE2`.** A seed `X` that stays in `GE2` for ever has a
nonzero row `F X` one step later, and from that finite start the kit's zero-driven left half keeps
column `-1` black at every even step (bridge `L_zero_eq_iterate`), which `Q01` forbids. -/
theorem noSeed_GE2_of_Q01 (hQ : Rule30PeriodTwo.Q01) : NoSeedGE2 := by
  intro X hX
  have h1 : tr X 1 = true := (hX 1).1.2.1 0 (by omega)
  have hY : F X ≠ 0 := by
    intro h0
    unfold tr at h1
    change (F X).testBit 0 = true at h1
    rw [h0] at h1
    simp at h1
  refine hQ (Nat.log2 (F X) + 1) (startOf (F X)) (by omega) (fun p hp => ?_) ?_ (fun k => ?_)
  · have hp0 : p < 0 := by omega
    simp only [startOf, hp0, ite_true]
    apply Nat.testBit_lt_two_pow
    exact Nat.lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by decide) (by omega))
  · have hn : -((Nat.log2 (F X) + 1 : Nat) : Int) < 0 := by omega
    simp only [startOf, hn, ite_true]
    rw [show (-1 - -((Nat.log2 (F X) + 1 : Nat) : Int)).toNat = Nat.log2 (F X) by omega]
    exact Nat.testBit_log2 hY
  · rw [L_zero_eq_iterate (F X) (2 * k) (-1) (by omega)]
    have h2 := (hX (k + 1)).1.2.1 k (by omega)
    unfold tr at h2
    rw [iter_succ_right] at h2
    simpa using h2

/-- The kit's reduction recovered through `G ∩ E2`: `Q01` excludes period 2
(compare `Rule30PeriodTwo.not_eventually_period_two_of_Q01`). -/
theorem not_eventually_period_two_of_Q01_via_E2 (hQ : Rule30PeriodTwo.Q01) :
    ¬ ∃ T0, ∀ t, T0 ≤ t → center (t + 2) = center t :=
  not_eventually_period_two_of_noSeed_GE2 (noSeed_GE2_of_Q01 hQ)

/-- Any function bound on the even-time zeros of the finite `GE2` words gives `NoSeedGE2`. -/
theorem noSeed_GE2_of_massBoundFun (g : Nat → Nat) (hyp : MassBoundFunP GE2 g) : NoSeedGE2 :=
  fun X => no_finite_seed_fun GE2 prefixDet_GE2 (fun _ _ h => h.1) g hyp X

end NoSeed

/-! ## Two-sided finiteness for `CQ01`: the split `RD ∧ Q01Gap → CQ01` -/

section CQSplit

/-- **Right dichotomy** (open): every finitely supported right half driven by the alternating
column either enters the kit's gate trap (`Rule30GateTrap.trap`, columns `1..16`) at some white
(odd) time, or has eventually periodic column `1` at the white times (`Rule30PeriodTwoSideways.u`). -/
def RD : Prop := ∀ R : Nat → Bool, Rule30ZeroBoundary.FinSupp R →
  (∃ t0, t0 % 2 = 1 ∧ Rule30GateTrap.win R t0 ∈ Rule30GateTrap.trap) ∨
    Rule30Jen.EventuallyPeriodic (Rule30PeriodTwoSideways.u R)

/-- **`RD` and `Q01Gap` give `CQ01`.** The trap branch is the kit's
`Rule30GateTrap.not_finSupp_Psi_of_Q01Gap`; the periodic branch is the kit's
`Rule30PeriodTwoSideways.not_finSupp_Psi_of_eventuallyPeriodic` (Jen). The finiteness of the right
half is used only in `RD`, that of the left half only in `Q01Gap`. -/
theorem CQ01_of_RD_of_Q01Gap (hRD : RD) (hQ : Rule30GateTrap.Q01Gap) :
    Rule30PeriodTwoCoupled.CQ01 := by
  rw [Rule30PeriodTwoSideways.CQ01_iff_Psi]
  intro R hR
  rcases hRD R hR with ⟨t0, h0, hw⟩ | hp
  · exact Rule30GateTrap.not_finSupp_Psi_of_Q01Gap hQ R h0 hw
  · exact Rule30PeriodTwoSideways.not_finSupp_Psi_of_eventuallyPeriodic R hp

/-- The single-seed corollary: `RD` and `Q01Gap` exclude an eventually 2-periodic center column
(through the kit's `Rule30PeriodTwoCoupled.no_eventual_period_two_of_CQ01`). -/
theorem no_eventual_period_two_of_RD_of_Q01Gap (hRD : RD) (hQ : Rule30GateTrap.Q01Gap) :
    ¬ ∃ T0, ∀ t, T0 ≤ t → Rule30Prize.center (t + 2) = Rule30Prize.center t :=
  Rule30PeriodTwoCoupled.no_eventual_period_two_of_CQ01 (CQ01_of_RD_of_Q01Gap hRD hQ)

end CQSplit
/-! ## Sideways retrodiction of internal columns `x X 1..5`, initial seed-bit pinning, and exact low-bit weight invariants (`wtH 4 X = 2`, `wtH 6 X = 3`) -/

section Retrodiction

/-- **Initial Seed Bit Readout (`x_zero_eq_testBit`):**
at time `t = 0`, the retrodicted cell `x X j 0` at depth `j` is bit `j` of the seed `X`. -/
theorem x_zero_eq_testBit (X j : Nat) : x X j 0 = X.testBit j := rfl

/-- **Boundary Trace Readout (`x_zero_depth_eq_tr`):**
at depth `j = 0`, `x X 0 t` is the boundary trace `tr X t`. -/
theorem x_zero_depth_eq_tr (X t : Nat) : x X 0 t = tr X t := rfl

/-- **Forced Black Cell at `t = 2` under `GValid` (`tr_two_eq_true_of_gvalid`):**
if `GValid (tr X) m` holds with `2 ≤ m`, then `tr X 0 = false` and `(tr X 0 || tr X 2) = true`
force `tr X 2 = true`. -/
theorem tr_two_eq_true_of_gvalid {X m : Nat} (hm : 2 ≤ m) (hG : GValid (tr X) m) :
    tr X 0 = false ∧ tr X 2 = true := by
  have h0 : tr X 0 = false := hG.1 (by omega)
  have h02 : (tr X 0 || tr X 2) = true := by
    simpa using hG.2.2 0 (by omega)
  rw [h0, Bool.false_or] at h02
  exact ⟨h0, h02⟩

/-- **Exact Retrodiction of Depth `j = 1` under `GValid` (`x_one_even_odd`):**
if `GValid (tr X) m` holds, then for every `r` with `r + 1 < m`,
`x X 1 (2 * r) = !tr X (2 * r)` and `x X 1 (2 * r + 1) = !tr X (2 * r + 2)`. -/
theorem x_one_even_odd {X m r : Nat} (hr : r + 1 < m) (hG : GValid (tr X) m) :
    x X 1 (2 * r) = !tr X (2 * r) ∧ x X 1 (2 * r + 1) = !tr X (2 * r + 2) := by
  have hodd0 : x X 0 (2 * r + 1) = true := hG.2.1 r (by omega)
  refine ⟨?_, ?_⟩
  · rw [x_rec0, hodd0]
    unfold x tr; cases (iter F (2 * r) X).testBit 0 <;> rfl
  · rw [x_rec0, show 2 * r + 1 + 1 = 2 * r + 2 by omega, hodd0]
    unfold x tr; cases (iter F (2 * r + 2) X).testBit 0 <;> rfl

/-- **Exact Retrodiction & Even-Odd Synchronization of Depth `j = 2` under `GValid` (`x_two_even_odd`):**
if `GValid (tr X) m` holds, then for every `r` with `r + 1 < m`, both the even-time cell `x X 2 (2 * r)`
and the odd-time cell `x X 2 (2 * r + 1)` equal `tr X (2 * r + 2)`. -/
theorem x_two_even_odd {X m r : Nat} (hr : r + 1 < m) (hG : GValid (tr X) m) :
    x X 2 (2 * r) = tr X (2 * r + 2) ∧ x X 2 (2 * r + 1) = tr X (2 * r + 2) := by
  rcases x_one_even_odd hr hG with ⟨h1e, h1o⟩
  have hodd0 : x X 0 (2 * r + 1) = true := hG.2.1 r (by omega)
  have h0e : x X 0 (2 * r) = tr X (2 * r) := rfl
  have h0e2 : x X 1 (2 * r + 2) = !tr X (2 * r + 2) := by
    have hodd1 : x X 0 (2 * (r + 1) + 1) = true := hG.2.1 (r + 1) hr
    rw [x_rec0, show 2 * r + 2 + 1 = 2 * (r + 1) + 1 by omega, hodd1]
    unfold x tr; cases (iter F (2 * r + 2) X).testBit 0 <;> rfl
  refine ⟨?_, ?_⟩
  · rw [x_rec X 0 (2 * r), h1o, h1e, h0e]
    cases tr X (2 * r) <;> cases tr X (2 * r + 2) <;> rfl
  · rw [x_rec X 0 (2 * r + 1), show 2 * r + 1 + 1 = 2 * r + 2 by omega, h0e2, h1o, hodd0]
    cases tr X (2 * r + 2) <;> rfl

/-- **Universal All-White Even-Time Column at Depth `j = 3` under `GValid` (`x_three_even_of_gvalid`):**
if `GValid (tr X) m` holds, then for every `r` with `r + 1 < m`, `x X 3 (2 * r) = false`. -/
theorem x_three_even_of_gvalid {X m r : Nat} (hr : r + 1 < m) (hG : GValid (tr X) m) :
    x X 3 (2 * r) = false := by
  rcases x_one_even_odd hr hG with ⟨h1e, _⟩
  rcases x_two_even_odd hr hG with ⟨h2e, h2o⟩
  have hgold : (tr X (2 * r) || tr X (2 * r + 2)) = true := hG.2.2 r hr
  rw [x_rec X 1 (2 * r), h2o, h2e, h1e]
  revert hgold
  cases tr X (2 * r) <;> cases tr X (2 * r + 2) <;> decide

/-- **Exact Retrodiction of Depth `j = 3` under `GValid` (`x_three_even_odd`):**
if `GValid (tr X) m` holds, then for every `r` with `r + 2 < m`, the even-time cell `x X 3 (2 * r)`
is identically `false` (an all-white even-time column) and `x X 3 (2 * r + 1) = !tr X (2 * r + 4)`. -/
theorem x_three_even_odd {X m r : Nat} (hr : r + 2 < m) (hG : GValid (tr X) m) :
    x X 3 (2 * r) = false ∧ x X 3 (2 * r + 1) = !tr X (2 * r + 4) := by
  rcases x_one_even_odd (by omega : r + 1 < m) hG with ⟨_, h1o⟩
  rcases x_two_even_odd (by omega : r + 1 < m) hG with ⟨_, h2o⟩
  rcases x_two_even_odd (r := r + 1) hr hG with ⟨h2e_next, _⟩
  refine ⟨x_three_even_of_gvalid (by omega) hG, ?_⟩
  rw [x_rec X 1 (2 * r + 1), show 2 * r + 1 + 1 = 2 * (r + 1) by omega,
      h2e_next, h2o, h1o, show 2 * (r + 1) + 2 = 2 * r + 4 by omega]
  cases tr X (2 * r + 2) <;> cases tr X (2 * r + 4) <;> rfl

/-- **Exact Retrodiction of Depths `j = 4` and `j = 5` at `t = 0` (`x_four_five_zero`):**
if `GValid (tr X) m` holds with `3 ≤ m`, then `x X 4 0 = tr X 4`, `x X 4 1 = true`, and
`x X 5 0 = !tr X 4`. -/
theorem x_four_five_zero {X m : Nat} (hm : 3 ≤ m) (hG : GValid (tr X) m) :
    x X 4 0 = tr X 4 ∧ x X 4 1 = true ∧ x X 5 0 = !tr X 4 := by
  rcases tr_two_eq_true_of_gvalid (by omega) hG with ⟨h0, h2⟩
  rcases x_two_even_odd (r := 0) (by omega) hG with ⟨h2_0, h2_1⟩
  rcases x_two_even_odd (r := 1) (by omega) hG with ⟨h2_2, _⟩
  rcases x_three_even_odd (r := 0) (by omega) hG with ⟨h3_0, h3_1⟩
  have h3_2 : x X 3 (2 * 1) = false := x_three_even_of_gvalid (r := 1) (by omega) hG
  simp only [Nat.mul_zero, Nat.zero_add] at h2_0 h2_1 h3_0 h3_1
  have hx4_0 : x X 4 0 = tr X 4 := by
    rw [x_rec X 2 0, h3_1, h3_0, h2_0, h2]
    cases tr X 4 <;> rfl
  have hx4_1 : x X 4 1 = true := by
    rw [x_rec X 2 1, show (1 + 1 : Nat) = 2 * 1 by rfl, h3_2, h3_1, h2_1, h2]
    cases tr X 4 <;> rfl
  have hx5_0 : x X 5 0 = !tr X 4 := by
    rw [x_rec X 3 0, hx4_1, hx4_0, h3_0]
    cases tr X 4 <;> rfl
  exact ⟨hx4_0, hx4_1, hx5_0⟩

/-- **Exact Pinning of the First Six Seed Bits under `GValid` (`seed_bits_zero_to_five`):**
for any seed `X` satisfying `GValid (tr X) m` with `3 ≤ m`, its lowest six binary digits are
`(false, true, true, false, tr X 4, !tr X 4)`. -/
theorem seed_bits_zero_to_five {X m : Nat} (hm : 3 ≤ m) (hG : GValid (tr X) m) :
    X.testBit 0 = false ∧ X.testBit 1 = true ∧ X.testBit 2 = true ∧
    X.testBit 3 = false ∧ X.testBit 4 = tr X 4 ∧ X.testBit 5 = !tr X 4 := by
  rcases tr_two_eq_true_of_gvalid (by omega) hG with ⟨h0, h2⟩
  have h1 := (x_one_even_odd (r := 0) (by omega) hG).1
  have h2' := (x_two_even_odd (r := 0) (by omega) hG).1
  have h3' := (x_three_even_odd (r := 0) (by omega) hG).1
  rcases x_four_five_zero hm hG with ⟨h4', _, h5'⟩
  simp only [Nat.mul_zero, Nat.zero_add, x_zero_eq_testBit] at h1 h2' h3' h4' h5'
  rw [h0] at h1
  rw [h2] at h2'
  exact ⟨h0, h1, h2', h3', h4', h5'⟩

/-- **Universal 4-Bit and 6-Bit Seed Weight Invariants (`wtH_four_and_six_of_gvalid`):**
for every seed `X` satisfying `GValid (tr X) m` with `3 ≤ m`, `wtH 4 X = 2` and `wtH 6 X = 3`
(since bits `0..3` are `(false, true, true, false)` and bits `4, 5` are complementary `(tr X 4, !tr X 4)`). -/
theorem wtH_four_and_six_of_gvalid {X m : Nat} (hm : 3 ≤ m) (hG : GValid (tr X) m) :
    wtH 4 X = 2 ∧ wtH 6 X = 3 := by
  rcases seed_bits_zero_to_five hm hG with ⟨b0, b1, b2, b3, b4, b5⟩
  have hw4 : wtH 4 X = 2 := by
    simp only [wtH, b0, b1, b2, b3]
    rfl
  refine ⟨hw4, ?_⟩
  change wtH 4 X + (if X.testBit 4 = true then 1 else 0) + (if X.testBit 5 = true then 1 else 0) = 3
  rw [hw4, b4, b5]
  cases tr X 4 <;> rfl

end Retrodiction

/-! ## Weakening `Q01Gap` to the 5-word condition `Q01GapWords` in the `RD` split -/

section CQSplitWords

/-- **`RD` and `Q01GapWords` give `CQ01` (`CQ01_of_RD_of_Q01GapWords`):**
weakens `CQ01_of_RD_of_Q01Gap` from `Rule30GateTrap.Q01Gap` to the 5-word forbidden-gap condition
`Rule30GateTrapWords.Q01GapWords`. -/
theorem CQ01_of_RD_of_Q01GapWords (hRD : RD) (hQ : Rule30GateTrapWords.Q01GapWords) :
    Rule30PeriodTwoCoupled.CQ01 := by
  rw [Rule30PeriodTwoSideways.CQ01_iff_Psi]
  intro R hR
  rcases hRD R hR with ⟨t0, h0, hw⟩ | hp
  · exact Rule30GateTrapWords.not_finSupp_Psi_of_Q01GapWords hQ R h0 hw
  · exact Rule30PeriodTwoSideways.not_finSupp_Psi_of_eventuallyPeriodic R hp

/-- **Single-Seed Corollary (`no_eventual_period_two_of_RD_of_Q01GapWords`):**
`RD` and `Q01GapWords` exclude an eventually 2-periodic center column. -/
theorem no_eventual_period_two_of_RD_of_Q01GapWords (hRD : RD)
    (hQ : Rule30GateTrapWords.Q01GapWords) :
    ¬ ∃ T0, ∀ t, T0 ≤ t → Rule30Prize.center (t + 2) = Rule30Prize.center t :=
  Rule30PeriodTwoCoupled.no_eventual_period_two_of_CQ01 (CQ01_of_RD_of_Q01GapWords hRD hQ)

end CQSplitWords

end Rule30PeriodTwoWidth13
end Ruliology.CellularAutomata
