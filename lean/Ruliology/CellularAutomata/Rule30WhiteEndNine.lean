module

public import Ruliology.CellularAutomata.Rule30StripCertificates
public import Ruliology.CellularAutomata.Rule30MaskedJen

/-!
# The white end from `q = 9`: one pumped mode certificate for every `1 0^q`

For every `q ≥ 9`, the center column of the single-seed pattern is not eventually the repeating word
`1 0^q`, whatever the transient (`not_eventually_white_end_ge9`). One certificate covers the whole
family; `Rule30WhiteEnd` is not used.

**Mode certificates.** Watch `K` cells right of the center with an arbitrary cell beyond them, as in
`Rule30StripCertificates`. Fix a word `w`, `k` warm-up periods and one white phase `pe`. Let `S0`
contain the strips reachable after `k` periods and be closed under one more period. At every other
white phase column `1` is constant on the corresponding set. At `pe`, column `1` is a *label* fixed
by the strip at the start of the period: `1` on a set `E1`, `0` on a set `E0`, with
`S0 ⊆ E0 ∪ E1`. Two transition rules are checked: after a period labelled `1` comes a period
labelled `0`, and after two periods labelled `0` comes a period labelled `0`. Along the true history
the labels are then eventually constant or alternating, so `orCol 0` is eventually periodic with
period `2 |w|`, which `Rule30MaskedJen.orCol_not_eventuallyPeriodic` forbids
(`not_eventually_word_mode`, sound for every word, width, warm-up and label phase).

**One formula for every `q`.** For `w = 1 0^q` take width `12`, `5` warm-up periods and label
phase `2`. `S0 = reach 12 5 q` is the set of strips reachable after five periods from all `4096`
strips, and `E0`, `E1` are its intersections with two fixed masks: column `1` two steps after the
black cell is white exactly when the strip starts with `1` and has a `1` among its next two cells
(`lab0`).

**Pumping over the white run** (`modeCert_pumped`). A period of `1 0^q` is one black step and `q`
white steps. For `q ≥ M` every period lands in a set that contains the `M`-step image and is closed
under white steps. These sets are built once (`chainU`, `pumpSet`) and checked once (`pumpCheck`),
with no dependence on `q`. Strip images are monotone, so the reachable sets of every `q ≥ M` lie
inside them, and every condition of the mode certificate follows: the forced phases from the forced
phases of the closed sets, the labels from the masks, and both transition rules because the closed
sets carry label `0` throughout. With `M = 10` this covers every `q ≥ 10` (`pumpCheck_12`).
At `q = 9` the label `1` occurs, and the kernel evaluates the same formula there
(`modeCert_nine`). The same pumped check started at nine white steps fails (`pumpCheck_12_nine`):
its sets contain strips with label `1`.

**Bit-parallel images.** `fimage` computes all successors of a set of strips with `O(K)` operations
on `2 ^ (K + 1)`-bit numbers: one cell at a time, with one extra bit holding the old right
neighbour (`flipStep`, `sweep`). Its soundness is `fimage_mem`. All kernel checks of this module
take a few seconds.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30WhiteEndNine

open Rule30Jen Rule30Prize Rule30MaskedJen Rule30StripCertificates

/-- Bits `x < 2 ^ m` of an index with `x.testBit j`. -/
def bm (j : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => bm j m ||| ((if m = j then 2 ^ (2 ^ m) - 1 else bm j m) <<< 2 ^ m)

theorem testBit_bm (j : Nat) : ∀ m x, (bm j m).testBit x = (decide (x < 2 ^ m) && x.testBit j)
  | 0, x => by
    by_cases hx : x = 0
    · subst hx; simp [bm]
    · simp [bm]; omega
  | m + 1, x => by
    rw [bm, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_bm j m x]
    have hp : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [Nat.pow_succ]; omega
    by_cases hx : x < 2 ^ m
    · have hb : (2 ^ (m + 1) > x) := by omega
      simp [hx, hb, show ¬ (x ≥ 2 ^ m) by omega]
    · obtain ⟨y, rfl⟩ : ∃ y, x = 2 ^ m + y := ⟨x - 2 ^ m, by omega⟩
      have e1 : 2 ^ m + y - 2 ^ m = y := by omega
      simp only [hx, decide_false, Bool.false_and, Bool.false_or, e1,
        show 2 ^ m + y ≥ 2 ^ m by omega, decide_true, Bool.true_and]
      by_cases hmj : m = j
      · subst hmj
        rw [ite_eq_left rfl, Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_add_eq]
        by_cases hy : y < 2 ^ m
        · simp [hy, Nat.testBit_lt_two_pow hy, show 2 ^ m + y < 2 ^ (m + 1) by omega]
        · simp [hy, show ¬ 2 ^ m + y < 2 ^ (m + 1) by omega]
      · rw [ite_eq_right hmj, testBit_bm j m y]
        by_cases hy : y < 2 ^ m
        · simp only [hy, decide_true, Bool.true_and, show 2 ^ m + y < 2 ^ (m + 1) by omega]
          by_cases hjm : j < m
          · rw [Nat.testBit_two_pow_add_gt hjm]
          · have hj : m < j := by omega
            have h1 : y < 2 ^ j := Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by omega) (by omega))
            have h2 : 2 ^ m + y < 2 ^ j := Nat.lt_of_lt_of_le (by omega : 2 ^ m + y < 2 ^ (m + 1))
              (Nat.pow_le_pow_right (by omega) (by omega))
            rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]
        · simp [hy, show ¬ 2 ^ m + y < 2 ^ (m + 1) by omega]

theorem testBit_fullSet (n x : Nat) : (fullSet n).testBit x = decide (x < 2 ^ n) := by
  unfold fullSet; exact Nat.testBit_two_pow_sub_one _ _

theorem xor_two_pow_eq_add : ∀ (k x : Nat), x.testBit k = false → x ^^^ 2 ^ k = x + 2 ^ k
  | 0, x, h => by
    have h0 : x % 2 = 0 := by simp [Nat.testBit_zero] at h; omega
    apply Nat.eq_of_testBit_eq; intro i
    cases i with
    | zero => simp [Nat.testBit_zero]; omega
    | succ i =>
      have e : (x + 2 ^ 0) / 2 = x / 2 := by simp; omega
      rw [Nat.testBit_xor, Nat.testBit_succ x, Nat.testBit_succ (x + 2 ^ 0), e, Nat.testBit_two_pow]
      simp
  | k + 1, x, h => by
    have hk : (x / 2).testBit k = false := by rw [Nat.testBit_div_two]; exact h
    have ih := xor_two_pow_eq_add k (x / 2) hk
    apply Nat.eq_of_testBit_eq; intro i
    have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
    cases i with
    | zero =>
      rw [Nat.testBit_xor, Nat.testBit_two_pow]
      simp only [Nat.testBit_zero, hp]
      have : (x + 2 * 2 ^ k) % 2 = x % 2 := by omega
      simp [this]
    | succ i =>
      have e : (x + 2 ^ (k + 1)) / 2 = x / 2 + 2 ^ k := by rw [hp]; omega
      rw [Nat.testBit_xor, Nat.testBit_succ x, Nat.testBit_succ (x + 2 ^ (k + 1)), e, ← ih,
        Nat.testBit_xor, Nat.testBit_two_pow, Nat.testBit_two_pow]
      simp

theorem shl_mem {A y : Nat} (s : Nat) (hy : y.testBit s = false) (hA : A.testBit y = true) :
    (A <<< 2 ^ s).testBit (y ^^^ 2 ^ s) = true := by
  rw [xor_two_pow_eq_add s y hy, Nat.testBit_shiftLeft]
  simp [hA]

theorem shr_mem {A y : Nat} (s : Nat) (hy : y.testBit s = true) (hA : A.testBit y = true) :
    (A >>> 2 ^ s).testBit (y ^^^ 2 ^ s) = true := by
  rw [Nat.testBit_shiftRight]
  have h1 : (y ^^^ 2 ^ s).testBit s = false := by simp [Nat.testBit_xor, hy]
  have h2 := xor_two_pow_eq_add s _ h1
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at h2
  rw [Nat.add_comm, ← h2]; exact hA

/-- One cell `k` of the strip, on extended indices: bit `K` holds the old value of cell `k + 1`. -/
def flipStep (K n k Lm T : Nat) : Nat :=
  (T &&& (fullSet n ^^^ Lm) &&& (fullSet n ^^^ bm k n) &&& (fullSet n ^^^ bm K n)) |||
  (((T &&& (fullSet n ^^^ Lm) &&& (fullSet n ^^^ bm k n) &&& bm K n) >>> 2 ^ K) <<< 2 ^ k) |||
  ((T &&& (fullSet n ^^^ Lm) &&& bm k n &&& (fullSet n ^^^ bm K n)) <<< 2 ^ K) |||
  (T &&& (fullSet n ^^^ Lm) &&& bm k n &&& bm K n) |||
  ((T &&& Lm &&& (fullSet n ^^^ bm k n) &&& (fullSet n ^^^ bm K n)) <<< 2 ^ k) |||
  ((T &&& Lm &&& (fullSet n ^^^ bm k n) &&& bm K n) >>> 2 ^ K) |||
  (((T &&& Lm &&& bm k n &&& (fullSet n ^^^ bm K n)) >>> 2 ^ k) <<< 2 ^ K) |||
  ((T &&& Lm &&& bm k n &&& bm K n) >>> 2 ^ k)

theorem mem_flipStep {K n k Lm T x : Nat} (hkK : k < K) (hK : K < n) (hx : x < 2 ^ n)
    (hT : T.testBit x = true) :
    ∃ x', (flipStep K n k Lm T).testBit x' = true ∧ ∀ i, x'.testBit i =
      if i = k then xor (Lm.testBit x) (x.testBit k || x.testBit K)
      else if i = K then x.testBit k else x.testBit i := by
  have hF : ∀ M, (fullSet n ^^^ M).testBit x = !M.testBit x := by
    intro M; rw [Nat.testBit_xor, testBit_fullSet]; simp [hx]
  have hk : (bm k n).testBit x = x.testBit k := by rw [testBit_bm]; simp [hx]
  have hKb : (bm K n).testBit x = x.testBit K := by rw [testBit_bm]; simp [hx]
  have hne : k ≠ K := by omega
  have hxk : ∀ i, (x ^^^ 2 ^ k).testBit i = (x.testBit i ^^ decide (i = k)) := by
    intro i; simp [Nat.testBit_xor, Nat.testBit_two_pow, eq_comm]
  have hxK : ∀ i, (x ^^^ 2 ^ K).testBit i = (x.testBit i ^^ decide (i = K)) := by
    intro i; simp [Nat.testBit_xor, Nat.testBit_two_pow, eq_comm]
  have hxkK : ∀ i, ((x ^^^ 2 ^ k) ^^^ 2 ^ K).testBit i =
      (x.testBit i ^^ decide (i = k) ^^ decide (i = K)) := by
    intro i; simp [Nat.testBit_xor, Nat.testBit_two_pow, eq_comm]
  have hxKk : ∀ i, ((x ^^^ 2 ^ K) ^^^ 2 ^ k).testBit i =
      (x.testBit i ^^ decide (i = K) ^^ decide (i = k)) := by
    intro i; simp [Nat.testBit_xor, Nat.testBit_two_pow, eq_comm]
  cases hl : Lm.testBit x <;> cases hc : x.testBit k <;> cases hu : x.testBit K
  · refine ⟨x, ?_, fun i => ?_⟩
    · have key : (T &&& (fullSet n ^^^ Lm) &&& (fullSet n ^^^ bm k n) &&& (fullSet n ^^^ bm K n)).testBit x
          = true := by simp only [Nat.testBit_and, hT, hF, hk, hKb, hl, hc, hu]; rfl
      unfold flipStep; simp only [Nat.testBit_or, key, Bool.true_or]
    · by_cases h1 : i = k
      · subst h1; simp [hc]
      · by_cases h2 : i = K
        · subst h2; simp [h1, hu]
        · simp [h1, h2]
  · refine ⟨(x ^^^ 2 ^ K) ^^^ 2 ^ k, ?_, fun i => ?_⟩
    · have key : (((T &&& (fullSet n ^^^ Lm) &&& (fullSet n ^^^ bm k n) &&& bm K n) >>> 2 ^ K)
          <<< 2 ^ k).testBit ((x ^^^ 2 ^ K) ^^^ 2 ^ k) = true := by
        apply shl_mem k (by rw [hxK]; simp [hc, hne])
        apply shr_mem K hu
        simp only [Nat.testBit_and, hT, hF, hk, hKb, hl, hc, hu]; rfl
      unfold flipStep; simp only [Nat.testBit_or, key, Bool.true_or, Bool.or_true]
    · rw [hxKk]
      by_cases h1 : i = k
      · subst h1; simp [hc, hne]
      · by_cases h2 : i = K
        · subst h2; simp [h1, hu]
        · simp [h1, h2]
  · refine ⟨x ^^^ 2 ^ K, ?_, fun i => ?_⟩
    · have key : ((T &&& (fullSet n ^^^ Lm) &&& bm k n &&& (fullSet n ^^^ bm K n)) <<< 2 ^ K).testBit
          (x ^^^ 2 ^ K) = true := by
        apply shl_mem K hu
        simp only [Nat.testBit_and, hT, hF, hk, hKb, hl, hc, hu]; rfl
      unfold flipStep; simp only [Nat.testBit_or, key, Bool.true_or, Bool.or_true]
    · rw [hxK]
      by_cases h1 : i = k
      · subst h1; simp [hc, hne]
      · by_cases h2 : i = K
        · subst h2; simp [h1, hu]
        · simp [h1, h2]
  · refine ⟨x, ?_, fun i => ?_⟩
    · have key : (T &&& (fullSet n ^^^ Lm) &&& bm k n &&& bm K n).testBit x = true := by
        simp only [Nat.testBit_and, hT, hF, hk, hKb, hl, hc, hu]; rfl
      unfold flipStep; simp only [Nat.testBit_or, key, Bool.true_or, Bool.or_true]
    · by_cases h1 : i = k
      · subst h1; simp [hc]
      · by_cases h2 : i = K
        · subst h2; simp [h1, hu]
        · simp [h1, h2]
  · refine ⟨x ^^^ 2 ^ k, ?_, fun i => ?_⟩
    · have key : ((T &&& Lm &&& (fullSet n ^^^ bm k n) &&& (fullSet n ^^^ bm K n)) <<< 2 ^ k).testBit
          (x ^^^ 2 ^ k) = true := by
        apply shl_mem k hc
        simp only [Nat.testBit_and, hT, hF, hk, hKb, hl, hc, hu]; rfl
      unfold flipStep; simp only [Nat.testBit_or, key, Bool.true_or, Bool.or_true]
    · rw [hxk]
      by_cases h1 : i = k
      · subst h1; simp [hc]
      · by_cases h2 : i = K
        · subst h2; simp [h1, hu]
        · simp [h1, h2]
  · refine ⟨x ^^^ 2 ^ K, ?_, fun i => ?_⟩
    · have key : ((T &&& Lm &&& (fullSet n ^^^ bm k n) &&& bm K n) >>> 2 ^ K).testBit
          (x ^^^ 2 ^ K) = true := by
        apply shr_mem K hu
        simp only [Nat.testBit_and, hT, hF, hk, hKb, hl, hc, hu]; rfl
      unfold flipStep; simp only [Nat.testBit_or, key, Bool.true_or, Bool.or_true]
    · rw [hxK]
      by_cases h1 : i = k
      · subst h1; simp [hc, hne]
      · by_cases h2 : i = K
        · subst h2; simp [h1, hu]
        · simp [h1, h2]
  · refine ⟨(x ^^^ 2 ^ k) ^^^ 2 ^ K, ?_, fun i => ?_⟩
    · have key : (((T &&& Lm &&& bm k n &&& (fullSet n ^^^ bm K n)) >>> 2 ^ k) <<< 2 ^ K).testBit
          ((x ^^^ 2 ^ k) ^^^ 2 ^ K) = true := by
        apply shl_mem K (by rw [hxk]; simp [hu, Ne.symm hne])
        apply shr_mem k hc
        simp only [Nat.testBit_and, hT, hF, hk, hKb, hl, hc, hu]; rfl
      unfold flipStep; simp only [Nat.testBit_or, key, Bool.true_or, Bool.or_true]
    · rw [hxkK]
      by_cases h1 : i = k
      · subst h1; simp [hc, hne]
      · by_cases h2 : i = K
        · subst h2; simp [h1, hu]
        · simp [h1, h2]
  · refine ⟨x ^^^ 2 ^ k, ?_, fun i => ?_⟩
    · have key : ((T &&& Lm &&& bm k n &&& bm K n) >>> 2 ^ k).testBit (x ^^^ 2 ^ k) = true := by
        apply shr_mem k hc
        simp only [Nat.testBit_and, hT, hk, hKb, hl, hc, hu]; rfl
      unfold flipStep; simp only [Nat.testBit_or, key, Bool.or_true]
    · rw [hxk]
      by_cases h1 : i = k
      · subst h1; simp [hc]
      · by_cases h2 : i = K
        · subst h2; simp [h1, hu]
        · simp [h1, h2]

def leftMask (n : Nat) (a : Bool) (k : Nat) : Nat :=
  if k = 0 then (if a then fullSet n else 0) else bm (k - 1) n

/-- Update the cells `k - 1, …, 0` (the cells `k, …, K - 1` are already updated). -/
def sweep (K : Nat) (a : Bool) : Nat → Nat → Nat
  | 0, T => T
  | k + 1, T => sweep K a k (flipStep K (K + 1) k (leftMask (K + 1) a k) T)

/-- **Bit-parallel image.** All successors of the strips in `S` (both values of the right
boundary), computed with `O(K)` operations on `2 ^ (K + 1)`-bit numbers. -/
def fimage (K : Nat) (a : Bool) (S : Nat) : Nat :=
  let T := sweep K a K ((S &&& fullSet K) ||| ((S &&& fullSet K) <<< 2 ^ K))
  (T ||| (T >>> 2 ^ K)) &&& fullSet K

/-- Bits of an extended index once cells `k, …, K - 1` hold the new strip `s` and bit `K` holds
the old cell `k` (the right boundary `z` while `k = K`). -/
def Spec (K k r s : Nat) (z : Bool) (x : Nat) : Prop :=
  ∀ i, x.testBit i = if i < k then r.testBit i else if i < K then s.testBit i
    else if i = K then (if k = K then z else r.testBit k) else false

theorem spec_lt {K k r s : Nat} {z : Bool} {x : Nat} (hk : k ≤ K) (h : Spec K k r s z x) :
    x < 2 ^ (K + 1) := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [h i]; simp [show ¬ i < k by omega, show ¬ i < K by omega, show i ≠ K by omega]

theorem sweep_mem (K : Nat) (a : Bool) (r : Nat) (z : Bool) (hr : r < 2 ^ K) :
    ∀ k, k ≤ K → ∀ T x, T.testBit x = true → Spec K k r (stripStep K a z r) z x →
      ∃ x', (sweep K a k T).testBit x' = true ∧ Spec K 0 r (stripStep K a z r) z x'
  | 0, _, T, x, hT, hs => ⟨x, hT, hs⟩
  | k + 1, hk, T, x, hT, hs => by
    obtain ⟨x', hT', hb⟩ := mem_flipStep (Lm := leftMask (K + 1) a k) (by omega : k < K)
      (by omega : K < K + 1) (spec_lt hk hs) hT
    refine sweep_mem K a r z hr k (by omega) _ x' hT' (fun i => ?_)
    rw [hb i]
    have hl : (leftMask (K + 1) a k).testBit x = if k = 0 then a else r.testBit (k - 1) := by
      unfold leftMask
      by_cases h0 : k = 0
      · subst h0; cases a <;> simp [testBit_fullSet, spec_lt hk hs]
      · simp only [h0, ite_false, testBit_bm, spec_lt hk hs, decide_true, Bool.true_and, hs (k - 1)]
        simp [show k - 1 < k + 1 by omega]
    by_cases h1 : i = k
    · subst h1
      rw [ite_eq_left rfl, hl, hs i, hs K, testBit_stripStep K a z r hr i (by omega)]
      simp only [show i < i + 1 by omega, ite_true, show ¬ K < i + 1 by omega, show ¬ K < K by omega,
        ite_false, show ¬ i < i by omega, show i < K by omega, ite_true]
      unfold rule
      by_cases h2 : i + 1 = K
      · simp [h2]
      · simp [h2]
    · rw [ite_eq_right h1]
      by_cases h2 : i = K
      · subst h2
        rw [ite_eq_left rfl, hs k]
        simp [show k < k + 1 by omega, show ¬ i < k by omega, show k ≠ i by omega]
      · rw [ite_eq_right h2, hs i]
        by_cases h3 : i < k
        · simp [h3, show i < k + 1 by omega]
        · simp [h3, show ¬ i < k + 1 by omega, h2]

/-- **Soundness of the bit-parallel image**: each successor of a strip in `S` is in `fimage K a S`. -/
theorem fimage_mem {K : Nat} {a : Bool} {S r : Nat} (hr : r < 2 ^ K) (hS : S.testBit r = true)
    (z : Bool) : (fimage K a S).testBit (stripStep K a z r) = true := by
  have hS' : (S &&& fullSet K).testBit r = true := by
    rw [Nat.testBit_and, hS, testBit_fullSet]; simp [hr]
  have hrK : r.testBit K = false := Nat.testBit_lt_two_pow hr
  -- the extended start index
  obtain ⟨x0, hx0, hs0⟩ : ∃ x0, ((S &&& fullSet K) ||| ((S &&& fullSet K) <<< 2 ^ K)).testBit x0 = true ∧
      Spec K K r (stripStep K a z r) z x0 := by
    cases z
    · refine ⟨r, by rw [Nat.testBit_or, hS', Bool.true_or], fun i => ?_⟩
      by_cases h1 : i < K
      · simp [h1]
      · simp only [h1, ite_false, ite_true]
        by_cases h2 : i = K
        · subst h2; simp [hrK]
        · simp only [h2, ite_false]
          exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hr (Nat.pow_le_pow_right (by omega) (by omega)))
    · refine ⟨r ^^^ 2 ^ K, ?_, fun i => ?_⟩
      · rw [Nat.testBit_or, shl_mem K hrK hS', Bool.or_true]
      · rw [Nat.testBit_xor, Nat.testBit_two_pow]
        by_cases h1 : i < K
        · simp [h1, show K ≠ i by omega]
        · simp only [h1, ite_false, ite_true]
          by_cases h2 : i = K
          · subst h2; simp [hrK]
          · simp only [h2, ite_false, show (K = i) = False from propext ⟨fun h => h2 h.symm, False.elim⟩,
              decide_false, Bool.xor_false]
            exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hr (Nat.pow_le_pow_right (by omega) (by omega)))
  obtain ⟨x, hx, hs⟩ := sweep_mem K a r z hr K (Nat.le_refl K) _ x0 hx0 hs0
  have hlt := stripStep_lt K a z r
  have hsK : ∀ i, K ≤ i → (stripStep K a z r).testBit i = false := fun i hi =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) hi))
  unfold fimage
  simp only
  rw [Nat.testBit_and, testBit_fullSet, Nat.testBit_or, Nat.testBit_shiftRight]
  simp only [hlt, decide_true, Bool.and_true]
  cases hb : x.testBit K
  · have : x = stripStep K a z r := by
      apply Nat.eq_of_testBit_eq; intro i
      by_cases h1 : i < K
      · rw [hs i]; simp [h1]
      · by_cases h2 : i = K
        · subst h2; rw [hb, hsK i (Nat.le_refl i)]
        · rw [hs i]; simp [h1, h2, hsK i (by omega)]
    rw [← this, hx, Bool.true_or]
  · have : 2 ^ K + stripStep K a z r = x := by
      rw [Nat.add_comm, ← xor_two_pow_eq_add K _ (hsK K (Nat.le_refl K))]
      apply Nat.eq_of_testBit_eq; intro i
      rw [Nat.testBit_xor, Nat.testBit_two_pow]
      by_cases h1 : i < K
      · rw [hs i]; simp [h1, show K ≠ i by omega]
      · by_cases h2 : i = K
        · subst h2; rw [hb, hsK i (Nat.le_refl i)]; simp
        · rw [hs i]; simp [h1, h2, hsK i (by omega), show K ≠ i by omega]
    rw [this, hx, Bool.or_true]

/-! Monotonicity. -/

def Mono (A B : Nat) : Prop := ∀ i, A.testBit i = true → B.testBit i = true

theorem mono_and {A B : Nat} (M : Nat) (h : Mono A B) : Mono (A &&& M) (B &&& M) := by
  intro i hi; rw [Nat.testBit_and] at hi ⊢
  rw [Bool.and_eq_true] at hi ⊢; exact ⟨h i hi.1, hi.2⟩

theorem mono_or {A B C D : Nat} (h1 : Mono A B) (h2 : Mono C D) : Mono (A ||| C) (B ||| D) := by
  intro i hi; rw [Nat.testBit_or] at hi ⊢
  rw [Bool.or_eq_true] at hi ⊢
  exact hi.imp (h1 i) (h2 i)

theorem mono_shl {A B : Nat} (s : Nat) (h : Mono A B) : Mono (A <<< s) (B <<< s) := by
  intro i hi; rw [Nat.testBit_shiftLeft] at hi ⊢
  rw [Bool.and_eq_true] at hi ⊢; exact ⟨hi.1, h _ hi.2⟩

theorem mono_shr {A B : Nat} (s : Nat) (h : Mono A B) : Mono (A >>> s) (B >>> s) := by
  intro i hi; rw [Nat.testBit_shiftRight] at hi ⊢; exact h _ hi

theorem flipStep_mono (K n k Lm : Nat) {T T' : Nat} (h : Mono T T') :
    Mono (flipStep K n k Lm T) (flipStep K n k Lm T') := by
  unfold flipStep
  refine mono_or (mono_or (mono_or (mono_or (mono_or (mono_or (mono_or ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_
  all_goals (repeat (first | exact h | apply mono_and | apply mono_shl | apply mono_shr))

theorem sweep_mono (K : Nat) (a : Bool) : ∀ k {T T' : Nat}, Mono T T' →
    Mono (sweep K a k T) (sweep K a k T')
  | 0, _, _, h => h
  | k + 1, _, _, h => sweep_mono K a k (flipStep_mono _ _ _ _ h)

/-- `S ⊆ S'` on strip states. -/
def SubK (K S S' : Nat) : Prop := ∀ i, i < 2 ^ K → S.testBit i = true → S'.testBit i = true

theorem fimage_mono (K : Nat) (a : Bool) {S S' : Nat} (h : SubK K S S') :
    Mono (fimage K a S) (fimage K a S') := by
  have h0 : Mono (S &&& fullSet K) (S' &&& fullSet K) := by
    intro i hi
    rw [Nat.testBit_and, Bool.and_eq_true, testBit_fullSet, decide_eq_true_eq] at hi
    rw [Nat.testBit_and, h i hi.2 hi.1, testBit_fullSet, decide_eq_true hi.2]; rfl
  unfold fimage
  exact mono_and _ (mono_or (sweep_mono K a K (mono_or h0 (mono_shl _ h0)))
    (mono_shr _ (sweep_mono K a K (mono_or h0 (mono_shl _ h0)))))

theorem SubK.of_mono {K S S' : Nat} (h : Mono S S') : SubK K S S' := fun i _ hi => h i hi

theorem SubK.trans {K A B C : Nat} (h1 : SubK K A B) (h2 : SubK K B C) : SubK K A C :=
  fun i hi ha => h2 i hi (h1 i hi ha)

theorem SubK.refl (K S : Nat) : SubK K S S := fun _ _ h => h

/-- Apply a driver word with the bit-parallel image. -/
def fapply (K : Nat) : List Bool → Nat → Nat
  | [], S => S
  | a :: u, S => fapply K u (fimage K a S)

theorem fapply_mono (K : Nat) : ∀ (u : List Bool) {S S' : Nat}, SubK K S S' →
    SubK K (fapply K u S) (fapply K u S')
  | [], _, _, h => h
  | a :: u, _, _, h => fapply_mono K u (SubK.of_mono (fimage_mono K a h))

theorem fapply_append (K : Nat) (u v : List Bool) (S : Nat) :
    fapply K (u ++ v) S = fapply K v (fapply K u S) := by
  induction u generalizing S with
  | nil => rfl
  | cons a u ih => exact ih (fimage K a S)

theorem enc_fapply {K : Nat} {j : Int} :
    ∀ (u : List Bool) (t r S : Nat), Enc K t j r → S.testBit r = true →
      (∀ s, s < u.length → cell (t + s) j = u.getD s false) →
      ∃ r', Enc K (t + u.length) j r' ∧ (fapply K u S).testBit r' = true
  | [], t, r, S, he, hS, _ => ⟨r, he, hS⟩
  | a :: u, t, r, S, he, hS, hu => by
    have ha : cell t j = a := by simpa using hu 0 (by simp)
    have he1 := enc_step he
    rw [ha] at he1
    have hS1 : (fimage K a S).testBit (stripStep K a (cell t (j + 1 + K)) r) = true :=
      fimage_mem he.1 hS _
    obtain ⟨r', he', hS'⟩ := enc_fapply u (t + 1) _ _ he1 hS1 (fun s hs => by
      have := hu (s + 1) (by simp; omega)
      rw [show t + (s + 1) = t + 1 + s by omega] at this
      simpa using this)
    refine ⟨r', ?_, hS'⟩
    rw [show t + (a :: u).length = t + 1 + u.length by simp; omega]
    exact he'

/-- `k` repetitions of the word. -/
def fiter (K : Nat) (w : List Bool) : Nat → Nat → Nat
  | 0, S => S
  | k + 1, S => fiter K w k (fapply K w S)

theorem enc_fiter {K : Nat} {j : Int} (w : List Bool) :
    ∀ (k t r S : Nat), Enc K t j r → S.testBit r = true →
      (∀ m s, m < k → s < w.length → cell (t + m * w.length + s) j = w.getD s false) →
      ∃ r', Enc K (t + k * w.length) j r' ∧ (fiter K w k S).testBit r' = true
  | 0, t, r, S, he, hS, _ => ⟨r, by simpa using he, hS⟩
  | k + 1, t, r, S, he, hS, hw => by
    obtain ⟨r1, he1, hS1⟩ := enc_fapply w t r S he hS (fun s hs => by
      simpa using hw 0 s (by omega) hs)
    obtain ⟨r', he', hS'⟩ := enc_fiter w k (t + w.length) r1 _ he1 hS1 (fun m s hm hs => by
      rw [show t + w.length + m * w.length + s = t + (m + 1) * w.length + s by
        rw [Nat.succ_mul]; omega]
      exact hw (m + 1) s (by omega) hs)
    refine ⟨r', ?_, hS'⟩
    rw [show t + (k + 1) * w.length = t + w.length + k * w.length by rw [Nat.succ_mul]; omega]
    exact he'

/-! Bit-parallel set tests. -/

/-- `S ⊆ S'` on the `2 ^ K` strip states. -/
def subB (K S S' : Nat) : Bool := S &&& (fullSet K ^^^ (S' &&& fullSet K)) == 0

/-- Column `1` (bit `0` of the strip) equals `b` on every state of `S`. -/
def colC (K S : Nat) (b : Bool) : Bool := S &&& (if b then fullSet K ^^^ bm 0 K else bm 0 K) == 0

theorem subB_spec {K S S' : Nat} (h : subB K S S' = true) : SubK K S S' := by
  intro r hr hS
  have h0 : S &&& (fullSet K ^^^ (S' &&& fullSet K)) = 0 := by simpa [subB] using h
  have := congrArg (fun x => x.testBit r) h0
  simp only [Nat.testBit_and, Nat.testBit_xor, testBit_fullSet, hr, hS, Nat.zero_testBit,
    decide_true, Bool.and_true, Bool.true_and] at this
  cases h' : S'.testBit r
  · rw [h'] at this; exact absurd this (by decide)
  · rfl

theorem subB_of {K S S' : Nat} (h : SubK K S S') : subB K S S' = true := by
  have h0 : S &&& (fullSet K ^^^ (S' &&& fullSet K)) = 0 := by
    apply Nat.eq_of_testBit_eq; intro r
    simp only [Nat.testBit_and, Nat.testBit_xor, testBit_fullSet, Nat.zero_testBit]
    by_cases hr : r < 2 ^ K
    · cases hS : S.testBit r
      · rfl
      · simp [hr, h r hr hS]
    · simp [hr]
  simp [subB, h0]

theorem colC_spec {K S : Nat} {b : Bool} (h : colC K S b = true) {r : Nat} (hr : r < 2 ^ K)
    (hS : S.testBit r = true) : r.testBit 0 = b := by
  have h0 : S &&& (if b then fullSet K ^^^ bm 0 K else bm 0 K) = 0 := by simpa [colC] using h
  have h1 : (S &&& (if b then fullSet K ^^^ bm 0 K else bm 0 K)).testBit r = false := by
    rw [h0]; exact Nat.zero_testBit r
  have hm : (bm 0 K).testBit r = r.testBit 0 := by rw [testBit_bm]; simp [hr]
  have hf : (fullSet K).testBit r = true := by rw [testBit_fullSet]; simp [hr]
  rw [Nat.testBit_and, hS, Bool.true_and] at h1
  cases b
  · rw [ite_eq_right (by decide), hm] at h1; exact h1
  · rw [ite_eq_left rfl, Nat.testBit_xor, hf, hm] at h1
    cases hb : r.testBit 0 <;> simp_all

theorem colC_mono {K S S' : Nat} {b : Bool} (hsub : SubK K S S') (h : colC K S' b = true) :
    colC K S b = true := by
  have h0 : S &&& (if b then fullSet K ^^^ bm 0 K else bm 0 K) = 0 := by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and, Nat.zero_testBit]
    by_cases hr : r < 2 ^ K
    · cases hS : S.testBit r
      · rfl
      · have := colC_spec h hr (hsub r hr hS)
        cases b <;> simp [Nat.testBit_xor, testBit_fullSet, testBit_bm, hr, this]
    · cases b <;> simp [Nat.testBit_xor, testBit_fullSet, testBit_bm, hr]
  simp [colC, h0]

/-- The encoding of a strip is unique. -/
theorem enc_unique {K t : Nat} {j : Int} {r r' : Nat} (h : Enc K t j r) (h' : Enc K t j r') : r = r' := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < K
  · rw [h.2 i hi, h'.2 i hi]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h.1 (Nat.pow_le_pow_right (by omega) (by omega))),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h'.1 (Nat.pow_le_pow_right (by omega) (by omega)))]


/-- **Mode certificate.** `S0` is the strip set after `k` warm-up periods of `w`, mapped into
itself by one more period. At every white phase other than `pe`, column `1` is constant on the
corresponding set (as in `stripCert`). At the phase `pe` column `1` is a label of the strip at the
start of the period: `1` on `E1`, `0` on `E0`, and `E0 ∪ E1` covers `S0`. The labels obey two
transition rules: after a `1` comes a `0`, and after `0 0` comes a `0`. -/
def modeCert (w : List Bool) (K k pe S0 E0 E1 : Nat) : Bool :=
  subB K (fiter K w k (fullSet K)) S0 &&
  subB K (fapply K w S0) S0 &&
  ((List.range w.length).all fun φ => w.getD φ false || φ == pe ||
      colC K (fapply K (w.take φ) S0) false || colC K (fapply K (w.take φ) S0) true) &&
  decide (pe < w.length) && !(w.getD pe false) &&
  subB K S0 (E0 ||| E1) &&
  colC K (fapply K (w.take pe) E1) true &&
  colC K (fapply K (w.take pe) E0) false &&
  subB K (fapply K w E1) E0 &&
  subB K (fapply K w (fapply K w E0 &&& E0)) E0

/-- **Soundness of mode certificates.** -/
theorem not_eventually_word_mode (w : List Bool) (K k pe S0 E0 E1 : Nat) (hK : 1 ≤ K)
    (hw : 0 < w.length) (hcert : modeCert w K k pe S0 E0 E1 = true) : ¬ EventuallyWord w := by
  rintro ⟨T, hT⟩
  unfold modeCert at hcert
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hcert
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hini, hsub⟩, hforce⟩, hpe⟩, hpew⟩, hcov⟩, hl1⟩, hl0⟩, hd1⟩, hd2⟩ := hcert
  have hblock : ∀ m s, s < w.length → cell (T + m * w.length + s) 0 = w.getD s false := by
    intro m s hs
    rw [hT _ (by omega), show T + m * w.length + s - T = s + m * w.length by omega,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]
  have hcper : ∀ t, T ≤ t → cell (t + w.length) 0 = cell t 0 := by
    intro t ht
    rw [hT t ht, hT (t + w.length) (by omega), show t + w.length - T = (t - T) + w.length by omega,
      Nat.add_mod_right]
  -- the strip at the start of period `m` (after warm-up)
  let R : Nat → Nat := fun m => encRow (T + (k + m) * w.length) 0 K
  have hR : ∀ m, Enc K (T + (k + m) * w.length) 0 (R m) := fun m => enc_encRow K _ 0
  have htime : ∀ m, T + (k + m) * w.length + w.length = T + (k + (m + 1)) * w.length := by
    intro m; rw [show k + (m + 1) = (k + m) + 1 by omega, Nat.succ_mul]; omega
  -- one period maps membership forward
  have hstep : ∀ m X, X.testBit (R m) = true → (fapply K w X).testBit (R (m + 1)) = true := by
    intro m X hX
    obtain ⟨r', he', hS'⟩ := enc_fapply w _ (R m) X (hR m) hX (fun s hs => hblock (k + m) s hs)
    rw [htime m] at he'
    rw [enc_unique (hR (m + 1)) he']
    exact hS'
  -- the strip is in `S0` at every period start
  have hS0 : ∀ m, S0.testBit (R m) = true := by
    have hstart : ∃ r, Enc K (T + k * w.length) 0 r ∧ (fiter K w k (fullSet K)).testBit r = true := by
      have h0 := enc_encRow K T 0
      have hfull : (fullSet K).testBit (encRow T 0 K) = true := by
        unfold fullSet; rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true h0.1
      exact enc_fiter w k T _ _ h0 hfull (fun m s _ hs => hblock m s hs)
    intro m
    induction m with
    | zero =>
      obtain ⟨r, he, hS⟩ := hstart
      rw [enc_unique (hR 0) (by simpa using he)]; exact subB_spec hini _ he.1 hS
    | succ m ih =>
      exact subB_spec hsub _ (hR (m + 1)).1 (hstep m _ ih)
  -- the column-1 value at phase `φ` of period `m` is read from the strip set reached from `X`
  have hread : ∀ m φ X, φ < w.length → X.testBit (R m) = true →
      ∃ r', r' < 2 ^ K ∧ (fapply K (w.take φ) X).testBit r' = true ∧
        cell (T + (k + m) * w.length + φ) 1 = r'.testBit 0 := by
    intro m φ X hφ hX
    obtain ⟨r', he', hS'⟩ := enc_fapply (w.take φ) _ (R m) X (hR m) hX (fun s hs => by
      rw [List.length_take] at hs
      have hs' : s < φ := by omega
      rw [hblock _ s (by omega)]
      simp [List.getD_eq_getElem?_getD, hs'])
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hφ)] at he'
    refine ⟨r', he'.1, hS', ?_⟩
    rw [he'.2 0 (by omega)]; rfl
  -- labels
  let ℓ : Nat → Bool := fun m => cell (T + (k + m) * w.length + pe) 1
  have hlab1 : ∀ m, E1.testBit (R m) = true → ℓ m = true := by
    intro m h
    obtain ⟨r', hr', hS', hc⟩ := hread m pe E1 hpe h
    show cell _ 1 = true
    rw [hc]; exact colC_spec hl1 hr' hS'
  have hlab0 : ∀ m, E0.testBit (R m) = true → ℓ m = false := by
    intro m h
    obtain ⟨r', hr', hS', hc⟩ := hread m pe E0 hpe h
    show cell _ 1 = false
    rw [hc]; exact colC_spec hl0 hr' hS'
  have hcover : ∀ m, E0.testBit (R m) = true ∨ E1.testBit (R m) = true := by
    intro m
    have := subB_spec hcov _ (hR m).1 (hS0 m)
    rw [Nat.testBit_or, Bool.or_eq_true] at this
    exact this
  have hd1' : ∀ m, E1.testBit (R m) = true → E0.testBit (R (m + 1)) = true :=
    fun m h => subB_spec hd1 _ (hR (m + 1)).1 (hstep m E1 h)
  have hd2' : ∀ m, E0.testBit (R m) = true → E0.testBit (R (m + 1)) = true →
      E0.testBit (R (m + 2)) = true := by
    intro m h0 h1
    have ha : (fapply K w E0 &&& E0).testBit (R (m + 1)) = true := by
      rw [Nat.testBit_and, hstep m E0 h0, h1]; rfl
    exact subB_spec hd2 _ (hR (m + 2)).1 (hstep (m + 1) _ ha)
  -- the labels are eventually 2-periodic
  have hper2 : ∃ m0, ∀ m, m0 ≤ m → ℓ (m + 2) = ℓ m := by
    by_cases hA : ∃ m, E0.testBit (R m) = true ∧ E0.testBit (R (m + 1)) = true
    · obtain ⟨m0, h0, h1⟩ := hA
      have hall : ∀ n, E0.testBit (R (m0 + n)) = true ∧ E0.testBit (R (m0 + n + 1)) = true := by
        intro n
        induction n with
        | zero => exact ⟨h0, h1⟩
        | succ n ih =>
          refine ⟨by simpa [Nat.add_assoc] using ih.2, ?_⟩
          have := hd2' (m0 + n) ih.1 ih.2
          simpa [Nat.add_assoc] using this
      refine ⟨m0, fun m hm => ?_⟩
      obtain ⟨n, rfl⟩ : ∃ n, m = m0 + n := ⟨m - m0, by omega⟩
      rw [hlab0 _ (hall n).1, hlab0 _ (by simpa [Nat.add_assoc] using (hall (n + 1)).2)]
    · have hB : ∀ m, E0.testBit (R m) = true → E0.testBit (R (m + 1)) = true → False :=
        fun m h0 h1 => hA ⟨m, h0, h1⟩
      refine ⟨0, fun m _ => ?_⟩
      by_cases h1 : E1.testBit (R m) = true
      · have h0' := hd1' m h1
        have h2 : E1.testBit (R (m + 2)) = true := by
          rcases hcover (m + 2) with h | h
          · exact absurd (hB (m + 1) h0' h) id
          · exact h
        rw [hlab1 _ h1, hlab1 _ h2]
      · have h0 : E0.testBit (R m) = true := by
          rcases hcover m with h | h
          · exact h
          · exact absurd h h1
        have h1' : E1.testBit (R (m + 1)) = true := by
          rcases hcover (m + 1) with h | h
          · exact absurd (hB m h0 h) id
          · exact h
        rw [hlab0 _ h0, hlab0 _ (hd1' (m + 1) h1')]
  obtain ⟨m0, hm0⟩ := hper2
  -- column `1` at the other white phases is forced
  have hforced : ∀ m φ, φ < w.length → w.getD φ false = false → φ ≠ pe →
      cell (T + (k + m) * w.length + φ) 1 =
        !colC K (fapply K (w.take φ) S0) false := by
    intro m φ hφ hwφ hne
    obtain ⟨r', hr', hS', hc⟩ := hread m φ _ hφ (hS0 m)
    rw [hc]
    have hf := List.all_eq_true.mp hforce φ (List.mem_range.mpr hφ)
    rw [hwφ, Bool.false_or, show (φ == pe) = false from beq_false_of_ne hne, Bool.false_or] at hf
    cases hc0 : colC K (fapply K (w.take φ) S0) false
    · rw [hc0, Bool.false_or] at hf
      rw [colC_spec hf hr' hS']; rfl
    · rw [colC_spec hc0 hr' hS']; rfl
  -- `orCol 0` repeats with period `2 |w|` along the periods
  have hrep : ∀ m φ, m0 ≤ m → φ < w.length →
      orCol 0 (T + (k + (m + 2)) * w.length + φ) = orCol 0 (T + (k + m) * w.length + φ) := by
    intro m φ hm hφ
    unfold orCol
    simp only [Int.zero_add]
    rw [hblock (k + (m + 2)) φ hφ, hblock (k + m) φ hφ]
    cases hwφ : w.getD φ false
    · simp only [Bool.false_or]
      by_cases hne : φ = pe
      · subst hne
        exact hm0 m hm
      · rw [hforced (m + 2) φ hφ hwφ hne, hforced m φ hφ hwφ hne]
    · rfl
  refine orCol_not_eventuallyPeriodic 0 ⟨T, w.length, hw, hcper⟩
    ⟨T + (k + m0) * w.length, 2 * w.length, by omega, fun t ht => ?_⟩
  show orCol 0 (t + 2 * w.length) = orCol 0 t
  have hφ : (t - T) % w.length < w.length := Nat.mod_lt _ hw
  have hq : k + m0 ≤ (t - T) / w.length := (Nat.le_div_iff_mul_le hw).2 (by omega)
  have hdec : t = T + (k + ((t - T) / w.length - k)) * w.length + (t - T) % w.length := by
    have hd := Nat.div_add_mod (t - T) w.length
    rw [show k + ((t - T) / w.length - k) = (t - T) / w.length by omega, Nat.mul_comm]
    omega
  have h2 := hrep ((t - T) / w.length - k) ((t - T) % w.length) (by omega) hφ
  rw [← hdec] at h2
  rw [← h2]
  congr 1
  rw [show k + ((t - T) / w.length - k + 2) = (k + ((t - T) / w.length - k)) + 2 by omega,
    Nat.add_mul]
  omega

/-! ## Pumping over the white run -/

/-- The word `1 0^q`. -/
def wq (q : Nat) : List Bool := true :: List.replicate q false

/-- `n` white steps. -/
def fzeros (K n S : Nat) : Nat := fapply K (List.replicate n false) S

/-- Column `1` is constant on `S`. -/
def forces (K S : Nat) : Bool := colC K S false || colC K S true

/-- The label masks: column `1` two steps after a black driver cell is white exactly when the strip
starts with `1` and has a `1` among its next two cells. -/
def lab0 (K : Nat) : Nat := bm 0 K &&& (bm 1 K ||| bm 2 K)

def lab1 (K : Nat) : Nat := fullSet K ^^^ lab0 K

/-- The strips reachable after `k` periods of `1 0^q`: the same formula for every `q`. -/
def reach (K k q : Nat) : Nat := fiter K (wq q) k (fullSet K)

/-- Close a set under white steps (at most `f` rounds). -/
def closeW (K : Nat) : Nat → Nat → Nat
  | 0, Z => Z
  | f + 1, Z => if subB K (fimage K false Z) Z then Z else closeW K f (Z ||| fimage K false Z)

/-- A set containing every `fzeros K n (fimage K true S)` with `n ≥ M`, once it is checked closed. -/
def pumpSet (K M S : Nat) : Nat := closeW K (2 ^ K) (fzeros K M (fimage K true S))

/-- The warm-up chain of pumped sets, shared by every `q ≥ M`. -/
def chainU (K M : Nat) : Nat → Nat
  | 0 => fullSet K
  | i + 1 => pumpSet K M (chainU K M i)

/-- **The pumped check**, independent of `q`. -/
def pumpCheck (K M k : Nat) : Bool :=
  (List.range k).all (fun i =>
      subB K (fzeros K M (fimage K true (chainU K M i))) (chainU K M (i + 1)) &&
      subB K (fimage K false (chainU K M (i + 1))) (chainU K M (i + 1))) &&
  subB K (chainU K M k) (lab0 K) &&
  (List.range M).all (fun j => j == 1 || forces K (fzeros K j (fimage K true (chainU K M k)))) &&
  subB K (fzeros K M (fimage K true (chainU K M k))) (pumpSet K M (chainU K M k)) &&
  subB K (fimage K false (pumpSet K M (chainU K M k))) (pumpSet K M (chainU K M k)) &&
  forces K (pumpSet K M (chainU K M k)) &&
  colC K (fapply K [true, false] (lab1 K)) true &&
  colC K (fapply K [true, false] (lab0 K)) false

theorem fzeros_closed {K Z : Nat} (hZ : SubK K (fimage K false Z) Z) :
    ∀ n X, SubK K X Z → SubK K (fzeros K n X) Z
  | 0, _, h => h
  | n + 1, X, h => fzeros_closed hZ n (fimage K false X)
      ((SubK.of_mono (fimage_mono K false h)).trans hZ)

theorem fzeros_add (K m n X : Nat) : fzeros K (m + n) X = fzeros K n (fzeros K m X) := by
  unfold fzeros; rw [← List.replicate_append_replicate, fapply_append]

/-- One period of `1 0^q`, `q ≥ M`, lands in a closed set containing the `M`-step image. -/
theorem period_sub {K M X Z : Nat} (h1 : SubK K (fzeros K M (fimage K true X)) Z)
    (h2 : SubK K (fimage K false Z) Z) {q : Nat} (hq : M ≤ q) : SubK K (fapply K (wq q) X) Z := by
  have : fapply K (wq q) X = fzeros K (q - M) (fzeros K M (fimage K true X)) := by
    rw [← fzeros_add, show M + (q - M) = q by omega]; rfl
  rw [this]; exact fzeros_closed h2 _ _ h1

theorem fiter_mono (K : Nat) (w : List Bool) : ∀ k {S S' : Nat}, SubK K S S' →
    SubK K (fiter K w k S) (fiter K w k S')
  | 0, _, _, h => h
  | k + 1, _, _, h => fiter_mono K w k (fapply_mono K w h)

theorem fapply_fiter (K : Nat) (w : List Bool) : ∀ k S,
    fapply K w (fiter K w k S) = fiter K w k (fapply K w S)
  | 0, _ => rfl
  | k + 1, S => fapply_fiter K w k (fapply K w S)

theorem sub_fullSet (K S : Nat) : SubK K S (fullSet K) := by
  intro i hi _; rw [testBit_fullSet]; exact decide_eq_true hi

theorem forces_mono {K S S' : Nat} (h : SubK K S S') (hf : forces K S' = true) : forces K S = true := by
  unfold forces at *
  rw [Bool.or_eq_true] at hf ⊢
  exact hf.imp (colC_mono h) (colC_mono h)

theorem chain_sub {K M : Nat} {w : List Bool} (k0 : Nat)
    (hstep : ∀ i, i < k0 → SubK K (fapply K w (chainU K M i)) (chainU K M (i + 1))) :
    ∀ k i S, i + k ≤ k0 → SubK K S (chainU K M i) → SubK K (fiter K w k S) (chainU K M (i + k))
  | 0, _, _, _, h => h
  | k + 1, i, S, hk, h => by
    have := chain_sub k0 hstep k (i + 1) (fapply K w S) (by omega)
      ((fapply_mono K w h).trans (hstep i (by omega)))
    rwa [show i + 1 + k = i + (k + 1) by omega] at this

theorem getD_wq (q j : Nat) : (wq q).getD j false = decide (j = 0) := by
  cases j with
  | zero => rfl
  | succ j =>
    unfold wq; rw [List.getD_cons_succ, List.getD_eq_getElem?_getD]
    by_cases h : j < q
    · simp [h]
    · simp [h]

/-- **Pumping.** If the `q`-independent check passes, the mode certificate built from the reachable
sets holds for every `q ≥ M`. -/
theorem modeCert_pumped (K M k : Nat) (hM : 2 ≤ M) (h : pumpCheck K M k = true) (q : Nat)
    (hq : M ≤ q) :
    modeCert (wq q) K k 2 (reach K k q) (reach K k q &&& lab0 K) (reach K k q &&& lab1 K) = true := by
  unfold pumpCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hchain, hU0⟩, hpre⟩, hZ1⟩, hZ2⟩, hZf⟩, hl1⟩, hl0⟩ := h
  have hstep : ∀ i, i < k → SubK K (fapply K (wq q) (chainU K M i)) (chainU K M (i + 1)) :=
    fun i hi => period_sub (subB_spec (hchain i hi).1) (subB_spec (hchain i hi).2) hq
  have hRU : SubK K (reach K k q) (chainU K M k) := by
    have := chain_sub k hstep k 0 (fullSet K) (by omega) (SubK.refl _ _)
    unfold reach; simpa using this
  have hFR : SubK K (fapply K (wq q) (reach K k q)) (reach K k q) := by
    unfold reach; rw [fapply_fiter]; exact fiter_mono K _ k (sub_fullSet K _)
  have hRL : SubK K (reach K k q) (lab0 K) := hRU.trans (subB_spec hU0)
  have hlen : (wq q).length = q + 1 := by simp [wq]
  have htake2 : (wq q).take 2 = [true, false] := by
    unfold wq
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rfl
  unfold modeCert
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨subB_of (SubK.refl _ _), subB_of hFR⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · -- forcing at the white phases
    rw [List.all_eq_true]
    intro φ hφ
    rw [List.mem_range, hlen] at hφ
    rw [getD_wq]
    cases φ with
    | zero => rfl
    | succ j =>
      by_cases hj1 : j = 1
      · subst hj1; simp
      have htake : (wq q).take (j + 1) = true :: List.replicate j false := by
        unfold wq; rw [List.take_succ_cons, List.take_replicate, Nat.min_eq_left (by omega)]
      rw [htake]
      have hsub : SubK K (fapply K (true :: List.replicate j false) (reach K k q))
          (fzeros K j (fimage K true (chainU K M k))) :=
        fapply_mono K (List.replicate j false) (SubK.of_mono (fimage_mono K true hRU))
      have hf : forces K (fzeros K j (fimage K true (chainU K M k))) = true ∨
          SubK K (fzeros K j (fimage K true (chainU K M k))) (pumpSet K M (chainU K M k)) := by
        by_cases hjM : j < M
        · left
          have := hpre j hjM
          rw [Bool.or_eq_true] at this
          rcases this with h1 | h1
          · exact absurd (beq_iff_eq.mp h1) hj1
          · exact h1
        · right
          rw [show j = M + (j - M) by omega, fzeros_add]
          exact fzeros_closed (subB_spec hZ2) _ _ (subB_spec hZ1)
      have hfin : forces K (fapply K (true :: List.replicate j false) (reach K k q)) = true := by
        rcases hf with hf | hf
        · exact forces_mono hsub hf
        · exact forces_mono (hsub.trans hf) hZf
      unfold forces at hfin
      rw [Bool.or_eq_true] at hfin
      rcases hfin with h | h <;> simp [h]
  · simp [hlen]; omega
  · rw [getD_wq]; rfl
  · -- the labels cover the reachable set
    apply subB_of
    intro i hi hR
    simp only [Nat.testBit_or, Nat.testBit_and, hR, Bool.true_and, lab1, Nat.testBit_xor,
      testBit_fullSet, hi, decide_true]
    cases (lab0 K).testBit i <;> rfl
  · rw [htake2]
    exact colC_mono (fapply_mono K _ (fun i _ h => by
      rw [Nat.testBit_and, Bool.and_eq_true] at h; exact h.2)) hl1
  · rw [htake2]
    exact colC_mono (fapply_mono K _ (fun i _ h => by
      rw [Nat.testBit_and, Bool.and_eq_true] at h; exact h.2)) hl0
  · apply subB_of
    intro i hi hm
    have hR : (reach K k q).testBit i = true :=
      hFR i hi (fapply_mono K _ (fun i _ h => by
        rw [Nat.testBit_and, Bool.and_eq_true] at h; exact h.1) i hi hm)
    rw [Nat.testBit_and, hR, hRL i hi hR]; rfl
  · apply subB_of
    intro i hi hm
    have hR : (reach K k q).testBit i = true :=
      hFR i hi (fapply_mono K _ (fun i _ h => by
        rw [Nat.testBit_and, Nat.testBit_and, Bool.and_eq_true, Bool.and_eq_true] at h
        exact h.2.1) i hi hm)
    rw [Nat.testBit_and, hR, hRL i hi hR]; rfl

/-! ## The instance: width `12`, `M = 10`, five warm-up periods -/

set_option maxRecDepth 100000 in
/-- The `q`-independent check, decided by the kernel. -/
theorem pumpCheck_12 : pumpCheck 12 10 5 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The pumped check fails when started at nine white steps: its sets contain strips with label `1`. -/
theorem pumpCheck_12_nine : pumpCheck 12 9 5 = false := by decide +kernel

set_option maxRecDepth 100000 in
/-- The same certificate formula at `q = 9`, decided by the kernel. -/
theorem modeCert_nine :
    modeCert (wq 9) 12 5 2 (reach 12 5 9) (reach 12 5 9 &&& lab0 12) (reach 12 5 9 &&& lab1 12) = true := by
  decide +kernel

/-- **One mode certificate for every `q ≥ 9`.** -/
theorem modeCert_white_end (q : Nat) (hq : 9 ≤ q) :
    modeCert (wq q) 12 5 2 (reach 12 5 q) (reach 12 5 q &&& lab0 12) (reach 12 5 q &&& lab1 12) = true := by
  rcases Nat.lt_or_ge q 10 with h | h
  · obtain rfl : q = 9 := by omega
    exact modeCert_nine
  · exact modeCert_pumped 12 10 5 (by decide) pumpCheck_12 q h

/-- **The white end from `q = 9`.** For every `q ≥ 9`, the center column of the single-seed pattern
is not eventually the repeating word `1 0^q`, whatever the transient. -/
theorem not_eventually_white_end_ge9 (q : Nat) (hq : 9 ≤ q) :
    ¬ EventuallyWord (true :: List.replicate q false) :=
  not_eventually_word_mode (wq q) 12 5 2 _ _ _ (by decide) (by simp [wq]) (modeCert_white_end q hq)

/-! ## Semigroup additivity of `fiter`, `subB` equivalence, and exclusion of `0^q 1` for all `q ≥ 9` -/

/-- **Semigroup Additivity of `fiter` and Exact Subset Equivalence `subB K S S' = true ↔ SubK K S S'` (`fiter_add_and_subB_iff`).** -/
theorem fiter_add_and_subB_iff (K : Nat) (w : List Bool) (a b S S' : Nat) :
    fiter K w (a + b) S = fiter K w b (fiter K w a S) ∧
    (subB K S S' = true ↔ SubK K S S') := by
  refine ⟨?_, ⟨subB_spec, subB_of⟩⟩
  induction a generalizing S with
  | zero => simp [fiter]
  | succ a ih =>
    rw [Nat.succ_add]
    exact ih (fapply K w S)

/-- **Exact `getD` Formula for `0^q 1` (`getD_replicate_false_append_true`).** -/
theorem getD_replicate_false_append_true : ∀ (q k : Nat),
    (List.replicate q false ++ [true]).getD k false = decide (k = q)
  | 0, 0 => rfl
  | 0, k + 1 => rfl
  | q + 1, 0 => rfl
  | q + 1, k + 1 => by
    rw [List.replicate_succ, List.cons_append, List.getD_cons_succ,
        getD_replicate_false_append_true q k]
    exact decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩

/-- **Unconditional Exclusion of `0^q 1` (`List.replicate q false ++ [true]`) for Every `q ≥ 9` (`not_eventually_oneBlack_ge9`).** -/
theorem not_eventually_oneBlack_ge9 (q : Nat) (hq : 9 ≤ q) :
    ¬ EventuallyWord (List.replicate q false ++ [true]) := by
  rintro ⟨T, hT⟩
  have hlen1 : (List.replicate q false ++ [true]).length = q + 1 := by simp
  have hlen2 : (true :: List.replicate q false).length = q + 1 := by simp
  apply not_eventually_white_end_ge9 q hq
  refine ⟨T + q, fun t ht => ?_⟩
  rw [hT t (by omega), hlen1, hlen2, getD_replicate_false_append_true, show true :: List.replicate q false = wq q from rfl, getD_wq]
  let u := t - (T + q)
  have htu : t - T = u + q := by dsimp [u]; omega
  rw [htu]
  have hd := Nat.div_add_mod u (q + 1)
  have hm := Nat.mod_lt u (by omega : 0 < q + 1)
  generalize u / (q + 1) = k at hd
  generalize u % (q + 1) = r at hd hm ⊢
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  · have heq : u + q = q + (q + 1) * k := by omega
    rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega : q < q + 1), hr0]
    simp
  · have heq : u + q = (r - 1) + (q + 1) * (k + 1) := by
      rw [Nat.mul_add, Nat.mul_one]; omega
    rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega : r - 1 < q + 1)]
    exact decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩

end Rule30WhiteEndNine
end Ruliology.CellularAutomata
