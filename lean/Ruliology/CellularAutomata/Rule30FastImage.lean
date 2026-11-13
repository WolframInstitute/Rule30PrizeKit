module
public import Ruliology.CellularAutomata.Rule30RunEnvelopes
/-!
# Bit-parallel images for strip-envelope checks

Ported from Rule30WhiteEndNine, with the same generic fimage and fimage_mem proof.
One sweep updates every member of a strip set at once; fcovers_sound returns the
ordinary strip image inclusion consumed by the existing envelope/pumping proofs.
Thus this is a faster checker for the same transitions, with no new assumption.
The original sparse checker remains available for arbitrary predicates.
-/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30FastImage
open Rule30Jen Rule30Prize Rule30MaskedJen Rule30StripCertificates Rule30RunEnvelopes
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


/-- Test an inclusion using a bit-parallel overapproximation of all successors. -/
def fcovers (K : Nat) (a : Bool) (A B : Nat) : Bool :=
  fimage K a A &&& B == fimage K a A

/-- Soundness with respect to the existing strip image (all widths and both boundary values). -/
theorem fcovers_sound {K : Nat} {a : Bool} {A B : Nat}
    (hc : fcovers K a A B = true) : Sub (image K a A) B := by
  have he : fimage K a A &&& B = fimage K a A := by simpa [fcovers] using hc
  apply imageAux_forall K a A (fun y => B.testBit y = true) _ (2^K) (by omega)
  intro s hs hm z
  have hf := fimage_mem (a := a) hs hm z
  have hb := congrArg (fun n : Nat => n.testBit (stripStep K a z s)) he
  rw [Nat.testBit_and, hf, Bool.true_and] at hb
  exact hb

/-! ## Fundamental inclusions `Sub (image K a S) (fimage K a S)` and `Sub (fimage K a S) (fullSet K)`, and `fcovers` equivalence -/

/-- **Fundamental Inclusions for `fimage` and Exact `fcovers` Equivalence (`image_sub_fimage_and_fcovers_iff_sub`).** -/
theorem image_sub_fimage_and_fcovers_iff_sub (K : Nat) (a : Bool) (S A B : Nat) :
    Sub (image K a S) (fimage K a S) ∧
    Sub (fimage K a S) (fullSet K) ∧
    (fcovers K a A B = true ↔ Sub (fimage K a A) B) := by
  refine ⟨?_, fun s hs => ?_, ⟨fun hc s hs => ?_, fun h => ?_⟩⟩
  · apply imageAux_forall K a S (fun y => (fimage K a S).testBit y = true) _ (2 ^ K) (by omega)
    intro s hs hm z
    exact fimage_mem hs hm z
  · unfold fimage at hs
    simp only [Nat.testBit_and, Bool.and_eq_true] at hs
    exact hs.2
  · have he : fimage K a A &&& B = fimage K a A := by simpa [fcovers] using hc
    have hbit := congrArg (fun n : Nat => n.testBit s) he
    rw [Nat.testBit_and, hs, Bool.true_and] at hbit
    exact hbit
  · simp only [fcovers, beq_iff_eq]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases hf : (fimage K a A).testBit i
    · simp
    · simp [h i hf]

end Ruliology.CellularAutomata.Rule30FastImage
