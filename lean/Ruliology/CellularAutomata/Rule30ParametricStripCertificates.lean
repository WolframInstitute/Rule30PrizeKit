module

public import Ruliology.CellularAutomata.Rule30StripCertificates
public import Ruliology.CellularAutomata.Rule30StripCertificateTable
public import Ruliology.CellularAutomata.Rule30FiniteMaskedJen
public import Ruliology.CellularAutomata.Rule30FiniteConfigs
public import Ruliology.CellularAutomata.Rule30PeriodTwoSideways

/-!
# Parametric Strip Certificates and Semigroup Saturation in Rule 30

This module introduces semigroup saturation (`iterAtLeast`, `paramStripCert`) on 2^K-bit masks
for strip certificates in Rule 30, lifting certificate evaluations from single repeating words
to entire infinite families a^r ++ u for all r ≥ r0 and all transients.

## Headline theorems
- `paramStripCert`: bitmask semigroup saturation checker for infinite families `a^r ++ u` (`r ≥ r0`).
- `not_eventually_param_word`: a single certified `paramStripCert` excludes `a^r ++ u` for all `r ≥ r0`.
- `not_eventually_paramBlackTable`: excludes 14 infinite black-run families `1^r ++ u` (`r ≥ 8, 9, 15`),
  lowering the thresholds of Theorem B′ in `Rule30BlackRunBlocks`.
- `not_eventually_word_strip_finite`: lifts strip certificates to every column of every nonzero finite configuration.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30ParametricStripCertificates

open Rule30Jen Rule30Prize Rule30Realization Rule30PeriodTwoSideways
open Rule30FiniteConfigs Rule30FiniteMaskedJen
open Rule30StripCertificates Rule30StripCertificateTable

/-! ### List indexing lemmas for parametric words `List.replicate r a ++ u` -/

theorem getD_replicate (a : Bool) :
    ∀ (n s : Nat), s < n → (List.replicate n a).getD s false = a
  | 0, s, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, _ => rfl
  | n + 1, s + 1, h => getD_replicate a n s (by omega)

theorem getD_replicate_append_left (a : Bool) (u : List Bool) :
    ∀ (r s : Nat), s < r → (List.replicate r a ++ u).getD s false = a
  | 0, s, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, _ => rfl
  | r + 1, s + 1, h => getD_replicate_append_left a u r s (by omega)

theorem getD_replicate_append_right (a : Bool) (u : List Bool) :
    ∀ (r s : Nat), (List.replicate r a ++ u).getD (r + s) false = u.getD s false
  | 0, s => by simp
  | r + 1, s => by
    rw [show r + 1 + s = (r + s) + 1 by omega]
    exact getD_replicate_append_right a u r s

theorem getD_take :
    ∀ (u : List Bool) (ψ s : Nat), s < ψ → (u.take ψ).getD s false = u.getD s false
  | [], _, _, _ => by simp
  | _ :: _, 0, s, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, _ + 1, 0, _ => rfl
  | _ :: u, ψ + 1, s + 1, h => getD_take u ψ s (by omega)

/-! ### Strip encodings in the evolution of an arbitrary configuration -/

/-- Column `j` of `evol x` equals `w` repeated from time `T` on. -/
def EventuallyWordAt (x : Int → Bool) (j : Int) (w : List Bool) : Prop :=
  ∃ T, ∀ t, T ≤ t → evol x t j = w.getD ((t - T) % w.length) false

/-- The single black cell at position `0`. -/
def seed0 (p : Int) : Bool := decide (p = 0)

theorem evol_seed0 : ∀ (t : Nat) (p : Int), evol seed0 t p = cell t p
  | 0, _ => rfl
  | t + 1, p => by
    show rule (evol seed0 t (p - 1)) (evol seed0 t p) (evol seed0 t (p + 1)) =
      rule (cell t (p - 1)) (cell t p) (cell t (p + 1))
    rw [evol_seed0 t (p - 1), evol_seed0 t p, evol_seed0 t (p + 1)]

theorem eventuallyWordAt_seed0_iff (w : List Bool) :
    EventuallyWordAt seed0 0 w ↔ EventuallyWord w := by
  unfold EventuallyWordAt EventuallyWord
  simp only [evol_seed0]

/-- Strip encoding in `evol x`: `r < 2 ^ K` and bit `k < K` of `r` is `evol x t (j + 1 + k)`. -/
def EncAt (x : Int → Bool) (K t : Nat) (j : Int) (r : Nat) : Prop :=
  r < 2 ^ K ∧ ∀ k, k < K → r.testBit k = evol x t (j + 1 + k)

theorem encAt_step {x : Int → Bool} {K t : Nat} {j : Int} {r : Nat} (h : EncAt x K t j r) :
    EncAt x K (t + 1) j (stripStep K (evol x t j) (evol x t (j + 1 + K)) r) := by
  refine ⟨stripStep_lt _ _ _ _, fun k hk => ?_⟩
  rw [testBit_stripStep K _ _ r h.1 k hk]
  show _ = rule (evol x t (j + 1 + (k : Int) - 1)) (evol x t (j + 1 + k)) (evol x t (j + 1 + k + 1))
  have hc : r.testBit k = evol x t (j + 1 + k) := h.2 k hk
  have hl : (if k = 0 then evol x t j else r.testBit (k - 1)) =
      evol x t (j + 1 + (k : Int) - 1) := by
    split
    · rename_i h0; subst h0; congr 1; omega
    · rename_i h0; rw [h.2 (k - 1) (by omega)]; congr 1; omega
  have hr : (if k + 1 = K then evol x t (j + 1 + K) else r.testBit (k + 1)) =
      evol x t (j + 1 + k + 1) := by
    split
    · rename_i h1; congr 1; omega
    · rename_i h1; rw [h.2 (k + 1) (by omega)]; congr 1; omega
  rw [hl, hc, hr]

/-- The integer encoding of the actual strip of `K` cells right of column `j` in `evol x t`. -/
def encRowAt (x : Int → Bool) (t : Nat) (j : Int) : Nat → Nat
  | 0 => 0
  | K + 1 => encRowAt x t j K ||| ((evol x t (j + 1 + K)).toNat <<< K)

theorem testBit_encRowAt (x : Int → Bool) (t : Nat) (j : Int) :
    ∀ K k, (encRowAt x t j K).testBit k = (decide (k < K) && evol x t (j + 1 + k))
  | 0, k => by simp [encRowAt]
  | K + 1, k => by
    rw [encRowAt, Nat.testBit_or, testBit_encRowAt x t j K k, Nat.testBit_shiftLeft, testBit_toNat]
    by_cases hk : k < K
    · simp [hk, show k < K + 1 by omega, show ¬ K ≤ k by omega]
    · by_cases hk' : k = K
      · subst hk'; simp
      · simp [hk, show ¬ k < K + 1 by omega, show k - K ≠ 0 by omega]

theorem encAt_encRowAt (x : Int → Bool) (K t : Nat) (j : Int) :
    EncAt x K t j (encRowAt x t j K) := by
  refine ⟨Nat.lt_pow_two_of_testBit _ fun i hi => ?_, fun k hk => ?_⟩
  · rw [testBit_encRowAt]; simp [show ¬ i < K by omega]
  · rw [testBit_encRowAt]; simp [hk]

/-- Soundness of `applyWord` for an arbitrary configuration `x` and column `j`. -/
theorem encAt_applyWord {x : Int → Bool} {K : Nat} {j : Int} :
    ∀ (u : List Bool) (t r S : Nat), EncAt x K t j r → S.testBit r = true →
      (∀ s, s < u.length → evol x (t + s) j = u.getD s false) →
      ∃ r', EncAt x K (t + u.length) j r' ∧ (applyWord K u S).testBit r' = true
  | [], t, r, S, he, hS, _ => ⟨r, he, hS⟩
  | a :: u, t, r, S, he, hS, hu => by
    have ha : evol x t j = a := by simpa using hu 0 (by simp)
    have he1 := encAt_step he
    rw [ha] at he1
    have hS1 : (image K a S).testBit (stripStep K a (evol x t (j + 1 + K)) r) = true :=
      mem_imageAux hS _ (2 ^ K) he.1
    obtain ⟨r', he', hS'⟩ := encAt_applyWord u (t + 1) _ _ he1 hS1 (fun s hs => by
      have := hu (s + 1) (by simp; omega)
      rw [show t + (s + 1) = t + 1 + s by omega] at this
      simpa using this)
    refine ⟨r', ?_, hS'⟩
    rw [show t + (a :: u).length = t + 1 + u.length by simp; omega]
    exact he'

theorem encAt_iterW {x : Int → Bool} {K : Nat} {j : Int} (w : List Bool) :
    ∀ (k t r S : Nat), EncAt x K t j r → S.testBit r = true →
      (∀ m s, m < k → s < w.length → evol x (t + m * w.length + s) j = w.getD s false) →
      ∃ r', EncAt x K (t + k * w.length) j r' ∧ (iterW K w k S).testBit r' = true
  | 0, t, r, S, he, hS, _ => ⟨r, by simpa using he, hS⟩
  | k + 1, t, r, S, he, hS, hw => by
    obtain ⟨r1, he1, hS1⟩ := encAt_applyWord w t r S he hS (fun s hs => by
      simpa using hw 0 s (by omega) hs)
    obtain ⟨r', he', hS'⟩ := encAt_iterW w k (t + w.length) r1 _ he1 hS1 (fun m s hm hs => by
      rw [show t + w.length + m * w.length + s = t + (m + 1) * w.length + s by
        rw [Nat.succ_mul]; omega]
      exact hw (m + 1) s (by omega) hs)
    refine ⟨r', ?_, hS'⟩
    rw [show t + (k + 1) * w.length = t + w.length + k * w.length by rw [Nat.succ_mul]; omega]
    exact he'

/-! ### Part 1: Uniformity of `stripCert` and `certTable` across all finite configurations -/

/-- **Soundness of bitmask strip certificates for any configuration with a leftmost black cell.**
If `stripCert w K k` holds, no column `j` of `evol x` is eventually equal to `w` repeated. -/
theorem not_eventually_word_strip_leftmost {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false) (j : Int)
    (w : List Bool) (K k : Nat) (hK : 1 ≤ K) (hw : 0 < w.length)
    (hcert : stripCert w K k = true) : ¬ EventuallyWordAt x j w := by
  rintro ⟨T, hT⟩
  unfold stripCert at hcert
  rw [Bool.and_eq_true] at hcert
  obtain ⟨hsub, hforce⟩ := hcert
  have hsub' := allBelow_spec hsub
  have hblock : ∀ m s, s < w.length → evol x (T + m * w.length + s) j = w.getD s false := by
    intro m s hs
    rw [hT _ (by omega), show T + m * w.length + s - T = s + m * w.length by omega,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]
  have hcper : ∀ t, T ≤ t → evol x (t + w.length) j = evol x t j := by
    intro t ht
    rw [hT t ht, hT (t + w.length) (by omega), show t + w.length - T = (t - T) + w.length by omega,
      Nat.add_mod_right]
  let S0 := iterW K w k (fullSet K)
  have hstart : ∃ r, EncAt x K (T + k * w.length) j r ∧ S0.testBit r = true := by
    have h0 := encAt_encRowAt x K T j
    have hfull : (fullSet K).testBit (encRowAt x T j K) = true := by
      unfold fullSet; rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true h0.1
    exact encAt_iterW w k T _ _ h0 hfull (fun m s _ hs => hblock m s hs)
  have hinv : ∀ m, ∃ r, EncAt x K (T + (k + m) * w.length) j r ∧ S0.testBit r = true := by
    intro m
    induction m with
    | zero => simpa using hstart
    | succ m ih =>
      obtain ⟨r, he, hS⟩ := ih
      obtain ⟨r', he', hS'⟩ := encAt_applyWord w _ r S0 he hS (fun s hs => hblock (k + m) s hs)
      refine ⟨r', ?_, ?_⟩
      · have hm : (k + (m + 1)) * w.length = (k + m) * w.length + w.length := by
          rw [show k + (m + 1) = (k + m) + 1 by omega, Nat.succ_mul]
        rw [hm, ← Nat.add_assoc]
        exact he'
      · have := hsub' r' he'.1
        rw [hS', Bool.not_true, Bool.false_or] at this
        exact this
  let g : Nat → Bool := fun φ => w.getD φ false ||
    !colConst K (applyWord K (w.take φ) S0) false
  have hform : ∀ t, T + k * w.length ≤ t → orCol x j t = g ((t - T) % w.length) := by
    intro t ht
    have hφ : (t - T) % w.length < w.length := Nat.mod_lt _ hw
    have hdec : t = T + (k + ((t - T) / w.length - k)) * w.length + (t - T) % w.length := by
      have hd := Nat.div_add_mod (t - T) w.length
      have hq : k ≤ (t - T) / w.length := (Nat.le_div_iff_mul_le hw).2 (by omega)
      rw [show k + ((t - T) / w.length - k) = (t - T) / w.length by omega, Nat.mul_comm]
      omega
    obtain ⟨r, he, hS⟩ := hinv ((t - T) / w.length - k)
    obtain ⟨r', he', hS'⟩ := encAt_applyWord (w.take ((t - T) % w.length)) _ r S0 he hS
      (fun s hs => by
        rw [List.length_take] at hs
        have hs' : s < (t - T) % w.length := by omega
        rw [hblock _ s (by omega), getD_take w _ s hs'])
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hφ), ← hdec] at he'
    have hcell : evol x t (j + 1) = r'.testBit 0 := by
      rw [he'.2 0 (by omega)]; congr 1; omega
    unfold orCol g
    rw [hT t (by omega)]
    have hfφ := List.all_eq_true.mp hforce ((t - T) % w.length) (List.mem_range.mpr hφ)
    cases hwφ : w.getD ((t - T) % w.length) false
    · rw [hwφ, Bool.false_or] at hfφ
      simp only [Bool.false_or]
      rw [hcell]
      cases hc0 : colConst K (applyWord K (w.take ((t - T) % w.length)) S0) false
      · rw [hc0, Bool.false_or] at hfφ
        have := allBelow_spec hfφ r' he'.1
        rw [hS', Bool.not_true, Bool.false_or, beq_iff_eq] at this
        rw [this]; rfl
      · have := allBelow_spec hc0 r' he'.1
        rw [hS', Bool.not_true, Bool.false_or, beq_iff_eq] at this
        rw [this]; rfl
    · rfl
  refine Rule30FiniteMaskedJen.orCol_not_eventuallyPeriodic hlo hzero j ⟨T, w.length, hw, hcper⟩
    ⟨T + k * w.length, w.length, hw, fun t ht => ?_⟩
  show orCol x j (t + w.length) = orCol x j t
  rw [hform t ht, hform (t + w.length) (by omega),
    show t + w.length - T = (t - T) + w.length by omega, Nat.add_mod_right]

/-- **Every nonzero finite configuration**: if `stripCert w K k` holds, no column `j` of `evol x`
is eventually `w` repeated. -/
theorem not_eventually_word_strip_finite {x : Int → Bool} (hfin : FinConfig x)
    (hne : ∃ p, x p = true) (j : Int) (w : List Bool) (K k : Nat) (hK : 1 ≤ K) (hw : 0 < w.length)
    (hcert : stripCert w K k = true) : ¬ EventuallyWordAt x j w := by
  obtain ⟨lo, hlo, hzero⟩ := exists_leftmost hfin hne
  exact not_eventually_word_strip_leftmost hlo hzero j w K k hK hw hcert

/-- **All thirty words of `certTable` are excluded in every column of every nonzero finite
configuration.** -/
theorem not_eventually_certTable_finite {x : Int → Bool} (hfin : FinConfig x)
    (hne : ∃ p, x p = true) (j : Int) (e : Nat × Nat × Nat × Nat) (he : e ∈ certTable) :
    ¬ EventuallyWordAt x j (wordOf e.1 e.2.1) := by
  have h := List.all_eq_true.mp certTable_ok e he
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact not_eventually_word_strip_finite hfin hne j (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2 h.1.1
    (by rw [wordOf_length]; exact h.1.2) h.2

/-! ### Part 2: Semigroup Saturation and Parametric Strip Certificates (`paramStripCert`) -/

/-- Iterate `S ↦ S ||| image K a S` up to `m` steps, stopping early once a fixed point is reached. -/
def closeIter (K : Nat) (a : Bool) : Nat → Nat → Nat
  | 0, S => S
  | m + 1, S =>
    if (S ||| image K a S) == S then S else closeIter K a m (S ||| image K a S)

theorem testBit_closeIter (K : Nat) (a : Bool) :
    ∀ (m S r : Nat), S.testBit r = true → (closeIter K a m S).testBit r = true
  | 0, _, _, h => h
  | m + 1, S, r, h => by
    unfold closeIter
    split
    · exact h
    · refine testBit_closeIter K a m (S ||| image K a S) r ?_
      rw [Nat.testBit_or, h, Bool.true_or]

/-- Semigroup closure over-approximating `n ≥ n0` steps of `image K a` from `S`. -/
def iterAtLeast (K : Nat) (a : Bool) (n0 S : Nat) : Nat :=
  closeIter K a (2 ^ K) (applyWord K (List.replicate n0 a) S)

/-- One abstract period of `List.replicate r a ++ u` (`r ≥ r0`) on a strip bitmask `S`. -/
def absPeriod (K : Nat) (a : Bool) (r0 : Nat) (u : List Bool) (S : Nat) : Nat :=
  applyWord K u (iterAtLeast K a r0 S)

/-- `k` abstract warm-up periods from `S`. -/
def iterAbsPeriod (K : Nat) (a : Bool) (r0 : Nat) (u : List Bool) : Nat → Nat → Nat
  | 0, S => S
  | k + 1, S => iterAbsPeriod K a r0 u k (absPeriod K a r0 u S)

/-- Verify that `iterAtLeast K a r0 S` is closed under `image K a` along each of `k` warm-up steps. -/
def warmupClosed (K : Nat) (a : Bool) (r0 : Nat) (u : List Bool) : Nat → Nat → Bool
  | 0, _ => true
  | k + 1, S =>
    let T := iterAtLeast K a r0 S
    subsetB K (image K a T) T && warmupClosed K a r0 u k (applyWord K u T)

/-- Check that all phases during the `a^r` prefix have constant column-1 values when `a = false`. -/
def runPhasesForced (K : Nat) (a : Bool) (r0 S0 : Nat) : Bool :=
  a || (subsetB K (image K a (iterAtLeast K a (r0 - 1) S0)) (iterAtLeast K a (r0 - 1) S0) &&
    (List.range (r0 - 1)).all (fun φ =>
      colConst K (applyWord K (List.replicate φ a) S0) false ||
        colConst K (applyWord K (List.replicate φ a) S0) true) &&
    (colConst K (iterAtLeast K a (r0 - 1) S0) false ||
      colConst K (iterAtLeast K a (r0 - 1) S0) true))

theorem runPhasesForced_of_ne_true {K : Nat} {a : Bool} {r0 S0 : Nat}
    (h : runPhasesForced K a r0 S0 = true) (hna : ¬ a = true) :
    subsetB K (image K a (iterAtLeast K a (r0 - 1) S0)) (iterAtLeast K a (r0 - 1) S0) = true ∧
      ((List.range (r0 - 1)).all fun φ =>
        colConst K (applyWord K (List.replicate φ a) S0) false ||
          colConst K (applyWord K (List.replicate φ a) S0) true) = true ∧
      (colConst K (iterAtLeast K a (r0 - 1) S0) false ||
        colConst K (iterAtLeast K a (r0 - 1) S0) true) = true := by
  unfold runPhasesForced at h
  cases a
  · simp only [Bool.false_or, Bool.and_eq_true] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  · exact absurd rfl hna

/-- **Parametric strip certificate** for the infinite family `List.replicate r a ++ u` (`r ≥ r0`)
at strip width `K` with `k` warm-up periods. -/
def paramStripCert (a : Bool) (r0 : Nat) (u : List Bool) (K k : Nat) : Bool :=
  let S0 := iterAbsPeriod K a r0 u k (fullSet K)
  let T0 := iterAtLeast K a r0 S0
  warmupClosed K a r0 u k (fullSet K) &&
    subsetB K (image K a T0) T0 &&
    subsetB K (applyWord K u T0) S0 &&
    runPhasesForced K a r0 S0 &&
    (List.range u.length).all (fun ψ =>
      u.getD ψ false ||
        colConst K (applyWord K (u.take ψ) T0) false ||
        colConst K (applyWord K (u.take ψ) T0) true)

/-- If `T` is closed under `image K a`, any run of `m` steps of `a` keeps the strip in `T`. -/
theorem encAt_stay_closed {x : Int → Bool} {K : Nat} {j : Int} {a : Bool} {T : Nat}
    (hclosed : subsetB K (image K a T) T = true) :
    ∀ (m t r : Nat), EncAt x K t j r → T.testBit r = true →
      (∀ s, s < m → evol x (t + s) j = a) →
      ∃ r', EncAt x K (t + m) j r' ∧ T.testBit r' = true
  | 0, t, r, he, hT, _ => ⟨r, he, hT⟩
  | m + 1, t, r, he, hT, ha => by
    have ha0 : evol x t j = a := by simpa using ha 0 (by omega)
    have he1 := encAt_step he
    rw [ha0] at he1
    have himg : (image K a T).testBit (stripStep K a (evol x t (j + 1 + K)) r) = true :=
      mem_imageAux hT _ (2 ^ K) he.1
    have hsub := allBelow_spec hclosed _ he1.1
    rw [himg, Bool.not_true, Bool.false_or] at hsub
    obtain ⟨r', he', hT'⟩ := encAt_stay_closed hclosed m (t + 1) _ he1 hsub (fun s hs => by
      have := ha (s + 1) (by omega)
      rwa [show t + (s + 1) = t + 1 + s by omega] at this)
    rw [show t + (m + 1) = t + 1 + m by omega]
    exact ⟨r', he', hT'⟩

/-- Soundness of `iterAtLeast`: for every `n ≥ n0`, a run of `n` steps of `a` from `S` lands in
`iterAtLeast K a n0 S` whenever the latter is closed under `image K a`. -/
theorem encAt_iterAtLeast {x : Int → Bool} {K : Nat} {j : Int} {a : Bool} {n0 n t r S : Nat}
    (hn : n0 ≤ n) (hclosed : subsetB K (image K a (iterAtLeast K a n0 S)) (iterAtLeast K a n0 S) = true)
    (he : EncAt x K t j r) (hS : S.testBit r = true)
    (ha : ∀ s, s < n → evol x (t + s) j = a) :
    ∃ r', EncAt x K (t + n) j r' ∧ (iterAtLeast K a n0 S).testBit r' = true := by
  obtain ⟨r1, he1, hS1⟩ := encAt_applyWord (List.replicate n0 a) t r S he hS (fun s hs => by
    rw [List.length_replicate] at hs
    rw [ha s (by omega), getD_replicate a n0 s hs])
  rw [List.length_replicate] at he1
  have hT1 : (iterAtLeast K a n0 S).testBit r1 = true :=
    testBit_closeIter K a (2 ^ K) _ r1 hS1
  obtain ⟨r', he', hT'⟩ := encAt_stay_closed hclosed (n - n0) (t + n0) r1 he1 hT1 (fun s hs => by
    have := ha (n0 + s) (by omega)
    rwa [show t + (n0 + s) = t + n0 + s by omega] at this)
  rw [show t + n0 + (n - n0) = t + n by omega] at he'
  exact ⟨r', he', hT'⟩

/-- Soundness of one abstract period `absPeriod K a r0 u S` for any `r ≥ r0`. -/
theorem encAt_absPeriod {x : Int → Bool} {K : Nat} {j : Int} {a : Bool} {r0 r : Nat}
    {u : List Bool} {t r_st S : Nat} (hr : r0 ≤ r)
    (hclosed : subsetB K (image K a (iterAtLeast K a r0 S)) (iterAtLeast K a r0 S) = true)
    (he : EncAt x K t j r_st) (hS : S.testBit r_st = true)
    (hw : ∀ s, s < r + u.length →
      evol x (t + s) j = (List.replicate r a ++ u).getD s false) :
    ∃ r', EncAt x K (t + (r + u.length)) j r' ∧ (absPeriod K a r0 u S).testBit r' = true := by
  obtain ⟨r1, he1, hT1⟩ := encAt_iterAtLeast hr hclosed he hS (fun s hs => by
    rw [hw s (by omega), getD_replicate_append_left a u r s hs])
  obtain ⟨r', he', hS'⟩ := encAt_applyWord u (t + r) r1 (iterAtLeast K a r0 S) he1 hT1
    (fun s hs => by
      have := hw (r + s) (by omega)
      rw [show t + (r + s) = t + r + s by omega, getD_replicate_append_right a u r s] at this
      exact this)
  rw [show t + r + u.length = t + (r + u.length) by omega] at he'
  exact ⟨r', he', hS'⟩

/-- Soundness of `k` abstract warm-up periods `iterAbsPeriod K a r0 u k S` for any `r ≥ r0`. -/
theorem encAt_iterAbsPeriod {x : Int → Bool} {K : Nat} {j : Int} {a : Bool} {r0 r : Nat}
    (u : List Bool) (hr : r0 ≤ r) :
    ∀ (k t r_st S : Nat), warmupClosed K a r0 u k S = true →
      EncAt x K t j r_st → S.testBit r_st = true →
      (∀ m s, m < k → s < r + u.length →
        evol x (t + m * (r + u.length) + s) j = (List.replicate r a ++ u).getD s false) →
      ∃ r', EncAt x K (t + k * (r + u.length)) j r' ∧
        (iterAbsPeriod K a r0 u k S).testBit r' = true
  | 0, t, r_st, S, _, he, hS, _ => ⟨r_st, by simpa using he, hS⟩
  | k + 1, t, r_st, S, hwc, he, hS, hw => by
    unfold warmupClosed at hwc
    rw [Bool.and_eq_true] at hwc
    obtain ⟨r1, he1, hS1⟩ := encAt_absPeriod hr hwc.1 he hS (fun s hs => by
      simpa using hw 0 s (by omega) hs)
    obtain ⟨r', he', hS'⟩ := encAt_iterAbsPeriod u hr k (t + (r + u.length)) r1
      (absPeriod K a r0 u S) hwc.2 he1 hS1 (fun m s hm hs => by
        rw [show t + (r + u.length) + m * (r + u.length) + s =
          t + (m + 1) * (r + u.length) + s by rw [Nat.succ_mul]; omega]
        exact hw (m + 1) s (by omega) hs)
    refine ⟨r', ?_, hS'⟩
    rw [show t + (k + 1) * (r + u.length) =
      t + (r + u.length) + k * (r + u.length) by rw [Nat.succ_mul]; omega]
    exact he'

/-- **Universal soundness of parametric strip certificates (`paramStripCert`).**
If `paramStripCert a r0 u K k = true`, then for **every** `r ≥ r0`, no column `j` of `evol x`
(for any configuration `x` with a leftmost black cell) is eventually equal to
`List.replicate r a ++ u` repeated, whatever the transient. -/
theorem not_eventually_param_word_leftmost {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false) (j : Int)
    (a : Bool) (r0 : Nat) (u : List Bool) (K k : Nat)
    (hK : 1 ≤ K) (hr0 : 1 ≤ r0) (hcert : paramStripCert a r0 u K k = true) :
    ∀ r, r0 ≤ r → ¬ EventuallyWordAt x j (List.replicate r a ++ u) := by
  intro r hr ⟨T, hT⟩
  let w := List.replicate r a ++ u
  have hwlen : w.length = r + u.length := by simp [w]
  have hwpos : 0 < w.length := by rw [hwlen]; omega
  unfold paramStripCert at hcert
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hcert
  obtain ⟨⟨⟨⟨hwc, hT0closed⟩, hsub⟩, hrunForce⟩, huForce⟩ := hcert
  have hsub' := allBelow_spec hsub
  have hblock : ∀ m s, s < r + u.length →
      evol x (T + m * (r + u.length) + s) j = w.getD s false := by
    intro m s hs
    have hs' : s < w.length := by rw [hwlen]; exact hs
    rw [hT _ (by omega), ← hwlen, show T + m * w.length + s - T = s + m * w.length by omega,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs']
  have hcper : ∀ t, T ≤ t → evol x (t + w.length) j = evol x t j := by
    intro t ht
    rw [hT t ht, hT (t + w.length) (by omega), show t + w.length - T = (t - T) + w.length by omega,
      Nat.add_mod_right]
  let S0 := iterAbsPeriod K a r0 u k (fullSet K)
  let T0 := iterAtLeast K a r0 S0
  let Ttail := iterAtLeast K a (r0 - 1) S0
  have hstart : ∃ r_st, EncAt x K (T + k * (r + u.length)) j r_st ∧ S0.testBit r_st = true := by
    have h0 := encAt_encRowAt x K T j
    have hfull : (fullSet K).testBit (encRowAt x T j K) = true := by
      unfold fullSet; rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true h0.1
    exact encAt_iterAbsPeriod u hr k T _ (fullSet K) hwc h0 hfull (fun m s _ hs => hblock m s hs)
  have hinv : ∀ m, ∃ r_st, EncAt x K (T + (k + m) * (r + u.length)) j r_st ∧
      S0.testBit r_st = true := by
    intro m
    induction m with
    | zero => simpa using hstart
    | succ m ih =>
      obtain ⟨r_st, he, hS⟩ := ih
      obtain ⟨r', he', hS'⟩ := encAt_absPeriod hr hT0closed he hS (fun s hs => hblock (k + m) s hs)
      refine ⟨r', ?_, ?_⟩
      · have hm : (k + (m + 1)) * (r + u.length) =
            (k + m) * (r + u.length) + (r + u.length) := by
          rw [show k + (m + 1) = (k + m) + 1 by omega, Nat.succ_mul]
        rw [hm, ← Nat.add_assoc]
        exact he'
      · have := hsub' r' he'.1
        unfold absPeriod at hS'
        rw [hS', Bool.not_true, Bool.false_or] at this
        exact this
  let g : Nat → Bool := fun φ =>
    if φ < r0 - 1 then
      a || !colConst K (applyWord K (List.replicate φ a) S0) false
    else if φ < r then
      a || !colConst K Ttail false
    else
      u.getD (φ - r) false || !colConst K (applyWord K (u.take (φ - r)) T0) false
  have hform : ∀ t, T + k * w.length ≤ t → orCol x j t = g ((t - T) % w.length) := by
    intro t ht
    have hφ : (t - T) % w.length < w.length := Nat.mod_lt _ hwpos
    generalize hφdef : (t - T) % w.length = φ at hφ
    have hφ' : φ < r + u.length := by omega
    let m := (t - T) / w.length - k
    have hdec : t = T + (k + m) * (r + u.length) + φ := by
      have hd := Nat.div_add_mod (t - T) w.length
      have hq : k ≤ (t - T) / w.length := (Nat.le_div_iff_mul_le hwpos).2 (by omega)
      rw [hφdef] at hd
      rw [← hwlen, show k + m = (t - T) / w.length by omega, Nat.mul_comm]
      omega
    obtain ⟨r_st, he, hS⟩ := hinv m
    unfold orCol g
    rw [hT t (by omega), hφdef]
    by_cases h1 : φ < r0 - 1
    · simp only [h1, ↓reduceIte]
      have hφr : φ < r := by omega
      have hcenter : w.getD φ false = a := getD_replicate_append_left a u r φ hφr
      rw [hcenter]
      by_cases ha : a = true
      · rw [ha, Bool.true_or, Bool.true_or]
      · obtain ⟨_, hpref, _⟩ := runPhasesForced_of_ne_true hrunForce ha
        have haf : a = false := Bool.eq_false_iff.mpr ha
        obtain ⟨r', he', hS'⟩ := encAt_applyWord (List.replicate φ a) _ r_st S0 he hS
          (fun s hs => by
            rw [List.length_replicate] at hs
            rw [hblock (k + m) s (by omega), getD_replicate_append_left a u r s (by omega),
              getD_replicate a φ s hs])
        rw [List.length_replicate, ← hdec] at he'
        have hcell : evol x t (j + 1) = r'.testBit 0 := by
          rw [he'.2 0 (by omega)]; congr 1; omega
        rw [hcell]
        have hfφ := List.all_eq_true.mp hpref φ (List.mem_range.mpr h1)
        cases hc0 : colConst K (applyWord K (List.replicate φ a) S0) false
        · rw [hc0, Bool.false_or] at hfφ
          have := allBelow_spec hfφ r' he'.1
          rw [hS', Bool.not_true, Bool.false_or, beq_iff_eq] at this
          rw [this, haf]; rfl
        · have := allBelow_spec hc0 r' he'.1
          rw [hS', Bool.not_true, Bool.false_or, beq_iff_eq] at this
          rw [this, haf]; rfl
    · simp only [h1, ↓reduceIte]
      by_cases h2 : φ < r
      · simp only [h2, ↓reduceIte]
        have hcenter : w.getD φ false = a := getD_replicate_append_left a u r φ h2
        rw [hcenter]
        by_cases ha : a = true
        · rw [ha, Bool.true_or, Bool.true_or]
        · obtain ⟨hTtailClosed, _, hTtailForce⟩ := runPhasesForced_of_ne_true hrunForce ha
          have haf : a = false := Bool.eq_false_iff.mpr ha
          obtain ⟨r', he', hS'⟩ := encAt_iterAtLeast (n0 := r0 - 1) (n := φ) (by omega)
            hTtailClosed he hS (fun s hs => by
              rw [hblock (k + m) s (by omega), getD_replicate_append_left a u r s (by omega)])
          rw [← hdec] at he'
          have hcell : evol x t (j + 1) = r'.testBit 0 := by
            rw [he'.2 0 (by omega)]; congr 1; omega
          rw [hcell]
          cases hc0 : colConst K Ttail false
          · rw [hc0, Bool.false_or] at hTtailForce
            have := allBelow_spec hTtailForce r' he'.1
            rw [hS', Bool.not_true, Bool.false_or, beq_iff_eq] at this
            rw [this, haf]; rfl
          · have := allBelow_spec hc0 r' he'.1
            rw [hS', Bool.not_true, Bool.false_or, beq_iff_eq] at this
            rw [this, haf]; rfl
      · simp only [h2, ↓reduceIte]
        let ψ := φ - r
        have hψ : ψ < u.length := by omega
        have hφeq : φ = r + ψ := by omega
        have hcenter : w.getD φ false = u.getD ψ false := by
          rw [hφeq]; exact getD_replicate_append_right a u r ψ
        rw [hcenter]
        obtain ⟨r1, he1, hT1⟩ := encAt_iterAtLeast hr hT0closed he hS (fun s hs => by
          rw [hblock (k + m) s (by omega), getD_replicate_append_left a u r s hs])
        obtain ⟨r', he', hS'⟩ := encAt_applyWord (u.take ψ) _ r1 T0 he1 hT1 (fun s hs => by
          rw [List.length_take] at hs
          have hs' : s < ψ := by omega
          have hb := hblock (k + m) (r + s) (by omega)
          rw [show T + (k + m) * (r + u.length) + (r + s) =
            T + (k + m) * (r + u.length) + r + s by omega,
            getD_replicate_append_right a u r s] at hb
          rw [hb, getD_take u ψ s hs'])
        rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hψ),
          show T + (k + m) * (r + u.length) + r + ψ = t by omega] at he'
        have hcell : evol x t (j + 1) = r'.testBit 0 := by
          rw [he'.2 0 (by omega)]; congr 1; omega
        have hfψ := List.all_eq_true.mp huForce ψ (List.mem_range.mpr hψ)
        cases huψ : u.getD ψ false
        · rw [huψ, Bool.false_or] at hfψ
          simp only [Bool.false_or]
          rw [hcell]
          cases hc0 : colConst K (applyWord K (u.take ψ) T0) false
          · rw [hc0, Bool.false_or] at hfψ
            have := allBelow_spec hfψ r' he'.1
            rw [hS', Bool.not_true, Bool.false_or, beq_iff_eq] at this
            rw [this]; rfl
          · have := allBelow_spec hc0 r' he'.1
            rw [hS', Bool.not_true, Bool.false_or, beq_iff_eq] at this
            rw [this]; rfl
        · rfl
  refine Rule30FiniteMaskedJen.orCol_not_eventuallyPeriodic hlo hzero j ⟨T, w.length, hwpos, hcper⟩
    ⟨T + k * w.length, w.length, hwpos, fun t ht => ?_⟩
  show orCol x j (t + w.length) = orCol x j t
  rw [hform t ht, hform (t + w.length) (by omega),
    show t + w.length - T = (t - T) + w.length by omega, Nat.add_mod_right]

/-- **Every nonzero finite configuration**: if `paramStripCert a r0 u K k = true`, then for every
`r ≥ r0`, no column `j` of `evol x` is eventually `List.replicate r a ++ u` repeated. -/
theorem not_eventually_param_word_finite {x : Int → Bool} (hfin : FinConfig x)
    (hne : ∃ p, x p = true) (j : Int) (a : Bool) (r0 : Nat) (u : List Bool) (K k : Nat)
    (hK : 1 ≤ K) (hr0 : 1 ≤ r0) (hcert : paramStripCert a r0 u K k = true) :
    ∀ r, r0 ≤ r → ¬ EventuallyWordAt x j (List.replicate r a ++ u) := by
  obtain ⟨lo, hlo, hzero⟩ := exists_leftmost hfin hne
  exact not_eventually_param_word_leftmost hlo hzero j a r0 u K k hK hr0 hcert

/-- **Single-seed center column (`EventuallyWord`)**: if `paramStripCert a r0 u K k = true`, then
for every `r ≥ r0`, `¬ EventuallyWord (List.replicate r a ++ u)`. -/
theorem not_eventually_param_word (a : Bool) (r0 : Nat) (u : List Bool) (K k : Nat)
    (hK : 1 ≤ K) (hr0 : 1 ≤ r0) (hcert : paramStripCert a r0 u K k = true) :
    ∀ r, r0 ≤ r → ¬ EventuallyWord (List.replicate r a ++ u) := by
  intro r hr hew
  have hlo : seed0 0 = true := rfl
  have hzero : ∀ p, p < 0 → seed0 p = false := fun p hp => by
    unfold seed0; simp [show p ≠ 0 by omega]
  exact not_eventually_param_word_leftmost hlo hzero 0 a r0 u K k hK hr0 hcert r hr
    ((eventuallyWordAt_seed0_iff _).2 hew)

/-- Bridge from the `t1`-shifted periodic block presentation (used in `Rule30BlackRunBlocks` and
`Rule30WhiteRunEight`) to `EventuallyWordAt`. -/
theorem eventuallyWordAt_of_run_block {x : Int → Bool} {j : Int} {a : Bool} {T r t1 : Nat}
    {u : List Bool} (hP : 0 < r + u.length)
    (hper : ∀ t, T ≤ t → evol x (t + (r + u.length)) j = evol x t j) (ht1 : T ≤ t1)
    (hrun : ∀ s, s < r → evol x (t1 + s) j = a)
    (hu : ∀ i, i < u.length → evol x (t1 + r + i) j = u.getD i false) :
    EventuallyWordAt x j (List.replicate r a ++ u) := by
  have hperk : ∀ m t, T ≤ t → evol x (t + m * (r + u.length)) j = evol x t j :=
    periodic_mul (f := fun t => evol x t j) hper
  refine ⟨t1, fun t ht => ?_⟩
  have hlen : (List.replicate r a ++ u).length = r + u.length := by simp
  rw [hlen]
  have hmod : (t - t1) % (r + u.length) < r + u.length := Nat.mod_lt _ hP
  have hd := Nat.div_add_mod (t - t1) (r + u.length)
  generalize (t - t1) / (r + u.length) = m at hd
  generalize (t - t1) % (r + u.length) = s at hd hmod
  have ht_eq : t = t1 + s + m * (r + u.length) := by rw [Nat.mul_comm] at hd; omega
  rw [ht_eq, hperk m (t1 + s) (by omega)]
  by_cases hsr : s < r
  · rw [hrun s hsr, getD_replicate_append_left a u r s hsr]
  · have h1 : t1 + s = t1 + r + (s - r) := by omega
    have h2 := getD_replicate_append_right a u r (s - r)
    rw [show r + (s - r) = s by omega] at h2
    rw [h1, hu (s - r) (by omega), h2]

/-- **Block-form exclusion (`Rule30BlackRunBlocks` / `Rule30WhiteRunEight` style)** for any
configuration with a leftmost black cell and any column `j`. -/
theorem no_param_run_block_leftmost {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false) (j : Int)
    (a : Bool) (r0 : Nat) (u : List Bool) (K k : Nat)
    (hK : 1 ≤ K) (hr0 : 1 ≤ r0) (hcert : paramStripCert a r0 u K k = true)
    (T r t1 : Nat) (hr : r0 ≤ r)
    (hper : ∀ t, T ≤ t → evol x (t + (r + u.length)) j = evol x t j) (ht1 : T ≤ t1)
    (hrun : ∀ s, s < r → evol x (t1 + s) j = a)
    (hu : ∀ i, i < u.length → evol x (t1 + r + i) j = u.getD i false) : False :=
  not_eventually_param_word_leftmost hlo hzero j a r0 u K k hK hr0 hcert r hr
    (eventuallyWordAt_of_run_block (by omega) hper ht1 hrun hu)

/-! ### Part 3: Kernel-checked Parametric Tables and Headline Theorems -/

/-- Parametric black-run table `(n, bits, r0, K, k)`: block `u = wordOf n bits` of length `n`,
threshold `r0`, strip width `K`, warm-up periods `k`. Certifies `1^r ++ u` for all `r ≥ r0`. -/
def paramBlackTable : List (Nat × Nat × Nat × Nat × Nat) := [
  -- Length 1..4 blocks from Rule30BlackRunBlocks (lowered from r ≥ 18 / 27 to r ≥ 8 / 9 at K = 5)
  (1, 0, 9, 5, 1),   -- u = 0:     all r ≥ 9  (was r ≥ 18)
  (2, 0, 9, 5, 1),   -- u = 00:    all r ≥ 9  (was r ≥ 18)
  (3, 0, 9, 5, 1),   -- u = 000:   all r ≥ 9  (was r ≥ 18)
  (3, 2, 8, 5, 1),   -- u = 010:   all r ≥ 8  (was r ≥ 27)
  (4, 0, 9, 5, 1),   -- u = 0000:  all r ≥ 9  (was r ≥ 18)
  (4, 2, 9, 5, 1),   -- u = 0010:  all r ≥ 9  (was r ≥ 27)
  (4, 4, 9, 5, 1),   -- u = 0100:  all r ≥ 9  (was r ≥ 18)
  (4, 6, 9, 5, 1),   -- u = 0110:  all r ≥ 9  (was r ≥ 27)
  -- New length-5 blocks
  (5, 0, 9, 5, 1),   -- u = 00000: all r ≥ 9
  (5, 2, 8, 5, 1),   -- u = 00010: all r ≥ 8
  (5, 6, 15, 7, 1),  -- u = 00110: all r ≥ 15
  (5, 10, 15, 7, 1), -- u = 01010: all r ≥ 15
  (5, 12, 9, 5, 1),  -- u = 01100: all r ≥ 9
  (5, 14, 9, 5, 1)   -- u = 01110: all r ≥ 9
]

theorem paramBlackTable_ok :
    paramBlackTable.all (fun e =>
      decide (1 ≤ e.2.2.2.1) && decide (1 ≤ e.2.2.1) &&
        paramStripCert true e.2.2.1 (wordOf e.1 e.2.1) e.2.2.2.1 e.2.2.2.2) = true := by
  decide +kernel

/-- **Every black-run family `1^r ++ u` (`r ≥ r0`) in `paramBlackTable` is excluded** as an
eventual repeating word of the center column, whatever the transient. -/
theorem not_eventually_paramBlackTable (e : Nat × Nat × Nat × Nat × Nat)
    (he : e ∈ paramBlackTable) (r : Nat) (hr : e.2.2.1 ≤ r) :
    ¬ EventuallyWord (List.replicate r true ++ wordOf e.1 e.2.1) := by
  have h := List.all_eq_true.mp paramBlackTable_ok e he
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact not_eventually_param_word true e.2.2.1 (wordOf e.1 e.2.1) e.2.2.2.1 e.2.2.2.2
    h.1.1 h.1.2 h.2 r hr

/-- **Every black-run family `1^r ++ u` (`r ≥ r0`) in `paramBlackTable` is excluded in every
column of every nonzero finite configuration.** -/
theorem not_eventually_paramBlackTable_finite {x : Int → Bool} (hfin : FinConfig x)
    (hne : ∃ p, x p = true) (j : Int) (e : Nat × Nat × Nat × Nat × Nat)
    (he : e ∈ paramBlackTable) (r : Nat) (hr : e.2.2.1 ≤ r) :
    ¬ EventuallyWordAt x j (List.replicate r true ++ wordOf e.1 e.2.1) := by
  have h := List.all_eq_true.mp paramBlackTable_ok e he
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact not_eventually_param_word_finite hfin hne j true e.2.2.1 (wordOf e.1 e.2.1)
    e.2.2.2.1 e.2.2.2.2 h.1.1 h.1.2 h.2 r hr

/-- **Sharpened Theorem B′ for `u = 010`**: `1^r 010` is excluded for all `r ≥ 8` (lowering the
threshold `r ≥ 27` of `Rule30BlackRunBlocks.det_010` to `r ≥ 8`). -/
theorem not_eventually_black_run_010 (r : Nat) (hr : 8 ≤ r) :
    ¬ EventuallyWord (List.replicate r true ++ [false, true, false]) :=
  not_eventually_param_word true 8 [false, true, false] 5 1 (by decide) (by decide)
    (by decide +kernel) r hr

/-- **New block `u = 00010` at `r ≥ 8`**: `1^r 00010` is excluded for all `r ≥ 8` at strip width `5`. -/
theorem not_eventually_black_run_00010 (r : Nat) (hr : 8 ≤ r) :
    ¬ EventuallyWord (List.replicate r true ++ [false, false, false, true, false]) :=
  not_eventually_param_word true 8 [false, false, false, true, false] 5 1 (by decide) (by decide)
    (by decide +kernel) r hr

end Ruliology.CellularAutomata.Rule30ParametricStripCertificates
