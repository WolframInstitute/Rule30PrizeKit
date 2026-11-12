module

public import Ruliology.CellularAutomata.Rule30StripCertificates
public import Ruliology.CellularAutomata.Rule30FiniteMaskedJen

@[expose] public section

/-!
# Bitmask strip certificates for arbitrary left-finite configurations

The certificate checker has no initial-state dependence. Its soundness extends
from the single seed to every column of any configuration with a leftmost
black cell, by the existing uniform masked Jen theorem. In particular every
concrete bitmask certificate in the catalog has this stronger conclusion.
-/

namespace Ruliology.CellularAutomata
namespace Rule30FiniteStrips

open Rule30Jen Rule30Realization Rule30FiniteConfigs Rule30StripCertificates

/-- Column i eventually reads the nonempty word w, starting at an arbitrary transient. -/
def EventuallyWord (x : Int → Bool) (i : Int) (w : List Bool) : Prop :=
  ∃ T, ∀ t, T ≤ t → evol x t i = w.getD ((t - T) % w.length) false

/-- Strip encoding: `r < 2 ^ K` and bit `k < K` of `r` is `evol x t (j + 1 + k)`. -/
def Enc (x : Int → Bool) (K t : Nat) (j : Int) (r : Nat) : Prop :=
  r < 2 ^ K ∧ ∀ k, k < K → r.testBit k = evol x t (j + 1 + k)

theorem enc_step {x : Int → Bool} {K t : Nat} {j : Int} {r : Nat} (h : Enc x K t j r) :
    Enc x K (t + 1) j (stripStep K (evol x t j) (evol x t (j + 1 + K)) r) := by
  refine ⟨stripStep_lt _ _ _ _, fun k hk => ?_⟩
  rw [testBit_stripStep K _ _ r h.1 k hk]
  show _ = rule (evol x t (j + 1 + (k : Int) - 1)) (evol x t (j + 1 + k)) (evol x t (j + 1 + k + 1))
  have hc : r.testBit k = evol x t (j + 1 + k) := h.2 k hk
  have hl : (if k = 0 then evol x t j else r.testBit (k - 1)) = evol x t (j + 1 + (k : Int) - 1) := by
    split
    · rename_i h0; subst h0; congr 1; omega
    · rename_i h0; rw [h.2 (k - 1) (by omega)]; congr 1; omega
  have hr : (if k + 1 = K then evol x t (j + 1 + K) else r.testBit (k + 1)) =
      evol x t (j + 1 + k + 1) := by
    split
    · rename_i h1; congr 1; omega
    · rename_i h1; rw [h.2 (k + 1) (by omega)]; congr 1; omega
  rw [hl, hc, hr]

/-- The encoding of the actual strip. -/
def encRow (x : Int → Bool) (t : Nat) (j : Int) : Nat → Nat
  | 0 => 0
  | K + 1 => encRow x t j K ||| ((evol x t (j + 1 + K)).toNat <<< K)

theorem testBit_encRow {x : Int → Bool} (t : Nat) (j : Int) :
    ∀ K k, (encRow x t j K).testBit k = (decide (k < K) && evol x t (j + 1 + k))
  | 0, k => by simp [encRow]
  | K + 1, k => by
    rw [encRow, Nat.testBit_or, testBit_encRow t j K k, Nat.testBit_shiftLeft, testBit_toNat]
    by_cases hk : k < K
    · simp [hk, show k < K + 1 by omega, show ¬ K ≤ k by omega]
    · by_cases hk' : k = K
      · subst hk'; simp
      · simp [hk, show ¬ k < K + 1 by omega, show k - K ≠ 0 by omega]

theorem enc_encRow {x : Int → Bool} (K t : Nat) (j : Int) : Enc x K t j (encRow x t j K) := by
  refine ⟨Nat.lt_pow_two_of_testBit _ fun i hi => ?_, fun k hk => ?_⟩
  · rw [testBit_encRow]; simp [show ¬ i < K by omega]
  · rw [testBit_encRow]; simp [hk]

/-- **Soundness of the strip sets.** If the actual strip is in `S` at time `t` and column `j` carries
the word `u` from `t` on, the actual strip at time `t + u.length` is in `applyWord K u S`. -/
theorem enc_applyWord {x : Int → Bool} {K : Nat} {j : Int} :
    ∀ (u : List Bool) (t r S : Nat), Enc x K t j r → S.testBit r = true →
      (∀ s, s < u.length → evol x (t + s) j = u.getD s false) →
      ∃ r', Enc x K (t + u.length) j r' ∧ (applyWord K u S).testBit r' = true
  | [], t, r, S, he, hS, _ => ⟨r, he, hS⟩
  | a :: u, t, r, S, he, hS, hu => by
    have ha : evol x t j = a := by simpa using hu 0 (by simp)
    have he1 := enc_step he
    rw [ha] at he1
    have hS1 : (image K a S).testBit (stripStep K a (evol x t (j + 1 + K)) r) = true :=
      mem_imageAux hS _ (2 ^ K) he.1
    obtain ⟨r', he', hS'⟩ := enc_applyWord u (t + 1) _ _ he1 hS1 (fun s hs => by
      have := hu (s + 1) (by simp; omega)
      rw [show t + (s + 1) = t + 1 + s by omega] at this
      simpa using this)
    refine ⟨r', ?_, hS'⟩
    rw [show t + (a :: u).length = t + 1 + u.length by simp; omega]
    exact he'

theorem enc_iterW {x : Int → Bool} {K : Nat} {j : Int} (w : List Bool) :
    ∀ (k t r S : Nat), Enc x K t j r → S.testBit r = true →
      (∀ m s, m < k → s < w.length → evol x (t + m * w.length + s) j = w.getD s false) →
      ∃ r', Enc x K (t + k * w.length) j r' ∧ (iterW K w k S).testBit r' = true
  | 0, t, r, S, he, hS, _ => ⟨r, by simpa using he, hS⟩
  | k + 1, t, r, S, he, hS, hw => by
    obtain ⟨r1, he1, hS1⟩ := enc_applyWord w t r S he hS (fun s hs => by
      simpa using hw 0 s (by omega) hs)
    obtain ⟨r', he', hS'⟩ := enc_iterW w k (t + w.length) r1 _ he1 hS1 (fun m s hm hs => by
      rw [show t + w.length + m * w.length + s = t + (m + 1) * w.length + s by
        rw [Nat.succ_mul]; omega]
      exact hw (m + 1) s (by omega) hs)
    refine ⟨r', ?_, hS'⟩
    rw [show t + (k + 1) * w.length = t + w.length + k * w.length by rw [Nat.succ_mul]; omega]
    exact he'

/-- A bitmask strip certificate forces the effective right boundary to be eventually periodic,
in the evolution of an arbitrary configuration, provided column i reads w eventually. -/
theorem orCol_exact_period_of_word_strip {x : Int → Bool} (i : Int) (w : List Bool)
    (K k : Nat) (hK : 1 ≤ K) (hw : 0 < w.length)
    (hcert : stripCert w K k = true) (hword : EventuallyWord x i w) :
    ∃ T, ∀ t, T ≤ t →
      Rule30FiniteMaskedJen.orCol x i (t + w.length) = Rule30FiniteMaskedJen.orCol x i t := by
  obtain ⟨T, hT⟩ := hword
  unfold stripCert at hcert
  rw [Bool.and_eq_true] at hcert
  obtain ⟨hsub, hforce⟩ := hcert
  have hsub' := allBelow_spec hsub
  -- the driver is `w` on every period from `T`
  have hblock : ∀ m s, s < w.length → evol x (T + m * w.length + s) i = w.getD s false := by
    intro m s hs
    rw [hT _ (by omega), show T + m * w.length + s - T = s + m * w.length by omega,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]
  let S0 := iterW K w k (fullSet K)
  -- after `k` periods the strip is in `S0`
  have hstart : ∃ r, Enc x K (T + k * w.length) i r ∧ S0.testBit r = true := by
    have h0 := enc_encRow (x := x) K T i
    have hfull : (fullSet K).testBit (encRow x T i K) = true := by
      unfold fullSet; rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true h0.1
    exact enc_iterW w k T _ _ h0 hfull (fun m s _ hs => hblock m s hs)
  -- and it stays in `S0` at every later period start
  have hinv : ∀ m, ∃ r, Enc x K (T + (k + m) * w.length) i r ∧ S0.testBit r = true := by
    intro m
    induction m with
    | zero => simpa using hstart
    | succ m ih =>
      obtain ⟨r, he, hS⟩ := ih
      obtain ⟨r', he', hS'⟩ := enc_applyWord w _ r S0 he hS (fun s hs => by
        rw [show T + (k + m) * w.length + s = T + (k + m) * w.length + s from rfl]
        exact hblock (k + m) s hs)
      refine ⟨r', ?_, ?_⟩
      · have hm : (k + (m + 1)) * w.length = (k + m) * w.length + w.length := by
          rw [show k + (m + 1) = (k + m) + 1 by omega, Nat.succ_mul]
        rw [hm, ← Nat.add_assoc]
        exact he'
      · have hlt : r' < 2 ^ K := he'.1
        have := hsub' r' hlt
        rw [hS', Bool.not_true, Bool.false_or] at this
        exact this
  -- the forced value at each white phase
  let g : Nat → Bool := fun φ => w.getD φ false ||
    !colConst K (applyWord K (w.take φ) S0) false
  have hform : ∀ t, T + k * w.length ≤ t → Rule30FiniteMaskedJen.orCol x i t = g ((t - T) % w.length) := by
    intro t ht
    have hφ : (t - T) % w.length < w.length := Nat.mod_lt _ hw
    have hdec : t = T + (k + ((t - T) / w.length - k)) * w.length + (t - T) % w.length := by
      have hd := Nat.div_add_mod (t - T) w.length
      have hq : k ≤ (t - T) / w.length := (Nat.le_div_iff_mul_le hw).2 (by omega)
      rw [show k + ((t - T) / w.length - k) = (t - T) / w.length by omega, Nat.mul_comm]
      omega
    obtain ⟨r, he, hS⟩ := hinv ((t - T) / w.length - k)
    obtain ⟨r', he', hS'⟩ := enc_applyWord (w.take ((t - T) % w.length)) _ r S0 he hS
      (fun s hs => by
        rw [List.length_take] at hs
        have hs' : s < (t - T) % w.length := by omega
        rw [hblock _ s (by omega)]
        simp [List.getD_eq_getElem?_getD, hs'])
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hφ), ← hdec] at he'
    have hcell : evol x t (i + 1) = r'.testBit 0 := by
      simpa using (he'.2 0 (by omega)).symm
    unfold Rule30FiniteMaskedJen.orCol g
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
  refine ⟨T + k * w.length, fun t ht => ?_⟩
  show Rule30FiniteMaskedJen.orCol x i (t + w.length) = Rule30FiniteMaskedJen.orCol x i t
  rw [hform t ht, hform (t + w.length) (by omega), show t + w.length - T = (t - T) + w.length by omega,
    Nat.add_mod_right]


/-- Eventual periodicity version of the exact-period implication. -/
theorem orCol_periodic_of_word_strip {x : Int → Bool} (i : Int) (w : List Bool)
    (K k : Nat) (hK : 1 ≤ K) (hw : 0 < w.length)
    (hcert : stripCert w K k = true) (hword : EventuallyWord x i w) :
    EventuallyPeriodic (Rule30FiniteMaskedJen.orCol x i) := by
  obtain ⟨T, hT⟩ := orCol_exact_period_of_word_strip i w K k hK hw hcert hword
  exact ⟨T, w.length, hw, hT⟩

/-- **Uniform strip soundness.** Every bitmask certificate excludes its word at every column
of every configuration having a leftmost black cell, for every transient. -/
theorem not_eventually_word_strip {x : Int → Bool} {lo : Int}
    (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false) (i : Int)
    (w : List Bool) (K k : Nat) (hK : 1 ≤ K) (hw : 0 < w.length)
    (hcert : stripCert w K k = true) : ¬ EventuallyWord x i w := by
  intro hword
  have hcper : EventuallyPeriodic (fun t => evol x t i) := by
    obtain ⟨T, hT⟩ := hword
    refine ⟨T, w.length, hw, fun t ht => ?_⟩
    change evol x (t + w.length) i = evol x t i
    rw [hT t ht, hT (t + w.length) (by omega),
      show t + w.length - T = (t - T) + w.length by omega, Nat.add_mod_right]
  exact Rule30FiniteMaskedJen.orCol_not_eventuallyPeriodic hlo hzero i hcper
    (orCol_periodic_of_word_strip i w K k hK hw hcert hword)

/-- In particular, the certificate excludes the word in every column of every nonzero finite
configuration. Neither the column nor the transient is bounded. -/
theorem not_eventually_word_strip_finite {x : Int → Bool}
    (hfin : Rule30PeriodTwoSideways.FinConfig x) (hne : ∃ p, x p = true) (i : Int)
    (w : List Bool) (K k : Nat) (hK : 1 ≤ K) (hw : 0 < w.length)
    (hcert : stripCert w K k = true) : ¬ EventuallyWord x i w := by
  obtain ⟨lo, hlo, hzero⟩ := exists_leftmost hfin hne
  exact not_eventually_word_strip hlo hzero i w K k hK hw hcert


/-! ### Pointwise strip equality characterization of `encRow` and single-seed `EventuallyWord` equivalence -/

/-- **Pointwise Cell-Agreement Characterization of `encRow` Equality (`encRow_eq_iff_cells_eq`).** -/
theorem encRow_eq_iff_cells_eq (x y : Int → Bool) (K t1 t2 : Nat) (j1 j2 : Int) :
    Rule30FiniteStrips.encRow x t1 j1 K = Rule30FiniteStrips.encRow y t2 j2 K ↔
      ∀ k, k < K → Rule30Realization.evol x t1 (j1 + 1 + k) = Rule30Realization.evol y t2 (j2 + 1 + k) := by
  constructor
  · intro heq k hk
    have h1 := (Rule30FiniteStrips.enc_encRow (x := x) K t1 j1).2 k hk
    have h2 := (Rule30FiniteStrips.enc_encRow (x := y) K t2 j2).2 k hk
    rw [heq] at h1
    exact h1.symm.trans h2
  · intro hall
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Rule30FiniteStrips.testBit_encRow, Rule30FiniteStrips.testBit_encRow]
    by_cases hk : k < K
    · simp [hk, hall k hk]
    · simp [hk]

/-- **Eventual Periodicity from `EventuallyWord` and Single-Seed Equivalence (`eventuallyWord_periodic_and_seed_iff`).** -/
theorem eventuallyWord_periodic_and_seed_iff (x : Int → Bool) (i : Int) (w : List Bool) :
    (0 < w.length → Rule30FiniteStrips.EventuallyWord x i w →
      Rule30Jen.EventuallyPeriodic (fun t => Rule30Realization.evol x t i)) ∧
    (Rule30FiniteStrips.EventuallyWord Rule30Realization.seed 0 w ↔
      Rule30StripCertificates.EventuallyWord w) := by
  refine ⟨fun hw ⟨T, hT⟩ => ⟨T, w.length, hw, fun t ht => ?_⟩, ?_⟩
  · change Rule30Realization.evol x (t + w.length) i = Rule30Realization.evol x t i
    rw [hT t ht, hT (t + w.length) (by omega),
      show t + w.length - T = (t - T) + w.length by omega, Nat.add_mod_right]
  · simp only [Rule30FiniteStrips.EventuallyWord, Rule30StripCertificates.EventuallyWord,
      Rule30Realization.evol_seed]

end Rule30FiniteStrips
end Ruliology.CellularAutomata
