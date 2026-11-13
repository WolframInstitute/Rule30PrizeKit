module
public import Ruliology.CellularAutomata.Rule30StripCertificates
/-!
# Sparse strip checks and envelopes for arbitrary white padding

`checkMask` recursively skips empty halves of a state bitmask. Its soundness is
proved for every width and predicate; concrete transitions are checked by the
ordinary kernel. Capture into a white-closed envelope then permits any longer
white padding. A finite observation profile ending black persists under white
steps, so masked Jen excludes the entire unbounded family.

`no_word_of_invariant` generalizes the width-eight theorem of
`Rule30WhitePad10111` to arbitrary width, preserving its proof. The strip model,
masked Jen and image monotonicity are from the kit, not new claims here.
-/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30RunEnvelopes
open Rule30StripCertificates

def checkMask (f : Nat → Bool) : Nat → Nat → Nat → Bool
  | 0, off, A => !A.testBit 0 || f off
  | h+1, off, A => if A == 0 then true else
      checkMask f h off (A % 2^(2^h)) && checkMask f h (off+2^h) (A >>> (2^h))

theorem checkMask_spec (f : Nat → Bool) : ∀ h off A,
    checkMask f h off A = true → ∀ i, i < 2^h → A.testBit i = true → f (off+i) = true := by
  intro h
  induction h with
  | zero =>
    intro off A hh i hi hm
    have : i=0 := by simpa using hi
    subst i
    simpa [checkMask,hm] using hh
  | succ h ih =>
    intro off A hh i hi hm
    have hA : ¬ A == 0 := by
      intro hz
      have hz' : A=0 := by simpa using hz
      simp [hz'] at hm
    simp only [checkMask, ite_eq_right hA, Bool.and_eq_true] at hh
    by_cases hl : i < 2^h
    · have hm' : (A % 2^(2^h)).testBit i = true := by simp [Nat.testBit_mod_two_pow,hl,hm]
      exact ih off _ hh.1 i hl hm'
    · have hh' : i-2^h < 2^h := by simp only [Nat.pow_succ] at hi; omega
      have hm' : (A >>> (2^h)).testBit (i-2^h) = true := by
        rw [Nat.testBit_shiftRight, show 2^h+(i-2^h)=i by omega]; exact hm
      have := ih (off+2^h) _ hh.2 (i-2^h) hh' hm'
      simpa [show off+2^h+(i-2^h)=off+i by omega] using this

def covers (K : Nat) (a : Bool) (A B : Nat) : Bool :=
 checkMask (fun s => B.testBit (stripStep K a false s) && B.testBit (stripStep K a true s)) K 0 A


def Sub (A B : Nat) : Prop := ∀ s, A.testBit s = true → B.testBit s = true

theorem allBelow_intro {P : Nat → Bool} {n : Nat}
    (h : ∀ s, s < n → P s = true) : allBelow P n = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [allBelow, Bool.and_eq_true]
    exact ⟨ih (fun s hs => h s (by omega)), h n (by omega)⟩

theorem subsetB_of_sub {K A B : Nat} (h : Sub A B) : subsetB K A B = true := by
  apply allBelow_intro
  intro s _
  cases hs : A.testBit s
  · rfl
  · simp only [Bool.not_true, Bool.false_or, h s hs]

theorem colConst_of_forall {K A : Nat} {b : Bool}
    (h : ∀ s, s < 2^K → A.testBit s = true → s.testBit 0 = b) :
    colConst K A b = true := by
  apply allBelow_intro
  intro s hs
  cases ha : A.testBit s
  · rfl
  · simp only [Bool.not_true, Bool.false_or, h s hs ha, beq_self_eq_true]

theorem sub_refl (A : Nat) : Sub A A := fun _ h => h

theorem sub_trans {A B C : Nat} (h : Sub A B) (g : Sub B C) : Sub A C :=
  fun s hs => g s (h s hs)

theorem imageAux_forall (K : Nat) (a : Bool) (A : Nat) (P : Nat → Prop)
    (hh : ∀ s, s < 2^K → A.testBit s = true → ∀ z, P (stripStep K a z s)) :
    ∀ n, n ≤ 2^K → ∀ y, (imageAux K a A n).testBit y = true → P y := by
  intro n
  induction n with
  | zero => intro hn y hy; simp [imageAux] at hy
  | succ n ih =>
    intro hn y hy
    rw [imageAux, Nat.testBit_or] at hy
    rcases Bool.or_eq_true_iff.mp hy with hy | hy
    · exact ih (by omega) y hy
    · split at hy
      next ha =>
        rw [Nat.testBit_or, testBit_one_shiftLeft, testBit_one_shiftLeft] at hy
        rcases Bool.or_eq_true_iff.mp hy with hy | hy
        · have he : stripStep K a false n = y := by simpa using hy
          subst y; exact hh n (by omega) ha false
        · have he : stripStep K a true n = y := by simpa using hy
          subst y; exact hh n (by omega) ha true
      next ha => simp at hy

theorem covers_sound {K : Nat} {a : Bool} {A B : Nat} (hc : covers K a A B = true) :
    Sub (image K a A) B := by
  apply imageAux_forall K a A (fun y => B.testBit y = true) _ (2^K) (by omega)
  intro s hs hm z
  have hh := checkMask_spec _ K 0 A hc s hs hm
  simp only [Nat.zero_add, Bool.and_eq_true] at hh
  cases z
  · exact hh.1
  · exact hh.2

theorem word_mono (K : Nat) {A B : Nat} (h : Sub A B) (w : List Bool) :
    Sub (applyWord K w A) (applyWord K w B) := applyWord_mono K w h

theorem cover_cons {K A B C : Nat} {a : Bool} {w : List Bool}
    (h : Sub (image K a A) B) (g : Sub (applyWord K w B) C) :
    Sub (applyWord K (a::w) A) C := sub_trans (word_mono K h w) g

def Const (K S : Nat) (b : Bool) : Prop := ∀ s, s < 2^K → S.testBit s = true → s.testBit 0 = b

def constCheck (K S : Nat) (b : Bool) : Bool := checkMask (fun s => s.testBit 0 == b) K 0 S

theorem constCheck_sound {K S : Nat} {b : Bool} (h : constCheck K S b = true) : Const K S b := by
  intro s hs hm
  have hh := checkMask_spec _ K 0 S h s hs hm
  simpa using hh

theorem const_sub {K A B : Nat} {b : Bool} (hh : Sub A B) (hb : Const K B b) : Const K A b :=
  fun s hs hm => hb s hs (hh s hm)

theorem const_white {K S : Nat} (hK : 0<K) (h : Const K S true) :
    Const K (image K false S) true := by
  intro y hy hm
  apply imageAux_forall K false S (fun y => y.testBit 0 = true) _ (2^K) (by omega) y hm
  intro s hs hmem z
  rw [testBit_stripStep K false z s hs 0 hK, h s hs hmem]
  rfl

theorem const_whites {K S : Nat} (hK : 0<K) (h : Const K S true) (n : Nat) :
    Const K (applyWord K (List.replicate n false) S) true := by
  induction n generalizing S with
  | zero => exact h
  | succ n ih => simpa [List.replicate_succ, applyWord] using ih (const_white hK h)


theorem apply_append (K : Nat) (u v : List Bool) (A : Nat) :
    applyWord K (u++v) A = applyWord K v (applyWord K u A) := by
  induction u generalizing A with
  | nil => rfl
  | cons a u ih => exact ih _

theorem whites_add (K n m A : Nat) :
    applyWord K (List.replicate (n+m) false) A =
      applyWord K (List.replicate m false) (applyWord K (List.replicate n false) A) := by
  have hrep : List.replicate (n+m) false = List.replicate n false ++ List.replicate m false := by
    induction n with
    | zero => simp
    | succ n ih => simp [Nat.succ_add, List.replicate_succ]
  rw [hrep, apply_append]

theorem whites_closed {K B : Nat} (h : Sub (image K false B) B) (n : Nat) :
    Sub (applyWord K (List.replicate n false) B) B := by
  induction n with
  | zero => exact sub_refl B
  | succ n ih =>
    rw [List.replicate_succ, applyWord]
    exact sub_trans (word_mono K h _) ih

/-- A capture after G whites remains valid after any larger number of whites. -/
theorem pump_capture {K r G A B : Nat}
    (cap : Sub (applyWord K (List.replicate r true ++ List.replicate G false) A) B)
    (closed : Sub (image K false B) B) (q : Nat) (hq : G ≤ q) :
    Sub (applyWord K (List.replicate r true ++ List.replicate q false) A) B := by
  rw [apply_append, show q=G+(q-G) by omega, whites_add]
  rw [apply_append] at cap
  exact sub_trans (word_mono K cap _) (whites_closed closed _)

open Ruliology.CellularAutomata
open Rule30Jen Rule30Prize Rule30MaskedJen

theorem no_word_of_invariant (K : Nat) (hK : 1 ≤ K) (w : List Bool) (S k : Nat) (g : Nat → Bool)
    (hw : 0 < w.length)
    (warm : Sub (iterW K w k (fullSet K)) S)
    (closed : Sub (applyWord K w S) S)
    (obs : ∀ φ, φ < w.length → ∀ r, r < 2^K →
      (applyWord K (w.take φ) S).testBit r = true →
      (w.getD φ false || r.testBit 0) = g φ) : ¬ EventuallyWord w := by
  rintro ⟨T, hT⟩
  have hblock : ∀ m s, s < w.length → cell (T + m * w.length + s) 0 = w.getD s false := by
    intro m s hs
    rw [hT _ (by omega), show T + m * w.length + s - T = s + m * w.length by omega,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]
  have hcper : ∀ t, T ≤ t → cell (t + w.length) 0 = cell t 0 := by
    intro t ht
    rw [hT t ht, hT (t + w.length) (by omega), show t + w.length - T = (t - T) + w.length by omega,
      Nat.add_mod_right]
  have hstart : ∃ r, Enc K (T + k * w.length) 0 r ∧ S.testBit r = true := by
    have h0 := enc_encRow K T 0
    have hfull : (fullSet K).testBit (encRow T 0 K) = true := by
      unfold fullSet; rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true h0.1
    obtain ⟨r, he, hmem⟩ := enc_iterW w k T _ _ h0 hfull (fun m s _ hs => hblock m s hs)
    exact ⟨r, he, warm r hmem⟩
  have hinv : ∀ m, ∃ r, Enc K (T + (k + m) * w.length) 0 r ∧ S.testBit r = true := by
    intro m
    induction m with
    | zero => simpa using hstart
    | succ m ih =>
      obtain ⟨r, he, hS⟩ := ih
      obtain ⟨r', he', hS'⟩ := enc_applyWord w _ r S he hS (fun s hs => hblock (k+m) s hs)
      refine ⟨r', ?_, closed r' hS'⟩
      have hm : (k + (m + 1)) * w.length = (k + m) * w.length + w.length := by
        rw [show k + (m + 1) = (k + m) + 1 by omega, Nat.succ_mul]
      rw [hm, ← Nat.add_assoc]
      exact he'
  have hform : ∀ t, T + k * w.length ≤ t → orCol 0 t = g ((t-T)%w.length) := by
    intro t ht
    have hφ : (t-T)%w.length < w.length := Nat.mod_lt _ hw
    have hdec : t = T + (k + ((t-T)/w.length-k))*w.length + (t-T)%w.length := by
      have hd := Nat.div_add_mod (t-T) w.length
      have hq : k ≤ (t-T)/w.length := (Nat.le_div_iff_mul_le hw).2 (by omega)
      rw [show k+((t-T)/w.length-k) = (t-T)/w.length by omega, Nat.mul_comm]
      omega
    obtain ⟨r, he, hS⟩ := hinv ((t-T)/w.length-k)
    obtain ⟨r', he', hS'⟩ := enc_applyWord (w.take ((t-T)%w.length)) _ r S he hS
      (fun s hs => by
        rw [List.length_take] at hs
        have hs' : s < (t-T)%w.length := by omega
        rw [hblock _ s (by omega)]
        simp [List.getD_eq_getElem?_getD, hs'])
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hφ), ← hdec] at he'
    have hcell : cell t 1 = r'.testBit 0 := by
      rw [he'.2 0 (by omega)]; rfl
    unfold orCol
    rw [hT t (by omega)]
    simp only [Int.zero_add]
    rw [hcell]
    exact obs _ hφ r' he'.1 hS'
  refine orCol_not_eventuallyPeriodic 0 ⟨T, w.length, hw, hcper⟩
    ⟨T+k*w.length, w.length, hw, fun t ht => ?_⟩
  show orCol 0 (t+w.length) = orCol 0 t
  rw [hform t ht, hform (t+w.length) (by omega),
    show t+w.length-T = (t-T)+w.length by omega, Nat.add_mod_right]


theorem image_full (K : Nat) (a : Bool) (A : Nat) : Sub (image K a A) (fullSet K) := by
  apply imageAux_forall K a A (fun y => (fullSet K).testBit y = true) _ (2^K) (by omega)
  intro s hs hm z
  simp only [fullSet, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true (stripStep_lt K a z s)

theorem word_full (K : Nat) (w : List Bool) : Sub (applyWord K w (fullSet K)) (fullSet K) := by
  induction w with
  | nil => exact sub_refl _
  | cons a w ih => exact cover_cons (image_full K a _) ih

/-- A finite white-phase profile ending black extends through arbitrarily long white runs. -/
theorem white_profile {K S d : Nat} (hK : 0<K)
    (h : ∀ i, i ≤ d → Const K (applyWord K (List.replicate i false) S) (decide (d ≤ i))) :
    ∀ i, Const K (applyWord K (List.replicate i false) S) (decide (d ≤ i)) := by
  intro i
  by_cases hi : i ≤ d
  · exact h i hi
  · have hd : Const K (applyWord K (List.replicate d false) S) true := by simpa using h d (by omega)
    have hh := const_whites hK hd (i-d)
    rw [← whites_add, show d+(i-d)=i by omega] at hh
    simpa [show d≤i by omega] using hh

def word (r q : Nat) : List Bool := List.replicate r true ++ List.replicate q false

theorem false_getD : ∀ (q i : Nat), (List.replicate q false).getD i false = false
  | 0, _ => rfl
  | _ + 1, 0 => rfl
  | q + 1, i + 1 => by simpa [List.replicate_succ] using false_getD q i

theorem word_getD (r q i : Nat) : (word r q).getD i false = decide (i < r) := by
  induction r generalizing i with
  | zero => change (List.replicate q false).getD i false = false; exact false_getD q i
  | succ r ih =>
    cases i with
    | zero => simp [word, List.replicate_succ]
    | succ i => simpa [word, List.replicate_succ] using ih i

/-- General unbounded-white-run envelope criterion. -/
theorem no_black_white_of_envelope (K r G d S k : Nat) (hK : 1≤K) (hr : 1≤r)
    (warm : ∀ q, G≤q → Sub (iterW K (word r q) k (fullSet K)) S)
    (closed : ∀ q, G≤q → Sub (applyWord K (word r q) S) S)
    (profile : ∀ i, i≤d → Const K
      (applyWord K (List.replicate i false) (applyWord K (List.replicate r true) S)) (decide (d≤i)))
    (q : Nat) (hq : G≤q) : ¬ EventuallyWord (word r q) := by
  apply no_word_of_invariant K hK (word r q) S k
    (fun i => if i<r then true else decide (d≤i-r))
    (by simp [word]; omega) (warm q hq) (closed q hq)
  intro i hi s hs hm
  rw [word_getD]
  by_cases hir : i<r
  · simp [hir]
  · have htake : (word r q).take i = List.replicate r true ++ List.replicate (i-r) false := by
      have hi' : i-r ≤ q := by simp only [word, List.length_append, List.length_replicate] at hi; omega
      simp [word, List.take_append, List.take_replicate, Nat.min_eq_right (by omega : r≤i), Nat.min_eq_left hi']
    rw [htake, apply_append] at hm
    have hh := white_profile (by omega : 0<K) profile (i-r) s hs hm
    simpa [hir] using hh

/-! ## Antisymmetry of `Sub` and exact equivalence `Const K S b ↔ colConst K S b = true` -/

/-- **Antisymmetry of `Sub` and Exact Equivalence `Const K S b ↔ colConst K S b = true` (`sub_antisymm_and_const_iff_colConst`).** -/
theorem sub_antisymm_and_const_iff_colConst (K A B S : Nat) (b : Bool) :
    (Sub A B → Sub B A → A = B) ∧
    (Const K S b ↔ colConst K S b = true) := by
  refine ⟨fun hab hba => Nat.eq_of_testBit_eq fun i => ?_,
          ⟨colConst_of_forall, fun h s hs hm => ?_⟩⟩
  · cases ha : A.testBit i <;> cases hb : B.testBit i
    · rfl
    · have := hba i hb; rw [ha] at this; cases this
    · have := hab i ha; rw [hb] at this; cases this
    · rfl
  · have hall := allBelow_spec h s hs
    rw [hm, Bool.not_true, Bool.false_or, beq_iff_eq] at hall
    exact hall

end Ruliology.CellularAutomata.Rule30RunEnvelopes
