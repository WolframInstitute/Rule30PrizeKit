module

public import Ruliology.CellularAutomata.Rule30StripCertificates

/-!
# White padding before 10111

For every `q ≥ 9`, the single-seed Rule 30 center is not eventually a repetition
of `0^q 10111`. The proof uses closed reachable-set envelopes on eight-cell
strips and the masked Jen theorem. All right-boundary bits remain arbitrary.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30WhitePad10111
open Ruliology.CellularAutomata.Rule30StripCertificates

def Sub (A B : Nat) : Prop := ∀ s, A.testBit s = true → B.testBit s = true

theorem sub_refl (A : Nat) : Sub A A := fun _ h => h

theorem sub_trans {A B C : Nat} (h : Sub A B) (g : Sub B C) : Sub A C :=
  fun s hs => g s (h s hs)

theorem sub_of_and {A B : Nat} (h : A &&& B = A) : Sub A B := by
  intro s hs
  have hbit := congrArg (fun n : Nat => n.testBit s) h
  rw [Nat.testBit_and, hs, Bool.true_and] at hbit
  exact hbit

theorem image_mono {A B : Nat} (h : Sub A B) (a : Bool) :
    Sub (image 8 a A) (image 8 a B) :=
  imageAux_mono h (2^8)

theorem word_mono {A B : Nat} (h : Sub A B) (u : List Bool) :
    Sub (applyWord 8 u A) (applyWord 8 u B) := applyWord_mono 8 u h

def wp : Nat → Nat → Nat
  | 0, A => A
  | n+1, A => image 8 false (wp n A)

theorem wp_mono {A B : Nat} (h : Sub A B) (n : Nat) : Sub (wp n A) (wp n B) := by
  induction n with
  | zero => exact h
  | succ n ih => exact image_mono ih false

theorem wp_add (n m A : Nat) : wp (n+m) A = wp n (wp m A) := by
  induction n with
  | zero => simp only [Nat.zero_add, wp]
  | succ n ih =>
    rw [show n+1+m = (n+m)+1 by omega]
    simp only [wp, ih]

theorem wp_closed {U : Nat} (h : Sub (image 8 false U) U) (n : Nat) : Sub (wp n U) U := by
  induction n with
  | zero => exact sub_refl U
  | succ n ih => exact sub_trans (image_mono ih false) h

def tail : List Bool := [true, false, true, true, true]
def driver (q : Nat) : List Bool := List.replicate q false ++ tail
def mac (q A : Nat) : Nat := applyWord 8 tail (wp q A)

theorem capture {A U B : Nat}
    (entry : Sub (wp 9 A) U) (closed : Sub (image 8 false U) U)
    (exit : Sub (applyWord 8 tail U) B) {q : Nat} (hq : 9 ≤ q) : Sub (mac q A) B := by
  have h1 : Sub (wp q A) U := by
    rw [show q = (q-9)+9 by omega, wp_add]
    exact sub_trans (wp_mono entry (q-9)) (wp_closed closed (q-9))
  exact sub_trans (word_mono h1 tail) exit

theorem apply_append (u v : List Bool) (A : Nat) :
    applyWord 8 (u++v) A = applyWord 8 v (applyWord 8 u A) := by
  induction u generalizing A with
  | nil => rfl
  | cons a u ih => exact ih _

theorem wp_comm (n A : Nat) : wp n (image 8 false A) = image 8 false (wp n A) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [wp, ih]

theorem wp_eq (n A : Nat) : wp n A = applyWord 8 (List.replicate n false) A := by
  induction n generalizing A with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, applyWord, ← ih, wp_comm]
    rfl

theorem mac_eq (q A : Nat) : mac q A = applyWord 8 (driver q) A := by
  rw [driver, apply_append, ← wp_eq]
  rfl

def A0 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def U0 : Nat := 0xa868b02aa120302920298022a128222ba868a02b2120102220298062a028222b
def A1 : Nat := 0x4415451444116545444564154405255504150554440164154545641504056554
def U1 : Nat := 0xa028a02aa020202820288022a020202aa028a02a2020002220288022a020202a
def A2 : Nat := 0x414041444104444044404144404045404140454440044140444041404044454
def U2 : Nat := 0x2028202820202028202800202020202820282028202000202028002020202028
def A3 : Nat := 0x400040404000404040004040404040404000400000004040400040404040404
def U3 : Nat := 0x2028202820202028202800202020202820282028202000202028002020202028

theorem entry0 : wp 9 A0 &&& U0 = wp 9 A0 := by decide +kernel
theorem closed0 : image 8 false U0 &&& U0 = image 8 false U0 := by decide +kernel
theorem exit0 : applyWord 8 tail U0 &&& A1 = applyWord 8 tail U0 := by decide +kernel
theorem stage0 {q : Nat} (hq : 9 ≤ q) : Sub (mac q A0) A1 :=
  capture (sub_of_and entry0) (sub_of_and closed0) (sub_of_and exit0) hq

theorem entry1 : wp 9 A1 &&& U1 = wp 9 A1 := by decide +kernel
theorem closed1 : image 8 false U1 &&& U1 = image 8 false U1 := by decide +kernel
theorem exit1 : applyWord 8 tail U1 &&& A2 = applyWord 8 tail U1 := by decide +kernel
theorem stage1 {q : Nat} (hq : 9 ≤ q) : Sub (mac q A1) A2 :=
  capture (sub_of_and entry1) (sub_of_and closed1) (sub_of_and exit1) hq

theorem entry2 : wp 9 A2 &&& U2 = wp 9 A2 := by decide +kernel
theorem closed2 : image 8 false U2 &&& U2 = image 8 false U2 := by decide +kernel
theorem exit2 : applyWord 8 tail U2 &&& A3 = applyWord 8 tail U2 := by decide +kernel
theorem stage2 {q : Nat} (hq : 9 ≤ q) : Sub (mac q A2) A3 :=
  capture (sub_of_and entry2) (sub_of_and closed2) (sub_of_and exit2) hq

theorem entry3 : wp 9 A3 &&& U3 = wp 9 A3 := by decide +kernel
theorem closed3 : image 8 false U3 &&& U3 = image 8 false U3 := by decide +kernel
theorem exit3 : applyWord 8 tail U3 &&& A3 = applyWord 8 tail U3 := by decide +kernel
theorem stage3 {q : Nat} (hq : 9 ≤ q) : Sub (mac q A3) A3 :=
  capture (sub_of_and entry3) (sub_of_and closed3) (sub_of_and exit3) hq

theorem mac_mono (q : Nat) {A B : Nat} (h : Sub A B) : Sub (mac q A) (mac q B) :=
  word_mono (wp_mono h q) tail

/-- Three independent white-run lengths, all at least nine, enter the same 24-state invariant. -/
theorem three_blocks {q₁ q₂ q₃ : Nat} (h₁ : 9 ≤ q₁) (h₂ : 9 ≤ q₂) (h₃ : 9 ≤ q₃) :
    Sub (mac q₃ (mac q₂ (mac q₁ A0))) A3 :=
  sub_trans (mac_mono q₃ (sub_trans (mac_mono q₂ (stage0 h₁)) (stage1 h₂))) (stage2 h₃)

/-- The invariant allows any next white-run length at least nine. -/
theorem invariant {q : Nat} (hq : 9 ≤ q) : Sub (mac q A3) A3 := stage3 hq

def oddMask : Nat := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
theorem white_start : colConst 8 A3 false = true := by decide +kernel
theorem white_first : image 8 false A3 &&& oddMask = image 8 false A3 := by decide +kernel
theorem white_odd_closed : image 8 false oddMask &&& oddMask = image 8 false oddMask := by decide +kernel
theorem odd_bit : colConst 8 oddMask true = true := by decide +kernel
theorem tail_white : colConst 8 (image 8 true U3) false = true := by decide +kernel

theorem white_positive {n : Nat} (hn : 1 ≤ n) : Sub (wp n A3) oddMask := by
  rw [show n = (n-1)+1 by omega, wp_add]
  exact sub_trans (wp_mono (sub_of_and white_first) (n-1))
    (wp_closed (sub_of_and white_odd_closed) (n-1))

open Ruliology.CellularAutomata
open Rule30Jen Rule30Prize Rule30MaskedJen

/-- A reachable invariant set with a deterministic masked observation excludes an eventual driver. -/
theorem no_word_of_invariant (w : List Bool) (S k : Nat) (g : Nat → Bool)
    (hw : 0 < w.length)
    (warm : Sub (iterW 8 w k (fullSet 8)) S)
    (closed : Sub (applyWord 8 w S) S)
    (obs : ∀ φ, φ < w.length → ∀ r, r < 2^8 →
      (applyWord 8 (w.take φ) S).testBit r = true →
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
  have hstart : ∃ r, Enc 8 (T + k * w.length) 0 r ∧ S.testBit r = true := by
    have h0 := enc_encRow 8 T 0
    have hfull : (fullSet 8).testBit (encRow T 0 8) = true := by
      unfold fullSet; rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true h0.1
    obtain ⟨r, he, hmem⟩ := enc_iterW w k T _ _ h0 hfull (fun m s _ hs => hblock m s hs)
    exact ⟨r, he, warm r hmem⟩
  have hinv : ∀ m, ∃ r, Enc 8 (T + (k + m) * w.length) 0 r ∧ S.testBit r = true := by
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

theorem const_mem {S r : Nat} {b : Bool} (h : colConst 8 S b = true)
    (hr : r < 2^8) (hm : S.testBit r = true) : r.testBit 0 = b := by
  have h' := allBelow_spec h r hr
  rw [hm, Bool.not_true, Bool.false_or, beq_iff_eq] at h'
  exact h'

theorem driver_length (q : Nat) : (driver q).length = q+5 := by simp [driver, tail]

theorem get_white {q i : Nat} (h : i < q) : (driver q).getD i false = false := by
  simp [driver, List.getD_eq_getElem?_getD, List.getElem?_append, h]

theorem get_tail (q j : Nat) : (driver q).getD (q+j) false = tail.getD j false := by
  simp [driver, List.getD_eq_getElem?_getD, List.getElem?_append, show ¬q+j<q by omega]

theorem take_white {q i : Nat} (h : i ≤ q) :
    (driver q).take i = List.replicate i false := by
  simp [driver, List.take_append, Nat.min_eq_left h, Nat.sub_eq_zero_of_le h]

theorem take_tail_white (q : Nat) :
    (driver q).take (q+1) = List.replicate q false ++ [true] := by
  simp [driver, tail, List.take_append]

theorem white_long {q : Nat} (hq : 9 ≤ q) : Sub (wp q A3) U3 := by
  rw [show q=(q-9)+9 by omega, wp_add]
  exact sub_trans (wp_mono (sub_of_and entry3) (q-9))
    (wp_closed (sub_of_and closed3) (q-9))

def masked (q i : Nat) : Bool := !(decide (i=0) || decide (i=q+1))

theorem observed {q : Nat} (hq : 9 ≤ q) (i : Nat) (hi : i < (driver q).length)
    (r : Nat) (hr : r < 2^8) (hm : (applyWord 8 ((driver q).take i) A3).testBit r = true) :
    ((driver q).getD i false || r.testBit 0) = masked q i := by
  rw [driver_length] at hi
  by_cases hw : i < q
  · rw [get_white hw, Bool.false_or]
    rw [take_white (Nat.le_of_lt hw), ← wp_eq] at hm
    by_cases hz : i=0
    · subst i
      rw [const_mem white_start hr hm]
      simp [masked]
    · rw [const_mem odd_bit hr (white_positive (by omega) r hm)]
      simp [masked, hz, show i ≠ q+1 by omega]
  · obtain h0 | h1 | h2 | h3 | h4 : i=q ∨ i=q+1 ∨ i=q+2 ∨ i=q+3 ∨ i=q+4 := by omega
    · subst i
      have hv : (driver q).getD q false = true := by simpa [tail] using get_tail q 0
      rw [hv, Bool.true_or]
      simp [masked, show q ≠ 0 by omega]
    · subst i
      have hv : (driver q).getD (q+1) false = false := by simpa [tail] using get_tail q 1
      rw [hv, Bool.false_or]
      rw [take_tail_white, apply_append, ← wp_eq] at hm
      have hb := image_mono (white_long hq) true r hm
      rw [const_mem tail_white hr hb]
      simp [masked]
    · subst i
      have hv : (driver q).getD (q+2) false = true := by simpa [tail] using get_tail q 2
      rw [hv, Bool.true_or]
      simp [masked]
    · subst i
      have hv : (driver q).getD (q+3) false = true := by simpa [tail] using get_tail q 3
      rw [hv, Bool.true_or]
      simp [masked]
    · subst i
      have hv : (driver q).getD (q+4) false = true := by simpa [tail] using get_tail q 4
      rw [hv, Bool.true_or]
      simp [masked]

theorem full_A0 : fullSet 8 = A0 := by decide +kernel

/-- Every white padding q≥9 before the fixed tail10111 is excluded, for every transient. -/
theorem not_eventually_zeros_10111 (q : Nat) (hq : 9 ≤ q) :
    ¬ EventuallyWord (List.replicate q false ++ [true, false, true, true, true]) := by
  change ¬ EventuallyWord (driver q)
  apply no_word_of_invariant (driver q) A3 3 (masked q) (by rw [driver_length]; omega)
  · simpa only [iterW, full_A0, ← mac_eq] using three_blocks hq hq hq
  · rw [← mac_eq]
    exact invariant hq
  · exact observed hq

/-! ### Multi-period stability of `A3` under `iterW` and post-padded `10111 0^q` exclusion (`q ≥ 9`) -/

/-- **Multi-Period Stability of the 24-State Invariant `A3` (`iterW_driver_A3_sub`).** -/
theorem iterW_driver_A3_sub {q : Nat} (hq : 9 ≤ q) :
    ∀ m : Nat, Sub (iterW 8 (driver q) m A3) A3
  | 0 => sub_refl A3
  | m + 1 => by
    unfold iterW
    rw [← mac_eq]
    have hstep : Sub (iterW 8 (driver q) m (mac q A3)) (iterW 8 (driver q) m A3) := by
      have hmono : ∀ (k : Nat) {X Y : Nat}, Sub X Y → Sub (iterW 8 (driver q) k X) (iterW 8 (driver q) k Y) := by
        intro k
        induction k with
        | zero => intro X Y h; exact h
        | succ k ih => intro X Y h; exact ih (word_mono h (driver q))
      exact hmono m (invariant hq)
    exact sub_trans hstep (iterW_driver_A3_sub hq m)

/-- **Multi-Period Closure of `wp` Under `U0`, `U1`, `U2`, and `U3` (`wp_envelopes_closed`).** -/
theorem wp_envelopes_closed (n : Nat) :
    Sub (wp n U0) U0 ∧ Sub (wp n U1) U1 ∧ Sub (wp n U2) U2 ∧ Sub (wp n U3) U3 :=
  ⟨wp_closed (sub_of_and closed0) n,
   wp_closed (sub_of_and closed1) n,
   wp_closed (sub_of_and closed2) n,
   wp_closed (sub_of_and closed3) n⟩

end Ruliology.CellularAutomata.Rule30WhitePad10111
