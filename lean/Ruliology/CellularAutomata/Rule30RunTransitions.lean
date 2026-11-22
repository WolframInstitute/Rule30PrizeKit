module

public import Ruliology.CellularAutomata.Rule30StripCertificates

/-!
# Rule 30: run transitions of the center column

Suppose the center column of the single black cell is eventually the repeating word `w`. At a
white letter of `w`, the cell right of the center is often forced by the letters just before it:
nine black letters force it white (`Rule30BlackRuns.nine_black`), and so do some shorter black
runs when the run before them is long enough. If this happens at every white letter of `w`,
column `1` is periodic at the white times, which masked Jen forbids.

**Windows.** Each finite window below is checked on a strip of five cells with the cell beyond
free (`Rule30StripCertificates.applyWord`, sound by `enc_applyWord`), from all `32` strips:

* `1^9` forces column `1` white; `1^4 0 1^7` forces it white; `1^8 0 1^2` forces it black;
* `1^8 0` forces it black; `1^8 0 1 0` forces it white; `1^4 0 1^6 0` and `1^8 0 1^4 0` force it
  black; `1^4 0 1^2 0` forces column `1` or column `2` black.

**Ping-pong.** While the center is black, `a(1) ∨ a(2)` at one step makes `a(1)` white at the next,
and a white `a(1)` makes `a(1) ∨ a(2)` hold at the next (`pp_or`, `pp_zero`). So after a prefix that
forces `a(1) ∨ a(2)`, every odd black run forces column `1` white, and after a prefix that forces
`a(1)` white, every even black run does (`pp_odd`, `pp_even`).

**The theorem** (`not_eventuallyWord_of_good`). If at every white letter of `w` the cyclic
letters before it end with one of

* `1^9`, `1^4 0 1^7`, `1^8 0 1^2`,
* `1^8 0 1^r`, `1^4 0 1^2 0 1^r`, `1^4 0 1^6 0 1^r`, `1^8 0 1^4 0 1^r` with `r` odd,
* `1^8 0 1 0 1^r` with `r` even,

then the center column is not eventually `w`, whatever the transient. For a word whose white
letters are isolated and whose cyclic black runs are `r₁, …, r_k`, this holds when every `i` has
one of: `r_i ≥ 9`; `r_i = 7` and `r_{i-1} ≥ 4`; `r_i ∈ {1, 2, 3, 5}` and `r_{i-1} ≥ 8`; `r_i`
odd, `r_{i-1} ∈ {2, 6}` and `r_{i-2} ≥ 4`; `r_i` odd, `r_{i-1} = 4` and `r_{i-2} ≥ 8`; `r_i`
even, `r_{i-1} = 1` and `r_{i-2} ≥ 8`. Examples: the runs `(9, 7, 7)`, `(9, 5, 7)`,
`(9, 1, 8, 1, 8)`, `(9, 2, 5, 7, 7)`.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30RunTransitions

open Rule30Jen Rule30Prize Rule30MaskedJen Rule30StripCertificates

/-! ### Window forcing on strips -/

/-- Every state of the strip set `S` satisfies `p`. -/
def allIn (K S : Nat) (p : Nat → Bool) : Bool := allBelow (fun s => !S.testBit s || p s) (2 ^ K)

theorem fullSet_testBit (K x : Nat) (hx : x < 2 ^ K) : (fullSet K).testBit x = true := by
  unfold fullSet
  rw [Nat.testBit_two_pow_sub_one]
  exact decide_eq_true hx

/-- The center column reads `v` on `[s, s + v.length)`. -/
def Occ (s : Nat) (v : List Bool) : Prop := ∀ k, k < v.length → cell (s + k) 0 = v.getD k false

/-- **Soundness of a window check.** -/
theorem window_sound (K : Nat) (u : List Bool) (p : Nat → Bool)
    (h : allIn K (applyWord K u (fullSet K)) p = true) (t : Nat) (hu : Occ t u) :
    ∃ r, Enc K (t + u.length) 0 r ∧ p r = true := by
  obtain ⟨r, he, hm⟩ := enc_applyWord (K := K) (j := 0) u t (encRow t 0 K) (fullSet K)
    (enc_encRow K t 0) (fullSet_testBit K _ (enc_encRow K t 0).1) hu
  refine ⟨r, he, ?_⟩
  have := allBelow_spec h r he.1
  simpa [hm] using this

theorem enc_col1 {K t r : Nat} (hK : 1 ≤ K) (h : Enc K t 0 r) : cell t 1 = r.testBit 0 := by
  have := h.2 0 (by omega)
  simpa using this.symm

theorem enc_col2 {K t r : Nat} (hK : 2 ≤ K) (h : Enc K t 0 r) : cell t 2 = r.testBit 1 := by
  have := h.2 1 (by omega)
  simpa using this.symm

/-! ### The windows -/

/-- `n` black letters. -/
def ones (n : Nat) : List Bool := List.replicate n true

def w9 : List Bool := ones 9
def w7 : List Bool := ones 4 ++ [false] ++ ones 7
def w2 : List Bool := ones 8 ++ [false] ++ ones 2
def a8 : List Bool := ones 8 ++ [false]
def b42 : List Bool := ones 4 ++ [false] ++ ones 2 ++ [false]
def b46 : List Bool := ones 4 ++ [false] ++ ones 6 ++ [false]
def b84 : List Bool := ones 8 ++ [false] ++ ones 4 ++ [false]
def b81 : List Bool := ones 8 ++ [false, true, false]

def col1White (r : Nat) : Bool := !r.testBit 0
def col1Black (r : Nat) : Bool := r.testBit 0
def col12Or (r : Nat) : Bool := r.testBit 0 || r.testBit 1

theorem chk_w9 : allIn 5 (applyWord 5 w9 (fullSet 5)) col1White = true := by decide +kernel
theorem chk_w7 : allIn 5 (applyWord 5 w7 (fullSet 5)) col1White = true := by decide +kernel
theorem chk_w2 : allIn 5 (applyWord 5 w2 (fullSet 5)) col1Black = true := by decide +kernel
theorem chk_a8 : allIn 5 (applyWord 5 a8 (fullSet 5)) col1Black = true := by decide +kernel
theorem chk_b42 : allIn 5 (applyWord 5 b42 (fullSet 5)) col12Or = true := by decide +kernel
theorem chk_b46 : allIn 5 (applyWord 5 b46 (fullSet 5)) col1Black = true := by decide +kernel
theorem chk_b84 : allIn 5 (applyWord 5 b84 (fullSet 5)) col1Black = true := by decide +kernel
theorem chk_b81 : allIn 5 (applyWord 5 b81 (fullSet 5)) col1White = true := by decide +kernel

theorem force_white {u : List Bool} (h : allIn 5 (applyWord 5 u (fullSet 5)) col1White = true)
    {t : Nat} (hu : Occ t u) : cell (t + u.length) 1 = false := by
  obtain ⟨r, he, hp⟩ := window_sound 5 u col1White h t hu
  rw [enc_col1 (by decide) he]
  simpa [col1White] using hp

theorem force_black {u : List Bool} (h : allIn 5 (applyWord 5 u (fullSet 5)) col1Black = true)
    {t : Nat} (hu : Occ t u) : cell (t + u.length) 1 = true := by
  obtain ⟨r, he, hp⟩ := window_sound 5 u col1Black h t hu
  rw [enc_col1 (by decide) he]
  simpa [col1Black] using hp

theorem force_or {u : List Bool} (h : allIn 5 (applyWord 5 u (fullSet 5)) col12Or = true)
    {t : Nat} (hu : Occ t u) : (cell (t + u.length) 1 || cell (t + u.length) 2) = true := by
  obtain ⟨r, he, hp⟩ := window_sound 5 u col12Or h t hu
  rw [enc_col1 (by decide) he, enc_col2 (by decide) he]
  simpa [col12Or] using hp

/-! ### Ping-pong under a black center -/

theorem cell_succ (t : Nat) (i : Int) :
    cell (t + 1) i = rule (cell t (i - 1)) (cell t i) (cell t (i + 1)) := rfl

/-- A black center turns `a(1) ∨ a(2)` into a white `a(1)`. -/
theorem pp_or (t : Nat) (hc : cell t 0 = true) (h : (cell t 1 || cell t 2) = true) :
    cell (t + 1) 1 = false := by
  rw [cell_succ, show (1 : Int) - 1 = 0 by decide, show (1 : Int) + 1 = 2 by decide, hc]
  unfold rule
  rw [h]
  rfl

/-- A black center turns a white `a(1)` into `a(1) ∨ a(2)`. -/
theorem pp_zero (t : Nat) (hc : cell t 0 = true) (h : cell t 1 = false) :
    (cell (t + 1) 1 || cell (t + 1) 2) = true := by
  rw [cell_succ, cell_succ, show (1 : Int) - 1 = 0 by decide, show (1 : Int) + 1 = 2 by decide,
    show (2 : Int) - 1 = 1 by decide, show (2 : Int) + 1 = 3 by decide, hc, h]
  unfold rule
  cases cell t 2 <;> cases cell t 3 <;> rfl

/-- After `a(1) ∨ a(2)`, an odd black run forces `a(1)` white. -/
theorem pp_odd : ∀ (n s : Nat), (∀ k, k < 2 * n + 1 → cell (s + k) 0 = true) →
    (cell s 1 || cell s 2) = true → cell (s + (2 * n + 1)) 1 = false
  | 0, s, hb, h => by simpa using pp_or s (by simpa using hb 0 (by omega)) h
  | n + 1, s, hb, h => by
    have h1 : cell (s + 1) 1 = false := pp_or s (by simpa using hb 0 (by omega)) h
    have h2 : (cell (s + 1 + 1) 1 || cell (s + 1 + 1) 2) = true :=
      pp_zero (s + 1) (by simpa using hb 1 (by omega)) h1
    have := pp_odd n (s + 1 + 1) (fun k hk => by
      have e := hb (k + 2) (by omega)
      rwa [show s + (k + 2) = s + 1 + 1 + k by omega] at e) h2
    rwa [show s + 1 + 1 + (2 * n + 1) = s + (2 * (n + 1) + 1) by omega] at this

/-- After a white `a(1)`, an even black run forces `a(1)` white. -/
theorem pp_even : ∀ (n s : Nat), (∀ k, k < 2 * n → cell (s + k) 0 = true) →
    cell s 1 = false → cell (s + 2 * n) 1 = false
  | 0, s, _, h => by simpa using h
  | n + 1, s, hb, h => by
    have h1 : (cell (s + 1) 1 || cell (s + 1) 2) = true :=
      pp_zero s (by simpa using hb 0 (by omega)) h
    have h2 : cell (s + 1 + 1) 1 = false := pp_or (s + 1) (by simpa using hb 1 (by omega)) h1
    have := pp_even n (s + 1 + 1) (fun k hk => by
      have e := hb (k + 2) (by omega)
      rwa [show s + (k + 2) = s + 1 + 1 + k by omega] at e) h2
    rwa [show s + 1 + 1 + 2 * n = s + 2 * (n + 1) by omega] at this

/-! ### Occurrences of concatenated windows -/

theorem occ_left {s : Nat} {a b : List Bool} (h : Occ s (a ++ b)) : Occ s a := by
  intro k hk
  have := h k (by simp; omega)
  rwa [List.getD_eq_getElem?_getD, List.getElem?_append_left hk,
    ← List.getD_eq_getElem?_getD] at this

theorem occ_right {s : Nat} {a b : List Bool} (h : Occ s (a ++ b)) : Occ (s + a.length) b := by
  intro k hk
  have := h (a.length + k) (by simp; omega)
  rwa [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
    show a.length + k - a.length = k by omega, ← List.getD_eq_getElem?_getD,
    show s + (a.length + k) = s + a.length + k by omega] at this

theorem getD_ones {n k : Nat} (hk : k < n) : (ones n).getD k false = true := by
  simp [ones, hk]

theorem occ_ones {s n : Nat} (h : Occ s (ones n)) : ∀ k, k < n → cell (s + k) 0 = true := by
  intro k hk
  have := h k (by simp [ones]; exact hk)
  rwa [getD_ones hk] at this

theorem length_ones (n : Nat) : (ones n).length = n := by simp [ones]

/-- A prefix forcing `a(1) ∨ a(2)` followed by an odd black run forces column `1` white. -/
theorem force_or_odd {p : List Bool} (hp : allIn 5 (applyWord 5 p (fullSet 5)) col12Or = true)
    (n : Nat) {t : Nat} (h : Occ t (p ++ ones (2 * n + 1))) :
    cell (t + (p ++ ones (2 * n + 1)).length) 1 = false := by
  have h1 := force_or hp (occ_left h)
  have h2 := pp_odd n (t + p.length) (by
    have := occ_ones (occ_right h); exact this) h1
  rwa [List.length_append, length_ones, ← Nat.add_assoc]

/-- A prefix forcing column `1` black followed by an odd black run forces column `1` white. -/
theorem force_black_odd {p : List Bool} (hp : allIn 5 (applyWord 5 p (fullSet 5)) col1Black = true)
    (n : Nat) {t : Nat} (h : Occ t (p ++ ones (2 * n + 1))) :
    cell (t + (p ++ ones (2 * n + 1)).length) 1 = false := by
  have h1 := force_black hp (occ_left h)
  have h1' : (cell (t + p.length) 1 || cell (t + p.length) 2) = true := by simp [h1]
  have h2 := pp_odd n (t + p.length) (occ_ones (occ_right h)) h1'
  rwa [List.length_append, length_ones, ← Nat.add_assoc]

/-- A prefix forcing column `1` white followed by an even black run forces column `1` white. -/
theorem force_white_even {p : List Bool} (hp : allIn 5 (applyWord 5 p (fullSet 5)) col1White = true)
    (n : Nat) {t : Nat} (h : Occ t (p ++ ones (2 * n))) :
    cell (t + (p ++ ones (2 * n)).length) 1 = false := by
  have h1 := force_white hp (occ_left h)
  have h2 := pp_even n (t + p.length) (occ_ones (occ_right h)) h1
  rwa [List.length_append, length_ones, ← Nat.add_assoc]

/-! ### The theorem -/

/-- Letter `n` of `w` repeated, read cyclically. -/
def cyc (w : List Bool) (n : Nat) : Bool := w.getD (n % w.length) false

/-- The cyclic letters of `w` just before position `j` end with `v`. -/
def EndsWith (w : List Bool) (j : Nat) (v : List Bool) : Prop :=
  ∀ k, k < v.length → cyc w (j + v.length * w.length - v.length + k) = v.getD k false

instance (w : List Bool) (j : Nat) (v : List Bool) : Decidable (EndsWith w j v) :=
  inferInstanceAs (Decidable (∀ k, k < v.length → _))

/-- **The run-transition condition at a white letter.** -/
def Good (w : List Bool) (j : Nat) : Prop :=
  EndsWith w j w9 ∨ EndsWith w j w7 ∨ EndsWith w j w2 ∨
  (∃ n, n < w.length ∧ (EndsWith w j (a8 ++ ones (2 * n + 1)) ∨
    EndsWith w j (b42 ++ ones (2 * n + 1)) ∨ EndsWith w j (b46 ++ ones (2 * n + 1)) ∨
    EndsWith w j (b84 ++ ones (2 * n + 1)))) ∨
  (∃ n, n < w.length ∧ EndsWith w j (b81 ++ ones (2 * n)))

instance (w : List Bool) (j : Nat) : Decidable (Good w j) := by
  unfold Good; infer_instance

/-- Every white letter of `w` satisfies the run-transition condition. -/
def AllGood (w : List Bool) : Prop := ∀ j, j < w.length → w.getD j false = false → Good w j

instance (w : List Bool) : Decidable (AllGood w) :=
  inferInstanceAs (Decidable (∀ j, j < w.length → _))

/-- Reading `w` from time `T`, a window that ends at a time of phase `j` is an occurrence. -/
theorem occ_of_endsWith {w : List Bool} (hP : 0 < w.length) {T : Nat}
    (hT : ∀ t, T ≤ t → cell t 0 = w.getD ((t - T) % w.length) false)
    {j : Nat} {v : List Bool} (hv : EndsWith w j v) {t : Nat} (ht : T + v.length ≤ t)
    (hj : (t - T) % w.length = j) : Occ (t - v.length) v := by
  intro k hk
  rw [hT _ (by omega), ← hv k hk]
  unfold cyc
  congr 1
  -- both indices agree modulo the period
  have hA : v.length ≤ v.length * w.length := Nat.le_mul_of_pos_right _ hP
  obtain ⟨q, hq⟩ : ∃ q, t - T = q * w.length + j :=
    ⟨(t - T) / w.length, by rw [← hj, Nat.mul_comm]; exact (Nat.div_add_mod _ _).symm⟩
  have key : (t - v.length + k - T) + v.length * w.length =
      (j + v.length * w.length - v.length + k) + q * w.length := by
    generalize v.length * w.length = A at hA ⊢
    generalize q * w.length = B at hq ⊢
    omega
  have := congrArg (· % w.length) key
  simpa [Nat.add_mul_mod_self_right] using this

/-- Pattern lengths are bounded by the period plus `13`. -/
theorem forced_const {w : List Bool} (hP : 0 < w.length) {T : Nat}
    (hT : ∀ t, T ≤ t → cell t 0 = w.getD ((t - T) % w.length) false)
    {j : Nat} (hg : Good w j) :
    ∃ b, ∀ t, T + 3 * w.length + 16 ≤ t → (t - T) % w.length = j → cell t 1 = b := by
  -- one occurrence lemma per window shape
  have win : ∀ (v : List Bool), EndsWith w j v → v.length ≤ 3 * w.length + 16 →
      ∀ t, T + 3 * w.length + 16 ≤ t → (t - T) % w.length = j →
        Occ (t - v.length) v ∧ t - v.length + v.length = t := by
    intro v hv hl t ht htj
    exact ⟨occ_of_endsWith hP hT hv (by omega) htj, by omega⟩
  rcases hg with h | h | h | ⟨n, hn, h | h | h | h⟩ | ⟨n, hn, h⟩
  · refine ⟨false, fun t ht htj => ?_⟩
    obtain ⟨ho, he⟩ := win _ h (by simp [w9, ones] <;> omega) t ht htj
    have := force_white chk_w9 ho; rwa [he] at this
  · refine ⟨false, fun t ht htj => ?_⟩
    obtain ⟨ho, he⟩ := win _ h (by simp [w7, ones] <;> omega) t ht htj
    have := force_white chk_w7 ho; rwa [he] at this
  · refine ⟨true, fun t ht htj => ?_⟩
    obtain ⟨ho, he⟩ := win _ h (by simp [w2, ones] <;> omega) t ht htj
    have := force_black chk_w2 ho; rwa [he] at this
  · refine ⟨false, fun t ht htj => ?_⟩
    obtain ⟨ho, he⟩ := win _ h (by simp [a8, ones] <;> omega) t ht htj
    have := force_black_odd chk_a8 n ho; rwa [he] at this
  · refine ⟨false, fun t ht htj => ?_⟩
    obtain ⟨ho, he⟩ := win _ h (by simp [b42, ones] <;> omega) t ht htj
    have := force_or_odd chk_b42 n ho; rwa [he] at this
  · refine ⟨false, fun t ht htj => ?_⟩
    obtain ⟨ho, he⟩ := win _ h (by simp [b46, ones] <;> omega) t ht htj
    have := force_black_odd chk_b46 n ho; rwa [he] at this
  · refine ⟨false, fun t ht htj => ?_⟩
    obtain ⟨ho, he⟩ := win _ h (by simp [b84, ones] <;> omega) t ht htj
    have := force_black_odd chk_b84 n ho; rwa [he] at this
  · refine ⟨false, fun t ht htj => ?_⟩
    obtain ⟨ho, he⟩ := win _ h (by simp [b81, ones] <;> omega) t ht htj
    have := force_white_even chk_b81 n ho; rwa [he] at this

/-- **Run-transition theorem.** If every white letter of the nonempty word `w` satisfies the
run-transition condition, the center column is not eventually `w`, whatever the transient. -/
theorem not_eventuallyWord_of_good (w : List Bool) (hw : w ≠ []) (hg : AllGood w) :
    ¬ EventuallyWord w := by
  rintro ⟨T, hT⟩
  have hP : 0 < w.length := List.length_pos_iff.2 hw
  have hc : ∀ t, T ≤ t → cell (t + w.length) 0 = cell t 0 := by
    intro t ht
    rw [hT t ht, hT (t + w.length) (by omega), show t + w.length - T = (t - T) + w.length by omega,
      Nat.add_mod_right]
  refine masked_jen_center hP hc (T + 3 * w.length + 16) (fun t ht hwhite => ?_)
  have hj : (t - T) % w.length < w.length := Nat.mod_lt _ hP
  have hwj : w.getD ((t - T) % w.length) false = false := by rw [← hT t (by omega)]; exact hwhite
  obtain ⟨b, hb⟩ := forced_const hP hT (hg _ hj hwj)
  rw [hb (t + w.length) (by omega)
      (by rw [show t + w.length - T = (t - T) + w.length by omega, Nat.add_mod_right]),
    hb t ht rfl]

/-! ### Run-length words and examples -/

/-- The word with black runs `rs`, each followed by one white letter. -/
def runsWord : List Nat → List Bool
  | [] => []
  | r :: rs => ones r ++ [false] ++ runsWord rs

/-- Two sevens after a long run: three-cell window sets after nine black cells lose track here. -/
theorem not_eventually_9_7_7 : ¬ EventuallyWord (runsWord [9, 7, 7]) :=
  not_eventuallyWord_of_good _ (by decide) (by decide +kernel)

/-- A five, then a seven. -/
theorem not_eventually_9_5_7 : ¬ EventuallyWord (runsWord [9, 5, 7]) :=
  not_eventuallyWord_of_good _ (by decide) (by decide +kernel)

/-- Two `(1, 8)` blocks after a long run. -/
theorem not_eventually_9_1_8_1_8 : ¬ EventuallyWord (runsWord [9, 1, 8, 1, 8]) :=
  not_eventuallyWord_of_good _ (by decide) (by decide +kernel)

/-- A two, a five and two sevens. -/
theorem not_eventually_9_2_5_7_7 : ¬ EventuallyWord (runsWord [9, 2, 5, 7, 7]) :=
  not_eventuallyWord_of_good _ (by decide) (by decide +kernel)

/-- A four and a six between sevens. -/
theorem not_eventually_9_1_4_7_9_1_6_7_7 :
    ¬ EventuallyWord (runsWord [9, 1, 4, 7, 9, 1, 6, 7, 7]) :=
  not_eventuallyWord_of_good _ (by decide) (by decide +kernel)

end Rule30RunTransitions
end Ruliology.CellularAutomata
