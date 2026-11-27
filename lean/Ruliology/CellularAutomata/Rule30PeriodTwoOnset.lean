module

public import Ruliology.CellularAutomata.Rule30Prize
public import Ruliology.CellularAutomata.Rule30Jen

/-!
# Period 2: the column-1 words of widths 5 and 6 from two ticks on, for every history

`Rule30PeriodTwoWidth5.col1_constraints` and `Rule30PeriodTwoWidth6.col1_constraints` say: if the
center column of rule 30 from a single black cell is white, black, white, … from a time `T`, then
from some later time on, column `1` read at consecutive white times never spells a word of their
lists `col1Forbidden`. This module gives the later time, `T + 2`, and drops the single seed: the
same words are excluded for every space-time history `H : Nat → Int → Bool` that obeys rule 30 at
the columns `1..b` (`Obeys`), whatever its other columns do, finite or not.

* `win_dstep`: if column `0` is white at the tick `s` and black at `s + 1`, the window of columns
  `1..b` at `s + 2` is the double step `dstep` of the window at `s`, whose only other inputs are the
  two cells of column `b + 1` at `s` and `s + 1`.
* `img5_length`, `img6_length`: one double step takes the `32` windows of width `5` onto `20`
  windows, and the `64` of width `6` onto `38` (`img`). `img5_closed`, `img6_closed`: the double
  step takes these back into themselves, whatever column `b + 1` does.
* `no_word5`, `no_word6`: if column `0` alternates white, black on the `2 m` ticks
  `s, s + 1, …, s + 2 m - 1`, then column `1` at the ticks `s + 2, s + 4, …, s + 2 m` does not read
  a word of `forbidden5` (resp. `forbidden6`) of length `m`. These are the kit's lists
  `col1Forbidden`. `no_short6`: at width `6`, the kit's word `1010100001` can be shortened to
  `101010000`.
* `onset5`, `onset6`: so if column `0` alternates from `T` on, no word of the lists is read from
  any white time `t ≥ T + 2`. `col1_constraints5`, `col1_constraints6` are the kit's statements
  for the single seed with `T' = T + 2`.
* `free_bit5`, `free_bit6`: column `-1` at the white times is the complement of column `1` when
  the rule holds at column `0` and the next tick is black, so it never reads a complemented word;
  this needs the alternation on two more ticks. `free_bit_constraints5`, `free_bit_constraints6`
  are the kit's statements for the single seed with `T' = T + 2`.

The method is the kit's (`Rule30GateTrap`, `Rule30GateTrapWords`): the windows that can have read
the first `k` samples of a word form a layer, the double step for every value of column `b + 1`
takes each layer into the next, and the last layer is empty (`run`, `excludes`). Here the first
layer is the image of all windows, so it needs no entry time. The relation forgets the columns
beyond `b + 1`, so the onset `T + 2` is not claimed to be the earliest for actual configurations.
Nothing here excludes period 2.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30PeriodTwoOnset

open Rule30Jen

/-! ## Histories and windows -/

/-- `H` obeys rule 30 at column `j`, at every tick. -/
def ObeysAt (H : Nat → Int → Bool) (j : Int) : Prop :=
  ∀ s, H (s + 1) j = rule (H s (j - 1)) (H s j) (H s (j + 1))

/-- `H` obeys rule 30 at the columns `1..b`. -/
def Obeys (b : Nat) (H : Nat → Int → Bool) : Prop :=
  ∀ j : Int, 1 ≤ j → j ≤ b → ObeysAt H j

/-- Rule 30 from a single black cell obeys rule 30 at every column. -/
theorem cell_obeysAt (j : Int) : ObeysAt cell j := fun _ => rfl

theorem cell_obeys (b : Nat) : Obeys b cell := fun j _ _ => cell_obeysAt j

/-- The cells of the columns `a, a + 1, …, a + n - 1` at the tick `s`. -/
def seg (H : Nat → Int → Bool) (s : Nat) (a : Int) : Nat → List Bool
  | 0 => []
  | n + 1 => H s a :: seg H s (a + 1) n

theorem length_seg (H : Nat → Int → Bool) (s : Nat) : ∀ (a : Int) (n : Nat), (seg H s a n).length = n
  | _, 0 => rfl
  | a, n + 1 => by rw [seg, List.length_cons, length_seg H s (a + 1) n]

/-- One tick of rule 30 on a window, with the cell `l` on its left and the cell `r` on its right. -/
def step (l r : Bool) : List Bool → List Bool
  | [] => []
  | [x] => [rule l x r]
  | x :: y :: z => rule l x y :: step x r (y :: z)

/-- A window obeying the rule moves by `step`, with its two outer cells as inputs. -/
theorem seg_step (H : Nat → Int → Bool) (s : Nat) : ∀ (n : Nat) (a : Int),
    (∀ j : Int, a ≤ j → j < a + n → ObeysAt H j) →
    seg H (s + 1) a n = step (H s (a - 1)) (H s (a + n)) (seg H s a n) := by
  intro n
  induction n with
  | zero => intro a _; rfl
  | succ n ih =>
    intro a h
    cases n with
    | zero =>
      show [H (s + 1) a] = [rule (H s (a - 1)) (H s a) (H s (a + ((0 + 1 : Nat) : Int)))]
      rw [h a (Int.le_refl a) (by omega) s, show a + ((0 + 1 : Nat) : Int) = a + 1 by omega]
    | succ m =>
      have e := ih (a + 1) (fun j h1 h2 => h j (by omega) (by omega))
      rw [show a + 1 - 1 = a by omega,
        show a + 1 + ((m + 1 : Nat) : Int) = a + ((m + 1 + 1 : Nat) : Int) by omega] at e
      show H (s + 1) a :: seg H (s + 1) (a + 1) (m + 1) =
        rule (H s (a - 1)) (H s a) (H s (a + 1)) ::
          step (H s a) (H s (a + ((m + 1 + 1 : Nat) : Int))) (seg H s (a + 1) (m + 1))
      rw [e, h a (Int.le_refl a) (by omega) s]

/-- Two ticks from a white tick of column `0`: the left inputs are white, then black, and `r₁`, `r₂`
are the cells of column `b + 1`. -/
def dstep (r₁ r₂ : Bool) (x : List Bool) : List Bool := step true r₂ (step false r₁ x)

/-- **The double step.** If column `0` is white at `s` and black at `s + 1`, the window of the
columns `1..b` at `s + 2` is the double step of the window at `s`. -/
theorem win_dstep {b : Nat} {H : Nat → Int → Bool} (hH : Obeys b H) {s : Nat}
    (h0 : H s 0 = false) (h1 : H (s + 1) 0 = true) :
    seg H (s + 2) 1 b = dstep (H s (1 + b)) (H (s + 1) (1 + b)) (seg H s 1 b) := by
  have hO : ∀ j : Int, 1 ≤ j → j < 1 + b → ObeysAt H j := fun j hj1 hj2 => hH j hj1 (by omega)
  show seg H (s + 1 + 1) 1 b = _
  rw [seg_step H (s + 1) b 1 hO, seg_step H s b 1 hO, show (1 : Int) - 1 = 0 by decide, h0, h1]
  rfl

/-! ## Finite sets of windows -/

/-- The four windows one double step can reach. -/
def succs (x : List Bool) : List (List Bool) :=
  [dstep false false x, dstep false true x, dstep true false x, dstep true true x]

theorem dstep_mem_succs (r₁ r₂ : Bool) (x : List Bool) : dstep r₁ r₂ x ∈ succs x := by
  cases r₁ <;> cases r₂ <;> simp [succs]

/-- A list of windows without repeats. -/
def nub : List (List Bool) → List (List Bool)
  | [] => []
  | x :: l => if x ∈ l then nub l else x :: nub l

theorem mem_nub {y : List Bool} : ∀ {l : List (List Bool)}, y ∈ nub l ↔ y ∈ l
  | [] => Iff.rfl
  | x :: l => by
    by_cases hx : x ∈ l
    · rw [nub, ite_eq_left hx, mem_nub, List.mem_cons]
      exact ⟨Or.inr, fun h => h.elim (fun e => e ▸ hx) id⟩
    · rw [nub, ite_eq_right hx, List.mem_cons, List.mem_cons, mem_nub]

/-- The windows of width `b` that one double step reaches. -/
def img (b : Nat) : List (List Bool) := nub ((allLists b).flatMap succs)

theorem mem_img {b : Nat} {x : List Bool} (hx : x.length = b) (r₁ r₂ : Bool) :
    dstep r₁ r₂ x ∈ img b := by
  rw [img, mem_nub, List.mem_flatMap]
  exact ⟨x, hx ▸ mem_allLists x, dstep_mem_succs r₁ r₂ x⟩

/-- `S` is closed under the double step, for every value of column `b + 1`. -/
def closedB (S : List (List Bool)) : Bool := S.all fun x => (succs x).all fun y => decide (y ∈ S)

theorem img5_length : (img 5).length = 20 := by decide +kernel
theorem img6_length : (img 6).length = 38 := by decide +kernel

/-- The `20` windows of width `5` are closed under the double step. -/
theorem img5_closed : closedB (img 5) = true := by decide +kernel

/-- The `38` windows of width `6` are closed under the double step. -/
theorem img6_closed : closedB (img 6) = true := by decide +kernel

/-! ## Words -/

/-- The windows of `S` whose column-`1` cell is `c`. -/
def layer (c : Bool) (S : List (List Bool)) : List (List Bool) := S.filter fun x => x.headD false == c

/-- The windows that a window of `L` can reach while column `1` reads the samples of `w`, one per
double step. -/
def run : List (List Bool) → List Bool → List (List Bool)
  | L, [] => L
  | L, c :: w => run (nub (layer c (L.flatMap succs))) w

/-- No window of `S` begins a reading of `w`. -/
def excludes (S : List (List Bool)) : List Bool → Bool
  | [] => false
  | c :: w => (run (layer c S) w).isEmpty

theorem headD_seg (H : Nat → Int → Bool) (s : Nat) (a : Int) (n : Nat) :
    (seg H s a (n + 1)).headD false = H s a := rfl

theorem mem_run {b : Nat} (hb : 0 < b) {H : Nat → Int → Bool} (hH : Obeys b H) :
    ∀ (w : List Bool) (L : List (List Bool)) (s : Nat), seg H s 1 b ∈ L →
      (∀ i, i < 2 * w.length → H (s + i) 0 = (i % 2 == 1)) →
      (∀ i, i < w.length → H (s + 2 + 2 * i) 1 = w.getD i false) →
      seg H (s + 2 * w.length) 1 b ∈ run L w
  | [], L, s, hL, _, _ => hL
  | c :: w, L, s, hL, hc, hr => by
    have h0 : H s 0 = false := hc 0 (by simp)
    have h1 : H (s + 1) 0 = true := hc 1 (by simp; omega)
    have hm : seg H (s + 2) 1 b ∈ nub (layer c (L.flatMap succs)) := by
      rw [mem_nub, layer, List.mem_filter, List.mem_flatMap, win_dstep hH h0 h1]
      refine ⟨⟨_, hL, dstep_mem_succs _ _ _⟩, ?_⟩
      rw [← win_dstep hH h0 h1]
      obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
      rw [headD_seg]
      have := hr 0 (by simp)
      rw [show s + 2 + 2 * 0 = s + 2 by omega] at this
      rw [this]; simp
    have := mem_run hb hH w _ (s + 2) hm
      (fun i hi => by
        have := hc (i + 2) (by simp at hi ⊢; omega)
        rwa [show s + (i + 2) = s + 2 + i by omega, show (i + 2) % 2 = i % 2 by omega] at this)
      (fun i hi => by
        have := hr (i + 1) (by simp; omega)
        rwa [show s + 2 + 2 * (i + 1) = s + 2 + 2 + 2 * i by omega] at this)
    rwa [List.length_cons, show s + 2 * (w.length + 1) = s + 2 + 2 * w.length by omega]

/-- A word that `img b` excludes is not read by column `1` at the ticks `s + 2, s + 4, …` when
column `0` alternates on the ticks `s, …, s + 2 m - 1`. -/
theorem no_word {b : Nat} (hb : 0 < b) {H : Nat → Int → Bool} (hH : Obeys b H) {w : List Bool}
    (hw : excludes (img b) w = true) (s : Nat)
    (hc : ∀ i, i < 2 * w.length → H (s + i) 0 = (i % 2 == 1)) :
    ¬ ∀ i, i < w.length → H (s + 2 + 2 * i) 1 = w.getD i false := by
  intro hr
  match w, hw, hc, hr with
  | c :: w, hw, hc, hr =>
    have h0 : H s 0 = false := hc 0 (by simp)
    have h1 : H (s + 1) 0 = true := hc 1 (by simp; omega)
    have hm : seg H (s + 2) 1 b ∈ layer c (img b) := by
      rw [layer, List.mem_filter, win_dstep hH h0 h1]
      refine ⟨mem_img (length_seg H s 1 b) _ _, ?_⟩
      rw [← win_dstep hH h0 h1]
      obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
      rw [headD_seg]
      have := hr 0 (by simp)
      rw [show s + 2 + 2 * 0 = s + 2 by omega] at this
      rw [this]; simp
    have hrun := mem_run hb hH w _ (s + 2) hm
      (fun i hi => by
        have := hc (i + 2) (by simp at hi ⊢; omega)
        rwa [show s + (i + 2) = s + 2 + i by omega, show (i + 2) % 2 = i % 2 by omega] at this)
      (fun i hi => by
        have := hr (i + 1) (by simp; omega)
        rwa [show s + 2 + 2 * (i + 1) = s + 2 + 2 + 2 * i by omega] at this)
    rw [excludes, List.isEmpty_iff] at hw
    rw [hw] at hrun
    exact List.not_mem_nil hrun

/-! ## The words of widths 5 and 6 -/

/-- The column-`1` words of `Rule30PeriodTwoWidth5.col1Forbidden`: `11`, `00000`, `100101`,
`10010001`. -/
def forbidden5 : List (List Bool) := [[true, true], [false, false, false, false, false],
  [true, false, false, true, false, true], [true, false, false, true, false, false, false, true]]

/-- The column-`1` words of `Rule30PeriodTwoWidth6.col1Forbidden`: those of width `5` and
`101001`, `1010100001`, `1010001001`, `10010000101`, `1001000010001`. -/
def forbidden6 : List (List Bool) := [[true, true], [false, false, false, false, false],
  [true, false, false, true, false, true], [true, false, false, true, false, false, false, true],
  [true, false, true, false, false, true], [true, false, true, false, true, false, false, false, false, true],
  [true, false, true, false, false, false, true, false, false, true],
  [true, false, false, true, false, false, false, false, true, false, true],
  [true, false, false, true, false, false, false, false, true, false, false, false, true]]

/-- `101010000`, the width-`6` word `1010100001` without its last sample. -/
def short6 : List Bool := [true, false, true, false, true, false, false, false, false]

theorem excludes5 : forbidden5.all (excludes (img 5)) = true := by decide +kernel
theorem excludes6 : forbidden6.all (excludes (img 6)) = true := by decide +kernel
theorem excludes_short6 : excludes (img 6) short6 = true := by decide +kernel

/-- **Width 5.** If `H` obeys rule 30 at the columns `1..5` and column `0` alternates white, black
on the ticks `s, …, s + 2 m - 1`, then column `1` at the ticks `s + 2, …, s + 2 m` does not read a
word of `forbidden5` of length `m`. -/
theorem no_word5 {H : Nat → Int → Bool} (hH : Obeys 5 H) (s : Nat) {w : List Bool}
    (hw : w ∈ forbidden5) (hc : ∀ i, i < 2 * w.length → H (s + i) 0 = (i % 2 == 1)) :
    ¬ ∀ i, i < w.length → H (s + 2 + 2 * i) 1 = w.getD i false :=
  no_word (by decide) hH (List.all_eq_true.1 excludes5 w hw) s hc

/-- **Width 6.** The same with the columns `1..6` and `forbidden6`. -/
theorem no_word6 {H : Nat → Int → Bool} (hH : Obeys 6 H) (s : Nat) {w : List Bool}
    (hw : w ∈ forbidden6) (hc : ∀ i, i < 2 * w.length → H (s + i) 0 = (i % 2 == 1)) :
    ¬ ∀ i, i < w.length → H (s + 2 + 2 * i) 1 = w.getD i false :=
  no_word (by decide) hH (List.all_eq_true.1 excludes6 w hw) s hc

/-- **The shortened width-6 word.** Column `1` does not read `101010000` either. -/
theorem no_short6 {H : Nat → Int → Bool} (hH : Obeys 6 H) (s : Nat)
    (hc : ∀ i, i < 2 * short6.length → H (s + i) 0 = (i % 2 == 1)) :
    ¬ ∀ i, i < short6.length → H (s + 2 + 2 * i) 1 = short6.getD i false :=
  no_word (by decide) hH excludes_short6 s hc

/-! ## From an alternation that starts at `T` -/

theorem clock_shift {H : Nat → Int → Bool} {T t : Nat} (hT : ∀ u, T ≤ u → H u 0 = ((u - T) % 2 == 1))
    (ht : T + 2 ≤ t) (hp : (t - T) % 2 = 0) (n : Nat) :
    ∀ i, i < n → H (t - 2 + i) 0 = (i % 2 == 1) := fun i _ => by
  rw [hT _ (by omega), show (t - 2 + i - T) % 2 = i % 2 by omega]

/-- **Width 5 from `T + 2`.** If `H` obeys rule 30 at the columns `1..5` and column `0` is white,
black, white, … from `T`, then from every white time `t ≥ T + 2`, column `1` read at consecutive
white times never spells a word of `forbidden5`. -/
theorem onset5 {H : Nat → Int → Bool} (hH : Obeys 5 H) (T : Nat)
    (hT : ∀ t, T ≤ t → H t 0 = ((t - T) % 2 == 1)) :
    ∀ t, T + 2 ≤ t → (t - T) % 2 = 0 → ∀ pat ∈ forbidden5,
      ¬ ∀ i, i < pat.length → H (t + 2 * i) 1 = pat.getD i false := by
  intro t ht hp pat hpat hr
  refine no_word5 hH (t - 2) hpat (clock_shift hT ht hp _) fun i hi => ?_
  rw [show t - 2 + 2 + 2 * i = t + 2 * i by omega]
  exact hr i hi

/-- **Width 6 from `T + 2`.** The same with the columns `1..6` and `forbidden6`. -/
theorem onset6 {H : Nat → Int → Bool} (hH : Obeys 6 H) (T : Nat)
    (hT : ∀ t, T ≤ t → H t 0 = ((t - T) % 2 == 1)) :
    ∀ t, T + 2 ≤ t → (t - T) % 2 = 0 → ∀ pat ∈ forbidden6,
      ¬ ∀ i, i < pat.length → H (t + 2 * i) 1 = pat.getD i false := by
  intro t ht hp pat hpat hr
  refine no_word6 hH (t - 2) hpat (clock_shift hT ht hp _) fun i hi => ?_
  rw [show t - 2 + 2 + 2 * i = t + 2 * i by omega]
  exact hr i hi

/-- **The kit's width-5 constraints with `T' = T + 2`** (`Rule30PeriodTwoWidth5.col1_constraints`
has `∃ T'`). -/
theorem col1_constraints5 (T : Nat) (h : ∀ t, T ≤ t → cell t 0 = ((t - T) % 2 == 1)) :
    ∀ t, T + 2 ≤ t → (t - T) % 2 = 0 → ∀ pat ∈ forbidden5,
      ¬ ∀ i, i < pat.length → cell (t + 2 * i) 1 = pat.getD i false :=
  onset5 (cell_obeys 5) T h

/-- **The kit's width-6 constraints with `T' = T + 2`** (`Rule30PeriodTwoWidth6.col1_constraints`
has `∃ T'`). -/
theorem col1_constraints6 (T : Nat) (h : ∀ t, T ≤ t → cell t 0 = ((t - T) % 2 == 1)) :
    ∀ t, T + 2 ≤ t → (t - T) % 2 = 0 → ∀ pat ∈ forbidden6,
      ¬ ∀ i, i < pat.length → cell (t + 2 * i) 1 = pat.getD i false :=
  onset6 (cell_obeys 6) T h

/-! ## The free bits -/

/-- At a white tick of column `0` followed by a black one, column `-1` is the complement of
column `1`, when the rule holds at column `0`. -/
theorem left_right {H : Nat → Int → Bool} (h0 : ObeysAt H 0) {u : Nat} (hu : H u 0 = false)
    (hu1 : H (u + 1) 0 = true) : H u (-1) = !H u 1 := by
  have e := h0 u
  rw [hu1, hu, show (0 : Int) - 1 = -1 by decide, show (0 : Int) + 1 = 1 by decide] at e
  revert e
  cases H u (-1) <;> cases H u 1 <;> decide

theorem free_of_col1 {H : Nat → Int → Bool} (h0 : ObeysAt H 0) (s : Nat) {w : List Bool}
    (hc : ∀ i, i < 2 * w.length + 2 → H (s + i) 0 = (i % 2 == 1))
    (hr : ∀ i, i < w.length → H (s + 2 + 2 * i) (-1) = !w.getD i false) :
    ∀ i, i < w.length → H (s + 2 + 2 * i) 1 = w.getD i false := by
  intro i hi
  have hu : H (s + 2 + 2 * i) 0 = false := by
    have := hc (2 + 2 * i) (by omega)
    rwa [show s + (2 + 2 * i) = s + 2 + 2 * i by omega, show (2 + 2 * i) % 2 = 0 by omega] at this
  have hu1 : H (s + 2 + 2 * i + 1) 0 = true := by
    have := hc (3 + 2 * i) (by omega)
    rwa [show s + (3 + 2 * i) = s + 2 + 2 * i + 1 by omega, show (3 + 2 * i) % 2 = 1 by omega] at this
  have e := left_right h0 hu hu1
  rw [hr i hi] at e
  revert e
  cases H (s + 2 + 2 * i) 1 <;> cases w.getD i false <;> decide

/-- **Free bits, width 5.** If moreover the rule holds at column `0` and the alternation lasts two
more ticks, column `-1` at the ticks `s + 2, …, s + 2 m` does not read the complement of a word of
`forbidden5`. -/
theorem free_bit5 {H : Nat → Int → Bool} (hH : Obeys 5 H) (h0 : ObeysAt H 0) (s : Nat)
    {w : List Bool} (hw : w ∈ forbidden5)
    (hc : ∀ i, i < 2 * w.length + 2 → H (s + i) 0 = (i % 2 == 1)) :
    ¬ ∀ i, i < w.length → H (s + 2 + 2 * i) (-1) = !w.getD i false := fun hr =>
  no_word5 hH s hw (fun i hi => hc i (by omega)) (free_of_col1 h0 s hc hr)

/-- **Free bits, width 6.** The same with the columns `1..6` and `forbidden6`. -/
theorem free_bit6 {H : Nat → Int → Bool} (hH : Obeys 6 H) (h0 : ObeysAt H 0) (s : Nat)
    {w : List Bool} (hw : w ∈ forbidden6)
    (hc : ∀ i, i < 2 * w.length + 2 → H (s + i) 0 = (i % 2 == 1)) :
    ¬ ∀ i, i < w.length → H (s + 2 + 2 * i) (-1) = !w.getD i false := fun hr =>
  no_word6 hH s hw (fun i hi => hc i (by omega)) (free_of_col1 h0 s hc hr)

/-- **The kit's width-5 free-bit constraints with `T' = T + 2`**
(`Rule30PeriodTwoWidth5.free_bit_constraints`). -/
theorem free_bit_constraints5 (T : Nat) (h : ∀ t, T ≤ t → cell t 0 = ((t - T) % 2 == 1)) :
    ∀ t, T + 2 ≤ t → (t - T) % 2 = 0 → ∀ pat ∈ forbidden5,
      ¬ ∀ i, i < pat.length → cell (t + 2 * i) (-1) = !pat.getD i false := by
  intro t ht hp pat hpat hr
  refine free_bit5 (cell_obeys 5) (cell_obeysAt 0) (t - 2) hpat (clock_shift h ht hp _) fun i hi => ?_
  rw [show t - 2 + 2 + 2 * i = t + 2 * i by omega]
  exact hr i hi

/-- **The kit's width-6 free-bit constraints with `T' = T + 2`**
(`Rule30PeriodTwoWidth6.free_bit_constraints`). -/
theorem free_bit_constraints6 (T : Nat) (h : ∀ t, T ≤ t → cell t 0 = ((t - T) % 2 == 1)) :
    ∀ t, T + 2 ≤ t → (t - T) % 2 = 0 → ∀ pat ∈ forbidden6,
      ¬ ∀ i, i < pat.length → cell (t + 2 * i) (-1) = !pat.getD i false := by
  intro t ht hp pat hpat hr
  refine free_bit6 (cell_obeys 6) (cell_obeysAt 0) (t - 2) hpat (clock_shift h ht hp _) fun i hi => ?_
  rw [show t - 2 + 2 + 2 * i = t + 2 * i by omega]
  exact hr i hi

/-! ## Space-time translation invariance and arbitrary-column period-2 onset constraints -/

/-- Space-time translated history `(s, j) ↦ H (d + s) (a + j)`. -/
def shiftH (H : Nat → Int → Bool) (d : Nat) (a : Int) : Nat → Int → Bool :=
  fun s j => H (d + s) (a + j)

/-- **Space-Time Shift Equivalence for `ObeysAt` (`obeysAt_shiftH`):**
`shiftH H d a` obeys Rule 30 at column `j` for all ticks iff `H` obeys Rule 30 at column `a + j`
for all ticks `s ≥ d`. -/
theorem obeysAt_shiftH_of_obeysAt {H : Nat → Int → Bool} (d : Nat) (a j : Int)
    (h : ObeysAt H (a + j)) : ObeysAt (shiftH H d a) j := by
  intro s
  unfold shiftH
  have hs := h (d + s)
  rw [show d + (s + 1) = (d + s) + 1 by omega,
    show a + (j - 1) = a + j - 1 by omega,
    show a + (j + 1) = a + j + 1 by omega]
  exact hs

/-- **Spatial Shift Transfer for `Obeys` (`obeys_shiftH_of_interval`):**
if `H` obeys Rule 30 at every column `k` in `[a + 1, a + b]`, then `shiftH H d a` satisfies
`Obeys b (shiftH H d a)`. -/
theorem obeys_shiftH_of_interval {H : Nat → Int → Bool} (d b : Nat) (a : Int)
    (h : ∀ k : Int, a + 1 ≤ k → k ≤ a + (b : Int) → ObeysAt H k) :
    Obeys b (shiftH H d a) := by
  intro j hj1 hjb
  exact obeysAt_shiftH_of_obeysAt d a j (h (a + j) (by omega) (by omega))

/-- **Unconditional `Obeys` for Space-Time Shifted Single-Seed Evolution (`cell_obeys_shiftH`).** -/
theorem cell_obeys_shiftH (d b : Nat) (a : Int) : Obeys b (shiftH cell d a) :=
  obeys_shiftH_of_interval d b a (fun k _ _ => cell_obeysAt k)

/-- **Arbitrary-Column Width-`5` Forbidden-Word Exclusion (`no_word5_at_col`):**
if `H` obeys Rule 30 on columns `[a + 1, a + 5]` and column `a` alternates on `[s, s + 2 * w.length)`,
then column `a + 1` at `s + 2 + 2 * i` never spells `w ∈ forbidden5`. -/
theorem no_word5_at_col {H : Nat → Int → Bool} (a : Int)
    (hH : ∀ k : Int, a + 1 ≤ k → k ≤ a + 5 → ObeysAt H k) (s : Nat)
    {w : List Bool} (hw : w ∈ forbidden5)
    (hc : ∀ i, i < 2 * w.length → H (s + i) a = (i % 2 == 1)) :
    ¬ ∀ i, i < w.length → H (s + 2 + 2 * i) (a + 1) = w.getD i false := by
  have hshift := no_word5 (obeys_shiftH_of_interval 0 5 a hH) s hw
    (fun i hi => by simpa [shiftH] using hc i hi)
  intro hr
  exact hshift (fun i hi => by simpa [shiftH] using hr i hi)

/-- **Arbitrary-Column Width-`6` Forbidden-Word Exclusion (`no_word6_at_col`):**
if `H` obeys Rule 30 on columns `[a + 1, a + 6]` and column `a` alternates on `[s, s + 2 * w.length)`,
then column `a + 1` at `s + 2 + 2 * i` never spells `w ∈ forbidden6`. -/
theorem no_word6_at_col {H : Nat → Int → Bool} (a : Int)
    (hH : ∀ k : Int, a + 1 ≤ k → k ≤ a + 6 → ObeysAt H k) (s : Nat)
    {w : List Bool} (hw : w ∈ forbidden6)
    (hc : ∀ i, i < 2 * w.length → H (s + i) a = (i % 2 == 1)) :
    ¬ ∀ i, i < w.length → H (s + 2 + 2 * i) (a + 1) = w.getD i false := by
  have hshift := no_word6 (obeys_shiftH_of_interval 0 6 a hH) s hw
    (fun i hi => by simpa [shiftH] using hc i hi)
  intro hr
  exact hshift (fun i hi => by simpa [shiftH] using hr i hi)

/-- **Arbitrary-Column Width-`5` Left-Neighbor (`a - 1`) Exclusion (`free_bit5_at_col`):**
if `H` obeys Rule 30 on `[a, a + 5]` and column `a` alternates on `[s, s + 2 * w.length + 2)`,
then column `a - 1` at `s + 2 + 2 * i` never spells the bitwise complement of `w ∈ forbidden5`. -/
theorem free_bit5_at_col {H : Nat → Int → Bool} (a : Int)
    (hH : ∀ k : Int, a + 1 ≤ k → k ≤ a + 5 → ObeysAt H k)
    (ha : ObeysAt H a) (s : Nat)
    {w : List Bool} (hw : w ∈ forbidden5)
    (hc : ∀ i, i < 2 * w.length + 2 → H (s + i) a = (i % 2 == 1)) :
    ¬ ∀ i, i < w.length → H (s + 2 + 2 * i) (a - 1) = !w.getD i false := by
  have ha0 : ObeysAt (shiftH H 0 a) 0 := by
    simpa [Int.add_zero] using obeysAt_shiftH_of_obeysAt 0 a 0 (by simpa [Int.add_zero] using ha)
  have hshift := free_bit5 (obeys_shiftH_of_interval 0 5 a hH) ha0 s hw
    (fun i hi => by simpa [shiftH] using hc i hi)
  intro hr
  exact hshift (fun i hi => by
    simpa [shiftH, show a + (-1 : Int) = a - 1 by omega] using hr i hi)

/-- **Arbitrary-Column Width-`6` Left-Neighbor (`a - 1`) Exclusion (`free_bit6_at_col`):**
if `H` obeys Rule 30 on `[a, a + 6]` and column `a` alternates on `[s, s + 2 * w.length + 2)`,
then column `a - 1` at `s + 2 + 2 * i` never spells the bitwise complement of `w ∈ forbidden6`. -/
theorem free_bit6_at_col {H : Nat → Int → Bool} (a : Int)
    (hH : ∀ k : Int, a + 1 ≤ k → k ≤ a + 6 → ObeysAt H k)
    (ha : ObeysAt H a) (s : Nat)
    {w : List Bool} (hw : w ∈ forbidden6)
    (hc : ∀ i, i < 2 * w.length + 2 → H (s + i) a = (i % 2 == 1)) :
    ¬ ∀ i, i < w.length → H (s + 2 + 2 * i) (a - 1) = !w.getD i false := by
  have ha0 : ObeysAt (shiftH H 0 a) 0 := by
    simpa [Int.add_zero] using obeysAt_shiftH_of_obeysAt 0 a 0 (by simpa [Int.add_zero] using ha)
  have hshift := free_bit6 (obeys_shiftH_of_interval 0 6 a hH) ha0 s hw
    (fun i hi => by simpa [shiftH] using hc i hi)
  intro hr
  exact hshift (fun i hi => by
    simpa [shiftH, show a + (-1 : Int) = a - 1 by omega] using hr i hi)

/-- **Single-Seed Arbitrary-Column Right-Neighbor Onset-`T + 2` Constraints (`cell_col_succ_constraints6`):**
if column `a` of `cell` alternates `cell t a = ((t - T) % 2 == 1)` from `T` on, then from every
white tick `t ≥ T + 2` (`(t - T) % 2 = 0`), column `a + 1` avoids every pattern in `forbidden6`. -/
theorem cell_col_succ_constraints6 (a : Int) (T : Nat)
    (h : ∀ t, T ≤ t → cell t a = ((t - T) % 2 == 1)) :
    ∀ t, T + 2 ≤ t → (t - T) % 2 = 0 → ∀ pat ∈ forbidden6,
      ¬ ∀ i, i < pat.length → cell (t + 2 * i) (a + 1) = pat.getD i false := by
  have hon := onset6 (cell_obeys_shiftH 0 6 a) T (fun t ht => by simpa [shiftH] using h t ht)
  intro t ht hp pat hpat hr
  exact hon t ht hp pat hpat (fun i hi => by simpa [shiftH] using hr i hi)

/-- **Single-Seed Arbitrary-Column Left-Neighbor Onset-`T + 2` Constraints (`cell_col_pred_constraints6`):**
if column `a` of `cell` alternates `cell t a = ((t - T) % 2 == 1)` from `T` on, then from every
white tick `t ≥ T + 2` (`(t - T) % 2 = 0`), column `a - 1` avoids the bitwise complement of every
pattern in `forbidden6`. -/
theorem cell_col_pred_constraints6 (a : Int) (T : Nat)
    (h : ∀ t, T ≤ t → cell t a = ((t - T) % 2 == 1)) :
    ∀ t, T + 2 ≤ t → (t - T) % 2 = 0 → ∀ pat ∈ forbidden6,
      ¬ ∀ i, i < pat.length → cell (t + 2 * i) (a - 1) = !pat.getD i false := by
  intro t ht hp pat hpat hr
  have hcs := clock_shift (H := shiftH cell 0 a) (fun u hu => by simpa [shiftH] using h u hu) ht hp (2 * pat.length + 2)
  refine free_bit6_at_col a (fun k _ _ => cell_obeysAt k) (cell_obeysAt a) (t - 2) hpat
    (fun i hi => by simpa [shiftH] using hcs i hi)
    (fun i hi => ?_)
  rw [show t - 2 + 2 + 2 * i = t + 2 * i by omega]
  exact hr i hi

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

/-! ## Universal width-6 closed-system entropy (`15/11`) and left-word diversity bridge -/

def dec6 (c : Nat) : List Bool := (List.range 6).map (fun i => c.testBit i)
def enc6 : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * enc6 bs

def img6TwoCodesPack : Nat := 0x3e3c3a3837343231302e2d2a2827242221201e1c1a1918171412100e0d0a080704020100
def img6TwoIdxPack : Nat := 0x240023002200212000001f001e1d1c001b1a000019001817000016001514130012001100100f0e0d00000c000b000a00090800000700060500000400030201
def img6TwoSuccPack : Nat := 0x1503150318061806200d200d1f0c1f0c0f210f210a1d0a1d0012001205170517071907191e1e1e1e222222221717171716161616080808080202020209090909101010100e0e0e0e15031e1e18062121200d17171b0912121f0c16160f210f0f0a1d0a0a0012000007190707101010220b0b0b1e05050517040404161a1a231114141d0a202017051e1e15031c1c1301
def onset6DfaStepPack : Nat := 0x90a1c001b0006001a1300081918000017001600150e1413090a1200110010000f0e0d000c0300000b0a06030908070306000503040302
def onset6DfaMasksPack : Nat := 0x10084222102a15014440540a1200803219426650a04028100001048401206637144dc00804010100000840021084ca70328010080202000230044c00110cc623302814010400448040a000221940465050081200004632144c8020000810000924850920c4c060b0003a1d436650192cc72b30763f164dc03b3dc76f70e4ca78b2807f3fd76ff0fffffffff
def onset6DfaWtPack : Nat := 0x39003200250063001c004b008a001500370066001000580084001400410061000f0077000b004d0058006b0086008f00b0006900cf00e5

def img6CodeAt (i : Nat) : Nat := (img6TwoCodesPack >>> (8 * i)) % 256
def img6IdxOf (c : Nat) : Nat := (img6TwoIdxPack >>> (8 * c)) % 256
def img6SuccAt (i : Nat) (x1 x2 : Bool) : Nat :=
  let idx := 4 * i + (if x1 then 2 else 0) + (if x2 then 1 else 0)
  (img6TwoSuccPack >>> (8 * idx)) % 256

def onset6DfaStep (q : Nat) (b : Bool) : Option Nat :=
  let v := (onset6DfaStepPack >>> (16 * q + (if b then 8 else 0))) % 256
  if v = 0 then none else some (v - 1)

def onset6DfaHas (q i : Nat) : Bool := onset6DfaMasksPack.testBit (40 * q + i)
def onset6DfaWtAt (q : Nat) : Nat := (onset6DfaWtPack >>> (16 * q)) % 65536

def onset6DfaRun : Nat → List Bool → Option Nat
  | q, [] => some q
  | q, b :: bs => match onset6DfaStep q b with
    | some q' => onset6DfaRun q' bs
    | none => none

def onset6DfaAccepts (q : Nat) (w : List Bool) : Bool := (onset6DfaRun q w).isSome

def onset6DfaWords (q : Nat) : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 =>
    let l0 := match onset6DfaStep q false with
      | some q' => (onset6DfaWords q' n).map (false :: ·)
      | none => []
    let l1 := match onset6DfaStep q true with
      | some q' => (onset6DfaWords q' n).map (true :: ·)
      | none => []
    l0 ++ l1

private theorem img6Two_entry_ok :
    (List.range 64).all (fun c =>
      let w0 := dec6 c
      ([false, true].all (fun a1 => [false, true].all (fun a2 =>
        let w1 := dstep a1 a2 w0
        ([false, true].all (fun b1 => [false, true].all (fun b2 =>
          let c2 := enc6 (dstep b1 b2 w1)
          let u := img6IdxOf c2
          1 ≤ u && u ≤ 36 && (img6CodeAt (u - 1) == c2)))))))) = true := by decide +kernel

private theorem img6Two_succ_ok :
    (List.range 36).all (fun i =>
      let w := dec6 (img6CodeAt i)
      let j00 := img6SuccAt i false false
      let j01 := img6SuccAt i false true
      let j10 := img6SuccAt i true false
      let j11 := img6SuccAt i true true
      j00 < 36 && j01 < 36 && j10 < 36 && j11 < 36 &&
      (enc6 (dstep false false w) == img6CodeAt j00) &&
      (enc6 (dstep false true w) == img6CodeAt j01) &&
      (enc6 (dstep true false w) == img6CodeAt j10) &&
      (enc6 (dstep true true w) == img6CodeAt j11)) = true := by decide +kernel

private theorem onset6Dfa_sound_ok :
    (List.range 28).all (fun q =>
      (List.range 36).all (fun i =>
        if onset6DfaHas q i then
          let b := img6CodeAt i % 2 == 1
          match onset6DfaStep q b with
          | some q' =>
            q' < 28 &&
            onset6DfaHas q' (img6SuccAt i false false) &&
            onset6DfaHas q' (img6SuccAt i false true) &&
            onset6DfaHas q' (img6SuccAt i true false) &&
            onset6DfaHas q' (img6SuccAt i true true)
          | none => false
        else true)) = true := by decide +kernel

private theorem onset6Dfa_init_all : (List.range 36).all (fun i => onset6DfaHas 0 i) = true := by decide +kernel

private theorem onset6Dfa_weights_ok :
    (List.range 28).all (fun q =>
      let wq := onset6DfaWtAt q
      let s0 := match onset6DfaStep q false with | some q' => onset6DfaWtAt q' | none => 0
      let s1 := match onset6DfaStep q true with | some q' => onset6DfaWtAt q' | none => 0
      (match onset6DfaStep q false with | none => true | some q' => q' < 28) &&
      (match onset6DfaStep q true with | none => true | some q' => q' < 28) &&
      1 ≤ wq && 11 * (s0 + s1) ≤ 15 * wq) = true := by decide +kernel

private theorem dec6_enc6 (w : List Bool) (hw : w.length = 6) : dec6 (enc6 w) = w := by
  rcases w with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | _⟩⟩⟩⟩⟩⟩ <;> simp at hw
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> decide

private theorem enc6_lt_64 (w : List Bool) (hw : w.length = 6) : enc6 w < 64 := by
  rcases w with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | _⟩⟩⟩⟩⟩⟩ <;> simp at hw
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> decide

private theorem dstep_len6 (w : List Bool) (hw : w.length = 6) (x1 x2 : Bool) : (dstep x1 x2 w).length = 6 := by
  rcases w with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | _⟩⟩⟩⟩⟩⟩ <;> simp at hw
  rfl

theorem onset6_two_step_closed {H : Nat → Int → Bool} (hH : Obeys 6 H) (s : Nat)
    (h0 : H s 0 = false) (h1 : H (s + 1) 0 = true)
    (h2 : H (s + 2) 0 = false) (h3 : H (s + 3) 0 = true) :
    ∃ i, i < 36 ∧ seg H (s + 4) 1 6 = dec6 (img6CodeAt i) := by
  have hw1 : seg H (s + 2) 1 6 = dstep (H s 7) (H (s + 1) 7) (seg H s 1 6) := win_dstep hH h0 h1
  have hw2 : seg H (s + 4) 1 6 = dstep (H (s + 2) 7) (H (s + 3) 7) (seg H (s + 2) 1 6) := by
    simpa [Nat.add_assoc] using win_dstep hH h2 h3
  have hlen0 : (seg H s 1 6).length = 6 := length_seg H s 1 6
  have hlt : enc6 (seg H s 1 6) < 64 := enc6_lt_64 _ hlen0
  have hall := List.all_eq_true.mp img6Two_entry_ok (enc6 (seg H s 1 6)) (List.mem_range.mpr hlt)
  have hm (b : Bool) : b ∈ [false, true] := by cases b <;> simp
  have hcont := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hall _ (hm (H s 7))) _ (hm (H (s + 1) 7))) _ (hm (H (s + 2) 7))) _ (hm (H (s + 3) 7))
  dsimp only at hcont; simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcont
  rw [dec6_enc6 _ hlen0, ← hw1, ← hw2] at hcont
  exact ⟨img6IdxOf (enc6 (seg H (s + 4) 1 6)) - 1, by omega, by rw [hcont.2, dec6_enc6 _ (length_seg H (s + 4) 1 6)]⟩

theorem onset6Dfa_sound_of_obeys6 {H : Nat → Int → Bool} (hH : Obeys 6 H) (s m : Nat)
    (hc : ∀ i, i < 2 * m + 4 → H (s + i) 0 = (i % 2 == 1)) :
    onset6DfaAccepts 0 ((List.range m).map (fun k => H (s + 4 + 2 * k) 1)) = true := by
  obtain ⟨i0, hi0, hseg0⟩ := onset6_two_step_closed hH s (hc 0 (by omega)) (hc 1 (by omega)) (hc 2 (by omega)) (hc 3 (by omega))
  have hrec : ∀ k t q i, q < 28 → i < 36 → onset6DfaHas q i = true →
      seg H t 1 6 = dec6 (img6CodeAt i) →
      (∀ j, j < 2 * k → H (t + j) 0 = (j % 2 == 1)) →
      onset6DfaAccepts q ((List.range k).map (fun j => H (t + 2 * j) 1)) = true := by
    intro k; induction k with
    | zero => intro t q i _ _ _ _ _; rfl
    | succ k ih =>
      intro t q i hq hi hm hseg hct
      have hsnd := List.all_eq_true.mp (List.all_eq_true.mp onset6Dfa_sound_ok q (List.mem_range.mpr hq)) i (List.mem_range.mpr hi)
      dsimp only at hsnd; simp only [hm, ↓reduceIte] at hsnd
      have hbit : H t 1 = (img6CodeAt i % 2 == 1) := by
        have hh := congrArg (fun l => l.headD false) hseg
        have hd0 : (dec6 (img6CodeAt i)).headD false = (img6CodeAt i % 2 == 1) := by
          show (img6CodeAt i).testBit 0 = _; rw [Nat.testBit_zero]; cases h : (img6CodeAt i % 2 == 1) <;> simp_all
        rw [hd0] at hh; exact hh
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [onset6DfaAccepts, onset6DfaRun, Nat.mul_zero, Nat.add_zero, hbit]
      cases hst : onset6DfaStep q (img6CodeAt i % 2 == 1) with
      | none => rw [hst] at hsnd; exact Bool.noConfusion hsnd
      | some q' =>
        rw [hst] at hsnd; simp only [Bool.and_eq_true, decide_eq_true_eq] at hsnd
        have hw_next : seg H (t + 2) 1 6 = dstep (H t 7) (H (t + 1) 7) (dec6 (img6CodeAt i)) := by
          rw [← hseg]; exact win_dstep hH (hct 0 (by omega)) (hct 1 (by omega))
        have hsu := List.all_eq_true.mp img6Two_succ_ok i (List.mem_range.mpr hi)
        dsimp only at hsu; simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hsu
        have hlen_d : (dstep (H t 7) (H (t + 1) 7) (dec6 (img6CodeAt i))).length = 6 := dstep_len6 _ (by simp [dec6]) _ _
        have hstep_to : ∃ i', i' < 36 ∧ onset6DfaHas q' i' = true ∧ seg H (t + 2) 1 6 = dec6 (img6CodeAt i') := by
          cases hx1 : H t 7 <;> cases hx2 : H (t + 1) 7 <;> rw [hx1, hx2] at hw_next hlen_d
          · exact ⟨_, hsu.1.1.1.1.1.1.1, hsnd.1.1.1.2, hw_next.trans ((dec6_enc6 _ hlen_d).symm.trans (congrArg dec6 hsu.1.1.1.2))⟩
          · exact ⟨_, hsu.1.1.1.1.1.1.2, hsnd.1.1.2, hw_next.trans ((dec6_enc6 _ hlen_d).symm.trans (congrArg dec6 hsu.1.1.2))⟩
          · exact ⟨_, hsu.1.1.1.1.1.2, hsnd.1.2, hw_next.trans ((dec6_enc6 _ hlen_d).symm.trans (congrArg dec6 hsu.1.2))⟩
          · exact ⟨_, hsu.1.1.1.1.2, hsnd.2, hw_next.trans ((dec6_enc6 _ hlen_d).symm.trans (congrArg dec6 hsu.2))⟩
        obtain ⟨i', hi', hm', hseg'⟩ := hstep_to
        have hmap : (List.map ((fun j => H (t + 2 * j) 1) ∘ Nat.succ) (List.range k)) =
            (List.range k).map (fun j => H (t + 2 + 2 * j) 1) := by
          apply List.map_congr_left; intro j _; simp only [Function.comp_apply]; congr 1; omega
        rw [hmap]
        exact ih (t + 2) q' i' hsnd.1.1.1.1 hi' hm' hseg' (fun j hj => by
          have h := hct (j + 2) (by omega); rw [show t + (j + 2) = t + 2 + j by omega] at h
          simpa [show (j + 2) % 2 = j % 2 by omega] using h)
  exact hrec m (s + 4) 0 i0 (by decide) hi0 (List.all_eq_true.mp onset6Dfa_init_all i0 (List.mem_range.mpr hi0)) hseg0 (fun j hj => by
    have h := hc (j + 4) (by omega); rw [show s + (j + 4) = s + 4 + j by omega] at h
    simpa [show (j + 4) % 2 = j % 2 by omega] using h)

private theorem mem_onset6DfaWords_iff (n : Nat) :
    ∀ q w, w ∈ onset6DfaWords q n ↔ w.length = n ∧ onset6DfaAccepts q w = true := by
  induction n with
  | zero => intro q w; cases w <;> simp [onset6DfaWords, onset6DfaAccepts, onset6DfaRun]
  | succ n ih =>
    intro q w; constructor
    · intro hw; simp only [onset6DfaWords, List.mem_append] at hw
      rcases hw with h0 | h1
      · cases hst : onset6DfaStep q false with
        | none => rw [hst] at h0; simp at h0
        | some q' => rw [hst] at h0; obtain ⟨u, hu, rfl⟩ := List.mem_map.mp h0; obtain ⟨hl, ha⟩ := (ih q' u).mp hu; exact ⟨by simp [hl], by simp [onset6DfaAccepts, onset6DfaRun, hst]; exact ha⟩
      · cases hst : onset6DfaStep q true with
        | none => rw [hst] at h1; simp at h1
        | some q' => rw [hst] at h1; obtain ⟨u, hu, rfl⟩ := List.mem_map.mp h1; obtain ⟨hl, ha⟩ := (ih q' u).mp hu; exact ⟨by simp [hl], by simp [onset6DfaAccepts, onset6DfaRun, hst]; exact ha⟩
    · rintro ⟨hlen, hacc⟩; cases w with
      | nil => simp at hlen
      | cons b bs =>
        simp only [onset6DfaAccepts, onset6DfaRun] at hacc
        cases hst : onset6DfaStep q b with
        | none => rw [hst] at hacc; simp at hacc
        | some q' =>
          rw [hst] at hacc; have hm := (ih q' bs).mpr ⟨by simpa using hlen, hacc⟩
          simp only [onset6DfaWords, List.mem_append]; cases b
          · left; rw [hst]; exact List.mem_map_of_mem hm
          · right; rw [hst]; exact List.mem_map_of_mem hm

theorem onset6Dfa_wordCount_le_15_11 (m : Nat) :
    (onset6DfaWords 0 m).length * 11 ^ m ≤ 229 * 15 ^ m := by
  have hgen : ∀ n q, q < 28 → (onset6DfaWords q n).length * 11 ^ n ≤ onset6DfaWtAt q * 15 ^ n := by
    intro n; induction n with
    | zero =>
      intro q hq; have hw := List.all_eq_true.mp onset6Dfa_weights_ok q (List.mem_range.mpr hq)
      dsimp only at hw; simp only [Bool.and_eq_true, decide_eq_true_eq] at hw; simp [onset6DfaWords]; exact hw.1.2
    | succ n ih =>
      intro q hq; have hw := List.all_eq_true.mp onset6Dfa_weights_ok q (List.mem_range.mpr hq)
      dsimp only at hw; simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
      have h0 : (match onset6DfaStep q false with | some q' => (onset6DfaWords q' n).length | none => 0) * 11 ^ n ≤
          (match onset6DfaStep q false with | some q' => onset6DfaWtAt q' | none => 0) * 15 ^ n := by
        cases hst : onset6DfaStep q false with | none => simp | some q' => rw [hst] at hw; exact ih q' (by simpa using hw.1.1.1)
      have h1 : (match onset6DfaStep q true with | some q' => (onset6DfaWords q' n).length | none => 0) * 11 ^ n ≤
          (match onset6DfaStep q true with | some q' => onset6DfaWtAt q' | none => 0) * 15 ^ n := by
        cases hst : onset6DfaStep q true with | none => simp | some q' => rw [hst] at hw; exact ih q' (by simpa using hw.1.1.2)
      have hlen : (onset6DfaWords q (n + 1)).length =
          (match onset6DfaStep q false with | some q' => (onset6DfaWords q' n).length | none => 0) +
          (match onset6DfaStep q true with | some q' => (onset6DfaWords q' n).length | none => 0) := by
        simp only [onset6DfaWords, List.length_append]; congr 1 <;> cases onset6DfaStep q _ <;> simp
      rw [hlen, Nat.pow_succ, Nat.pow_succ]
      calc ((match onset6DfaStep q false with | some q' => (onset6DfaWords q' n).length | none => 0) +
            (match onset6DfaStep q true with | some q' => (onset6DfaWords q' n).length | none => 0)) * (11 ^ n * 11)
          = ((match onset6DfaStep q false with | some q' => (onset6DfaWords q' n).length | none => 0) * 11 ^ n +
             (match onset6DfaStep q true with | some q' => (onset6DfaWords q' n).length | none => 0) * 11 ^ n) * 11 := by
            rw [← Nat.mul_assoc, Nat.add_mul]
        _ ≤ ((match onset6DfaStep q false with | some q' => onset6DfaWtAt q' | none => 0) * 15 ^ n +
             (match onset6DfaStep q true with | some q' => onset6DfaWtAt q' | none => 0) * 15 ^ n) * 11 :=
            Nat.mul_le_mul_right 11 (Nat.add_le_add h0 h1)
        _ = (11 * ((match onset6DfaStep q false with | some q' => onset6DfaWtAt q' | none => 0) +
                   (match onset6DfaStep q true with | some q' => onset6DfaWtAt q' | none => 0))) * 15 ^ n := by
            rw [← Nat.add_mul, Nat.mul_right_comm, Nat.mul_comm _ 11]
        _ ≤ (15 * onset6DfaWtAt q) * 15 ^ n := Nat.mul_le_mul_right _ hw.2
        _ = onset6DfaWtAt q * (15 ^ n * 15) := by rw [Nat.mul_comm 15 _, Nat.mul_assoc, Nat.mul_comm 15 (15 ^ n)]
  have h0 : onset6DfaWtAt 0 = 229 := by decide +kernel
  rw [← h0]; exact hgen m 0 (by decide)

private theorem obeys_left_inv {H : Nat → Int → Bool} {j : Int} (hj : ObeysAt H j) (t : Nat) :
    H t (j - 1) = xor (H (t + 1) j) (H t j || H t (j + 1)) := by
  rw [hj t]; unfold rule; cases H t (j - 1) <;> cases (H t j || H t (j + 1)) <;> rfl

/-- **Leftward Spatial Reconstruction from Alternating Column `0` and White-Tick Column `1`
(`leftSeg_determined_by_white_col1`):** in any Rule 30 spacetime obeying columns `-2*m .. 0`, two
white-phase ages sharing `m` white-tick readings of column `1` share their entire `2*m`-cell spatial
word immediately west of column `0`. -/
theorem leftSeg_determined_by_white_col1 {H : Nat → Int → Bool} {m s1 s2 : Nat}
    (hwest : ∀ j : Int, -((2 * m : Nat) : Int) ≤ j → j ≤ 0 → ObeysAt H j)
    (hc1 : ∀ k, k ≤ 2 * m → H (s1 + k) 0 = (k % 2 == 1))
    (hc2 : ∀ k, k ≤ 2 * m → H (s2 + k) 0 = (k % 2 == 1))
    (hr : ∀ k, k < m → H (s1 + 2 * k) 1 = H (s2 + 2 * k) 1) :
    seg H s1 (-((2 * m : Nat) : Int)) (2 * m) = seg H s2 (-((2 * m : Nat) : Int)) (2 * m) := by
  have hor : ∀ k, k < 2 * m → (H (s1 + k) 0 || H (s1 + k) 1) = (H (s2 + k) 0 || H (s2 + k) 1) := by
    intro k hk
    rw [hc1 k (by omega), hc2 k (by omega)]
    by_cases he : k % 2 = 0
    · have h0 : (k % 2 == 1) = false := beq_eq_false_iff_ne.mpr (by omega)
      rw [h0, Bool.false_or, Bool.false_or, show k = 2 * (k / 2) by omega]
      exact hr (k / 2) (by omega)
    · have h1 : (k % 2 == 1) = true := beq_iff_eq.mpr (by omega)
      rw [h1, Bool.true_or, Bool.true_or]
  have htri : ∀ d : Nat, d ≤ 2 * m →
      (∀ k, k + d ≤ 2 * m → H (s1 + k) (-(d : Int)) = H (s2 + k) (-(d : Int))) ∧
      (d < 2 * m → ∀ k, k + (d + 1) ≤ 2 * m → H (s1 + k) (-((d + 1 : Nat) : Int)) = H (s2 + k) (-((d + 1 : Nat) : Int))) := by
    intro d
    induction d with
    | zero =>
      intro _
      refine ⟨fun k hk => by simpa using (hc1 k hk).trans (hc2 k hk).symm, fun _ k hk => ?_⟩
      have e : (-((1 : Nat) : Int)) = 0 - 1 := rfl
      rw [e, obeys_left_inv (hwest 0 (by omega) (by omega)), obeys_left_inv (hwest 0 (by omega) (by omega))]
      rw [show s1 + k + 1 = s1 + (k + 1) by omega, show s2 + k + 1 = s2 + (k + 1) by omega,
          hc1 (k + 1) (by omega), hc2 (k + 1) (by omega), show (0 : Int) + 1 = 1 by rfl, hor k (by omega)]
    | succ d ih =>
      intro hd
      obtain ⟨hprev, hcur⟩ := ih (by omega)
      refine ⟨hcur (by omega), fun hdlt k hk => ?_⟩
      have e1 : (-((d + 1 + 1 : Nat) : Int)) = (-((d + 1 : Nat) : Int)) - 1 := by omega
      have e2 : (-((d + 1 : Nat) : Int)) + 1 = -(d : Int) := by omega
      rw [e1, obeys_left_inv (hwest (-((d + 1 : Nat) : Int)) (by omega) (by omega)),
          obeys_left_inv (hwest (-((d + 1 : Nat) : Int)) (by omega) (by omega)), e2,
          show s1 + k + 1 = s1 + (k + 1) by omega, show s2 + k + 1 = s2 + (k + 1) by omega,
          hcur (by omega) (k + 1) (by omega), hcur (by omega) k (by omega), hprev k (by omega)]
  have hseg_eq : ∀ (n : Nat) (a : Int), (∀ j, j < n → H s1 (a + j) = H s2 (a + j)) → seg H s1 a n = seg H s2 a n := by
    intro n
    induction n with
    | zero => intro _ _; rfl
    | succ n ih =>
      intro a h
      simp only [seg]
      congr 1
      · simpa using h 0 (by omega)
      · exact ih (a + 1) (fun j hj => by simpa [show a + 1 + (j : Int) = a + ((j + 1 : Nat) : Int) by omega] using h (j + 1) (by omega))
  apply hseg_eq
  intro j hj
  have hd : 2 * m - j ≤ 2 * m := by omega
  have hcell := (htri (2 * m - j) hd).1 0 (by omega)
  rw [show -((2 * m : Nat) : Int) + (j : Int) = -((2 * m - j : Nat) : Int) by omega]; exact hcell

/-- **Universal Alternating-Column Spatial Diversity Bound (`alternating_leftWord_diversity_15_11`):**
in **any** Rule 30 spacetime `H` obeying columns `-2*m .. 6` whose column `0` alternates from `T` on,
every list `ts` of white-phase ages `≥ T + 4` with pairwise distinct `2*m`-cell spatial words west of
column `0` satisfies `ts.length * 11 ^ m ≤ 229 * 15 ^ m` (below `0.22373` bits per spatial cell,
with zero trap assumption and explicit `T + 4` onset). -/
theorem alternating_leftWord_diversity_15_11 {H : Nat → Int → Bool} {T m : Nat}
    (hwest : ∀ j : Int, -((2 * m : Nat) : Int) ≤ j → j ≤ 0 → ObeysAt H j)
    (heast : Obeys 6 H)
    (halt : ∀ t, T ≤ t → H t 0 = ((t - T) % 2 == 1))
    (ts : List Nat)
    (hts : ∀ t ∈ ts, T + 4 ≤ t ∧ (t - T) % 2 = 0)
    (hnd : (ts.map (fun t => seg H t (-((2 * m : Nat) : Int)) (2 * m))).Nodup) :
    ts.length * 11 ^ m ≤ 229 * 15 ^ m := by
  let obs : Nat → List Bool := fun t => (List.range m).map (fun k => H (t + 2 * k) 1)
  have hobs_in : ∀ t ∈ ts, obs t ∈ onset6DfaWords 0 m := by
    intro t ht
    obtain ⟨ht4, hpar⟩ := hts t ht
    have hc : ∀ i, i < 2 * m + 4 → H ((t - 4) + i) 0 = (i % 2 == 1) := by
      intro i hi
      rw [halt ((t - 4) + i) (by omega)]
      have : ((t - 4) + i - T) % 2 = i % 2 := by omega
      rw [this]
    have hacc := onset6Dfa_sound_of_obeys6 heast (t - 4) m hc
    have hshift : (List.range m).map (fun k => H ((t - 4) + 4 + 2 * k) 1) = obs t := by
      apply List.map_congr_left; intro k _; rw [show t - 4 + 4 = t by omega]
    rw [hshift] at hacc
    exact (mem_onset6DfaWords_iff m 0 (obs t)).mpr ⟨by simp [obs], hacc⟩
  have hobs_nd : (ts.map obs).Nodup := by
    have aux : ∀ (l : List Nat), (∀ t ∈ l, T + 4 ≤ t ∧ (t - T) % 2 = 0) →
        (l.map (fun t => seg H t (-((2 * m : Nat) : Int)) (2 * m))).Nodup → (l.map obs).Nodup := by
      intro l
      induction l with
      | nil => intro _ _; exact List.nodup_nil
      | cons a rest ih =>
        intro hl hndl
        obtain ⟨ha_not, hnd_r⟩ := List.nodup_cons.mp hndl
        apply List.nodup_cons.mpr
        refine ⟨?_, ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)) hnd_r⟩
        intro hm
        obtain ⟨b, hb, hobs_eq⟩ := List.mem_map.mp hm
        have ha_p := hl a List.mem_cons_self
        have hb_p := hl b (List.mem_cons_of_mem _ hb)
        have hr : ∀ k, k < m → H (b + 2 * k) 1 = H (a + 2 * k) 1 := by
          intro k hk
          have hg := congrArg (fun u => u.getD k false) hobs_eq
          simpa [obs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk] using hg
        have hseg_eq := leftSeg_determined_by_white_col1 hwest
          (fun k _ => by rw [halt (b + k) (by omega), show (b + k - T) % 2 = k % 2 by omega])
          (fun k _ => by rw [halt (a + k) (by omega), show (a + k - T) % 2 = k % 2 by omega]) hr
        exact ha_not (List.mem_map.mpr ⟨b, hb, hseg_eq⟩)
    exact aux ts hts hnd
  have hle : ts.length ≤ (onset6DfaWords 0 m).length := by
    have aux_le : ∀ (xs ys : List (List Bool)), xs.Nodup → (∀ x ∈ xs, x ∈ ys) → xs.length ≤ ys.length := by
      intro xs
      induction xs with
      | nil => intro _ _ _; exact Nat.zero_le _
      | cons x xs ih =>
        intro ys hndx hsubx
        obtain ⟨hxn, hndxs⟩ := List.nodup_cons.mp hndx
        have hxmem := hsubx x List.mem_cons_self
        have hrec := ih (ys.erase x) hndxs (fun z hz =>
          (List.mem_erase_of_ne (fun e => hxn (by subst e; exact hz))).mpr (hsubx z (List.mem_cons_of_mem _ hz)))
        have her : (ys.erase x).length + 1 = ys.length := by
          rw [List.length_erase_of_mem hxmem]; have := List.length_pos_of_mem hxmem; omega
        simp only [List.length_cons]; omega
    simpa [List.length_map] using aux_le (ts.map obs) (onset6DfaWords 0 m) hobs_nd (fun w hw => by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hw; exact hobs_in t ht)
  exact Nat.le_trans (Nat.mul_le_mul_right _ hle) (onset6Dfa_wordCount_le_15_11 m)

end Rule30PeriodTwoOnset
end Ruliology.CellularAutomata
