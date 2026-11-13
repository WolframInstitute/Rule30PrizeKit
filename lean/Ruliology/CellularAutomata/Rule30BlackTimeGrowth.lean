module

public import Ruliology.CellularAutomata.Rule30BlackRunErosion

@[expose] public section

/-!
# Rule 30: black center cells grow at least like `log_{8/5}`

Let `b₀ = 0 < b₁ < b₂ < ⋯` be the times at which the center column of rule 30 (started from
a single black cell) is black, and let `g_j` be the number of white cells at positions
`1, 2, …` before the first black cell, in row `b_j + 1`.

Main result (`black_time_bound`): `5^j · (b_j + 20) ≤ 20 · 8^j` for every `j`.
Corollary (`log_eight_fifths_le_blackCount`): if `20 · 8^j ≤ 5^j · (N + 19)` then
`j + 1 ≤ blackCount N`, i.e. `blackCount N ≥ 1 + ⌊log_{8/5} ((N + 19) / 20)⌋`. This raises the
base of `Rule30CenterRuns.log_two_succ_le_blackCount` from `2` to `8/5`.

Ingredients, all for consecutive black times `b < b'` with `w = b' - b - 1` white center cells
between them, and gaps `g` (row `b + 1`) and `g'` (row `b' + 1`):

1. `good_step`: if `g ≤ 6` then `5 b' ≤ 8 b + 36` (white-run erosion,
   `Rule30BlackRunErosion.white_run_le_erosion`).
2. `double_step`: `b' ≤ 2 b + 2` (`Rule30CenterRuns.white_run_le'`).
3. `bad_gap`: if `g' > 6` then `g ≤ 5` and `b' ≤ b + 14`. Two finite invariants of the strip
   to the right of the center, valid for every right exterior input:
   * `six_white_reset`: six white cells at positions `1..6`, any number of white center
     inputs and then one black input leave a black cell among positions `1..7`;
   * `shield`: once position `1` is black, nine white center inputs force the prefix
     black-white-black at positions `1, 2, 3`, which persists; one step later position `3`
     is black, so `g' ≤ 2`.
4. Induction: a step from a gap `≤ 6` multiplies `b + 20` by at most `8/5`; a step from a
   gap `> 6` is preceded by a short step from a gap `≤ 5`, and the pair multiplies
   `b + 20` by at most `64/25`.
-/

namespace Ruliology.CellularAutomata
namespace Rule30BlackTimeGrowth

open Rule30Jen Rule30Prize Rule30CenterRuns Rule30BlackRuns Rule30BlackRunErosion

/-! ## Finite strips to the right of the center -/

local instance forallBoolDec (P : Bool → Prop) [DecidablePred P] : Decidable (∀ b, P b) :=
  decidable_of_iff (P false ∧ P true)
    ⟨fun h b => by cases b; exact h.1; exact h.2, fun h => ⟨h _, h _⟩⟩

/-- One rule-30 step of a finite strip with left input `l` and right input `r`. -/
def stepL (l r : Bool) : List Bool → List Bool
  | [] => []
  | [x] => [rule l x r]
  | x :: y :: zs => rule l x y :: stepL x r (y :: zs)

/-- The cells at positions `p, p + 1, …, p + k - 1` at time `t`. -/
def rowFrom (t : Nat) (p : Int) : Nat → List Bool
  | 0 => []
  | k + 1 => cell t p :: rowFrom t (p + 1) k

/-- The strip evolves by `stepL`, with the cells just outside it as inputs. -/
theorem rowFrom_succ (t : Nat) : ∀ (k : Nat) (p : Int),
    rowFrom (t + 1) p k = stepL (cell t (p - 1)) (cell t (p + k)) (rowFrom t p k)
  | 0, _ => rfl
  | 1, p => by
    show [cell (t + 1) p] = [rule (cell t (p - 1)) (cell t p) (cell t (p + ((1 : Nat) : Int)))]
    rfl
  | k + 2, p => by
    have ih := rowFrom_succ t (k + 1) (p + 1)
    rw [show p + 1 - 1 = p by omega, show p + 1 + ((k + 1 : Nat) : Int) = p + ((k + 2 : Nat) : Int)
      by omega] at ih
    show cell (t + 1) p :: rowFrom (t + 1) (p + 1) (k + 1) = _
    rw [ih]
    rfl

/-- Binary code of a strip, position `p + i` at bit `i`. -/
def code : List Bool → Nat
  | [] => 0
  | x :: xs => x.toNat + 2 * code xs

/-- An invariant set of 8-cell strips under white center input (bit `s` of the mask is set
iff the strip with code `s` is in the set). -/
def resetMask : Nat := 0x2868302ba120302120290022a1282221286820092120102320290062a0282221

def Reset (xs : List Bool) : Bool := resetMask.testBit (code xs)

theorem reset_init : ∀ x7 x8 : Bool,
    Reset [false, false, false, false, false, false, x7, x8] = true := by decide

theorem reset_closed : ∀ x1 x2 x3 x4 x5 x6 x7 x8 r : Bool,
    Reset [x1, x2, x3, x4, x5, x6, x7, x8] = true →
    Reset (stepL false r [x1, x2, x3, x4, x5, x6, x7, x8]) = true := by decide

theorem reset_escape : ∀ x1 x2 x3 x4 x5 x6 x7 x8 r : Bool,
    Reset [x1, x2, x3, x4, x5, x6, x7, x8] = true →
    (stepL true r [x1, x2, x3, x4, x5, x6, x7, x8]).take 7
      ≠ [false, false, false, false, false, false, false] := by decide

/-- The reachable sets of 6-cell strips after `n` white center inputs, starting from a black
first cell. -/
def stageMask : Nat → Nat
  | 0 => 0xaaaaaaaaaaaaaaaa
  | 1 => 0xaa2aa22aaa22a22a
  | 2 => 0xa82aa22aa822a22a
  | 3 => 0xa82aa22aa822222a
  | 4 => 0xa828a22aa820222a
  | 5 => 0xa028a22aa020222a
  | 6 => 0xa028a02aa020202a
  | 7 => 0x2028202a2020202a
  | 8 => 0x2028202820202028
  | _ => 0x2020202020202020

def Stage (n : Nat) (xs : List Bool) : Bool := (stageMask n).testBit (code xs)

theorem stage_init : ∀ x2 x3 x4 x5 x6 : Bool, Stage 0 [true, x2, x3, x4, x5, x6] = true := by
  decide

theorem stage_closed : ∀ n, n < 9 → ∀ x1 x2 x3 x4 x5 x6 r : Bool,
    Stage n [x1, x2, x3, x4, x5, x6] = true →
    Stage (n + 1) (stepL false r [x1, x2, x3, x4, x5, x6]) = true := by decide

theorem stage_terminal : ∀ x1 x2 x3 x4 x5 x6 : Bool,
    Stage 9 [x1, x2, x3, x4, x5, x6] = true → x1 = true ∧ x2 = false ∧ x3 = true := by decide

/-! ## The strips in the orbit -/

theorem cell_succ (t : Nat) (p : Int) :
    cell (t + 1) p = rule (cell t (p - 1)) (cell t p) (cell t (p + 1)) := rfl

theorem row8 (t : Nat) : rowFrom t 1 8 =
    [cell t 1, cell t 2, cell t 3, cell t 4, cell t 5, cell t 6, cell t 7, cell t 8] := rfl

theorem row6 (t : Nat) : rowFrom t 1 6 =
    [cell t 1, cell t 2, cell t 3, cell t 4, cell t 5, cell t 6] := rfl

theorem reset_orbit (r : Nat) (w : Nat) (hr : Reset (rowFrom r 1 8) = true)
    (hw : ∀ i, i < w → cell (r + i) 0 = false) : Reset (rowFrom (r + w) 1 8) = true := by
  induction w with
  | zero => exact hr
  | succ w ih =>
    have h := ih (fun i hi => hw i (by omega))
    rw [← Nat.add_assoc, rowFrom_succ, show (1 : Int) - 1 = 0 from rfl, hw w (by omega)]
    rw [row8] at h ⊢
    exact reset_closed _ _ _ _ _ _ _ _ _ h

/-- **Six white cells reset the gap.** If positions `1..6` are white at time `r`, the center
is white at times `r, …, r + w - 1` and black at time `r + w`, then some position in `1..7` is
black at time `r + w + 1`. -/
theorem six_white_reset (r w : Nat) (h6 : ∀ p : Int, 1 ≤ p → p ≤ 6 → cell r p = false)
    (hw : ∀ i, i < w → cell (r + i) 0 = false) (hb : cell (r + w) 0 = true) :
    ∃ p : Int, 1 ≤ p ∧ p ≤ 7 ∧ cell (r + w + 1) p = true := by
  have h0 : Reset (rowFrom r 1 8) = true := by
    rw [row8, h6 1 (by omega) (by omega), h6 2 (by omega) (by omega), h6 3 (by omega) (by omega),
      h6 4 (by omega) (by omega), h6 5 (by omega) (by omega), h6 6 (by omega) (by omega)]
    exact reset_init _ _
  have h1 := reset_orbit r w h0 hw
  rw [row8] at h1
  have h2 := reset_escape _ _ _ _ _ _ _ _ (cell (r + w) 9) h1
  have e := rowFrom_succ (r + w) 8 1
  rw [show (1 : Int) - 1 = 0 from rfl, hb, show (1 : Int) + ((8 : Nat) : Int) = 9 from rfl,
    row8, row8] at e
  rw [← e] at h2
  refine Classical.byContradiction fun hcon => h2 ?_
  have hf : ∀ p : Int, 1 ≤ p → p ≤ 7 → cell (r + w + 1) p = false := by
    intro p h1 h2
    cases hc : cell (r + w + 1) p
    · rfl
    · exact absurd ⟨p, h1, h2, hc⟩ hcon
  rw [hf 1 (by omega) (by omega), hf 2 (by omega) (by omega), hf 3 (by omega) (by omega),
    hf 4 (by omega) (by omega), hf 5 (by omega) (by omega), hf 6 (by omega) (by omega),
    hf 7 (by omega) (by omega)]
  rfl

theorem stage_orbit (r : Nat) (h1 : cell r 1 = true) (hw : ∀ i, i < 9 → cell (r + i) 0 = false) :
    ∀ n, n ≤ 9 → Stage n (rowFrom (r + n) 1 6) = true := by
  intro n
  induction n with
  | zero => intro _; rw [row6, Nat.add_zero, h1]; exact stage_init _ _ _ _ _
  | succ n ih =>
    intro hn
    have h := ih (by omega)
    rw [← Nat.add_assoc, rowFrom_succ, show (1 : Int) - 1 = 0 from rfl, hw n (by omega)]
    rw [row6] at h ⊢
    exact stage_closed n (by omega) _ _ _ _ _ _ _ h

/-- **The shield.** If position `1` is black at time `r` and the center is white at times
`r, …, r + n - 1` with `n ≥ 9`, then positions `1, 2, 3` are black, white, black at time
`r + n`. -/
theorem shield (r n : Nat) (hn : 9 ≤ n) (h1 : cell r 1 = true)
    (hw : ∀ i, i < n → cell (r + i) 0 = false) :
    cell (r + n) 1 = true ∧ cell (r + n) 2 = false ∧ cell (r + n) 3 = true := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 9 + m := ⟨n - 9, by omega⟩
  induction m with
  | zero =>
    have := stage_orbit r h1 (fun i hi => hw i hi) 9 (Nat.le_refl _)
    rw [row6] at this
    exact stage_terminal _ _ _ _ _ _ this
  | succ m ih =>
    have ih := ih (by omega) (fun i hi => hw i (by omega))
    obtain ⟨a1, a2, a3⟩ := ih
    have c0 := hw (9 + m) (by omega)
    rw [show 9 + (m + 1) = (9 + m) + 1 by omega, ← Nat.add_assoc]
    refine ⟨?_, ?_, ?_⟩
    · rw [cell_succ, show (1 : Int) - 1 = 0 from rfl, c0, a1]; rfl
    · rw [cell_succ, show (2 : Int) - 1 = 1 from rfl, show (2 : Int) + 1 = 3 from rfl, a1, a2, a3]
      rfl
    · rw [cell_succ, show (3 : Int) - 1 = 2 from rfl, a2, a3]; rfl

/-- Under white center input, a white gap at positions `1..g` before a black cell shrinks by
one per step. -/
theorem gap_shrink (r g : Nat) (hg : ∀ p : Int, 1 ≤ p → p ≤ g → cell r p = false)
    (hb : cell r ((g : Int) + 1) = true) (hw : ∀ i, i < g → cell (r + i) 0 = false) :
    ∀ k, k ≤ g → (∀ p : Int, 1 ≤ p → p ≤ (g : Int) - k → cell (r + k) p = false) ∧
      cell (r + k) ((g : Int) - k + 1) = true := by
  intro k
  induction k with
  | zero => intro _; exact ⟨fun p h1 h2 => hg p h1 (by omega), by simpa using hb⟩
  | succ k ih =>
    intro hk
    obtain ⟨A, B⟩ := ih (by omega)
    have left : ∀ p : Int, 1 ≤ p → p ≤ (g : Int) - k → cell (r + k) (p - 1) = false := by
      intro p h1 h2
      by_cases hp : p = 1
      · rw [hp, show (1 : Int) - 1 = 0 from rfl]; exact hw k (by omega)
      · exact A _ (by omega) (by omega)
    rw [← Nat.add_assoc]
    refine ⟨fun p h1 h2 => ?_, ?_⟩
    · rw [cell_succ, left p h1 (by omega), A p h1 (by omega), A (p + 1) (by omega) (by omega)]; rfl
    · rw [cell_succ, show (g : Int) - ((k + 1 : Nat) : Int) + 1 - 1 = ((g : Int) - k) - 1 by omega,
        left _ (by omega) (by omega), show (g : Int) - ((k + 1 : Nat) : Int) + 1 = (g : Int) - k by omega,
        A _ (by omega) (by omega), show (g : Int) - k + 1 = (g : Int) - k + 1 from rfl, B]
      rfl

/-- **A long white wait leaves a small gap.** If positions `1..g` are white and `g + 1` is
black at time `r`, the center is white at times `r, …, r + w - 1` with `w ≥ g + 9`,
then position `3` is black at time `r + w + 1` (whatever the center input at time `r + w`). -/
theorem long_wait (r g w : Nat) (hg : ∀ p : Int, 1 ≤ p → p ≤ g → cell r p = false)
    (hb : cell r ((g : Int) + 1) = true) (hgw : g + 9 ≤ w)
    (hw : ∀ i, i < w → cell (r + i) 0 = false) :
    cell (r + w + 1) 3 = true := by
  have h1 : cell (r + g) 1 = true := by
    have := (gap_shrink r g hg hb (fun i hi => hw i (by omega)) g (Nat.le_refl _)).2
    rwa [show (g : Int) - g + 1 = 1 by omega] at this
  have hs := shield (r + g) (w - g) (by omega) h1
    (fun i hi => by rw [Nat.add_assoc]; exact hw (g + i) (by omega))
  rw [show r + g + (w - g) = r + w by omega] at hs
  rw [cell_succ, show (3 : Int) - 1 = 2 from rfl, hs.2.1, hs.2.2]
  rfl

/-! ## Black times and gaps -/

/-- The first `t ≥ a` with `p t`, searching `k` values. -/
def firstFrom (p : Nat → Bool) (a : Nat) : Nat → Nat
  | 0 => a
  | k + 1 => if p a then a else firstFrom p (a + 1) k

theorem firstFrom_spec (p : Nat → Bool) : ∀ (k a t : Nat), a ≤ t → t < a + k → p t = true →
    a ≤ firstFrom p a k ∧ firstFrom p a k ≤ t ∧ p (firstFrom p a k) = true ∧
      ∀ u, a ≤ u → u < firstFrom p a k → p u = false := by
  intro k
  induction k with
  | zero => intro a t h1 h2; omega
  | succ k ih =>
    intro a t h1 h2 ht
    unfold firstFrom
    split
    · next hp => exact ⟨Nat.le_refl _, h1, hp, fun u h1 h2 => by omega⟩
    · next hp =>
        have hat : a ≠ t := fun e => hp (e ▸ ht)
        obtain ⟨A, B, C, D⟩ := ih (a + 1) t (by omega) (by omega) ht
        refine ⟨by omega, B, C, fun u hu1 hu2 => ?_⟩
        by_cases hu : u = a
        · subst hu; simpa using hp
        · exact D u (by omega) hu2

/-- `blackTime j` is the `(j + 1)`-st time at which the center column is black. -/
def blackTime : Nat → Nat
  | 0 => 0
  | j + 1 => firstFrom center (blackTime j + 1) (blackTime j + 1)

theorem blackTime_spec (j : Nat) :
    blackTime j < blackTime (j + 1) ∧ blackTime (j + 1) ≤ 2 * blackTime j + 1 ∧
      center (blackTime (j + 1)) = true ∧
      ∀ u, blackTime j < u → u < blackTime (j + 1) → center u = false := by
  obtain ⟨t, h1, h2, h3⟩ := exists_black' (blackTime j + 1) (by omega)
  obtain ⟨A, B, C, D⟩ := firstFrom_spec center (blackTime j + 1) (blackTime j + 1) t h1 (by omega) h3
  refine ⟨A, ?_, C, fun u h1 h2 => D u h1 h2⟩
  show firstFrom center (blackTime j + 1) (blackTime j + 1) ≤ 2 * blackTime j + 1
  omega

theorem center_blackTime : ∀ j, center (blackTime j) = true
  | 0 => rfl
  | j + 1 => (blackTime_spec j).2.2.1

/-- The number of white cells at positions `1, 2, …` before the first black one, at time `t`. -/
def gap (t : Nat) : Nat := firstFrom (fun p => cell t ((p : Int) + 1)) 0 t

theorem gap_spec (t : Nat) (ht : 1 ≤ t) :
    (∀ p : Int, 1 ≤ p → p ≤ gap t → cell t p = false) ∧ cell t ((gap t : Int) + 1) = true := by
  have hr : cell t (((t - 1 : Nat) : Int) + 1) = true := by
    rw [show ((t - 1 : Nat) : Int) + 1 = (t : Int) by omega]; exact cell_right_edge t
  obtain ⟨_, _, C, D⟩ := firstFrom_spec (fun p => cell t ((p : Int) + 1)) t 0 (t - 1)
    (Nat.zero_le _) (by omega) hr
  refine ⟨fun p h1 h2 => ?_, C⟩
  unfold gap at h2
  have := D (p - 1).toNat (Nat.zero_le _) (by omega)
  rwa [show (((p - 1).toNat : Nat) : Int) + 1 = p by omega] at this

/-- `g j`: the gap right of the center just after the `j`-th black center cell. -/
def g (j : Nat) : Nat := gap (blackTime j + 1)

/-! ## The three step estimates -/

/-- **Good step**: after a gap `≤ 6`, `5 b_{j+1} ≤ 8 b_j + 36`. -/
theorem good_step (j : Nat) (hg : g j ≤ 6) : 5 * blackTime (j + 1) ≤ 8 * blackTime j + 36 := by
  obtain ⟨h1, _, _, hw⟩ := blackTime_spec j
  obtain ⟨G1, G2⟩ := gap_spec (blackTime j + 1) (by omega)
  have hrun : ∀ i, i < blackTime (j + 1) - blackTime j - 1 →
      center (blackTime j + 1 + i) = false := fun i hi => hw _ (by omega) (by omega)
  by_cases ha : g j + 3 ≤ blackTime j + 1
  · have := white_run_le_erosion (blackTime j + 1) (blackTime (j + 1) - blackTime j - 1) (g j) hrun
      (fun p h1 h2 => G1 p (by omega) (by have : g j = gap (blackTime j + 1) := rfl; omega))
      G2 ((blackTime j + 1 - g j - 3) / 5) (by omega)
    omega
  · have := white_run_le' (blackTime j + 1) (blackTime (j + 1) - blackTime j - 1) (by omega) hrun
    omega

/-- **Doubling step**: `b_{j+1} ≤ 2 b_j + 2`. -/
theorem double_step (j : Nat) : blackTime (j + 1) ≤ 2 * blackTime j + 2 := by
  have := (blackTime_spec j).2.1; omega

/-- **Bad gaps follow short steps from small gaps**: if `g_{j+1} > 6`, then `g_j ≤ 5` and
`b_{j+1} ≤ b_j + 14`. -/
theorem bad_gap (j : Nat) (hg : 6 < g (j + 1)) : g j ≤ 5 ∧ blackTime (j + 1) ≤ blackTime j + 14 := by
  obtain ⟨h1, _, hc, hw⟩ := blackTime_spec j
  obtain ⟨G1, G2⟩ := gap_spec (blackTime j + 1) (by omega)
  obtain ⟨G1', _⟩ := gap_spec (blackTime (j + 1) + 1) (by omega)
  have hw' : ∀ i, i < blackTime (j + 1) - blackTime j - 1 →
      cell (blackTime j + 1 + i) 0 = false := fun i hi => hw _ (by omega) (by omega)
  have hc' : cell (blackTime j + 1 + (blackTime (j + 1) - blackTime j - 1)) 0 = true := by
    rw [show blackTime j + 1 + (blackTime (j + 1) - blackTime j - 1) = blackTime (j + 1) by omega]
    exact hc
  have e : blackTime j + 1 + (blackTime (j + 1) - blackTime j - 1) + 1 = blackTime (j + 1) + 1 := by
    omega
  constructor
  · refine Nat.le_of_not_lt fun h5 => ?_
    obtain ⟨p, hp1, hp2, hp⟩ := six_white_reset _ _
      (fun p h1 h2 => G1 p h1 (by have : g j = gap (blackTime j + 1) := rfl; omega)) hw' hc'
    rw [e, G1' p hp1 (by have : g (j + 1) = gap (blackTime (j + 1) + 1) := rfl; omega)] at hp
    exact Bool.noConfusion hp
  · refine Nat.le_of_not_lt fun h14 => ?_
    have h5 : g j ≤ 5 := by
      refine Nat.le_of_not_lt fun h5 => ?_
      obtain ⟨p, hp1, hp2, hp⟩ := six_white_reset _ _
        (fun p h1 h2 => G1 p h1 (by have : g j = gap (blackTime j + 1) := rfl; omega)) hw' hc'
      rw [e, G1' p hp1 (by have : g (j + 1) = gap (blackTime (j + 1) + 1) := rfl; omega)] at hp
      exact Bool.noConfusion hp
    have := long_wait _ (g j) _ (fun p h1 h2 => G1 p h1 (by have : g j = gap (blackTime j + 1) := rfl; omega)) G2
      (by omega) hw'
    rw [e, G1' 3 (by omega) (by have : g (j + 1) = gap (blackTime (j + 1) + 1) := rfl; omega)] at this
    exact Bool.noConfusion this

theorem g_zero : g 0 = 0 := rfl

/-! ## Assembly -/

/-- One good step multiplies `b + 20` by at most `8/5`. -/
theorem bound_good (j : Nat) (hg : g j ≤ 6) (h : 5 ^ j * (blackTime j + 20) ≤ 20 * 8 ^ j) :
    5 ^ (j + 1) * (blackTime (j + 1) + 20) ≤ 20 * 8 ^ (j + 1) := by
  have h1 := good_step j hg
  have : 5 * (blackTime (j + 1) + 20) ≤ 8 * (blackTime j + 20) := by omega
  calc 5 ^ (j + 1) * (blackTime (j + 1) + 20)
      = 5 ^ j * (5 * (blackTime (j + 1) + 20)) := by rw [Nat.pow_succ, Nat.mul_assoc]
    _ ≤ 5 ^ j * (8 * (blackTime j + 20)) := Nat.mul_le_mul_left _ this
    _ = 8 * (5 ^ j * (blackTime j + 20)) := by
      rw [← Nat.mul_assoc, Nat.mul_comm (5 ^ j) 8, Nat.mul_assoc]
    _ ≤ 8 * (20 * 8 ^ j) := Nat.mul_le_mul_left _ h
    _ = 20 * 8 ^ (j + 1) := by rw [Nat.pow_succ]; omega

/-- A bad step together with the short step before it multiplies `b + 20` by at most
`64/25`. -/
theorem bound_bad (i : Nat) (hg : 6 < g (i + 1)) (h : 5 ^ i * (blackTime i + 20) ≤ 20 * 8 ^ i) :
    5 ^ (i + 2) * (blackTime (i + 2) + 20) ≤ 20 * 8 ^ (i + 2) := by
  have h1 := (bad_gap i hg).2
  have h2 := double_step (i + 1)
  rw [show i + 1 + 1 = i + 2 from rfl] at h2
  have : 25 * (blackTime (i + 2) + 20) ≤ 64 * (blackTime i + 20) := by omega
  calc 5 ^ (i + 2) * (blackTime (i + 2) + 20)
      = 5 ^ i * (25 * (blackTime (i + 2) + 20)) := by
        rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_assoc, Nat.mul_assoc]; congr 1; omega
    _ ≤ 5 ^ i * (64 * (blackTime i + 20)) := Nat.mul_le_mul_left _ this
    _ = 64 * (5 ^ i * (blackTime i + 20)) := by
      rw [← Nat.mul_assoc, Nat.mul_comm (5 ^ i) 64, Nat.mul_assoc]
    _ ≤ 64 * (20 * 8 ^ i) := Nat.mul_le_mul_left _ h
    _ = 20 * 8 ^ (i + 2) := by rw [Nat.pow_succ, Nat.pow_succ]; omega

/-- **Black times grow at most like `(8/5)^j`**: `5^j · (b_j + 20) ≤ 20 · 8^j`, where `b_j` is
the `(j + 1)`-st black time of the center column. -/
theorem black_time_bound (j : Nat) : 5 ^ j * (blackTime j + 20) ≤ 20 * 8 ^ j := by
  have pair : ∀ j, 5 ^ j * (blackTime j + 20) ≤ 20 * 8 ^ j ∧
      5 ^ (j + 1) * (blackTime (j + 1) + 20) ≤ 20 * 8 ^ (j + 1) := by
    intro j
    induction j with
    | zero => exact ⟨by decide, bound_good 0 (by rw [g_zero]; decide) (by decide)⟩
    | succ i ih =>
      refine ⟨ih.2, ?_⟩
      by_cases hg : g (i + 1) ≤ 6
      · exact bound_good (i + 1) hg ih.2
      · exact bound_bad i (by omega) ih.1
  exact (pair j).1

/-- The first `j + 1` black times are counted by `blackCount (b_j + 1)`. -/
theorem blackCount_blackTime : ∀ j, j + 1 ≤ blackCount (blackTime j + 1)
  | 0 => by decide
  | j + 1 => by
    have ih := blackCount_blackTime j
    have := blackCount_lt (a := blackTime j + 1) (b := blackTime (j + 1) + 1)
      (t := blackTime (j + 1)) (by have := (blackTime_spec j).1; omega) (by omega)
      (center_blackTime (j + 1))
    omega

/-- **`blackCount N ≥ 1 + ⌊log_{8/5} ((N + 19) / 20)⌋`**, in integer form: if
`20 · 8^j ≤ 5^j · (N + 19)` then at least `j + 1` of the cells `center 0, …, center (N - 1)`
are black. -/
theorem log_eight_fifths_le_blackCount (j N : Nat) (h : 20 * 8 ^ j ≤ 5 ^ j * (N + 19)) :
    j + 1 ≤ blackCount N := by
  have h1 := black_time_bound j
  have h2 : 5 ^ j * (blackTime j + 20) ≤ 5 ^ j * (N + 19) := Nat.le_trans h1 h
  have h3 : blackTime j + 20 ≤ N + 19 := Nat.le_of_mul_le_mul_left h2 (Nat.pow_pos (by decide))
  exact Nat.le_trans (blackCount_blackTime j) (blackCount_mono _ _ (by omega))

/-! ## Exclusion of consecutive bad gaps `> 6` and good-step bound prior to any bad gap -/

/-- **No Consecutive Bad Gaps `> 6` and Good-Step Bound Prior to Any Bad Gap (`no_consecutive_bad_gaps_and_good_before_bad`).** -/
theorem no_consecutive_bad_gaps_and_good_before_bad (j : Nat) :
    (g j ≤ 6 ∨ g (j + 1) ≤ 6) ∧
    (6 < g (j + 1) → g j ≤ 5 ∧ blackTime (j + 1) ≤ blackTime j + 14 ∧
      5 * blackTime (j + 1) ≤ 8 * blackTime j + 36) := by
  refine ⟨?_, fun hbad => ?_⟩
  · by_cases h1 : g (j + 1) ≤ 6
    · exact Or.inr h1
    · have hb := (bad_gap j (by omega)).1
      exact Or.inl (by omega)
  · obtain ⟨hg5, hle14⟩ := bad_gap j hbad
    exact ⟨hg5, hle14, good_step j (by omega)⟩

end Rule30BlackTimeGrowth
end Ruliology.CellularAutomata
