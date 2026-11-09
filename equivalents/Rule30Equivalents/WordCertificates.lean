module

public import Ruliology.CellularAutomata.Rule30Prize
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Rule 30: no smaller observable certifies the word `1001`

Let `X_t = x_t[-1, 2]` be the four cells around the center, `a_t = 1` iff `X_t = 1001`, and
`S_t = x_t[-7, 8]` the sixteen-cell state. Rule 30 has the spatially 4-periodic cycle of rows
`1 → 11 → 8 → 13 → 4 → 14 → 2 → 7 → 1` (a row is a 4-bit integer, site `i` in bit `i`). Along it
the window `X` runs through the eight odd-parity words, so `a = 0` there and every proper subset
of the four window cells takes every value.

**Theorem** (`no_smaller_certificate`). For a proper subset `J` of the window, a nonnegative
function `ψ` of the cells in `J` and any rational function `φ` of the sixteen-cell state, if
`a_t ≥ ψ (x_t|_J) + φ (S_(t+1)) - φ (S_t)` holds on the eight transitions of the cycle, then
`ψ = 0`. Summing over the cycle telescopes `φ`.

The same holds for every even-parity target word (`all_even_targets`). On the single-seed
pattern, `S_97 = S_143` and `1001` occurs at times `109` and `133` in between, so `a_t` is not an
exact coboundary `φ (S_(t+1)) - φ (S_t)` of the sixteen-cell state (`no_exact_coboundary`).
-/

namespace Rule30Equivalents.WordCertificates

open Ruliology.CellularAutomata.Rule30Jen
open Ruliology.CellularAutomata.Rule30Prize

/-! ### Spatially 4-periodic rows -/

/-- A spatially 4-periodic row: site `i` of the period, `i : Fin 4`. -/
abbrev Row4 := Fin 4 → Bool

/-- The row encoded by a 4-bit integer, site `i` in bit `i`. -/
def ofNat (n : Nat) : Row4 := fun i => n.testBit i.val

/-- One Rule 30 step on a 4-periodic row. -/
def step4 (ρ : Row4) : Row4 := fun i => rule (ρ (i - 1)) (ρ i) (ρ (i + 1))

/-- The cycle `1 → 11 → 8 → 13 → 4 → 14 → 2 → 7 → 1`. -/
def cycle (k : Fin 8) : Row4 := ofNat ([1, 11, 8, 13, 4, 14, 2, 7].getD k.val 0)

/-- The window `X ρ` of positions `-1, 0, 1, 2` of the periodic row `ρ`. -/
def X (ρ : Row4) : Fin 4 → Bool := fun j => ρ (j + 3)

/-- The sixteen-cell state `S ρ` of positions `-7, …, 8` of the periodic row `ρ`. -/
def S (ρ : Row4) : Fin 16 → Bool := fun m => ρ ⟨(m.val + 1) % 4, Nat.mod_lt _ (by decide)⟩

/-- Odd parity of a four-letter word. -/
def parityOdd (w : Fin 4 → Bool) : Bool := xor (xor (w 0) (w 1)) (xor (w 2) (w 3))

/-- The target indicator `a w = 1` iff `w = 1001`. -/
def a (w : Fin 4 → Bool) : ℚ := if w = ![true, false, false, true] then 1 else 0

/-- The restriction of a word to the cells in `J`. -/
def restrict (J : Finset (Fin 4)) (w : Fin 4 → Bool) : J → Bool := fun i => w i.val

/-! ### The cycle -/

theorem step4_cycle : ∀ k : Fin 8, step4 (cycle k) = cycle (k + 1) := by decide

/-- A word is determined by its four letters. -/
theorem word_eq (w : Fin 4 → Bool) : w = ![w 0, w 1, w 2, w 3] := by
  funext i; fin_cases i <;> rfl

/-- On the cycle the window runs through the eight odd-parity words. -/
theorem X_cycle_odd : ∀ k : Fin 8, parityOdd (X (cycle k)) := by decide

theorem odd_mem_cycle (w : Fin 4 → Bool) (hw : parityOdd w) : ∃ k : Fin 8, X (cycle k) = w := by
  have key : ∀ b0 b1 b2 b3 : Bool, xor (xor b0 b1) (xor b2 b3) = true →
      ∃ k : Fin 8, X (cycle k) = ![b0, b1, b2, b3] := by decide
  rw [word_eq w]
  exact key _ _ _ _ hw

/-- Every value on a proper subset `J` of the window is the restriction of an odd-parity word. -/
theorem restrict_odd_surj (J : Finset (Fin 4)) (hJ : J ≠ Finset.univ) (v : J → Bool) :
    ∃ w : Fin 4 → Bool, parityOdd w ∧ restrict J w = v := by
  obtain ⟨m, hm⟩ : ∃ m, m ∉ J := by
    by_contra h
    exact hJ (Finset.eq_univ_of_forall fun i => by
      by_contra hi
      exact h ⟨i, hi⟩)
  let w0 : Fin 4 → Bool := fun i => if h : i ∈ J then v ⟨i, h⟩ else false
  let p : Bool := xor (xor (w0 0) (w0 1)) (xor (w0 2) (w0 3))
  let w : Fin 4 → Bool := fun i => if i = m then !(xor p (w0 m)) else w0 i
  refine ⟨w, ?_, ?_⟩
  · unfold parityOdd
    have e : ∀ i, w i = if i = m then !(xor p (w0 m)) else w0 i := fun _ => rfl
    rw [e 0, e 1, e 2, e 3]
    fin_cases m <;> simp [p] <;>
      cases w0 0 <;> cases w0 1 <;> cases w0 2 <;> cases w0 3 <;> decide
  · funext i
    have hi : i.val ≠ m := fun h => hm (h ▸ i.property)
    simp [restrict, w, w0, hi]

/-! ### The obstruction -/

/-- **Obstruction for any target vanishing on the cycle.** If `A ≤ 0` on the eight windows of
the cycle and `A (X_k) ≥ ψ (X_k|_J) + φ (S_(k+1)) - φ (S_k)` on its eight transitions, with
`J` a proper subset and `ψ ≥ 0`, then `ψ = 0`. -/
theorem no_certificate_of_nonpos (A : (Fin 4 → Bool) → ℚ) (hA : ∀ k : Fin 8, A (X (cycle k)) ≤ 0)
    (J : Finset (Fin 4)) (hJ : J ≠ Finset.univ) (ψ : (J → Bool) → ℚ) (hψ : ∀ v, 0 ≤ ψ v)
    (φ : (Fin 16 → Bool) → ℚ)
    (h : ∀ k : Fin 8,
      A (X (cycle k)) ≥ ψ (restrict J (X (cycle k))) + φ (S (step4 (cycle k))) - φ (S (cycle k))) :
    ∀ v, ψ v = 0 := by
  have h' : ∀ k : Fin 8,
      A (X (cycle k)) ≥ ψ (restrict J (X (cycle k))) + φ (S (cycle (k + 1))) - φ (S (cycle k)) := by
    intro k; rw [← step4_cycle k]; exact h k
  have hzero : ∀ k : Fin 8, ψ (restrict J (X (cycle k))) = 0 := by
    have h0 := h' 0; have h1 := h' 1; have h2 := h' 2; have h3 := h' 3
    have h4 := h' 4; have h5 := h' 5; have h6 := h' 6; have h7 := h' 7
    have a0 := hA 0; have a1 := hA 1; have a2 := hA 2; have a3 := hA 3
    have a4 := hA 4; have a5 := hA 5; have a6 := hA 6; have a7 := hA 7
    have p0 := hψ (restrict J (X (cycle 0))); have p1 := hψ (restrict J (X (cycle 1)))
    have p2 := hψ (restrict J (X (cycle 2))); have p3 := hψ (restrict J (X (cycle 3)))
    have p4 := hψ (restrict J (X (cycle 4))); have p5 := hψ (restrict J (X (cycle 5)))
    have p6 := hψ (restrict J (X (cycle 6))); have p7 := hψ (restrict J (X (cycle 7)))
    simp only [show (0 : Fin 8) + 1 = 1 from rfl, show (1 : Fin 8) + 1 = 2 from rfl,
      show (2 : Fin 8) + 1 = 3 from rfl, show (3 : Fin 8) + 1 = 4 from rfl,
      show (4 : Fin 8) + 1 = 5 from rfl, show (5 : Fin 8) + 1 = 6 from rfl,
      show (6 : Fin 8) + 1 = 7 from rfl, show (7 : Fin 8) + 1 = 0 from rfl]
      at h0 h1 h2 h3 h4 h5 h6 h7
    intro k
    fin_cases k <;> simp <;> linarith
  intro v
  obtain ⟨w, hw, hv⟩ := restrict_odd_surj J hJ v
  obtain ⟨k, hk⟩ := odd_mem_cycle w hw
  rw [← hv, ← hk]
  exact hzero k

/-- **No smaller certificate.** Let `J` be a proper subset of the window `{-1, 0, 1, 2}`, `ψ ≥ 0`
a function of the cells in `J` and `φ` a rational function of the sixteen-cell state. If
`a ≥ ψ (X|_J) + φ (S') - φ (S)` on the eight transitions of the cycle
`1 → 11 → 8 → 13 → 4 → 14 → 2 → 7 → 1`, then `ψ = 0`. -/
theorem no_smaller_certificate (J : Finset (Fin 4)) (hJ : J ≠ Finset.univ) (ψ : (J → Bool) → ℚ)
    (hψ : ∀ v, 0 ≤ ψ v) (φ : (Fin 16 → Bool) → ℚ)
    (h : ∀ k : Fin 8,
      a (X (cycle k)) ≥ ψ (restrict J (X (cycle k))) + φ (S (step4 (cycle k))) - φ (S (cycle k))) :
    ∀ v, ψ v = 0 := by
  apply no_certificate_of_nonpos a _ J hJ ψ hψ φ h
  intro k
  have hne : X (cycle k) ≠ ![true, false, false, true] := by
    intro he
    have := X_cycle_odd k
    rw [he] at this
    exact absurd this (by decide)
  simp [a, hne]

/-- **Every even-parity target.** The obstruction holds with `a` replaced by the indicator of
any even-parity word `e`. -/
theorem all_even_targets (e : Fin 4 → Bool) (he : ¬ parityOdd e) (J : Finset (Fin 4))
    (hJ : J ≠ Finset.univ) (ψ : (J → Bool) → ℚ) (hψ : ∀ v, 0 ≤ ψ v) (φ : (Fin 16 → Bool) → ℚ)
    (h : ∀ k : Fin 8, (if X (cycle k) = e then 1 else 0 : ℚ)
      ≥ ψ (restrict J (X (cycle k))) + φ (S (step4 (cycle k))) - φ (S (cycle k))) :
    ∀ v, ψ v = 0 := by
  apply no_certificate_of_nonpos (fun w => if w = e then 1 else 0) _ J hJ ψ hψ φ h
  intro k
  have hne : X (cycle k) ≠ e := by
    intro hk
    exact he (hk ▸ X_cycle_odd k)
  simp [hne]

/-! ### The single-seed orbit: `S_97 = S_143` -/

/-- The window `X_t = x_t[-1, 2]` of the single-seed pattern. -/
def Xt (t : Nat) : Fin 4 → Bool := fun j => cell t ((j.val : Int) - 1)

/-- The sixteen-cell state `S_t = x_t[-7, 8]` of the single-seed pattern. -/
def St (t : Nat) : Fin 16 → Bool := fun m => cell t ((m.val : Int) - 7)

theorem cell_eq_false_of_gt' : ∀ (t : Nat) (p : Int), (t : Int) < p → cell t p = false
  | 0, p, h => by simp [cell]; omega
  | t + 1, p, h => by
    show rule (cell t (p - 1)) (cell t p) (cell t (p + 1)) = false
    rw [cell_eq_false_of_gt' t (p - 1) (by omega), cell_eq_false_of_gt' t p (by omega),
      cell_eq_false_of_gt' t (p + 1) (by omega)]
    rfl

/-- The cells at positions `p, …, p + n - 1` at time `t`. -/
def rowAt (t : Nat) (p : Int) : Nat → List Bool
  | 0 => []
  | n + 1 => cell t p :: rowAt t (p + 1) n

/-- One Rule 30 step on a finite row with left neighbour `l`; the result is one cell shorter. -/
def stepRow (l : Bool) : List Bool → List Bool
  | a :: b :: rest => rule l a b :: stepRow a (b :: rest)
  | _ => []

theorem stepRow_rowAt (t : Nat) : ∀ (n : Nat) (p : Int),
    stepRow (cell t (p - 1)) (rowAt t p (n + 1)) = rowAt (t + 1) p n
  | 0, _ => rfl
  | n + 1, p => by
    have ih := stepRow_rowAt t n (p + 1)
    rw [show p + 1 - 1 = p by omega] at ih
    show rule (cell t (p - 1)) (cell t p) (cell t (p + 1)) ::
        stepRow (cell t p) (rowAt t (p + 1) (n + 1)) = cell (t + 1) p :: rowAt (t + 1) (p + 1) n
    rw [ih]
    rfl

theorem rowAt_add (t : Nat) : ∀ (m n : Nat) (p : Int),
    rowAt t p (m + n) = rowAt t p m ++ rowAt t (p + m) n
  | 0, n, p => by simp [rowAt]
  | m + 1, n, p => by
    rw [show m + 1 + n = (m + n) + 1 by omega]
    show cell t p :: rowAt t (p + 1) (m + n) = cell t p :: (rowAt t (p + 1) m ++ _)
    rw [rowAt_add t m n (p + 1),
      show p + 1 + (m : Int) = p + ((m + 1 : Nat) : Int) by push_cast; omega]

theorem getD_rowAt (t : Nat) : ∀ (n : Nat) (p : Int) (i : Nat), i < n →
    (rowAt t p n).getD i false = cell t (p + i)
  | 0, _, _, h => by omega
  | n + 1, p, 0, _ => by simp [rowAt]
  | n + 1, p, i + 1, h => by
    show (rowAt t (p + 1) n).getD i false = _
    rw [getD_rowAt t n (p + 1) i (by omega)]
    congr 1; push_cast; omega

/-- One step on the row of positions `-t, …, t`, giving positions `-(t+1), …, t+1`. -/
def next (r : List Bool) : List Bool := stepRow false (false :: r ++ [false, false])

/-- The row of positions `-t, …, t` at time `t`, computed step by step. -/
def rowL : Nat → List Bool
  | 0 => [true]
  | t + 1 => next (rowL t)

theorem rowL_eq : ∀ t : Nat, rowL t = rowAt t (-(t : Int)) (2 * t + 1)
  | 0 => rfl
  | t + 1 => by
    show next (rowL t) = _
    rw [rowL_eq t]
    unfold next
    have hl : cell t (-(t : Int) - 1) = false := cell_eq_false_of_lt t _ (by omega)
    have hl2 : cell t (-(t : Int) - 1 - 1) = false := cell_eq_false_of_lt t _ (by omega)
    have hr1 : cell t ((t : Int) + 1) = false := cell_eq_false_of_gt' t _ (by omega)
    have hr2 : cell t ((t : Int) + 2) = false := cell_eq_false_of_gt' t _ (by omega)
    have e : false :: rowAt t (-(t : Int)) (2 * t + 1) ++ [false, false]
        = rowAt t (-(t : Int) - 1) ((2 * t + 3) + 1) := by
      rw [show (2 * t + 3) + 1 = 1 + ((2 * t + 1) + 2) by omega,
        rowAt_add t 1 ((2 * t + 1) + 2) (-(t : Int) - 1)]
      rw [rowAt_add t (2 * t + 1) 2 (-(t : Int) - 1 + ((1 : Nat) : Int))]
      have e1 : rowAt t (-(t : Int) - 1) 1 = [false] := by simp [rowAt, hl]
      have e2 : -(t : Int) - 1 + ((1 : Nat) : Int) = -(t : Int) := by push_cast; omega
      have e3 : -(t : Int) + (((2 * t + 1 : Nat)) : Int) = (t : Int) + 1 := by push_cast; omega
      have e4 : rowAt t ((t : Int) + 1) 2 = [false, false] := by
        simp [rowAt, hr1, show (t : Int) + 1 + 1 = (t : Int) + 2 by omega, hr2]
      rw [e1, e2, e3, e4]
      rfl
    rw [e, ← hl2, stepRow_rowAt]
    congr 1
    · push_cast; omega

/-- The window `x_t[-1, 2]` read from the row of positions `-t, …, t`. -/
def xw (r : List Bool) (t : Nat) : Fin 4 → Bool := fun j => r.getD (t - 1 + j.val) false

/-- The state `x_t[-7, 8]` read from the row of positions `-t, …, t`. -/
def sw (r : List Bool) (t : Nat) : Fin 16 → Bool := fun m => r.getD (t - 7 + m.val) false

theorem xw_rowL (t : Nat) (ht : 2 ≤ t) : xw (rowL t) t = Xt t := by
  funext j
  unfold xw Xt
  rw [rowL_eq, getD_rowAt t _ _ _ (by omega)]
  congr 1; omega

theorem sw_rowL (t : Nat) (ht : 8 ≤ t) : sw (rowL t) t = St t := by
  funext m
  unfold sw St
  rw [rowL_eq, getD_rowAt t _ _ _ (by omega)]
  congr 1; omega

/-- The target test `w = 1001`, as a Boolean. -/
def isTarget (w : Fin 4 → Bool) : Bool := w 0 && !w 1 && !w 2 && w 3

theorem a_eq (w : Fin 4 → Bool) : a w = if isTarget w = true then 1 else 0 := by
  have key : ∀ b0 b1 b2 b3 : Bool,
      (![b0, b1, b2, b3] = ![true, false, false, true] ↔ (b0 && !b1 && !b2 && b3) = true) := by
    decide
  unfold a isTarget
  rw [word_eq w]
  simp only [key]
  rfl

/-- The number of target times among `t, …, t + n - 1`, computed step by step from the row `r`
at time `t`. -/
def targetCount (r : List Bool) (t : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (if isTarget (xw r t) then 1 else 0) + targetCount (next r) (t + 1) n

/-- `Σ_{i < n} f (t + i)` in `ℚ`. -/
def qsum (f : Nat → ℚ) (t : Nat) : Nat → ℚ
  | 0 => 0
  | n + 1 => f t + qsum f (t + 1) n

theorem targetCount_eq : ∀ (n t : Nat), 2 ≤ t →
    (targetCount (rowL t) t n : ℚ) = qsum (fun s => a (Xt s)) t n
  | 0, t, _ => by simp [targetCount, qsum]
  | n + 1, t, ht => by
    have ih := targetCount_eq n (t + 1) (by omega)
    show (((if isTarget (xw (rowL t) t) then 1 else 0) + targetCount (rowL (t + 1)) (t + 1) n : Nat)
      : ℚ) = a (Xt t) + qsum _ (t + 1) n
    rw [Nat.cast_add, ih, xw_rowL t ht, a_eq]
    cases isTarget (Xt t) <;> simp

/-- An exact coboundary telescopes. -/
theorem qsum_telescope (φ : (Fin 16 → Bool) → ℚ) (h : ∀ t, a (Xt t) = φ (St (t + 1)) - φ (St t)) :
    ∀ n t, qsum (fun s => a (Xt s)) t n = φ (St (t + n)) - φ (St t)
  | 0, t => by simp [qsum]
  | n + 1, t => by
    show a (Xt t) + qsum _ (t + 1) n = _
    rw [qsum_telescope φ h n (t + 1), h t, show t + 1 + n = t + (n + 1) by omega]
    ring

/-- The state `x_t[-7, 8]` as a list, read from the row of positions `-t, …, t`. -/
def swList (r : List Bool) (t : Nat) : List Bool :=
  (List.range 16).map (fun i => r.getD (t - 7 + i) false)

/-- Kernel computation: the states at times `97` and `143` agree. -/
theorem orbit_return_list : swList (rowL 97) 97 = swList (rowL 143) 143 := by decide +kernel

/-- Kernel computation: `1001` occurs exactly twice among the windows at times `97, …, 142`. -/
theorem orbit_count : targetCount (rowL 97) 97 46 = 2 := by decide +kernel

/-- `S_97 = S_143` on the single-seed pattern. -/
theorem state_97_eq_143 : St 97 = St 143 := by
  rw [← sw_rowL 97 (by omega), ← sw_rowL 143 (by omega)]
  funext m
  have h := congrArg (fun l => l.getD m.val false) orbit_return_list
  simpa [swList, sw, List.getD_eq_getElem?_getD, m.isLt] using h

/-- **No exact coboundary.** On the single-seed pattern, the target indicator
`a_t = [x_t[-1, 2] = 1001]` is not of the form `φ (S_(t+1)) - φ (S_t)` for any rational function
`φ` of the sixteen-cell state `S_t = x_t[-7, 8]`: summing from `t = 97` to `142` gives `2` on the
left and `φ (S_143) - φ (S_97) = 0` on the right. -/
theorem no_exact_coboundary :
    ¬ ∃ φ : (Fin 16 → Bool) → ℚ, ∀ t, a (Xt t) = φ (St (t + 1)) - φ (St t) := by
  intro ⟨φ, h⟩
  have h1 := qsum_telescope φ h 46 97
  rw [← targetCount_eq 46 97 (by omega), orbit_count, show 97 + 46 = 143 from rfl,
    ← state_97_eq_143] at h1
  norm_num at h1

end Rule30Equivalents.WordCertificates
