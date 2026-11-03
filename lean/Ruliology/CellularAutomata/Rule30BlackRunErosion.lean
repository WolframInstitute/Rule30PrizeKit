module

public import Ruliology.CellularAutomata.Rule30CenterRuns

/-!
# Rule30BlackRunErosion

Black center runs force alternating rows whose two-step erosion strengthens the linear run bound.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30BlackRunErosion

open Ruliology.CellularAutomata
open Rule30Jen Rule30Prize Rule30Diagonals Rule30CenterRuns

def alt (i : Int) : Bool := decide (i % 2 = 0)

theorem alt_pred (i : Int) : alt (i - 1) = !alt i := by
  unfold alt
  by_cases h : i % 2 = 0
  · rw [decide_eq_true h, decide_eq_false (by omega)]; rfl
  · rw [decide_eq_false h, decide_eq_true (by omega)]; rfl

theorem alt_neg (k : Nat) : alt (-(k : Int)) = ev k := by
  unfold alt ev
  by_cases h : k % 2 = 0
  · rw [decide_eq_true h, decide_eq_true (by omega)]
  · rw [decide_eq_false h, decide_eq_false (by omega)]

theorem pat_left (f : Int → Bool) (hf : ∀ i, f (i - 1) = !f i) {t : Nat} {i : Int} (hb : cell (t + 1) i = f i)
    (h0 : cell t i = f i) (h1 : cell t (i + 1) = f (i + 1)) :
    cell t (i - 1) = f (i - 1) := by
  have p : f (i + 1) = !f i := by
    have := hf (i + 1)
    rw [show i + 1 - 1 = i by omega] at this
    rw [this]; cases f (i + 1) <;> rfl
  rw [cell_left, hb, h0, h1, p, hf]
  cases f i <;> rfl

theorem erode_step_pat (f : Int → Bool) (hf : ∀ i, f (i - 1) = !f i) (t : Nat) (lo hi : Int)
    (h : ∀ i, lo ≤ i → i ≤ hi → cell (t + 1) i = f i) :
    ∀ i, lo - 1 ≤ i → i ≤ hi - 4 → cell t i = f i := by
  intro i hi1 hi2
  have p1 : f (hi - 1) = !f hi := hf hi
  have p2 : f (hi - 2) = f hi := by
    have := hf (hi - 1)
    rw [show hi - 1 - 1 = hi - 2 by omega, p1] at this
    rw [this]; cases f hi <;> rfl
  have p3 : f (hi - 3) = !f hi := by
    have := hf (hi - 2)
    rw [show hi - 2 - 1 = hi - 3 by omega, p2] at this
    exact this
  have p4 : f (hi - 4) = f hi := by
    have := hf (hi - 3)
    rw [show hi - 3 - 1 = hi - 4 by omega, p3] at this
    rw [this]; cases f hi <;> rfl
  have p5 : f (hi - 5) = !f hi := by
    have := hf (hi - 4)
    rw [show hi - 4 - 1 = hi - 5 by omega, p4] at this
    exact this
  have q0 : cell t (hi - 1) = xor (f hi) (cell t hi || cell t (hi + 1)) := by
    have := cell_left t hi
    rw [h hi (by omega) (Int.le_refl _)] at this
    exact this
  have q1 : cell t (hi - 2) = xor (f (hi - 1)) (cell t (hi - 1) || cell t hi) := by
    have := cell_left t (hi - 1)
    rw [h (hi - 1) (by omega) (by omega), show hi - 1 - 1 = hi - 2 by omega,
      show hi - 1 + 1 = hi by omega] at this
    exact this
  have q2 : cell t (hi - 3) = xor (f (hi - 2)) (cell t (hi - 2) || cell t (hi - 1)) := by
    have := cell_left t (hi - 2)
    rw [h (hi - 2) (by omega) (by omega), show hi - 2 - 1 = hi - 3 by omega,
      show hi - 2 + 1 = hi - 1 by omega] at this
    exact this
  have q3 : cell t (hi - 4) = xor (f (hi - 3)) (cell t (hi - 3) || cell t (hi - 2)) := by
    have := cell_left t (hi - 3)
    rw [h (hi - 3) (by omega) (by omega), show hi - 3 - 1 = hi - 4 by omega,
      show hi - 3 + 1 = hi - 2 by omega] at this
    exact this
  have b4 : cell t (hi - 4) = f (hi - 4) := by
    rw [q3, q2, q1, q0, p1, p2, p3, p4]
    generalize f hi = A; generalize cell t hi = v; generalize cell t (hi + 1) = u
    cases A <;> cases v <;> cases u <;> rfl
  by_cases hi4 : i = hi - 4
  · rw [hi4]; exact b4
  have q4 : cell t (hi - 5) = xor (f (hi - 4)) (cell t (hi - 4) || cell t (hi - 3)) := by
    have := cell_left t (hi - 4)
    rw [h (hi - 4) (by omega) (by omega), show hi - 4 - 1 = hi - 5 by omega,
      show hi - 4 + 1 = hi - 3 by omega] at this
    exact this
  have b5 : cell t (hi - 5) = f (hi - 5) := by
    rw [q4, q3, q2, q1, q0, p1, p2, p3, p4, p5]
    generalize f hi = A; generalize cell t hi = v; generalize cell t (hi + 1) = u
    cases A <;> cases v <;> cases u <;> rfl
  have H : ∀ n : Nat, lo - 1 ≤ hi - 5 - n →
      cell t (hi - 5 - n) = f (hi - 5 - n) ∧ cell t (hi - 4 - n) = f (hi - 4 - n) := by
    intro n
    induction n with
    | zero => intro _; exact ⟨by simpa using b5, by simpa using b4⟩
    | succ n ih =>
      intro hn
      obtain ⟨hA, hB⟩ := ih (by omega)
      have hb := h (hi - 5 - n) (by omega) (by omega)
      have := pat_left f hf hb hA (by rw [show hi - 5 - (n : Int) + 1 = hi - 4 - n by omega]; exact hB)
      rw [show hi - 5 - (n : Int) - 1 = hi - 5 - ((n + 1 : Nat) : Int) by omega] at this
      refine ⟨this, ?_⟩
      rw [show hi - 4 - ((n + 1 : Nat) : Int) = hi - 5 - (n : Int) by omega]; exact hA
  have := (H (hi - 5 - i).toNat (by omega)).1
  rwa [show hi - 5 - ((hi - 5 - i).toNat : Int) = i by omega] at this

theorem alt_left {t : Nat} {i : Int} (hb : cell (t + 1) i = alt i)
    (h0 : cell t i = alt i) (h1 : cell t (i + 1) = alt (i + 1)) :
    cell t (i - 1) = alt (i - 1) := pat_left alt alt_pred hb h0 h1

theorem erode_step (t : Nat) (lo hi : Int)
    (h : ∀ i, lo ≤ i → i ≤ hi → cell (t + 1) i = alt i) :
    ∀ i, lo - 1 ≤ i → i ≤ hi - 4 → cell t i = alt i := erode_step_pat alt alt_pred t lo hi h

theorem black_block_back (a L : Nat) (h : ∀ i, i < L → cell (a + i) 0 = true) :
    ∀ s, s ≤ a → ∀ i : Int, -((L : Int) - 1) - s ≤ i → i ≤ -4 * (s : Int) →
      cell (a - s) i = alt i := by
  intro s
  induction s with
  | zero =>
    intro _ i hi1 hi2
    have := black_triangle a L h (-i).toNat a (Nat.le_refl a) (by omega)
    rw [show (a - 0) = a by omega, show i = -(((-i).toNat : Nat) : Int) by omega, this, alt_neg]
  | succ s ih =>
    intro hs i hi1 hi2
    have ih' := ih (by omega)
    have := erode_step (a - (s + 1)) (-((L : Int) - 1) - s) (-4 * (s : Int))
      (fun j hj1 hj2 => by
        rw [show a - (s + 1) + 1 = a - s by omega]; exact ih' j hj1 hj2) i (by omega) (by omega)
    exact this

theorem black_run_le_erosion (a L : Nat) (ha : 1 ≤ a) (h : ∀ i, i < L → center (a + i) = true) :
    L + 2 * ((a - 1) / 5) ≤ a := by
  refine Classical.byContradiction fun hcon => ?_
  have h' : ∀ i, i < L → cell (a + i) 0 = true := h
  obtain ⟨s, hs⟩ : ∃ s, s = (a - 1) / 5 := ⟨_, rfl⟩
  have h5 : 5 * s ≤ a - 1 := by omega
  have hb := black_block_back a L h' s (by omega)
  have hτ : 1 ≤ a - s := by omega
  have c1 := hb (-((a - s : Nat) : Int)) (by omega) (by omega)
  have c2 := hb (-((a - s : Nat) : Int) + 1) (by omega) (by omega)
  rw [cell_left_edge] at c1
  have hD : D 1 (a - s) = true := by
    obtain ⟨u, hu⟩ : ∃ u, a - s = u + 1 := ⟨a - s - 1, by omega⟩
    rw [hu]; exact D_one u
  have e : cell (a - s) (-((a - s : Nat) : Int) + 1) = D 1 (a - s) := cell_congr (by omega)
  rw [e, hD] at c2
  have := alt_pred (-((a - s : Nat) : Int) + 1)
  rw [show -((a - s : Nat) : Int) + 1 - 1 = -((a - s : Nat) : Int) by omega, ← c1, ← c2] at this
  exact Bool.noConfusion this

theorem exists_white_erosion (a : Nat) (ha : 1 ≤ a) :
    ∃ t, a ≤ t ∧ t ≤ 2 * a - 2 * ((a - 1) / 5) ∧ center t = false := by
  refine Classical.byContradiction fun hcon => ?_
  have hall : ∀ i, i < a - 2 * ((a - 1) / 5) + 1 → center (a + i) = true := by
    intro i hi
    cases hc : center (a + i)
    · exact absurd ⟨a + i, by omega, by omega, hc⟩ hcon
    · rfl
  have := black_run_le_erosion a (a - 2 * ((a - 1) / 5) + 1) ha hall
  omega

def nalt (i : Int) : Bool := !alt i

theorem nalt_pred (i : Int) : nalt (i - 1) = !nalt i := by
  unfold nalt; rw [alt_pred]

theorem white_block_back (a L ℓ : Nat) (h0 : ∀ i, i < L → cell (a + i) 0 = false)
    (hw : ∀ p : Nat, 1 ≤ p → p ≤ ℓ → cell a p = false) (hb : cell a ((ℓ + 1 : Nat) : Int) = true) :
    ∀ s, s ≤ a → ∀ i : Int, -((L : Int) - 1) - s ≤ i → i ≤ -((ℓ : Int) + 2) - 4 * (s : Int) →
      cell (a - s) i = nalt i := by
  intro s
  induction s with
  | zero =>
    intro _ i hi1 hi2
    have := pre_triangle a ℓ L h0 (col_one a ℓ L h0 hw hb) (-i).toNat a (Nat.le_refl a) (by omega)
    rw [show (a - 0) = a by omega, show i = -(((-i).toNat : Nat) : Int) by omega, this,
      show a + ℓ - a = ℓ by omega]
    unfold preRow nalt alt
    by_cases hk : (-i).toNat % 2 = 0
    · rw [decide_eq_false (by omega), decide_eq_true (by omega)]; rfl
    · rw [decide_eq_true (by omega), decide_eq_false (by omega)]; rfl
  | succ s ih =>
    intro hs i hi1 hi2
    have ih' := ih (by omega)
    exact erode_step_pat nalt nalt_pred (a - (s + 1)) (-((L : Int) - 1) - s)
      (-((ℓ : Int) + 2) - 4 * (s : Int))
      (fun j hj1 hj2 => by
        rw [show a - (s + 1) + 1 = a - s by omega]; exact ih' j hj1 hj2) i (by omega) (by omega)

theorem white_run_le_erosion (a L ℓ : Nat) (h : ∀ i, i < L → center (a + i) = false)
    (hw : ∀ p : Nat, 1 ≤ p → p ≤ ℓ → cell a p = false) (hb : cell a ((ℓ + 1 : Nat) : Int) = true)
    (s : Nat) (hs : 5 * s + ℓ + 3 ≤ a) : L + 2 * s ≤ a := by
  refine Classical.byContradiction fun hcon => ?_
  have h' : ∀ i, i < L → cell (a + i) 0 = false := h
  have hbk := white_block_back a L ℓ h' hw hb s (by omega)
  have c1 := hbk (-((a - s : Nat) : Int)) (by omega) (by omega)
  have c2 := hbk (-((a - s : Nat) : Int) + 1) (by omega) (by omega)
  rw [cell_left_edge] at c1
  have hD : D 1 (a - s) = true := by
    obtain ⟨u, hu⟩ : ∃ u, a - s = u + 1 := ⟨a - s - 1, by omega⟩
    rw [hu]; exact D_one u
  have e : cell (a - s) (-((a - s : Nat) : Int) + 1) = D 1 (a - s) := cell_congr (by omega)
  rw [e, hD] at c2
  have := nalt_pred (-((a - s : Nat) : Int) + 1)
  rw [show -((a - s : Nat) : Int) + 1 - 1 = -((a - s : Nat) : Int) by omega, ← c1, ← c2] at this
  exact Bool.noConfusion this

/-! ### Parity-Resolved `D 0`/`D 1` Boundary Collisions and Strengthened Erosion Bounds -/

/-- **Parity of `alt` at `-((k : Nat) : Int) + 1` (`alt_neg_add_one`):** for every `k : Nat`,
`alt (-((k : Nat) : Int) + 1) = !ev k`. -/
theorem alt_neg_add_one (k : Nat) : alt (-((k : Nat) : Int) + 1) = !ev k := by
  have h := alt_pred (-((k : Nat) : Int) + 1)
  rw [show -((k : Nat) : Int) + 1 - 1 = -((k : Nat) : Int) by omega, alt_neg] at h
  rw [← Bool.not_not (alt (-((k : Nat) : Int) + 1)), h]

/-- **Single-Point Left-Edge (`D 0`) Collision for Black Center Runs (`black_block_back_left_edge_even`):**
if a black center run of length `L` starts at `a`, `5 * s ≤ a`, and `a < L + 2 * s`, then the left
boundary `cell (a - s) (-(a - s)) = true` forces `(a - s) % 2 = 0`. -/
theorem black_block_back_left_edge_even {a L s : Nat}
    (h : ∀ i, i < L → center (a + i) = true)
    (hs : 5 * s ≤ a) (hL : a < L + 2 * s) :
    (a - s) % 2 = 0 := by
  have h' : ∀ i, i < L → cell (a + i) 0 = true := h
  have hb := black_block_back a L h' s (by omega) (-((a - s : Nat) : Int)) (by omega) (by omega)
  rw [cell_left_edge, alt_neg] at hb
  unfold ev at hb
  by_cases hmod : (a - s) % 2 = 0
  · exact hmod
  · rw [decide_eq_false hmod] at hb
    exact Bool.noConfusion hb

/-- **Single-Point `D 1` Collision for Black Center Runs (`black_block_back_D_one_odd`):**
if a black center run of length `L` starts at `a`, `5 * s + 1 ≤ a`, and `a < L + 2 * s`, then the
first inner diagonal `D 1 (a - s) = true` forces `(a - s) % 2 = 1`. -/
theorem black_block_back_D_one_odd {a L s : Nat}
    (h : ∀ i, i < L → center (a + i) = true)
    (hs : 5 * s + 1 ≤ a) (hL : a < L + 2 * s) :
    (a - s) % 2 = 1 := by
  have h' : ∀ i, i < L → cell (a + i) 0 = true := h
  have hb := black_block_back a L h' s (by omega) (-((a - s : Nat) : Int) + 1) (by omega) (by omega)
  have hD : D 1 (a - s) = true := by
    obtain ⟨u, hu⟩ : ∃ u, a - s = u + 1 := ⟨a - s - 1, by omega⟩
    rw [hu]; exact D_one u
  have e : cell (a - s) (-((a - s : Nat) : Int) + 1) = D 1 (a - s) := cell_congr (by omega)
  rw [e, hD, alt_neg_add_one] at hb
  unfold ev at hb
  by_cases hmod : (a - s) % 2 = 0
  · rw [decide_eq_true hmod] at hb
    exact Bool.noConfusion hb
  · omega

/-- **Single-Point Left-Edge Black-Run Erosion under Odd `(a - s)` (`black_run_le_erosion_of_odd_diff`):**
if `5 * s ≤ a` and `(a - s) % 2 = 1`, then `L + 2 * s ≤ a` holds from the left edge `D 0` alone. -/
theorem black_run_le_erosion_of_odd_diff (a L s : Nat)
    (h : ∀ i, i < L → center (a + i) = true)
    (hs : 5 * s ≤ a) (hodd : (a - s) % 2 = 1) :
    L + 2 * s ≤ a := by
  refine Classical.byContradiction fun hcon => ?_
  have heven := black_block_back_left_edge_even h hs (by omega)
  omega

/-- **Exact Remainder Form of the Linear Black-Run Erosion Bound (`five_mul_black_run_le_exact_mod`):**
for every `a ≥ 1` and `L : Nat`, if `center (a + i) = true` for all `i < L`, then
`5 * L ≤ 3 * a + 2 * ((a - 1) % 5) + 2`. -/
theorem five_mul_black_run_le_exact_mod (a L : Nat) (ha : 1 ≤ a)
    (h : ∀ i, i < L → center (a + i) = true) :
    5 * L ≤ 3 * a + 2 * ((a - 1) % 5) + 2 := by
  have hb := black_run_le_erosion a L ha h
  omega

/-- **Sharp `5 * L ≤ 3 * a + 2` Black-Run Bound when `a % 5 = 1` (`five_mul_black_run_le_of_mod_one`):**
whenever `1 ≤ a` and `a % 5 = 1`, any black center run of length `L` starting at `a` satisfies
`5 * L ≤ 3 * a + 2`. -/
theorem five_mul_black_run_le_of_mod_one (a L : Nat) (ha : 1 ≤ a) (hmod : a % 5 = 1)
    (h : ∀ i, i < L → center (a + i) = true) :
    5 * L ≤ 3 * a + 2 := by
  have hb := five_mul_black_run_le_exact_mod a L ha h
  omega

/-- **Single-Point Left-Edge (`D 0`) Collision for White Center Runs (`white_block_back_left_edge_odd`):**
under the hypotheses of `white_block_back`, if `5 * s + ℓ + 2 ≤ a` and `a < L + 2 * s`, then the
left boundary `cell (a - s) (-(a - s)) = true` forces `(a - s) % 2 = 1`. -/
theorem white_block_back_left_edge_odd {a L ℓ s : Nat}
    (h : ∀ i, i < L → center (a + i) = false)
    (hw : ∀ p : Nat, 1 ≤ p → p ≤ ℓ → cell a p = false)
    (hb : cell a ((ℓ + 1 : Nat) : Int) = true)
    (hs : 5 * s + ℓ + 2 ≤ a) (hL : a < L + 2 * s) :
    (a - s) % 2 = 1 := by
  have h' : ∀ i, i < L → cell (a + i) 0 = false := h
  have hbk := white_block_back a L ℓ h' hw hb s (by omega) (-((a - s : Nat) : Int)) (by omega) (by omega)
  rw [cell_left_edge] at hbk
  unfold nalt at hbk
  rw [alt_neg] at hbk
  unfold ev at hbk
  by_cases hmod : (a - s) % 2 = 0
  · rw [decide_eq_true hmod] at hbk
    exact Bool.noConfusion hbk
  · omega

/-- **Single-Point `D 1` Collision for White Center Runs (`white_block_back_D_one_even`):**
under the hypotheses of `white_block_back`, if `5 * s + ℓ + 3 ≤ a` and `a < L + 2 * s`, then the
first inner diagonal `D 1 (a - s) = true` forces `(a - s) % 2 = 0`. -/
theorem white_block_back_D_one_even {a L ℓ s : Nat}
    (h : ∀ i, i < L → center (a + i) = false)
    (hw : ∀ p : Nat, 1 ≤ p → p ≤ ℓ → cell a p = false)
    (hb : cell a ((ℓ + 1 : Nat) : Int) = true)
    (hs : 5 * s + ℓ + 3 ≤ a) (hL : a < L + 2 * s) :
    (a - s) % 2 = 0 := by
  have h' : ∀ i, i < L → cell (a + i) 0 = false := h
  have hbk := white_block_back a L ℓ h' hw hb s (by omega) (-((a - s : Nat) : Int) + 1) (by omega) (by omega)
  have hD : D 1 (a - s) = true := by
    obtain ⟨u, hu⟩ : ∃ u, a - s = u + 1 := ⟨a - s - 1, by omega⟩
    rw [hu]; exact D_one u
  have e : cell (a - s) (-((a - s : Nat) : Int) + 1) = D 1 (a - s) := cell_congr (by omega)
  rw [e, hD] at hbk
  unfold nalt at hbk
  rw [alt_neg_add_one, Bool.not_not] at hbk
  exact of_decide_eq_true hbk.symm

/-- **Parity-Sharpened White-Run Erosion Bound (`white_run_le_erosion_of_even_diff`):** if
`5 * s + ℓ + 2 ≤ a` and `(a - s) % 2 = 0`, then `L + 2 * s ≤ a` holds with threshold
`5 * s + ℓ + 2 ≤ a` (one step earlier than `white_run_le_erosion`). -/
theorem white_run_le_erosion_of_even_diff (a L ℓ : Nat)
    (h : ∀ i, i < L → center (a + i) = false)
    (hw : ∀ p : Nat, 1 ≤ p → p ≤ ℓ → cell a p = false)
    (hb : cell a ((ℓ + 1 : Nat) : Int) = true)
    (s : Nat) (hs : 5 * s + ℓ + 2 ≤ a) (heven : (a - s) % 2 = 0) :
    L + 2 * s ≤ a := by
  refine Classical.byContradiction fun hcon => ?_
  have hodd := white_block_back_left_edge_odd h hw hb hs (by omega)
  omega

/-- **Strengthened White-Run Erosion Bound for Even `ℓ` (`white_run_le_erosion_of_even_ell`):**
whenever `ℓ % 2 = 0` and `5 * s + ℓ + 2 ≤ a`, a white center run of length `L` starting at `a`
satisfies `L + 2 * s ≤ a` (improving `white_run_le_erosion` from `5 * s + ℓ + 3 ≤ a` to
`5 * s + ℓ + 2 ≤ a` for every even `ℓ`). -/
theorem white_run_le_erosion_of_even_ell (a L ℓ : Nat)
    (h : ∀ i, i < L → center (a + i) = false)
    (hw : ∀ p : Nat, 1 ≤ p → p ≤ ℓ → cell a p = false)
    (hb : cell a ((ℓ + 1 : Nat) : Int) = true)
    (hℓ_even : ℓ % 2 = 0) (s : Nat) (hs : 5 * s + ℓ + 2 ≤ a) :
    L + 2 * s ≤ a := by
  by_cases hs3 : 5 * s + ℓ + 3 ≤ a
  · exact white_run_le_erosion a L ℓ h hw hb s hs3
  · have ha_eq : a = 5 * s + ℓ + 2 := by omega
    exact white_run_le_erosion_of_even_diff a L ℓ h hw hb s hs (by omega)

/-- **Closed-Form Division Bound for White-Run Erosion (`white_run_le_erosion_div`):** if
`ℓ + 3 ≤ a`, then `L + 2 * ((a - ℓ - 3) / 5) ≤ a`, and if `ℓ % 2 = 0` with `ℓ + 2 ≤ a`, then
`L + 2 * ((a - ℓ - 2) / 5) ≤ a`. -/
theorem white_run_le_erosion_div (a L ℓ : Nat)
    (h : ∀ i, i < L → center (a + i) = false)
    (hw : ∀ p : Nat, 1 ≤ p → p ≤ ℓ → cell a p = false)
    (hb : cell a ((ℓ + 1 : Nat) : Int) = true) :
    (ℓ + 3 ≤ a → L + 2 * ((a - ℓ - 3) / 5) ≤ a) ∧
    (ℓ % 2 = 0 → ℓ + 2 ≤ a → L + 2 * ((a - ℓ - 2) / 5) ≤ a) :=
  ⟨fun h3 => white_run_le_erosion a L ℓ h hw hb ((a - ℓ - 3) / 5) (by omega),
   fun hev h2 => white_run_le_erosion_of_even_ell a L ℓ h hw hb hev ((a - ℓ - 2) / 5) (by omega)⟩

end Ruliology.CellularAutomata.Rule30BlackRunErosion
