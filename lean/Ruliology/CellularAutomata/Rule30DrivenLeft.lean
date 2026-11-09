module

public import Ruliology.CellularAutomata.Rule30MaskedJen

/-!
# Rule 30: the left half driven by a boundary column

Fix any boundary column `c` at position `0` and any start `s` of the left half (positions
`p < 0`). Running rule 30 on `p < 0` with `c` as the right neighbour of `-1` gives the **driven
left half** `L c s t p` (`L c s t 0 = c t`). The real pattern is such a half from every time `T`
on: driven by the real center column (`cell_eq_L`), or, by the effective boundary of
`Rule30MaskedJen`, by `c' k = c (T + k) && c (T + k + 1)` (`cell_eq_L_effective`).

**Driven-left Jen.** Let the start `s` be finite and nonzero on the left: its leftmost black
cell is at `-m`, `m ≥ 1`, and everything further left is white.
* `edge`: the leftmost black cell of `L c s t` is at `-(m + t)`, whatever the driver.
* `no_periodic_adjacent`: two adjacent columns `i, i + 1` with `i + 1 ≤ 0` are never both
  eventually periodic.
* `col_neg_one_not_periodic`, `no_periodic_column`: **if the driver is eventually periodic, no
  column `q < 0` of the driven left half is eventually periodic.** So the left half has no
  absorbing words: whatever the start, an eventually periodic driver never makes a column of the
  left half eventually periodic. The absorbing-word route to a contradiction with Jen's theorem
  (used on the right half in `Rule30BlackRuns` and `Rule30StripCertificates`) is closed on the
  left.

**The barrier.** Column `-1` of the driven left half encodes the start.
* `light_cone`, `permutive`: column `-1` at step `k` depends only on the start cells
  `-1, …, -(k + 1)`, and flipping cell `-(k + 1)` flips it.
* `barrier_exists`, `barrier_unique`: **for every driver, every `n ≥ 1` and every target
  `b : Nat → Bool`, exactly one start with leftmost black cell at `-n` (white beyond) has column
  `-1` equal to `b` at steps `0, …, n - 2`.** A left-half argument that starts at time `T` (where
  the real left edge is at `-T`) must therefore look at column `-1` past step `T - 2`: any
  constraint on the window before that is met by some start.
* `ones_fails`: with the driver `c ≡ 1`, every start with leftmost black cell at `-n` makes
  column `-1` black at some step `≤ n + 1`. (Column `-1` white at every step is what an eventually
  black center column would force, since a black center cell makes column `-1` the negation of
  the next center cell.)

Source: E. Jen, *Global properties of cellular automata*, J. Stat. Phys. 43 (1986) 219–242; the
argument here is Jen's, run inside the half-line.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30DrivenLeft

open Rule30Jen Rule30Prize Rule30MaskedJen

/-- The left half driven by the boundary column `c`, from left-half state `s` at time `0`. -/
def L (c : Nat → Bool) (s : Int → Bool) : Nat → Int → Bool
  | 0, p => if p < 0 then s p else c 0
  | t + 1, p => if p < 0 then rule (L c s t (p - 1)) (L c s t p) (L c s t (p + 1)) else c (t + 1)

section Driven

variable {c : Nat → Bool} {s : Int → Bool}

theorem L_col0 (t : Nat) : L c s t 0 = c t := by
  cases t <;> simp [L]

theorem L_succ {t : Nat} {p : Int} (hp : p < 0) :
    L c s (t + 1) p = rule (L c s t (p - 1)) (L c s t p) (L c s t (p + 1)) := by
  simp [L, hp]

theorem L_zero {p : Int} (hp : p < 0) : L c s 0 p = s p := by
  simp [L, hp]

/-- Left permutivity inside the driven half (needs `p < 0`; at `p = 0` this is exactly the
consistency condition, which the driven half does not impose). -/
theorem L_left (t : Nat) {p : Int} (hp : p < 0) :
    L c s t (p - 1) = xor (L c s (t + 1) p) (L c s t p || L c s t (p + 1)) := by
  rw [L_succ hp]
  show L c s t (p - 1) = xor (xor (L c s t (p - 1)) (L c s t p || L c s t (p + 1)))
    (L c s t p || L c s t (p + 1))
  cases L c s t (p - 1) <;> cases L c s t p <;> cases L c s t (p + 1) <;> rfl

/-- The left edge moves left one cell per step. -/
theorem edge {m : Nat} (hs0 : ∀ p : Int, p < -(m : Int) → s p = false) (hs1 : s (-(m : Int)) = true)
    (hm : 0 < m) :
    ∀ t : Nat, (∀ p : Int, p < -((m + t : Nat) : Int) → L c s t p = false) ∧
      L c s t (-((m + t : Nat) : Int)) = true := by
  intro t
  induction t with
  | zero =>
    refine ⟨fun p hp => ?_, ?_⟩
    · rw [L_zero (by omega)]; exact hs0 p (by omega)
    · rw [L_zero (by omega)]; simpa using hs1
  | succ t ih =>
    refine ⟨fun p hp => ?_, ?_⟩
    · rw [L_succ (by omega), ih.1 (p - 1) (by omega), ih.1 p (by omega), ih.1 (p + 1) (by omega)]
      rfl
    · rw [L_succ (by omega), ih.1 _ (by omega), ih.1 _ (by omega),
        show -(((m + (t + 1) : Nat)) : Int) + 1 = -((m + t : Nat) : Int) by omega, ih.2]
      rfl

theorem periodic_left {T P : Nat} {i : Int} (hi : i < 0)
    (h0 : ∀ t, T ≤ t → L c s (t + P) i = L c s t i)
    (h1 : ∀ t, T ≤ t → L c s (t + P) (i + 1) = L c s t (i + 1)) :
    ∀ t, T ≤ t → L c s (t + P) (i - 1) = L c s t (i - 1) := by
  intro t ht
  rw [L_left _ hi, L_left t hi, show t + P + 1 = (t + 1) + P by omega, h0 (t + 1) (by omega),
    h0 t ht, h1 t ht]

/-- Two adjacent periodic columns `i, i+1` (with `i < 0`) make every column to their left periodic. -/
theorem periodic_left_all {T P : Nat} {i : Int} (hi : i < 0)
    (h0 : ∀ t, T ≤ t → L c s (t + P) i = L c s t i)
    (h1 : ∀ t, T ≤ t → L c s (t + P) (i + 1) = L c s t (i + 1)) :
    ∀ n : Nat, (∀ t, T ≤ t → L c s (t + P) (i - n) = L c s t (i - n)) ∧
      ∀ t, T ≤ t → L c s (t + P) (i - n + 1) = L c s t (i - n + 1) := by
  intro n
  induction n with
  | zero => simpa using ⟨h0, h1⟩
  | succ n ih =>
    refine ⟨?_, ?_⟩
    · have := periodic_left (by omega) ih.1 ih.2
      rwa [show i - (n : Int) - 1 = i - ((n + 1 : Nat) : Int) by omega] at this
    · rw [show i - ((n + 1 : Nat) : Int) + 1 = i - (n : Int) by omega]
      exact ih.1

/-- Far to the left, the edge reaches every column once: no column there is periodic. -/
theorem no_left_periodic {m : Nat} (hs0 : ∀ p : Int, p < -(m : Int) → s p = false)
    (hs1 : s (-(m : Int)) = true) (hm : 0 < m) {T P : Nat} (hP : 0 < P) {i : Int}
    (h : ∀ n : Nat, ∀ t, T ≤ t → L c s (t + P) (i - n) = L c s t (i - n)) : False := by
  -- a column q ≤ i with q ≤ -(m + T + P) - 1
  let q : Int := min i (-((m + T + P : Nat) : Int) - 1)
  have hq : q ≤ i := Int.min_le_left _ _
  have hq' : q ≤ -((m + T + P : Nat) : Int) - 1 := Int.min_le_right _ _
  -- the edge is at column q at time t₁ = -q - m
  obtain ⟨t₁, ht₁⟩ : ∃ t₁ : Nat, (t₁ : Int) = -q - m := ⟨(-q - m).toNat, by omega⟩
  have hper := h (i - q).toNat (t₁ - P) (by omega)
  rw [show i - (((i - q).toNat : Nat) : Int) = q by omega, show t₁ - P + P = t₁ by omega] at hper
  have hedge : L c s t₁ q = true := by
    have := (edge (c := c) hs0 hs1 hm t₁).2
    rwa [show -((m + t₁ : Nat) : Int) = q by omega] at this
  have hwhite : L c s (t₁ - P) q = false :=
    (edge (c := c) hs0 hs1 hm (t₁ - P)).1 q (by omega)
  rw [hedge, hwhite] at hper
  exact absurd hper (by decide)

/-- **Adjacent columns.** In the driven left half (finite-support nonzero start), two adjacent
columns `i, i + 1` with `i + 1 ≤ 0` are never both eventually periodic. -/
theorem no_periodic_adjacent {m : Nat} (hs0 : ∀ p : Int, p < -(m : Int) → s p = false)
    (hs1 : s (-(m : Int)) = true) (hm : 0 < m) {i : Int} (hi : i < 0)
    (h0 : EventuallyPeriodic fun t => L c s t i)
    (h1 : EventuallyPeriodic fun t => L c s t (i + 1)) : False := by
  obtain ⟨T, P, hP, hp0, hp1⟩ := common_period h0 h1
  exact no_left_periodic hs0 hs1 hm hP fun n => (periodic_left_all hi hp0 hp1 n).1

/-- **No left absorption.** If the driver `c` is eventually periodic, column `-1` of the driven
left half is not eventually periodic, whatever the (finite-support, nonzero) start state. -/
theorem col_neg_one_not_periodic {m : Nat} (hs0 : ∀ p : Int, p < -(m : Int) → s p = false)
    (hs1 : s (-(m : Int)) = true) (hm : 0 < m) (hc : EventuallyPeriodic c) :
    ¬ EventuallyPeriodic fun t => L c s t (-1) := by
  intro hx
  refine no_periodic_adjacent hs0 hs1 hm (i := -1) (by omega) hx ?_
  obtain ⟨T, P, hP, h⟩ := hc
  exact ⟨T, P, hP, fun t ht => by simp only [show (-1 : Int) + 1 = 0 by omega, L_col0]; exact h t ht⟩

/-! ### Non-adjacent columns: the strip between column `j` and column `k ≤ 0` -/

/-- The cells strictly between columns `j` and `k` at step `t`. -/
def strip (c : Nat → Bool) (s : Int → Bool) (j k : Int) (t : Nat) : List Bool :=
  (List.range (k - j - 1).toNat).map fun (r : Nat) => L c s t (j + 1 + (r : Int))

set_option linter.unusedSimpArgs false in
theorem strip_agree {j k : Int} (hjk : j < k) (hk : k ≤ 0) {t₁ t₂ : Nat}
    (hs : strip c s j k t₁ = strip c s j k t₂)
    (hb : ∀ r, L c s (t₁ + r) j = L c s (t₂ + r) j ∧ L c s (t₁ + r) k = L c s (t₂ + r) k) :
    ∀ r, ∀ i, j ≤ i → i ≤ k → L c s (t₁ + r) i = L c s (t₂ + r) i := by
  intro r
  induction r with
  | zero =>
    intro i hi1 hi2
    by_cases e1 : i = j
    · subst e1; exact (hb 0).1
    by_cases e2 : i = k
    · subst e2; exact (hb 0).2
    have := congrArg (fun l => l.getD (i - j - 1).toNat false) hs
    simp only [strip, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (show (i - j - 1).toNat < (k - j - 1).toNat by omega),
      Option.map_some, Option.getD_some] at this
    rwa [show j + 1 + (((i - j - 1).toNat : Nat) : Int) = i by omega] at this
  | succ r ih =>
    intro i hi1 hi2
    by_cases e1 : i = j
    · subst e1; exact (hb (r + 1)).1
    by_cases e2 : i = k
    · subst e2; exact (hb (r + 1)).2
    rw [show t₁ + (r + 1) = (t₁ + r) + 1 by omega, show t₂ + (r + 1) = (t₂ + r) + 1 by omega,
      L_succ (by omega), L_succ (by omega)]
    rw [ih (i - 1) (by omega) (by omega), ih i (by omega) (by omega), ih (i + 1) (by omega) (by omega)]

theorem between_periodic {j k : Int} (hjk : j + 1 < k) (hk : k ≤ 0)
    (hj : EventuallyPeriodic fun t => L c s t j) (hk' : EventuallyPeriodic fun t => L c s t k) :
    EventuallyPeriodic fun t => L c s t (j + 1) := by
  obtain ⟨T, P, hP, hpj, hpk⟩ := common_period hj hk'
  obtain ⟨m, n, hmn, -, he⟩ := pigeonhole (k - j - 1).toNat (fun m => strip c s j k (T + m * P))
    (fun m => by simp only [strip, List.length_map, List.length_range])
  refine ⟨T + m * P, (n - m) * P, Nat.mul_pos (by omega) hP, fun t ht => ?_⟩
  have key := strip_agree (by omega) hk he (fun r => ⟨?_, ?_⟩) (t - (T + m * P)) (j + 1)
    (by omega) (by omega)
  · rw [show T + m * P + (t - (T + m * P)) = t by omega,
      show T + n * P + (t - (T + m * P)) = t + (n - m) * P by
        rw [Nat.sub_mul]; have : m * P ≤ n * P := Nat.mul_le_mul_right _ (by omega); omega] at key
    exact key.symm
  · rw [show T + n * P + r = (T + m * P + r) + (n - m) * P by
      rw [Nat.sub_mul]; have : m * P ≤ n * P := Nat.mul_le_mul_right _ (by omega); omega]
    exact (periodic_mul (f := fun t => L c s t j) hpj (n - m) _ (by omega)).symm
  · rw [show T + n * P + r = (T + m * P + r) + (n - m) * P by
      rw [Nat.sub_mul]; have : m * P ≤ n * P := Nat.mul_le_mul_right _ (by omega); omega]
    exact (periodic_mul (f := fun t => L c s t k) hpk (n - m) _ (by omega)).symm

/-- **No column of the driven left half is eventually periodic** when the driver is eventually
periodic (finite-support nonzero start). -/
theorem no_periodic_column {m : Nat} (hs0 : ∀ p : Int, p < -(m : Int) → s p = false)
    (hs1 : s (-(m : Int)) = true) (hm : 0 < m) (hc : EventuallyPeriodic c) {q : Int} (hq : q < 0)
    (hcol : EventuallyPeriodic fun t => L c s t q) : False := by
  have hc' : EventuallyPeriodic fun t => L c s t 0 := by
    obtain ⟨T, P, hP, h⟩ := hc
    exact ⟨T, P, hP, fun t ht => by simp only [L_col0]; exact h t ht⟩
  by_cases hadj : q = -1
  · subst hadj
    exact no_periodic_adjacent hs0 hs1 hm (i := -1) (by omega) hcol
      (by simpa [show (-1 : Int) + 1 = 0 by omega] using hc')
  · have hnext := between_periodic (j := q) (k := 0) (by omega) (Int.le_refl _) hcol hc'
    exact no_periodic_adjacent hs0 hs1 hm (i := q) hq hcol hnext


/-! ### Bridge to the real pattern -/

/-- The real rule 30 left half from time `T` on is the left half driven by the real center
column from the real row at time `T`. -/
theorem cell_eq_L (T : Nat) : ∀ k : Nat, ∀ p : Int, p ≤ 0 →
    L (fun k => cell (T + k) 0) (fun p => cell T p) k p = cell (T + k) p := by
  intro k
  induction k with
  | zero =>
    intro p hp
    by_cases h : p < 0
    · rw [L_zero h]; rfl
    · rw [show p = 0 by omega, L_col0]
  | succ k ih =>
    intro p hp
    by_cases h : p < 0
    · rw [L_succ h, ih (p - 1) (by omega), ih p (by omega), ih (p + 1) (by omega)]
      rfl
    · rw [show p = 0 by omega, L_col0]

/-- The real left half at time `T ≥ 1` is edge-structured with edge at `-T`. -/
theorem real_edge (T : Nat) :
    (∀ p : Int, p < -((T : Nat) : Int) → cell T p = false) ∧ cell T (-((T : Nat) : Int)) = true :=
  ⟨fun p hp => cell_eq_false_of_lt T p hp, cell_left_edge T⟩

/-- **The real left half with the effective boundary.** From time `T` on, columns `p < 0` of the
real pattern are the left half driven by `c' k = c (T + k) && c (T + k + 1)` from the real row at
time `T` (`Rule30MaskedJen.effective_step`). -/
theorem cell_eq_L_effective (T : Nat) : ∀ k : Nat, ∀ p : Int, p < 0 →
    L (fun k => center (T + k) && center (T + k + 1)) (fun p => cell T p) k p =
      cell (T + k) p := by
  intro k
  induction k with
  | zero => intro p hp; rw [L_zero hp]; rfl
  | succ k ih =>
    intro p hp
    rw [L_succ hp, ih (p - 1) (by omega), ih p hp]
    by_cases h1 : p = -1
    · subst h1
      rw [show (-1 : Int) + 1 = 0 by rfl, L_col0, show T + (k + 1) = (T + k) + 1 by omega,
        effective_step (T + k), show (-1 : Int) - 1 = -2 by rfl]
    · rw [ih (p + 1) (by omega)]
      rfl

end Driven

/-! ### The barrier: column `-1` encodes the start -/

section Barrier

variable {c : Nat → Bool}

/-- Neighbour value: positions `p + 1 ≤ 0` agree if `p + 1 < 0` agrees or `p + 1 = 0` (driver). -/
theorem nb_agree {s s' : Int → Bool} {j : Nat} {p : Int} (hp : p < 0)
    (h : p + 1 < 0 → L c s j (p + 1) = L c s' j (p + 1)) : L c s j (p + 1) = L c s' j (p + 1) := by
  by_cases hq : p + 1 < 0
  · exact h hq
  · rw [show p + 1 = 0 by omega, L_col0, L_col0]

/-- **Light cone.** If two starts agree on `-(k+1) … -1`, then at step `j ≤ k` they agree on
`-(k+1-j) … -1`. -/
theorem light_cone {s s' : Int → Bool} {k : Nat}
    (h : ∀ p : Int, -((k + 1 : Nat) : Int) ≤ p → p < 0 → s p = s' p) :
    ∀ j : Nat, j ≤ k → ∀ p : Int, -((k + 1 - j : Nat) : Int) ≤ p → p < 0 →
      L c s j p = L c s' j p := by
  intro j
  induction j with
  | zero =>
    intro _ p hp1 hp2
    rw [L_zero (s := s) hp2, L_zero (s := s') hp2]
    exact h p (by omega) hp2
  | succ j ih =>
    intro hj p hp1 hp2
    rw [L_succ (s := s) hp2, L_succ (s := s') hp2, ih (by omega) (p - 1) (by omega) (by omega),
      ih (by omega) p (by omega) hp2,
      nb_agree hp2 (fun hq => ih (by omega) (p + 1) (by omega) hq)]

theorem rule_not (a b d : Bool) : rule (!a) b d = !rule a b d := by
  cases a <;> cases b <;> cases d <;> rfl

/-- **Permutivity.** If two starts agree on `-k … -1` and differ at `-(k+1)`, then at step `j ≤ k`
they agree on `-(k-j) … -1` and differ at `-(k+1-j)`. -/
theorem permutive_aux {s s' : Int → Bool} {k : Nat}
    (hag : ∀ p : Int, -((k : Nat) : Int) ≤ p → p < 0 → s p = s' p)
    (hd : s (-((k + 1 : Nat) : Int)) = !s' (-((k + 1 : Nat) : Int))) :
    ∀ j : Nat, j ≤ k → (∀ p : Int, -((k - j : Nat) : Int) ≤ p → p < 0 → L c s j p = L c s' j p) ∧
      L c s j (-((k + 1 - j : Nat) : Int)) = !L c s' j (-((k + 1 - j : Nat) : Int)) := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨fun p hp1 hp2 => ?_, ?_⟩
    · rw [L_zero (s := s) hp2, L_zero (s := s') hp2]; exact hag p (by omega) hp2
    · rw [L_zero (s := s) (by omega), L_zero (s := s') (by omega)]; simpa using hd
  | succ j ih =>
    intro hj
    have ih' := ih (by omega)
    refine ⟨fun p hp1 hp2 => ?_, ?_⟩
    · rw [L_succ (s := s) hp2, L_succ (s := s') hp2, ih'.1 (p - 1) (by omega) (by omega), ih'.1 p (by omega) hp2,
        nb_agree hp2 (fun hq => ih'.1 (p + 1) (by omega) hq)]
    · have hp2 : -((k + 1 - (j + 1) : Nat) : Int) < 0 := by omega
      rw [L_succ (s := s) hp2, L_succ (s := s') hp2,
        show -((k + 1 - (j + 1) : Nat) : Int) - 1 = -((k + 1 - j : Nat) : Int) by omega, ih'.2,
        ih'.1 (-((k + 1 - (j + 1) : Nat) : Int)) (by omega) hp2,
        nb_agree hp2 (fun hq => ih'.1 _ (by omega) hq), rule_not]

theorem permutive {s s' : Int → Bool} {k : Nat}
    (hag : ∀ p : Int, -((k : Nat) : Int) ≤ p → p < 0 → s p = s' p)
    (hd : s (-((k + 1 : Nat) : Int)) = !s' (-((k + 1 : Nat) : Int))) :
    L c s k (-1) = !L c s' k (-1) := by
  have := (permutive_aux (c := c) hag hd k (Nat.le_refl k)).2
  rwa [show -((k + 1 - k : Nat) : Int) = -1 by omega] at this

/-- Any prefix of column `-1` of length `j` is produced by some start supported on `-j … -1`. -/
theorem exists_prefix (b : Nat → Bool) : ∀ j : Nat, ∃ s : Int → Bool,
    (∀ p : Int, p < -((j : Nat) : Int) → s p = false) ∧ ∀ k, k < j → L c s k (-1) = b k := by
  intro j
  induction j with
  | zero => exact ⟨fun _ => false, fun _ _ => rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | succ j ih =>
    obtain ⟨s, hsupp, hpre⟩ := ih
    let v : Bool := xor (L c s j (-1)) (b j)
    let s' : Int → Bool := fun p => if p = -((j + 1 : Nat) : Int) then v else s p
    have hagree : ∀ p : Int, -((j : Nat) : Int) ≤ p → p < 0 → s' p = s p := by
      intro p hp1 _
      simp only [s']
      rw [ite_eq_right (by omega)]
    refine ⟨s', fun p hp => ?_, fun k hk => ?_⟩
    · simp only [s']
      rw [ite_eq_right (by omega)]
      exact hsupp p (by omega)
    · by_cases hkj : k < j
      · rw [← hpre k hkj]
        exact light_cone (k := k) (fun p hp1 hp2 => hagree p (by omega) hp2) k (Nat.le_refl k) (-1)
          (by omega) (by omega)
      · have hk' : k = j := by omega
        subst hk'
        have hsj : s (-((k + 1 : Nat) : Int)) = false := hsupp _ (by omega)
        have hs'j : s' (-((k + 1 : Nat) : Int)) = v := by simp [s']
        cases hv : v
        · -- `s'` equals `s` on `-(k+1) … -1`
          have heq : L c s' k (-1) = L c s k (-1) :=
            light_cone (k := k) (fun p hp1 hp2 => by
              by_cases e : p = -((k + 1 : Nat) : Int)
              · rw [e, hs'j, hsj, hv]
              · exact hagree p (by omega) hp2) k (Nat.le_refl k) (-1) (by omega) (by omega)
          rw [heq]
          have : xor (L c s k (-1)) (b k) = false := hv
          revert this; cases L c s k (-1) <;> cases b k <;> simp
        · -- `s'` differs from `s` exactly at `-(k+1)`
          have hp := permutive (c := c) (k := k) (s := s') (s' := s) (fun p hp1 hp2 => hagree p hp1 hp2)
            (by rw [hs'j, hsj, hv]; rfl)
          rw [hp]
          have : xor (L c s k (-1)) (b k) = true := hv
          revert this; cases L c s k (-1) <;> cases b k <;> simp

/-- **Barrier (existence).** For every driver, every `n ≥ 1` and every `b`, some start with its
leftmost black cell at `-n` (white beyond) has column `-1` equal to `b` at steps `0 … n-2`. -/
theorem barrier_exists (b : Nat → Bool) {n : Nat} (hn : 0 < n) : ∃ s : Int → Bool,
    (∀ p : Int, p < -((n : Nat) : Int) → s p = false) ∧ s (-((n : Nat) : Int)) = true ∧
      ∀ k, k + 1 < n → L c s k (-1) = b k := by
  obtain ⟨s, hsupp, hpre⟩ := exists_prefix (c := c) b (n - 1)
  let s' : Int → Bool := fun p => if p = -((n : Nat) : Int) then true else s p
  refine ⟨s', fun p hp => ?_, by simp [s'], fun k hk => ?_⟩
  · simp only [s']
    rw [ite_eq_right (by omega)]
    exact hsupp p (by omega)
  · rw [← hpre k (by omega)]
    exact light_cone (k := k) (fun p hp1 hp2 => by simp only [s']; rw [ite_eq_right (by omega)])
      k (Nat.le_refl k) (-1) (by omega) (by omega)

/-- **Barrier (uniqueness).** Two starts with leftmost black cell at `-n` (white beyond) whose
columns `-1` agree at steps `0 … n-2` are equal. -/
theorem barrier_unique {s s' : Int → Bool} {n : Nat}
    (hs0 : ∀ p : Int, p < -((n : Nat) : Int) → s p = false) (hs1 : s (-((n : Nat) : Int)) = true)
    (hs0' : ∀ p : Int, p < -((n : Nat) : Int) → s' p = false) (hs1' : s' (-((n : Nat) : Int)) = true)
    (hx : ∀ k, k + 1 < n → L c s k (-1) = L c s' k (-1)) :
    ∀ p : Int, p < 0 → s p = s' p := by
  -- agreement on `-k … -1` for all `k ≤ n - 1`, by induction
  have key : ∀ k : Nat, k + 1 ≤ n → ∀ p : Int, -((k : Nat) : Int) ≤ p → p < 0 → s p = s' p := by
    intro k
    induction k with
    | zero => intro _ p hp1 hp2; omega
    | succ k ih =>
      intro hk p hp1 hp2
      by_cases e : p = -((k + 1 : Nat) : Int)
      · subst e
        cases h1 : s (-((k + 1 : Nat) : Int)) <;> cases h2 : s' (-((k + 1 : Nat) : Int))
        · rfl
        · exact absurd (hx k (by omega)) (by
            rw [permutive (c := c) (ih (by omega)) (by rw [h1, h2]; rfl)]
            cases L c s' k (-1) <;> simp)
        · exact absurd (hx k (by omega)) (by
            rw [permutive (c := c) (ih (by omega)) (by rw [h1, h2]; rfl)]
            cases L c s' k (-1) <;> simp)
        · rfl
      · exact ih (by omega) p (by omega) hp2
  intro p hp
  by_cases h1 : p < -((n : Nat) : Int)
  · rw [hs0 p h1, hs0' p h1]
  by_cases h2 : p = -((n : Nat) : Int)
  · rw [h2, hs1, hs1']
  · exact key (n - 1) (by omega) p (by omega) hp

/-! ### The word `1`: a T-independent left-only exclusion -/

/-- The alternating half-configuration: black exactly at even positions. -/
def alt (p : Int) : Bool := decide (p % 2 = 0)

theorem alt_fixed : ∀ t : Nat, ∀ p : Int, p < 0 → L (fun _ => true) alt t p = alt p := by
  intro t
  induction t with
  | zero => intro p hp; exact L_zero (s := alt) hp
  | succ t ih =>
    intro p hp
    rw [L_succ (s := alt) hp, ih (p - 1) (by omega), ih p hp]
    have hr : L (fun _ => true) alt t (p + 1) = alt (p + 1) := by
      by_cases hq : p + 1 < 0
      · exact ih (p + 1) hq
      · rw [show p + 1 = 0 by omega, L_col0]; rfl
    rw [hr]
    simp only [alt, rule]
    have : p % 2 = 0 ∨ p % 2 = 1 := by omega
    rcases this with h | h
    · have h1 : (p - 1) % 2 = 1 := by omega
      simp [h, h1]
    · have h1 : (p - 1) % 2 = 0 := by omega
      have h2 : (p + 1) % 2 = 0 := by omega
      simp [h, h1, h2]

/-- **The word `1` is excluded by the left half alone, uniformly in the onset.** With driver
`c ≡ 1`, the forced values say column `-1` is white at every step; every start whose leftmost black
cell is at `-n` (white beyond) violates this at some step `k ≤ n + 1`. -/
theorem ones_fails {s : Int → Bool} {n : Nat} (hn : 0 < n)
    (hs0 : ∀ p : Int, p < -((n : Nat) : Int) → s p = false) (hs1 : s (-((n : Nat) : Int)) = true) :
    ∃ k, k ≤ n + 1 ∧ L (fun _ => true) s k (-1) = true := by
  refine Classical.byContradiction fun hno => ?_
  have hx : ∀ k, k ≤ n + 1 → L (fun _ => true) s k (-1) = false := by
    intro k hk
    cases h : L (fun _ => true) s k (-1)
    · rfl
    · exact absurd ⟨k, hk, h⟩ hno
  -- `s` agrees with `alt` on `-k … -1` for all `k ≤ n + 2`
  have key : ∀ k : Nat, k ≤ n + 2 → ∀ p : Int, -((k : Nat) : Int) ≤ p → p < 0 → s p = alt p := by
    intro k
    induction k with
    | zero => intro _ p hp1 hp2; omega
    | succ k ih =>
      intro hk p hp1 hp2
      by_cases e : p = -((k + 1 : Nat) : Int)
      · subst e
        cases h1 : s (-((k + 1 : Nat) : Int)) <;> cases h2 : alt (-((k + 1 : Nat) : Int))
        · rfl
        · have hp := permutive (c := fun _ => true) (k := k) (s := s) (s' := alt) (ih (by omega))
            (by rw [h1, h2]; rfl)
          rw [hx k (by omega), alt_fixed k (-1) (by omega)] at hp
          exact absurd hp (by decide)
        · have hp := permutive (c := fun _ => true) (k := k) (s := s) (s' := alt) (ih (by omega))
            (by rw [h1, h2]; rfl)
          rw [hx k (by omega), alt_fixed k (-1) (by omega)] at hp
          exact absurd hp (by decide)
        · rfl
      · exact ih (by omega) p (by omega) hp2
  have e1 := key (n + 2) (Nat.le_refl _) (-((n : Nat) : Int)) (by omega) (by omega)
  have e2 := key (n + 2) (Nat.le_refl _) (-((n : Nat) : Int) - 2) (by omega) (by omega)
  rw [hs1] at e1
  rw [hs0 _ (by omega)] at e2
  simp only [alt] at e1 e2
  have h1 : -((n : Nat) : Int) % 2 = 0 := by simpa using e1.symm
  have h2 : ¬ ((-((n : Nat) : Int) - 2) % 2 = 0) := by simpa using e2.symm
  omega

end Barrier

/-! ### Non-Autonomous Semiflow, All-White Driver Injection, Left-Bounded Nonperiodicity, and Single-Free-Phase Aperiodicity -/

/-- **Non-Autonomous Semiflow of the Driven Left Half (`L_add`):** for `p ≤ 0`, evolving `L c s`
for `t₁ + t₂` steps equals evolving `L c s t₁` for `t₂` steps under the time-shifted driver
`fun k => c (t₁ + k)`. -/
theorem L_add (c : Nat → Bool) (s : Int → Bool) (t₁ t₂ : Nat) :
    ∀ p : Int, p ≤ 0 → L c s (t₁ + t₂) p = L (fun k => c (t₁ + k)) (L c s t₁) t₂ p := by
  induction t₂ with
  | zero =>
    intro p hp
    rw [Nat.add_zero]
    by_cases hlt : p < 0
    · rw [L_zero hlt]
    · have hp0 : p = 0 := by omega
      subst hp0
      rw [L_col0, L_col0, Nat.add_zero]
  | succ t₂ ih =>
    intro p hp
    rw [← Nat.add_assoc]
    by_cases hlt : p < 0
    · rw [L_succ hlt, L_succ hlt, ih (p - 1) (by omega), ih p hp, ih (p + 1) (by omega)]
    · have hp0 : p = 0 := by omega
      subst hp0
      rw [L_col0, L_col0, Nat.add_assoc]

/-- If the left start `s` is all-white on `p < 0` and the driver `c` is white on `k < t`, then
`L c s t` remains all-white on `p < 0`. -/
theorem L_eq_false_of_white_driver {c : Nat → Bool} {s : Int → Bool}
    (hs : ∀ p : Int, p < 0 → s p = false) :
    ∀ t : Nat, (∀ k < t, c k = false) → ∀ p : Int, p < 0 → L c s t p = false
  | 0, _, p, hp => by rw [L_zero hp]; exact hs p hp
  | t + 1, hc, p, hp => by
    rw [L_succ hp,
        L_eq_false_of_white_driver hs t (fun k hk => hc k (by omega)) (p - 1) (by omega),
        L_eq_false_of_white_driver hs t (fun k hk => hc k (by omega)) p hp]
    have hr : L c s t (p + 1) = false := by
      by_cases hp1 : p + 1 < 0
      · exact L_eq_false_of_white_driver hs t (fun k hk => hc k (by omega)) (p + 1) hp1
      · have hp0 : p + 1 = 0 := by omega
        rw [hp0, L_col0]
        exact hc t (by omega)
    rw [hr]
    rfl

/-- **First Black Driver Cell Injects a Left Edge at `-1` (`L_first_black_driver_edge`):** if `s`
is all-white on `p < 0`, `c k = false` for all `k < t₀`, and `c t₀ = true`, then at step `t₀ + 1`
the driven left half has a leftmost black cell at `-1` (and is white everywhere below `-1`). -/
theorem L_first_black_driver_edge {c : Nat → Bool} {s : Int → Bool} {t₀ : Nat}
    (hs : ∀ p : Int, p < 0 → s p = false)
    (hwhite : ∀ k < t₀, c k = false) (hblack : c t₀ = true) :
    (∀ p : Int, p < -1 → L c s (t₀ + 1) p = false) ∧ L c s (t₀ + 1) (-1) = true := by
  refine ⟨fun p hp => ?_, ?_⟩
  · rw [L_succ (by omega),
        L_eq_false_of_white_driver hs t₀ hwhite (p - 1) (by omega),
        L_eq_false_of_white_driver hs t₀ hwhite p (by omega),
        L_eq_false_of_white_driver hs t₀ hwhite (p + 1) (by omega)]
    rfl
  · rw [L_succ (by omega),
        L_eq_false_of_white_driver hs t₀ hwhite (-1 - 1) (by omega),
        L_eq_false_of_white_driver hs t₀ hwhite (-1) (by omega),
        show (-1 : Int) + 1 = 0 by omega, L_col0, hblack]
    rfl

/-- Least witness for an existential natural-number predicate (`exists_least_nat`). -/
theorem exists_least_nat {P : Nat → Prop} :
    (∃ n, P n) → ∃ n, P n ∧ ∀ k < n, ¬ P k := by
  intro ⟨n, hn⟩
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : ∃ k < n, P k
    · obtain ⟨k, hkn, hk⟩ := h
      exact ih k hkn hk
    · refine ⟨n, hn, fun k hkn hk => h ⟨k, hkn, hk⟩⟩

/-- **All-White Start Column Nonperiodicity (`no_periodic_column_of_all_white`):** if `s` is
all-white on `p < 0` and the driver `c` is eventually periodic with at least one black cell
(`∃ t, c t = true`), then no column `q < 0` of `L c s` is eventually periodic. -/
theorem no_periodic_column_of_all_white {c : Nat → Bool} {s : Int → Bool}
    (hs : ∀ p : Int, p < 0 → s p = false)
    (hblack : ∃ t, c t = true) (hc : EventuallyPeriodic c) {q : Int} (hq : q < 0)
    (hcol : EventuallyPeriodic fun t => L c s t q) : False := by
  obtain ⟨t₀, ht₀, hmin⟩ := exists_least_nat (P := fun t => c t = true) hblack
  have hwhite : ∀ k < t₀, c k = false := by
    intro k hk
    cases hck : c k
    · rfl
    · exact False.elim (hmin k hk hck)
  have hedge := L_first_black_driver_edge hs hwhite ht₀
  obtain ⟨T, P, hP, hper_c⟩ := hc
  have hc_shift : EventuallyPeriodic (fun k => c (t₀ + 1 + k)) :=
    ⟨T, P, hP, fun k hk => by
      show c (t₀ + 1 + (k + P)) = c (t₀ + 1 + k)
      rw [show t₀ + 1 + (k + P) = (t₀ + 1 + k) + P by omega]
      exact hper_c (t₀ + 1 + k) (by omega)⟩
  obtain ⟨Tc, Pc, hPc, hper_col⟩ := hcol
  have hcol_shift : EventuallyPeriodic (fun k => L (fun r => c (t₀ + 1 + r)) (L c s (t₀ + 1)) k q) :=
    ⟨Tc, Pc, hPc, fun k hk => by
      dsimp only
      rw [← L_add c s (t₀ + 1) (k + Pc) q (by omega), ← L_add c s (t₀ + 1) k q (by omega)]
      rw [show t₀ + 1 + (k + Pc) = (t₀ + 1 + k) + Pc by omega]
      exact hper_col (t₀ + 1 + k) (by omega)⟩
  exact no_periodic_column (m := 1) (c := fun r => c (t₀ + 1 + r)) (s := L c s (t₀ + 1))
    hedge.1 hedge.2 (by decide) hc_shift hq hcol_shift

/-- **Left-Bounded Start Dichotomy (`bounded_all_white_or_has_edge`):** every left-bounded start `s`
(`∀ p < -(M : Int), s p = false`) either is all-white on `p < 0` or has a unique leftmost black cell
at `-m` for some `1 ≤ m ≤ M`. -/
theorem bounded_all_white_or_has_edge (s : Int → Bool) :
    ∀ M : Nat, (∀ p : Int, p < -((M : Nat) : Int) → s p = false) →
      (∀ p : Int, p < 0 → s p = false) ∨
      ∃ m : Nat, 0 < m ∧ m ≤ M ∧
        (∀ p : Int, p < -((m : Nat) : Int) → s p = false) ∧ s (-((m : Nat) : Int)) = true
  | 0, hM => Or.inl (fun p hp => hM p (by omega))
  | M + 1, hM => by
    cases hs : s (-((M + 1 : Nat) : Int))
    · have hM' : ∀ p : Int, p < -((M : Nat) : Int) → s p = false := by
        intro p hp
        by_cases heq : p = -((M + 1 : Nat) : Int)
        · rw [heq, hs]
        · exact hM p (by omega)
      rcases bounded_all_white_or_has_edge s M hM' with hall | ⟨m, hm1, hm2, hs0, hs1⟩
      · exact Or.inl hall
      · exact Or.inr ⟨m, hm1, by omega, hs0, hs1⟩
    · exact Or.inr ⟨M + 1, by omega, Nat.le_refl _, hM, hs⟩

/-- **Complete Left-Bounded Column Nonperiodicity (`no_periodic_column_of_bounded`):** for every
left-bounded start `s` (`∀ p < -(M : Int), s p = false`) and every eventually periodic driver `c`,
if either `∃ p < 0, s p = true` or `∃ t, c t = true`, then no column `q < 0` of `L c s` is
eventually periodic. -/
theorem no_periodic_column_of_bounded {c : Nat → Bool} {s : Int → Bool} {M : Nat}
    (hM : ∀ p : Int, p < -((M : Nat) : Int) → s p = false)
    (hnonempty : (∃ p : Int, p < 0 ∧ s p = true) ∨ (∃ t : Nat, c t = true))
    (hc : EventuallyPeriodic c) {q : Int} (hq : q < 0)
    (hcol : EventuallyPeriodic fun t => L c s t q) : False := by
  rcases bounded_all_white_or_has_edge s M hM with hall | ⟨m, hm, _, hs0, hs1⟩
  · rcases hnonempty with ⟨p, hp, hsp⟩ | hblack
    · rw [hall p hp] at hsp
      exact Bool.noConfusion hsp
    · exact no_periodic_column_of_all_white hall hblack hc hq hcol
  · exact no_periodic_column hs0 hs1 hm hc hq hcol

/-- Periodicity along multiples of `P` on fixed phases (`periodic_mul_of_phase_fixed`). -/
theorem periodic_mul_of_phase_fixed {x : Nat → Bool} {P K φ₀ : Nat}
    (hfix : ∀ k, K ≤ k → k % P ≠ φ₀ → x (k + P) = x k) :
    ∀ (d k : Nat), K ≤ k → k % P ≠ φ₀ → x (k + d * P) = x k
  | 0, k, _, _ => by simp
  | d + 1, k, hk, hφ => by
    rw [show k + (d + 1) * P = (k + d * P) + P by
           rw [Nat.succ_mul, ← Nat.add_assoc],
        hfix (k + d * P) (by omega) (by rw [Nat.add_mul_mod_self_right]; exact hφ),
        periodic_mul_of_phase_fixed hfix d k hk hφ]

/-- **Single-Free-Phase Periodicity Lifting (`eventuallyPeriodic_of_single_free_phase`):** for any
period `P > 0` and phase `φ₀ < P`, if `x (k + P) = x k` for all `k ≥ K` with `k % P ≠ φ₀`, and the
remaining phase subsequence `m ↦ x (P * m + φ₀)` is eventually periodic, then `x` is eventually
periodic. -/
theorem eventuallyPeriodic_of_single_free_phase {x : Nat → Bool} {P K φ₀ : Nat}
    (hP : 0 < P) (hφ₀ : φ₀ < P)
    (hfix : ∀ k, K ≤ k → k % P ≠ φ₀ → x (k + P) = x k)
    (hfree : EventuallyPeriodic (fun m => x (P * m + φ₀))) :
    EventuallyPeriodic x := by
  obtain ⟨M₀, D, hD, hper_free⟩ := hfree
  refine ⟨max K (P * M₀), D * P, Nat.mul_pos hD hP, fun k hk => ?_⟩
  have hkK : K ≤ k := Nat.le_trans (Nat.le_max_left _ _) hk
  have hkM : P * M₀ ≤ k := Nat.le_trans (Nat.le_max_right _ _) hk
  by_cases hmod : k % P = φ₀
  · have hk_eq : k = P * (k / P) + φ₀ := by
      have hdiv := Nat.div_add_mod k P
      omega
    have hm : M₀ ≤ k / P := by
      have hlt : P * M₀ < P * (k / P + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
        omega
      have : M₀ < k / P + 1 := Nat.lt_of_mul_lt_mul_left hlt
      omega
    have hstep : x (P * (k / P + D) + φ₀) = x (P * (k / P) + φ₀) := hper_free (k / P) hm
    have harg : P * (k / P + D) + φ₀ = k + D * P := by
      rw [Nat.mul_add, Nat.mul_comm P D]
      omega
    rw [← harg, hstep, ← hk_eq]
  · exact periodic_mul_of_phase_fixed hfix D k hkK hmod

/-- **Aperiodicity of the Single Free Phase in the Driven Left Half
(`not_eventuallyPeriodic_free_phase_of_bounded`):** for any left-bounded start `s` and eventually
periodic driver `c` (with `∃ p < 0, s p = true` or `∃ t, c t = true`), if column `-1` is `P`-periodic
at all phases `k % P ≠ φ₀` from `K` on (`0 < P`, `φ₀ < P`), then the single free-phase sequence
`m ↦ L c s (P * m + φ₀) (-1)` is not eventually periodic. -/
theorem not_eventuallyPeriodic_free_phase_of_bounded {c : Nat → Bool} {s : Int → Bool}
    {M P K φ₀ : Nat} (hP : 0 < P) (hφ₀ : φ₀ < P)
    (hM : ∀ p : Int, p < -((M : Nat) : Int) → s p = false)
    (hnonempty : (∃ p : Int, p < 0 ∧ s p = true) ∨ (∃ t : Nat, c t = true))
    (hc : EventuallyPeriodic c)
    (hfix : ∀ k, K ≤ k → k % P ≠ φ₀ → L c s (k + P) (-1) = L c s k (-1)) :
    ¬ EventuallyPeriodic (fun m => L c s (P * m + φ₀) (-1)) := by
  intro hfree
  exact no_periodic_column_of_bounded hM hnonempty hc (q := -1) (by omega)
    (eventuallyPeriodic_of_single_free_phase hP hφ₀ hfix hfree)

/-- **Cofinal Oscillation of the Single Free Phase (`cofinal_true_and_false_free_phase_of_bounded`):**
under the hypotheses of `not_eventuallyPeriodic_free_phase_of_bounded`, the single free-phase
sequence `m ↦ L c s (P * m + φ₀) (-1)` takes both `true` and `false` infinitely often. -/
theorem cofinal_true_and_false_free_phase_of_bounded {c : Nat → Bool} {s : Int → Bool}
    {M P K φ₀ : Nat} (hP : 0 < P) (hφ₀ : φ₀ < P)
    (hM : ∀ p : Int, p < -((M : Nat) : Int) → s p = false)
    (hnonempty : (∃ p : Int, p < 0 ∧ s p = true) ∨ (∃ t : Nat, c t = true))
    (hc : EventuallyPeriodic c)
    (hfix : ∀ k, K ≤ k → k % P ≠ φ₀ → L c s (k + P) (-1) = L c s k (-1))
    (N : Nat) :
    (∃ m, N ≤ m ∧ L c s (P * m + φ₀) (-1) = true) ∧
    (∃ m, N ≤ m ∧ L c s (P * m + φ₀) (-1) = false) := by
  have hnot := not_eventuallyPeriodic_free_phase_of_bounded hP hφ₀ hM hnonempty hc hfix
  refine ⟨?_, ?_⟩
  · refine Classical.byContradiction fun hno => hnot ⟨N, 1, by decide, fun m hm => ?_⟩
    have hm1 : L c s (P * (m + 1) + φ₀) (-1) = false := by
      cases hval : L c s (P * (m + 1) + φ₀) (-1)
      · rfl
      · exact False.elim (hno ⟨m + 1, by omega, hval⟩)
    have hm0 : L c s (P * m + φ₀) (-1) = false := by
      cases hval : L c s (P * m + φ₀) (-1)
      · rfl
      · exact False.elim (hno ⟨m, hm, hval⟩)
    dsimp only
    rw [hm1, hm0]
  · refine Classical.byContradiction fun hno => hnot ⟨N, 1, by decide, fun m hm => ?_⟩
    have hm1 : L c s (P * (m + 1) + φ₀) (-1) = true := by
      cases hval : L c s (P * (m + 1) + φ₀) (-1)
      · exact False.elim (hno ⟨m + 1, by omega, hval⟩)
      · rfl
    have hm0 : L c s (P * m + φ₀) (-1) = true := by
      cases hval : L c s (P * m + φ₀) (-1)
      · exact False.elim (hno ⟨m, hm, hval⟩)
      · rfl
    dsimp only
    rw [hm1, hm0]

/-! ### All-Column Window Locality, Top-Edge Bit-Flip Propagation, Space-Time Slice Bijection, and Single-Free-Phase Determination -/

/-- **All-Column Window Locality (`L_neg_eq_of_col_neg1_window_eq`):** for every column depth
`d : Nat` and time `t : Nat`, `L c s t (-(d : Int) - 1)` is completely determined by the driver
`c` and the values of column `-1` across the finite time window `[t, t + d]`. -/
theorem L_neg_eq_of_col_neg1_window_eq (c : Nat → Bool) (s₁ s₂ : Int → Bool) :
    ∀ (d t : Nat),
      (∀ k : Nat, t ≤ k → k ≤ t + d → L c s₁ k (-1) = L c s₂ k (-1)) →
      L c s₁ t (-(d : Int) - 1) = L c s₂ t (-(d : Int) - 1)
  | 0, t, h => by
    simpa using h t (Nat.le_refl t) (by omega)
  | d + 1, t, h => by
    have step1 := L_left (c := c) (s := s₁) (p := -(d : Int) - 1) t (by omega)
    have step2 := L_left (c := c) (s := s₂) (p := -(d : Int) - 1) t (by omega)
    have hcol : (-(d : Int) - 1) - 1 = -((d + 1 : Nat) : Int) - 1 := by omega
    rw [hcol] at step1 step2
    have ih_top : L c s₁ (t + 1) (-(d : Int) - 1) = L c s₂ (t + 1) (-(d : Int) - 1) :=
      L_neg_eq_of_col_neg1_window_eq c s₁ s₂ d (t + 1) (fun k hk1 hk2 => h k (by omega) (by omega))
    have ih_mid : L c s₁ t (-(d : Int) - 1) = L c s₂ t (-(d : Int) - 1) :=
      L_neg_eq_of_col_neg1_window_eq c s₁ s₂ d t (fun k hk1 hk2 => h k hk1 (by omega))
    have ih_right : L c s₁ t (-(d : Int) - 1 + 1) = L c s₂ t (-(d : Int) - 1 + 1) := by
      cases d with
      | zero =>
        have h0 : (-(0 : Nat) : Int) - 1 + 1 = 0 := by decide
        rw [h0, L_col0, L_col0]
      | succ d' =>
        have h1 : -((d' + 1 : Nat) : Int) - 1 + 1 = -(d' : Int) - 1 := by omega
        rw [h1]
        exact L_neg_eq_of_col_neg1_window_eq c s₁ s₂ d' t (fun k hk1 hk2 => h k hk1 (by omega))
    rw [step1, step2, ih_top, ih_mid, ih_right]

/-- **All-Column Top-Edge Bit-Flip Propagation (`L_neg_flip_of_col_neg1_top_flip`):** for every
column depth `d : Nat` and time `t : Nat`, if `s₁` and `s₂` agree on column `-1` across
`[t, t + d)` and differ at `t + d` (`L c s₁ (t + d) (-1) = !L c s₂ (t + d) (-1)`), then their
values at column `-(d : Int) - 1` at time `t` are opposite. -/
theorem L_neg_flip_of_col_neg1_top_flip (c : Nat → Bool) (s₁ s₂ : Int → Bool) :
    ∀ (d t : Nat),
      (∀ k : Nat, t ≤ k → k < t + d → L c s₁ k (-1) = L c s₂ k (-1)) →
      L c s₁ (t + d) (-1) = !L c s₂ (t + d) (-1) →
      L c s₁ t (-(d : Int) - 1) = !L c s₂ t (-(d : Int) - 1)
  | 0, t, _, htop => by
    simpa using htop
  | d + 1, t, hlow, htop => by
    have step1 := L_left (c := c) (s := s₁) (p := -(d : Int) - 1) t (by omega)
    have step2 := L_left (c := c) (s := s₂) (p := -(d : Int) - 1) t (by omega)
    have hcol : (-(d : Int) - 1) - 1 = -((d + 1 : Nat) : Int) - 1 := by omega
    rw [hcol] at step1 step2
    have ih_top : L c s₁ (t + 1) (-(d : Int) - 1) = !L c s₂ (t + 1) (-(d : Int) - 1) :=
      L_neg_flip_of_col_neg1_top_flip c s₁ s₂ d (t + 1)
        (fun k hk1 hk2 => hlow k (by omega) (by omega))
        (by simpa [show t + 1 + d = t + (d + 1) by omega] using htop)
    have ih_mid : L c s₁ t (-(d : Int) - 1) = L c s₂ t (-(d : Int) - 1) :=
      L_neg_eq_of_col_neg1_window_eq c s₁ s₂ d t (fun k hk1 hk2 => hlow k hk1 (by omega))
    have ih_right : L c s₁ t (-(d : Int) - 1 + 1) = L c s₂ t (-(d : Int) - 1 + 1) := by
      cases d with
      | zero =>
        have h0 : (-(0 : Nat) : Int) - 1 + 1 = 0 := by decide
        rw [h0, L_col0, L_col0]
      | succ d' =>
        have h1 : -((d' + 1 : Nat) : Int) - 1 + 1 = -(d' : Int) - 1 := by omega
        rw [h1]
        exact L_neg_eq_of_col_neg1_window_eq c s₁ s₂ d' t (fun k hk1 hk2 => hlow k hk1 (by omega))
    rw [step1, step2, ih_top, ih_mid, ih_right]
    cases L c s₂ (t + 1) (-(d : Int) - 1) <;>
      cases (L c s₂ t (-(d : Int) - 1) || L c s₂ t (-(d : Int) - 1 + 1)) <;> rfl

/-- **All-Column Space-Time Slice Bijection (`L_spatial_slice_eq_iff_col_neg1_window_eq`):** for
every time `t₀ : Nat` and horizon `D : Nat`, `s₁` and `s₂` agree across the spatial slice
`-(d : Int) - 1` (`d ≤ D`) at time `t₀` if and only if they agree on column `-1` across the
temporal window `[t₀, t₀ + D]`. -/
theorem L_spatial_slice_eq_iff_col_neg1_window_eq (c : Nat → Bool) (s₁ s₂ : Int → Bool)
    (t₀ D : Nat) :
    (∀ d : Nat, d ≤ D → L c s₁ t₀ (-(d : Int) - 1) = L c s₂ t₀ (-(d : Int) - 1)) ↔
    (∀ k : Nat, k ≤ D → L c s₁ (t₀ + k) (-1) = L c s₂ (t₀ + k) (-1)) := by
  induction D with
  | zero =>
    constructor <;> intro h n hn <;> have h0 : n = 0 := by omega
    · subst h0; simpa using h 0 (Nat.le_refl 0)
    · subst h0; simpa using h 0 (Nat.le_refl 0)
  | succ D ih =>
    constructor
    · intro hslice
      have hprev : ∀ k : Nat, k ≤ D → L c s₁ (t₀ + k) (-1) = L c s₂ (t₀ + k) (-1) :=
        ih.mp (fun d hd => hslice d (by omega))
      intro k hk
      by_cases hkD : k ≤ D
      · exact hprev k hkD
      · have hk_eq : k = D + 1 := by omega
        subst hk_eq
        refine Classical.byContradiction fun hne => ?_
        have htop : L c s₁ (t₀ + (D + 1)) (-1) = !L c s₂ (t₀ + (D + 1)) (-1) := by
          revert hne; cases L c s₁ (t₀ + (D + 1)) (-1) <;> cases L c s₂ (t₀ + (D + 1)) (-1) <;> decide
        have hflip := L_neg_flip_of_col_neg1_top_flip c s₁ s₂ (D + 1) t₀
          (fun j hj1 hj2 => by
            have hsub : j - t₀ ≤ D := by omega
            simpa [show t₀ + (j - t₀) = j by omega] using hprev (j - t₀) hsub)
          htop
        have heq := hslice (D + 1) (Nat.le_refl (D + 1))
        rw [heq] at hflip
        revert hflip; cases L c s₂ t₀ (-((D + 1 : Nat) : Int) - 1) <;> decide
    · intro hwin d hd
      exact L_neg_eq_of_col_neg1_window_eq c s₁ s₂ d t₀ (fun k hk1 hk2 => by
        have hsub : k - t₀ ≤ D + 1 := by omega
        simpa [show t₀ + (k - t₀) = k by omega] using hwin (k - t₀) hsub)

/-- **Initial-Prefix Bijection (`init_prefix_eq_iff_col_neg1_prefix_eq`):** two initial starts
`s₁, s₂` agree on `[-(D : Int) - 1, -1]` if and only if their column-`-1` traces under `c` agree
on `[0, D]`. -/
theorem init_prefix_eq_iff_col_neg1_prefix_eq (c : Nat → Bool) (s₁ s₂ : Int → Bool) (D : Nat) :
    (∀ d : Nat, d ≤ D → s₁ (-(d : Int) - 1) = s₂ (-(d : Int) - 1)) ↔
    (∀ k : Nat, k ≤ D → L c s₁ k (-1) = L c s₂ k (-1)) := by
  constructor
  · intro hs k hk
    have h0 := (L_spatial_slice_eq_iff_col_neg1_window_eq c s₁ s₂ 0 D).mp (fun d hd => by
      rw [L_zero (by omega), L_zero (by omega)]
      exact hs d hd) k hk
    simpa using h0
  · intro hcol d hd
    have h0 := (L_spatial_slice_eq_iff_col_neg1_window_eq c s₁ s₂ 0 D).mpr (fun k hk => by
      simpa using hcol k hk) d hd
    rwa [L_zero (by omega), L_zero (by omega)] at h0

/-- **Finite-Prefix Determination of the Entire Left Half-Plane for Left-Bounded Starts
(`L_eq_all_of_left_bounded_col_neg1_prefix_eq`):** if `s₁` and `s₂` both vanish below `-(M : Int)`
and agree on column `-1` for the first `M` steps (`∀ k < M, L c s₁ k (-1) = L c s₂ k (-1)`),
then `L c s₁ t (-(d : Int) - 1) = L c s₂ t (-(d : Int) - 1)` for every time `t : Nat` and
every column depth `d : Nat`. -/
theorem L_eq_all_of_left_bounded_col_neg1_prefix_eq (c : Nat → Bool) (s₁ s₂ : Int → Bool)
    (M : Nat)
    (hb₁ : ∀ p : Int, p < -(M : Int) → s₁ p = false)
    (hb₂ : ∀ p : Int, p < -(M : Int) → s₂ p = false)
    (hpref : ∀ k : Nat, k < M → L c s₁ k (-1) = L c s₂ k (-1))
    (t d : Nat) :
    L c s₁ t (-(d : Int) - 1) = L c s₂ t (-(d : Int) - 1) := by
  have hs_all : ∀ j : Nat, s₁ (-(j : Int) - 1) = s₂ (-(j : Int) - 1) := by
    intro j
    by_cases hj : j < M
    · cases M with
      | zero => omega
      | succ M' =>
        have hinit := (init_prefix_eq_iff_col_neg1_prefix_eq c s₁ s₂ M').mpr
          (fun k hk => hpref k (by omega))
        exact hinit j (by omega)
    · rw [hb₁ (-(j : Int) - 1) (by omega), hb₂ (-(j : Int) - 1) (by omega)]
  have hcol1_all : ∀ k : Nat, L c s₁ k (-1) = L c s₂ k (-1) := fun k =>
    (init_prefix_eq_iff_col_neg1_prefix_eq c s₁ s₂ k).mp (fun j _ => hs_all j) k (Nat.le_refl k)
  exact L_neg_eq_of_col_neg1_window_eq c s₁ s₂ d t (fun k _ _ => hcol1_all k)

/-- **All-Column Determination by the Single Free Phase Stream
(`L_neg_eq_of_free_phase_window_eq`):** when all phases `k % P ≠ φ₀` of column `-1` agree across
`[t, t + d]`, every column `-(d : Int) - 1` (`∀ d : Nat`) at time `t` is completely determined
by the single free-phase stream `m ↦ L c s (P * m + φ₀) (-1)` inside `[t, t + d]`. -/
theorem L_neg_eq_of_free_phase_window_eq (c : Nat → Bool) (s₁ s₂ : Int → Bool)
    (P φ₀ d t : Nat)
    (hfixed : ∀ k : Nat, t ≤ k → k ≤ t + d → k % P ≠ φ₀ → L c s₁ k (-1) = L c s₂ k (-1))
    (hfree : ∀ m : Nat, t ≤ P * m + φ₀ → P * m + φ₀ ≤ t + d →
      L c s₁ (P * m + φ₀) (-1) = L c s₂ (P * m + φ₀) (-1)) :
    L c s₁ t (-(d : Int) - 1) = L c s₂ t (-(d : Int) - 1) := by
  refine L_neg_eq_of_col_neg1_window_eq c s₁ s₂ d t (fun k hk1 hk2 => ?_)
  by_cases hmod : k % P = φ₀
  · have hdiv : P * (k / P) + φ₀ = k := by
      have hd := Nat.div_add_mod k P
      omega
    simpa [hdiv] using hfree (k / P) (by omega) (by omega)
  · exact hfixed k hk1 hk2 hmod

/-- **All-Column Compression of Left-Bounded Starts to Initial Free-Phase Bits
(`L_eq_all_of_left_bounded_free_phase_prefix_eq`):** if `s₁, s₂` vanish below `-(M : Int)`,
agree on the constrained phases `k % P ≠ φ₀` of column `-1` for `k < M`, and agree on the
free-phase bits `L c s (P * m + φ₀) (-1)` with `P * m + φ₀ < M`, then they agree at every
column `-(d : Int) - 1` (`∀ d : Nat`) and every time `t : Nat`. -/
theorem L_eq_all_of_left_bounded_free_phase_prefix_eq (c : Nat → Bool) (s₁ s₂ : Int → Bool)
    (P φ₀ M : Nat)
    (hb₁ : ∀ p : Int, p < -(M : Int) → s₁ p = false)
    (hb₂ : ∀ p : Int, p < -(M : Int) → s₂ p = false)
    (hfixed : ∀ k : Nat, k < M → k % P ≠ φ₀ → L c s₁ k (-1) = L c s₂ k (-1))
    (hfree : ∀ m : Nat, P * m + φ₀ < M →
      L c s₁ (P * m + φ₀) (-1) = L c s₂ (P * m + φ₀) (-1))
    (t d : Nat) :
    L c s₁ t (-(d : Int) - 1) = L c s₂ t (-(d : Int) - 1) := by
  refine L_eq_all_of_left_bounded_col_neg1_prefix_eq c s₁ s₂ M hb₁ hb₂ (fun k hk => ?_) t d
  by_cases hmod : k % P = φ₀
  · have hdiv : P * (k / P) + φ₀ = k := by
      have hd := Nat.div_add_mod k P
      omega
    simpa [hdiv] using hfree (k / P) (by omega)
  · exact hfixed k hk hmod

/-! ### 4. Global Left-Half-Plane Periodicity Exclusion (`Rule30DrivenLeft` ↔ `Rule30Jen.cell`) -/

/-- **Global Left-Half-Plane Non-Periodicity Under Periodic Center (`not_neg_col_eventuallyPeriodic_of_center`):**
if the center column `fun t => cell t 0` is eventually periodic, then NO negative column `q < 0`
of `cell` (`fun t => cell t q`) is eventually periodic. -/
theorem not_neg_col_eventuallyPeriodic_of_center
    (hc : EventuallyPeriodic (fun t => cell t 0)) {q : Int} (hq : q < 0) :
    ¬ EventuallyPeriodic (fun t => cell t q) := by
  intro hcol
  obtain ⟨T_c, P_c, hP_c, hper_c⟩ := hc
  have hc_shift : EventuallyPeriodic (fun k => cell (1 + k) 0) :=
    ⟨T_c, P_c, hP_c, fun k hk => by
      dsimp only
      rw [show 1 + (k + P_c) = (1 + k) + P_c by omega]
      exact hper_c (1 + k) (by omega)⟩
  obtain ⟨T_q, P_q, hP_q, hper_q⟩ := hcol
  have hcol_L : EventuallyPeriodic (fun k => L (fun r => cell (1 + r) 0) (fun p => cell 1 p) k q) :=
    ⟨T_q, P_q, hP_q, fun k hk => by
      dsimp only
      rw [cell_eq_L 1 (k + P_q) q (by omega), cell_eq_L 1 k q (by omega),
          show 1 + (k + P_q) = (1 + k) + P_q by omega]
      exact hper_q (1 + k) (by omega)⟩
  have hedge := real_edge 1
  exact no_periodic_column hedge.1 hedge.2 (by decide) hc_shift hq hcol_L

end Rule30DrivenLeft
end Ruliology.CellularAutomata
