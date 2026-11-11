module

public import Ruliology.CellularAutomata.Rule30Prize

@[expose] public section

/-!
# Rule 30: cylinders of the white-center, black-right times

For a Rule 30 trajectory `x` and `t ≥ 2`, the *gap* `g_t` is the least `g ∈ {1, …, t}` with
`x (t - g) (g - 2) = 1`: the time since the last black cell on the diagonal of depth `t - 2`.
For `1 ≤ g ≤ t` and `u = t - g`:

* `g_t = g ∧ x t 0 = 0 ∧ x t 1 = 1` iff the cells `x u (-g), …, x u (g + 1)` read
  `1^(2g-1) w` with `w ∈ {010, 011, 100}` (`cylinder_iff`);
* `g_t = g ∧ x t 0 = 0` iff `x u (-g), …, x u (g - 2)` are all black and
  `x u (g - 1) ∨ x u g` (`cylinder_white_iff`).

The proof is a backward reconstruction along diagonals: a black cell on one diagonal followed by
`g - 1` zero pairs on two adjacent diagonals is equivalent to a solid interval of `2g - 1` black
cells at the earlier time (`zero_pairs_iff_solid`).

On the single-seed pattern every white center time `t ≥ 2` has a gap with `2 g_t ≤ t`
(`gap_exists_of_white`), so the number of white-center, black-right times on the block
`I_H = {H + 1, …, 2H}`, which equals the number `N11 H` of words `11` in column `1` there, is the
sum over `t ∈ I_H` and `1 ≤ g ≤ t / 2` of the cylinder indicators, with at most one nonzero
term for each `t` (`white_black_count`).
-/

namespace Ruliology.CellularAutomata.Rule30CenterCylinders

open Rule30Jen Rule30Prize

/-! ### Trajectories and diagonals -/

/-- `x` is a Rule 30 trajectory. -/
def IsTraj (x : Nat → Int → Bool) : Prop :=
  ∀ (t : Nat) (i : Int), x (t + 1) i = rule (x t (i - 1)) (x t i) (x t (i + 1))

theorem cell_isTraj : IsTraj cell := fun _ _ => rfl

/-- The read of the diagonal of depth `D` at time `v`: `x v (D - v)`. -/
def lam (x : Nat → Int → Bool) (D : Int) (v : Nat) : Bool := x v (D - v)

/-- The diagonal of depth `D` at time `v + 1` is the rule applied to depths `D - 2, D - 1, D`
at time `v`. -/
theorem lam_succ {x : Nat → Int → Bool} (hx : IsTraj x) (D : Int) (v : Nat) :
    lam x D (v + 1) = rule (lam x (D - 2) v) (lam x (D - 1) v) (lam x D v) := by
  unfold lam
  rw [hx]
  have e1 : D - ((v + 1 : Nat) : Int) - 1 = D - 2 - v := by push_cast; omega
  have e2 : D - ((v + 1 : Nat) : Int) = D - 1 - v := by push_cast; omega
  have e3 : D - ((v + 1 : Nat) : Int) + 1 = D - v := by push_cast; omega
  rw [e1, e3, e2]

/-- A zero pair: the diagonals of depths `D` and `D + 1` are both white at time `v`. -/
def ZeroPair (x : Nat → Int → Bool) (D : Int) (v : Nat) : Prop :=
  lam x D v = false ∧ lam x (D + 1) v = false

/-- Below a zero pair, the next zero pair on the same diagonals is the zero pair two depths
lower. -/
theorem zeroPair_succ_iff {x : Nat → Int → Bool} (hx : IsTraj x) (D : Int) (v : Nat)
    (h : ZeroPair x D v) : ZeroPair x D (v + 1) ↔ ZeroPair x (D - 2) v := by
  unfold ZeroPair at *
  rw [lam_succ hx D v, lam_succ hx (D + 1) v]
  have e1 : D + 1 - 2 = D - 1 := by omega
  have e2 : D + 1 - 1 = D := by omega
  have e3 : D - 2 + 1 = D - 1 := by omega
  rw [e1, e2, e3, h.1, h.2]
  cases lam x (D - 2) v <;> cases lam x (D - 1) v <;> simp [rule]

/-- Above a black cell, the zero pair one step later is two more black cells. -/
theorem zeroPair_first_iff {x : Nat → Int → Bool} (hx : IsTraj x) (D : Int) (u : Nat)
    (h : lam x D u = true) :
    ZeroPair x D (u + 1) ↔ lam x (D - 2) u = true ∧ lam x (D - 1) u = true := by
  unfold ZeroPair
  rw [lam_succ hx D u, lam_succ hx (D + 1) u]
  have e1 : D + 1 - 2 = D - 1 := by omega
  have e2 : D + 1 - 1 = D := by omega
  rw [e1, e2, h]
  cases lam x (D - 2) u <;> cases lam x (D - 1) u <;> cases lam x (D + 1) u <;> simp [rule]

/-- A solid diagonal interval: depths `a, …, b` are black at time `u`. -/
def solidDiag (x : Nat → Int → Bool) (u : Nat) (a b : Int) : Prop :=
  ∀ i, a ≤ i → i ≤ b → lam x i u = true

/-- A run of zero pairs on depths `D, D + 1` at times `u + 1, …, u + k` reduces to a first zero
pair and a run on depths `D - 2, D - 1` at times `u + 1, …, u + k - 1`. -/
theorem zeroPairs_shift {x : Nat → Int → Bool} (hx : IsTraj x) (D : Int) (u : Nat) :
    ∀ k, (∀ j, 1 ≤ j → j ≤ k + 1 → ZeroPair x D (u + j)) ↔
      ZeroPair x D (u + 1) ∧ ∀ j, 1 ≤ j → j ≤ k → ZeroPair x (D - 2) (u + j)
  | 0 => by
    constructor
    · intro h; exact ⟨h 1 (Nat.le_refl 1) (Nat.le_refl 1), fun j h1 h2 => by omega⟩
    · intro h j h1 h2
      have : j = 1 := by omega
      subst this; exact h.1
  | k + 1 => by
    have ih := zeroPairs_shift hx D u k
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := ih.mp (fun j a b => h j a (by omega))
      refine ⟨h1, fun j a b => ?_⟩
      by_cases hj : j ≤ k
      · exact h2 j a hj
      · have hj' : j = k + 1 := by omega
        subst hj'
        have hz := h (k + 1) (by omega) (by omega)
        exact (zeroPair_succ_iff hx D (u + (k + 1)) hz).mp (h (k + 2) (by omega) (Nat.le_refl _))
    · intro ⟨h1, h2⟩ j a b
      have hk : ∀ j, 1 ≤ j → j ≤ k + 1 → ZeroPair x D (u + j) :=
        ih.mpr ⟨h1, fun j a b => h2 j a (by omega)⟩
      by_cases hj : j ≤ k + 1
      · exact hk j a hj
      · have hj' : j = k + 2 := by omega
        subst hj'
        exact (zeroPair_succ_iff hx D (u + (k + 1)) (hk (k + 1) (by omega) (Nat.le_refl _))).mpr
          (h2 (k + 1) (by omega) (Nat.le_refl _))

/-- **Zero pairs and solid intervals.** A black cell on the diagonal of depth `D` at time `u`
followed by `g - 1` zero pairs on depths `D, D + 1` is equivalent to the depths
`D - 2g + 2, …, D` being all black at time `u`. -/
theorem zero_pairs_iff_solid {x : Nat → Int → Bool} (hx : IsTraj x) (D : Int) (u g : Nat)
    (hg : 1 ≤ g) :
    (lam x D u = true ∧
        ∀ j, 1 ≤ j → j < g → lam x D (u + j) = false ∧ lam x (D + 1) (u + j) = false)
      ↔ solidDiag x u (D - 2 * g + 2) D := by
  induction g generalizing D with
  | zero => omega
  | succ g ih =>
    cases g with
    | zero =>
      constructor
      · intro ⟨h, _⟩ i a b
        have : i = D := by omega
        subst this; exact h
      · intro h
        exact ⟨h D (by omega) (by omega), fun j a b => by omega⟩
    | succ g =>
      have ih' := ih (D - 2) (by omega)
      have hs := zeroPairs_shift hx D u g
      constructor
      · intro ⟨hD, hz⟩
        have hz' : ∀ j, 1 ≤ j → j ≤ g + 1 → ZeroPair x D (u + j) :=
          fun j a b => hz j a (by omega)
        obtain ⟨h1, h2⟩ := hs.mp hz'
        obtain ⟨hD2, hD1⟩ := (zeroPair_first_iff hx D u hD).mp h1
        have hsol := ih'.mp ⟨hD2, fun j a b => h2 j a (by omega)⟩
        intro i a b
        by_cases hi : i ≤ D - 2
        · exact hsol i (by omega) hi
        · by_cases hi' : i = D - 1
          · subst hi'; exact hD1
          · have : i = D := by omega
            subst this; exact hD
      · intro hsol
        have hD : lam x D u = true := hsol D (by omega) (Int.le_refl _)
        have hD1 : lam x (D - 1) u = true := hsol (D - 1) (by omega) (by omega)
        have hrest := ih'.mpr (fun i a b => hsol i (by omega) (by omega))
        have h1 := (zeroPair_first_iff hx D u hD).mpr ⟨hrest.1, hD1⟩
        have hz := hs.mpr ⟨h1, fun j a b => hrest.2 j a (by omega)⟩
        exact ⟨hD, fun j a b => hz j a (by omega)⟩

/-! ### The cylinder characterization -/

/-- The gap at time `t` is exactly `g`: `x (t - g) (g - 2)` is black and `x (t - j) (j - 2)` is
white for `1 ≤ j < g`. -/
def gapAt (x : Nat → Int → Bool) (t g : Nat) : Prop :=
  x (t - g) ((g : Int) - 2) = true ∧
    ∀ j, 1 ≤ j → j < g → x (t - j) ((j : Int) - 2) = false

/-- The cells `x u a, …, x u b` are all black. -/
def solid (x : Nat → Int → Bool) (u : Nat) (a b : Int) : Prop :=
  ∀ i, a ≤ i → i ≤ b → x u i = true

theorem lam_eq (x : Nat → Int → Bool) (D : Int) (v : Nat) (p : Int) (h : D - v = p) :
    lam x D v = x v p := by
  unfold lam; rw [h]

/-- The center chain: with `C v = lam x (D + 2) v`, `B v = lam x (D + 1) v`, if the diagonal of
depth `D` is white at times `u + 1, …, u + k`, then `C (u + k + 1)` is `C (u + 1)` or one of
`B (u + 1), …, B (u + k)`. -/
theorem center_chain {x : Nat → Int → Bool} (hx : IsTraj x) (D : Int) (u : Nat) :
    ∀ k, (∀ j, 1 ≤ j → j ≤ k → lam x D (u + j) = false) →
      (lam x (D + 2) (u + k + 1) = false ↔
        lam x (D + 2) (u + 1) = false ∧
          ∀ j, 1 ≤ j → j ≤ k → lam x (D + 1) (u + j) = false)
  | 0 => fun _ => by
    constructor
    · intro h; exact ⟨h, fun j a b => by omega⟩
    · intro h; exact h.1
  | k + 1 => fun hA => by
    have ih := center_chain hx D u k (fun j a b => hA j a (by omega))
    have hs := lam_succ hx (D + 2) (u + (k + 1))
    have e1 : D + 2 - 2 = D := by omega
    have e2 : D + 2 - 1 = D + 1 := by omega
    rw [e1, e2, hA (k + 1) (by omega) (Nat.le_refl _)] at hs
    have e4 : u + k + 1 = u + (k + 1) := by omega
    rw [hs]
    rw [e4] at ih
    constructor
    · intro h
      have hb : lam x (D + 1) (u + (k + 1)) = false ∧ lam x (D + 2) (u + (k + 1)) = false := by
        revert h; cases lam x (D + 1) (u + (k + 1)) <;> cases lam x (D + 2) (u + (k + 1)) <;>
          simp [rule]
      obtain ⟨h1, h2⟩ := ih.mp hb.2
      refine ⟨h1, fun j a b => ?_⟩
      by_cases hj : j ≤ k
      · exact h2 j a hj
      · have : j = k + 1 := by omega
        subst this; exact hb.1
    · intro ⟨h1, h2⟩
      have hc := ih.mpr ⟨h1, fun j a b => h2 j a (by omega)⟩
      rw [hc, h2 (k + 1) (by omega) (Nat.le_refl _)]
      rfl

/-- The right chain: with `R v = lam x (D + 3) v`, if the depths `D + 1, D + 2` are white at
times `u + 1, …, u + k`, then `R (u + k + 1) = R (u + 1)`. -/
theorem right_chain {x : Nat → Int → Bool} (hx : IsTraj x) (D : Int) (u : Nat) :
    ∀ k, (∀ j, 1 ≤ j → j ≤ k →
        lam x (D + 1) (u + j) = false ∧ lam x (D + 2) (u + j) = false) →
      lam x (D + 3) (u + k + 1) = lam x (D + 3) (u + 1)
  | 0 => fun _ => rfl
  | k + 1 => fun h => by
    have ih := right_chain hx D u k (fun j a b => h j a (by omega))
    have hs := lam_succ hx (D + 3) (u + (k + 1))
    have e1 : D + 3 - 2 = D + 1 := by omega
    have e2 : D + 3 - 1 = D + 2 := by omega
    have hk := h (k + 1) (by omega) (Nat.le_refl _)
    rw [e1, e2, hk.1, hk.2] at hs
    have e4 : u + k + 1 = u + (k + 1) := by omega
    rw [e4] at ih
    rw [hs]
    simp [rule, ih]

/-- The white-center core, on diagonals: a black cell on depth `D` at time `u`, white cells on
depth `D` at times `u + 1, …, u + k` and a white cell on depth `D + 2` at time `u + k + 1` are
equivalent to depths `D - 2k, …, D` black at time `u` and depth `D + 1` or `D + 2` black at
time `u`. -/
theorem white_core {x : Nat → Int → Bool} (hx : IsTraj x) (D : Int) (u k : Nat) :
    (lam x D u = true ∧ (∀ j, 1 ≤ j → j ≤ k → lam x D (u + j) = false) ∧
        lam x (D + 2) (u + k + 1) = false) ↔
      solidDiag x u (D - 2 * (k + 1) + 2) D ∧ (lam x (D + 1) u || lam x (D + 2) u) = true := by
  have hzs := zero_pairs_iff_solid hx D u (k + 1) (by omega)
  have hc1 : lam x (D + 2) (u + 1) = !(lam x (D + 1) u || lam x (D + 2) u) ↔
      lam x D u = true := by
    rw [lam_succ hx (D + 2) u]
    have e1 : D + 2 - 2 = D := by omega
    have e2 : D + 2 - 1 = D + 1 := by omega
    rw [e1, e2]
    cases lam x D u <;> cases lam x (D + 1) u <;> cases lam x (D + 2) u <;> simp [rule]
  constructor
  · intro ⟨hA, hz, hC⟩
    have hch := (center_chain hx D u k hz).mp hC
    have hc := hc1.mpr hA
    rw [hch.1] at hc
    refine ⟨hzs.mp ⟨hA, fun j a b => ⟨hz j a (by omega), hch.2 j a (by omega)⟩⟩, ?_⟩
    revert hc; cases (lam x (D + 1) u || lam x (D + 2) u) <;> simp
  · intro ⟨hsol, hbc⟩
    obtain ⟨hA, hz⟩ := hzs.mpr hsol
    have hz' : ∀ j, 1 ≤ j → j ≤ k → lam x D (u + j) = false :=
      fun j a b => (hz j a (by omega)).1
    refine ⟨hA, hz', ?_⟩
    have hc := hc1.mpr hA
    rw [hbc] at hc
    exact (center_chain hx D u k hz').mpr ⟨hc, fun j a b => (hz j a (by omega)).2⟩

/-- The right-neighbour core: under white cells on depth `D` at times `u + 1, …, u + k` and a
white cell on depth `D + 2` at time `u + k + 1`, the cell on depth `D + 3` at time
`u + k + 1` is `B xor (C || R)` for the depths `D + 1, D + 2, D + 3` at time `u`. -/
theorem right_core {x : Nat → Int → Bool} (hx : IsTraj x) (D : Int) (u k : Nat)
    (hz : ∀ j, 1 ≤ j → j ≤ k → lam x D (u + j) = false)
    (hC : lam x (D + 2) (u + k + 1) = false) :
    lam x (D + 3) (u + k + 1) = rule (lam x (D + 1) u) (lam x (D + 2) u) (lam x (D + 3) u) := by
  have hch := (center_chain hx D u k hz).mp hC
  have hCj : ∀ j, 1 ≤ j → j ≤ k → lam x (D + 2) (u + j) = false := by
    intro j a b
    have hzj : ∀ i, 1 ≤ i → i ≤ j - 1 → lam x D (u + i) = false :=
      fun i a' b' => hz i a' (by omega)
    have e : u + (j - 1) + 1 = u + j := by omega
    have := (center_chain hx D u (j - 1) hzj).mpr ⟨hch.1, fun i a' b' => hch.2 i a' (by omega)⟩
    rw [e] at this; exact this
  rw [right_chain hx D u k (fun j a b => ⟨hch.2 j a b, hCj j a b⟩), lam_succ hx (D + 3) u]
  have e1 : D + 3 - 2 = D + 1 := by omega
  have e2 : D + 3 - 1 = D + 2 := by omega
  rw [e1, e2]

/-- The gap, read on the diagonal of depth `t - 2`. -/
theorem gapAt_iff (x : Nat → Int → Bool) (t g : Nat) (h1 : 1 ≤ g) (h2 : g ≤ t) :
    gapAt x t g ↔ lam x ((t : Int) - 2) (t - g) = true ∧
      ∀ j, 1 ≤ j → j ≤ g - 1 → lam x ((t : Int) - 2) (t - g + j) = false := by
  have hl : ∀ v : Nat, v ≤ t → lam x ((t : Int) - 2) v = x v (((t - v : Nat) : Int) - 2) := by
    intro v hv; apply lam_eq; omega
  unfold gapAt
  rw [hl (t - g) (by omega)]
  have e : t - (t - g) = g := by omega
  rw [e]
  apply and_congr_right
  intro _
  constructor
  · intro h j a b
    rw [hl (t - g + j) (by omega)]
    have e1 : t - (t - g + j) = g - j := by omega
    have e2 : t - g + j = t - (g - j) := by omega
    rw [e1, e2]
    exact h (g - j) (by omega) (by omega)
  · intro h j a b
    have := h (g - j) (by omega) (by omega)
    rw [hl (t - g + (g - j)) (by omega)] at this
    have e1 : t - (t - g + (g - j)) = j := by omega
    have e2 : t - g + (g - j) = t - j := by omega
    rw [e1, e2] at this
    exact this

/-- **Cylinder law without the right neighbour.** For `1 ≤ g ≤ t` and `u = t - g`: the gap at
time `t` is `g` and the center `x t 0` is white iff `x u (-g), …, x u (g - 2)` are black and
`x u (g - 1) ∨ x u g`. -/
theorem cylinder_white_iff {x : Nat → Int → Bool} (hx : IsTraj x) (t g : Nat)
    (h : 1 ≤ g ∧ g ≤ t) :
    gapAt x t g ∧ x t 0 = false ↔
      solid x (t - g) (-(g : Int)) ((g : Int) - 2) ∧
        (x (t - g) ((g : Int) - 1) || x (t - g) (g : Int)) = true := by
  obtain ⟨h1, h2⟩ := h
  have hw := white_core hx ((t : Int) - 2) (t - g) (g - 1)
  have et : t - g + (g - 1) + 1 = t := by omega
  rw [et] at hw
  have hc : lam x ((t : Int) - 2 + 2) t = x t 0 := lam_eq x _ _ _ (by omega)
  have hb : lam x ((t : Int) - 2 + 1) (t - g) = x (t - g) ((g : Int) - 1) :=
    lam_eq x _ _ _ (by omega)
  have hc0 : lam x ((t : Int) - 2 + 2) (t - g) = x (t - g) (g : Int) := lam_eq x _ _ _ (by omega)
  rw [hc, hb, hc0] at hw
  rw [gapAt_iff x t g h1 h2, and_assoc, hw]
  apply and_congr_left
  intro _
  constructor
  · intro hs i a b
    have := hs (i + (t - g : Nat)) (by omega) (by omega)
    rw [lam_eq x _ _ i (by omega)] at this
    exact this
  · intro hs i a b
    rw [lam_eq x _ _ (i - (t - g : Nat)) (by omega)]
    exact hs _ (by omega) (by omega)

/-- **Cylinder law.** For `1 ≤ g ≤ t` and `u = t - g`: the gap at time `t` is `g`, the center
`x t 0` is white and its right neighbour `x t 1` is black iff `x u (-g), …, x u (g - 2)` are
black and `(x u (g - 1), x u g, x u (g + 1))` is `010`, `011` or `100`. -/
theorem cylinder_iff {x : Nat → Int → Bool} (hx : IsTraj x) (t g : Nat)
    (h : 1 ≤ g ∧ g ≤ t) :
    gapAt x t g ∧ x t 0 = false ∧ x t 1 = true ↔
      solid x (t - g) (-(g : Int)) ((g : Int) - 2) ∧
        (x (t - g) ((g : Int) - 1), x (t - g) (g : Int), x (t - g) ((g : Int) + 1)) ∈
          [(false, true, false), (false, true, true), (true, false, false)] := by
  obtain ⟨h1, h2⟩ := h
  have hwi := cylinder_white_iff hx t g ⟨h1, h2⟩
  -- The right neighbour, from the right core.
  have hR : gapAt x t g → x t 0 = false →
      x t 1 =
        rule (x (t - g) ((g : Int) - 1)) (x (t - g) (g : Int)) (x (t - g) ((g : Int) + 1)) := by
    intro hgap hc
    obtain ⟨_, hz⟩ := (gapAt_iff x t g h1 h2).mp hgap
    have et : t - g + (g - 1) + 1 = t := by omega
    have hC : lam x ((t : Int) - 2 + 2) (t - g + (g - 1) + 1) = false := by
      rw [et, lam_eq x _ _ 0 (by omega)]; exact hc
    have := right_core hx ((t : Int) - 2) (t - g) (g - 1) hz hC
    rw [et, lam_eq x _ _ 1 (by omega), lam_eq x _ _ ((g : Int) - 1) (by omega),
      lam_eq x _ _ (g : Int) (by omega), lam_eq x _ _ ((g : Int) + 1) (by omega)] at this
    exact this
  constructor
  · intro ⟨hgap, hc, hr⟩
    obtain ⟨hs, hbc⟩ := hwi.mp ⟨hgap, hc⟩
    refine ⟨hs, ?_⟩
    have := hR hgap hc
    rw [hr] at this
    revert hbc this
    cases x (t - g) ((g : Int) - 1) <;> cases x (t - g) (g : Int) <;>
      cases x (t - g) ((g : Int) + 1) <;> simp [rule]
  · intro ⟨hs, hm⟩
    have hbc : (x (t - g) ((g : Int) - 1) || x (t - g) (g : Int)) = true := by
      revert hm
      cases x (t - g) ((g : Int) - 1) <;> cases x (t - g) (g : Int) <;>
        cases x (t - g) ((g : Int) + 1) <;> simp
    obtain ⟨hgap, hc⟩ := hwi.mpr ⟨hs, hbc⟩
    refine ⟨hgap, hc, ?_⟩
    rw [hR hgap hc]
    revert hm
    cases x (t - g) ((g : Int) - 1) <;> cases x (t - g) (g : Int) <;>
      cases x (t - g) ((g : Int) + 1) <;> simp [rule]

/-! ### Zero pairs propagate down to the initial row -/

/-- Zero pairs on depths `D, D + 1` at times `u, …, u + k` force depths `D - 2k, …, D + 1` to be
white at time `u`. -/
theorem zeroPairs_down {x : Nat → Int → Bool} (hx : IsTraj x) (u : Nat) :
    ∀ k (D : Int), (∀ j, j ≤ k → ZeroPair x D (u + j)) →
      ∀ i, D - 2 * k ≤ i → i ≤ D + 1 → lam x i u = false
  | 0, D, h => by
    intro i a b
    have h0 := h 0 (Nat.le_refl 0)
    by_cases hi : i = D
    · subst hi; exact h0.1
    · have : i = D + 1 := by omega
      subst this; exact h0.2
  | k + 1, D, h => by
    have hd : ∀ j, j ≤ k → ZeroPair x (D - 2) (u + j) := fun j hj =>
      (zeroPair_succ_iff hx D (u + j) (h j (by omega))).mp (h (j + 1) (by omega))
    have ih := zeroPairs_down hx u k (D - 2) hd
    intro i a b
    by_cases hi : i ≤ D - 1
    · exact ih i (by omega) (by omega)
    · have h0 := h 0 (by omega)
      by_cases hi' : i = D
      · subst hi'; exact h0.1
      · have : i = D + 1 := by omega
        subst this; exact h0.2

/-! ### The single-seed pattern -/

/-- A least witness in `{1, …, n}`. -/
theorem exists_least (P : Nat → Prop) :
    ∀ n, (∃ g, 1 ≤ g ∧ g ≤ n ∧ P g) →
      ∃ g, 1 ≤ g ∧ g ≤ n ∧ P g ∧ ∀ j, 1 ≤ j → j < g → ¬ P j
  | 0, ⟨g, h1, h2, _⟩ => by omega
  | n + 1, ⟨g, h1, h2, hg⟩ => by
    by_cases hn : ∃ g, 1 ≤ g ∧ g ≤ n ∧ P g
    · obtain ⟨g', a, b, c, d⟩ := exists_least P n hn
      exact ⟨g', a, by omega, c, d⟩
    · have hg' : g = n + 1 := by
        apply Nat.le_antisymm h2
        apply Nat.le_of_not_lt
        intro hlt
        exact hn ⟨g, h1, by omega, hg⟩
      subst hg'
      exact ⟨n + 1, h1, Nat.le_refl _, hg, fun j a b hj => hn ⟨j, a, by omega, hj⟩⟩

/-- **Cone lemma.** On the single-seed pattern every white center time `t ≥ 2` has a gap `g`,
and `1 ≤ g` and `2g ≤ t`. -/
theorem gap_exists_of_white (t : Nat) (ht : 2 ≤ t) (hc : center t = false) :
    ∃ g, 1 ≤ g ∧ 2 * g ≤ t ∧ gapAt cell t g := by
  have hex : ∃ g, 1 ≤ g ∧ g ≤ t ∧ cell (t - g) ((g : Int) - 2) = true := by
    apply Classical.byContradiction
    intro hno
    -- The diagonal of depth `t - 2` is white at times `0, …, t - 1`.
    have hA : ∀ v, v ≤ t - 1 → lam cell ((t : Int) - 2) v = false := by
      intro v hv
      rw [lam_eq cell _ _ (((t - v : Nat) : Int) - 2) (by omega)]
      cases hcv : cell (t - (t - v)) (((t - v : Nat) : Int) - 2)
      · have e : t - (t - v) = v := by omega
        rw [e] at hcv; exact hcv
      · exact absurd ⟨t - v, by omega, by omega, hcv⟩ hno
    have hC : lam cell ((t : Int) - 2 + 2) (0 + (t - 1) + 1) = false := by
      rw [lam_eq cell _ _ 0 (by omega)]
      have e : 0 + (t - 1) + 1 = t := by omega
      rw [e]; exact hc
    have hch := (center_chain cell_isTraj ((t : Int) - 2) 0 (t - 1)
      (fun j a b => hA (0 + j) (by omega))).mp hC
    -- The first step: `C 1 = A 0 xor (B 0 || C 0)` with `A 0` white.
    have h1 := hch.1
    rw [lam_succ cell_isTraj] at h1
    have e1 : (t : Int) - 2 + 2 - 2 = (t : Int) - 2 := by omega
    have e2 : (t : Int) - 2 + 2 - 1 = (t : Int) - 2 + 1 := by omega
    rw [e1, hA 0 (by omega), e2] at h1
    have hB0 : lam cell ((t : Int) - 2 + 1) 0 = false := by
      revert h1; cases lam cell ((t : Int) - 2 + 1) 0 <;> simp [rule]
    have hz : ∀ j, j ≤ t - 1 → ZeroPair cell ((t : Int) - 2) (0 + j) := by
      intro j hj
      refine ⟨hA (0 + j) (by omega), ?_⟩
      by_cases hj0 : j = 0
      · subst hj0; exact hB0
      · exact hch.2 j (by omega) hj
    have h00 := zeroPairs_down cell_isTraj 0 (t - 1) ((t : Int) - 2) hz 0 (by omega) (by omega)
    have : lam cell 0 0 = true := rfl
    rw [this] at h00
    exact Bool.noConfusion h00
  obtain ⟨g, h1, h2, hg, hmin⟩ := exists_least _ t hex
  have hgap : gapAt cell t g := ⟨hg, fun j a b => by
    cases hj : cell (t - j) ((j : Int) - 2)
    · rfl
    · exact absurd hj (hmin j a b)⟩
  refine ⟨g, h1, ?_, hgap⟩
  obtain ⟨hs, _⟩ := (cylinder_white_iff cell_isTraj t g ⟨h1, h2⟩).mp ⟨hgap, hc⟩
  have hleft := hs (-(g : Int)) (Int.le_refl _) (by omega)
  apply Nat.le_of_not_lt
  intro hlt
  have := cell_eq_false_of_lt (t - g) (-(g : Int)) (by omega)
  rw [this] at hleft
  exact Bool.noConfusion hleft

/-- **Gap uniqueness.** The gap is the least such `g`, so there is at most one. -/
theorem gap_unique (x : Nat → Int → Bool) (t g g' : Nat) (hg : 1 ≤ g) (hg' : 1 ≤ g')
    (h : gapAt x t g) (h' : gapAt x t g') : g = g' := by
  apply Classical.byContradiction
  intro hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := h'.2 g hg hlt
    rw [h.1] at this; exact Bool.noConfusion this
  · have := h.2 g' hg' hlt
    rw [h'.1] at this; exact Bool.noConfusion this

/-! ### The counting law -/

/-- Column `1` of the single-seed pattern: the right neighbour of the center. -/
def r (t : Nat) : Bool := cell t 1

/-- The number of `t` in `I_H = {H + 1, …, 2H}` with `f t`. -/
def blockCount (f : Nat → Bool) (H : Nat) : Nat :=
  ((List.range H).map (fun i => H + 1 + i) |>.filter f).length

/-- The number of words `11` in column `1` starting in `I_H`. -/
def N11 (H : Nat) : Nat := blockCount (fun t => r t && r (t + 1)) H

/-- A black cell in column `1` forces the center at the same time: `center t = !r (t + 1)`. -/
theorem center_of_right_black (t : Nat) (h : r t = true) : center t = !(r (t + 1)) := by
  have e : r (t + 1) = rule (cell t 0) (cell t 1) (cell t 2) := rfl
  have h' : cell t 1 = true := h
  rw [e, h']
  unfold center rule
  cases cell t 0 <;> cases cell t 2 <;> rfl

/-- The cylinder indicator at time `t` and gap `g` on the single-seed pattern: with
`u = t - g`, the cells `cell u (-g), …, cell u (g - 2)` are black and
`(cell u (g - 1), cell u g, cell u (g + 1))` is `010`, `011` or `100`. -/
def cyl (t g : Nat) : Bool :=
  (List.range (2 * g - 1)).all (fun k => cell (t - g) (-(g : Int) + k)) &&
    decide ((cell (t - g) ((g : Int) - 1), cell (t - g) (g : Int), cell (t - g) ((g : Int) + 1)) ∈
      [(false, true, false), (false, true, true), (true, false, false)])

theorem cyl_iff (t g : Nat) (hg : 1 ≤ g) :
    cyl t g = true ↔ solid cell (t - g) (-(g : Int)) ((g : Int) - 2) ∧
      (cell (t - g) ((g : Int) - 1), cell (t - g) (g : Int), cell (t - g) ((g : Int) + 1)) ∈
        [(false, true, false), (false, true, true), (true, false, false)] := by
  unfold cyl
  rw [Bool.and_eq_true, decide_eq_true_iff, List.all_eq_true]
  apply and_congr_left
  intro _
  constructor
  · intro h i a b
    have := h (i + g).toNat (List.mem_range.mpr (by omega))
    have e : -(g : Int) + ((i + g).toNat : Nat) = i := by omega
    rw [e] at this; exact this
  · intro h k hk
    rw [List.mem_range] at hk
    exact h _ (by omega) (by omega)

/-- The number of `t ∈ {a, …, a + n - 1}` with `f t`. -/
def countFrom (f : Nat → Bool) (a n : Nat) : Nat :=
  ((List.range n).map (fun i => a + i) |>.filter f).length

theorem countFrom_succ (f : Nat → Bool) (a n : Nat) :
    countFrom f a (n + 1) = countFrom f a n + if f (a + n) then 1 else 0 := by
  unfold countFrom
  rw [List.range_succ, List.map_append, List.filter_append, List.length_append]
  cases h : f (a + n) <;> simp [h]

/-- `Σ_{i < n} f (a + i)`. -/
def natSumFrom (f : Nat → Nat) (a : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => natSumFrom f a n + f (a + n)

theorem countFrom_eq_sum (f : Nat → Bool) (a : Nat) :
    ∀ n, countFrom f a n = natSumFrom (fun t => if f t then 1 else 0) a n
  | 0 => rfl
  | n + 1 => by rw [countFrom_succ, countFrom_eq_sum f a n]; rfl

theorem natSumFrom_congr (f f' : Nat → Nat) (a : Nat) :
    ∀ n, (∀ i, i < n → f (a + i) = f' (a + i)) → natSumFrom f a n = natSumFrom f' a n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [natSumFrom]
    rw [natSumFrom_congr f f' a n (fun i hi => h i (by omega)), h n (by omega)]

theorem countFrom_eq_zero (f : Nat → Bool) (a : Nat) :
    ∀ n, (∀ i, i < n → f (a + i) = false) → countFrom f a n = 0
  | 0, _ => rfl
  | n + 1, h => by
    rw [countFrom_succ, countFrom_eq_zero f a n (fun i hi => h i (by omega)), h n (by omega)]
    rfl

theorem countFrom_eq_one (f : Nat → Bool) (a i0 : Nat) :
    ∀ n, i0 < n → f (a + i0) = true → (∀ i, i < n → f (a + i) = true → i = i0) →
      countFrom f a n = 1
  | 0, h, _, _ => by omega
  | n + 1, h, hf, hu => by
    rw [countFrom_succ]
    by_cases hn : i0 = n
    · subst hn
      rw [countFrom_eq_zero f a i0 (fun i hi => by
        cases hfi : f (a + i)
        · rfl
        · exact absurd (hu i (by omega) hfi) (by omega)), hf]
      rfl
    · rw [countFrom_eq_one f a i0 n (by omega) hf (fun i hi => hu i (by omega))]
      cases hfn : f (a + n)
      · rfl
      · exact absurd (hu n (by omega) hfn).symm hn

/-- For `t ≥ 2`, the white-center, black-right indicator at time `t` is the number of
`g ∈ {1, …, t / 2}` whose cylinder indicator holds. -/
theorem indicator_eq_cyl_count (t : Nat) (ht : 2 ≤ t) :
    (if (!center t && cell t 1) then 1 else 0) = countFrom (fun g => cyl t g) 1 (t / 2) := by
  have hcyl : ∀ g, 1 ≤ g → g ≤ t →
      (cyl t g = true ↔ gapAt cell t g ∧ center t = false ∧ cell t 1 = true) := by
    intro g a b
    rw [cyl_iff t g a, ← cylinder_iff cell_isTraj t g ⟨a, b⟩]
    rfl
  cases hw : (!center t && cell t 1)
  · symm
    apply countFrom_eq_zero
    intro i hi
    cases hc : cyl t (1 + i)
    · rfl
    · obtain ⟨_, h1, h2⟩ := (hcyl (1 + i) (by omega) (by omega)).mp hc
      rw [h1, h2] at hw; exact Bool.noConfusion hw
  · rw [Bool.and_eq_true, Bool.not_eq_true'] at hw
    obtain ⟨g0, h1, h2, hgap⟩ := gap_exists_of_white t ht hw.1
    symm
    apply countFrom_eq_one _ 1 (g0 - 1)
    · omega
    · have e : 1 + (g0 - 1) = g0 := by omega
      show cyl t (1 + (g0 - 1)) = true
      rw [e]; exact (hcyl g0 h1 (by omega)).mpr ⟨hgap, hw.1, hw.2⟩
    · intro i hi hc
      have := gap_unique cell t (1 + i) g0 (by omega) h1
        ((hcyl (1 + i) (by omega) (by omega)).mp hc).1 hgap
      omega

/-- **Counting law.** On the block `I_H = {H + 1, …, 2H}`, the number of white-center,
black-right times is the sum over `t ∈ I_H` of the number of `g ∈ {1, …, t / 2}` whose
cylinder indicator holds (at most one for each `t`), and it equals the number `N11 H` of
words `11` in column `1`. -/
theorem white_black_count (H : Nat) :
    blockCount (fun t => !center t && cell t 1) H
        = natSumFrom (fun t => countFrom (fun g => cyl t g) 1 (t / 2)) (H + 1) H ∧
      blockCount (fun t => !center t && cell t 1) H = N11 H := by
  constructor
  · show countFrom _ (H + 1) H = _
    rw [countFrom_eq_sum]
    apply natSumFrom_congr
    intro i hi
    exact indicator_eq_cyl_count (H + 1 + i) (by omega)
  · unfold N11
    have e : (fun t => !center t && cell t 1) = (fun t => r t && r (t + 1)) := by
      funext t
      cases hr : r t
      · have : cell t 1 = false := hr
        rw [this]; simp
      · rw [center_of_right_black t hr]
        have : cell t 1 = true := hr
        rw [this]; simp
    rw [e]

/-! ### Shifted cylinder law for white-center, white-right times and full white-center block decomposition -/

/-- **White-Center, White-Right Cylinder Law (`cylinder_white_white_iff`):**
for `1 ≤ g ≤ t` and `u = t - g`, the gap at time `t` is `g` and both `x t 0 = false` and
`x t 1 = false` hold if and only if the `2g` cells `x u (-g), …, x u (g - 1)` are all black and
`(x u g || x u (g + 1)) = true`. -/
theorem cylinder_white_white_iff {x : Nat → Int → Bool} (hx : IsTraj x) (t g : Nat)
    (h : 1 ≤ g ∧ g ≤ t) :
    gapAt x t g ∧ x t 0 = false ∧ x t 1 = false ↔
      solid x (t - g) (-(g : Int)) ((g : Int) - 1) ∧
        (x (t - g) (g : Int) || x (t - g) ((g : Int) + 1)) = true := by
  obtain ⟨h1, h2⟩ := h
  have hwi := cylinder_white_iff hx t g ⟨h1, h2⟩
  have hR : gapAt x t g → x t 0 = false →
      x t 1 =
        rule (x (t - g) ((g : Int) - 1)) (x (t - g) (g : Int)) (x (t - g) ((g : Int) + 1)) := by
    intro hgap hc
    obtain ⟨_, hz⟩ := (gapAt_iff x t g h1 h2).mp hgap
    have et : t - g + (g - 1) + 1 = t := by omega
    have hC : lam x ((t : Int) - 2 + 2) (t - g + (g - 1) + 1) = false := by
      rw [et, lam_eq x _ _ 0 (by omega)]; exact hc
    have := right_core hx ((t : Int) - 2) (t - g) (g - 1) hz hC
    rw [et, lam_eq x _ _ 1 (by omega), lam_eq x _ _ ((g : Int) - 1) (by omega),
      lam_eq x _ _ (g : Int) (by omega), lam_eq x _ _ ((g : Int) + 1) (by omega)] at this
    exact this
  have hsol_split : solid x (t - g) (-(g : Int)) ((g : Int) - 1) ↔
      solid x (t - g) (-(g : Int)) ((g : Int) - 2) ∧ x (t - g) ((g : Int) - 1) = true := by
    constructor
    · intro hs
      exact ⟨fun i a b => hs i a (by omega), hs ((g : Int) - 1) (by omega) (Int.le_refl _)⟩
    · intro ⟨hs, hb⟩ i a b
      by_cases hi : i ≤ (g : Int) - 2
      · exact hs i a hi
      · have heq : i = (g : Int) - 1 := by omega
        subst heq; exact hb
  rw [hsol_split]
  constructor
  · intro ⟨hgap, hc, hr⟩
    obtain ⟨hs, hbc⟩ := hwi.mp ⟨hgap, hc⟩
    have hrule := hR hgap hc
    rw [hr] at hrule
    have hbits : x (t - g) ((g : Int) - 1) = true ∧
        (x (t - g) (g : Int) || x (t - g) ((g : Int) + 1)) = true := by
      revert hbc hrule
      cases x (t - g) ((g : Int) - 1) <;> cases x (t - g) (g : Int) <;>
        cases x (t - g) ((g : Int) + 1) <;> simp [rule]
    exact ⟨⟨hs, hbits.1⟩, hbits.2⟩
  · intro ⟨⟨hs, hb1⟩, hcr⟩
    have hbc : (x (t - g) ((g : Int) - 1) || x (t - g) (g : Int)) = true := by
      rw [hb1, Bool.true_or]
    obtain ⟨hgap, hc⟩ := hwi.mpr ⟨hs, hbc⟩
    refine ⟨hgap, hc, ?_⟩
    rw [hR hgap hc, hb1]
    revert hcr
    cases x (t - g) (g : Int) <;> cases x (t - g) ((g : Int) + 1) <;> simp [rule]

/-- The full white-center cylinder indicator at time `t` and gap `g`:
`cell (t - g) (-g), …, cell (t - g) (g - 2)` are black and
`(cell (t - g) (g - 1) || cell (t - g) g) = true`. -/
def cylWhite (t g : Nat) : Bool :=
  (List.range (2 * g - 1)).all (fun k => cell (t - g) (-(g : Int) + k)) &&
    (cell (t - g) ((g : Int) - 1) || cell (t - g) (g : Int))

/-- The white-center, white-right cylinder indicator at time `t` and gap `g`:
`cell (t - g) (-g), …, cell (t - g) (g - 1)` are black and
`(cell (t - g) g || cell (t - g) (g + 1)) = true`. -/
def cylWW (t g : Nat) : Bool :=
  (List.range (2 * g - 1)).all (fun k => cell (t - g) (-(g : Int) + k)) &&
    cell (t - g) ((g : Int) - 1) &&
    (cell (t - g) (g : Int) || cell (t - g) ((g : Int) + 1))

/-- **Disjoint Partition of `cylWhite` into `cyl` and `cylWW` (`cylWhite_decomp`):**
for all `t, g : Nat`, `cylWhite t g = (cyl t g || cylWW t g)` and `(cyl t g && cylWW t g) = false`. -/
theorem cylWhite_decomp (t g : Nat) :
    cylWhite t g = (cyl t g || cylWW t g) ∧ (cyl t g && cylWW t g) = false := by
  unfold cylWhite cyl cylWW
  generalize (List.range (2 * g - 1)).all (fun k => cell (t - g) (-(g : Int) + k)) = S
  generalize cell (t - g) ((g : Int) - 1) = b
  generalize cell (t - g) (g : Int) = c
  generalize cell (t - g) ((g : Int) + 1) = d
  cases S <;> cases b <;> cases c <;> cases d <;> decide

/-- **Characterization of `cylWhite` (`cylWhite_iff`):**
for `1 ≤ g`, `cylWhite t g = true` iff `solid cell (t - g) (-g) (g - 2)` and
`(cell (t - g) (g - 1) || cell (t - g) g) = true`. -/
theorem cylWhite_iff (t g : Nat) (hg : 1 ≤ g) :
    cylWhite t g = true ↔ solid cell (t - g) (-(g : Int)) ((g : Int) - 2) ∧
      (cell (t - g) ((g : Int) - 1) || cell (t - g) (g : Int)) = true := by
  unfold cylWhite
  rw [Bool.and_eq_true, List.all_eq_true]
  apply and_congr_left
  intro _
  constructor
  · intro h i a b
    have := h (i + g).toNat (List.mem_range.mpr (by omega))
    have e : -(g : Int) + ((i + g).toNat : Nat) = i := by omega
    rw [e] at this; exact this
  · intro h k hk
    rw [List.mem_range] at hk
    exact h _ (by omega) (by omega)

/-- **Characterization of `cylWW` (`cylWW_iff`):**
for `1 ≤ g ≤ t`, `cylWW t g = true` iff `gapAt cell t g ∧ center t = false ∧ cell t 1 = false`. -/
theorem cylWW_iff (t g : Nat) (h1 : 1 ≤ g) (h2 : g ≤ t) :
    cylWW t g = true ↔ gapAt cell t g ∧ center t = false ∧ cell t 1 = false := by
  have hcw : cylWhite t g = true ↔ gapAt cell t g ∧ center t = false := by
    rw [cylWhite_iff t g h1, ← cylinder_white_iff cell_isTraj t g ⟨h1, h2⟩]
    rfl
  have hcb : cyl t g = true ↔ gapAt cell t g ∧ center t = false ∧ cell t 1 = true := by
    rw [cyl_iff t g h1, ← cylinder_iff cell_isTraj t g ⟨h1, h2⟩]
    rfl
  rcases cylWhite_decomp t g with ⟨hor, hand⟩
  constructor
  · intro hww
    have hwhite : cylWhite t g = true := by rw [hor, hww, Bool.or_true]
    have hnotb : cyl t g = false := by
      rw [hww, Bool.and_true] at hand; exact hand
    obtain ⟨hgap, hc⟩ := hcw.mp hwhite
    refine ⟨hgap, hc, ?_⟩
    cases h1b : cell t 1
    · rfl
    · have : cyl t g = true := hcb.mpr ⟨hgap, hc, h1b⟩
      rw [hnotb] at this; exact Bool.noConfusion this
  · intro ⟨hgap, hc, hr⟩
    have hwhite : cylWhite t g = true := hcw.mpr ⟨hgap, hc⟩
    have hnotb : cyl t g = false := by
      cases hb : cyl t g
      · rfl
      · obtain ⟨_, _, h1t⟩ := hcb.mp hb
        rw [hr] at h1t; exact Bool.noConfusion h1t
    rw [hor, hnotb, Bool.false_or] at hwhite
    exact hwhite

/-- **Full White-Center Indicator Identity (`indicator_white_eq_cylWhite_count`):**
for `t ≥ 2`, the white-center indicator `if !center t then 1 else 0` equals the number of
`g ∈ {1, …, t / 2}` with `cylWhite t g = true`. -/
theorem indicator_white_eq_cylWhite_count (t : Nat) (ht : 2 ≤ t) :
    (if !center t then 1 else 0) = countFrom (fun g => cylWhite t g) 1 (t / 2) := by
  have hcw : ∀ g, 1 ≤ g → g ≤ t →
      (cylWhite t g = true ↔ gapAt cell t g ∧ center t = false) := by
    intro g a b
    rw [cylWhite_iff t g a, ← cylinder_white_iff cell_isTraj t g ⟨a, b⟩]
    rfl
  cases hw : (!center t)
  · symm
    apply countFrom_eq_zero
    intro i hi
    cases hc : cylWhite t (1 + i)
    · rfl
    · obtain ⟨_, h1⟩ := (hcw (1 + i) (by omega) (by omega)).mp hc
      rw [h1] at hw; exact Bool.noConfusion hw
  · rw [Bool.not_eq_true'] at hw
    obtain ⟨g0, h1, h2, hgap⟩ := gap_exists_of_white t ht hw
    symm
    apply countFrom_eq_one _ 1 (g0 - 1)
    · omega
    · have e : 1 + (g0 - 1) = g0 := by omega
      show cylWhite t (1 + (g0 - 1)) = true
      rw [e]; exact (hcw g0 h1 (by omega)).mpr ⟨hgap, hw⟩
    · intro i hi hc
      have := gap_unique cell t (1 + i) g0 (by omega) h1
        ((hcw (1 + i) (by omega) (by omega)).mp hc).1 hgap
      omega

/-- **White-Center, White-Right Indicator Identity (`indicator_ww_eq_cylWW_count`):**
for `t ≥ 2`, the white-center, white-right indicator `if (!center t && !cell t 1) then 1 else 0`
equals the number of `g ∈ {1, …, t / 2}` with `cylWW t g = true`. -/
theorem indicator_ww_eq_cylWW_count (t : Nat) (ht : 2 ≤ t) :
    (if (!center t && !cell t 1) then 1 else 0) = countFrom (fun g => cylWW t g) 1 (t / 2) := by
  cases hw : (!center t && !cell t 1)
  · symm
    apply countFrom_eq_zero
    intro i hi
    cases hc : cylWW t (1 + i)
    · rfl
    · obtain ⟨_, h1, h2⟩ := (cylWW_iff t (1 + i) (by omega) (by omega)).mp hc
      rw [h1, h2] at hw; exact Bool.noConfusion hw
  · rw [Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true'] at hw
    obtain ⟨g0, h1, h2, hgap⟩ := gap_exists_of_white t ht hw.1
    symm
    apply countFrom_eq_one _ 1 (g0 - 1)
    · omega
    · have e : 1 + (g0 - 1) = g0 := by omega
      show cylWW t (1 + (g0 - 1)) = true
      rw [e]; exact (cylWW_iff t g0 h1 (by omega)).mpr ⟨hgap, hw.1, hw.2⟩
    · intro i hi hc
      have := gap_unique cell t (1 + i) g0 (by omega) h1
        ((cylWW_iff t (1 + i) (by omega) (by omega)).mp hc).1 hgap
      omega

/-- **Block Counting Law for White Center Cells and White-White Pairs (`white_and_ww_block_count`):**
on `I_H = {H + 1, …, 2H}`, `blockCount (fun t => !center t) H` equals the sum of `cylWhite`
counts and `blockCount (fun t => !center t && !cell t 1) H` equals the sum of `cylWW` counts. -/
theorem white_and_ww_block_count (H : Nat) :
    blockCount (fun t => !center t) H =
      natSumFrom (fun t => countFrom (fun g => cylWhite t g) 1 (t / 2)) (H + 1) H ∧
    blockCount (fun t => !center t && !cell t 1) H =
      natSumFrom (fun t => countFrom (fun g => cylWW t g) 1 (t / 2)) (H + 1) H := by
  constructor
  · show countFrom _ (H + 1) H = _
    rw [countFrom_eq_sum]
    apply natSumFrom_congr
    intro i hi
    exact indicator_white_eq_cylWhite_count (H + 1 + i) (by omega)
  · show countFrom _ (H + 1) H = _
    rw [countFrom_eq_sum]
    apply natSumFrom_congr
    intro i hi
    exact indicator_ww_eq_cylWW_count (H + 1 + i) (by omega)

end Ruliology.CellularAutomata.Rule30CenterCylinders
