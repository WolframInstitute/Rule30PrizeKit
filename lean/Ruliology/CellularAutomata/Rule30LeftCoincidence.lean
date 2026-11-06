module
public import Ruliology.CellularAutomata.Rule30Prize
public import Ruliology.CellularAutomata.Rule30LeftReset

/-!
# The farther parent and the coincidence criterion of the left reset recurrence (F1–F3)

`Rule30LeftReset` studies the recurrence `x (t + 1) = a t ⊕ (b t ∨ x t)`: a child `x` driven by a nearer word `b` and a
farther word `a`. The left diagonals of the single-cell pattern obey it (`Rule30Diagonals.D_step`: the child `D (j + 2)`,
the nearer `D (j + 1)`, the farther `D j`). This module adds three facts about it, for arbitrary words in natural time.

* `closed_form` (F1): after a black nearer bit at `r` and a white run of the nearer word on `(r, t]`, the child is the
  complemented parity of the farther word over `r … t`: `x (t + 1) = ¬ par a r (t + 1 - r)`. This packages the kit's reset
  step with `accum` on a bounded run.
* `farther_of_child`, `farther_unique`, `solutions_agree` (F2): the farther word is recovered from the child and the
  nearer word, `a t = x (t + 1) ⊕ (b t ∨ x t)`, for any triple; and two children of the same farther and nearer words
  agree from `s0 + 1` on once `b s0` is black. With the kit's `reset_periodic` this is the bijection between periodic
  farther words and periodic children whenever the nearer word has a black.
* `coincidence_iff` (F3): if `b s0` is black, the child equals the nearer word from `s0 + 1` on iff the farther word is the
  nearer word's difference `b t ⊕ b (t + 1)` from `s0` on. No periodicity is needed.
* `white_of_coincidence`, `evwhite_iff_eventually_eq` (Lemma E): if the farther word equals the nearer word from some
  time on, the child falls to white at the next black of the nearer word; so, when the nearer word has blacks arbitrarily
  late, the child is eventually white iff its parents eventually coincide (the forward way is the kit's `white_forces_eq`).
* `D_closed_form`, `D_farther_of_child`, `D_coincidence_iff`, `D_white_of_coincidence`, `D_evwhite_iff_eventually_eq`:
  the same for the left diagonals. With the kit's
  `D_white_of_eq`, a white diagonal `D (j + 3)` forces `D (j + 1) = D (j + 2)`, and that coincidence holds after a black of
  `D (j + 1)` iff `D j` is the difference of `D (j + 1)` there: one farther diagonal for each nearer one.

The statements and their hand proofs were proposed in the contributors' record by Claude (Anthropic); the reset and
the accumulation are the kit's. Nothing here concerns the centre column or the Prize problems.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30LeftCoincidence

set_option autoImplicit false

open Rule30LeftReset Rule30Diagonals

section Generic
variable {x a b : Nat → Bool}

/-- The parity of `a r, …, a (r + n)` peeled from the front. -/
theorem par_cons (a : Nat → Bool) (r : Nat) : ∀ n, par a r (n + 1) = xor (a r) (par a (r + 1) n)
  | 0 => by simp [par]
  | n + 1 => by
    have ih := par_cons a r n
    show xor (par a r (n + 1)) (a (r + (n + 1))) = xor (a r) (xor (par a (r + 1) n) (a (r + 1 + n)))
    rw [ih, show r + (n + 1) = r + 1 + n by omega]
    cases a r <;> cases par a (r + 1) n <;> cases a (r + 1 + n) <;> rfl

/-- One reset step: a black nearer bit sets the child to the complement of the farther bit. -/
theorem reset_step (hx : ∀ t, x (t + 1) = xor (a t) (b t || x t)) {r : Nat} (hr : b r = true) :
    x (r + 1) = !a r := by
  rw [hx, hr]
  cases a r <;> rfl

/-- Accumulation of the farther word over a bounded white run of the nearer word. -/
theorem accum_upto (hx : ∀ t, x (t + 1) = xor (a t) (b t || x t)) (r : Nat) :
    ∀ n, (∀ k, r < k → k ≤ r + n → b k = false) → x (r + 1 + n) = xor (x (r + 1)) (par a (r + 1) n)
  | 0, _ => by simp [par]
  | n + 1, hw => by
    have ih := accum_upto hx r n (fun k h1 h2 => hw k h1 (by omega))
    rw [show r + 1 + (n + 1) = (r + 1 + n) + 1 by omega, hx, hw (r + 1 + n) (by omega) (by omega), ih]
    simp only [par, Bool.false_or]
    cases a (r + 1 + n) <;> cases x (r + 1) <;> cases par a (r + 1) n <;> rfl

/-- **F1, the closed form.** After a black nearer bit at `r` and a white run of the nearer word on `(r, t]`, the child at
`t + 1` is the complemented parity of the farther word over `r … t`. -/
theorem closed_form (hx : ∀ t, x (t + 1) = xor (a t) (b t || x t)) {r t : Nat} (hrt : r ≤ t) (hr : b r = true)
    (hw : ∀ k, r < k → k ≤ t → b k = false) : x (t + 1) = !(par a r (t + 1 - r)) := by
  obtain ⟨n, rfl⟩ : ∃ n, t = r + n := ⟨t - r, by omega⟩
  have h := accum_upto hx r n (fun k h1 h2 => hw k h1 h2)
  rw [show r + n + 1 = r + 1 + n by omega, h, reset_step hx hr, show r + 1 + n - r = n + 1 by omega, par_cons]
  cases a r <;> cases par a (r + 1) n <;> rfl

/-- **F2, recovery.** The farther word is determined by the child and the nearer word, for any triple. -/
theorem farther_of_child (hx : ∀ t, x (t + 1) = xor (a t) (b t || x t)) (t : Nat) :
    a t = xor (x (t + 1)) (b t || x t) := by
  rw [hx]
  cases a t <;> cases (b t || x t) <;> rfl

/-- Two farther words with the same child and the same nearer word are equal. -/
theorem farther_unique {a' : Nat → Bool} (hx : ∀ t, x (t + 1) = xor (a t) (b t || x t))
    (hx' : ∀ t, x (t + 1) = xor (a' t) (b t || x t)) : a = a' := by
  funext t
  rw [farther_of_child hx t, farther_of_child hx' t]

/-- **F2, uniqueness.** Two children of the same farther and nearer words agree from `s0 + 1` on once `b s0` is black. -/
theorem solutions_agree {x' : Nat → Bool} (hx : ∀ t, x (t + 1) = xor (a t) (b t || x t))
    (hx' : ∀ t, x' (t + 1) = xor (a t) (b t || x' t)) {s0 : Nat} (hs : b s0 = true) :
    ∀ t, s0 + 1 ≤ t → x t = x' t := by
  intro t ht
  obtain ⟨n, rfl⟩ : ∃ n, t = s0 + 1 + n := ⟨t - (s0 + 1), by omega⟩
  clear ht
  induction n with
  | zero => rw [Nat.add_zero, reset_step hx hs, reset_step hx' hs]
  | succ n ih => rw [show s0 + 1 + (n + 1) = (s0 + 1 + n) + 1 by omega, hx, hx', ih]

/-- **F3, the coincidence criterion.** If `b s0` is black, the child equals the nearer word from `s0 + 1` on iff the
farther word is the nearer word's difference `b t ⊕ b (t + 1)` from `s0` on. -/
theorem coincidence_iff (hx : ∀ t, x (t + 1) = xor (a t) (b t || x t)) {s0 : Nat} (hs : b s0 = true) :
    (∀ t, s0 + 1 ≤ t → x t = b t) ↔ (∀ t, s0 ≤ t → a t = xor (b t) (b (t + 1))) := by
  constructor
  · intro h t ht
    rw [farther_of_child hx t, h (t + 1) (by omega)]
    rcases Nat.lt_or_eq_of_le ht with hlt | heq
    · rw [h t (by omega)]
      cases b t <;> cases b (t + 1) <;> rfl
    · subst heq
      rw [hs]
      cases b (s0 + 1) <;> rfl
  · intro h t ht
    obtain ⟨n, rfl⟩ : ∃ n, t = s0 + 1 + n := ⟨t - (s0 + 1), by omega⟩
    clear ht
    induction n with
    | zero =>
      rw [Nat.add_zero, reset_step hx hs, h s0 (Nat.le_refl _), hs]
      cases b (s0 + 1) <;> rfl
    | succ n ih =>
      rw [show s0 + 1 + (n + 1) = (s0 + 1 + n) + 1 by omega, hx, ih, h (s0 + 1 + n) (by omega)]
      cases b (s0 + 1 + n) <;> cases b (s0 + 1 + n + 1) <;> rfl

/-- **Lemma E, the converse direction.** If the farther word equals the nearer word from `s` on, then each step reads
`x (t + 1) = ¬ b t ∧ x t`, so the child can only fall, and it is white from `s1 + 1` on after a black `b s1` with `s ≤ s1`. -/
theorem white_of_coincidence (hx : ∀ t, x (t + 1) = xor (a t) (b t || x t)) {s s1 : Nat}
    (heq : ∀ t, s ≤ t → a t = b t) (hs : s ≤ s1) (h1 : b s1 = true) : ∀ t, s1 + 1 ≤ t → x t = false := by
  intro t ht
  obtain ⟨n, rfl⟩ : ∃ n, t = s1 + 1 + n := ⟨t - (s1 + 1), by omega⟩
  clear ht
  induction n with
  | zero => rw [Nat.add_zero, hx, heq s1 hs, h1]; rfl
  | succ n ih =>
    rw [show s1 + 1 + (n + 1) = (s1 + 1 + n) + 1 by omega, hx, heq _ (by omega), ih]
    cases b (s1 + 1 + n) <;> rfl

/-- **Lemma E both ways.** If the nearer word has blacks arbitrarily late, the child is eventually white iff the farther
word eventually equals the nearer word. The forward direction is the kit's `white_forces_eq`. -/
theorem evwhite_iff_eventually_eq (hx : ∀ t, x (t + 1) = xor (a t) (b t || x t))
    (hb : ∀ T, ∃ t, T ≤ t ∧ b t = true) : EvWhite x ↔ ∃ s, ∀ t, s ≤ t → a t = b t := by
  constructor
  · rintro ⟨T, hT⟩
    exact ⟨T, white_forces_eq hx hT⟩
  · rintro ⟨s, heq⟩
    obtain ⟨s1, hs, h1⟩ := hb s
    exact ⟨s1 + 1, white_of_coincidence hx heq hs h1⟩

end Generic

/-! ### The left diagonals -/

/-- F1 for the left diagonals. -/
theorem D_closed_form {j r t : Nat} (hrt : r ≤ t) (hr : D (j + 1) r = true)
    (hw : ∀ k, r < k → k ≤ t → D (j + 1) k = false) : D (j + 2) (t + 1) = !(par (D j) r (t + 1 - r)) :=
  closed_form (x := D (j + 2)) (a := D j) (b := D (j + 1)) (D_step j) hrt hr hw

/-- F2 for the left diagonals: each diagonal is recovered from the next two. -/
theorem D_farther_of_child (j t : Nat) : D j t = xor (D (j + 2) (t + 1)) (D (j + 1) t || D (j + 2) t) :=
  farther_of_child (x := D (j + 2)) (a := D j) (b := D (j + 1)) (D_step j) t

/-- Lemma E's converse for the left diagonals: if `D j = D (j + 1)` from `s` on and `D (j + 1)` is black at `s1 ≥ s`, then
`D (j + 2)` is white from `s1 + 1` on. -/
theorem D_white_of_coincidence {j s s1 : Nat} (heq : ∀ t, s ≤ t → D j t = D (j + 1) t) (hs : s ≤ s1)
    (h1 : D (j + 1) s1 = true) : ∀ t, s1 + 1 ≤ t → D (j + 2) t = false :=
  white_of_coincidence (x := D (j + 2)) (a := D j) (b := D (j + 1)) (D_step j) heq hs h1

/-- Lemma E both ways for the left diagonals, when `D (j + 1)` has blacks arbitrarily late. -/
theorem D_evwhite_iff_eventually_eq {j : Nat} (hb : ∀ T, ∃ t, T ≤ t ∧ D (j + 1) t = true) :
    EvWhite (D (j + 2)) ↔ ∃ s, ∀ t, s ≤ t → D j t = D (j + 1) t :=
  evwhite_iff_eventually_eq (x := D (j + 2)) (a := D j) (b := D (j + 1)) (D_step j) hb

/-- F3 for the left diagonals: after a black of `D (j + 1)` at `s0`, `D (j + 2)` coincides with `D (j + 1)` iff `D j` is
the difference of `D (j + 1)`. -/
theorem D_coincidence_iff {j s0 : Nat} (hs : D (j + 1) s0 = true) :
    (∀ t, s0 + 1 ≤ t → D (j + 2) t = D (j + 1) t) ↔
      (∀ t, s0 ≤ t → D j t = xor (D (j + 1) t) (D (j + 1) (t + 1))) :=
  coincidence_iff (x := D (j + 2)) (a := D j) (b := D (j + 1)) (D_step j) hs

/-! ### Cofinal-Black Duality, Four-Diagonal Coincidence Exclusion, and Difference-Operator Period Transfer -/

/-- **Cofinal Black Cells from `¬ EvWhite` (`exists_true_ge_of_not_evWhite`):** if a Boolean sequence
`b : Nat → Bool` is not eventually white (`¬ EvWhite b`), then for every threshold `T : Nat` there
exists `t ≥ T` such that `b t = true`. -/
theorem exists_true_ge_of_not_evWhite {b : Nat → Bool} (hnot : ¬ EvWhite b) (T : Nat) :
    ∃ t, T ≤ t ∧ b t = true := by
  refine Classical.byContradiction fun hne => hnot ⟨T, fun t ht => ?_⟩
  cases hb : b t
  · rfl
  · exact False.elim (hne ⟨t, ht, hb⟩)

/-- **Lemma E Under `¬ EvWhite b` (`evwhite_iff_eventually_eq_of_not_evWhite`):** for any reset
triple `x (t + 1) = xor (a t) (b t || x t)` with `¬ EvWhite b`, the child `x` is eventually white
if and only if the parents `a` and `b` eventually coincide. -/
theorem evwhite_iff_eventually_eq_of_not_evWhite {x a b : Nat → Bool}
    (hx : ∀ t, x (t + 1) = xor (a t) (b t || x t)) (hb : ¬ EvWhite b) :
    EvWhite x ↔ ∃ s, ∀ t, s ≤ t → a t = b t :=
  evwhite_iff_eventually_eq hx (exists_true_ge_of_not_evWhite hb)

/-- **Left-Diagonal Lemma E Under `¬ EvWhite (D (j + 1))` (`D_evwhite_iff_eventually_eq_of_not_evWhite`):**
whenever `¬ EvWhite (D (j + 1))`, `EvWhite (D (j + 2))` holds if and only if `D j` and `D (j + 1)`
eventually coincide. -/
theorem D_evwhite_iff_eventually_eq_of_not_evWhite {j : Nat} (hb : ¬ EvWhite (D (j + 1))) :
    EvWhite (D (j + 2)) ↔ ∃ s, ∀ t, s ≤ t → D j t = D (j + 1) t :=
  D_evwhite_iff_eventually_eq (exists_true_ge_of_not_evWhite hb)

/-- **Unconditional Dichotomy of Diagonal Coincidence (`D_evWhite_or_evWhite_of_eventually_eq`):**
for every diagonal index `j : Nat`, if `D j` and `D (j + 1)` eventually coincide
(`∃ s, ∀ t ≥ s, D j t = D (j + 1) t`), then either `EvWhite (D (j + 1))` or `EvWhite (D (j + 2))`. -/
theorem D_evWhite_or_evWhite_of_eventually_eq {j : Nat}
    (heq : ∃ s, ∀ t, s ≤ t → D j t = D (j + 1) t) :
    EvWhite (D (j + 1)) ∨ EvWhite (D (j + 2)) := by
  by_cases hb : EvWhite (D (j + 1))
  · exact Or.inl hb
  · exact Or.inr ((D_evwhite_iff_eventually_eq_of_not_evWhite hb).mpr heq)

/-- **Three Eventually Coinciding Consecutive Diagonals Force `EvWhite (D (j + 2))`
(`D_evWhite_two_of_three_eventually_eq`):** for every `j : Nat`, if `D j`, `D (j + 1)`, and `D (j + 2)`
all eventually coincide, then `EvWhite (D (j + 2))` holds (and both `¬ EvWhite (D (j + 1))` and
`¬ EvWhite (D (j + 3))` hold). -/
theorem D_evWhite_two_of_three_eventually_eq {j : Nat}
    (heq01 : ∃ s, ∀ t, s ≤ t → D j t = D (j + 1) t)
    (heq12 : ∃ s, ∀ t, s ≤ t → D (j + 1) t = D (j + 2) t) :
    EvWhite (D (j + 2)) ∧ ¬ EvWhite (D (j + 1)) ∧ ¬ EvWhite (D (j + 3)) := by
  have hw2 : EvWhite (D (j + 2)) := by
    rcases D_evWhite_or_evWhite_of_eventually_eq heq01 with hw1 | hw2
    · obtain ⟨s1, hs1⟩ := hw1
      obtain ⟨s2, hs2⟩ := heq12
      exact ⟨s1 + s2, fun t ht => by rw [← hs2 t (by omega), hs1 t (by omega)]⟩
    · exact hw2
  refine ⟨hw2, ?_, ?_⟩
  · exact fun hw1 => no_two_consecutive_evwhite (j + 1) ⟨hw1, hw2⟩
  · exact fun hw3 => no_two_consecutive_evwhite (j + 2) ⟨hw2, hw3⟩

/-- **Unconditional Exclusion of Four Eventually Coinciding Consecutive Left Diagonals
(`D_no_four_eventually_eq`):** for every `j : Nat`, it is impossible for four consecutive left
diagonals `D j`, `D (j + 1)`, `D (j + 2)`, and `D (j + 3)` to eventually coincide. -/
theorem D_no_four_eventually_eq (j : Nat) :
    ¬ ∃ s, ∀ t, s ≤ t → D j t = D (j + 1) t ∧ D (j + 1) t = D (j + 2) t ∧ D (j + 2) t = D (j + 3) t := by
  rintro ⟨s, hs⟩
  have heq01 : ∃ s, ∀ t, s ≤ t → D j t = D (j + 1) t := ⟨s, fun t ht => (hs t ht).1⟩
  have heq12 : ∃ s, ∀ t, s ≤ t → D (j + 1) t = D (j + 2) t := ⟨s, fun t ht => (hs t ht).2.1⟩
  have heq23 : ∃ s, ∀ t, s ≤ t → D (j + 2) t = D (j + 3) t := ⟨s, fun t ht => (hs t ht).2.2⟩
  have h1 := D_evWhite_two_of_three_eventually_eq heq01 heq12
  have h2 := D_evWhite_two_of_three_eventually_eq (j := j + 1) heq12 heq23
  exact h1.2.2 h2.1

/-- **Period Transfer Under Nearer-Child Coincidence (`coincidence_farther_periodic_of_periodic`):**
if `b s0 = true`, `x` and `b` coincide from `s0 + 1` on, and `b` has period `L` from `s0` on, then
the farther word `a` also has period `L` from `s0` on. -/
theorem coincidence_farther_periodic_of_periodic {x a b : Nat → Bool}
    (hx : ∀ t, x (t + 1) = xor (a t) (b t || x t)) {s0 L : Nat} (hs : b s0 = true)
    (hco : ∀ t, s0 + 1 ≤ t → x t = b t) (hb : ∀ t, s0 ≤ t → b (t + L) = b t) :
    ∀ t, s0 ≤ t → a (t + L) = a t := by
  have hd := (coincidence_iff hx hs).mp hco
  intro t ht
  rw [hd (t + L) (by omega), hd t ht, hb t ht,
    show t + L + 1 = (t + 1) + L by omega, hb (t + 1) (by omega)]

/-- **Antiperiod-to-Period Transfer Under Nearer-Child Coincidence (`coincidence_farther_periodic_of_antiperiodic`):**
if `b s0 = true`, `x` and `b` coincide from `s0 + 1` on, and `b` is `L`-antiperiodic from `s0` on
(`b (t + L) = !b t`), then the farther word `a` is `L`-periodic from `s0` on (`a (t + L) = a t`). -/
theorem coincidence_farther_periodic_of_antiperiodic {x a b : Nat → Bool}
    (hx : ∀ t, x (t + 1) = xor (a t) (b t || x t)) {s0 L : Nat} (hs : b s0 = true)
    (hco : ∀ t, s0 + 1 ≤ t → x t = b t) (hb : ∀ t, s0 ≤ t → b (t + L) = !b t) :
    ∀ t, s0 ≤ t → a (t + L) = a t := by
  have hd := (coincidence_iff hx hs).mp hco
  intro t ht
  rw [hd (t + L) (by omega), hd t ht, hb t ht,
    show t + L + 1 = (t + 1) + L by omega, hb (t + 1) (by omega)]
  cases b t <;> cases b (t + 1) <;> rfl

/-- **Left-Diagonal Period Transfer Under Coincidence (`D_coincidence_farther_periodic`):**
if `D (j + 1) s0 = true`, `D (j + 2)` coincides with `D (j + 1)` from `s0 + 1` on, and `D (j + 1)`
has period `L` from `s0` on, then `D j` has period `L` from `s0` on. -/
theorem D_coincidence_farther_periodic {j s0 L : Nat} (hs : D (j + 1) s0 = true)
    (hco : ∀ t, s0 + 1 ≤ t → D (j + 2) t = D (j + 1) t)
    (hb : ∀ t, s0 ≤ t → D (j + 1) (t + L) = D (j + 1) t) :
    ∀ t, s0 ≤ t → D j (t + L) = D j t :=
  coincidence_farther_periodic_of_periodic (D_step j) hs hco hb

/-- **Left-Diagonal Antiperiod-to-Period Transfer Under Coincidence (`D_coincidence_farther_periodic_of_antiperiodic`):**
if `D (j + 1) s0 = true`, `D (j + 2)` coincides with `D (j + 1)` from `s0 + 1` on, and `D (j + 1)`
is `L`-antiperiodic from `s0` on, then `D j` is `L`-periodic from `s0` on. -/
theorem D_coincidence_farther_periodic_of_antiperiodic {j s0 L : Nat} (hs : D (j + 1) s0 = true)
    (hco : ∀ t, s0 + 1 ≤ t → D (j + 2) t = D (j + 1) t)
    (hb : ∀ t, s0 ≤ t → D (j + 1) (t + L) = !D (j + 1) t) :
    ∀ t, s0 ≤ t → D j (t + L) = D j t :=
  coincidence_farther_periodic_of_antiperiodic (D_step j) hs hco hb

/-- **Two-Step Retrodiction of Left Diagonals (`D_two_step_retrodiction`):** every left diagonal bit
`D j t` is uniquely determined by `D (j + 1) t`, `D (j + 2) t`, `D (j + 3) (t + 1)`, `D (j + 4) (t + 1)`,
and `D (j + 4) (t + 2)` via two applications of `D_farther_of_child`. -/
theorem D_two_step_retrodiction (j t : Nat) :
    D j t = xor (xor (D (j + 2 + 2) (t + 1 + 1)) (D (j + 2 + 1) (t + 1) || D (j + 2 + 2) (t + 1)))
      (D (j + 1) t || D (j + 2) t) := by
  rw [D_farther_of_child j t, D_farther_of_child (j + 2) (t + 1)]

/-! ### Exact `L`-Step XOR Divided-Difference Law Under Periodic Nearer and Anti-Periodic Parent Diagonals -/

/-- **Exact `L`-Step Shift Law Under Periodic Nearer Child and Anti-Periodic Parent
(`farther_shift_eq_xor_of_periodic_and_antiperiodic`):** if
`∀ t, x (t + 1) = xor (a t) (b t || x t)`, `∀ t ≥ s0, b (t + L) = b t`, and
`∀ t ≥ s0, x (t + L) = !x t`, then `∀ t ≥ s0, a (t + L) = xor (a t) (b t)`. -/
theorem farther_shift_eq_xor_of_periodic_and_antiperiodic {x a b : Nat → Bool}
    (hx : ∀ t : Nat, x (t + 1) = xor (a t) (b t || x t)) {s0 L : Nat}
    (hb : ∀ t : Nat, s0 ≤ t → b (t + L) = b t)
    (hanti : ∀ t : Nat, s0 ≤ t → x (t + L) = !x t) :
    ∀ t : Nat, s0 ≤ t → a (t + L) = xor (a t) (b t) := by
  intro t ht
  have ha1 : a t = xor (x (t + 1)) (b t || x t) := by
    rw [hx t]; cases a t <;> cases (b t || x t) <;> rfl
  have ha2 : a (t + L) = xor (x (t + L + 1)) (b (t + L) || x (t + L)) := by
    rw [hx (t + L)]; cases a (t + L) <;> cases (b (t + L) || x (t + L)) <;> rfl
  have hx1 : x (t + L + 1) = !x (t + 1) := by
    rw [show t + L + 1 = (t + 1) + L by omega]
    exact hanti (t + 1) (by omega)
  rw [ha2, ha1, hx1, hb t ht, hanti t ht]
  cases b t <;> cases x t <;> cases x (t + 1) <;> rfl

/-- **Exact Reconstruction of the Nearer Child as the `L`-Step Divided Difference of the Farther
Child (`nearer_eq_xor_farther_shift_of_periodic_and_antiperiodic`):** under the hypotheses of
`farther_shift_eq_xor_of_periodic_and_antiperiodic`, `∀ t ≥ s0, b t = xor (a t) (a (t + L))`. -/
theorem nearer_eq_xor_farther_shift_of_periodic_and_antiperiodic {x a b : Nat → Bool}
    (hx : ∀ t : Nat, x (t + 1) = xor (a t) (b t || x t)) {s0 L : Nat}
    (hb : ∀ t : Nat, s0 ≤ t → b (t + L) = b t)
    (hanti : ∀ t : Nat, s0 ≤ t → x (t + L) = !x t) :
    ∀ t : Nat, s0 ≤ t → b t = xor (a t) (a (t + L)) := by
  intro t ht
  rw [farther_shift_eq_xor_of_periodic_and_antiperiodic hx hb hanti t ht]
  cases a t <;> cases b t <;> rfl

/-- **Left-Diagonal `L`-Step Divided-Difference Law (`D_shift_eq_xor_of_periodic_and_antiperiodic`):**
if `D (j + 1)` is `L`-periodic from `s0` on and `D (j + 2)` is `L`-anti-periodic from `s0` on,
then `∀ t ≥ s0, D j (t + L) = xor (D j t) (D (j + 1) t)`. -/
theorem D_shift_eq_xor_of_periodic_and_antiperiodic {j s0 L : Nat}
    (hb : ∀ t : Nat, s0 ≤ t → D (j + 1) (t + L) = D (j + 1) t)
    (hanti : ∀ t : Nat, s0 ≤ t → D (j + 2) (t + L) = !D (j + 2) t) :
    ∀ t : Nat, s0 ≤ t → D j (t + L) = xor (D j t) (D (j + 1) t) :=
  farther_shift_eq_xor_of_periodic_and_antiperiodic (D_step j) hb hanti

/-- **Exact Equivalence Between `L`-Periodicity of `D j` and Eventual Whiteness of `D (j + 1)`
(`D_periodic_iff_nearer_white_of_periodic_and_antiperiodic`):** when `D (j + 1)` is `L`-periodic
from `s0` on and `D (j + 2)` is `L`-anti-periodic from `s0` on, `D j` is `L`-periodic from `s0`
on if and only if `∀ t ≥ s0, D (j + 1) t = false`. -/
theorem D_periodic_iff_nearer_white_of_periodic_and_antiperiodic {j s0 L : Nat}
    (hb : ∀ t : Nat, s0 ≤ t → D (j + 1) (t + L) = D (j + 1) t)
    (hanti : ∀ t : Nat, s0 ≤ t → D (j + 2) (t + L) = !D (j + 2) t) :
    (∀ t : Nat, s0 ≤ t → D j (t + L) = D j t) ↔ (∀ t : Nat, s0 ≤ t → D (j + 1) t = false) := by
  constructor
  · intro hper t ht
    have hxor := D_shift_eq_xor_of_periodic_and_antiperiodic hb hanti t ht
    rw [hper t ht] at hxor
    revert hxor; cases D j t <;> cases D (j + 1) t <;> decide
  · intro hwhite t ht
    rw [D_shift_eq_xor_of_periodic_and_antiperiodic hb hanti t ht, hwhite t ht, Bool.xor_false]

/-- **Exact Equivalence Between `L`-Anti-Periodicity of `D j` and Eventual Blackness of
`D (j + 1)` (`D_antiperiodic_iff_nearer_black_of_periodic_and_antiperiodic`):** when `D (j + 1)`
is `L`-periodic from `s0` on and `D (j + 2)` is `L`-anti-periodic from `s0` on, `D j` is
`L`-anti-periodic from `s0` on if and only if `∀ t ≥ s0, D (j + 1) t = true`. -/
theorem D_antiperiodic_iff_nearer_black_of_periodic_and_antiperiodic {j s0 L : Nat}
    (hb : ∀ t : Nat, s0 ≤ t → D (j + 1) (t + L) = D (j + 1) t)
    (hanti : ∀ t : Nat, s0 ≤ t → D (j + 2) (t + L) = !D (j + 2) t) :
    (∀ t : Nat, s0 ≤ t → D j (t + L) = !D j t) ↔ (∀ t : Nat, s0 ≤ t → D (j + 1) t = true) := by
  constructor
  · intro hanti_j t ht
    have hxor := D_shift_eq_xor_of_periodic_and_antiperiodic hb hanti t ht
    rw [hanti_j t ht] at hxor
    revert hxor; cases D j t <;> cases D (j + 1) t <;> decide
  · intro hblack t ht
    rw [D_shift_eq_xor_of_periodic_and_antiperiodic hb hanti t ht, hblack t ht]
    cases D j t <;> rfl

/-- **Unconditional `(2 * L)`-Periodicity of `D j` Under `L`-Periodic `D (j + 1)` and
`L`-Anti-Periodic `D (j + 2)` (`D_two_mul_periodic_of_periodic_and_antiperiodic`):** whenever
`D (j + 1)` is `L`-periodic from `s0` on and `D (j + 2)` is `L`-anti-periodic from `s0` on,
`D j` is `(2 * L)`-periodic from `s0` on (`∀ t ≥ s0, D j (t + 2 * L) = D j t`). -/
theorem D_two_mul_periodic_of_periodic_and_antiperiodic {j s0 L : Nat}
    (hb : ∀ t : Nat, s0 ≤ t → D (j + 1) (t + L) = D (j + 1) t)
    (hanti : ∀ t : Nat, s0 ≤ t → D (j + 2) (t + L) = !D (j + 2) t) :
    ∀ t : Nat, s0 ≤ t → D j (t + 2 * L) = D j t := by
  intro t ht
  have h2L : t + 2 * L = (t + L) + L := by omega
  rw [h2L,
    D_shift_eq_xor_of_periodic_and_antiperiodic hb hanti (t + L) (by omega),
    D_shift_eq_xor_of_periodic_and_antiperiodic hb hanti t ht,
    hb t ht]
  cases D j t <;> cases D (j + 1) t <;> rfl

end Ruliology.CellularAutomata.Rule30LeftCoincidence
