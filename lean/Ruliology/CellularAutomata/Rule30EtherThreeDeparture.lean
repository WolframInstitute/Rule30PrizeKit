module

public import Ruliology.CellularAutomata.Rule30EtherThreeErosion

/-!
# Leaving the period-3 ether: one path and an exact time

Setting of `Rule30EtherThreeErosion`: `F` is a rule-30 evolution of the columns `p ≥ 1` whose column `0` is ether column
`j0` with phase offset `s`. That column may read either word of least period three. The *front* is the first column that
differs from the ether; its state is the class of its column and whether the next column differs too. `wake_good` proves
that from a good front `5 D + 2 t + ψ` does not increase.

* Thirteen of the good states are closed (`IsRec`), and from a recurrent front `5 D + 2 t + ψ`, with `ψ` the class itself
  (and `2` for one state), is **exactly conserved** until the front reaches column `1`, for every right side (`rigid_step`,
  `rigid_path`). Any other good front settles to a recurrent one within its rank, at most five ticks, if it has room: a
  front at column `rank + 2` or beyond does (`settles`).
* So two recurrent fronts beside the same ether column that start at one column with one value of `ψ` are at one column at
  every later tick through their first arrival at column `1`, whatever lies to the right (`same_path`). From column `7` or
  beyond, ten ticks take a recurrent front exactly four columns left (`ten_ticks`).
* From a recurrent front the tick at which column `1` first leaves the ether is a formula in its column and state
  (`first_departure`).
* From an aligned prefix of **any** length `N ≥ 3` that breaks at the next tick, it is a formula in `N`, the class of
  column `N` and one bit (`departure_after_exit`). The cells beyond the prefix are arbitrary. At one class and bit, twelve
  more columns cost thirty more ticks for `N ≥ 4` (`exitWait_add_twelve`); from `N = 3` one exit state gives 28.

Two other backgrounds have exact front speeds in `Rule30MovingWall`. Here the whole path is fixed, and the first departure
with it.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30EtherThreeDeparture

open Rule30EtherThree Rule30EtherThreeErosion Rule30Jen Rule30Ether

/-! ### The thirteen recurrent states -/

/-- The recurrent front states `(class, next column defective)`. -/
def isRec (g : Nat) (u : Bool) : Bool :=
  (if u then [true, true, true, true, true, false, false, false, true, false, false, false]
    else [true, true, true, false, false, true, true, false, true, true, false, false]).getD g false

/-- The conserved potential: the class, except `2` at class `8` with the next column defective. -/
def psiR (g : Nat) (u : Bool) : Nat := if g == 8 && u then 2 else g

/-- Ranks of the good states: the number of ticks within which the state is recurrent. -/
def rankR (g : Nat) (u : Bool) : Nat :=
  (if u then [0, 0, 0, 0, 0, 1, 2, 5, 0, 1, 0, 4] else [0, 0, 0, 3, 1, 0, 0, 1, 0, 0, 1, 4]).getD g 0

/-- The certificate for one local pattern: from a recurrent state, the new front is one of three columns, its state is
recurrent, and the potential balances exactly. -/
abbrev recAt (c φ : Nat) (x1 x2 x3 x4 : Bool) : Prop :=
  isRec ((c + 4 * φ) % 12) (uC c φ x1) = true →
    ∃ i, i < 3 ∧ (∀ j, j < i → dC c φ x1 x2 x3 x4 j = false) ∧ dC c φ x1 x2 x3 x4 i = true ∧
      isRec ((c + 4 * φ + i + 3) % 12) (dC c φ x1 x2 x3 x4 (i + 1)) = true ∧
      5 * i + 2 + psiR ((c + 4 * φ + i + 3) % 12) (dC c φ x1 x2 x3 x4 (i + 1)) =
        psiR ((c + 4 * φ) % 12) (uC c φ x1) + 5

set_option synthInstance.maxSize 1024 in
set_option synthInstance.maxHeartbeats 400000 in
theorem rec_all : ∀ c, c < 12 → ∀ φ, φ < 3 → ∀ x1 x2 x3 x4 : Bool, recAt c φ x1 x2 x3 x4 := by
  decide +kernel

/-- The certificate that a good state settles: the new front is one of four columns and its rank is smaller. -/
abbrev settleAt (c φ : Nat) (x1 x2 x3 x4 : Bool) : Prop :=
  isBad ((c + 4 * φ) % 12) (uC c φ x1) = false →
    ∃ i, i < 3 ∧ (∀ j, j < i → dC c φ x1 x2 x3 x4 j = false) ∧ dC c φ x1 x2 x3 x4 i = true ∧
      isBad ((c + 4 * φ + i + 3) % 12) (dC c φ x1 x2 x3 x4 (i + 1)) = false ∧
      rankR ((c + 4 * φ + i + 3) % 12) (dC c φ x1 x2 x3 x4 (i + 1)) ≤
        rankR ((c + 4 * φ) % 12) (uC c φ x1) - 1

set_option synthInstance.maxSize 1024 in
set_option synthInstance.maxHeartbeats 400000 in
theorem settle_all : ∀ c, c < 12 → ∀ φ, φ < 3 → ∀ x1 x2 x3 x4 : Bool, settleAt c φ x1 x2 x3 x4 := by
  decide +kernel

theorem rank_zero : ∀ g, g < 12 → ∀ u, isBad g u = false → rankR g u = 0 → isRec g u = true := by decide
theorem rank_le : ∀ g, g < 12 → ∀ u, rankR g u ≤ 5 := by decide
theorem rec_facts : ∀ g, g < 12 → ∀ u, isRec g u = true →
    g ≠ 7 ∧ g ≤ 9 ∧ (psiR g u = g ∨ (g = 8 ∧ psiR g u = 2)) := by decide

section
variable (F : Nat → Nat → Bool) (j0 s : Nat)

/-- The front state at `(t, D)` is recurrent. -/
def IsRec (t D : Nat) : Prop := isRec (cls j0 s D t) (ubit F j0 s t D) = true

/-- The conserved potential of the front state. -/
def psi (t D : Nat) : Nat := psiR (cls j0 s D t) (ubit F j0 s t D)

/-- The rank of the front state. -/
def rank (t D : Nat) : Nat := rankR (cls j0 s D t) (ubit F j0 s t D)
end

theorem cls_lt (j0 s D t : Nat) : cls j0 s D t < 12 := Nat.mod_lt _ (by decide)

/-! ### One tick -/

/-- The local picture of one tick, shared by the two certificates. From a front at `D ≥ 2`, if the local patterns
always put the first defect among three columns, there is a front one tick later, and its class and next bit are the
certificate's. -/
theorem local_step {F : Nat → Nat → Bool} (hF : IsR30 F) {j0 s t D : Nat}
    (h0 : F (t + 1) 0 = eth j0 s 0 (t + 1)) (hD2 : 2 ≤ D) (hfr : Front F j0 s t D) :
    ∃ c φ x1 x2 x3 x4, c < 12 ∧ φ < 3 ∧ cls j0 s D t = (c + 4 * φ) % 12 ∧ ubit F j0 s t D = uC c φ x1 ∧
      ∀ i, i < 3 → (∀ j, j < i → dC c φ x1 x2 x3 x4 j = false) → dC c φ x1 x2 x3 x4 i = true →
        Front F j0 s (t + 1) (D - 1 + i) ∧ cls j0 s (D - 1 + i) (t + 1) = (c + 4 * φ + i + 3) % 12 ∧
        ubit F j0 s (t + 1) (D - 1 + i) = dC c φ x1 x2 x3 x4 (i + 1) := by
  obtain ⟨E, rfl⟩ : ∃ E, D = E + 2 := ⟨D - 2, by omega⟩
  obtain ⟨c, hc⟩ : ∃ c, c = (j0 + (E + 2)) % 12 := ⟨_, rfl⟩
  obtain ⟨φ, hφ⟩ : ∃ φ, φ = (t + s) % 3 := ⟨_, rfl⟩
  have x0 : F t E = ether3 (c + 10) φ := by
    rw [hfr.1 E (by omega)]; exact ether3_congr (by omega) (by omega)
  have x1 : F t (E + 1) = ether3 (c + 11) φ := by
    rw [hfr.1 (E + 1) (by omega)]; exact ether3_congr (by omega) (by omega)
  have x2 : F t (E + 2) = !ether3 c φ := by
    rw [ne_eth hfr.2, show eth j0 s (E + 2) t = ether3 c φ from ether3_congr (by omega) (by omega)]
  generalize hy1 : F t (E + 3) = y1
  generalize hy2 : F t (E + 4) = y2
  generalize hy3 : F t (E + 5) = y3
  generalize hy4 : F t (E + 6) = y4
  have hn : ∀ i, i ≤ 4 → F (t + 1) (E + 1 + i) = nC c φ y1 y2 y3 y4 i := by
    intro i hi
    have hr := hF t (E + i)
    rw [show E + i + 1 = E + 1 + i by omega] at hr
    rw [hr]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
    · simp only [Nat.add_zero]; rw [x0, x1, x2]; rfl
    · rw [show E + 1 + 1 = E + 2 by omega, show E + 1 + 2 = E + 3 by omega, x1, x2, hy1]; rfl
    · rw [show E + 2 + 1 = E + 3 by omega, show E + 2 + 2 = E + 4 by omega, x2, hy1, hy2]; rfl
    · rw [show E + 3 + 1 = E + 4 by omega, show E + 3 + 2 = E + 5 by omega, hy1, hy2, hy3]; rfl
    · rw [show E + 4 + 1 = E + 5 by omega, show E + 4 + 2 = E + 6 by omega, hy2, hy3, hy4]; rfl
  have he : ∀ i, eth j0 s (E + 1 + i) (t + 1) = ether3 (c + 11 + i) (φ + 1) :=
    fun i => ether3_congr (by omega) (by omega)
  have hd : ∀ i, i ≤ 4 →
      (dC c φ y1 y2 y3 y4 i = true ↔ F (t + 1) (E + 1 + i) ≠ eth j0 s (E + 1 + i) (t + 1)) := by
    intro i hi
    unfold dC; rw [hn i hi, he i, bne_iff_ne]
  have hub : ubit F j0 s t (E + 2) = uC c φ y1 := by
    unfold ubit uC
    rw [show E + 2 + 1 = E + 3 by omega, hy1,
      show eth j0 s (E + 3) t = ether3 (c + 1) φ from ether3_congr (by omega) (by omega)]
  refine ⟨c, φ, y1, y2, y3, y4, by omega, by omega, by unfold cls; omega, hub, ?_⟩
  intro i hi hbefore hdi
  rw [show E + 2 - 1 + i = E + 1 + i by omega]
  have hpre := prefix_step hF h0 hfr.1
  refine ⟨⟨fun p hp => ?_, (hd i (by omega)).1 hdi⟩, by unfold cls; omega, ?_⟩
  · by_cases hpE : p < E + 1
    · exact hpre p (by omega)
    · obtain ⟨j, rfl⟩ : ∃ j, p = E + 1 + j := ⟨p - (E + 1), by omega⟩
      have hj := hbefore j (by omega)
      refine Classical.byContradiction fun hne => ?_
      have := (hd j (by omega)).2 hne
      rw [hj] at this; exact absurd this (by decide)
  · unfold ubit dC
    rw [show E + 1 + i + 1 = E + 1 + (i + 1) by omega, hn (i + 1) (by omega), he (i + 1)]

/-- **One tick of a recurrent front.** It moves by at most one column, stays recurrent, and `5 D + ψ` falls by exactly
`2`, for every right side. -/
theorem rigid_step {F : Nat → Nat → Bool} (hF : IsR30 F) {j0 s t D : Nat}
    (h0 : F (t + 1) 0 = eth j0 s 0 (t + 1)) (hD2 : 2 ≤ D) (hfr : Front F j0 s t D) (hr : IsRec F j0 s t D) :
    ∃ D', Front F j0 s (t + 1) D' ∧ IsRec F j0 s (t + 1) D' ∧ D ≤ D' + 1 ∧ D' ≤ D + 1 ∧
      5 * D' + 2 + psi F j0 s (t + 1) D' = 5 * D + psi F j0 s t D := by
  obtain ⟨c, φ, x1, x2, x3, x4, hc, hφ, hcls, hub, hstep⟩ := local_step hF h0 hD2 hfr
  have hr' : isRec ((c + 4 * φ) % 12) (uC c φ x1) = true := by
    unfold IsRec at hr; rw [hcls, hub] at hr; exact hr
  obtain ⟨i, hi, hb, hdi, hrec, hpot⟩ := rec_all c hc φ hφ x1 x2 x3 x4 hr'
  obtain ⟨hf, hcl, hu⟩ := hstep i hi hb hdi
  refine ⟨D - 1 + i, hf, ?_, by omega, by omega, ?_⟩
  · unfold IsRec; rw [hcl, hu]; exact hrec
  · unfold psi; rw [hcl, hu, hcls, hub]; omega

/-- One tick of a good front towards a recurrent state. -/
theorem settle_step {F : Nat → Nat → Bool} (hF : IsR30 F) {j0 s t D : Nat}
    (h0 : F (t + 1) 0 = eth j0 s 0 (t + 1)) (hD2 : 2 ≤ D) (hfr : Front F j0 s t D) (hg : ¬ IsB F j0 s t D) :
    ∃ D', Front F j0 s (t + 1) D' ∧ ¬ IsB F j0 s (t + 1) D' ∧ D ≤ D' + 1 ∧
      rank F j0 s (t + 1) D' ≤ rank F j0 s t D - 1 := by
  obtain ⟨c, φ, x1, x2, x3, x4, hc, hφ, hcls, hub, hstep⟩ := local_step hF h0 hD2 hfr
  have hg' : isBad ((c + 4 * φ) % 12) (uC c φ x1) = false := by
    unfold IsB at hg; rw [hcls, hub] at hg; simpa using hg
  obtain ⟨i, hi, hb, hdi, hbad, hrk⟩ := settle_all c hc φ hφ x1 x2 x3 x4 hg'
  obtain ⟨hf, hcl, hu⟩ := hstep i hi hb hdi
  refine ⟨D - 1 + i, hf, ?_, by omega, ?_⟩
  · unfold IsB; rw [hcl, hu, hbad]; decide
  · unfold rank; rw [hcl, hu, hcls, hub]; exact hrk

/-! ### The path -/

theorem psi_le {F : Nat → Nat → Bool} {j0 s t D : Nat} (hr : IsRec F j0 s t D) : psi F j0 s t D ≤ 9 := by
  obtain ⟨-, h9, h | h⟩ := rec_facts _ (cls_lt j0 s D t) _ hr
  · unfold psi; omega
  · unfold psi; omega

/-- **The conserved quantity.** From a recurrent front, `5 D + 2 n + ψ` is constant for as long as the front has been
at column `2` or more, for every right side. -/
theorem rigid_path {F : Nat → Nat → Bool} (hF : IsR30 F) {j0 s t D : Nat}
    (h0 : ∀ u, t ≤ u → F u 0 = eth j0 s 0 u) (hfr : Front F j0 s t D) (hr : IsRec F j0 s t D) :
    ∀ n, (∀ m, m < n → ∀ E, Front F j0 s (t + m) E → 2 ≤ E) →
      ∃ E, Front F j0 s (t + n) E ∧ IsRec F j0 s (t + n) E ∧
        5 * E + 2 * n + psi F j0 s (t + n) E = 5 * D + psi F j0 s t D := by
  intro n
  induction n with
  | zero => intro _; exact ⟨D, hfr, hr, by simp⟩
  | succ n ih =>
    intro h
    obtain ⟨E, hE, hrE, hp⟩ := ih fun m hm => h m (by omega)
    obtain ⟨E', hE', hrE', -, -, hp'⟩ :=
      rigid_step hF (h0 (t + n + 1) (by omega)) (h n (by omega) E hE) hE hrE
    refine ⟨E', ?_, ?_, ?_⟩
    · rw [show t + (n + 1) = t + n + 1 by omega]; exact hE'
    · rw [show t + (n + 1) = t + n + 1 by omega]; exact hrE'
    · rw [show t + (n + 1) = t + n + 1 by omega]; omega

/-- A front is determined: there is at most one at a tick. -/
theorem front_unique {F : Nat → Nat → Bool} {j0 s t D E : Nat} (hD : Front F j0 s t D) (hE : Front F j0 s t E) :
    D = E := by
  rcases Nat.lt_trichotomy D E with h | h | h
  · exact absurd (hE.1 D h) hD.2
  · exact h
  · exact absurd (hD.1 E h) hE.2

/-- Two recurrent fronts at one tick with one value of `5 D + ψ`, at most two columns apart, are at one column. -/
theorem same_column {F G : Nat → Nat → Bool} {j0 s t D E : Nat} (hD : IsRec F j0 s t D) (hE : IsRec G j0 s t E)
    (h : 5 * D + psi F j0 s t D = 5 * E + psi G j0 s t E) : D = E := by
  obtain ⟨a7, a9, a⟩ := rec_facts _ (cls_lt j0 s D t) _ hD
  obtain ⟨b7, b9, b⟩ := rec_facts _ (cls_lt j0 s E t) _ hE
  have hcD : cls j0 s D t = (j0 + D + 4 * (t + s)) % 12 := rfl
  have hcE : cls j0 s E t = (j0 + E + 4 * (t + s)) % 12 := rfl
  unfold psi at h
  rcases a with a | a <;> rcases b with b | b <;> omega

/-- **One path for every right side.** Two evolutions beside the same ether column whose fronts at tick `t` are at one
column, recurrent and with one value of `ψ`, have the same front at every later tick for as long as it has been at
column `2` or more. -/
theorem same_path {F G : Nat → Nat → Bool} (hF : IsR30 F) (hG : IsR30 G) {j0 s t D : Nat}
    (h0F : ∀ u, t ≤ u → F u 0 = eth j0 s 0 u) (h0G : ∀ u, t ≤ u → G u 0 = eth j0 s 0 u)
    (hfF : Front F j0 s t D) (hrF : IsRec F j0 s t D) (hfG : Front G j0 s t D) (hrG : IsRec G j0 s t D)
    (hψ : psi F j0 s t D = psi G j0 s t D) :
    ∀ n, (∀ m, m < n → ∀ E, Front F j0 s (t + m) E → 2 ≤ E) →
      ∃ E, Front F j0 s (t + n) E ∧ Front G j0 s (t + n) E := by
  intro n hn
  suffices H : ∀ n, (∀ m, m < n → ∀ E, Front F j0 s (t + m) E → 2 ≤ E) →
      ∃ E, (Front F j0 s (t + n) E ∧ IsRec F j0 s (t + n) E) ∧ (Front G j0 s (t + n) E ∧ IsRec G j0 s (t + n) E) ∧
        psi F j0 s (t + n) E = psi G j0 s (t + n) E by
    obtain ⟨E, ⟨h1, -⟩, ⟨h2, -⟩, -⟩ := H n hn
    exact ⟨E, h1, h2⟩
  intro n
  induction n with
  | zero => intro _; exact ⟨D, ⟨hfF, hrF⟩, ⟨hfG, hrG⟩, hψ⟩
  | succ n ih =>
    intro h
    obtain ⟨E, ⟨f1, r1⟩, ⟨f2, r2⟩, hp⟩ := ih (fun m hm => h m (by omega)) 
    have hE2 := h n (by omega) E f1
    obtain ⟨A, fA, rA, -, -, pA⟩ := rigid_step hF (h0F (t + n + 1) (by omega)) hE2 f1 r1
    obtain ⟨B, fB, rB, -, -, pB⟩ := rigid_step hG (h0G (t + n + 1) (by omega)) hE2 f2 r2
    have hAB : A = B := same_column rA rB (by omega)
    subst hAB
    rw [show t + (n + 1) = t + n + 1 by omega]
    exact ⟨A, ⟨fA, rA⟩, ⟨fB, rB⟩, by omega⟩

/-- **Every ten ticks, four columns.** From a recurrent front at column `7` or more the front is exactly four columns
left after ten ticks, recurrent, with the same `ψ`, for every right side. -/
theorem ten_ticks {F : Nat → Nat → Bool} (hF : IsR30 F) {j0 s t D : Nat}
    (h0 : ∀ u, t ≤ u → F u 0 = eth j0 s 0 u) (hfr : Front F j0 s t D) (hr : IsRec F j0 s t D) (hD : 7 ≤ D) :
    Front F j0 s (t + 10) (D - 4) ∧ IsRec F j0 s (t + 10) (D - 4) ∧
      psi F j0 s (t + 10) (D - 4) = psi F j0 s t D := by
  have key : ∀ n, n ≤ 10 → ∃ E, Front F j0 s (t + n) E ∧ IsRec F j0 s (t + n) E ∧
      5 * E + 2 * n + psi F j0 s (t + n) E = 5 * D + psi F j0 s t D := by
    intro n
    induction n with
    | zero => intro _; exact ⟨D, hfr, hr, by simp⟩
    | succ n ih =>
      intro hn
      obtain ⟨E, hE, hrE, hp⟩ := ih (by omega)
      have hψ := psi_le hrE
      obtain ⟨E', hE', hrE', -, -, hp'⟩ :=
        rigid_step hF (h0 (t + n + 1) (by omega)) (by omega) hE hrE
      rw [show t + (n + 1) = t + n + 1 by omega]
      exact ⟨E', hE', hrE', by omega⟩
  obtain ⟨E, hE, hrE, hp⟩ := key 10 (Nat.le_refl _)
  obtain ⟨a7, a9, a⟩ := rec_facts _ (cls_lt j0 s D t) _ hr
  obtain ⟨b7, b9, b⟩ := rec_facts _ (cls_lt j0 s E (t + 10)) _ hrE
  have hcD : cls j0 s D t = (j0 + D + 4 * (t + s)) % 12 := rfl
  have hcE : cls j0 s E (t + 10) = (j0 + E + 4 * (t + 10 + s)) % 12 := rfl
  have hED : E = D - 4 := by
    unfold psi at hp
    rcases a with a | a <;> rcases b with b | b <;> omega
  subst hED
  exact ⟨hE, hrE, by omega⟩

/-- **The wake settles.** From any front state but the bad one the front is recurrent within its rank, at most five
ticks (`rank_le`), when it starts far enough from the centre. -/
theorem settles {F : Nat → Nat → Bool} (hF : IsR30 F) {j0 s : Nat} :
    ∀ k t D, (∀ u, t ≤ u → F u 0 = eth j0 s 0 u) → Front F j0 s t D → ¬ IsB F j0 s t D →
      rank F j0 s t D ≤ k → k + 2 ≤ D →
      ∃ n, n ≤ k ∧ ∃ E, Front F j0 s (t + n) E ∧ IsRec F j0 s (t + n) E := by
  intro k
  induction k with
  | zero =>
    intro t D _ hfr hg hrk _
    refine ⟨0, Nat.le_refl _, D, hfr, ?_⟩
    show isRec (cls j0 s D t) (ubit F j0 s t D) = true
    refine rank_zero _ (cls_lt j0 s D t) _ ?_ (Nat.le_zero.1 hrk)
    unfold IsB at hg; simpa using hg
  | succ k ih =>
    intro t D h0 hfr hg hrk hD
    obtain ⟨E, hE, hgE, hDE, hrkE⟩ := settle_step hF (h0 (t + 1) (by omega)) (by omega) hfr hg
    obtain ⟨n, hn, E', hE', hrE'⟩ :=
      ih (t + 1) E (fun u hu => h0 u (by omega)) hE hgE (by omega) (by omega)
    refine ⟨n + 1, by omega, E', ?_, ?_⟩
    · rw [show t + (n + 1) = t + 1 + n by omega]; exact hE'
    · rw [show t + (n + 1) = t + 1 + n by omega]; exact hrE'

/-- Phase of the recurrent front in its ten-tick displacement cycle. -/
def slot (g : Nat) (u : Bool) : Nat :=
  if g == 8 && u then 9 else [0,7,4,1,8,5,2,0,6,3].getD g 0

/-- Waits at the distances `1` to `5`, by slot. -/
def smallWait (d j : Nat) : Nat :=
  let row := match d with
    | 0 => []
    | 1 => [1,1,1,3,1,1,5,1,3,2]
    | 2 => [2,2,4,8,2,6,6,4,4,3]
    | 3 => [3,5,9,9,7,7,7,5,5,4]
    | 4 => [6,10,10,10,8,8,10,6,8,7]
    | _ => [11,11,11,13,9,11,15,9,13,12]
  row.getD j 0

/-- Wait from distance d = D − 1 to the first discrepancy at site 1. -/
def ticksToOne (d j : Nat) : Nat :=
  if d < 2 then smallWait d j
  else 10*((d-2)/4) + smallWait (2+(d-2)%4) j

theorem ticks_add_four {d : Nat} (hd : 2 ≤ d) (j : Nat) :
    ticksToOne (d+4) j = ticksToOne d j + 10 := by
  simp only [ticksToOne, ite_eq_right (show ¬d+4 < 2 by omega), ite_eq_right (show ¬d < 2 by omega)]
  have modEq : (d+4-2)%4 = (d-2)%4 := by omega
  rw [modEq]; omega

/-- The original invariant restricts the next displacement to i−1. On every
allowed transition the proposed waiting time drops by one. -/
theorem small_step : ∀ (d : Fin 7) (g : Fin 12) (i : Fin 3) (u v : Bool),
    1 ≤ d.val → isRec g.val u = true → isRec ((g.val+3+i.val)%12) v = true →
    5*i.val+2+psiR ((g.val+3+i.val)%12) v = 5+psiR g.val u →
    ticksToOne (d.val-1+i.val) (slot ((g.val+3+i.val)%12) v) + 1 =
      ticksToOne d.val (slot g.val u) := by decide +kernel

/-- The same at every distance, by four columns at a time. -/
theorem step_duration (d g i : Nat) (u v : Bool)
    (hd : 1 ≤ d) (hg : g < 12) (hi : i < 3) (hu : isRec g u = true)
    (hv : isRec ((g+3+i)%12) v = true) (hbal : 5*i+2+psiR ((g+3+i)%12) v = 5+psiR g u) :
    ticksToOne (d-1+i) (slot ((g+3+i)%12) v) + 1 = ticksToOne d (slot g u) := by
  by_cases h : d < 7
  · exact small_step ⟨d,h⟩ ⟨g,hg⟩ ⟨i,hi⟩ u v hd hu hv hbal
  · have ih := step_duration (d-4) g i u v (by omega) hg hi hu hv hbal
    have x := ticks_add_four (d := d-4) (by omega) (slot g u)
    have y := ticks_add_four (d := d-4-1+i) (by omega) (slot ((g+3+i)%12) v)
    rw [show d-4+4 = d by omega] at x
    rw [show d-4-1+i+4 = d-1+i by omega] at y
    omega
termination_by d

/-- The wait of the front at `(t, D)`. -/
def waitAt (F : Nat → Nat → Bool) (j0 s t D : Nat) :=
  ticksToOne (D-1) (slot (cls j0 s D t) (ubit F j0 s t D))

/-- One tick of a recurrent front takes one tick off its wait. -/
theorem advance {F : Nat → Nat → Bool} (hF : IsR30 F) {j0 s t D : Nat}
    (h0 : F (t+1) 0 = eth j0 s 0 (t+1)) (hd : 2 ≤ D)
    (hf : Front F j0 s t D) (hr : IsRec F j0 s t D) :
    ∃ E, 1 ≤ E ∧ Front F j0 s (t+1) E ∧ IsRec F j0 s (t+1) E ∧
      waitAt F j0 s (t+1) E + 1 = waitAt F j0 s t D := by
  obtain ⟨E,hE,rE,hl,hh,bal⟩ := rigid_step hF h0 hd hf hr
  let i := E+1-D
  have hi : i < 3 := by dsimp [i]; omega
  have eqD : E+1 = D+i := by dsimp [i]; omega
  have cc : cls j0 s E (t+1) = (cls j0 s D t+3+i)%12 := by unfold cls; omega
  unfold psi at bal
  unfold IsRec at rE
  rw [cc] at rE bal
  have step := step_duration (D-1) (cls j0 s D t) i (ubit F j0 s t D) (ubit F j0 s (t+1) E)
    (by omega) (cls_lt ..) hi hr rE (by omega)
  refine ⟨E,by omega,hE,by unfold IsRec; rw [cc]; exact rE,?_⟩
  unfold waitAt; rw [cc, ← show D-1-1+i = E-1 by omega]; exact step

/-- Agreement before t+n and the first discrepancy at t+n, measured from t. -/
def FirstDeparture (F : Nat → Nat → Bool) (j0 s t n : Nat) : Prop :=
  (∀ m, m < n → F (t+m) 1 = eth j0 s 1 (t+m)) ∧ F (t+n) 1 ≠ eth j0 s 1 (t+n)

theorem reaches {F : Nat → Nat → Bool} (hF : IsR30 F) {j0 s : Nat} (n t D : Nat)
    (h0 : ∀ w, t ≤ w → F w 0 = eth j0 s 0 w)
    (hd : 1 ≤ D) (hf : Front F j0 s t D) (hr : IsRec F j0 s t D) (hn : waitAt F j0 s t D = n) :
    FirstDeparture F j0 s t n := by
  by_cases one : D = 1
  · subst D
    have zero : n = 0 := by simpa [waitAt,ticksToOne,smallWait] using hn.symm
    rw [zero]; exact ⟨fun _ hm => by omega,by simpa using hf.2⟩
  · obtain ⟨E,he,hE,rE,dec⟩ := advance hF (h0 _ (by omega)) (by omega) hf hr
    cases n with
    | zero => omega
    | succ n =>
      obtain ⟨prior,last⟩ := reaches hF n (t+1) E (fun w hw => h0 w (by omega)) he hE rE (by omega)
      refine ⟨?_,by simpa only [show t+(n+1) = t+1+n by omega] using last⟩
      intro m hm
      cases m with
      | zero => simpa using hf.1 1 (by omega)
      | succ m => simpa only [show t+(m+1) = t+1+m by omega] using prior m (by omega)
termination_by n

/-- Closed-form first-departure time at every recurrent front, for any right
continuation. The inputs are the distance to site 1, the ether class and a
single bit immediately east of the front. -/
theorem first_departure {F : Nat → Nat → Bool} (hF : IsR30 F) {j0 s t D : Nat}
    (h0 : ∀ w, t ≤ w → F w 0 = eth j0 s 0 w)
    (hd : 1 ≤ D) (hf : Front F j0 s t D) (hr : IsRec F j0 s t D) :
    FirstDeparture F j0 s t
      (ticksToOne (D-1) (slot (cls j0 s D t) (ubit F j0 s t D))) :=
  reaches hF _ t D h0 hd hf hr rfl


/-! ### The transient states an exit can meet -/

/-- The transient states met on the way from an exit to the recurrent path. -/
def shortState (g : Nat) (u : Bool) : Prop :=
  (g = 3 ∧ u = false) ∨ (g = 6 ∨ g = 9) ∧ u = true

theorem short_table : ∀ (c : Fin 12) (φ : Fin 3) (x y z w : Bool),
    let g := (c.val+4*φ.val)%12
    let i := if g = 9 then 1 else 0
    shortState g (uC c.val φ.val x) →
      (∀ j, j < i → dC c.val φ.val x y z w j = false) ∧ dC c.val φ.val x y z w i = true ∧
      (g ≠ 9 → dC c.val φ.val x y z w (i+1) = true) := by
  unfold shortState
  decide +kernel

theorem short_step {F : Nat → Nat → Bool} (hF : IsR30 F) {j0 s t D g : Nat}
    (h0 : F (t+1) 0 = eth j0 s 0 (t+1)) (hd : 2 ≤ D) (hf : Front F j0 s t D)
    (hc : cls j0 s D t = g) (hs : shortState g (ubit F j0 s t D)) :
    let i := if g = 9 then 1 else 0
    let E := D-1+i
    Front F j0 s (t+1) E ∧ cls j0 s E (t+1) = (g+3+i)%12 ∧
      (g ≠ 9 → ubit F j0 s (t+1) E = true) := by
  obtain ⟨c,φ,x,y,z,w,cl,ph,cg,bit,step⟩ := local_step hF h0 hd hf
  rw [←hc,cg,bit] at hs
  obtain ⟨before,atFront,after⟩ := short_table ⟨c,cl⟩ ⟨φ,ph⟩ x y z w hs
  rw [←hc,cg]
  let i := if (c+4*φ)%12 = 9 then 1 else 0
  obtain ⟨front,newClass,newBit⟩ := step i (by dsimp [i]; split <;> decide) before atFront
  exact ⟨front,by rw [newClass]; omega,fun h => newBit.trans (after h)⟩

theorem prepend {F j0 s t n} (h : F t 1 = eth j0 s 1 t)
    (later : FirstDeparture F j0 s (t+1) n) : FirstDeparture F j0 s t (n+1) := by
  refine ⟨?_,by simpa only [show t+(n+1) = (t+1)+n by omega] using later.2⟩
  intro m hm; cases m with
  | zero => simpa using h
  | succ m => simpa only [show t+(m+1) = (t+1)+m by omega] using later.1 m (by omega)

theorem nine {F : Nat → Nat → Bool} (hF : IsR30 F) {j0 s t D : Nat}
    (h0 : ∀ w, t ≤ w → F w 0 = eth j0 s 0 w)
    (hd : 2 ≤ D) (hf : Front F j0 s t D) (hc : cls j0 s D t = 9) (hu : ubit F j0 s t D = true) :
    FirstDeparture F j0 s t (ticksToOne (D-1) 7 + 1) := by
  obtain ⟨front,cl,_⟩ := short_step hF (h0 _ (by omega)) hd hf hc (Or.inr ⟨Or.inr rfl,hu⟩)
  simp only [ite_true] at front cl
  rw [show D-1+1 = D by omega] at front cl
  have cls1 : cls j0 s D (t+1) = 1 := cl
  have rec1 : IsRec F j0 s (t+1) D := by
    unfold IsRec; rw [cls1]; cases ubit F j0 s (t+1) D <;> decide
  have next := first_departure hF (fun w hw => h0 w (by omega)) (by omega) front rec1
  rw [cls1] at next
  apply prepend (hf.1 1 (by omega))
  exact next

theorem six {F : Nat → Nat → Bool} (hF : IsR30 F) {j0 s t D : Nat}
    (h0 : ∀ w, t ≤ w → F w 0 = eth j0 s 0 w)
    (hd : 3 ≤ D) (hf : Front F j0 s t D) (hc : cls j0 s D t = 6) (hu : ubit F j0 s t D = true) :
    FirstDeparture F j0 s t (ticksToOne (D-2) 7 + 2) := by
  obtain ⟨front,cl,bit⟩ := short_step hF (h0 _ (by omega)) (by omega) hf hc (Or.inr ⟨Or.inl rfl,hu⟩)
  apply prepend (hf.1 1 (by omega))
  exact nine hF (fun w hw => h0 w (by omega)) (D := D-1) (by omega) front cl (bit (by decide))

/-! ### Leaving an aligned prefix of any length -/

/-- The wait from the last aligned tick of a prefix of `N` columns, when the front one tick later has class `g` and next
bit `u`. -/
def exitWait (N g : Nat) (u : Bool) : Nat :=
  if g == 9 && u then ticksToOne (N - 1) 7 + 2
  else if g == 6 && u then ticksToOne (N - 2) 7 + 3
  else ticksToOne (N - 1) (slot g u) + 1

/-- The state in which a front leaves an aligned prefix: recurrent, or one of two transient ones. -/
theorem exit_table : ∀ (c : Fin 12) (φ : Fin 3) (e e2 : Bool),
    Rule30Jen.rule (ether3 (c.val + 11) φ.val) (ether3 c.val φ.val) e ≠ ether3 c.val (φ.val + 1) →
    isRec ((c.val + 4 * (φ.val + 1)) % 12)
        (Rule30Jen.rule (ether3 c.val φ.val) e e2 != ether3 (c.val + 1) (φ.val + 1)) = true ∨
      ((c.val + 4 * (φ.val + 1)) % 12 = 9 ∧
        (Rule30Jen.rule (ether3 c.val φ.val) e e2 != ether3 (c.val + 1) (φ.val + 1)) = true) ∨
      ((c.val + 4 * (φ.val + 1)) % 12 = 6 ∧
        (Rule30Jen.rule (ether3 c.val φ.val) e e2 != ether3 (c.val + 1) (φ.val + 1)) = true) := by
  decide +kernel

theorem rec_not : ∀ g, g < 12 → ∀ u, isRec g u = true → (g == 9 && u) = false ∧ (g == 6 && u) = false := by decide

/-- **First departure after a prefix of any length.** Let the column at site `0` be an ether column, and let the sites
`0` to `N` carry the aligned ether at tick `t` and not at tick `t + 1`, with `N ≥ 3`. Then site `1` first leaves the ether
exactly `exitWait N g u` ticks after `t`, where `g` is the class of site `N` and `u` says whether site `N + 1` is off the
ether at tick `t + 1`. The cells beyond are arbitrary. -/
theorem departure_after_exit {F : Nat → Nat → Bool} (hF : IsR30 F) {j0 s t N : Nat} (hN : 3 ≤ N)
    (h0 : ∀ w, t ≤ w → F w 0 = eth j0 s 0 w) (agree : ∀ p, p ≤ N → F t p = eth j0 s p t)
    (exit : ∃ p, p ≤ N ∧ F (t + 1) p ≠ eth j0 s p (t + 1)) :
    FirstDeparture F j0 s t (exitWait N (cls j0 s N (t + 1)) (ubit F j0 s (t + 1) N)) := by
  have before : ∀ p, p < N → F (t + 1) p = eth j0 s p (t + 1) := fun p hp =>
    prefix_step hF (h0 _ (by omega)) (D := N + 1) (fun q hq => agree q (by omega)) p (by omega)
  have diff : F (t + 1) N ≠ eth j0 s N (t + 1) := by
    obtain ⟨p, hp, hne⟩ := exit
    by_cases h : p = N
    · rw [← h]; exact hne
    · exact absurd (before p (by omega)) hne
  have front : Front F j0 s (t + 1) N := ⟨before, diff⟩
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  let c : Fin 12 := ⟨(j0 + (M + 1)) % 12, Nat.mod_lt _ (by decide)⟩
  let φ : Fin 3 := ⟨(t + s) % 3, Nat.mod_lt _ (by decide)⟩
  have e1 : F t M = ether3 (c.val + 11) φ.val := by
    rw [agree M (by omega)]; exact ether3_congr (by dsimp [c]; omega) (by dsimp [φ]; omega)
  have e2 : F t (M + 1) = ether3 c.val φ.val := by
    rw [agree (M + 1) (by omega)]; exact ether3_congr (by dsimp [c]; omega) (by dsimp [φ]; omega)
  have e3 : eth j0 s (M + 1) (t + 1) = ether3 c.val (φ.val + 1) :=
    ether3_congr (by dsimp [c]; omega) (by dsimp [φ]; omega)
  have e4 : eth j0 s (M + 1 + 1) (t + 1) = ether3 (c.val + 1) (φ.val + 1) :=
    ether3_congr (by dsimp [c]; omega) (by dsimp [φ]; omega)
  have lost : Rule30Jen.rule (ether3 (c.val + 11) φ.val) (ether3 c.val φ.val) (F t (M + 2)) ≠
      ether3 c.val (φ.val + 1) := by
    rw [← e1, ← e2, ← e3, ← hF t M]; exact diff
  have hu : ubit F j0 s (t + 1) (M + 1) =
      (Rule30Jen.rule (ether3 c.val φ.val) (F t (M + 2)) (F t (M + 3)) != ether3 (c.val + 1) (φ.val + 1)) := by
    unfold ubit; rw [e4, hF t (M + 1), e2]
  have hg : cls j0 s (M + 1) (t + 1) = (c.val + 4 * (φ.val + 1)) % 12 := by dsimp [c, φ, cls]; omega
  have hw0 : ∀ w, t + 1 ≤ w → F w 0 = eth j0 s 0 w := fun w hw => h0 w (by omega)
  have data := exit_table c φ (F t (M + 2)) (F t (M + 3)) lost
  rw [← hu, ← hg] at data
  rcases data with hr | ⟨h9, hu1⟩ | ⟨h6, hu1⟩
  · obtain ⟨n9, n6⟩ := rec_not _ (cls_lt j0 s (M + 1) (t + 1)) _ hr
    unfold exitWait
    rw [n9, n6]
    exact prepend (agree 1 (by omega)) (first_departure hF hw0 (by omega) front hr)
  · unfold exitWait
    rw [h9, hu1]
    exact prepend (agree 1 (by omega)) (nine hF hw0 (by omega) front h9 hu1)
  · unfold exitWait
    rw [h6, hu1]
    exact prepend (agree 1 (by omega)) (six hF hw0 (by omega) front h6 hu1)

/-- Twelve more columns of prefix, one period of the ether, cost exactly thirty more ticks. -/
theorem exitWait_add_twelve {N : Nat} (hN : 4 ≤ N) (g : Nat) (u : Bool) :
    exitWait (N + 12) g u = exitWait N g u + 30 := by
  have h : ∀ d, 2 ≤ d → ∀ j, ticksToOne (d + 12) j = ticksToOne d j + 30 := by
    intro d hd j
    have a := ticks_add_four (d := d) hd j
    have b := ticks_add_four (d := d + 4) (by omega) j
    have c := ticks_add_four (d := d + 8) (by omega) j
    rw [show d + 12 = d + 8 + 4 by omega, c, show d + 8 = d + 4 + 4 by omega, b, a]
  have h1 : ∀ j, ticksToOne (N + 12 - 1) j = ticksToOne (N - 1) j + 30 := fun j => by
    rw [show N + 12 - 1 = N - 1 + 12 by omega]; exact h _ (by omega) j
  have h2 : ∀ j, ticksToOne (N + 12 - 2) j = ticksToOne (N - 2) j + 30 := fun j => by
    rw [show N + 12 - 2 = N - 2 + 12 by omega]; exact h _ (by omega) j
  unfold exitWait
  simp only [h1, h2]
  split
  · omega
  · split <;> omega

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

def recStates13 : List (Nat × Bool) := [(0, false), (0, true), (1, false), (1, true), (2, false), (2, true), (3, true), (4, true), (5, false), (6, false), (8, false), (8, true), (9, false)]
def recShift13 : List Nat := [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 1, 2]
def recWakeNext : List (List Nat) := [[6], [6], [7], [7], [8], [8], [9], [11], [10], [12], [2, 3], [0, 1], [4, 5]]

def recWakePaths (k : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => (recWakeNext.getD k []).flatMap (fun k' => (recWakePaths k' n).map (k' :: ·))

theorem recWake_step_iff_exists_east :
    ∀ c : Fin 12, ∀ φ : Fin 3, ∀ x1 : Bool,
      let g := (c.val + 4 * φ.val) % 12
      let u := uC c.val φ.val x1
      isRec g u = true →
      ∃ k, k < 13 ∧ recStates13.getD k (99, false) = (g, u) ∧
        (∀ x2 x3 x4 : Bool,
          let i := recShift13.getD k 0
          (∀ j, j < i → dC c.val φ.val x1 x2 x3 x4 j = false) ∧
          dC c.val φ.val x1 x2 x3 x4 i = true ∧
          ∃ k' ∈ recWakeNext.getD k [],
            recStates13.getD k' (99, false) = ((g + i + 3) % 12, dC c.val φ.val x1 x2 x3 x4 (i + 1))) ∧
        (∀ k' ∈ recWakeNext.getD k [], ∃ x2 x3 x4 : Bool,
          let i := recShift13.getD k 0
          recStates13.getD k' (99, false) = ((g + i + 3) % 12, dC c.val φ.val x1 x2 x3 x4 (i + 1))) := by
  decide +kernel

theorem recWake_physical_step {F : Nat → Nat → Bool} (hF : IsR30 F) {j0 s t D : Nat}
    (h0 : F (t + 1) 0 = eth j0 s 0 (t + 1)) (hD2 : 2 ≤ D)
    (hfr : Front F j0 s t D) (hrec : IsRec F j0 s t D) :
    ∃ k, k < 13 ∧ recStates13.getD k (99, false) = (cls j0 s D t, ubit F j0 s t D) ∧
      let D' := D - 1 + recShift13.getD k 0
      Front F j0 s (t + 1) D' ∧ IsRec F j0 s (t + 1) D' ∧
      ∃ k' ∈ recWakeNext.getD k [],
        recStates13.getD k' (99, false) = (cls j0 s D' (t + 1), ubit F j0 s (t + 1) D') := by
  obtain ⟨c, φ, x1, x2, x3, x4, hc, hφ, hcls, hub, hstep⟩ := local_step hF h0 hD2 hfr
  have hr' : isRec ((c + 4 * φ) % 12) (uC c φ x1) = true := by
    unfold IsRec at hrec; rwa [hcls, hub] at hrec
  obtain ⟨k, hk_lt, hk_st, hsound, _⟩ := recWake_step_iff_exists_east ⟨c, hc⟩ ⟨φ, hφ⟩ x1 hr'
  obtain ⟨hclear, hhit, k', hk'_mem, hk'_st⟩ := hsound x2 x3 x4
  have hi_lt : recShift13.getD k 0 < 3 := by
    have hlt3 : (List.range 13).all (fun q => decide (recShift13.getD q 0 < 3)) = true := by decide +kernel
    exact decide_eq_true_eq.mp (List.all_eq_true.mp hlt3 k (List.mem_range.mpr hk_lt))
  obtain ⟨hfr', hcls', hubit'⟩ := hstep (recShift13.getD k 0) hi_lt hclear hhit
  have hk'_isrec : isRec (cls j0 s (D - 1 + recShift13.getD k 0) (t + 1)) (ubit F j0 s (t + 1) (D - 1 + recShift13.getD k 0)) = true := by
    have hall_rec : ∀ j ∈ recWakeNext.getD k [], isRec (recStates13.getD j (99, false)).1 (recStates13.getD j (99, false)).2 = true := by
      have hchk : (List.range 13).all (fun q => (recWakeNext.getD q []).all (fun j =>
          isRec (recStates13.getD j (99, false)).1 (recStates13.getD j (99, false)).2)) = true := by decide +kernel
      intro j hj; exact List.all_eq_true.mp (List.all_eq_true.mp hchk k (List.mem_range.mpr hk_lt)) j hj
    have hmod12 : ((c + 4 * φ) % 12 + recShift13.getD k 0 + 3) % 12 = (c + 4 * φ + recShift13.getD k 0 + 3) % 12 := by omega
    dsimp only at hk'_st
    rw [hmod12] at hk'_st
    have hrec_j := hall_rec k' hk'_mem
    rw [hk'_st] at hrec_j
    dsimp only at hrec_j
    rwa [hcls', hubit']
  have hmod12 : ((c + 4 * φ) % 12 + recShift13.getD k 0 + 3) % 12 = (c + 4 * φ + recShift13.getD k 0 + 3) % 12 := by omega
  dsimp only at hk_st hk'_st
  rw [hmod12] at hk'_st
  refine ⟨k, hk_lt, ?_, hfr', hk'_isrec, k', hk'_mem, ?_⟩
  · rw [hcls, hub]; exact hk_st
  · rw [hcls', hubit']; exact hk'_st

theorem recWake_diamond_merge :
    recStates13.getD 0 (99, false) = (0, false) ∧ recStates13.getD 1 (99, false) = (0, true) ∧
    recWakeNext.getD 0 [] = [6] ∧ recWakeNext.getD 1 [] = [6] ∧
    recStates13.getD 2 (99, false) = (1, false) ∧ recStates13.getD 3 (99, false) = (1, true) ∧
    recWakeNext.getD 2 [] = [7] ∧ recWakeNext.getD 3 [] = [7] ∧
    recStates13.getD 4 (99, false) = (2, false) ∧ recStates13.getD 5 (99, false) = (2, true) ∧
    recWakeNext.getD 4 [] = [8] ∧ recWakeNext.getD 5 [] = [8] := by decide +kernel

theorem recWake_ten_step_necklace :
    ∀ k : Fin 13, ∀ p ∈ recWakePaths k.val 10,
      (((k.val :: p).take 10).map (fun q => recShift13.getD q 0)).sum = 6 ∧
      (recStates13.getD (p.getLastD k.val) (99, false)).1 = (recStates13.getD k.val (99, false)).1 := by
  decide +kernel

def recWakeCount : Nat → Nat → Nat
  | 0, _ => 1
  | n + 1, k => (recWakeNext.getD k []).foldr (fun k' acc => recWakeCount n k' + acc) 0

private theorem recWakePaths_length (n k : Nat) : (recWakePaths k n).length = recWakeCount n k := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    unfold recWakePaths recWakeCount
    have hfl : ∀ (xs : List Nat), (xs.flatMap (fun k' => (recWakePaths k' n).map (k' :: ·))).length =
        xs.foldr (fun k' acc => recWakeCount n k' + acc) 0 := by
      intro xs; induction xs with
      | nil => rfl
      | cons x xs ihx => simp [List.flatMap_cons, ih x, ihx]
    exact hfl (recWakeNext.getD k [])

private theorem recWakeNext_lt : ∀ k < 13, ∀ k' ∈ recWakeNext.getD k [], k' < 13 := by
  have hok : (List.range 13).all (fun k => (recWakeNext.getD k []).all (fun k' => decide (k' < 13))) = true := by
    decide +kernel
  intro k hk k'
  intro hk'
  exact decide_eq_true_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp hok k (List.mem_range.mpr hk)) k' hk')

private theorem recWakeCount_scale (a b c : Nat) (h : ∀ j < 13, recWakeCount b j = c) :
    ∀ k < 13, recWakeCount (a + b) k = recWakeCount a k * c := by
  induction a with
  | zero => intro k hk; simp [recWakeCount, h k hk]
  | succ a ih =>
    intro k hk
    rw [show a + 1 + b = (a + b) + 1 by omega]
    unfold recWakeCount
    have hlt := recWakeNext_lt k hk
    have hfl : ∀ (xs : List Nat), (∀ x ∈ xs, x < 13) →
        xs.foldr (fun k' acc => recWakeCount (a + b) k' + acc) 0 =
        xs.foldr (fun k' acc => recWakeCount a k' + acc) 0 * c := by
      intro xs; induction xs with
      | nil => intro _; simp
      | cons x xs ihx =>
        intro hxs
        simp only [List.foldr_cons, ih x (hxs x List.mem_cons_self),
          ihx (fun y hy => hxs y (List.mem_cons_of_mem _ hy)), Nat.add_mul]
    exact hfl (recWakeNext.getD k []) hlt

theorem recWake_exact_count_eight_pow (k : Fin 13) (m : Nat) :
    (recWakePaths k.val (10 * m)).length = 8 ^ m := by
  rw [recWakePaths_length]
  have h10 : ∀ j < 13, recWakeCount 10 j = 8 := by
    have hchk : (List.range 13).all (fun j => recWakeCount 10 j == 8) = true := by decide +kernel
    intro j hj; exact beq_iff_eq.mp (List.all_eq_true.mp hchk j (List.mem_range.mpr hj))
  have hall : ∀ m' j, j < 13 → recWakeCount (10 * m') j = 8 ^ m' := by
    intro m'; induction m' with
    | zero => intro j _; rfl
    | succ m' ih =>
      intro j hj
      rw [show 10 * (m' + 1) = 10 + 10 * m' by omega]
      rw [recWakeCount_scale 10 (10 * m') (8 ^ m') (fun u hu => ih u hu) j hj, h10 j hj, Nat.pow_succ, Nat.mul_comm]
  exact hall m k.val k.isLt

end Rule30EtherThreeDeparture
end Ruliology.CellularAutomata
