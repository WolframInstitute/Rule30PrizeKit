module

public import Ruliology.CellularAutomata.Rule30EtherThree

/-!
# Rule 30, least period 3: the ether erodes, so there is no wall of any width

**Partial result.** Setting of `Rule30EtherThree`: `F` is a rule-30 evolution of the columns
`p ≥ 1` (`IsR30 F`) whose column `0` is ether column `j0` with phase offset `s` from time `t1` on.
The ether value of column `p` at time `t` is `ether3 (j0 + p) (t + s)`.

* `erosion3_fin`: if at time `t1` the columns `1..k` carry the ether, the columns beyond `k + w`
  carry the ether, and some column does not, then at some time `t ≤ t1 + 3 w + 6` one of the
  columns `1..k` differs from the ether. A finite perturbation always eats into the ether, at
  average speed at least `2/5` once it is in its wake.
* `no_wall`: for every attachment column `a` and every width `b ≥ 1`, a predicate `W` with
  `WallOK a b W` is empty. This extends the kernel certificate `no_wall_le_12`
  (`Rule30EtherThreeNoWall`) from widths `≤ 12` to all widths. So the period-3 ether-and-wall
  family of `Rule30EtherThree` is empty, and `absorption3_excludes` is vacuous for every wall:
  the ether-and-wall route to least period 3 is closed. The remaining open statements for least
  period 3 (`Q001`, `C3s001`, `C3w(011)`) do not involve walls. `AbsorptionT t001` is false
  (`Rule30EtherThreeNotAbsorption`).

**The argument.** Let the *front* `D` be the leftmost column that differs from the ether
(`Front`). Its *state* is the class of column `D`, `(j0 + D + 4 (t + s)) mod 12` (`cls`), together
with whether column `D + 1` is also a defect (`ubit`): 24 states. Columns `D - 2, D - 1` are ether,
so the next front and its state depend only on the class and on the columns `D + 1 .. D + 4`.
A kernel check over these 576 local patterns (`cert_all`) shows:

* exactly one state, `B = (class 10, D + 1 defective)`, can send the front three or more columns to
  the right in one step; every other next front lies in `D - 1 .. D + 2` and is not `B`;
* from `B` the front either moves by exactly `+2` into a good state, or jumps right by `≥ 3`;
  if it lands in `B` again, the class equation forces a jump of at least `8`;
* a potential `ψ ∈ [0, 10]` on the 23 good states (`psiTab`) satisfies
  `5 ΔD + 2 + ψ(new) ≤ ψ(old)` on every step from a good state.

`front_step` turns this into a statement about `F` (for `D ≥ 2`; column `0` is forced, not
computed). Hence the good states are closed and `5 D + 2 t + ψ` does not increase (`wake_good`):
the front moves left at average speed at least `2/5`. For a finite perturbation the rightmost
defect `R` moves right by exactly one column per step (`redge_step`: rule 30 is permutive in its
left input) and `D ≤ R`. A `B → B` step gains `≥ 8` on `R`'s `1`, so the initial run of `B` steps
is shorter than `(R - D) / 7 + 1 ≤ (w - 1) / 7 + 1` (`run_bad`); after it the front is good and at
most `w + n + 1` columns right of `k`, and the potential brings it to `≤ k` in time. The arithmetic
gives `3 w + 6`.

For `no_wall`: from a wall state at phase `< 3`, put the ether on columns `1..k`
(`k ≡ a mod 12`), the strip on `k + 1 .. k + b`, a flipped cell at `k + b + 1` and the ether beyond
(`wallCfg`), and drive column `0` with the ether (`Rule30Ether.drv`). `trap_invariant3` keeps
columns `1..k` ether forever, and `erosion3_fin` (with `w = b + 1`) breaks them.

The certificate and the potential come from an exhaustive computation (two independent code
paths); here they are checked by the kernel (`decide +kernel`, about two seconds).
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30EtherThreeErosion

open Ruliology.CellularAutomata
open Rule30EtherThree Rule30Jen Rule30Ether

/-! ### The local certificate -/

/-- The potential `ψ` on front states `(class, next column defective)`. -/
def psiTab (g : Nat) (u : Bool) : Nat :=
  (if u then [0, 1, 2, 3, 4, 5, 0, 7, 2, 3, 0, 2] else [0, 1, 2, 0, 10, 5, 6, 7, 8, 9, 4, 5]).getD g 0

/-- The single bad front state `B = (class 10, next column defective)`. -/
def isBad (g : Nat) (u : Bool) : Bool := g == 10 && u

/-- New cells at columns `D - 1 + i` (`i ≤ 4`) when columns `D - 2, D - 1` carry the ether, column `D`
is a defect, and columns `D + 1 .. D + 4` are `x1 .. x4`; column `D` is ether column `c`, phase `φ`. -/
def nC (c φ : Nat) (x1 x2 x3 x4 : Bool) : Nat → Bool
  | 0 => rule (ether3 (c + 10) φ) (ether3 (c + 11) φ) (!ether3 c φ)
  | 1 => rule (ether3 (c + 11) φ) (!ether3 c φ) x1
  | 2 => rule (!ether3 c φ) x1 x2
  | 3 => rule x1 x2 x3
  | _ => rule x2 x3 x4

/-- Whether the new cell at column `D - 1 + i` is a defect. -/
def dC (c φ : Nat) (x1 x2 x3 x4 : Bool) (i : Nat) : Bool :=
  nC c φ x1 x2 x3 x4 i != ether3 (c + 11 + i) (φ + 1)

/-- Whether column `D + 1` is a defect. -/
def uC (c φ : Nat) (x1 : Bool) : Bool := x1 != ether3 (c + 1) φ

/-- The new front `D - 1 + i` is good, and the potential drops. -/
abbrev stepGood (c φ : Nat) (x1 x2 x3 x4 : Bool) (i : Nat) : Prop :=
  isBad ((c + 4 * φ + i + 3) % 12) (dC c φ x1 x2 x3 x4 (i + 1)) = false ∧
  (isBad ((c + 4 * φ) % 12) (uC c φ x1) = true → i = 3) ∧
  (isBad ((c + 4 * φ) % 12) (uC c φ x1) = false →
    5 * i + 2 + psiTab ((c + 4 * φ + i + 3) % 12) (dC c φ x1 x2 x3 x4 (i + 1)) ≤
      psiTab ((c + 4 * φ) % 12) (uC c φ x1) + 5)

/-- The certificate for one local pattern. -/
abbrev certAt (c φ : Nat) (x1 x2 x3 x4 : Bool) : Prop :=
  (∀ i, i < 4 → (∀ j, j < i → dC c φ x1 x2 x3 x4 j = false) → dC c φ x1 x2 x3 x4 i = true →
    stepGood c φ x1 x2 x3 x4 i) ∧
  ((∀ j, j < 4 → dC c φ x1 x2 x3 x4 j = false) → isBad ((c + 4 * φ) % 12) (uC c φ x1) = true)

set_option synthInstance.maxSize 1024 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **The local certificate** (12 ether columns × 3 phases × 16 right patterns = 576 cases). -/
theorem cert_all : ∀ c, c < 12 → ∀ φ, φ < 3 → ∀ x1 x2 x3 x4 : Bool, certAt c φ x1 x2 x3 x4 := by
  decide +kernel

theorem psiTab_le : ∀ g, g < 12 → ∀ u, psiTab g u ≤ 10 := by decide

/-! ### Fronts of an evolution -/

section
variable (F : Nat → Nat → Bool) (j0 s : Nat)

/-- The ether value at column `p`, time `t`. -/
def eth (j0 s p t : Nat) : Bool := ether3 (j0 + p) (t + s)

/-- `D` is the front at time `t`: columns `0 .. D - 1` are ether, column `D` is not. -/
def Front (t D : Nat) : Prop := (∀ p, p < D → F t p = eth j0 s p t) ∧ F t D ≠ eth j0 s D t

/-- `R` is the right edge at time `t`: column `R` is a defect and every column right of it is ether. -/
def REdge (t R : Nat) : Prop := F t R ≠ eth j0 s R t ∧ ∀ p, R < p → F t p = eth j0 s p t

/-- The class of column `D` at time `t`. -/
def cls (D t : Nat) : Nat := (j0 + D + 4 * (t + s)) % 12

/-- Whether column `D + 1` is a defect at time `t`. -/
def ubit (t D : Nat) : Bool := F t (D + 1) != eth j0 s (D + 1) t

/-- The front state at `(t, D)` is the bad state `B`. -/
def IsB (t D : Nat) : Prop := isBad (cls j0 s D t) (ubit F j0 s t D) = true

/-- The potential of the front state. -/
def psiF (t D : Nat) : Nat := psiTab (cls j0 s D t) (ubit F j0 s t D)

end

theorem eth_rule (j0 s q t : Nat) :
    eth j0 s (q + 1) (t + 1) = rule (eth j0 s q t) (eth j0 s (q + 1) t) (eth j0 s (q + 2) t) := by
  unfold eth
  rw [show t + 1 + s = (t + s) + 1 by omega, ether3_rule,
    ether3_congr (j := j0 + (q + 1) + 11) (j' := j0 + q) (by omega) rfl,
    show j0 + (q + 1) + 1 = j0 + (q + 2) by omega]

theorem rule_flip (a b c : Bool) : rule (!a) b c = !rule a b c := by
  cases a <;> cases b <;> cases c <;> rfl

theorem ne_eth {a b : Bool} (h : a ≠ b) : a = !b := by cases a <;> cases b <;> simp_all

theorem psiF_le (F : Nat → Nat → Bool) (j0 s t D : Nat) : psiF F j0 s t D ≤ 10 :=
  psiTab_le _ (Nat.mod_lt _ (by decide)) _

theorem isB_cls {F : Nat → Nat → Bool} {j0 s t D : Nat} (h : IsB F j0 s t D) : cls j0 s D t = 10 := by
  unfold IsB isBad at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

/-- The ether prefix shrinks by at most one column per step. -/
theorem prefix_step {F : Nat → Nat → Bool} (hF : IsR30 F) {j0 s t D : Nat}
    (h0 : F (t + 1) 0 = eth j0 s 0 (t + 1)) (hpre : ∀ p, p < D → F t p = eth j0 s p t) :
    ∀ p, p + 1 < D → F (t + 1) p = eth j0 s p (t + 1) := by
  intro p hp
  rcases p with _ | q
  · exact h0
  · rw [hF t q, eth_rule, hpre q (by omega), hpre (q + 1) (by omega), hpre (q + 2) (by omega)]

/-- **The right edge moves right by exactly one column per step** (rule 30 is permutive in its left input). -/
theorem redge_step {F : Nat → Nat → Bool} (hF : IsR30 F) {j0 s t R : Nat} (h : REdge F j0 s t R) :
    REdge F j0 s (t + 1) (R + 1) := by
  refine ⟨?_, fun p hp => ?_⟩
  · rw [hF t R, eth_rule, ne_eth h.1, h.2 (R + 1) (by omega), h.2 (R + 2) (by omega), rule_flip]
    cases rule (eth j0 s R t) (eth j0 s (R + 1) t) (eth j0 s (R + 2) t) <;> decide
  · obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [hF t q, eth_rule, h.2 q (by omega), h.2 (q + 1) (by omega), h.2 (q + 2) (by omega)]

theorem redge_add {F : Nat → Nat → Bool} (hF : IsR30 F) {j0 s t R : Nat} (h : REdge F j0 s t R) :
    ∀ n, REdge F j0 s (t + n) (R + n)
  | 0 => h
  | n + 1 => redge_step hF (redge_add hF h n)

theorem front_le_redge {F : Nat → Nat → Bool} {j0 s t D R : Nat} (hD : Front F j0 s t D)
    (hR : REdge F j0 s t R) : D ≤ R := by
  refine Nat.le_of_not_lt fun h => hR.1 (hD.1 R h)

/-- A least witness (core Lean only). -/
theorem exists_least {P : Nat → Prop} (n : Nat) (hn : P n) : ∃ m, P m ∧ ∀ q, q < m → ¬ P q := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : ∃ q, q < n ∧ P q
    · obtain ⟨q, hq, hPq⟩ := h; exact ih q hq hPq
    · exact ⟨n, hn, fun q hq hPq => h ⟨q, hq, hPq⟩⟩

/-- **One step of the front** (certified by `cert_all`). Assumes the front is at `D ≥ 2` (column `0`
is forced, so the local relaxation is only valid there) and that some defect exists at `t + 1`.
From a good state the next state is good and `5 D + ψ` drops by at least `2`; from `B` the front
either moves by exactly `+2` into a good state or jumps right by at least `3`. -/
theorem front_step {F : Nat → Nat → Bool} (hF : IsR30 F) {j0 s t D : Nat}
    (h0 : F (t + 1) 0 = eth j0 s 0 (t + 1)) (hD2 : 2 ≤ D) (hfr : Front F j0 s t D)
    (hex : ∃ p, F (t + 1) p ≠ eth j0 s p (t + 1)) :
    ∃ D', Front F j0 s (t + 1) D' ∧ D ≤ D' + 1 ∧
      ((¬ IsB F j0 s t D ∧ ¬ IsB F j0 s (t + 1) D' ∧
          5 * D' + 2 + psiF F j0 s (t + 1) D' ≤ 5 * D + psiF F j0 s t D) ∨
        (IsB F j0 s t D ∧ ¬ IsB F j0 s (t + 1) D' ∧ D' = D + 2) ∨
        (IsB F j0 s t D ∧ D + 3 ≤ D')) := by
  classical
  obtain ⟨E, rfl⟩ : ∃ E, D = E + 2 := ⟨D - 2, by omega⟩
  obtain ⟨c, hc⟩ : ∃ c, c = (j0 + (E + 2)) % 12 := ⟨_, rfl⟩
  obtain ⟨φ, hφ⟩ : ∃ φ, φ = (t + s) % 3 := ⟨_, rfl⟩
  -- the row at time `t`
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
  -- the row at time `t + 1`
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
  -- the front state at time `t`
  have hcls : cls j0 s (E + 2) t = (c + 4 * φ) % 12 := by unfold cls; omega
  have hub : ubit F j0 s t (E + 2) = uC c φ y1 := by
    unfold ubit uC
    rw [show E + 2 + 1 = E + 3 by omega, hy1,
      show eth j0 s (E + 3) t = ether3 (c + 1) φ from ether3_congr (by omega) (by omega)]
  -- the new front
  obtain ⟨D', hsp, hmin⟩ : ∃ D', F (t + 1) D' ≠ eth j0 s D' (t + 1) ∧
      ∀ p, p < D' → F (t + 1) p = eth j0 s p (t + 1) :=
    by
      obtain ⟨p0, hp0⟩ := hex
      obtain ⟨m, hm, hmin⟩ := exists_least (P := fun p => F (t + 1) p ≠ eth j0 s p (t + 1)) p0 hp0
      exact ⟨m, hm, fun p hp => Classical.not_not.1 (hmin p hp)⟩
  have hpre := prefix_step hF h0 hfr.1
  have hD'1 : E + 1 ≤ D' := by
    refine Nat.le_of_not_lt fun h => hsp (hpre D' (by omega))
  obtain ⟨i, rfl⟩ : ∃ i, D' = E + 1 + i := ⟨D' - (E + 1), by omega⟩
  refine ⟨E + 1 + i, ⟨hmin, hsp⟩, by omega, ?_⟩
  have hbefore : ∀ j, j < i → j ≤ 4 → dC c φ y1 y2 y3 y4 j = false := by
    intro j hj hj4
    cases h : dC c φ y1 y2 y3 y4 j
    · rfl
    · exact absurd (hmin (E + 1 + j) (by omega)) ((hd j hj4).1 h)
  have cert := cert_all c (by omega) φ (by omega) y1 y2 y3 y4
  have hIsB : IsB F j0 s t (E + 2) ↔ isBad ((c + 4 * φ) % 12) (uC c φ y1) = true := by
    unfold IsB; rw [hcls, hub]
  by_cases hi4 : i < 4
  · have hdi : dC c φ y1 y2 y3 y4 i = true := (hd i (by omega)).2 hsp
    have hg := cert.1 i hi4 (fun j hj => hbefore j hj (by omega)) hdi
    have hcls' : cls j0 s (E + 1 + i) (t + 1) = (c + 4 * φ + i + 3) % 12 := by unfold cls; omega
    have hub' : ubit F j0 s (t + 1) (E + 1 + i) = dC c φ y1 y2 y3 y4 (i + 1) := by
      unfold ubit dC
      rw [show E + 1 + i + 1 = E + 1 + (i + 1) by omega, hn (i + 1) (by omega), he (i + 1),
        show c + 11 + (i + 1) = c + 11 + (i + 1) from rfl]
    have hnB' : ¬ IsB F j0 s (t + 1) (E + 1 + i) := by
      unfold IsB; rw [hcls', hub', hg.1]; decide
    by_cases hB : isBad ((c + 4 * φ) % 12) (uC c φ y1) = true
    · exact Or.inr (Or.inl ⟨hIsB.2 hB, hnB', by have := hg.2.1 hB; omega⟩)
    · refine Or.inl ⟨fun h => hB (hIsB.1 h), hnB', ?_⟩
      have hp := hg.2.2 (by simpa using hB)
      unfold psiF; rw [hcls', hub', hcls, hub]
      omega
  · have hB := cert.2 (fun j hj => hbefore j (by omega) (by omega))
    exact Or.inr (Or.inr ⟨hIsB.2 hB, by omega⟩)

/-! ### The good set is closed, and the front erodes at speed `2/5` in it -/

/-- **(a) The wake.** Once the front state is good it stays good, and `5 D + 2 n + ψ` never
increases, until the front reaches a column `≤ k`. This holds for any right side, as long as a
defect exists at every time. -/
theorem wake_good {F : Nat → Nat → Bool} (hF : IsR30 F) {j0 s t1 k : Nat} (hk : 1 ≤ k)
    (h0 : ∀ t, t1 ≤ t → F t 0 = eth j0 s 0 t)
    (hex : ∀ t, t1 ≤ t → ∃ p, F t p ≠ eth j0 s p t) :
    ∀ n t D, t1 ≤ t → Front F j0 s t D → ¬ IsB F j0 s t D →
      (∃ t', t ≤ t' ∧ t' ≤ t + n ∧ ∃ p, 1 ≤ p ∧ p ≤ k ∧ F t' p ≠ eth j0 s p t') ∨
      (∃ D', Front F j0 s (t + n) D' ∧ ¬ IsB F j0 s (t + n) D' ∧
        5 * D' + 2 * n + psiF F j0 s (t + n) D' ≤ 5 * D + psiF F j0 s t D) := by
  intro n
  induction n with
  | zero =>
    intro t D _ hD hB
    refine Or.inr ⟨D, hD, hB, ?_⟩
    show 5 * D + 2 * 0 + psiF F j0 s t D ≤ _
    omega
  | succ n ih =>
    intro t D ht hD hB
    rcases ih t D ht hD hB with ⟨t', h1, h2, hp⟩ | ⟨D', hD', hB', hpot⟩
    · exact Or.inl ⟨t', h1, by omega, hp⟩
    · by_cases hDk : D' ≤ k
      · refine Or.inl ⟨t + n, by omega, by omega, D', ?_, hDk, hD'.2⟩
        refine Nat.pos_of_ne_zero fun h => hD'.2 ?_
        subst h; exact h0 (t + n) (by omega)
      · obtain ⟨D'', hD'', -, h | h | h⟩ :=
          front_step hF (h0 (t + n + 1) (by omega)) (by omega) hD' (hex (t + n + 1) (by omega))
        · refine Or.inr ⟨D'', ?_, ?_, ?_⟩
          · rw [show t + (n + 1) = t + n + 1 by omega]; exact hD''
          · rw [show t + (n + 1) = t + n + 1 by omega]; exact h.2.1
          · rw [show t + (n + 1) = t + n + 1 by omega]; omega
        · exact absurd h.1 hB'
        · exact absurd h.1 hB'

/-! ### (b) The bad state: a run of `B` steps is short -/

/-- From `B`, while `R - D < 7 m`, the front reaches a good state within `m` steps: each `B → B`
step moves the front right by at least `8` (class equation), while the right edge moves by `1`. -/
theorem run_bad {F : Nat → Nat → Bool} (hF : IsR30 F) {j0 s t1 : Nat}
    (h0 : ∀ t, t1 ≤ t → F t 0 = eth j0 s 0 t) :
    ∀ m t D R, t1 ≤ t → 2 ≤ D → Front F j0 s t D → IsB F j0 s t D → REdge F j0 s t R →
      R < D + 7 * m →
      ∃ n, n < m ∧ ∃ D', Front F j0 s (t + n + 1) D' ∧ ¬ IsB F j0 s (t + n + 1) D' ∧ 2 ≤ D' := by
  intro m
  induction m with
  | zero =>
    intro t D R _ _ hD _ hR hRD
    have := front_le_redge hD hR; omega
  | succ m ih =>
    intro t D R ht hD2 hD hB hR hRD
    have hR1 := redge_step hF hR
    obtain ⟨D', hD', hle, h | h | h⟩ := front_step hF (h0 (t + 1) (by omega)) hD2 hD ⟨R + 1, hR1.1⟩
    · exact absurd hB h.1
    · exact ⟨0, by omega, D', hD', h.2.1, by omega⟩
    · by_cases hB' : IsB F j0 s (t + 1) D'
      · have c1 := isB_cls hB
        have c2 := isB_cls hB'
        unfold cls at c1 c2
        have h8 : D + 8 ≤ D' := by omega
        have hD'R := front_le_redge hD' hR1
        obtain ⟨n, hn, D'', h1, h2, h3⟩ :=
          ih (t + 1) D' (R + 1) (by omega) (by omega) hD' hB' hR1 (by omega)
        refine ⟨n + 1, by omega, D'', ?_, ?_, h3⟩
        · rw [show t + (n + 1) + 1 = t + 1 + n + 1 by omega]; exact h1
        · rw [show t + (n + 1) + 1 = t + 1 + n + 1 by omega]; exact h2
      · exact ⟨0, by omega, D', hD', hB', by omega⟩

/-! ### (c) Erosion of a finite perturbation -/

/-- **Erosion3-fin.** Let `F` be a rule-30 evolution of the columns `p ≥ 1` whose column `0` is
ether column `j0` (phase offset `s`) from time `t1` on. If at time `t1` the columns `1..k` carry the
ether, the columns beyond `k + w` carry the ether, and some column does not, then within `3 w + 6`
steps one of the columns `1..k` leaves the ether. -/
theorem erosion3_fin {F : Nat → Nat → Bool} (hF : IsR30 F) (j0 s k w t1 : Nat) (hk : 1 ≤ k)
    (h0 : ∀ t, t1 ≤ t → F t 0 = ether3 j0 (t + s))
    (hL : ∀ p, 1 ≤ p → p ≤ k → F t1 p = ether3 (j0 + p) (t1 + s))
    (hR : ∀ p, k + w < p → F t1 p = ether3 (j0 + p) (t1 + s))
    (hD : ∃ p, F t1 p ≠ ether3 (j0 + p) (t1 + s)) :
    ∃ t, t1 ≤ t ∧ t ≤ t1 + 3 * w + 6 ∧
      ∃ p, 1 ≤ p ∧ p ≤ k ∧ F t p ≠ ether3 (j0 + p) (t + s) := by
  have h0' : ∀ t, t1 ≤ t → F t 0 = eth j0 s 0 t := fun t ht => by
    rw [h0 t ht]; unfold eth; rw [Nat.add_zero]
  obtain ⟨p0, hp0⟩ := hD
  have hp0' : F t1 p0 ≠ eth j0 s p0 t1 := hp0
  -- the right edge at time `t1`
  obtain ⟨R0, hQ, hminQ⟩ := exists_least (P := fun m => ∀ q, m < q → F t1 q = eth j0 s q t1)
    (k + w) (fun q hq => hR q hq)
  have hp0R : p0 ≤ R0 := Nat.le_of_not_lt fun h => hp0' (hQ p0 h)
  have hp0k : k < p0 := by
    refine Nat.lt_of_not_le fun h => hp0' ?_
    rcases Nat.eq_zero_or_pos p0 with h1 | h1
    · subst h1; exact h0' t1 (Nat.le_refl _)
    · exact hL p0 h1 h
  have hRw : R0 ≤ k + w := Nat.le_of_not_lt fun h => hminQ (k + w) h (fun q hq => hR q hq)
  obtain ⟨m', hm'⟩ : ∃ m', R0 = m' + 1 := ⟨R0 - 1, by omega⟩
  have hRdef : F t1 R0 ≠ eth j0 s R0 t1 := by
    intro hne
    refine hminQ m' (by omega) (fun q hq => ?_)
    by_cases hq' : q = R0
    · subst hq'; exact hne
    · exact hQ q (by omega)
  have hRE : REdge F j0 s t1 R0 := ⟨hRdef, hQ⟩
  have hex : ∀ t, t1 ≤ t → ∃ p, F t p ≠ eth j0 s p t := by
    intro t ht
    have h := redge_add hF hRE (t - t1)
    rw [show t1 + (t - t1) = t by omega] at h
    exact ⟨_, h.1⟩
  -- the front at time `t1`
  obtain ⟨D1, hD1, hminD⟩ := exists_least (P := fun p => F t1 p ≠ eth j0 s p t1) p0 hp0'
  have hfr1 : Front F j0 s t1 D1 := ⟨fun p hp => Classical.not_not.1 (hminD p hp), hD1⟩
  have hD1k : k < D1 := by
    refine Nat.lt_of_not_le fun h => hD1 ?_
    rcases Nat.eq_zero_or_pos D1 with h1 | h1
    · subst h1; exact h0' t1 (Nat.le_refl _)
    · exact hL D1 h1 h
  have hD1R := front_le_redge hfr1 hRE
  -- the good phase
  have finish : ∀ t0 D0, t1 ≤ t0 → Front F j0 s t0 D0 → ¬ IsB F j0 s t0 D0 →
      ∃ t, t0 ≤ t ∧ t ≤ t0 + (5 * (D0 - k) + 5) / 2 + 1 ∧
        ∃ p, 1 ≤ p ∧ p ≤ k ∧ F t p ≠ eth j0 s p t := by
    intro t0 D0 ht0 hD0 hB0
    rcases wake_good hF hk h0' hex ((5 * (D0 - k) + 5) / 2 + 1) t0 D0 ht0 hD0 hB0 with
      ⟨t', h1, h2, hp⟩ | ⟨D', hD', -, hpot⟩
    · exact ⟨t', h1, h2, hp⟩
    · have hψ := psiF_le F j0 s t0 D0
      by_cases hDk : D' ≤ k
      · refine ⟨t0 + ((5 * (D0 - k) + 5) / 2 + 1), by omega, by omega, D', ?_, hDk, hD'.2⟩
        refine Nat.pos_of_ne_zero fun h => hD'.2 ?_
        subst h; exact h0' _ (by omega)
      · omega
  by_cases hB1 : IsB F j0 s t1 D1
  · obtain ⟨n, hn, D0, hD0, hB0, -⟩ :=
      run_bad hF h0' ((R0 - D1) / 7 + 1) t1 D1 R0 (Nat.le_refl _) (by omega) hfr1 hB1 hRE (by omega)
    have hD0R := front_le_redge hD0 (redge_add hF hRE (n + 1))
    obtain ⟨t, h1, h2, hp⟩ := finish (t1 + n + 1) D0 (by omega) hD0 hB0
    exact ⟨t, by omega, by omega, hp⟩
  · obtain ⟨t, h1, h2, hp⟩ := finish t1 D1 (Nat.le_refl _) hfr1 hB1
    exact ⟨t, h1, by omega, hp⟩

/-! ### Corollary: no period-3 wall of any width -/

/-- The initial right half used against a wall state `r` of width `b` attached at column `k`:
ether, the strip, one flipped cell at `k + b + 1`, ether. -/
def wallCfg (φ k b r : Nat) (p : Nat) : Bool :=
  if k < p ∧ p ≤ k + b then r.testBit (p - k - 1)
  else if p = k + b + 1 then !ether3 p φ else ether3 p φ

/-- **No period-3 wall of any width.** For every attachment column `a` and every width `b ≥ 1`, a
predicate `W` with `WallOK a b W` is empty. This extends `no_wall_le_12` to all widths. -/
theorem no_wall (a b : Nat) (hb : 0 < b) {W : Nat → Nat → Prop} (hW : WallOK a b W) :
    ∀ φ r, ¬ W φ r := by
  have key : ∀ φ r, φ < 3 → ¬ W φ r := by
    intro φ r hφ hWr
    obtain ⟨k, hk⟩ : ∃ k, k = a % 12 + 12 := ⟨_, rfl⟩
    have hF := drv_isR30 (fun t => ether3 0 (t + φ)) (wallCfg φ k b r)
    have h0 : ∀ t, 0 ≤ t →
        drv (fun t => ether3 0 (t + φ)) (wallCfg φ k b r) t 0 = ether3 0 (t + φ) :=
      fun t _ => drv_col0 _ _ t
    have hE : ∀ p, 1 ≤ p → p ≤ k →
        drv (fun t => ether3 0 (t + φ)) (wallCfg φ k b r) 0 p = ether3 (0 + p) (0 + φ) := by
      intro p h1 h2
      rw [drv_init _ _ p h1, Nat.zero_add, Nat.zero_add]
      unfold wallCfg
      simp [show ¬ (k < p ∧ p ≤ k + b) by omega, show p ≠ k + b + 1 by omega]
    have hr : EncF (drv (fun t => ether3 0 (t + φ)) (wallCfg φ k b r)) b 0 k r := by
      refine ⟨hW.1 φ r hWr, fun i hi => ?_⟩
      rw [drv_init _ _ _ (by omega)]
      unfold wallCfg
      simp [show k < k + 1 + i ∧ k + 1 + i ≤ k + b by omega, show k + 1 + i - k - 1 = i by omega]
    have inv := trap_invariant3 hF hW hb 0 φ k 0 (by omega) h0 hE r hr
      (by rw [Nat.zero_add, Nat.mod_eq_of_lt hφ]; exact hWr)
    obtain ⟨t, -, -, p, hp1, hpk, hne⟩ := erosion3_fin hF 0 φ k (b + 1) 0 (by omega) h0 hE
      (fun p hp => by
        rw [drv_init _ _ p (by omega), Nat.zero_add, Nat.zero_add]
        unfold wallCfg
        simp [show ¬ (k < p ∧ p ≤ k + b) by omega, show p ≠ k + b + 1 by omega])
      ⟨k + b + 1, by
        rw [drv_init _ _ _ (by omega), Nat.zero_add, Nat.zero_add]
        unfold wallCfg
        simp [show ¬ (k < k + b + 1 ∧ k + b + 1 ≤ k + b) by omega]⟩
    have e := (inv t).1 p hpk
    rw [show 0 + t = t from Nat.zero_add t] at e
    exact hne e
  intro φ r hWr
  exact key ((φ + 1) % 3) _ (Nat.mod_lt _ (by decide)) (hW.2.2 φ r false hWr)

end Ruliology.CellularAutomata.Rule30EtherThreeErosion
