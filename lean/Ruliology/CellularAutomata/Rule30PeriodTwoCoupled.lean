module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryBarriers
public import Ruliology.CellularAutomata.Rule30Ether

/-!
# Rule 30, period 2: the coupled question `CQ01` and the ether as an infinite witness

`Q01` (`Rule30ZeroBoundary.Q01`) only uses the left half. An eventual period `2` also constrains
the right half: with the center black at the even steps, column `1` at every white step is the
complement of column `-1` (`Rule30PeriodTwo.p1_odd`), and the right half evolves as the half driven
by the alternating column (`Rule30Ether.drv`).

* `CQ01`: **the coupled question** (open). No pair of a finitely supported ZBL start `L` and a
  finitely supported right half `R` such that, with column `0` alternating black at the even steps,
  `R` evolves as the driven right half, column `-1` of `L` is black at every black step, and at
  every white step column `-1` of `L` is the complement of column `1` of `R`.
* `CQ01_of_Q01`: `Q01` implies `CQ01`. `no_eventual_period_two_of_CQ01`: `CQ01` excludes an
  eventually 2-periodic center column, for every transient.

**The ether.** The 7×4 ether of `Rule30Ether` is the orbit of `c7` from the two-sided barrier
(`c7_eq_ether`, up to a spatial shift of `4`). Read from its alternating column B4:
* `etherLeft_zbl`: its left half is a ZBL orbit (B3 is black wherever B4 is: `B4_imp_B3`);
* `ether_col1_black`, `ether_free_bits`: column `-1` is black at the black steps and the free bits
  alternate `0, 1, 0, 1, …`; `etherLeft_eq_Theta`: the ether's left half is the constrained start
  `Theta` of the alternating free bits;
* `etherRight_drv`, `ether_coupled_witness`: its right half is the right half driven by the
  alternating column, and the free bits are the complement of column `1` at the white steps.
So the ether satisfies every condition of `CQ01` except finite support: as for `Q01` (whose
infinite witness is the stripe, `Rule30ZeroBoundary.zrow_stripe`), finite support is essential.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30PeriodTwoCoupled

open Rule30Jen Rule30Prize Rule30ZeroBoundary
open Rule30Ether (ether ether_rule ether_congr drv drv_col0 drv_init cell_eq_drv)

/-! ### The coupled question -/

/-- The alternating column, black at the even steps. -/
def altCol (t : Nat) : Bool := t % 2 == 0

/-- **`CQ01`** (open): no finitely supported ZBL start `L` and finitely supported right half `R`
such that, with column `0` alternating black at the even steps, column `-1` of `L` is black at the
black steps and is the complement of column `1` of the driven right half at the white steps. -/
def CQ01 : Prop :=
  ¬ ∃ L R : Nat → Bool, FinSupp L ∧ FinSupp R ∧ (∀ s, zrow L (2 * s) 1 = true) ∧
    ∀ s, zrow L (2 * s + 1) 1 = !drv altCol R (2 * s + 1) 1

/-- `Q01` implies `CQ01`. -/
theorem CQ01_of_Q01 (hQ : Q01) : CQ01 := by
  rintro ⟨L, R, hL, -, hX, -⟩
  exact hQ L hL hX

/-- **`CQ01` excludes an eventually 2-periodic center column**, for every transient. (The constant
case is excluded by `Rule30Prize.center_not_eventually_constant`, through
`Rule30PeriodTwo.normalize`.) -/
theorem no_eventual_period_two_of_CQ01 (hC : CQ01) :
    ¬ ∃ T0, ∀ t, T0 ≤ t → center (t + 2) = center t := by
  rintro ⟨T0, hT0⟩
  obtain ⟨T, hT⟩ := Rule30PeriodTwo.normalize hT0
  have hw : ∀ t, T ≤ t → (center t && center (t + 1)) = false := by
    intro t ht
    obtain ⟨j, rfl | rfl⟩ : ∃ j, t = T + 2 * j ∨ t = T + 2 * j + 1 := ⟨(t - T) / 2, by omega⟩
    · show (cell (T + 2 * j) 0 && cell (T + 2 * j + 1) 0) = false
      rw [(hT j).2]; cases cell (T + 2 * j) 0 <;> rfl
    · show (cell (T + 2 * j + 1) 0 && cell (T + 2 * j + 1 + 1) 0) = false
      rw [(hT j).2]; rfl
  have hz := left_half_is_zbl hw
  have hdrv : (fun t => cell (T + t) 0) = altCol := by
    funext t
    obtain ⟨j, rfl | rfl⟩ : ∃ j, t = 2 * j ∨ t = 2 * j + 1 := ⟨t / 2, by omega⟩
    · rw [(hT j).1]; unfold altCol; simp
    · rw [show T + (2 * j + 1) = T + 2 * j + 1 by omega, (hT j).2]; unfold altCol
      simp [show (2 * j + 1) % 2 = 1 by omega]
  refine hC ⟨leftRow T, fun p => cell T (p : Int), ⟨T, leftRow_fin T⟩,
    ⟨T, fun p hp => Rule30Diagonals.cell_eq_false_of_gt T p (by omega)⟩, fun s => ?_, fun s => ?_⟩
  · rw [hz (2 * s) 1 (Nat.le_refl 1)]
    exact Rule30PeriodTwo.m1_even hT s
  · rw [hz (2 * s + 1) 1 (Nat.le_refl 1), ← hdrv, ← cell_eq_drv T (2 * s + 1) 1]
    show cell (T + 2 * s + 1) (-1) = !cell (T + 2 * s + 1) 1
    rw [Rule30PeriodTwo.p1_odd hT s]
    cases cell (T + 2 * s + 1) (-1) <;> rfl

/-! ### The ether as an infinite witness -/

open Rule30ZeroBoundaryBarriers (c7 evol_c7_shift evol_c7_period_mul)

theorem c7_ether_check : ∀ a : Nat, a < 7 → ∀ b : Nat, b < 4 →
    Rule30Realization.evol c7 b ((a : Int) + 4) = ether a b := by decide

/-- **`c7` is the ether** up to a spatial shift of `4`: column `j + 4` of the orbit of `c7` is ether
column `j`, at every time. -/
theorem c7_eq_ether (j t : Nat) : Rule30Realization.evol c7 t ((j : Int) + 4) = ether j t := by
  have hj : (j : Int) + 4 = ((j % 7 : Nat) : Int) + 4 + 7 * ((j / 7 : Nat) : Int) := by omega
  have ht : t = t % 4 + 4 * (t / 4) := by omega
  rw [hj, evol_c7_shift, ht, evol_c7_period_mul,
    ether_congr (j' := j % 7) (φ' := t % 4) (by omega) (by omega)]
  exact c7_ether_check _ (Nat.mod_lt _ (by decide)) _ (Nat.mod_lt _ (by decide))

/-- Kernel check on the ether columns: B3 is black wherever B4 is; B4 alternates; B3 is the
complement of B5 at the even phases. -/
theorem ether_check : (∀ φ, φ < 4 → ether 3 φ = true → ether 2 φ = true) ∧
    (∀ φ, φ < 4 → ether 3 φ = (φ % 2 == 1)) ∧
    (∀ φ, φ < 4 → φ % 2 = 0 → ether 2 φ = !ether 4 φ) ∧
    (∀ φ, φ < 4 → φ % 2 = 0 → ether 2 φ = (φ == 0)) := by decide

theorem ether_mod (j φ : Nat) : ether j φ = ether j (φ % 4) := ether_congr rfl (by omega)

/-- B3 is black wherever B4 is black. -/
theorem B4_imp_B3 (φ : Nat) (h : ether 3 φ = true) : ether 2 φ = true := by
  rw [ether_mod] at h ⊢
  exact ether_check.1 _ (Nat.mod_lt _ (by decide)) h

/-- The alternating column is B4, one phase later. -/
theorem altCol_eq_B4 (t : Nat) : altCol t = ether 3 (t + 1) := by
  rw [ether_mod, ether_check.2.1 _ (Nat.mod_lt _ (by decide))]
  unfold altCol
  rw [show (t + 1) % 4 % 2 = (t + 1) % 2 by omega]
  rcases Nat.mod_two_eq_zero_or_one t with h | h
  · rw [h, show (t + 1) % 2 = 1 by omega]; rfl
  · rw [h, show (t + 1) % 2 = 0 by omega]; rfl

/-- The left half of the ether, read leftwards from B4 as a ZBL start at phase `φ`: depth `k ≥ 1`
is ether column `3 - k (mod 7)`. -/
def etherLeft (φ : Nat) (k : Nat) : Bool := if k = 0 then false else ether (3 + 6 * k) φ

/-- **The ether's left half is a ZBL orbit**: replacing B4 by a white wall does not change it. -/
theorem etherLeft_zbl (φ : Nat) : ∀ t k, zrow (etherLeft φ) t k = etherLeft (φ + t) k := by
  intro t
  induction t with
  | zero =>
    intro k
    cases k with
    | zero => rfl
    | succ k => rfl
  | succ t ih =>
    intro k
    cases k with
    | zero => rfl
    | succ j =>
      rw [zrow_succ, ih, ih, ih]
      show _ = ether (3 + 6 * (j + 1)) (φ + (t + 1))
      rw [show φ + (t + 1) = (φ + t) + 1 by omega, ether_rule]
      have e1 : etherLeft (φ + t) (j + 2) = ether (3 + 6 * (j + 1) + 6) (φ + t) := by
        show ether (3 + 6 * (j + 2)) (φ + t) = _
        exact ether_congr (by omega) rfl
      have e2 : etherLeft (φ + t) (j + 1) = ether (3 + 6 * (j + 1)) (φ + t) := rfl
      rw [e1, e2]
      unfold rule
      congr 1
      cases j with
      | zero =>
        have h3 : ether (3 + 6 * (0 + 1) + 1) (φ + t) = ether 3 (φ + t) := ether_congr (by omega) rfl
        have h2 : ether (3 + 6 * (0 + 1)) (φ + t) = ether 2 (φ + t) := ether_congr (by omega) rfl
        rw [h3, h2, show etherLeft (φ + t) 0 = false from rfl]
        cases hb : ether 3 (φ + t)
        · rfl
        · rw [B4_imp_B3 _ hb]; rfl
      | succ i =>
        have e3 : etherLeft (φ + t) (i + 1) = ether (3 + 6 * (i + 1 + 1) + 1) (φ + t) := by
          show ether (3 + 6 * (i + 1)) (φ + t) = _
          exact ether_congr (by omega) rfl
        rw [e3]

/-- Column `-1` of the ether's left half is black at the black steps. -/
theorem ether_col1_black (s : Nat) : zrow (etherLeft 1) (2 * s) 1 = true := by
  rw [etherLeft_zbl]
  show ether (3 + 6 * 1) (1 + 2 * s) = true
  rw [ether_congr (j' := 2) (φ' := 1 + 2 * s) (by omega) rfl]
  apply B4_imp_B3
  rw [show 1 + 2 * s = 2 * s + 1 by omega, ← altCol_eq_B4]
  unfold altCol; simp

/-- The free bits of the ether's left half alternate `0, 1, 0, 1, …`. -/
theorem ether_free_bits (s : Nat) : zrow (etherLeft 1) (2 * s + 1) 1 = (s % 2 == 1) := by
  rw [etherLeft_zbl]
  show ether (3 + 6 * 1) (1 + (2 * s + 1)) = _
  rw [ether_congr (j' := 2) (φ' := (2 * s + 2) % 4) (by omega) (by omega),
    ether_check.2.2.2 _ (Nat.mod_lt _ (by decide)) (by omega)]
  rcases Nat.mod_two_eq_zero_or_one s with h | h
  · rw [show (2 * s + 2) % 4 = 2 by omega, h]; rfl
  · rw [show (2 * s + 2) % 4 = 0 by omega, h]; rfl

/-- The ether's left half is the constrained start with alternating free bits. -/
theorem etherLeft_eq_Theta : zrow (etherLeft 1) 0 = Theta (fun s => s % 2 == 1) :=
  Theta_unique ether_col1_black ether_free_bits

/-- The right half of the ether at phase `φ`: column `p` is ether column `3 + p`. -/
def etherRight (φ : Nat) (p : Nat) : Bool := ether (3 + p) φ

/-- **The ether's right half is the right half driven by the alternating column.** -/
theorem etherRight_drv : ∀ t p, drv altCol (etherRight 1) t p = ether (3 + p) (1 + t) := by
  intro t
  induction t with
  | zero =>
    intro p
    cases p with
    | zero => rw [drv_col0, altCol_eq_B4]
    | succ q => rw [drv_init _ _ _ (by omega)]; rfl
  | succ t ih =>
    intro p
    cases p with
    | zero => rw [drv_col0, altCol_eq_B4, show t + 1 + 1 = 1 + (t + 1) by omega]
    | succ q =>
      show rule (drv altCol (etherRight 1) t q) (drv altCol (etherRight 1) t (q + 1))
        (drv altCol (etherRight 1) t (q + 2)) = _
      rw [ih, ih, ih, show 1 + (t + 1) = (1 + t) + 1 by omega, ether_rule,
        ether_congr (j := 3 + q) (j' := 3 + (q + 1) + 6) (φ := 1 + t) (φ' := 1 + t) (by omega) rfl,
        ether_congr (j := 3 + (q + 2)) (j' := 3 + (q + 1) + 1) (φ := 1 + t) (φ' := 1 + t) (by omega) rfl]

/-- **The ether is an infinite coupled witness.** Its left half `etherLeft 1` and right half
`etherRight 1` (driven by the alternating column, black at the even steps) satisfy every condition
of `CQ01` except finite support. -/
theorem ether_coupled_witness :
    (∀ s, zrow (etherLeft 1) (2 * s) 1 = true) ∧
    (∀ s, zrow (etherLeft 1) (2 * s + 1) 1 = !drv altCol (etherRight 1) (2 * s + 1) 1) := by
  refine ⟨ether_col1_black, fun s => ?_⟩
  rw [etherLeft_zbl, etherRight_drv]
  show ether (3 + 6 * 1) (1 + (2 * s + 1)) = !ether (3 + 1) (1 + (2 * s + 1))
  rw [ether_congr (j' := 2) (φ' := (2 * s + 2) % 4) (by omega) (by omega),
    ether_congr (j := 3 + 1) (j' := 4) (φ' := (2 * s + 2) % 4) (by omega) (by omega)]
  exact ether_check.2.2.1 _ (Nat.mod_lt _ (by decide)) (by omega)

/-! ### Single-Variable `Theta` Reformulation of `CQ01` and Ether Spatio-Temporal Laws -/

/-- **Uniqueness of the Left Start in `CQ01` (`left_eq_theta_of_coupled`):** if `L` and `R` satisfy
the two coupling equations of `CQ01`, then `L` is uniquely determined by `R` via
`L = Theta (fun s => !drv altCol R (2 * s + 1) 1)` on all positive depths (and `zrow L 0 = Theta ...`). -/
theorem zrow_zero_eq_theta_of_coupled {L R : Nat → Bool}
    (h1 : ∀ s, zrow L (2 * s) 1 = true)
    (h2 : ∀ s, zrow L (2 * s + 1) 1 = !drv altCol R (2 * s + 1) 1) :
    zrow L 0 = Theta (fun s => !drv altCol R (2 * s + 1) 1) :=
  Theta_unique h1 h2

/-- **Single-Variable `Theta` Characterization of `CQ01` (`CQ01_iff_no_finSupp_theta_drv`):** `CQ01`
holds if and only if for every finitely supported right half `R`, the constrained left start
`Theta (fun s => !drv altCol R (2 * s + 1) 1)` is not finitely supported. -/
theorem CQ01_iff_no_finSupp_theta_drv :
    CQ01 ↔ ∀ R : Nat → Bool, FinSupp R → ¬ FinSupp (Theta (fun s => !drv altCol R (2 * s + 1) 1)) := by
  unfold CQ01
  constructor
  · intro hC R hR hTh
    refine hC ⟨Theta (fun s => !drv altCol R (2 * s + 1) 1), R, hTh, hR, ?_, ?_⟩
    · exact Theta_inX (fun s => !drv altCol R (2 * s + 1) 1)
    · exact Theta_free (fun s => !drv altCol R (2 * s + 1) 1)
  · rintro hTh ⟨L, R, hL, hR, h1, h2⟩
    have heq := zrow_zero_eq_theta_of_coupled h1 h2
    obtain ⟨N, hN⟩ := hL
    refine hTh R hR ⟨N, fun k hk => ?_⟩
    rw [← heq]
    have hk0 : k ≠ 0 := by omega
    simp [zrow, hk0, hN k hk]

/-- **Bridge from Staged `Rule30PeriodTwo.Q01` to `CQ01` (`CQ01_of_staged_Q01`):** the staged
left-half hypothesis `Rule30PeriodTwo.Q01` implies the coupled period-2 question `CQ01`. -/
theorem CQ01_of_staged_Q01 (hQ : Rule30PeriodTwo.Q01) : CQ01 :=
  CQ01_of_Q01 (Q01_iff_staged.mpr hQ)

/-- **Period-2 Law of `altCol` (`altCol_add_two`):** `altCol (t + 2) = altCol t`. -/
theorem altCol_add_two (t : Nat) : altCol (t + 2) = altCol t := by
  unfold altCol
  rw [Nat.add_mod_right]

/-- **Step-Flip Law of `altCol` (`altCol_succ`):** `altCol (t + 1) = !altCol t`. -/
theorem altCol_succ (t : Nat) : altCol (t + 1) = !altCol t := by
  unfold altCol
  rcases Nat.mod_two_eq_zero_or_one t with h | h <;> simp [h, show (t + 1) % 2 = (t % 2 + 1) % 2 by omega]

/-- **Temporal Period 4 of `etherLeft` (`etherLeft_period_four`):** `etherLeft (φ + 4) = etherLeft φ`. -/
theorem etherLeft_period_four (φ : Nat) :
    etherLeft (φ + 4) = etherLeft φ := by
  funext k
  unfold etherLeft
  split
  · rfl
  · exact ether_congr rfl (by omega)

/-- **Spatial Period 7 of `etherLeft` for Positive Depths (`etherLeft_depth_add_seven`):** for every
`k ≥ 1`, `etherLeft φ (k + 7) = etherLeft φ k`. -/
theorem etherLeft_depth_add_seven (φ : Nat) {k : Nat} (hk : 0 < k) :
    etherLeft φ (k + 7) = etherLeft φ k := by
  have hk0 : k ≠ 0 := by omega
  have hk7 : k + 7 ≠ 0 := by omega
  simp only [etherLeft, hk0, hk7, ↓reduceIte]
  exact ether_congr (by omega) rfl

/-- **Temporal Period 4 of `etherRight` (`etherRight_period_four`):** `etherRight (φ + 4) = etherRight φ`. -/
theorem etherRight_period_four (φ : Nat) :
    etherRight (φ + 4) = etherRight φ := by
  funext p
  unfold etherRight
  exact ether_congr rfl (by omega)

/-- **Spatial Period 7 of `etherRight` (`etherRight_col_add_seven`):** `etherRight φ (p + 7) = etherRight φ p`. -/
theorem etherRight_col_add_seven (φ p : Nat) :
    etherRight φ (p + 7) = etherRight φ p := by
  unfold etherRight
  exact ether_congr (by omega) rfl

/-- **Infinite Support of `etherLeft 1` (`not_finSupp_etherLeft_one`):** `etherLeft 1` is not
finitely supported (`¬ FinSupp (etherLeft 1)`). -/
theorem not_finSupp_etherLeft_one : ¬ FinSupp (etherLeft 1) := by
  rintro ⟨N, hN⟩
  let k := 7 * (N + 1)
  have hk : N < k := by dsimp [k]; omega
  have hfalse := hN k hk
  have hk0 : k ≠ 0 := by dsimp [k]; omega
  have he : etherLeft 1 k = true := by
    simp only [etherLeft, hk0, ↓reduceIte]
    rw [ether_congr (j := 3 + 6 * k) (j' := 3) (φ := 1) (φ' := 1) (by dsimp [k]; omega) rfl]
    decide
  rw [he] at hfalse
  exact Bool.noConfusion hfalse

/-- **Infinite Support of `etherRight 1` (`not_finSupp_etherRight_one`):** `etherRight 1` is not
finitely supported (`¬ FinSupp (etherRight 1)`). -/
theorem not_finSupp_etherRight_one : ¬ FinSupp (etherRight 1) := by
  rintro ⟨N, hN⟩
  let p := 7 * (N + 1)
  have hp : N < p := by dsimp [p]; omega
  have hfalse := hN p hp
  have he : etherRight 1 p = true := by
    unfold etherRight
    rw [ether_congr (j := 3 + p) (j' := 3) (φ := 1) (φ' := 1) (by dsimp [p]; omega) rfl]
    decide
  rw [he] at hfalse
  exact Bool.noConfusion hfalse

/-! ### Phase-3 Complementary Coupled Ether Witness, Distinctness of Ether Orbits, and All-Phase Infinite Support -/

/-- The alternating column equals `ether 3 (3 + t)` at every step `t` (`altCol_eq_B4_three`). -/
theorem altCol_eq_B4_three (t : Nat) : altCol t = ether 3 (3 + t) := by
  rw [← altCol_add_two t, altCol_eq_B4, show t + 2 + 1 = 3 + t by omega]

/-- **Column `-1` of `etherLeft 3` is Black at Even Steps (`ether3_col1_black`):** for every `s`,
`zrow (etherLeft 3) (2 * s) 1 = true`. -/
theorem ether3_col1_black (s : Nat) : zrow (etherLeft 3) (2 * s) 1 = true := by
  rw [etherLeft_zbl]
  show ether (3 + 6 * 1) (3 + 2 * s) = true
  rw [ether_congr (j' := 2) (φ' := 3 + 2 * s) (by omega) rfl]
  apply B4_imp_B3
  rw [← altCol_eq_B4_three (2 * s)]
  unfold altCol; simp

/-- **Complementary Free Bits of `etherLeft 3` (`ether3_free_bits`):** at odd steps `2 * s + 1`,
column `-1` of `etherLeft 3` alternates `true, false, true, false, ...` (`s % 2 == 0`). -/
theorem ether3_free_bits (s : Nat) : zrow (etherLeft 3) (2 * s + 1) 1 = (s % 2 == 0) := by
  rw [etherLeft_zbl]
  show ether (3 + 6 * 1) (3 + (2 * s + 1)) = _
  rw [ether_congr (j' := 2) (φ' := (2 * s + 4) % 4) (by omega) (by omega),
    ether_check.2.2.2 _ (Nat.mod_lt _ (by decide)) (by omega)]
  rcases Nat.mod_two_eq_zero_or_one s with h | h
  · rw [show (2 * s + 4) % 4 = 0 by omega, h]
  · rw [show (2 * s + 4) % 4 = 2 by omega, h]; rfl

/-- **Exact Free-Bit Complementarity Between `etherLeft 3` and `etherLeft 1`
(`ether3_free_bits_eq_not_ether1`):** at every odd step `2 * s + 1`,
`zrow (etherLeft 3) (2 * s + 1) 1 = !zrow (etherLeft 1) (2 * s + 1) 1`. -/
theorem ether3_free_bits_eq_not_ether1 (s : Nat) :
    zrow (etherLeft 3) (2 * s + 1) 1 = !zrow (etherLeft 1) (2 * s + 1) 1 := by
  rw [ether3_free_bits, ether_free_bits]
  rcases Nat.mod_two_eq_zero_or_one s with h | h <;> simp [h]

/-- **`etherLeft 3` as a Constrained `Theta` Start (`etherLeft3_eq_Theta`):**
`zrow (etherLeft 3) 0 = Theta (fun s => s % 2 == 0)`. -/
theorem etherLeft3_eq_Theta : zrow (etherLeft 3) 0 = Theta (fun s => s % 2 == 0) :=
  Theta_unique ether3_col1_black ether3_free_bits

/-- **Driven Evolution of `etherRight 3` (`etherRight3_drv`):** driving `etherRight 3` by `altCol`
yields `ether (3 + p) (3 + t)` at every step `t` and column `p`. -/
theorem etherRight3_drv : ∀ t p, drv altCol (etherRight 3) t p = ether (3 + p) (3 + t) := by
  intro t
  induction t with
  | zero =>
    intro p
    cases p with
    | zero => rw [drv_col0, altCol_eq_B4_three]
    | succ q => rw [drv_init _ _ _ (by omega)]; rfl
  | succ t ih =>
    intro p
    cases p with
    | zero => rw [drv_col0, altCol_eq_B4_three, show 3 + (t + 1) = 3 + t + 1 by omega]
    | succ q =>
      show rule (drv altCol (etherRight 3) t q) (drv altCol (etherRight 3) t (q + 1))
        (drv altCol (etherRight 3) t (q + 2)) = _
      rw [ih, ih, ih, show 3 + (t + 1) = (3 + t) + 1 by omega, ether_rule,
        ether_congr (j := 3 + q) (j' := 3 + (q + 1) + 6) (φ := 3 + t) (φ' := 3 + t) (by omega) rfl,
        ether_congr (j := 3 + (q + 2)) (j' := 3 + (q + 1) + 1) (φ := 3 + t) (φ' := 3 + t) (by omega) rfl]

/-- **Phase-3 Coupled Ether Witness (`ether3_coupled_witness`):** the pair `(etherLeft 3, etherRight 3)`
is a second infinite witness satisfying the full coupled `CQ01` system under `altCol`. -/
theorem ether3_coupled_witness :
    (∀ s, zrow (etherLeft 3) (2 * s) 1 = true) ∧
    (∀ s, zrow (etherLeft 3) (2 * s + 1) 1 = !drv altCol (etherRight 3) (2 * s + 1) 1) := by
  refine ⟨ether3_col1_black, fun s => ?_⟩
  rw [etherLeft_zbl, etherRight3_drv]
  show ether (3 + 6 * 1) (3 + (2 * s + 1)) = !ether (3 + 1) (3 + (2 * s + 1))
  rw [ether_congr (j' := 2) (φ' := (2 * s + 4) % 4) (by omega) (by omega),
    ether_congr (j := 3 + 1) (j' := 4) (φ' := (2 * s + 4) % 4) (by omega) (by omega)]
  exact ether_check.2.2.1 _ (Nat.mod_lt _ (by decide)) (by omega)

/-- **Distinctness of the Two Coupled Left Ether Starts (`etherLeft_three_ne_one`):**
`etherLeft 3 ≠ etherLeft 1`. -/
theorem etherLeft_three_ne_one : etherLeft 3 ≠ etherLeft 1 := by
  intro h
  have h1 : zrow (etherLeft 3) 1 1 = zrow (etherLeft 1) 1 1 := by rw [h]
  have ha := ether3_free_bits 0
  have hb := ether_free_bits 0
  simp only [Nat.mul_zero, Nat.zero_add] at ha hb
  rw [ha, hb] at h1
  revert h1; decide

/-- **Distinctness of the Two Coupled Right Ether Starts (`etherRight_three_ne_one`):**
`etherRight 3 ≠ etherRight 1`. -/
theorem etherRight_three_ne_one : etherRight 3 ≠ etherRight 1 := by
  intro h
  have hdrv : (!drv altCol (etherRight 3) 1 1) = (!drv altCol (etherRight 1) 1 1) := by rw [h]
  have hc3 := ether3_coupled_witness.2 0
  have hc1 := ether_coupled_witness.2 0
  simp only [Nat.mul_zero, Nat.zero_add] at hc3 hc1
  rw [← hc3, ← hc1] at hdrv
  have ha := ether3_free_bits 0
  have hb := ether_free_bits 0
  simp only [Nat.mul_zero, Nat.zero_add] at ha hb
  rw [ha, hb] at hdrv
  revert hdrv; decide

/-- At every phase `φ`, either `ether 2 φ = true` or `ether 4 φ = true` (`ether_two_or_four_true`). -/
theorem ether_two_or_four_true (φ : Nat) : ether 2 φ = true ∨ ether 4 φ = true := by
  rw [ether_mod 2 φ, ether_mod 4 φ]
  rcases Nat.mod_two_eq_zero_or_one (φ % 4) with hev | hodd
  · have hcomp := ether_check.2.2.1 (φ % 4) (Nat.mod_lt _ (by decide)) hev
    cases h4 : ether 4 (φ % 4)
    · left; rw [hcomp, h4]; rfl
    · right; rfl
  · left
    apply B4_imp_B3
    rw [ether_check.2.1 (φ % 4) (Nat.mod_lt _ (by decide))]
    simp [hodd]

/-- **All-Phase Infinite Support of `etherLeft` (`not_finSupp_etherLeft`):** for every phase
`φ : Nat`, `etherLeft φ` is not finitely supported (`¬ FinSupp (etherLeft φ)`). -/
theorem not_finSupp_etherLeft (φ : Nat) : ¬ FinSupp (etherLeft φ) := by
  rintro ⟨N, hN⟩
  rcases ether_two_or_four_true φ with h2 | h4
  · let k := 7 * (N + 1) + 1
    have hfalse := hN k (by dsimp [k]; omega)
    have hk0 : k ≠ 0 := by dsimp [k]; omega
    have he : etherLeft φ k = true := by
      simp only [etherLeft, hk0, ↓reduceIte]
      rw [ether_congr (j := 3 + 6 * k) (j' := 2) (φ := φ) (φ' := φ) (by dsimp [k]; omega) rfl]
      exact h2
    rw [he] at hfalse; exact Bool.noConfusion hfalse
  · let k := 7 * (N + 1) + 6
    have hfalse := hN k (by dsimp [k]; omega)
    have hk0 : k ≠ 0 := by dsimp [k]; omega
    have he : etherLeft φ k = true := by
      simp only [etherLeft, hk0, ↓reduceIte]
      rw [ether_congr (j := 3 + 6 * k) (j' := 4) (φ := φ) (φ' := φ) (by dsimp [k]; omega) rfl]
      exact h4
    rw [he] at hfalse; exact Bool.noConfusion hfalse

/-- **All-Phase Infinite Support of `etherRight` (`not_finSupp_etherRight`):** for every phase
`φ : Nat`, `etherRight φ` is not finitely supported (`¬ FinSupp (etherRight φ)`). -/
theorem not_finSupp_etherRight (φ : Nat) : ¬ FinSupp (etherRight φ) := by
  rintro ⟨N, hN⟩
  rcases ether_two_or_four_true φ with h2 | h4
  · let p := 7 * (N + 1) + 6
    have hfalse := hN p (by dsimp [p]; omega)
    have he : etherRight φ p = true := by
      unfold etherRight
      rw [ether_congr (j := 3 + p) (j' := 2) (φ := φ) (φ' := φ) (by dsimp [p]; omega) rfl]
      exact h2
    rw [he] at hfalse; exact Bool.noConfusion hfalse
  · let p := 7 * (N + 1) + 1
    have hfalse := hN p (by dsimp [p]; omega)
    have he : etherRight φ p = true := by
      unfold etherRight
      rw [ether_congr (j := 3 + p) (j' := 4) (φ := φ) (φ' := φ) (by dsimp [p]; omega) rfl]
      exact h4
    rw [he] at hfalse; exact Bool.noConfusion hfalse

/-- **All-Time Infinite Support of Evolved Left Ether Rows (`not_finSupp_zrow_etherLeft`):** for
every initial phase `φ : Nat` and step `t : Nat`, `¬ FinSupp (zrow (etherLeft φ) t)`. -/
theorem not_finSupp_zrow_etherLeft (φ t : Nat) : ¬ FinSupp (zrow (etherLeft φ) t) := by
  have heq : zrow (etherLeft φ) t = etherLeft (φ + t) := by
    funext k
    exact etherLeft_zbl φ t k
  rw [heq]
  exact not_finSupp_etherLeft (φ + t)

end Rule30PeriodTwoCoupled
end Ruliology.CellularAutomata
