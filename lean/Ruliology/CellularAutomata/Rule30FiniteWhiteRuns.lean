module

public import Ruliology.CellularAutomata.Rule30WhiteRunEight
public import Ruliology.CellularAutomata.Rule30FiniteBlackRuns
public import Ruliology.CellularAutomata.Rule30FiniteDiagonals
public import Ruliology.CellularAutomata.Rule30ZeroBoundaryBarriers

/-!
# The words `0^r 1 1`, `r ≥ 8`, for every finite configuration

`Rule30WhiteRunEight` shows that the center column of the single black cell is not eventually
`0^r 1 1` repeated, for `r ≥ 8`. The proof follows column `1` at the starts of the periods, through
the first black cell right of the center; the seed has one at every time because of its right
edge. Here the same argument runs for column `0` of the evolution of any configuration `x` with a
leftmost black cell (for Jen's theorem), given a black cell right of column `0` from some time on.
Translation then gives every column of every nonzero finite configuration, whose rightmost black
cell moves one cell right per step.

* `front_moves`, `period_lock`, `period_late`, `period_far`, `period_z1`, …, `period_z4`,
  `periodic_blocks`, `first_black`: the lemmas of `Rule30BlackRuns`, for column `0` of any
  evolution.
* `no_white_run_11_col0`: column `0` of `evol x` is not eventually `0^r 1 1` repeated (`r ≥ 8`),
  whatever the transient, for every `x` with a leftmost black cell and a black cell right of
  column `0` from some time on.
* `evol_right_edge`, `exists_rightmost`: the right edge of a configuration that is white right of
  some black cell, and the rightmost black cell of a nonzero finite configuration.
* `no_white_run_11_finite`: **every column of every nonzero finite configuration**: no column is
  eventually `0^r 1 1` repeated, for `r ≥ 8`.

Source: E. Jen, *Global properties of cellular automata*, J. Stat. Phys. 43 (1986) 219–242; the
exclusion is that of `Rule30WhiteRunEight`.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30FiniteWhiteRuns

open Rule30Jen Rule30Realization Rule30PeriodTwoSideways Rule30FiniteConfigs
open Rule30FiniteBlackRuns (nine_black)

section Local
variable (x : Int → Bool)

/-- During a white run of column `0`, a black cell in column `1` stays black. -/
theorem black_stays (a n : Nat) (hc : ∀ i, i < n → evol x (a + i) 0 = false)
    (h1 : evol x a 1 = true) : ∀ i, i ≤ n → evol x (a + i) 1 = true
  | 0, _ => by simpa using h1
  | i + 1, hi => by
    have ih := black_stays a n hc h1 i (by omega)
    show rule (evol x (a + i) (1 - 1)) (evol x (a + i) 1) (evol x (a + i) (1 + 1)) = true
    rw [show (1 : Int) - 1 = 0 by rfl, hc i (by omega), ih]
    rfl

/-- During a white run of column `0`, the first black cell right of it moves one column left per
step. -/
theorem front_moves (a ℓ n : Nat) (hc : ∀ i, i < n → evol x (a + i) 0 = false)
    (hw : ∀ p : Nat, 1 ≤ p → p ≤ ℓ → evol x a p = false)
    (hb : evol x a ((ℓ + 1 : Nat) : Int) = true) :
    ∀ i, i ≤ n → i ≤ ℓ →
      (∀ p : Nat, 1 ≤ p → p ≤ ℓ - i → evol x (a + i) p = false) ∧
        evol x (a + i) ((ℓ - i + 1 : Nat) : Int) = true
  | 0, _, _ => ⟨fun p h1 h2 => by simpa using hw p h1 (by omega), by simpa using hb⟩
  | i + 1, hin, hil => by
    obtain ⟨ihw, ihb⟩ := front_moves a ℓ n hc hw hb i (by omega) (by omega)
    have wh : ∀ q : Int, 0 ≤ q → q ≤ ((ℓ - i : Nat) : Int) → evol x (a + i) q = false := by
      intro q hq0 hq1
      by_cases hq : q = 0
      · subst hq; exact hc i (by omega)
      · have := ihw q.toNat (by omega) (by omega)
        rwa [show ((q.toNat : Nat) : Int) = q by omega] at this
    refine ⟨fun p h1 h2 => ?_, ?_⟩
    · show rule (evol x (a + i) ((p : Int) - 1)) (evol x (a + i) (p : Int))
        (evol x (a + i) ((p : Int) + 1)) = false
      rw [wh _ (by omega) (by omega), wh _ (by omega) (by omega), wh _ (by omega) (by omega)]
      rfl
    · show rule (evol x (a + i) (((ℓ - (i + 1) + 1 : Nat) : Int) - 1))
        (evol x (a + i) ((ℓ - (i + 1) + 1 : Nat) : Int))
        (evol x (a + i) (((ℓ - (i + 1) + 1 : Nat) : Int) + 1)) = true
      rw [wh _ (by omega) (by omega), wh _ (by omega) (by omega),
        show ((ℓ - (i + 1) + 1 : Nat) : Int) + 1 = ((ℓ - i + 1 : Nat) : Int) by omega, ihb]
      rfl

section Period
variable (a r : Nat)
  (hwr : ∀ i, i < r → evol x (a + i) 0 = false)
  (hb1 : evol x (a + r) 0 = true) (hb2 : evol x (a + r + 1) 0 = true)
include hwr hb1 hb2

/-- One period of `0^r 1 1` whose first black cell is at column `ℓ + 1 ≤ r - 7`: the next period
starts with a black cell in column 1. -/
theorem period_lock (hr : 8 ≤ r) (ℓ : Nat) (hℓ : ℓ ≤ r - 8)
    (hw : ∀ p : Nat, 1 ≤ p → p ≤ ℓ → evol x a p = false)
    (hb : evol x a ((ℓ + 1 : Nat) : Int) = true) :
    (∀ i, ℓ ≤ i → i ≤ r → evol x (a + i) 1 = true) ∧ evol x (a + r + 1) 1 = false ∧
      evol x (a + r + 2) 1 = true := by
  have hfront := (front_moves x a ℓ r hwr hw hb ℓ (by omega) (Nat.le_refl ℓ)).2
  rw [show ℓ - ℓ + 1 = 1 by omega] at hfront
  have hblk : ∀ i, ℓ ≤ i → i ≤ r → evol x (a + i) 1 = true := by
    intro i h1 h2
    have := black_stays x (a + ℓ) (r - ℓ) (fun j hj => by
      have := hwr (ℓ + j) (by omega); rwa [show a + (ℓ + j) = a + ℓ + j by omega] at this)
      (by simpa using hfront) (i - ℓ) (by omega)
    rwa [show a + ℓ + (i - ℓ) = a + i by omega] at this
  have hA := (nine_black x (a + (r - 8)) 1 (fun s hs => by
    have := hblk (r - 8 + s) (by omega) (by omega)
    rwa [show a + (r - 8 + s) = a + (r - 8) + s by omega] at this)).1
  rw [show a + (r - 8) + 9 = a + r + 1 by omega, show (1 : Int) + 1 = 2 by rfl] at hA
  have c1 : evol x (a + r + 1) 1 = false := by
    show rule (evol x (a + r) (1 - 1)) (evol x (a + r) 1) (evol x (a + r) (1 + 1)) = false
    rw [show (1 : Int) - 1 = 0 by rfl, hb1, hblk r (by omega) (Nat.le_refl r)]
    rfl
  refine ⟨hblk, c1, ?_⟩
  show rule (evol x (a + r + 1) (1 - 1)) (evol x (a + r + 1) 1) (evol x (a + r + 1) (1 + 1)) =
    true
  rw [show (1 : Int) - 1 = 0 by rfl, show (1 : Int) + 1 = 2 by rfl, hb2, c1, hA]
  rfl

/-- First black cell at column `ℓ + 1 ≤ r + 1`: the next period's first black cell is in column
1 or 2. -/
theorem period_late (ℓ : Nat) (hℓ : ℓ ≤ r)
    (hw : ∀ p : Nat, 1 ≤ p → p ≤ ℓ → evol x a p = false)
    (hb : evol x a ((ℓ + 1 : Nat) : Int) = true) :
    evol x (a + r + 2) 1 = true ∨ (evol x (a + r + 2) 1 = false ∧ evol x (a + r + 2) 2 = true) := by
  have hfront := (front_moves x a ℓ r hwr hw hb ℓ (by omega) (Nat.le_refl ℓ)).2
  rw [show ℓ - ℓ + 1 = 1 by omega] at hfront
  have hr1 : evol x (a + r) 1 = true := by
    have := black_stays x (a + ℓ) (r - ℓ) (fun j hj => by
      have := hwr (ℓ + j) (by omega); rwa [show a + (ℓ + j) = a + ℓ + j by omega] at this)
      (by simpa using hfront) (r - ℓ) (Nat.le_refl _)
    rwa [show a + ℓ + (r - ℓ) = a + r by omega] at this
  have c1 : evol x (a + r + 1) 1 = false := by
    show rule (evol x (a + r) (1 - 1)) (evol x (a + r) 1) (evol x (a + r) (1 + 1)) = false
    rw [show (1 : Int) - 1 = 0 by rfl, hb1, hr1]
    rfl
  cases h2 : evol x (a + r + 1) 2
  · left
    show rule (evol x (a + r + 1) (1 - 1)) (evol x (a + r + 1) 1) (evol x (a + r + 1) (1 + 1)) =
      true
    rw [show (1 : Int) - 1 = 0 by rfl, show (1 : Int) + 1 = 2 by rfl, hb2, c1, h2]
    rfl
  · right
    constructor
    · show rule (evol x (a + r + 1) (1 - 1)) (evol x (a + r + 1) 1)
        (evol x (a + r + 1) (1 + 1)) = false
      rw [show (1 : Int) - 1 = 0 by rfl, show (1 : Int) + 1 = 2 by rfl, hb2, c1, h2]
      rfl
    · show rule (evol x (a + r + 1) (2 - 1)) (evol x (a + r + 1) 2)
        (evol x (a + r + 1) (2 + 1)) = true
      rw [show (2 : Int) - 1 = 1 by rfl, c1, h2]
      rfl

omit hb1 hb2 in
/-- The configuration at time `a + r` when the first black cell started at column `r + z + 1`. -/
theorem period_far (z : Nat) (hz : 1 ≤ z)
    (hw : ∀ p : Nat, 1 ≤ p → p ≤ r + z → evol x a p = false)
    (hb : evol x a ((r + z + 1 : Nat) : Int) = true) :
    (∀ p : Nat, 1 ≤ p → p ≤ z → evol x (a + r) p = false) ∧
      evol x (a + r) ((z + 1 : Nat) : Int) = true := by
  have := front_moves x a (r + z) r hwr hw hb r (Nat.le_refl r) (by omega)
  rw [show r + z - r = z by omega] at this
  exact this

theorem period_z1 (hw : ∀ p : Nat, 1 ≤ p → p ≤ r + 1 → evol x a p = false)
    (hb : evol x a ((r + 1 + 1 : Nat) : Int) = true) :
    evol x (a + r + 2) 1 = false ∧ evol x (a + r + 2) 2 = true := by
  obtain ⟨fw, fb⟩ := period_far x a r hwr 1 (Nat.le_refl 1) hw hb
  have w1 : evol x (a + r) 1 = false := by simpa using fw 1 (Nat.le_refl 1) (Nat.le_refl 1)
  have b2 : evol x (a + r) 2 = true := by simpa using fb
  have c1 : evol x (a + r + 1) 1 = false := by
    show rule (evol x (a + r) (1 - 1)) (evol x (a + r) 1) (evol x (a + r) (1 + 1)) = false
    rw [show (1 : Int) - 1 = 0 by rfl, show (1 : Int) + 1 = 2 by rfl, hb1, w1, b2]; rfl
  have c2 : evol x (a + r + 1) 2 = true := by
    show rule (evol x (a + r) (2 - 1)) (evol x (a + r) 2) (evol x (a + r) (2 + 1)) = true
    rw [show (2 : Int) - 1 = 1 by rfl, w1, b2]; rfl
  constructor
  · show rule (evol x (a + r + 1) (1 - 1)) (evol x (a + r + 1) 1)
      (evol x (a + r + 1) (1 + 1)) = false
    rw [show (1 : Int) - 1 = 0 by rfl, show (1 : Int) + 1 = 2 by rfl, hb2, c1, c2]; rfl
  · show rule (evol x (a + r + 1) (2 - 1)) (evol x (a + r + 1) 2)
      (evol x (a + r + 1) (2 + 1)) = true
    rw [show (2 : Int) - 1 = 1 by rfl, c1, c2]; rfl

omit hb2 in
theorem period_z2 (hw : ∀ p : Nat, 1 ≤ p → p ≤ r + 2 → evol x a p = false)
    (hb : evol x a ((r + 2 + 1 : Nat) : Int) = true) :
    (∀ i, i ≤ r → evol x (a + i) 1 = false) ∧ evol x (a + r + 1) 1 = true := by
  refine ⟨fun i hi => ?_, ?_⟩
  · have := (front_moves x a (r + 2) r hwr hw hb i hi (by omega)).1 1 (Nat.le_refl 1) (by omega)
    simpa using this
  · obtain ⟨fw, _⟩ := period_far x a r hwr 2 (by omega) hw hb
    have w1 : evol x (a + r) 1 = false := by simpa using fw 1 (by omega) (by omega)
    have w2 : evol x (a + r) 2 = false := by simpa using fw 2 (by omega) (by omega)
    show rule (evol x (a + r) (1 - 1)) (evol x (a + r) 1) (evol x (a + r) (1 + 1)) = true
    rw [show (1 : Int) - 1 = 0 by rfl, show (1 : Int) + 1 = 2 by rfl, hb1, w1, w2]; rfl

theorem period_z3 (hw : ∀ p : Nat, 1 ≤ p → p ≤ r + 3 → evol x a p = false)
    (hb : evol x a ((r + 3 + 1 : Nat) : Int) = true) :
    evol x (a + r + 2) 1 = false ∧ evol x (a + r + 2) 2 = false ∧
      evol x (a + r + 2) 3 = true := by
  obtain ⟨fw, fb⟩ := period_far x a r hwr 3 (by omega) hw hb
  have w1 : evol x (a + r) 1 = false := by simpa using fw 1 (by omega) (by omega)
  have w2 : evol x (a + r) 2 = false := by simpa using fw 2 (by omega) (by omega)
  have w3 : evol x (a + r) 3 = false := by simpa using fw 3 (by omega) (by omega)
  have b4 : evol x (a + r) 4 = true := by simpa using fb
  have c1 : evol x (a + r + 1) 1 = true := by
    show rule (evol x (a + r) (1 - 1)) (evol x (a + r) 1) (evol x (a + r) (1 + 1)) = true
    rw [show (1 : Int) - 1 = 0 by rfl, show (1 : Int) + 1 = 2 by rfl, hb1, w1, w2]; rfl
  have c2 : evol x (a + r + 1) 2 = false := by
    show rule (evol x (a + r) (2 - 1)) (evol x (a + r) 2) (evol x (a + r) (2 + 1)) = false
    rw [show (2 : Int) - 1 = 1 by rfl, show (2 : Int) + 1 = 3 by rfl, w1, w2, w3]; rfl
  have c3 : evol x (a + r + 1) 3 = true := by
    show rule (evol x (a + r) (3 - 1)) (evol x (a + r) 3) (evol x (a + r) (3 + 1)) = true
    rw [show (3 : Int) - 1 = 2 by rfl, show (3 : Int) + 1 = 4 by rfl, w2, w3, b4]; rfl
  refine ⟨?_, ?_, ?_⟩
  · show rule (evol x (a + r + 1) (1 - 1)) (evol x (a + r + 1) 1)
      (evol x (a + r + 1) (1 + 1)) = false
    rw [show (1 : Int) - 1 = 0 by rfl, show (1 : Int) + 1 = 2 by rfl, hb2, c1, c2]; rfl
  · show rule (evol x (a + r + 1) (2 - 1)) (evol x (a + r + 1) 2)
      (evol x (a + r + 1) (2 + 1)) = false
    rw [show (2 : Int) - 1 = 1 by rfl, show (2 : Int) + 1 = 3 by rfl, c1, c2, c3]; rfl
  · show rule (evol x (a + r + 1) (3 - 1)) (evol x (a + r + 1) 3)
      (evol x (a + r + 1) (3 + 1)) = true
    rw [show (3 : Int) - 1 = 2 by rfl, c2, c3]; rfl

theorem period_z4 (z : Nat) (hz : 4 ≤ z) (hw : ∀ p : Nat, 1 ≤ p → p ≤ r + z → evol x a p = false)
    (hb : evol x a ((r + z + 1 : Nat) : Int) = true) :
    evol x (a + r + 2) 1 = false ∧ evol x (a + r + 2) 2 = true := by
  obtain ⟨fw, _⟩ := period_far x a r hwr z (by omega) hw hb
  have w1 : evol x (a + r) 1 = false := by simpa using fw 1 (by omega) (by omega)
  have w2 : evol x (a + r) 2 = false := by simpa using fw 2 (by omega) (by omega)
  have w3 : evol x (a + r) 3 = false := by simpa using fw 3 (by omega) (by omega)
  have w4 : evol x (a + r) 4 = false := by simpa using fw 4 (by omega) (by omega)
  have c1 : evol x (a + r + 1) 1 = true := by
    show rule (evol x (a + r) (1 - 1)) (evol x (a + r) 1) (evol x (a + r) (1 + 1)) = true
    rw [show (1 : Int) - 1 = 0 by rfl, show (1 : Int) + 1 = 2 by rfl, hb1, w1, w2]; rfl
  have c2 : evol x (a + r + 1) 2 = false := by
    show rule (evol x (a + r) (2 - 1)) (evol x (a + r) 2) (evol x (a + r) (2 + 1)) = false
    rw [show (2 : Int) - 1 = 1 by rfl, show (2 : Int) + 1 = 3 by rfl, w1, w2, w3]; rfl
  have c3 : evol x (a + r + 1) 3 = false := by
    show rule (evol x (a + r) (3 - 1)) (evol x (a + r) 3) (evol x (a + r) (3 + 1)) = false
    rw [show (3 : Int) - 1 = 2 by rfl, show (3 : Int) + 1 = 4 by rfl, w2, w3, w4]; rfl
  constructor
  · show rule (evol x (a + r + 1) (1 - 1)) (evol x (a + r + 1) 1)
      (evol x (a + r + 1) (1 + 1)) = false
    rw [show (1 : Int) - 1 = 0 by rfl, show (1 : Int) + 1 = 2 by rfl, hb2, c1, c2]; rfl
  · show rule (evol x (a + r + 1) (2 - 1)) (evol x (a + r + 1) 2)
      (evol x (a + r + 1) (2 + 1)) = true
    rw [show (2 : Int) - 1 = 1 by rfl, show (2 : Int) + 1 = 3 by rfl, c1, c2, c3]; rfl

end Period

/-- Column 1 is eventually periodic if it repeats a fixed block from some time on. -/
theorem periodic_blocks (B Q : Nat) (hQ : 0 < Q) (g : Nat → Bool)
    (h : ∀ j i, i < Q → evol x (B + j * Q + i) 1 = g i) :
    EventuallyPeriodic (fun t => evol x t (0 + 1)) := by
  refine ⟨B, Q, hQ, fun t ht => ?_⟩
  show evol x (t + Q) (0 + 1) = evol x t (0 + 1)
  rw [show (0 : Int) + 1 = 1 by rfl]
  have hdm := Nat.div_add_mod (t - B) Q
  generalize (t - B) / Q = q at hdm
  have hmod := Nat.mod_lt (t - B) hQ
  generalize (t - B) % Q = s at hdm hmod
  have hq1 : (q + 1) * Q = q * Q + Q := Nat.succ_mul q Q
  have hcomm : Q * q = q * Q := Nat.mul_comm Q q
  have e1 := h q s hmod
  have e2 := h (q + 1) s hmod
  rw [hq1] at e2
  rw [show t + Q = B + (q * Q + Q) + s by omega, e2, ← e1, show B + q * Q + s = t by omega]

theorem first_black_aux (t : Nat) : ∀ n : Nat, (∀ p : Nat, 1 ≤ p → p ≤ n → evol x t p = false) ∨
    ∃ ℓ, ℓ < n ∧ (∀ p : Nat, 1 ≤ p → p ≤ ℓ → evol x t p = false) ∧
      evol x t ((ℓ + 1 : Nat) : Int) = true
  | 0 => Or.inl (fun p h1 h2 => by omega)
  | n + 1 => by
    rcases first_black_aux t n with hw | ⟨ℓ, hℓ, hw, hb⟩
    · by_cases hc : evol x t ((n + 1 : Nat) : Int) = true
      · exact Or.inr ⟨n, by omega, hw, hc⟩
      · refine Or.inl (fun p h1 h2 => ?_)
        by_cases hp : p ≤ n
        · exact hw p h1 hp
        · have : p = n + 1 := by omega
          subst this
          simpa using hc
    · exact Or.inr ⟨ℓ, by omega, hw, hb⟩

/-- If some cell right of column `0` is black at time `t`, there is a first one. -/
theorem first_black (t : Nat) (h : ∃ q : Nat, 1 ≤ q ∧ evol x t q = true) :
    ∃ ℓ, (∀ p : Nat, 1 ≤ p → p ≤ ℓ → evol x t p = false) ∧
      evol x t ((ℓ + 1 : Nat) : Int) = true := by
  obtain ⟨q, hq1, hq⟩ := h
  rcases first_black_aux x t q with hw | ⟨ℓ, _, hw, hb⟩
  · rw [hw q hq1 (Nat.le_refl q)] at hq
    exact absurd hq (by decide)
  · exact ⟨ℓ, hw, hb⟩

end Local

/-! ### Column `0` of any evolution with a black cell on its right -/

/-- **The words `0^r 1 1`, `r ≥ 8`, are excluded in column `0`** of the evolution of every
configuration with a leftmost black cell that has a black cell right of column `0` from some time
on, whatever the transient. -/
theorem no_white_run_11_col0 (x : Int → Bool) {lo : Int} (hlo : x lo = true)
    (hzero : ∀ p, p < lo → x p = false) {T₁ : Nat}
    (hright : ∀ t, T₁ ≤ t → ∃ q : Nat, 1 ≤ q ∧ evol x t q = true)
    (T r t0 : Nat) (hr : 8 ≤ r)
    (hper : ∀ t, T ≤ t → evol x (t + (r + 2)) 0 = evol x t 0) (ht0 : T ≤ t0)
    (hw : ∀ i, i < r → evol x (t0 + i) 0 = false) (hb1 : evol x (t0 + r) 0 = true)
    (hb2 : evol x (t0 + r + 1) 0 = true) : False := by
  generalize hQdef : r + 2 = Q at hper
  have hQ : 0 < Q := by omega
  have hperk : ∀ k t, T ≤ t → evol x (t + k * Q) 0 = evol x t 0 :=
    periodic_mul (f := fun t => evol x t 0) hper
  -- start enough periods later that a black cell right of column `0` exists at every start
  have hmQ : T₁ + 1 ≤ (T₁ + 1) * Q := Nat.le_mul_of_pos_right (T₁ + 1) hQ
  generalize hAdef : t0 + (T₁ + 1) * Q = A
  have hMul : ∀ k, (k + 1) * Q = k * Q + Q := fun k => Nat.succ_mul k Q
  have hshift : ∀ k t, T ≤ t → evol x (t + (k + (T₁ + 1)) * Q) 0 = evol x t 0 :=
    fun k t ht => hperk (k + (T₁ + 1)) t ht
  have drvw : ∀ k i, i < r → evol x (A + k * Q + i) 0 = false := by
    intro k i hi
    have := hshift k (t0 + i) (by omega)
    rw [Nat.add_mul, show t0 + i + (k * Q + (T₁ + 1) * Q) = A + k * Q + i by omega] at this
    rw [this]; exact hw i hi
  have drvb1 : ∀ k, evol x (A + k * Q + r) 0 = true := by
    intro k
    have := hshift k (t0 + r) (by omega)
    rw [Nat.add_mul, show t0 + r + (k * Q + (T₁ + 1) * Q) = A + k * Q + r by omega] at this
    rw [this]; exact hb1
  have drvb2 : ∀ k, evol x (A + k * Q + r + 1) 0 = true := by
    intro k
    have := hshift k (t0 + r + 1) (by omega)
    rw [Nat.add_mul,
      show t0 + r + 1 + (k * Q + (T₁ + 1) * Q) = A + k * Q + r + 1 by omega] at this
    rw [this]; exact hb2
  have hnext : ∀ k, A + k * Q + r + 2 = A + (k + 1) * Q := by intro k; rw [hMul k]; omega
  -- column 1 black at the start of period k is absorbing
  have s0_step : ∀ k, evol x (A + k * Q) 1 = true → evol x (A + (k + 1) * Q) 1 = true := by
    intro k hk
    have := (period_lock x (A + k * Q) r (drvw k) (drvb1 k) (drvb2 k) hr 0 (by omega)
      (fun p h1 h2 => by omega) (by simpa using hk)).2.2
    rwa [hnext k] at this
  have late : ∀ k ℓ, ℓ ≤ r → (∀ p : Nat, 1 ≤ p → p ≤ ℓ → evol x (A + k * Q) p = false) →
      evol x (A + k * Q) ((ℓ + 1 : Nat) : Int) = true →
      evol x (A + (k + 1) * Q) 1 = true ∨
        (evol x (A + (k + 1) * Q) 1 = false ∧ evol x (A + (k + 1) * Q) 2 = true) := by
    intro k ℓ hℓ hwℓ hbℓ
    have := period_late x (A + k * Q) r (drvw k) (drvb1 k) (drvb2 k) ℓ hℓ hwℓ hbℓ
    rwa [hnext k] at this
  have s1_step : ∀ k, (evol x (A + k * Q) 1 = false ∧ evol x (A + k * Q) 2 = true) →
      evol x (A + (k + 1) * Q) 1 = true ∨
        (evol x (A + (k + 1) * Q) 1 = false ∧ evol x (A + (k + 1) * Q) 2 = true) := by
    intro k hk
    exact late k 1 (by omega) (fun p hp1 hp2 => by
      have : p = 1 := by omega
      subst this; simpa using hk.1) (by simpa using hk.2)
  have step01 : ∀ k, (evol x (A + k * Q) 1 = true ∨
        (evol x (A + k * Q) 1 = false ∧ evol x (A + k * Q) 2 = true)) →
      (evol x (A + (k + 1) * Q) 1 = true ∨
        (evol x (A + (k + 1) * Q) 1 = false ∧ evol x (A + (k + 1) * Q) 2 = true)) := by
    intro k h
    rcases h with h | h
    · exact Or.inl (s0_step k h)
    · exact s1_step k h
  let Z2 : Nat → Prop := fun k =>
    (∀ p : Nat, 1 ≤ p → p ≤ r + 2 → evol x (A + k * Q) p = false) ∧
      evol x (A + k * Q) ((r + 2 + 1 : Nat) : Int) = true
  -- outside the exceptional class, the state is in class 0 or 1 two periods later
  have two_step : ∀ k, ¬ Z2 k → (evol x (A + (k + 2) * Q) 1 = true ∨
        (evol x (A + (k + 2) * Q) 1 = false ∧ evol x (A + (k + 2) * Q) 2 = true)) := by
    intro k hz
    have hkQ : 0 ≤ k * Q := Nat.zero_le _
    obtain ⟨ℓ, hwℓ, hbℓ⟩ := first_black x (A + k * Q) (hright _ (by omega))
    have via : (evol x (A + (k + 1) * Q) 1 = true ∨
        (evol x (A + (k + 1) * Q) 1 = false ∧ evol x (A + (k + 1) * Q) 2 = true)) →
        (evol x (A + (k + 2) * Q) 1 = true ∨
        (evol x (A + (k + 2) * Q) 1 = false ∧ evol x (A + (k + 2) * Q) 2 = true)) := by
      intro h
      have := step01 (k + 1) h
      rwa [show k + 1 + 1 = k + 2 by omega] at this
    by_cases c2 : ℓ ≤ r
    · exact via (late k ℓ c2 hwℓ hbℓ)
    by_cases c3 : ℓ = r + 1
    · subst c3
      obtain ⟨h1, h2⟩ := period_z1 x (A + k * Q) r (drvw k) (drvb1 k) (drvb2 k) hwℓ hbℓ
      rw [hnext k] at h1 h2
      exact via (Or.inr ⟨h1, h2⟩)
    by_cases c4 : ℓ = r + 2
    · subst c4
      exact absurd ⟨hwℓ, hbℓ⟩ hz
    by_cases c5 : ℓ = r + 3
    · subst c5
      obtain ⟨h1, h2, h3⟩ := period_z3 x (A + k * Q) r (drvw k) (drvb1 k) (drvb2 k) hwℓ hbℓ
      rw [hnext k] at h1 h2 h3
      have := late (k + 1) 2 (by omega) (fun p hp1 hp2 => by
        by_cases hp : p = 1
        · subst hp; simpa using h1
        · have : p = 2 := by omega
          subst this; simpa using h2) (by simpa using h3)
      rwa [show k + 1 + 1 = k + 2 by omega] at this
    · have hz4 : 4 ≤ ℓ - r := by omega
      obtain ⟨h1, h2⟩ := period_z4 x (A + k * Q) r (drvw k) (drvb1 k) (drvb2 k) (ℓ - r) hz4
        (fun p hp1 hp2 => hwℓ p hp1 (by omega))
        (by rw [show r + (ℓ - r) + 1 = ℓ + 1 by omega]; exact hbℓ)
      rw [hnext k] at h1 h2
      exact via (Or.inr ⟨h1, h2⟩)
  -- column 1 over one period in each of the three possible eventual classes
  have pattern0 : ∀ k, evol x (A + k * Q) 1 = true → ∀ i, i < Q →
      evol x (A + k * Q + i) 1 = decide (i ≤ r) := by
    intro k hk i hi
    obtain ⟨hblk, c1, _⟩ := period_lock x (A + k * Q) r (drvw k) (drvb1 k) (drvb2 k) hr 0
      (by omega) (fun p h1 h2 => by omega) (by simpa using hk)
    by_cases hir : i ≤ r
    · rw [hblk i (by omega) hir]; simp [hir]
    · have : i = r + 1 := by omega
      subst this; rw [show A + k * Q + (r + 1) = A + k * Q + r + 1 by omega, c1]; simp
  have pattern1 : ∀ k, (evol x (A + k * Q) 1 = false ∧ evol x (A + k * Q) 2 = true) →
      ∀ i, i < Q → evol x (A + k * Q + i) 1 = decide (1 ≤ i ∧ i ≤ r) := by
    intro k hk i hi
    have hw1 : ∀ p : Nat, 1 ≤ p → p ≤ 1 → evol x (A + k * Q) p = false := fun p hp1 hp2 => by
      have : p = 1 := by omega
      subst this; simpa using hk.1
    have hb1' : evol x (A + k * Q) ((1 + 1 : Nat) : Int) = true := by simpa using hk.2
    have hfront :=
      (front_moves x (A + k * Q) 1 r (drvw k) hw1 hb1' 1 (by omega) (Nat.le_refl 1)).2
    rw [show 1 - 1 + 1 = 1 by omega] at hfront
    have hblk : ∀ j, 1 ≤ j → j ≤ r → evol x (A + k * Q + j) 1 = true := by
      intro j h1 h2
      have := black_stays x (A + k * Q + 1) (r - 1) (fun m hm => by
        have := drvw k (1 + m) (by omega)
        rwa [show A + k * Q + (1 + m) = A + k * Q + 1 + m by omega] at this)
        (by simpa using hfront) (j - 1) (by omega)
      rwa [show A + k * Q + 1 + (j - 1) = A + k * Q + j by omega] at this
    have c1 : evol x (A + k * Q + r + 1) 1 = false := by
      show rule (evol x (A + k * Q + r) (1 - 1)) (evol x (A + k * Q + r) 1)
        (evol x (A + k * Q + r) (1 + 1)) = false
      rw [show (1 : Int) - 1 = 0 by rfl, drvb1 k, hblk r (by omega) (Nat.le_refl r)]
      rfl
    by_cases hi0 : i = 0
    · subst hi0; simpa using hk.1
    by_cases hir : i ≤ r
    · rw [hblk i (by omega) hir]; simp; omega
    · have : i = r + 1 := by omega
      subst this; rw [show A + k * Q + (r + 1) = A + k * Q + r + 1 by omega, c1]; simp
  have z2_pattern : ∀ k, Z2 k → ∀ i, i < Q → evol x (A + k * Q + i) 1 = decide (i = r + 1) := by
    intro k hk i hi
    obtain ⟨hw0, c1⟩ := period_z2 x (A + k * Q) r (drvw k) (drvb1 k) hk.1 hk.2
    by_cases hir : i ≤ r
    · rw [hw0 i hir]; simp; omega
    · have : i = r + 1 := by omega
      subst this; rw [show A + k * Q + (r + 1) = A + k * Q + r + 1 by omega, c1]; simp
  have h1 : EventuallyPeriodic (fun t => evol x t (0 + 1)) := by
    by_cases hall : ∀ k, Z2 k
    · exact periodic_blocks x A Q hQ (fun i => decide (i = r + 1))
        (fun j i hi => z2_pattern j (hall j) i hi)
    · have hex : ∃ k, ¬ Z2 k := Classical.byContradiction fun hne => hall fun k =>
        Classical.byContradiction fun hk => hne ⟨k, hk⟩
      obtain ⟨k, hk⟩ := hex
      have hU : ∀ j, evol x (A + (k + 2 + j) * Q) 1 = true ∨
          (evol x (A + (k + 2 + j) * Q) 1 = false ∧ evol x (A + (k + 2 + j) * Q) 2 = true) := by
        intro j
        induction j with
        | zero => simpa using two_step k hk
        | succ j ih =>
          rw [show k + 2 + (j + 1) = (k + 2 + j) + 1 by omega]
          exact step01 _ ih
      by_cases hs0 : ∃ j, evol x (A + (k + 2 + j) * Q) 1 = true
      · obtain ⟨j0, hj0⟩ := hs0
        have hall0 : ∀ j, evol x (A + (k + 2 + j0 + j) * Q) 1 = true := by
          intro j
          induction j with
          | zero => simpa using hj0
          | succ j ih =>
            rw [show k + 2 + j0 + (j + 1) = (k + 2 + j0 + j) + 1 by omega]
            exact s0_step _ ih
        refine periodic_blocks x (A + (k + 2 + j0) * Q) Q hQ (fun i => decide (i ≤ r))
          (fun j i hi => ?_)
        have := pattern0 (k + 2 + j0 + j) (hall0 j) i hi
        have hm : (k + 2 + j0 + j) * Q = (k + 2 + j0) * Q + j * Q := Nat.add_mul (k + 2 + j0) j Q
        rwa [hm, show A + ((k + 2 + j0) * Q + j * Q) + i = A + (k + 2 + j0) * Q + j * Q + i by
          omega] at this
      · have hall1 : ∀ j, evol x (A + (k + 2 + j) * Q) 1 = false ∧
            evol x (A + (k + 2 + j) * Q) 2 = true := by
          intro j
          rcases hU j with h | h
          · exact absurd ⟨j, h⟩ hs0
          · exact h
        refine periodic_blocks x (A + (k + 2) * Q) Q hQ (fun i => decide (1 ≤ i ∧ i ≤ r))
          (fun j i hi => ?_)
        have := pattern1 (k + 2 + j) (hall1 j) i hi
        have hm : (k + 2 + j) * Q = (k + 2) * Q + j * Q := Nat.add_mul (k + 2) j Q
        rwa [hm, show A + ((k + 2) * Q + j * Q) + i = A + (k + 2) * Q + j * Q + i by omega]
          at this
  have h0 : EventuallyPeriodic (fun t => evol x t 0) := ⟨T, Q, hQ, hper⟩
  exact not_adjacent hlo hzero 0 h0 h1

/-! ### Every column of every nonzero finite configuration -/

/-- **The right edge.** If `x` is black at `hi` and white right of it, the cell `hi + t` is black
at time `t`. -/
theorem evol_right_edge {x : Int → Bool} {hi : Int} (hhi : x hi = true)
    (hright : ∀ p, hi < p → x p = false) : ∀ t : Nat, evol x t (hi + t) = true
  | 0 => by
    show x (hi + ((0 : Nat) : Int)) = true
    simpa using hhi
  | t + 1 => by
    show rule (evol x t (hi + ((t + 1 : Nat) : Int) - 1)) (evol x t (hi + ((t + 1 : Nat) : Int)))
      (evol x t (hi + ((t + 1 : Nat) : Int) + 1)) = true
    rw [show hi + ((t + 1 : Nat) : Int) - 1 = hi + t by omega, evol_right_edge hhi hright t,
      Rule30FiniteDiagonals.evol_eq_false_of_gt hright t _ (by omega),
      Rule30FiniteDiagonals.evol_eq_false_of_gt hright t _ (by omega)]
    rfl

/-- A nonzero finite configuration has a rightmost black cell (the leftmost one of its
mirror image). -/
theorem exists_rightmost {x : Int → Bool} (hfin : FinConfig x) (hne : ∃ p, x p = true) :
    ∃ hi, x hi = true ∧ ∀ p, hi < p → x p = false := by
  obtain ⟨W, hW⟩ := hfin
  have hfin' : FinConfig (fun p => x (-p)) :=
    ⟨W, fun p hp => hW (-p) (by rw [Int.natAbs_neg]; exact hp)⟩
  obtain ⟨p, hp⟩ := hne
  obtain ⟨lo, hlo, hzero⟩ := exists_leftmost hfin' ⟨-p, by simpa using hp⟩
  refine ⟨-lo, hlo, fun q hq => ?_⟩
  have := hzero (-q) (by omega)
  simpa using this

/-- **The words `0^r 1 1`, `r ≥ 8`, are excluded in every column of every nonzero finite
configuration**: no column is eventually `0^r 1 1` repeated, whatever the transient. -/
theorem no_white_run_11_finite {x : Int → Bool} (hfin : FinConfig x) (hne : ∃ p, x p = true)
    (i : Int) (T r t0 : Nat) (hr : 8 ≤ r)
    (hper : ∀ t, T ≤ t → evol x (t + (r + 2)) i = evol x t i) (ht0 : T ≤ t0)
    (hw : ∀ k, k < r → evol x (t0 + k) i = false) (hb1 : evol x (t0 + r) i = true)
    (hb2 : evol x (t0 + r + 1) i = true) : False := by
  obtain ⟨lo, hlo, hzero⟩ := exists_leftmost hfin hne
  obtain ⟨hi, hhi, hright⟩ := exists_rightmost hfin hne
  -- translate column `i` to column `0`
  have hy : ∀ t p, evol (fun q => x (q + i)) t p = evol x t (p + i) := fun t p =>
    (Rule30ZeroBoundaryBarriers.evol_shift_all (x := fun q => x (q + i)) (x' := x) (d := i)
      (fun _ => rfl) t p).symm
  have hy0 : ∀ t, evol (fun q => x (q + i)) t 0 = evol x t i := fun t => by
    rw [hy, Int.zero_add]
  refine no_white_run_11_col0 (fun q => x (q + i)) (lo := lo - i)
    (by show x (lo - i + i) = true; rw [show lo - i + i = lo by omega]; exact hlo)
    (fun p hp => by show x (p + i) = false; exact hzero _ (by omega))
    (T₁ := (i - hi + 1).toNat) (fun t ht => ⟨(hi + t - i).toNat, by omega, ?_⟩)
    T r t0 hr (fun t ht => by rw [hy0, hy0]; exact hper t ht) ht0
    (fun k hk => by rw [hy0]; exact hw k hk) (by rw [hy0]; exact hb1) (by rw [hy0]; exact hb2)
  rw [hy, show (((hi + t - i).toNat : Nat) : Int) + i = hi + t by omega]
  exact evol_right_edge hhi hright t

/-! ### Uniqueness of the rightmost black cell and word-form `0^r 1 1` exclusion (`r ≥ 8`) -/

/-- **Uniqueness of the Rightmost Black Cell `hi` and Ordering `lo ≤ hi` (`rightmost_unique_and_leftmost_le`).** -/
theorem rightmost_unique_and_leftmost_le {x : Int → Bool} {lo hi1 hi2 : Int}
    (h1 : x hi1 = true) (hr1 : ∀ p, hi1 < p → x p = false)
    (h2 : x hi2 = true) (hr2 : ∀ p, hi2 < p → x p = false)
    (hlo : x lo = true) :
    hi1 = hi2 ∧ lo ≤ hi1 := by
  refine ⟨?_, ?_⟩
  · by_cases hlt : hi1 < hi2
    · rw [hr1 hi2 hlt] at h2; cases h2
    · by_cases hgt : hi2 < hi1
      · rw [hr2 hi1 hgt] at h1; cases h1
      · omega
  · by_cases hgt : hi1 < lo
    · rw [hr1 lo hgt] at hlo; cases hlo
    · omega

/-- **Word-Form Exclusion of `List.replicate r false ++ [true, true]` (`0^r 1 1`, `r ≥ 8`) for Every `FinConfig x` (`no_white_run_11_word_finite`).** -/
theorem no_white_run_11_word_finite {x : Int → Bool} (hfin : FinConfig x) (hne : ∃ p, x p = true)
    (i : Int) (r : Nat) (hr : 8 ≤ r) :
    ¬ ∃ T, ∀ t, T ≤ t →
      evol x t i = (List.replicate r false ++ [true, true]).getD ((t - T) % (r + 2)) false := by
  rintro ⟨T, hT⟩
  have hper : ∀ t, T ≤ t → evol x (t + (r + 2)) i = evol x t i := by
    intro t ht
    rw [hT (t + (r + 2)) (by omega), hT t ht,
        show t + (r + 2) - T = (t - T) + (r + 2) by omega, Nat.add_mod_right]
  have hget : ∀ (m k : Nat),
      (List.replicate m false ++ [true, true]).getD k false = decide (k = m ∨ k = m + 1) := by
    intro m
    induction m with
    | zero => rintro (_ | _ | k) <;> rfl
    | succ m ih =>
      rintro (_ | k)
      · rfl
      · rw [List.replicate_succ, List.cons_append, List.getD_cons_succ, ih k]
        exact decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩
  have hw : ∀ k, k < r → evol x (T + k) i = false := by
    intro k hk
    rw [hT (T + k) (by omega), show T + k - T = k by omega, Nat.mod_eq_of_lt (by omega), hget]
    exact decide_eq_false (by omega)
  have hb1 : evol x (T + r) i = true := by
    rw [hT (T + r) (by omega), show T + r - T = r by omega, Nat.mod_eq_of_lt (by omega), hget]
    exact decide_eq_true (by omega)
  have hb2 : evol x (T + r + 1) i = true := by
    rw [hT (T + r + 1) (by omega), show T + r + 1 - T = r + 1 by omega, Nat.mod_eq_of_lt (by omega), hget]
    exact decide_eq_true (by omega)
  exact no_white_run_11_finite hfin hne i T r T hr hper (Nat.le_refl T) hw hb1 hb2

end Rule30FiniteWhiteRuns
end Ruliology.CellularAutomata
