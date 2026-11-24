module

public import Ruliology.CellularAutomata.Rule30DoublingLanes

/-!
# Universal White-Gap Spectrum and Causal Run-Length Capture on `FirstLoss` Strips

This module establishes two certificate-free structural restrictions valid across all exponents
`e : Nat` on recurrent strips with `FirstLoss d a e` and `NextWhite d a b`:

1. **Backward white-gap spectrum (`backCol_eq_strip`, `odd_gap_ge_two_mul_add_five`,
   `firstLoss_gap_ge_21_of_pos`, `firstLoss_gap_ge_23_of_two_le`):**
   Reading sideways backward from `White d b` expresses `d (b - k)` as a carry-free local function
   of `x = d (b - 1)` of radius `⌊(k - 1)/2⌋`. Odd layers `2m + 1` are linear in `x (t + m)`, turning
   `d a ≡ false` into an `m`-bit feedback shift register with fixed point `0^m` and forcing
   `2 * e + 5 ≤ b - a` whenever `b - a` is odd. Paired de Bruijn pruning with Boolean matrix squaring
   (`pairedGapExclude_sound`) rules out every width `b - a ≤ 22` except `5` (`e = 0` only) and `21`
   (`e = 1` only), giving `a + 21 ≤ b` for `1 ≤ e` (sharp!) and `a + 23 ≤ b` for `2 ≤ e`.
2. **Universal causal factor and run-length capture (`causalCatch_sound`, `catch_of_nine_whites`,
   `catch_of_eight_blacks`):**
   Backed by `a + 21 ≤ b` (`1 ≤ e`) and `catch_of_firstLoss_le_four` (`e = 0`), a carry-branching
   causal evaluator proves that for *every* `e : Nat`, any `9` consecutive white ticks (`0^9`) on
   `d (a + 1)` catch within `9` wheels and any `8` consecutive black ticks (`1^8`) catch within `8`
   wheels—both thresholds sharp on genuine `e = 4` `FirstLoss` drivers.
-/

@[expose] public section

set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 3200000

namespace Ruliology.CellularAutomata.Rule30FirstLossBounds

open Ruliology.CellularAutomata
open Rule30AgedLeftDiagonals
open Ruliology.CellularAutomata.Rule30RecurrentStrip (Clock Reset)
open Ruliology.CellularAutomata.Rule30RootedWhiteReturns (Column)
open Ruliology.CellularAutomata.Rule30RelaxedWindows
open Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes (band pack testBit_pack pack_lt)
open Ruliology.CellularAutomata.Rule30DoublingLanes
  (band_eq_true period_mul_add period_between_whites catch_of_firstLoss_le_four trailingOnes trailingOnes_spec)

/-! ## 1. Carry-free backward recurrence from `White d b` -/

def backCol (x : Column) : Nat → Column
  | 0 => fun _ => false
  | 1 => x
  | k + 2 => fun t => xor (backCol x k (t + 1)) (backCol x (k + 1) t || backCol x k t)

theorem backCol_eq_strip {d : Nat → Column} (hd : Recurrence d) {b : Nat}
    (hwb : White d b) :
    ∀ k, k ≤ b → ∀ t, d (b - k) t = backCol (d (b - 1)) k t := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hkb t
    rcases k with _ | _ | k
    · simpa [backCol] using hwb t
    · rfl
    · have hstep := hd.2.2 (b - (k + 2)) t
      rw [show b - (k + 2) + 2 = b - k by omega,
          show b - (k + 2) + 1 = b - (k + 1) by omega] at hstep
      have hcancel : d (b - (k + 2)) t =
          xor (d (b - k) (t + 1)) (d (b - (k + 1)) t || d (b - k) t) := by
        rw [hstep]; cases d (b - (k + 2)) t <;> cases (d (b - (k + 1)) t || d (b - k) t) <;> rfl
      rw [hcancel, ih k (by omega) (by omega) (t + 1), ih (k + 1) (by omega) (by omega) t, ih k (by omega) (by omega) t]
      rfl

theorem backCol_explicit_two_to_five (x : Column) (t : Nat) :
    backCol x 2 t = x t ∧
    backCol x 3 t = xor (x t) (x (t + 1)) ∧
    backCol x 4 t = (x t && !(x (t + 1))) ∧
    backCol x 5 t = xor (x t) (x (t + 2)) := by
  dsimp only [backCol]
  cases x t <;> cases x (t + 1) <;> cases x (t + 2) <;> decide

/-! ## 2. Odd white-gap feedback shift register and `2 * e + 5 ≤ b - a` -/

def win (x : Column) (m t : Nat) : Nat := pack (fun j => x (t + j)) m

theorem win_lt (x : Column) (m t : Nat) : win x m t < 2 ^ m := pack_lt _ _

theorem win_mod (x : Column) (m t : Nat) : win x (m + 1) t % 2 ^ m = win x m t := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_mod_two_pow, win, win, testBit_pack, testBit_pack]
  by_cases hi : i < m
  · simp [hi, show i < m + 1 by omega]
  · simp [hi]

theorem win_div (x : Column) (m t : Nat) : win x (m + 1) t / 2 = win x m (t + 1) := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [show win x (m + 1) t / 2 = win x (m + 1) t >>> 1 from (Nat.shiftRight_eq_div_pow _ 1).symm,
      Nat.testBit_shiftRight, win, win, testBit_pack, testBit_pack]
  by_cases hi : i < m
  · simp [hi, show 1 + i < m + 1 by omega, show t + (1 + i) = t + 1 + i by omega]
  · simp [hi, show ¬ (1 + i < m + 1) by omega]

theorem win_top (x : Column) (m t : Nat) : (win x (m + 1) t).testBit m = x (t + m) := by
  rw [win, testBit_pack]; simp

def backPolys : Nat → (Nat → Bool) × (Nat → Bool)
  | 0 => (fun _ => false, fun _ => false)
  | m + 1 =>
    let p := backPolys m
    let ep' := fun w =>
      xor (p.1 (w / 2)) (xor (w.testBit m) (p.2 (w % 2 ^ m)) || p.1 (w % 2 ^ m))
    let op' := fun w =>
      xor (p.2 (w / 2)) (ep' w || xor (w.testBit m) (p.2 (w % 2 ^ m)))
    (ep', op')

theorem backPolys_spec : ∀ m : Nat,
    (backPolys m).1 0 = false ∧ (backPolys m).2 0 = false ∧
    (∀ x t, backCol x (2 * m) t = (backPolys m).1 (win x m t)) ∧
    (∀ x t, backCol x (2 * m + 1) t = xor (x (t + m)) ((backPolys m).2 (win x m t)))
  | 0 => ⟨rfl, rfl, fun _ _ => rfl, fun x t => by simp [backCol, backPolys]⟩
  | m + 1 => by
    obtain ⟨he0, ho0, he, ho⟩ := backPolys_spec m
    have he0' : (backPolys (m + 1)).1 0 = false := by
      simp [backPolys, he0, ho0]
    have ho0' : (backPolys (m + 1)).2 0 = false := by
      simp [backPolys, he0, ho0]
    refine ⟨he0', ho0', fun x t => ?_, fun x t => ?_⟩
    · show backCol x (2 * m + 2) t = _
      dsimp only [backCol, backPolys]
      rw [he x (t + 1), ho x t, he x t, win_div, win_mod, win_top]
    · show backCol x (2 * m + 1 + 2) t = _
      have he_next : backCol x (2 * m + 2) t = (backPolys (m + 1)).1 (win x (m + 1) t) := by
        dsimp only [backCol, backPolys]
        rw [he x (t + 1), ho x t, he x t, win_div, win_mod, win_top]
      change xor (backCol x (2 * m + 1) (t + 1)) (backCol x (2 * m + 2) t || backCol x (2 * m + 1) t) = _
      rw [ho x (t + 1), he_next, ho x t]
      dsimp only [backPolys]
      rw [win_div, win_mod, win_top, show t + 1 + m = t + (m + 1) by omega]
      exact Bool.xor_assoc _ _ _

theorem exists_collision : ∀ (N : Nat) (f : Nat → Nat),
    (∀ i, i ≤ N → f i < N) → ∃ i j, i < j ∧ j ≤ N ∧ f i = f j
  | 0, f, hf => absurd (hf 0 (Nat.le_refl 0)) (Nat.not_lt_zero _)
  | N + 1, f, hf => by
    by_cases hhit : ∃ i, i ≤ N ∧ f i = f (N + 1)
    · obtain ⟨i, hi, heq⟩ := hhit
      exact ⟨i, N + 1, by omega, Nat.le_refl _, heq⟩
    · let g : Nat → Nat := fun i => if f i < f (N + 1) then f i else f i - 1
      have hg : ∀ i, i ≤ N → g i < N := by
        intro i hi
        have hne : f i ≠ f (N + 1) := fun heq => hhit ⟨i, hi, heq⟩
        have h1 := hf i (by omega)
        have h2 := hf (N + 1) (Nat.le_refl _)
        dsimp only [g]; split <;> omega
      obtain ⟨i, j, hij, hjN, hgij⟩ := exists_collision N g hg
      have hnei : f i ≠ f (N + 1) := fun heq => hhit ⟨i, by omega, heq⟩
      have hnej : f j ≠ f (N + 1) := fun heq => hhit ⟨j, hjN, heq⟩
      refine ⟨i, j, hij, by omega, ?_⟩
      dsimp only [g] at hgij; split at hgij <;> split at hgij <;> omega

theorem period_gcd (f : Column) : ∀ a b : Nat,
    PeriodFrom f 0 a → PeriodFrom f 0 b → PeriodFrom f 0 (Nat.gcd a b) := by
  intro a
  induction a using Nat.strongRecOn with
  | ind a ih =>
    intro b ha hb
    by_cases ha0 : a = 0
    · subst ha0; simpa [Nat.gcd_zero_left] using hb
    · rw [Nat.gcd_rec]
      have hmod : PeriodFrom f 0 (b % a) := fun t _ => by
        have h1 := period_mul_add f ha (b / a) (t + b % a)
        rw [show t + b % a + b / a * a = t + (b % a + a * (b / a)) by rw [Nat.mul_comm]; omega,
            Nat.mod_add_div b a, hb t (Nat.zero_le _)] at h1
        exact h1.symm
      exact ih (b % a) (Nat.mod_lt b (by omega)) a hmod ha

theorem odd_dvd_two_pow {g : Nat} (hg1 : g % 2 = 1) : ∀ m : Nat, g ∣ 2 ^ m → g = 1
  | 0, hdvd => Nat.eq_one_of_dvd_one hdvd
  | m + 1, ⟨u, hu⟩ => by
    have hmul0 : (g * u) % 2 = 0 := by rw [← hu, Nat.pow_succ]; omega
    rw [Nat.mul_mod, hg1] at hmul0
    have hu0 : u % 2 = 0 := by rcases Nat.mod_two_eq_zero_or_one u with h | h <;> rw [h] at hmul0 <;> omega
    have hu_eq : u = 2 * (u / 2) := by omega
    have hdvd' : g ∣ 2 ^ m := by
      refine ⟨u / 2, ?_⟩
      rw [hu_eq, Nat.pow_succ] at hu
      have : 2 * 2 ^ m = 2 * (g * (u / 2)) := by
        calc 2 * 2 ^ m = 2 ^ m * 2 := Nat.mul_comm _ _
        _ = g * (2 * (u / 2)) := hu
        _ = 2 * (g * (u / 2)) := by rw [← Nat.mul_assoc, Nat.mul_comm g 2, Nat.mul_assoc]
      omega
    exact odd_dvd_two_pow hg1 m hdvd'

theorem dvd_two_pow_pred : ∀ (k : Nat) {g : Nat}, g ∣ 2 ^ (k + 1) → g < 2 ^ (k + 1) → g ∣ 2 ^ k
  | 0, g, hdvd, hlt => by
    rcases Nat.mod_two_eq_zero_or_one g with hg0 | hg1
    · have hg_zero : g = 0 := by omega
      subst hg_zero; obtain ⟨c, hc⟩ := hdvd; simp at hc
    · have hg_one := odd_dvd_two_pow hg1 1 hdvd
      subst hg_one; exact Nat.one_dvd _
  | k + 1, g, hdvd, hlt => by
    rcases Nat.mod_two_eq_zero_or_one g with hg0 | hg1
    · let g' := g / 2
      have hg_eq : g = 2 * g' := by omega
      obtain ⟨c, hc⟩ := hdvd
      have hdvd' : g' ∣ 2 ^ (k + 1) := by
        refine ⟨c, ?_⟩
        have : 2 * 2 ^ (k + 1) = 2 * (g' * c) := by
          calc 2 * 2 ^ (k + 1) = 2 ^ (k + 1) * 2 := Nat.mul_comm _ _
          _ = 2 ^ (k + 2) := (Nat.pow_succ _ _).symm
          _ = (2 * g') * c := by rw [← hg_eq]; exact hc
          _ = 2 * (g' * c) := Nat.mul_assoc _ _ _
        omega
      have hlt' : g' < 2 ^ (k + 1) := by
        have : 2 ^ (k + 2) = 2 ^ (k + 1) * 2 := Nat.pow_succ _ _
        omega
      obtain ⟨d, hd⟩ := dvd_two_pow_pred k hdvd' hlt'
      exact ⟨d, by rw [hg_eq, Nat.pow_succ, hd, Nat.mul_assoc, Nat.mul_comm d 2, ← Nat.mul_assoc, Nat.mul_comm g' 2]⟩
    · have hg_one := odd_dvd_two_pow hg1 (k + 2) hdvd
      subst hg_one; exact Nat.one_dvd _

theorem backCol_period (x : Column) {p : Nat} (hp : PeriodFrom x 0 p) :
    ∀ k, PeriodFrom (backCol x k) 0 p := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    rcases k with _ | _ | k
    · intro _ _; rfl
    · exact hp
    · intro t _
      dsimp only [backCol]
      rw [show t + p + 1 = t + 1 + p by omega,
          ih k (by omega) (t + 1) (Nat.zero_le _),
          ih (k + 1) (by omega) t (Nat.zero_le _),
          ih k (by omega) t (Nat.zero_le _)]

/-- **Universal Odd White-Gap Lower Bound:** on any `FirstLoss d a e` strip with `NextWhite d a b`,
if `b - a` is odd, then `2 * e + 5 ≤ b - a` (sharp at `e = 0`, where `b - a = 5`). -/
theorem odd_gap_ge_two_mul_add_five {d : Nat → Column} (hd : Recurrence d)
    (clocks : PrefixClocks d) {a e b : Nat} (loss : FirstLoss d a e) (hab : NextWhite d a b)
    (hodd : (b - a) % 2 = 1) : 2 * e + 5 ≤ b - a := by
  obtain ⟨m, hm_eq⟩ : ∃ m, b - a = 2 * m + 1 := ⟨(b - a) / 2, by omega⟩
  let x := d (b - 1)
  have hL : 0 < 2 * 2 ^ e := by have := Nat.two_pow_pos e; omega
  have hp1_L : PeriodFrom (d (a + 1)) 0 (2 * 2 ^ e) := fun t _ => by
    rw [show t + 2 * 2 ^ e = t + 2 ^ e + 2 ^ e by omega, loss.flip, loss.flip, Bool.not_not]
  have hx_L : PeriodFrom x 0 (2 * 2 ^ e) :=
    period_between_whites hd clocks loss.white hp1_L hab (b - 1) (by omega) (by omega)
  have hback_zero : ∀ t, backCol x (2 * m + 1) t = false := fun t => by
    have h := backCol_eq_strip hd hab.2.1 (2 * m + 1) (by omega) t
    rw [show b - (2 * m + 1) = a by omega, loss.white t] at h
    exact h.symm
  obtain ⟨he0, ho0, he_spec, ho_spec⟩ := backPolys_spec m
  let op := (backPolys m).2
  have hfsr : ∀ t, x (t + m) = op (win x m t) := fun t => by
    have h := (ho_spec x t).symm.trans (hback_zero t)
    dsimp only [op] at h ⊢
    generalize hb1 : x (t + m) = b1 at h ⊢
    generalize hb2 : (backPolys m).2 (win x m t) = b2 at h ⊢
    cases b1 <;> cases b2 <;> simp at h ⊢
  -- Rule out m = 0 (since b = a + 1 would make d(a+1) = d(b) white, contradicting loss.flip)
  rcases m with _ | m'
  · exfalso
    have hb_eq : b = a + 1 := by omega
    have hw1 : d (a + 1) 0 = false ∧ d (a + 1) (0 + 2 ^ e) = false := by
      rw [← hb_eq]; exact ⟨hab.2.1 0, hab.2.1 _⟩
    have hf := loss.flip 0
    rw [hw1.1, hw1.2] at hf; exact absurd hf (by decide)
  · let m := m' + 1
    have hstep_congr : ∀ t1 t2, win x m t1 = win x m t2 → win x m (t1 + 1) = win x m (t2 + 1) := by
      intro t1 t2 heq
      apply Nat.eq_of_testBit_eq; intro j
      rw [win, win, testBit_pack, testBit_pack]
      by_cases hj : j < m
      · simp only [hj, decide_true, Bool.true_and]
        by_cases hj1 : j + 1 < m
        · have hb := congrArg (fun v => v.testBit (j + 1)) heq
          simpa [win, testBit_pack, hj1, show t1 + (j + 1) = t1 + 1 + j by omega,
            show t2 + (j + 1) = t2 + 1 + j by omega] using hb
        · have hjm : j = m' := by omega
          rw [hjm, show t1 + 1 + m' = t1 + m by omega, show t2 + 1 + m' = t2 + m by omega,
              hfsr t1, hfsr t2, heq]
      · simp [hj]
    -- Show `win x m t ≠ 0` for all `t` (otherwise `x` becomes all `false` from `t` onward, hence globally)
    have hwin_pos : ∀ t, 0 < win x m t := by
      intro t0
      refine Classical.byContradiction fun hle => ?_
      have hw0 : win x m t0 = 0 := by omega
      have hall0 : ∀ u, win x m (t0 + u) = 0 := by
        intro u; induction u with
        | zero => simpa using hw0
        | succ u ih =>
          rw [show t0 + (u + 1) = (t0 + u) + 1 by omega]
          apply Nat.eq_of_testBit_eq; intro j
          rw [Nat.zero_testBit, win, testBit_pack]
          by_cases hj : j < m
          · simp only [hj, decide_true, Bool.true_and]
            by_cases hj1 : j + 1 < m
            · have hb := congrArg (fun v => v.testBit (j + 1)) ih
              simpa [win, testBit_pack, hj1, show t0 + u + (j + 1) = t0 + u + 1 + j by omega] using hb
            · have hjm : j = m' := by omega
              rw [hjm, show t0 + u + 1 + m' = t0 + u + m by omega, hfsr (t0 + u), ih]; exact ho0
          · simp [hj]
      have hx_false : ∀ t, x t = false := fun t => by
        have hge : t0 ≤ t + t0 * (2 * 2 ^ e) := by
          have : 1 ≤ 2 * 2 ^ e := hL
          have := Nat.mul_le_mul_left t0 this; omega
        rw [← period_mul_add x hx_L t0 t]
        have hb := congrArg (fun v => v.testBit 0) (hall0 (t + t0 * (2 * 2 ^ e) - t0))
        rw [Nat.zero_testBit, win, testBit_pack] at hb
        simp only [show 0 < m by omega, decide_true, Bool.true_and, Nat.add_zero] at hb
        rw [show t0 + (t + t0 * (2 * 2 ^ e) - t0) = t + t0 * (2 * 2 ^ e) by omega] at hb
        exact hb
      have hd1_false : ∀ t, d (a + 1) t = false := fun t => by
        rw [show a + 1 = b - 2 * m by omega, backCol_eq_strip hd hab.2.1 (2 * m) (by omega) t,
            he_spec x t]
        have hwx0 : win x m t = 0 := by
          apply Nat.eq_of_testBit_eq; intro j; simp [win, testBit_pack, hx_false]
        rw [hwx0]; exact he0
      have hf := loss.flip 0
      rw [hd1_false 0, hd1_false _] at hf; exact absurd hf (by decide)
    -- Pigeonhole on `2 ^ m - 1` nonzero states `win x m i - 1`
    have hN : ∀ i, i ≤ 2 ^ m - 1 → win x m i - 1 < 2 ^ m - 1 := fun i _ => by
      have h1 := hwin_pos i; have h2 := win_lt x m i; omega
    obtain ⟨i, j, hij, hj_le, heq_sub⟩ := exists_collision (2 ^ m - 1) (fun u => win x m u - 1) hN
    have heq_ij : win x m i = win x m j := by
      have := hwin_pos i; have := hwin_pos j; omega
    let p := j - i
    have hp_pos : 0 < p := by omega
    have hp_lt : p < 2 ^ m := by omega
    have htail_win : ∀ u, win x m (i + u + p) = win x m (i + u) := by
      intro u; induction u with
      | zero => simpa [p, show i + (j - i) = j by omega] using heq_ij.symm
      | succ u ih =>
        rw [show i + (u + 1) + p = (i + u + p) + 1 by omega,
            show i + (u + 1) = (i + u) + 1 by omega]
        exact hstep_congr _ _ ih
    have hx_p : PeriodFrom x 0 p := fun t _ => by
      have hge : i ≤ t + i * (2 * 2 ^ e) := by
        have := Nat.mul_le_mul_left i hL; omega
      have h1 := period_mul_add x hx_L i t
      have h2 := period_mul_add x hx_L i (t + p)
      have hw_eq := congrArg (fun v => v.testBit 0) (htail_win (t + i * (2 * 2 ^ e) - i))
      simp only [win, testBit_pack, show 0 < m by omega, decide_true, Bool.true_and, Nat.add_zero,
        show i + (t + i * (2 * 2 ^ e) - i) = t + i * (2 * 2 ^ e) by omega,
        show t + i * (2 * 2 ^ e) + p = t + p + i * (2 * 2 ^ e) by omega] at hw_eq
      exact h2.symm.trans (hw_eq.trans h1)
    let g := Nat.gcd p (2 ^ (e + 1))
    have hx_g : PeriodFrom x 0 g :=
      period_gcd x p (2 ^ (e + 1)) hx_p (by simpa [Nat.pow_succ, Nat.mul_comm] using hx_L)
    have hg_dvd : g ∣ 2 ^ (e + 1) := Nat.gcd_dvd_right p (2 ^ (e + 1))
    have hg_le : g ≤ p := Nat.le_of_dvd hp_pos (Nat.gcd_dvd_left p (2 ^ (e + 1)))
    by_cases hglt : g < 2 ^ (e + 1)
    · exfalso
      obtain ⟨c, hc⟩ := dvd_two_pow_pred e hg_dvd hglt
      have hx_2e : PeriodFrom x 0 (2 ^ e) := fun t _ => by
        rw [hc, Nat.mul_comm]; exact period_mul_add x hx_g c t
      have hd1_per := backCol_period x hx_2e (2 * m) 0 (Nat.zero_le _)
      have hd1_eq1 := backCol_eq_strip hd hab.2.1 (2 * m) (by omega) 0
      have hd1_eq2 := backCol_eq_strip hd hab.2.1 (2 * m) (by omega) (0 + 2 ^ e)
      rw [show b - 2 * m = a + 1 by omega] at hd1_eq1 hd1_eq2
      have hsame : d (a + 1) (0 + 2 ^ e) = d (a + 1) 0 :=
        hd1_eq2.trans (hd1_per.trans hd1_eq1.symm)
      rw [loss.flip 0] at hsame
      generalize hb0 : d (a + 1) 0 = b0 at hsame
      cases b0 <;> exact absurd hsame (by decide)
    · have hpow_lt : 2 ^ (e + 1) < 2 ^ m := by omega
      have he_lt_m : e + 1 < m := by
        refine Classical.byContradiction fun hge => ?_
        have : 2 ^ m ≤ 2 ^ (e + 1) := Nat.pow_le_pow_right (by decide) (by omega)
        omega
      omega

/-! ## 3. Fast bitwise paired de Bruijn pruning, matrix squaring, and sharp gap bounds -/

noncomputable def bpack (f : Nat → Bool) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Bool.rec (motive := fun _ => Nat) acc (acc ||| (1 <<< i)) (f i)) n

theorem bpack_eq_pack (f : Nat → Bool) (n : Nat) : bpack f n = pack f n := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [testBit_pack]
  induction n with
  | zero =>
    change (0 : Nat).testBit j = (decide (j < 0) && f j)
    simp [Nat.zero_testBit]
  | succ n ih =>
    change (Bool.rec (motive := fun _ => Nat) (bpack f n) (bpack f n ||| (1 <<< n)) (f n)).testBit j =
      (decide (j < n + 1) && f j)
    cases hfn : f n
    · dsimp only
      rw [ih]
      by_cases hjn : j = n
      · subst hjn; simp [hfn]
      · by_cases hlt : j < n
        · simp [hlt, show j < n + 1 by omega]
        · simp [hlt, show ¬ (j < n + 1) by omega]
    · dsimp only
      rw [Nat.testBit_or, ih, Nat.one_shiftLeft, Nat.testBit_two_pow]
      by_cases hjn : j = n
      · subst hjn; simp [hfn]
      · simp only [show ¬ (n = j) from Ne.symm hjn, decide_false, Bool.or_false]
        by_cases hlt : j < n
        · simp [hlt, show j < n + 1 by omega]
        · simp [hlt, show ¬ (j < n + 1) by omega]

theorem testBit_bpack (f : Nat → Bool) (n i : Nat) :
    (bpack f n).testBit i = (decide (i < n) && f i) := by
  rw [bpack_eq_pack, testBit_pack]

def onesMask (n : Nat) : Nat := (1 <<< n) - 1

theorem testBit_onesMask (n i : Nat) : (onesMask n).testBit i = decide (i < n) := by
  rw [onesMask, Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one]

theorem onesMask_eq_bpack (n : Nat) : onesMask n = bpack (fun _ => true) n := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [testBit_onesMask, testBit_bpack, Bool.and_true]

noncomputable def backVecPair (w k : Nat) : Nat × Nat :=
  Nat.rec (motive := fun _ => Nat × Nat) (0, w)
    (fun _ p => (p.2, (p.1 >>> 1) ^^^ (p.2 ||| p.1))) k

theorem backVecPair_spec (x : Column) (R t : Nat) :
    ∀ k, (∀ j, (k = 0 ∨ j + (k - 1) / 2 ≤ R) →
            (backVecPair (win x (R + 1) t) k).1.testBit j = backCol x k (t + j)) ∧
         (∀ j, j + k / 2 ≤ R →
            (backVecPair (win x (R + 1) t) k).2.testBit j = backCol x (k + 1) (t + j))
  | 0 => ⟨fun j _ => by
            change (0 : Nat).testBit j = false
            exact Nat.zero_testBit j,
          fun j hj => by
            change (win x (R + 1) t).testBit j = x (t + j)
            rw [win, testBit_pack]; simp [show j < R + 1 by omega]⟩
  | k + 1 => by
    obtain ⟨ih1, ih2⟩ := backVecPair_spec x R t k
    refine ⟨fun j hj => ih2 j (by omega), fun j hj => ?_⟩
    change (((backVecPair (win x (R + 1) t) k).1 >>> 1) ^^^
      ((backVecPair (win x (R + 1) t) k).2 ||| (backVecPair (win x (R + 1) t) k).1)).testBit j =
      backCol x (k + 2) (t + j)
    have hprev_shift : (backVecPair (win x (R + 1) t) k).1.testBit (1 + j) = backCol x k (t + j + 1) := by
      rcases k with _ | k'
      · change (0 : Nat).testBit (1 + j) = false; exact Nat.zero_testBit _
      · rw [ih1 (1 + j) (Or.inr (by omega)), show t + (1 + j) = t + j + 1 by omega]
    have hprev_cur : (backVecPair (win x (R + 1) t) k).1.testBit j = backCol x k (t + j) := by
      rcases k with _ | k'
      · exact ih1 j (Or.inl rfl)
      · exact ih1 j (Or.inr (by omega))
    rw [Nat.testBit_xor, Nat.testBit_shiftRight, Nat.testBit_or,
        hprev_shift, ih2 j (by omega), hprev_cur]
    rfl

theorem win_split_top (x : Column) (R t : Nat) :
    win x (R + 1) t = win x R t ∨ win x (R + 1) t = win x R t + 2 ^ R := by
  let w := win x (R + 1) t
  have hmod : w % 2 ^ R = win x R t := win_mod x R t
  have hlt : w < 2 ^ R * 2 := by rw [← Nat.pow_succ]; exact win_lt x (R + 1) t
  have hq_lt : w / 2 ^ R < 2 := Nat.div_lt_of_lt_mul hlt
  have hdm : 2 ^ R * (w / 2 ^ R) + w % 2 ^ R = w := Nat.div_add_mod w (2 ^ R)
  rcases hq : w / 2 ^ R with _ | _ | q'
  · left; rw [hq, Nat.mul_zero, Nat.zero_add] at hdm; exact hdm.symm.trans hmod
  · right; rw [hq, Nat.mul_one, hmod] at hdm; omega
  · rw [hq] at hq_lt; omega

noncomputable def stepLive1 (R okMask live : Nat) : Nat :=
  bpack (fun u =>
    live.testBit u &&
    ((okMask.testBit u && live.testBit (u / 2)) ||
     (okMask.testBit (u + 2 ^ R) && live.testBit ((u + 2 ^ R) / 2))) &&
    ((okMask.testBit (2 * u) && live.testBit ((2 * u) % 2 ^ R)) ||
     (okMask.testBit (2 * u + 1) && live.testBit ((2 * u + 1) % 2 ^ R)))) (2 ^ R)

noncomputable def prune1 (R okMask n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (onesMask (2 ^ R))
    (fun _ acc => stepLive1 R okMask acc) n

theorem win_period (x : Column) {L : Nat} (hx : PeriodFrom x 0 L) (M t : Nat) :
    win x M (t + L) = win x M t := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [win, win, testBit_pack, testBit_pack]
  by_cases hi : i < M
  · simp [hi, show t + L + i = t + i + L by omega, hx (t + i) (Nat.zero_le _)]
  · simp [hi]

theorem prune1_sound {x : Column} {R okMask L : Nat} (hL : 0 < L) (hx : PeriodFrom x 0 L)
    (hok : ∀ t, okMask.testBit (win x (R + 1) t) = true) :
    ∀ n t, (prune1 R okMask n).testBit (win x R t) = true
  | 0, t => by
    change (onesMask (2 ^ R)).testBit (win x R t) = true
    rw [testBit_onesMask]; simp [win_lt]
  | n + 1, t => by
    have ih := prune1_sound hL hx hok n
    change (stepLive1 R okMask (prune1 R okMask n)).testBit (win x R t) = true
    dsimp only [stepLive1]
    rw [testBit_bpack]
    simp only [win_lt x R t, decide_true, Bool.true_and, Bool.and_eq_true, Bool.or_eq_true]
    refine ⟨⟨ih t, ?_⟩, ?_⟩
    · have hdiv : win x (R + 1) t / 2 = win x R (t + 1) := win_div x R t
      rcases win_split_top x R t with hw | hw
      · left; rw [← hw, hdiv]; exact ⟨hok t, ih (t + 1)⟩
      · right; rw [← hw, hdiv]; exact ⟨hok t, ih (t + 1)⟩
    · let t' := t + L - 1
      let w' := win x (R + 1) t'
      have hdiv' : w' / 2 = win x R t := by
        calc w' / 2 = win x R (t' + 1) := win_div x R t'
        _ = win x R (t + L) := by rw [show t' + 1 = t + L by omega]
        _ = win x R t := win_period x hx R t
      have hmod' : w' % 2 ^ R = win x R t' := win_mod x R t'
      have hdm' := Nat.div_add_mod w' 2
      rcases (show w' = 2 * win x R t ∨ w' = 2 * win x R t + 1 by omega) with hw' | hw'
      · left; rw [← hw', hmod']; exact ⟨hok t', ih t'⟩
      · right; rw [← hw', hmod']; exact ⟨hok t', ih t'⟩

noncomputable def natAll (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i acc => acc && f i) n

theorem natAll_eq_true {n : Nat} {f : Nat → Bool} :
    natAll n f = true ↔ ∀ i, i < n → f i = true := by
  induction n with
  | zero => change true = true ↔ ∀ i, i < 0 → f i = true; simp
  | succ n ih =>
    change (natAll n f && f n) = true ↔ ∀ i, i < n + 1 → f i = true
    rw [Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      by_cases hlt : i < n
      · exact h1 i hlt
      · have : i = n := by omega
        subst this; exact h2
    · intro h; exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

noncomputable def natAny (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun i acc => acc || f i) n

theorem natAny_eq_true {n : Nat} {f : Nat → Bool} :
    natAny n f = true ↔ ∃ i, i < n ∧ f i = true := by
  induction n with
  | zero => simp [natAny]
  | succ n ih =>
    change (natAny n f || f n) = true ↔ ∃ i, i < n + 1 ∧ f i = true
    rw [Bool.or_eq_true, ih]
    constructor
    · rintro (⟨i, hi, hfi⟩ | hfn)
      · exact ⟨i, by omega, hfi⟩
      · exact ⟨n, by omega, hfn⟩
    · rintro ⟨i, hi, hfi⟩
      by_cases hlt : i < n
      · exact Or.inl ⟨i, hlt, hfi⟩
      · have : i = n := by omega
        subst this; exact Or.inr hfi

/-- Pure `Nat.rec` + `List.cons` filter (zero `List.append` `_sunfold`!). -/
noncomputable def filterMask (f : Nat → Bool) (n : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) []
    (fun i acc => Bool.rec (motive := fun _ => List Nat) acc (i :: acc) (f i)) n

theorem mem_filterMask {f : Nat → Bool} {n u : Nat} :
    u ∈ filterMask f n ↔ u < n ∧ f u = true := by
  induction n with
  | zero => change u ∈ [] ↔ u < 0 ∧ f u = true; simp
  | succ n ih =>
    change u ∈ Bool.rec (motive := fun _ => List Nat) (filterMask f n) (n :: filterMask f n) (f n) ↔
      u < n + 1 ∧ f u = true
    cases hfn : f n
    · dsimp only
      rw [ih]
      constructor
      · rintro ⟨hlt, hfu⟩; exact ⟨by omega, hfu⟩
      · rintro ⟨hlt, hfu⟩
        by_cases hun : u = n
        · subst hun; rw [hfn] at hfu; nomatch hfu
        · exact ⟨by omega, hfu⟩
    · dsimp only
      rw [List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨hlt, hfu⟩)
        · exact ⟨by omega, hfn⟩
        · exact ⟨by omega, hfu⟩
      · rintro ⟨hlt, hfu⟩
        by_cases hun : u = n
        · exact Or.inl hun
        · exact Or.inr ⟨by omega, hfu⟩

noncomputable def listLen (xs : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => ih + 1) xs

theorem listLen_eq_length : ∀ (xs : List Nat), listLen xs = xs.length
  | [] => rfl
  | _ :: t => by change listLen t + 1 = t.length + 1; rw [listLen_eq_length t]

noncomputable def listGetD (xs : List Nat) (idx : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun h _ ih k => Nat.rec (motive := fun _ => Nat) h (fun k' _ => ih k') k) xs idx

theorem listGetD_eq_getD : ∀ (xs : List Nat) (idx : Nat), listGetD xs idx = xs.getD idx 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: t, k + 1 => listGetD_eq_getD t k

noncomputable def idxOfNat (u : Nat) (xs : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun h _ ih => Bool.rec (motive := fun _ => Nat) (ih + 1) 0 (Nat.beq h u)) xs

theorem idxOfNat_mem {u : Nat} : ∀ {xs : List Nat},
    u ∈ xs → idxOfNat u xs < xs.length ∧ xs.getD (idxOfNat u xs) 0 = u
  | [], h => nomatch h
  | x :: xs, h => by
    change (Bool.rec (motive := fun _ => Nat) (idxOfNat u xs + 1) 0 (Nat.beq x u)) < (x :: xs).length ∧
      (x :: xs).getD (Bool.rec (motive := fun _ => Nat) (idxOfNat u xs + 1) 0 (Nat.beq x u)) 0 = u
    cases hbeq : Nat.beq x u
    · dsimp only
      rcases List.mem_cons.mp h with rfl | hmem
      · rw [Nat.beq_refl] at hbeq; exact absurd hbeq (by decide)
      · obtain ⟨hlt, hget⟩ := idxOfNat_mem hmem
        exact ⟨by simp; omega, by simpa [List.getD] using hget⟩
    · dsimp only
      rw [Nat.beq_eq] at hbeq
      exact ⟨by simp, by simp [List.getD, hbeq]⟩

theorem div_mod_pair (i1 : Nat) {i2 s : Nat} (hi2 : i2 < s) :
    (i1 * s + i2) / s = i1 ∧ (i1 * s + i2) % s = i2 := by
  refine ⟨?_, ?_⟩
  · rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_left _ _ (by omega),
        Nat.div_eq_of_lt hi2, Nat.zero_add]
  · rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi2]

theorem mul_add_lt_sq {i j m : Nat} (hi : i < m) (hj : j < m) : i * m + j < m * m := by
  calc i * m + j < i * m + m := by omega
  _ = (i + 1) * m := by rw [Nat.add_mul, Nat.one_mul]
  _ ≤ m * m := Nat.mul_le_mul_right m (by omega)

/-- Build an `O(1)` lookup table packing `idxOfNat u S1 % 65536` into 16-bit slot `u` for `live1` vertices. -/
noncomputable def buildPosMap (live1 : Nat) (S1 : List Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun u acc => Bool.rec (motive := fun _ => Nat) acc
      (acc ||| ((idxOfNat u S1 % 65536) <<< (16 * u))) (live1.testBit u)) n

theorem buildPosMap_testBit (live1 : Nat) (S1 : List Nat) : ∀ (n i : Nat),
    (buildPosMap live1 S1 n).testBit i =
      (decide (i / 16 < n) && live1.testBit (i / 16) && ((idxOfNat (i / 16) S1) % 65536).testBit (i % 16))
  | 0, i => by
    change (0 : Nat).testBit i = _
    simp [Nat.zero_testBit]
  | n + 1, i => by
    change (Bool.rec (motive := fun _ => Nat) (buildPosMap live1 S1 n)
      ((buildPosMap live1 S1 n) ||| ((idxOfNat n S1 % 65536) <<< (16 * n))) (live1.testBit n)).testBit i = _
    cases hlv : live1.testBit n
    · dsimp only
      rw [buildPosMap_testBit live1 S1 n i]
      by_cases hlt : i / 16 < n
      · simp [hlt, show i / 16 < n + 1 by omega]
      · by_cases heq : i / 16 = n
        · simp [heq, hlv]
        · simp [hlt, show ¬ (i / 16 < n + 1) by omega]
    · dsimp only
      rw [Nat.testBit_or, buildPosMap_testBit live1 S1 n i, Nat.testBit_shiftLeft]
      by_cases hlt : i / 16 < n
      · have hle_f : ¬ (16 * n ≤ i) := by have := Nat.div_add_mod i 16; omega
        simp [hlt, show i / 16 < n + 1 by omega, hle_f]
      · by_cases heq : i / 16 = n
        · have hle_t : 16 * n ≤ i := by have := Nat.div_add_mod i 16; omega
          have hsub : i - 16 * n = i % 16 := by have := Nat.div_add_mod i 16; omega
          simp [heq, hlv, hle_t, hsub]
        · have hge : 16 ≤ i - 16 * n := by have := Nat.div_add_mod i 16; omega
          have hhigh : ((idxOfNat n S1 % 65536).testBit (i - 16 * n)) = false := by
            rw [show (65536 : Nat) = 2 ^ 16 by decide, Nat.testBit_mod_two_pow]
            simp [show ¬ (i - 16 * n < 16) by omega]
          rw [hhigh, Bool.and_false, Bool.or_false]
          simp [show ¬ (i / 16 < n + 1) by omega, hlt]

noncomputable def posLookup (posMap u : Nat) : Nat :=
  (posMap >>> (16 * u)) % 65536

theorem posLookup_eq (live1 : Nat) (S1 : List Nat) {n u : Nat}
    (hu : u < n) (hlv : live1.testBit u = true) (hsmall : idxOfNat u S1 < 65536) :
    posLookup (buildPosMap live1 S1 n) u = idxOfNat u S1 := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [posLookup, show (65536 : Nat) = 2 ^ 16 by decide, Nat.testBit_mod_two_pow]
  by_cases hj : j < 16
  · rw [decide_eq_true hj, Bool.true_and, Nat.testBit_shiftRight, buildPosMap_testBit]
    have hdm := div_mod_pair u hj
    rw [show 16 * u + j = u * 16 + j by rw [Nat.mul_comm], hdm.1, hdm.2,
        decide_eq_true hu, hlv, Bool.true_and, Bool.true_and,
        show (65536 : Nat) = 2 ^ 16 by decide, Nat.testBit_mod_two_pow,
        decide_eq_true hj, Bool.true_and]
  · rw [decide_eq_false hj, Bool.false_and]
    have hlt_pow : idxOfNat u S1 < 2 ^ 16 := by simpa using hsmall
    cases hbit : (idxOfNat u S1).testBit j
    · rfl
    · exfalso
      have hge := Nat.ge_two_pow_of_testBit hbit
      have : 2 ^ 16 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
      omega

noncomputable def checkPairBranchFast (okMask emitMask live1 s posMap live2 u1 u2 d1 d2 : Nat) : Bool :=
  let w1 := u1 + d1
  let w2 := u2 + d2
  okMask.testBit w1 && okMask.testBit w2 &&
    xor (emitMask.testBit w1) (emitMask.testBit w2) &&
    live1.testBit (w1 / 2) && live1.testBit (w2 / 2) &&
    live2.testBit (posLookup posMap (w1 / 2) * s + posLookup posMap (w2 / 2))

noncomputable def hasPairNextFast (R okMask emitMask live1 s posMap : Nat) (S1 : List Nat) (live2 idx : Nat) : Bool :=
  let u1 := listGetD S1 (idx / s)
  let u2 := listGetD S1 (idx % s)
  let p := 2 ^ R
  checkPairBranchFast okMask emitMask live1 s posMap live2 u1 u2 0 0 ||
  checkPairBranchFast okMask emitMask live1 s posMap live2 u1 u2 0 p ||
  checkPairBranchFast okMask emitMask live1 s posMap live2 u1 u2 p 0 ||
  checkPairBranchFast okMask emitMask live1 s posMap live2 u1 u2 p p

noncomputable def stepLive2 (R okMask emitMask live1 s posMap : Nat) (S1 : List Nat) (live2 : Nat) : Nat :=
  bpack (fun idx => live2.testBit idx && hasPairNextFast R okMask emitMask live1 s posMap S1 live2 idx)
    (s * s)

noncomputable def prune2 (R okMask emitMask live1 s posMap : Nat) (S1 : List Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (onesMask (s * s))
    (fun _ acc => Bool.rec (motive := fun _ => Nat)
      (stepLive2 R okMask emitMask live1 s posMap S1 acc) 0 (Nat.beq acc 0)) n

noncomputable def hasMatEdge (R okMask emitMask s : Nat) (S1 P2 : List Nat) (i j : Nat) : Bool :=
  let idx := listGetD P2 i
  let jdx := listGetD P2 j
  let u1 := listGetD S1 (idx / s)
  let u2 := listGetD S1 (idx % s)
  let v1 := listGetD S1 (jdx / s)
  let v2 := listGetD S1 (jdx % s)
  let p := 2 ^ R
  let chk := fun d1 d2 =>
    let w1 := u1 + d1
    let w2 := u2 + d2
    okMask.testBit w1 && okMask.testBit w2 &&
      xor (emitMask.testBit w1) (emitMask.testBit w2) &&
      Nat.beq (w1 / 2) v1 && Nat.beq (w2 / 2) v2
  chk 0 0 || chk 0 p || chk p 0 || chk p p

noncomputable def mkMatNat (m : Nat) (entry : Nat → Nat → Bool) : Nat :=
  bpack (fun idx => entry (idx / m) (idx % m)) (m * m)

theorem mkMatNat_testBit {m : Nat} (entry : Nat → Nat → Bool) {i j : Nat}
    (hi : i < m) (hj : j < m) :
    (mkMatNat m entry).testBit (i * m + j) = entry i j := by
  have hlt := mul_add_lt_sq hi hj
  have hdm := div_mod_pair i hj
  rw [mkMatNat, testBit_bpack, decide_eq_true hlt, Bool.true_and, hdm.1, hdm.2]

noncomputable def matMulNat (m A B : Nat) : Nat :=
  mkMatNat m (fun i k =>
    natAny m (fun j => A.testBit (i * m + j) && B.testBit (j * m + k)))

noncomputable def matPow2Nat (m M n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) M (fun _ acc => matMulNat m acc acc) n

/-! ### Strict single-`Nat` bit-sliced backward plane evaluation (`O(K)` GMP ops, zero lazy `Prod`/`List` DAG) -/

noncomputable def stepPlanesNat (nw B allB st : Nat) : Nat :=
  let prev := st % (1 <<< B)
  let cur := st >>> B
  let nxt := ((prev >>> nw) ^^^ (cur ||| prev)) &&& allB
  cur ||| (nxt <<< B)

noncomputable def runPlanesNat (R k : Nat) : Nat :=
  let nw := 2 ^ (R + 1)
  let B := (R + 1) * nw
  let allB := onesMask B
  let init1 := bpack (fun idx => (idx % nw).testBit (idx / nw)) B
  Nat.rec (motive := fun _ => Nat) (init1 <<< B)
    (fun _ st => stepPlanesNat nw B allB st) k

theorem backVecPair_high_false {w n : Nat} (hw : w < 2 ^ n) :
    ∀ k j, n ≤ j → (backVecPair w k).1.testBit j = false ∧ (backVecPair w k).2.testBit j = false
  | 0, j, hj => by
    refine ⟨Nat.zero_testBit j, ?_⟩
    change w.testBit j = false
    cases hb : w.testBit j
    · rfl
    · exfalso
      have := Nat.ge_two_pow_of_testBit hb
      have : 2 ^ n ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) hj
      omega
  | k + 1, j, hj => by
    have ihj := backVecPair_high_false hw k j hj
    have ihj1 := backVecPair_high_false hw k (1 + j) (by omega)
    refine ⟨ihj.2, ?_⟩
    change (((backVecPair w k).1 >>> 1) ^^^ ((backVecPair w k).2 ||| (backVecPair w k).1)).testBit j = false
    rw [Nat.testBit_xor, Nat.testBit_shiftRight, Nat.testBit_or, ihj1.1, ihj.2, ihj.1]; rfl

theorem shiftLeft_one_eq_pow (B : Nat) : (1 <<< B) = 2 ^ B := by
  rw [Nat.one_shiftLeft]

theorem runPlanesNat_spec (R : Nat) :
    let nw := 2 ^ (R + 1)
    let B := (R + 1) * nw
    ∀ k, (∀ i, B ≤ i → ((runPlanesNat R k) >>> B).testBit i = false) ∧
      ∀ w j, w < nw → j < R + 1 →
        ((runPlanesNat R k) % (1 <<< B)).testBit (j * nw + w) = (backVecPair w k).1.testBit j ∧
        ((runPlanesNat R k) >>> B).testBit (j * nw + w) = (backVecPair w k).2.testBit j := by
  intro nw B k
  induction k with
  | zero =>
    refine ⟨fun i hi => ?_, fun w j hw hj => ⟨?_, ?_⟩⟩
    · change (((bpack (fun idx => (idx % nw).testBit (idx / nw)) B) <<< B) >>> B).testBit i = false
      rw [Nat.testBit_shiftRight, Nat.testBit_shiftLeft,
          decide_eq_true (Nat.le_add_right B i), Bool.true_and,
          Nat.add_sub_cancel_left, testBit_bpack,
          decide_eq_false (by omega), Bool.false_and]
    · change (((bpack (fun idx => (idx % nw).testBit (idx / nw)) B) <<< B) % (1 <<< B)).testBit (j * nw + w) =
        (0 : Nat).testBit j
      rw [shiftLeft_one_eq_pow, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft, Nat.zero_testBit]
      have hltB : j * nw + w < B := by
        calc j * nw + w < j * nw + nw := by omega
        _ = (j + 1) * nw := by rw [Nat.add_mul, Nat.one_mul]
        _ ≤ (R + 1) * nw := Nat.mul_le_mul_right nw (by omega)
      simp [hltB, show ¬ (B ≤ j * nw + w) by omega]
    · change (((bpack (fun idx => (idx % nw).testBit (idx / nw)) B) <<< B) >>> B).testBit (j * nw + w) =
        w.testBit j
      have hltB : j * nw + w < B := by
        calc j * nw + w < j * nw + nw := by omega
        _ = (j + 1) * nw := by rw [Nat.add_mul, Nat.one_mul]
        _ ≤ (R + 1) * nw := Nat.mul_le_mul_right nw (by omega)
      have hdm := div_mod_pair j hw
      rw [Nat.testBit_shiftRight, Nat.testBit_shiftLeft,
          decide_eq_true (Nat.le_add_right B _), Bool.true_and,
          Nat.add_sub_cancel_left, testBit_bpack, decide_eq_true hltB, Bool.true_and,
          hdm.2, hdm.1]
  | succ k ih =>
    obtain ⟨ih_hi, ih_lo⟩ := ih
    let st := runPlanesNat R k
    let allB := onesMask B
    let prev := st % (1 <<< B)
    let cur := st >>> B
    let nxt := ((prev >>> nw) ^^^ (cur ||| prev)) &&& allB
    have hnxt_hi : ∀ i, B ≤ i → nxt.testBit i = false := fun i hi => by
      dsimp only [nxt, allB]
      rw [Nat.testBit_and, testBit_onesMask, decide_eq_false (by omega), Bool.and_false]
    have hcur_hi : ∀ i, B ≤ i → cur.testBit i = false := ih_hi
    refine ⟨fun i hi => ?_, fun w j hw hj => ?_⟩
    · change ((cur ||| (nxt <<< B)) >>> B).testBit i = false
      rw [Nat.testBit_shiftRight, Nat.testBit_or, hcur_hi (B + i) (by omega), Bool.false_or,
          Nat.testBit_shiftLeft, decide_eq_true (Nat.le_add_right B i), Bool.true_and,
          Nat.add_sub_cancel_left, hnxt_hi i hi]
    · have hltB : j * nw + w < B := by
        calc j * nw + w < j * nw + nw := by omega
        _ = (j + 1) * nw := by rw [Nat.add_mul, Nat.one_mul]
        _ ≤ (R + 1) * nw := Nat.mul_le_mul_right nw (by omega)
      refine ⟨?_, ?_⟩
      · change ((cur ||| (nxt <<< B)) % (1 <<< B)).testBit (j * nw + w) = (backVecPair w k).2.testBit j
        rw [shiftLeft_one_eq_pow, Nat.testBit_mod_two_pow, decide_eq_true hltB, Bool.true_and,
            Nat.testBit_or, Nat.testBit_shiftLeft,
            decide_eq_false (show ¬ (B ≤ j * nw + w) by omega), Bool.false_and, Bool.or_false]
        exact (ih_lo w j hw hj).2
      · change ((cur ||| (nxt <<< B)) >>> B).testBit (j * nw + w) =
          (((backVecPair w k).1 >>> 1) ^^^ ((backVecPair w k).2 ||| (backVecPair w k).1)).testBit j
        rw [Nat.testBit_shiftRight, Nat.testBit_or,
            hcur_hi (B + (j * nw + w)) (by omega), Bool.false_or,
            Nat.testBit_shiftLeft, decide_eq_true (Nat.le_add_right B _), Bool.true_and,
            Nat.add_sub_cancel_left]
        dsimp only [nxt, allB]
        rw [Nat.testBit_and, testBit_onesMask, decide_eq_true hltB, Bool.and_true,
            Nat.testBit_xor, Nat.testBit_shiftRight, Nat.testBit_or]
        have hcur_eq : cur.testBit (j * nw + w) = (backVecPair w k).2.testBit j := (ih_lo w j hw hj).2
        have hprev_eq : prev.testBit (j * nw + w) = (backVecPair w k).1.testBit j := (ih_lo w j hw hj).1
        rw [hcur_eq, hprev_eq, Nat.testBit_xor, Nat.testBit_shiftRight, Nat.testBit_or]
        have hidx : nw + (j * nw + w) = (1 + j) * nw + w := by
          rw [Nat.add_mul, Nat.one_mul, Nat.add_assoc]
        rw [hidx]
        by_cases hj1 : 1 + j < R + 1
        · rw [(ih_lo w (1 + j) hw hj1).1]
        · have hgeB : B ≤ (1 + j) * nw + w := by
            have : R + 1 ≤ 1 + j := by omega
            have hm := Nat.mul_le_mul_right nw this
            dsimp only [B]; omega
          have hp_hi : prev.testBit ((1 + j) * nw + w) = false := by
            dsimp only [prev]
            rw [shiftLeft_one_eq_pow, Nat.testBit_mod_two_pow,
                decide_eq_false (by omega), Bool.false_and]
          rw [hp_hi, (backVecPair_high_false hw k (1 + j) (by omega)).1]

noncomputable def pairedGapExclude (K r1 r2 p0 e0 : Nat) : Bool :=
  decide (3 ≤ K) && decide (K ≤ 26) && decide (e0 ≤ p0) &&
  let R := (K - 1) / 2
  let nw := 2 ^ (R + 1)
  let B := (R + 1) * nw
  let st := runPlanesNat R (K - 1)
  let allW := onesMask nw
  let okMask := allW ^^^ ((st >>> B) % (1 <<< nw))
  let emitMask := st % (1 <<< nw)
  let live1 := prune1 R okMask r1
  let S1 := filterMask live1.testBit (2 ^ R)
  let s := listLen S1
  let posMap := buildPosMap live1 S1 (2 ^ R)
  let live2 := prune2 R okMask emitMask live1 s posMap S1 r2
  let P2 := filterMask live2.testBit (s * s)
  let m := listLen P2
  let M := mkMatNat m (hasMatEdge R okMask emitMask s S1 P2)
  Nat.beq (matPow2Nat m M p0) (matPow2Nat m M (p0 + 1)) &&
    natAll (p0 + 1) (fun e =>
      decide (e < e0) ||
        natAll m (fun i =>
          let idx := listGetD P2 i
          let swapped := (idx % s) * s + (idx / s)
          natAll m (fun j =>
            !(Nat.beq (listGetD P2 j) swapped) ||
              !((matPow2Nat m M e).testBit (i * m + j)))))

theorem matPow2Nat_periodic (m M p0 : Nat)
    (heq : matPow2Nat m M p0 = matPow2Nat m M (p0 + 1)) :
    ∀ {e e0 : Nat}, e0 ≤ p0 → e0 ≤ e →
      ∃ e', e' < p0 + 1 ∧ e0 ≤ e' ∧ matPow2Nat m M e = matPow2Nat m M e' := by
  have hstep : ∀ k, matPow2Nat m M (p0 + k + 1) = matPow2Nat m M (p0 + k) := by
    intro k; induction k with
    | zero => exact heq.symm
    | succ k ih =>
      change matMulNat m (matPow2Nat m M (p0 + k + 1)) (matPow2Nat m M (p0 + k + 1)) =
        matMulNat m (matPow2Nat m M (p0 + k)) (matPow2Nat m M (p0 + k))
      rw [ih]
  intro e
  induction e using Nat.strongRecOn with
  | ind e ih =>
    intro e0 he0p he0e
    by_cases hlt : e < p0 + 1
    · exact ⟨e, hlt, he0e, rfl⟩
    · obtain ⟨e', he'lt, he0e', heq'⟩ := ih (e - 1) (by omega) he0p (by omega)
      refine ⟨e', he'lt, he0e', ?_⟩
      have h1 := hstep (e - (p0 + 1))
      rw [show p0 + (e - (p0 + 1)) + 1 = e by omega, show p0 + (e - (p0 + 1)) = e - 1 by omega] at h1
      exact h1.trans heq'

theorem filterMask_length_le (f : Nat → Bool) : ∀ n, (filterMask f n).length ≤ n
  | 0 => Nat.le_refl 0
  | n + 1 => by
    change (Bool.rec (motive := fun _ => List Nat) (filterMask f n) (n :: filterMask f n) (f n)).length ≤ n + 1
    have ih := filterMask_length_le f n
    cases f n <;> dsimp only <;> simp <;> omega

theorem pairedGapExclude_sound {d : Nat → Column} (hd : Recurrence d) (clocks : PrefixClocks d)
    {K r1 r2 p0 e0 a e b : Nat} (hex : pairedGapExclude K r1 r2 p0 e0 = true)
    (hle : e0 ≤ e) (loss : FirstLoss d a e) (hab : NextWhite d a b) : b - a ≠ K := by
  intro hgap
  unfold pairedGapExclude at hex
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hex
  obtain ⟨⟨⟨hK3_b, hK26_b⟩, he0p_b⟩, hper_b, hnoswap⟩ := hex
  have hK3 : 3 ≤ K := decide_eq_true_eq.mp hK3_b
  have hK26 : K ≤ 26 := decide_eq_true_eq.mp hK26_b
  have he0p : e0 ≤ p0 := decide_eq_true_eq.mp he0p_b
  let R := (K - 1) / 2
  have hR12 : R ≤ 12 := by omega
  let nw := 2 ^ (R + 1)
  let B := (R + 1) * nw
  let st := runPlanesNat R (K - 1)
  let allW := onesMask nw
  let okMask := allW ^^^ ((st >>> B) % (1 <<< nw))
  let emitMask := st % (1 <<< nw)
  let live1 := prune1 R okMask r1
  let S1 := filterMask live1.testBit (2 ^ R)
  let s := listLen S1
  have hs_eq : s = S1.length := listLen_eq_length S1
  let posMap := buildPosMap live1 S1 (2 ^ R)
  let live2 := prune2 R okMask emitMask live1 s posMap S1 r2
  let P2 := filterMask live2.testBit (s * s)
  let m := listLen P2
  have hm_eq : m = P2.length := listLen_eq_length P2
  let M := mkMatNat m (hasMatEdge R okMask emitMask s S1 P2)
  let x := d (b - 1)
  let P := 2 ^ e
  let L := 2 * P
  have hL : 0 < L := by have := Nat.two_pow_pos e; omega
  have hp1_L : PeriodFrom (d (a + 1)) 0 L := fun t _ => by
    dsimp only [L, P]
    rw [show t + 2 * 2 ^ e = t + 2 ^ e + 2 ^ e by omega, loss.flip, loss.flip, Bool.not_not]
  have hx_L : PeriodFrom x 0 L :=
    period_between_whites hd clocks loss.white hp1_L hab (b - 1) (by omega) (by omega)
  have hok : ∀ t, okMask.testBit (win x (R + 1) t) = true := fun t => by
    dsimp only [okMask, allW]
    have hsp := (runPlanesNat_spec R (K - 1)).2 (win x (R + 1) t) 0 (win_lt x (R + 1) t) (by omega)
    simp only [Nat.zero_mul, Nat.zero_add] at hsp
    rw [Nat.testBit_xor, testBit_onesMask, decide_eq_true (win_lt x (R + 1) t),
        shiftLeft_one_eq_pow, Nat.testBit_mod_two_pow, decide_eq_true (win_lt x (R + 1) t),
        Bool.true_and, hsp.2]
    have hvp := (backVecPair_spec x R t (K - 1)).2 0 (by omega)
    rw [show K - 1 + 1 = K by omega] at hvp
    simp only [Nat.add_zero] at hvp
    rw [hvp]; dsimp only [x]
    rw [← backCol_eq_strip hd hab.2.1 K (by omega) t, show b - K = a by omega, loss.white t]
    rfl
  have hemit : ∀ t, emitMask.testBit (win x (R + 1) t) = d (a + 1) t := fun t => by
    dsimp only [emitMask]
    have hsp := (runPlanesNat_spec R (K - 1)).2 (win x (R + 1) t) 0 (win_lt x (R + 1) t) (by omega)
    simp only [Nat.zero_mul, Nat.zero_add] at hsp
    have hmodB : st % (1 <<< nw) = (st % (1 <<< B)) % (1 <<< nw) := by
      have hdvd : (1 <<< nw) ∣ (1 <<< B) := by
        rw [shiftLeft_one_eq_pow, shiftLeft_one_eq_pow]
        exact ⟨2 ^ (B - nw), by
          rw [← Nat.pow_add, show nw + (B - nw) = B by
            have : 1 * nw ≤ (R + 1) * nw := Nat.mul_le_mul_right nw (by omega)
            dsimp only [B]; omega]⟩
      exact (Nat.mod_mod_of_dvd st hdvd).symm
    rw [hmodB, shiftLeft_one_eq_pow nw, Nat.testBit_mod_two_pow,
        decide_eq_true (win_lt x (R + 1) t), Bool.true_and, hsp.1]
    have hvp := (backVecPair_spec x R t (K - 1)).1 0 (Or.inr (by omega))
    simp only [Nat.add_zero] at hvp
    rw [hvp]; dsimp only [x]
    rw [← backCol_eq_strip hd hab.2.1 (K - 1) (by omega) t, show b - (K - 1) = a + 1 by omega]
  have hS1_mem : ∀ t, win x R t ∈ S1 := fun t =>
    mem_filterMask.mpr ⟨win_lt x R t, prune1_sound hL hx_L hok r1 t⟩
  let ix := fun t => idxOfNat (win x R t) S1
  have hix : ∀ t, ix t < s ∧ S1.getD (ix t) 0 = win x R t := fun t => by
    rw [hs_eq]; exact idxOfNat_mem (hS1_mem t)
  have hs_lt : s < 65536 := by
    have h1 : S1.length ≤ 2 ^ R := filterMask_length_le live1.testBit (2 ^ R)
    have h2 : 2 ^ R ≤ 4096 := Nat.pow_le_pow_right (by decide) hR12
    omega
  let pairIdx := fun t => ix t * s + ix (t + P)
  have hpair_lt : ∀ t, pairIdx t < s * s := fun t => mul_add_lt_sq (hix t).1 (hix (t + P)).1
  have hprune2 : ∀ n t, (prune2 R okMask emitMask live1 s posMap S1 n).testBit (pairIdx t) = true := by
    intro n; induction n with
    | zero =>
      intro t
      change (onesMask (s * s)).testBit (pairIdx t) = true
      rw [testBit_onesMask]; simp [hpair_lt t]
    | succ n ih =>
      intro t
      have hacc_ne0 : Nat.beq (prune2 R okMask emitMask live1 s posMap S1 n) 0 = false := by
        cases hbeq : Nat.beq (prune2 R okMask emitMask live1 s posMap S1 n) 0
        · rfl
        · exfalso
          have hz := Nat.beq_eq.mp hbeq
          have hbit := ih t
          rw [hz, Nat.zero_testBit] at hbit; nomatch hbit
      change (Bool.rec (motive := fun _ => Nat)
        (stepLive2 R okMask emitMask live1 s posMap S1 (prune2 R okMask emitMask live1 s posMap S1 n)) 0
        (Nat.beq (prune2 R okMask emitMask live1 s posMap S1 n) 0)).testBit (pairIdx t) = true
      rw [hacc_ne0]; dsimp only [stepLive2]
      rw [testBit_bpack, decide_eq_true (hpair_lt t), Bool.true_and, Bool.and_eq_true]
      refine ⟨ih t, ?_⟩
      dsimp only [hasPairNextFast]
      have hdm : pairIdx t / s = ix t ∧ pairIdx t % s = ix (t + P) :=
        div_mod_pair (ix t) (hix (t + P)).1
      rw [listGetD_eq_getD, listGetD_eq_getD, hdm.1, hdm.2, (hix t).2, (hix (t + P)).2]
      let w1 := win x (R + 1) t
      let w2 := win x (R + 1) (t + P)
      have hw1 : w1 = win x R t + 0 ∨ w1 = win x R t + 2 ^ R := by simpa using win_split_top x R t
      have hw2 : w2 = win x R (t + P) + 0 ∨ w2 = win x R (t + P) + 2 ^ R := by simpa using win_split_top x R (t + P)
      have hflip : xor (emitMask.testBit w1) (emitMask.testBit w2) = true := by
        rw [hemit t, hemit (t + P), loss.flip t]; cases d (a + 1) t <;> rfl
      have hlv1 : live1.testBit (w1 / 2) = true := by
        rw [win_div x R t]; exact prune1_sound hL hx_L hok r1 (t + 1)
      have hlv2 : live1.testBit (w2 / 2) = true := by
        rw [win_div x R (t + P)]; exact prune1_sound hL hx_L hok r1 (t + P + 1)
      have hpos1 : posLookup posMap (w1 / 2) = ix (t + 1) := by
        rw [win_div x R t]
        exact posLookup_eq live1 S1 (win_lt x R (t + 1)) (prune1_sound hL hx_L hok r1 (t + 1))
          (by change ix (t + 1) < 65536; have := (hix (t + 1)).1; omega)
      have hpos2 : posLookup posMap (w2 / 2) = ix (t + 1 + P) := by
        rw [win_div x R (t + P), show t + P + 1 = t + 1 + P by omega]
        exact posLookup_eq live1 S1 (win_lt x R (t + 1 + P)) (prune1_sound hL hx_L hok r1 (t + 1 + P))
          (by change ix (t + 1 + P) < 65536; have := (hix (t + 1 + P)).1; omega)
      have hnext : (prune2 R okMask emitMask live1 s posMap S1 n).testBit
          (posLookup posMap (w1 / 2) * s + posLookup posMap (w2 / 2)) = true := by
        rw [hpos1, hpos2]; exact ih (t + 1)
      have hbr : ∀ d1 d2, w1 = win x R t + d1 → w2 = win x R (t + P) + d2 →
          checkPairBranchFast okMask emitMask live1 s posMap (prune2 R okMask emitMask live1 s posMap S1 n)
            (win x R t) (win x R (t + P)) d1 d2 = true := by
        intro d1 d2 hd1 hd2
        dsimp only [checkPairBranchFast]
        rw [← hd1, ← hd2, hok t, hok (t + P), hflip, hlv1, hlv2, hnext]; rfl
      rcases hw1 with hw1 | hw1 <;> rcases hw2 with hw2 | hw2
      · rw [hbr 0 0 hw1 hw2]; simp
      · rw [hbr 0 (2 ^ R) hw1 hw2]; simp
      · rw [hbr (2 ^ R) 0 hw1 hw2]; simp
      · rw [hbr (2 ^ R) (2 ^ R) hw1 hw2]; simp
  have hP2_mem : ∀ t, pairIdx t ∈ P2 := fun t => mem_filterMask.mpr ⟨hpair_lt t, hprune2 r2 t⟩
  let nodeAt := fun t => idxOfNat (pairIdx t) P2
  have hnode : ∀ t, nodeAt t < m ∧ P2.getD (nodeAt t) 0 = pairIdx t := fun t => by
    rw [hm_eq]; exact idxOfNat_mem (hP2_mem t)
  have hedge : ∀ t, M.testBit (nodeAt t * m + nodeAt (t + 1)) = true := fun t => by
    rw [mkMatNat_testBit _ (hnode t).1 (hnode (t + 1)).1]
    dsimp only [hasMatEdge]
    simp only [listGetD_eq_getD]
    rw [(hnode t).2, (hnode (t + 1)).2]
    have hdm1 := div_mod_pair (ix t) (hix (t + P)).1
    have hdm2 := div_mod_pair (ix (t + 1)) (hix (t + 1 + P)).1
    rw [hdm1.1, hdm1.2, hdm2.1, hdm2.2, (hix t).2, (hix (t + P)).2, (hix (t + 1)).2, (hix (t + 1 + P)).2]
    let w1 := win x (R + 1) t
    let w2 := win x (R + 1) (t + P)
    have hw1 : w1 = win x R t + 0 ∨ w1 = win x R t + 2 ^ R := by simpa using win_split_top x R t
    have hw2 : w2 = win x R (t + P) + 0 ∨ w2 = win x R (t + P) + 2 ^ R := by simpa using win_split_top x R (t + P)
    have hflip : xor (emitMask.testBit w1) (emitMask.testBit w2) = true := by
      rw [hemit t, hemit (t + P), loss.flip t]; cases d (a + 1) t <;> rfl
    have hv1 : Nat.beq (w1 / 2) (win x R (t + 1)) = true := by
      rw [win_div x R t, Nat.beq_refl]
    have hv2 : Nat.beq (w2 / 2) (win x R (t + 1 + P)) = true := by
      rw [win_div x R (t + P), show t + P + 1 = t + 1 + P by omega, Nat.beq_refl]
    rcases hw1 with hw1 | hw1 <;> rcases hw2 with hw2 | hw2
    · rw [← hw1, ← hw2, hok t, hok (t + P), hflip, hv1, hv2]; simp
    · rw [← hw1, ← hw2, hok t, hok (t + P), hflip, hv1, hv2]; simp
    · rw [← hw1, ← hw2, hok t, hok (t + P), hflip, hv1, hv2]; simp
    · rw [← hw1, ← hw2, hok t, hok (t + P), hflip, hv1, hv2]; simp
  have hpow_reach : ∀ n t, (matPow2Nat m M n).testBit (nodeAt t * m + nodeAt (t + 2 ^ n)) = true := by
    intro n; induction n with
    | zero => intro t; exact hedge t
    | succ n ih =>
      intro t
      change (matMulNat m (matPow2Nat m M n) (matPow2Nat m M n)).testBit
        (nodeAt t * m + nodeAt (t + 2 ^ (n + 1))) = true
      dsimp only [matMulNat]
      rw [mkMatNat_testBit _ (hnode t).1 (hnode (t + 2 ^ (n + 1))).1, natAny_eq_true]
      refine ⟨nodeAt (t + 2 ^ n), (hnode (t + 2 ^ n)).1, ?_⟩
      rw [Bool.and_eq_true]
      refine ⟨ih t, ?_⟩
      simpa [Nat.pow_succ, Nat.mul_two, Nat.add_assoc] using ih (t + 2 ^ n)
  obtain ⟨e', he'lt, he0e', hmat_eq⟩ :=
    matPow2Nat_periodic m M p0 (Nat.beq_eq.mp hper_b) he0p hle
  have hhit0 : (matPow2Nat m M e').testBit (nodeAt 0 * m + nodeAt P) = true := by
    rw [← hmat_eq]; simpa [P] using hpow_reach e 0
  have hswap_eq : listGetD P2 (nodeAt P) = (listGetD P2 (nodeAt 0) % s) * s + (listGetD P2 (nodeAt 0) / s) := by
    rw [listGetD_eq_getD, listGetD_eq_getD, (hnode P).2, (hnode 0).2]
    have hdm0 := div_mod_pair (ix 0) (hix (0 + P)).1
    rw [hdm0.1, hdm0.2, Nat.zero_add]
    have hix2P : ix (P + P) = ix 0 := by
      dsimp only [ix]
      rw [show P + P = 0 + L by dsimp [L]; omega, win_period x hx_L R 0]
    dsimp only [pairIdx]; rw [hix2P]
  have he'_all := natAll_eq_true.mp hnoswap e' he'lt
  simp only [show ¬ (e' < e0) by omega, decide_false, Bool.false_or] at he'_all
  have hi_all := natAll_eq_true.mp he'_all (nodeAt 0) (hnode 0).1
  have hj_all := natAll_eq_true.mp hi_all (nodeAt P) (hnode P).1
  rw [hswap_eq, Nat.beq_refl, hhit0] at hj_all
  exact absurd hj_all (by decide)

private theorem gap_excl_4 : pairedGapExclude 4 1 3 0 0 = true := by decide +kernel
private theorem gap_excl_6 : pairedGapExclude 6 1 1 1 1 = true := by decide +kernel
private theorem gap_excl_7 : pairedGapExclude 7 1 4 1 1 = true := by decide +kernel
private theorem gap_excl_8 : pairedGapExclude 8 1 5 1 1 = true := by decide +kernel
private theorem gap_excl_9 : pairedGapExclude 9 5 1 1 1 = true := by decide +kernel
private theorem gap_excl_10 : pairedGapExclude 10 4 1 1 1 = true := by decide +kernel
private theorem gap_excl_11 : pairedGapExclude 11 4 5 1 1 = true := by decide +kernel
private theorem gap_excl_12 : pairedGapExclude 12 2 6 1 1 = true := by decide +kernel
private theorem gap_excl_13 : pairedGapExclude 13 13 7 1 1 = true := by decide +kernel
private theorem gap_excl_14 : pairedGapExclude 14 3 8 1 1 = true := by decide +kernel
private theorem gap_excl_15 : pairedGapExclude 15 7 8 1 1 = true := by decide +kernel
private theorem gap_excl_16 : pairedGapExclude 16 6 12 1 1 = true := by decide +kernel
private theorem gap_excl_17 : pairedGapExclude 17 14 8 1 1 = true := by decide +kernel
private theorem gap_excl_18 : pairedGapExclude 18 8 1 1 1 = true := by decide +kernel
private theorem gap_excl_19 : pairedGapExclude 19 34 5 1 1 = true := by decide +kernel
private theorem gap_excl_20 : pairedGapExclude 20 7 4 1 1 = true := by decide +kernel
private theorem gap_excl_21 : pairedGapExclude 21 24 9 2 2 = true := by decide +kernel
private theorem gap_excl_22 : pairedGapExclude 22 6 2 2 2 = true := by decide +kernel

/-- **Sharp White-to-White Gap Bounds for `FirstLoss`:**
`a + 5 ≤ b` for all `e`; `a + 21 ≤ b` for `1 ≤ e` (sharp at `e = 1`!); and `a + 23 ≤ b` for `2 ≤ e`. -/
theorem firstLoss_gap_bounds {d : Nat → Column} (hd : Recurrence d) (clocks : PrefixClocks d)
    {a e b : Nat} (loss : FirstLoss d a e) (hab : NextWhite d a b) :
    a + 5 ≤ b ∧ (1 ≤ e → a + 21 ≤ b) ∧ (2 ≤ e → a + 23 ≤ b) := by
  have h4 : a + 4 ≤ b := (firstLoss_cascade_and_immediate_catch hd clocks loss hab).2.2.1
  have h5 : a + 5 ≤ b := by
    refine Classical.byContradiction fun hlt => ?_
    exact pairedGapExclude_sound hd clocks gap_excl_4 (Nat.zero_le _) loss hab (by omega)
  have h21 : 1 ≤ e → a + 21 ≤ b := fun he1 => by
    refine Classical.byContradiction fun hlt => ?_
    by_cases hk5 : b - a = 5
    · have hodd := odd_gap_ge_two_mul_add_five hd clocks loss hab (by omega)
      omega
    ·
      by_cases hle_12 : b - a ≤ 12
      ·
        by_cases hle_8 : b - a ≤ 8
        ·
          by_cases hle_6 : b - a ≤ 6
          ·
            exact pairedGapExclude_sound hd clocks gap_excl_6 he1 loss hab (by omega)
          ·
            by_cases hle_7 : b - a ≤ 7
            ·
              exact pairedGapExclude_sound hd clocks gap_excl_7 he1 loss hab (by omega)
            ·
              exact pairedGapExclude_sound hd clocks gap_excl_8 he1 loss hab (by omega)
        ·
          by_cases hle_10 : b - a ≤ 10
          ·
            by_cases hle_9 : b - a ≤ 9
            ·
              exact pairedGapExclude_sound hd clocks gap_excl_9 he1 loss hab (by omega)
            ·
              exact pairedGapExclude_sound hd clocks gap_excl_10 he1 loss hab (by omega)
          ·
            by_cases hle_11 : b - a ≤ 11
            ·
              exact pairedGapExclude_sound hd clocks gap_excl_11 he1 loss hab (by omega)
            ·
              exact pairedGapExclude_sound hd clocks gap_excl_12 he1 loss hab (by omega)
      ·
        by_cases hle_16 : b - a ≤ 16
        ·
          by_cases hle_14 : b - a ≤ 14
          ·
            by_cases hle_13 : b - a ≤ 13
            ·
              exact pairedGapExclude_sound hd clocks gap_excl_13 he1 loss hab (by omega)
            ·
              exact pairedGapExclude_sound hd clocks gap_excl_14 he1 loss hab (by omega)
          ·
            by_cases hle_15 : b - a ≤ 15
            ·
              exact pairedGapExclude_sound hd clocks gap_excl_15 he1 loss hab (by omega)
            ·
              exact pairedGapExclude_sound hd clocks gap_excl_16 he1 loss hab (by omega)
        ·
          by_cases hle_18 : b - a ≤ 18
          ·
            by_cases hle_17 : b - a ≤ 17
            ·
              exact pairedGapExclude_sound hd clocks gap_excl_17 he1 loss hab (by omega)
            ·
              exact pairedGapExclude_sound hd clocks gap_excl_18 he1 loss hab (by omega)
          ·
            by_cases hle_19 : b - a ≤ 19
            ·
              exact pairedGapExclude_sound hd clocks gap_excl_19 he1 loss hab (by omega)
            ·
              exact pairedGapExclude_sound hd clocks gap_excl_20 he1 loss hab (by omega)
  have h23 : 2 ≤ e → a + 23 ≤ b := fun he2 => by
    have := h21 (by omega)
    refine Classical.byContradiction fun hlt => ?_
    by_cases hk21 : b - a = 21
    · exact pairedGapExclude_sound hd clocks gap_excl_21 he2 loss hab hk21
    · exact pairedGapExclude_sound hd clocks gap_excl_22 he2 loss hab (by omega)
  exact ⟨h5, h21, h23⟩

theorem firstLoss_gap_ge_21_of_pos {d : Nat → Column} (hd : Recurrence d) (clocks : PrefixClocks d)
    {a e b : Nat} (he : 1 ≤ e) (loss : FirstLoss d a e) (hab : NextWhite d a b) :
    a + 21 ≤ b := (firstLoss_gap_bounds hd clocks loss hab).2.1 he

theorem firstLoss_gap_ge_23_of_two_le {d : Nat → Column} (hd : Recurrence d) (clocks : PrefixClocks d)
    {a e b : Nat} (he : 2 ≤ e) (loss : FirstLoss d a e) (hab : NextWhite d a b) :
    a + 23 ≤ b := (firstLoss_gap_bounds hd clocks loss hab).2.2 he

/-! ## 4. Universal carry-world causal factor verifier and sharp `0^9` / `1^8` capture -/

noncomputable def scanRow (p2 : List Bool) : List Bool → Bool → List Bool :=
  List.rec (motive := fun _ => List Bool → Bool → List Bool)
    (fun _ _ => [])
    (fun a _ ih p1 acc => acc :: ih p1.tail (xor a (p1.headD false || acc)))
    p2

theorem scanRow_length : ∀ (p2 p1 : List Bool) (acc : Bool),
    (scanRow p2 p1 acc).length = p2.length
  | [], _, _ => rfl
  | _ :: as, p1, acc => by
    change (acc :: scanRow as p1.tail _).length = _
    simp [scanRow_length as]

theorem scanRow_step : ∀ (p2 p1 : List Bool) (acc : Bool) (u : Nat),
    u + 1 < p2.length → p1.length = p2.length →
    (scanRow p2 p1 acc).getD (u + 1) false =
      xor (p2.getD u false) (p1.getD u false || (scanRow p2 p1 acc).getD u false)
  | [], _, _, _, hu, _ => absurd hu (Nat.not_lt_zero _)
  | _ :: _, [], _, _, _, hlen => by simp at hlen
  | a :: b :: as, c :: cs, acc, 0, _, _ => rfl
  | a :: as, c :: cs, acc, u + 1, hu, hlen => by
    change (scanRow as cs (xor a (c || acc))).getD (u + 1) false =
      xor (as.getD u false) (cs.getD u false || (scanRow as cs (xor a (c || acc))).getD u false)
    exact scanRow_step as cs (xor a (c || acc)) u (by simp at hu; omega) (by simp at hlen; omega)

noncomputable def dfaNext (st : Nat) (b : Bool) : Option Nat :=
  Bool.rec (motive := fun _ => Option Nat)
    (Bool.rec (motive := fun _ => Option Nat) (some 0) none (Nat.beq st 1))
    (some (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) 3 2 (Nat.beq st 1))
      1 (Nat.beq st 0 || Nat.beq st 3)))
    b

def dfaInv (st r : Nat) : Prop :=
  (st = 0 ∧ r = 0) ∨ (st = 1 ∧ r % 3 = 1) ∨ (st = 2 ∧ r % 3 = 2) ∨ (st = 3 ∧ 0 < r ∧ r % 3 = 0)

noncomputable def beqBoolList (xs : List Bool) : List Bool → Bool :=
  List.rec (motive := fun _ => List Bool → Bool)
    (fun ys => match ys with | [] => true | _ :: _ => false)
    (fun x _ ih ys => match ys with | [] => false | y :: ys' => Bool.beq x y && ih ys')
    xs

theorem beqBoolList_eq : ∀ {xs ys : List Bool}, beqBoolList xs ys = true → xs = ys
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    change (Bool.beq x y && beqBoolList xs ys) = true at h
    rw [Bool.and_eq_true] at h
    have hxy : x = y := by cases x <;> cases y <;> first | rfl | exact absurd h.1 (by decide)
    rw [hxy, beqBoolList_eq h.2]
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

abbrev World := List Bool × List Bool × Nat

noncomputable def beqWorld (x y : World) : Bool :=
  beqBoolList x.1 y.1 && beqBoolList x.2.1 y.2.1 && Nat.beq x.2.2 y.2.2

theorem beqWorld_eq {x y : World} (h : beqWorld x y = true) : x = y := by
  rcases x with ⟨x1, x2, x3⟩; rcases y with ⟨y1, y2, y3⟩
  dsimp only [beqWorld] at h
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  rw [beqBoolList_eq h.1.1, beqBoolList_eq h.1.2, h.2]

noncomputable def insWorld (w : World) (ws : List World) : List World :=
  List.rec (motive := fun _ => List World) [w]
    (fun h t ih => Bool.rec (motive := fun _ => List World) (h :: ih) (h :: t) (beqWorld w h)) ws

theorem mem_insWorld (w : World) : ∀ (ws : List World), w ∈ insWorld w ws
  | [] => List.mem_singleton.mpr rfl
  | h :: t => by
    change w ∈ Bool.rec (motive := fun _ => List World) (h :: insWorld w t) (h :: t) (beqWorld w h)
    cases hbeq : beqWorld w h
    · exact List.mem_cons_of_mem h (mem_insWorld w t)
    · dsimp only; rw [beqWorld_eq hbeq]; exact List.mem_cons_self

theorem mem_insWorld_of_mem {u w : World} : ∀ {ws : List World},
    u ∈ ws → u ∈ insWorld w ws
  | [], h => nomatch h
  | x :: xs, h => by
    change u ∈ Bool.rec (motive := fun _ => List World) (x :: insWorld w xs) (x :: xs) (beqWorld w x)
    cases beqWorld w x
    · dsimp only
      rcases List.mem_cons.mp h with rfl | hm
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_insWorld_of_mem hm)
    · exact h

noncomputable def pushBranch (wLen : Nat) (p2 p1 : List Bool) (st : Nat) (c0 : Bool) (acc : List World) :
    List World :=
  let nxt := scanRow p2 p1 c0
  match dfaNext st (nxt.getD (wLen - 1) false) with
  | none => acc
  | some st' => insWorld (p1, nxt, st') acc

noncomputable def stepWorlds (wLen : Nat) (ws : List World) : List World :=
  List.rec (motive := fun _ => List World) [] (fun item _ ih =>
    pushBranch wLen item.1 item.2.1 item.2.2 false
      (pushBranch wLen item.1 item.2.1 item.2.2 true ih)) ws

noncomputable def runWorlds (wLen fuel : Nat) (ws : List World) : Bool :=
  Nat.rec (motive := fun _ => List World → Bool)
    (fun cur => match cur with | [] => true | _ :: _ => false)
    (fun _ ih cur => match cur with | [] => true | _ :: _ => ih (stepWorlds wLen cur))
    fuel ws

noncomputable def causalCatch (w : List Bool) (fuel : Nat) : Bool :=
  decide (1 ≤ w.length) && decide (fuel ≤ 18) &&
  match dfaNext 0 (w.getD (w.length - 1) false) with
  | none => true
  | some s1 =>
    match dfaNext s1 true with
    | none => true
    | some s2 => runWorlds w.length fuel [(w, List.replicate w.length true, s2)]

theorem dfaNext_sound {d : Nat → Column} {a c : Nat} (k : Nat) {s st : Nat} (hwa : White d a)
    (hkc : a + k + 1 ≤ c) (hnc : ¬ Catch d a c s)
    (hinv : dfaInv st (trailingOnes (fun i => d i s) a k)) :
    ∃ st', dfaNext st (d (a + k + 1) s) = some st' ∧
      dfaInv st' (trailingOnes (fun i => d i s) a (k + 1)) := by
  let r := trailingOnes (fun i => d i s) a k
  have htr : trailingOnes (fun i => d i s) a (k + 1) = if d (a + k + 1) s then r + 1 else 0 := rfl
  cases hb : d (a + k + 1) s
  · rw [hb] at htr; simp only [Bool.false_eq_true, ↓reduceIte] at htr
    rcases hinv with ⟨rfl, _⟩ | ⟨rfl, hr1⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact ⟨0, rfl, Or.inl ⟨rfl, htr⟩⟩
    · exfalso
      obtain ⟨hr_le, hleft, hmid⟩ := trailingOnes_spec (fun i => d i s) a (hwa s) k
      apply hnc
      refine ⟨a + k - r, r, by omega, by omega, hr1, hleft, hmid, ?_⟩
      simpa [show a + k - r + 1 + r = a + k + 1 by omega] using hb
    · exact ⟨0, rfl, Or.inl ⟨rfl, htr⟩⟩
    · exact ⟨0, rfl, Or.inl ⟨rfl, htr⟩⟩
  · rw [hb] at htr; simp only [↓reduceIte] at htr
    rcases hinv with ⟨rfl, hr0⟩ | ⟨rfl, hr1⟩ | ⟨rfl, hr2⟩ | ⟨rfl, _, hr0⟩
    · exact ⟨1, rfl, Or.inr (Or.inl ⟨rfl, by omega⟩)⟩
    · exact ⟨2, rfl, Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩))⟩
    · exact ⟨3, rfl, Or.inr (Or.inr (Or.inr ⟨rfl, by omega, by omega⟩))⟩
    · exact ⟨1, rfl, Or.inr (Or.inl ⟨rfl, by omega⟩)⟩

theorem scanRow_eq_col {d : Nat → Column} (hd : Recurrence d) {i t0 W : Nat}
    {p2 p1 : List Bool} (hp2_len : p2.length = W) (hp1_len : p1.length = W)
    (hp2 : ∀ u, u < W → p2.getD u false = d i (t0 + u))
    (hp1 : ∀ u, u < W → p1.getD u false = d (i + 1) (t0 + u)) :
    ∀ u, u < W → (scanRow p2 p1 (d (i + 2) t0)).getD u false = d (i + 2) (t0 + u) := by
  intro u; induction u with
  | zero =>
    intro hu
    rcases p2 with _ | ⟨a, as⟩
    · simp at hp2_len; omega
    · rfl
  | succ u ih =>
    intro hu
    rw [scanRow_step p2 p1 (d (i + 2) t0) u (by omega) (by omega),
        hp2 u (by omega), hp1 u (by omega), ih (by omega),
        show t0 + (u + 1) = (t0 + u) + 1 by omega]
    exact (hd.2.2 i (t0 + u)).symm

theorem mem_stepWorlds {wLen : Nat} {p2 p1 : List Bool} {st : Nat} {c0 : Bool} {st' : Nat} :
    ∀ {ws : List World},
    (p2, p1, st) ∈ ws →
    dfaNext st ((scanRow p2 p1 c0).getD (wLen - 1) false) = some st' →
    (p1, scanRow p2 p1 c0, st') ∈ stepWorlds wLen ws
  | [], h, _ => nomatch h
  | (q2, q1, qst) :: rest, h, hdfa => by
    change (p1, scanRow p2 p1 c0, st') ∈
      pushBranch wLen q2 q1 qst false (pushBranch wLen q2 q1 qst true (stepWorlds wLen rest))
    rcases List.mem_cons.mp h with heq | hmem
    · cases heq
      cases c0
      · dsimp only [pushBranch]; rw [hdfa]; exact mem_insWorld _ _
      · dsimp only [pushBranch]
        cases dfaNext st ((scanRow p2 p1 false).getD (wLen - 1) false)
        · rw [hdfa]; exact mem_insWorld _ _
        · apply mem_insWorld_of_mem
          rw [hdfa]; exact mem_insWorld _ _
    · have ih := mem_stepWorlds hmem hdfa
      have h1 : (p1, scanRow p2 p1 c0, st') ∈ pushBranch wLen q2 q1 qst true (stepWorlds wLen rest) := by
        dsimp only [pushBranch]
        cases dfaNext qst ((scanRow q2 q1 true).getD (wLen - 1) false)
        · exact ih
        · exact mem_insWorld_of_mem ih
      dsimp only [pushBranch]
      cases dfaNext qst ((scanRow q2 q1 false).getD (wLen - 1) false)
      · exact h1
      · exact mem_insWorld_of_mem h1

theorem causalCatch_sound_aux {d : Nat → Column} (hd : Recurrence d) (clocks : PrefixClocks d)
    {a e b t0 : Nat} {w : List Bool} {fuel : Nat}
    (hc : causalCatch w fuel = true)
    (loss : FirstLoss d a e) (hab : NextWhite d a b)
    (hw : ∀ u, u < w.length → d (a + 1) (t0 + u) = w.getD u false) :
    Catch d a (a + 2 + fuel) (t0 + w.length - 1) := by
  refine Classical.byContradiction fun hnc => ?_
  dsimp only [causalCatch] at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hlen1, _⟩, hbody⟩ := hc
  let W := w.length
  let s := t0 + W - 1
  have hs_eq : t0 + (W - 1) = s := by omega
  have hw_last : d (a + 1) s = w.getD (W - 1) false := by
    rw [← hs_eq]; exact hw (W - 1) (by omega)
  have hd2_one : ∀ t, d (a + 2) t = true :=
    (firstLoss_cascade_and_immediate_catch hd clocks loss hab).1
  obtain ⟨s1, hs1_eq, hs1_inv⟩ :=
    dfaNext_sound 0 loss.white (by omega) hnc (Or.inl ⟨rfl, rfl⟩)
  rw [Nat.add_zero, hw_last] at hs1_eq
  rw [hs1_eq] at hbody; dsimp only at hbody
  obtain ⟨s2, hs2_eq, hs2_inv⟩ :=
    dfaNext_sound 1 loss.white (by omega) hnc hs1_inv
  rw [show a + 1 + 1 = a + 2 by omega, hd2_one s] at hs2_eq
  rw [hs2_eq] at hbody; dsimp only at hbody
  have hloop : ∀ (rem k : Nat) (ws : List World),
      k + rem = 1 + fuel →
      1 ≤ k →
      (∃ p2 p1 st, (p2, p1, st) ∈ ws ∧ p2.length = W ∧ p1.length = W ∧
        (∀ u, u < W → p2.getD u false = d (a + k) (t0 + u)) ∧
        (∀ u, u < W → p1.getD u false = d (a + k + 1) (t0 + u)) ∧
        dfaInv st (trailingOnes (fun i => d i s) a (k + 1))) →
      runWorlds W rem ws = true → False := by
    intro rem; induction rem with
    | zero =>
      intro k ws _ _ ⟨p2, p1, st, hmem, _⟩ hrun
      rcases ws with _ | ⟨h, t⟩
      · nomatch hmem
      · nomatch hrun
    | succ rem ih =>
      intro k ws hkrem hk1 ⟨p2, p1, st, hmem, hl2, hl1, hp2, hp1, hinv⟩ hrun
      rcases ws with _ | ⟨h, t⟩
      · nomatch hmem
      · change runWorlds W rem (stepWorlds W (h :: t)) = true at hrun
        let c0 := d (a + k + 2) t0
        have hscan := scanRow_eq_col hd hl2 hl1 hp2 hp1
        have hlast : (scanRow p2 p1 c0).getD (W - 1) false = d (a + k + 2) s := by
          rw [hscan (W - 1) (by omega), hs_eq]
        obtain ⟨st', hst'_eq, hst'_inv⟩ :=
          dfaNext_sound (k + 1) loss.white (by omega) hnc hinv
        rw [show a + (k + 1) + 1 = a + k + 2 by omega, ← hlast] at hst'_eq
        exact ih (k + 1) (stepWorlds W (h :: t)) (by omega) (by omega)
          ⟨p1, scanRow p2 p1 c0, st', mem_stepWorlds hmem hst'_eq, hl1,
           by rw [scanRow_length, hl2], hp1,
           fun u hu => by rw [show a + (k + 1) + 1 = a + k + 2 by omega]; exact hscan u hu, hst'_inv⟩ hrun
  exact hloop fuel 1 [(w, List.replicate W true, s2)] (by omega) (Nat.le_refl 1)
    ⟨w, List.replicate W true, s2, List.mem_singleton.mpr rfl, rfl, List.length_replicate,
     fun u hu => (hw u hu).symm,
     fun u hu => by
       have hrep : ∀ (n : Nat) (v : Nat), v < n → (List.replicate n true).getD v false = true := by
         intro n; induction n with
         | zero => intro v hv; omega
         | succ n ihn =>
           intro v hv; rcases v with _ | v
           · rfl
           · dsimp only [List.replicate, List.getD, List.getElem?_cons_succ]; exact ihn v (by omega)
       rw [hrep W u hu, hd2_one],
     hs2_inv⟩ hbody

theorem catch_mono_right {d : Nat → Column} {a c1 c2 s : Nat}
    (hc : Catch d a c1 s) (hle : c1 ≤ c2) : Catch d a c2 s := by
  obtain ⟨j, n, haj, hjn, hr⟩ := hc
  exact ⟨j, n, haj, by omega, hr⟩

theorem causalCatch_sound {d : Nat → Column} (hd : Recurrence d) (clocks : PrefixClocks d)
    {a e b t0 : Nat} {w : List Bool} {fuel : Nat}
    (hc : causalCatch w fuel = true)
    (loss : FirstLoss d a e) (hab : NextWhite d a b)
    (hw : ∀ u, u < w.length → d (a + 1) (t0 + u) = w.getD u false) :
    Catch d a b (t0 + w.length - 1) := by
  rcases e with _ | e'
  · exact catch_of_firstLoss_le_four hd clocks (by omega) loss hab (t0 + w.length - 1)
  · have hfuel18 : fuel ≤ 18 := by
      dsimp only [causalCatch] at hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact hc.1.2
    have h21 := firstLoss_gap_ge_21_of_pos hd clocks (by omega) loss hab
    exact catch_mono_right (causalCatch_sound_aux hd clocks hc loss hab hw) (by omega)

private theorem cc_nine_whites : causalCatch (List.replicate 9 false) 7 = true := by decide +kernel
private theorem cc_eight_blacks : causalCatch (List.replicate 8 true) 6 = true := by decide +kernel

/-- **Universal `0^9` White-Run Capture:** on *every* `FirstLoss d a e` strip (`e : Nat`),
any `9` consecutive white ticks on `d (a + 1)` catch tick `t0 + 8` within `9` wheels (`a + 9`)
and inside `[a, b]`. -/
theorem catch_of_nine_whites {d : Nat → Column} (hd : Recurrence d) (clocks : PrefixClocks d)
    {a e b t0 : Nat} (loss : FirstLoss d a e) (hab : NextWhite d a b)
    (hw : ∀ u, u < 9 → d (a + 1) (t0 + u) = false) :
    Catch d a (a + 9) (t0 + 8) ∧ Catch d a b (t0 + 8) := by
  have he1 : 1 ≤ e := by
    rcases e with _ | e'
    · exfalso
      have h0 := hw 0 (by omega); simp only [Nat.add_zero] at h0
      have h1 := hw 1 (by omega)
      have hf := loss.flip t0
      rw [show 2 ^ 0 = 1 from rfl, h0, h1] at hf; exact absurd hf (by decide)
    · omega
  have hw_list : ∀ u, u < (List.replicate 9 false).length →
      d (a + 1) (t0 + u) = (List.replicate 9 false).getD u false := by
    intro u hu; simp only [List.length_replicate] at hu
    have hrep : (List.replicate 9 false).getD u false = false := by
      rcases (show u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 ∨ u = 4 ∨ u = 5 ∨ u = 6 ∨ u = 7 ∨ u = 8 by omega)
        with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    rw [hw u hu, hrep]
  have hc9 := causalCatch_sound_aux hd clocks cc_nine_whites loss hab hw_list
  simp only [List.length_replicate] at hc9
  have h21 := firstLoss_gap_ge_21_of_pos hd clocks he1 loss hab
  exact ⟨hc9, catch_mono_right hc9 (by omega)⟩

/-- **Universal `1^8` Black-Run Capture:** on *every* `FirstLoss d a e` strip (`e : Nat`),
any `8` consecutive black ticks on `d (a + 1)` catch tick `t0 + 7` within `8` wheels (`a + 8`)
and inside `[a, b]`. -/
theorem catch_of_eight_blacks {d : Nat → Column} (hd : Recurrence d) (clocks : PrefixClocks d)
    {a e b t0 : Nat} (loss : FirstLoss d a e) (hab : NextWhite d a b)
    (hb8 : ∀ u, u < 8 → d (a + 1) (t0 + u) = true) :
    Catch d a (a + 8) (t0 + 7) ∧ Catch d a b (t0 + 7) := by
  have he1 : 1 ≤ e := by
    rcases e with _ | e'
    · exfalso
      have h0 := hb8 0 (by omega); simp only [Nat.add_zero] at h0
      have h1 := hb8 1 (by omega)
      have hf := loss.flip t0
      rw [show 2 ^ 0 = 1 from rfl, h0, h1] at hf; exact absurd hf (by decide)
    · omega
  have hw_list : ∀ u, u < (List.replicate 8 true).length →
      d (a + 1) (t0 + u) = (List.replicate 8 true).getD u false := by
    intro u hu; simp only [List.length_replicate] at hu
    have hrep : (List.replicate 8 true).getD u false = true := by
      rcases (show u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 ∨ u = 4 ∨ u = 5 ∨ u = 6 ∨ u = 7 by omega)
        with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    rw [hb8 u hu, hrep]
  have hc8 := causalCatch_sound_aux hd clocks cc_eight_blacks loss hab hw_list
  simp only [List.length_replicate] at hc8
  have h21 := firstLoss_gap_ge_21_of_pos hd clocks he1 loss hab
  exact ⟨hc8, catch_mono_right hc8 (by omega)⟩

/-! ## 5. Strict bitmask sharpness witnesses (`canonStrip`, `sharpWhite8Strip`, `sharpBlack7Strip`) -/

noncomputable def scanMaskFn (m2 m1 : Nat) (z : Bool) (n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) z (fun u acc => xor (m2.testBit u) (m1.testBit u || acc)) n

noncomputable def xorMaskFn (m2 L n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun u acc => xor (m2.testBit (u % L)) acc) n

theorem xorMaskFn_add_period (m2 L : Nat) (hL : 0 < L) :
    ∀ k, xorMaskFn m2 L (L + k) = xor (xorMaskFn m2 L k) (xorMaskFn m2 L L)
  | 0 => by
    change xorMaskFn m2 L L = xor false (xorMaskFn m2 L L)
    simp
  | k + 1 => by
    rw [show L + (k + 1) = (L + k) + 1 by omega]
    change xor (m2.testBit ((L + k) % L)) (xorMaskFn m2 L (L + k)) =
      xor (xor (m2.testBit (k % L)) (xorMaskFn m2 L k)) (xorMaskFn m2 L L)
    rw [show (L + k) % L = k % L by rw [Nat.add_comm, Nat.add_mod_right],
        xorMaskFn_add_period m2 L hL k, Bool.xor_assoc]

theorem scanMaskFn_sync {m2 m1 : Nat} {z1 z2 : Bool} {u0 : Nat} (hu0 : m1.testBit u0 = true) :
    ∀ k, u0 < k → scanMaskFn m2 m1 z1 k = scanMaskFn m2 m1 z2 k
  | 0, hk => absurd hk (Nat.not_lt_zero _)
  | k + 1, hk => by
    change xor (m2.testBit k) (m1.testBit k || scanMaskFn m2 m1 z1 k) =
      xor (m2.testBit k) (m1.testBit k || scanMaskFn m2 m1 z2 k)
    by_cases heq : k = u0
    · subst heq; simp [hu0]
    · rw [scanMaskFn_sync hu0 k (by omega)]

noncomputable def stepMaskState (st : Nat × Nat × Nat) : Nat × Nat × Nat :=
  let L := st.1
  let m2 := st.2.1
  let m1 := st.2.2
  Bool.rec (motive := fun _ => Nat × Nat × Nat)
    (let z0 := scanMaskFn m2 m1 false L
     (L, m1, bpack (fun u => scanMaskFn m2 m1 z0 u) L))
    (2 * L, bpack (fun u => m1.testBit (u % L)) (2 * L),
     bpack (fun u => xorMaskFn m2 L u) (2 * L))
    (Nat.beq (m1 % 2 ^ L) 0)

noncomputable def extMaskState (L0 m0 m1 n : Nat) : Nat × Nat × Nat :=
  Nat.rec (motive := fun _ => Nat × Nat × Nat) (L0, m0, m1) (fun _ acc => stepMaskState acc) n

noncomputable def maskStrip (L0 m0 m1 : Nat) (i t : Nat) : Bool :=
  match i with
  | 0 => m0.testBit (t % L0)
  | j + 1 =>
    let st := extMaskState L0 m0 m1 j
    st.2.2.testBit (t % st.1)

theorem stepMaskState_spec (st : Nat × Nat × Nat) (hL : 0 < st.1) :
    let nxt := stepMaskState st
    0 < nxt.1 ∧ st.1 ∣ nxt.1 ∧
    (∀ t, nxt.2.1.testBit (t % nxt.1) = st.2.2.testBit (t % st.1)) ∧
    (∀ t, nxt.2.2.testBit ((t + 1) % nxt.1) =
      xor (st.2.1.testBit (t % st.1))
        (st.2.2.testBit (t % st.1) || nxt.2.2.testBit (t % nxt.1))) := by
  rcases st with ⟨L, m2, m1⟩
  dsimp only [stepMaskState] at hL ⊢
  cases hzero : Nat.beq (m1 % 2 ^ L) 0
  · dsimp only
    have hex_one : ∃ u0, u0 < L ∧ m1.testBit u0 = true := by
      refine Classical.byContradiction fun hno => ?_
      have hm0 : m1 % 2 ^ L = 0 := by
        apply Nat.eq_of_testBit_eq; intro u
        rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
        by_cases hu : u < L
        · cases hb : m1.testBit u
          · simp [hu]
          · exact absurd ⟨u, hu, hb⟩ hno
        · simp [hu]
      rw [hm0, Nat.beq_refl] at hzero; exact absurd hzero (by decide)
    obtain ⟨u0, hu0_lt, hu0_b⟩ := hex_one
    let z0 := scanMaskFn m2 m1 false L
    have hsync : scanMaskFn m2 m1 z0 L = z0 := scanMaskFn_sync hu0_b L hu0_lt
    refine ⟨hL, Nat.dvd_refl L, fun _ => rfl, fun t => ?_⟩
    let r := t % L
    have hr_lt : r < L := Nat.mod_lt t hL
    rw [testBit_bpack _ L r, show decide (r < L) = true from decide_eq_true hr_lt, Bool.true_and]
    by_cases hlast : r + 1 = L
    · have hmod1 : (t + 1) % L = 0 := by
        have hdm := Nat.div_add_mod t L
        have : t + 1 = L * (t / L + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
        rw [this, Nat.mul_mod_right]
      rw [hmod1, testBit_bpack _ L 0, show decide (0 < L) = true from decide_eq_true hL, Bool.true_and]
      change z0 = xor (m2.testBit r) (m1.testBit r || scanMaskFn m2 m1 z0 r)
      have hw := hsync; rw [← hlast] at hw; exact hw.symm
    · have hmod1 : (t + 1) % L = r + 1 := by
        have : t + 1 = (r + 1) + L * (t / L) := by have := Nat.div_add_mod t L; omega
        rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      rw [hmod1, testBit_bpack _ L (r + 1),
          show decide (r + 1 < L) = true from decide_eq_true (by omega), Bool.true_and]
      rfl
  · dsimp only
    rw [Nat.beq_eq] at hzero
    have hm1_false : ∀ u, u < L → m1.testBit u = false := fun u hu => by
      have hb := congrArg (fun v => v.testBit u) hzero
      simpa [Nat.testBit_mod_two_pow, hu] using hb
    have hwrap : xorMaskFn m2 L (2 * L) = false := by
      rw [show 2 * L = L + L by omega, xorMaskFn_add_period m2 L hL L, Bool.xor_self]
    refine ⟨by omega, ⟨2, by omega⟩, fun t => ?_, fun t => ?_⟩
    · have hlt2 : t % (2 * L) < 2 * L := Nat.mod_lt t (by omega)
      rw [testBit_bpack, show decide (t % (2 * L) < 2 * L) = true from decide_eq_true hlt2, Bool.true_and,
          Nat.mod_mod_of_dvd t ⟨2, by omega⟩]
    · let r := t % (2 * L)
      have hr_lt : r < 2 * L := Nat.mod_lt t (by omega)
      have hr_mod : r % L = t % L := Nat.mod_mod_of_dvd t ⟨2, by omega⟩
      rw [hm1_false (t % L) (Nat.mod_lt t hL), Bool.false_or,
          testBit_bpack _ (2 * L) r, show decide (r < 2 * L) = true from decide_eq_true hr_lt, Bool.true_and]
      by_cases hlast : r + 1 = 2 * L
      · have hmod1 : (t + 1) % (2 * L) = 0 := by
          have hdm := Nat.div_add_mod t (2 * L)
          have : t + 1 = (2 * L) * (t / (2 * L) + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
          rw [this, Nat.mul_mod_right]
        rw [hmod1, testBit_bpack _ (2 * L) 0,
            show decide (0 < 2 * L) = true from decide_eq_true (by omega), Bool.true_and]
        change false = xor (m2.testBit (t % L)) (xorMaskFn m2 L r)
        have hw := hwrap; rw [← hlast] at hw
        rw [← hw]; change xor (m2.testBit (r % L)) (xorMaskFn m2 L r) = _
        rw [hr_mod]
      · have hmod1 : (t + 1) % (2 * L) = r + 1 := by
          have : t + 1 = (r + 1) + (2 * L) * (t / (2 * L)) := by have := Nat.div_add_mod t (2 * L); omega
          rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
        rw [hmod1, testBit_bpack _ (2 * L) (r + 1),
            show decide (r + 1 < 2 * L) = true from decide_eq_true (by omega), Bool.true_and]
        change xor (m2.testBit (r % L)) (xorMaskFn m2 L r) = _
        rw [hr_mod]

noncomputable def maskPeriod (L0 m0 m1 i : Nat) : Nat :=
  match i with
  | 0 => L0
  | j + 1 => (extMaskState L0 m0 m1 j).1

theorem maskStrip_spec {L0 m0 m1 : Nat} (hL0 : 0 < L0) :
    ∀ i, 0 < maskPeriod L0 m0 m1 i ∧
      PeriodFrom (maskStrip L0 m0 m1 i) 0 (maskPeriod L0 m0 m1 i) ∧
      (∀ j, j ≤ i → maskPeriod L0 m0 m1 j ∣ maskPeriod L0 m0 m1 i) ∧
      ∀ t, maskStrip L0 m0 m1 (i + 2) (t + 1) =
        xor (maskStrip L0 m0 m1 i t)
          (maskStrip L0 m0 m1 (i + 1) t || maskStrip L0 m0 m1 (i + 2) t) := by
  have hst_pos : ∀ k, 0 < (extMaskState L0 m0 m1 k).1 ∧
      (∀ j, j ≤ k + 1 → maskPeriod L0 m0 m1 j ∣ (extMaskState L0 m0 m1 k).1) := by
    intro k; induction k with
    | zero =>
      exact ⟨hL0, fun j hj => by
        rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;> exact Nat.dvd_refl L0⟩
    | succ k ih =>
      have hsp := stepMaskState_spec (extMaskState L0 m0 m1 k) ih.1
      refine ⟨hsp.1, fun j hj => ?_⟩
      by_cases hjk : j ≤ k + 1
      · exact Nat.dvd_trans (ih.2 j hjk) hsp.2.1
      · have hj_eq : j = k + 2 := by omega
        rw [hj_eq]; exact Nat.dvd_refl _
  have hp_per : ∀ k, PeriodFrom (maskStrip L0 m0 m1 k) 0 (maskPeriod L0 m0 m1 k) := by
    intro k; rcases k with _ | j
    · intro t _; dsimp only [maskStrip, maskPeriod]; rw [Nat.add_mod_right]
    · intro t _; dsimp only [maskStrip, maskPeriod]; rw [Nat.add_mod_right]
  intro i
  rcases i with _ | j
  · have hsp0 := stepMaskState_spec (L0, m0, m1) hL0
    refine ⟨hL0, hp_per 0, fun j hj => ?_, fun t => hsp0.2.2.2 t⟩
    have hj0 : j = 0 := by omega
    rw [hj0]; exact Nat.dvd_refl _
  · obtain ⟨hpos, hdvd⟩ := hst_pos j
    have hsp := stepMaskState_spec (extMaskState L0 m0 m1 (j + 1)) (hst_pos (j + 1)).1
    have hprev := stepMaskState_spec (extMaskState L0 m0 m1 j) hpos
    refine ⟨hpos, hp_per (j + 1), hdvd, fun t => ?_⟩
    change (stepMaskState (extMaskState L0 m0 m1 (j + 1))).2.2.testBit
      ((t + 1) % (stepMaskState (extMaskState L0 m0 m1 (j + 1))).1) = _
    rw [hsp.2.2.2 t]
    change xor ((stepMaskState (extMaskState L0 m0 m1 j)).2.1.testBit
      (t % (stepMaskState (extMaskState L0 m0 m1 j)).1)) _ = _
    rw [hprev.2.2.1 t]; rfl

noncomputable def canonStrip : Nat → Column := maskStrip 1 1 1

theorem canonStrip_sharp_five_and_twenty_one :
    Recurrence canonStrip ∧ PrefixClocks canonStrip ∧
    FirstLoss canonStrip 2 0 ∧ NextWhite canonStrip 2 7 ∧
    FirstLoss canonStrip 7 1 ∧ NextWhite canonStrip 7 28 := by
  have hsp := maskStrip_spec (L0 := 1) (m0 := 1) (m1 := 1) (by decide)
  have hc0 : ∀ t, canonStrip 0 t = true := fun t => by
    change (1 : Nat).testBit (t % 1) = true; rw [Nat.mod_one]; decide
  have hc1 : ∀ t, canonStrip 1 t = true := fun t => by
    change (1 : Nat).testBit (t % 1) = true; rw [Nat.mod_one]; decide
  have hrec : Recurrence canonStrip :=
    ⟨fun t => by rw [hc0, hc0], fun t => by rw [hc1, hc0, hc1]; rfl, fun i t => (hsp i).2.2.2 t⟩
  have hcl : PrefixClocks canonStrip := fun m => by
    refine ⟨maskPeriod 1 1 1 m, (hsp m).1, fun i hi t _ => ?_⟩
    obtain ⟨c, hc⟩ := (hsp m).2.2.1 i hi
    rw [hc, Nat.mul_comm]; exact period_mul_add _ (hsp i).2.1 c t
  have hwhite_of : ∀ i, Nat.beq ((extMaskState 1 1 1 i).2.2 % 2 ^ (extMaskState 1 1 1 i).1) 0 = true →
      White canonStrip (i + 1) := by
    intro i hbeq t
    rw [Nat.beq_eq] at hbeq
    have hb := congrArg (fun v => v.testBit (t % (extMaskState 1 1 1 i).1)) hbeq
    have hlt : t % (extMaskState 1 1 1 i).1 < (extMaskState 1 1 1 i).1 :=
      Nat.mod_lt t (hsp (i + 1)).1
    simpa [canonStrip, maskStrip, Nat.testBit_mod_two_pow, hlt] using hb
  have hnonwhite_of : ∀ i, Nat.beq ((extMaskState 1 1 1 i).2.2 % 2 ^ (extMaskState 1 1 1 i).1) 0 = false →
      ¬ White canonStrip (i + 1) := by
    intro i hne hw
    have hm0 : (extMaskState 1 1 1 i).2.2 % 2 ^ (extMaskState 1 1 1 i).1 = 0 := by
      apply Nat.eq_of_testBit_eq; intro u
      rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
      by_cases hu : u < (extMaskState 1 1 1 i).1
      · have hwu := hw u
        have hmod : u % (extMaskState 1 1 1 i).1 = u := Nat.mod_eq_of_lt hu
        change (extMaskState 1 1 1 i).2.2.testBit (u % (extMaskState 1 1 1 i).1) = false at hwu
        rw [hmod] at hwu; simp [hu, hwu]
      · simp [hu]
    rw [hm0, Nat.beq_refl] at hne; exact absurd hne (by decide)
  have hp2 : maskPeriod 1 1 1 2 = 1 := by decide +kernel
  have hp7 : maskPeriod 1 1 1 7 = 2 := by decide +kernel
  have hfl2 : FirstLoss canonStrip 2 0 := by
    refine ⟨fun i hi t _ => ?_, fun q hq _ => by omega, hwhite_of 1 (by decide +kernel), fun t => ?_⟩
    · obtain ⟨c, hc⟩ := (hsp 2).2.2.1 i hi
      rw [hp2] at hc
      have h1 : maskPeriod 1 1 1 i = 1 := Nat.eq_one_of_dvd_one ⟨c, hc⟩
      have hp := (hsp i).2.1; rw [h1] at hp; exact hp t (Nat.zero_le _)
    · have hp3 : maskPeriod 1 1 1 3 = 2 := by decide +kernel
      have hper3 := (hsp 3).2.1; rw [hp3] at hper3
      have hmod : ∀ u, canonStrip 3 u = canonStrip 3 (u % 2) := fun u => by
        have h := period_mul_add (canonStrip 3) hper3 (u / 2) (u % 2)
        rw [show u % 2 + u / 2 * 2 = u % 2 + 2 * (u / 2) by rw [Nat.mul_comm], Nat.mod_add_div u 2] at h
        exact h
      rw [hmod (t + 1), hmod t]
      have hvals : canonStrip 3 0 = false ∧ canonStrip 3 1 = true := by decide +kernel
      rcases Nat.mod_two_eq_zero_or_one t with ht0 | ht1
      · rw [ht0, show (t + 1) % 2 = 1 by omega, hvals.1, hvals.2]; rfl
      · rw [ht1, show (t + 1) % 2 = 0 by omega, hvals.1, hvals.2]; rfl
  have hnw2_7 : NextWhite canonStrip 2 7 := by
    refine ⟨by omega, hwhite_of 6 (by decide +kernel), fun i hi1 hi2 => ?_⟩
    rw [show i = (i - 1) + 1 by omega]
    apply hnonwhite_of (i - 1)
    rcases (show i - 1 = 2 ∨ i - 1 = 3 ∨ i - 1 = 4 ∨ i - 1 = 5 by omega) with h | h | h | h <;>
      rw [h] <;> decide +kernel
  have hfl7 : FirstLoss canonStrip 7 1 := by
    refine ⟨fun i hi t _ => ?_, fun q hq hcl7 => ?_, hwhite_of 6 (by decide +kernel), fun t => ?_⟩
    · obtain ⟨c, hc⟩ := (hsp 7).2.2.1 i hi
      rw [hp7] at hc
      have hp := (hsp i).2.1
      rw [Nat.pow_one, hc, Nat.mul_comm]
      exact period_mul_add _ hp c t
    · by_cases hq1 : q = 1
      · exfalso
        have h3 := hcl7 3 (by omega) 0 (Nat.zero_le _)
        have hvals : canonStrip 3 0 = false ∧ canonStrip 3 1 = true := by decide +kernel
        rw [hq1, Nat.zero_add, hvals.1, hvals.2] at h3; exact absurd h3 (by decide)
      · omega
    · have hp8 : maskPeriod 1 1 1 8 = 4 := by decide +kernel
      have hper8 := (hsp 8).2.1; rw [hp8] at hper8
      have hmod : ∀ u, canonStrip 8 u = canonStrip 8 (u % 4) := fun u => by
        have h := period_mul_add (canonStrip 8) hper8 (u / 4) (u % 4)
        rw [show u % 4 + u / 4 * 4 = u % 4 + 4 * (u / 4) by rw [Nat.mul_comm], Nat.mod_add_div u 4] at h
        exact h
      rw [hmod (t + 2), hmod t, Nat.add_mod t 2 4]
      have hvals : canonStrip 8 0 = false ∧ canonStrip 8 1 = false ∧
          canonStrip 8 2 = true ∧ canonStrip 8 3 = true := by decide +kernel
      have hlt4 : t % 4 < 4 := Nat.mod_lt t (by decide)
      rcases (show t % 4 = 0 ∨ t % 4 = 1 ∨ t % 4 = 2 ∨ t % 4 = 3 by omega) with h | h | h | h <;>
        rw [h] <;> simp [hvals.1, hvals.2.1, hvals.2.2.1, hvals.2.2.2]
  have hnw7_28 : NextWhite canonStrip 7 28 := by
    refine ⟨by omega, hwhite_of 27 (by decide +kernel), fun i hi1 hi2 => ?_⟩
    rw [show i = (i - 1) + 1 by omega]
    apply hnonwhite_of (i - 1)
    have hchk : ((List.range 20).all (fun d =>
      !(Nat.beq ((extMaskState 1 1 1 (7 + d)).2.2 % 2 ^ (extMaskState 1 1 1 (7 + d)).1) 0))) = true := by
      decide +kernel
    have hok := List.all_eq_true.mp hchk (i - 8) (List.mem_range.mpr (by omega))
    rw [show 7 + (i - 8) = i - 1 by omega, Bool.not_eq_true'] at hok
    exact hok
  exact ⟨hrec, hcl, hfl2, hnw2_7, hfl7, hnw7_28⟩

noncomputable def antiMask32 (lo : Nat) : Nat :=
  bpack (fun t => xor (lo.testBit (t % 16)) (decide (16 ≤ t))) 32

noncomputable def sharpWhite8Strip : Nat → Column := maskStrip 32 0 (antiMask32 0x007c)
noncomputable def sharpBlack7Strip : Nat → Column := maskStrip 32 0 (antiMask32 0x0164)

theorem antiMask32_flip (lo : Nat) (t : Nat) :
    (antiMask32 lo).testBit ((t + 16) % 32) = !((antiMask32 lo).testBit (t % 32)) := by
  have hlt1 : (t + 16) % 32 < 32 := Nat.mod_lt _ (by decide)
  have hlt2 : t % 32 < 32 := Nat.mod_lt _ (by decide)
  rw [antiMask32, testBit_bpack, testBit_bpack]
  simp only [hlt1, hlt2, decide_true, Bool.true_and]
  have hm16 : ((t + 16) % 32) % 16 = (t % 32) % 16 := by
    rw [Nat.mod_mod_of_dvd _ ⟨2, by decide⟩, Nat.mod_mod_of_dvd _ ⟨2, by decide⟩, Nat.add_mod_right]
  rw [hm16, Nat.add_mod t 16 32]
  by_cases h16 : 16 ≤ t % 32
  · have hsub : ¬ (16 ≤ (t % 32 + 16) % 32) := by
      have : t % 32 + 16 = (t % 32 - 16) + 32 * 1 := by omega
      rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]; omega
    rw [decide_eq_true h16, decide_eq_false hsub]
    cases lo.testBit ((t % 32) % 16) <;> rfl
  · have hadd : 16 ≤ (t % 32 + 16) % 32 := by
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    rw [decide_eq_false h16, decide_eq_true hadd]
    cases lo.testBit ((t % 32) % 16) <;> rfl

def catchBool (d : Nat → Column) (c s : Nat) : Bool :=
  (List.range c).any (fun j =>
    (List.range c).any (fun n =>
      decide (j + 1 + n ≤ c) && Nat.beq (n % 3) 1 && !(d j s) &&
        !(d (j + 1 + n) s) && (List.range n).all (fun u => d (j + 1 + u) s)))

theorem not_catch_of_catchBool_false {d : Nat → Column} {c s : Nat}
    (hf : catchBool d c s = false) : ¬ Catch d 0 c s := by
  rintro ⟨j, n, _, hjn, hmod, h0, hmid, hend⟩
  have hj : j < c := by omega
  have hn : n < c := by omega
  have hall : (List.range n).all (fun u => d (j + 1 + u) s) = true :=
    List.all_eq_true.mpr (fun u hu => hmid u (List.mem_range.mp hu))
  have hany : catchBool d c s = true := by
    dsimp only [catchBool]
    refine List.any_eq_true.mpr ⟨j, List.mem_range.mpr hj, List.any_eq_true.mpr ⟨n, List.mem_range.mpr hn, ?_⟩⟩
    simp [hjn, hmod, h0, hend, hall]
  rw [hf] at hany; exact absurd hany (by decide)

theorem sharp_eight_whites_and_seven_blacks :
    (∀ i t, sharpWhite8Strip (i + 2) (t + 1) =
      xor (sharpWhite8Strip i t) (sharpWhite8Strip (i + 1) t || sharpWhite8Strip (i + 2) t)) ∧
    PrefixClocks sharpWhite8Strip ∧ White sharpWhite8Strip 0 ∧
    (∀ t, sharpWhite8Strip 1 (t + 16) = !(sharpWhite8Strip 1 t)) ∧
    (∀ u, u < 8 → sharpWhite8Strip 1 (7 + u) = false) ∧
    ¬ Catch sharpWhite8Strip 0 9 14 ∧
    (∀ i t, sharpBlack7Strip (i + 2) (t + 1) =
      xor (sharpBlack7Strip i t) (sharpBlack7Strip (i + 1) t || sharpBlack7Strip (i + 2) t)) ∧
    PrefixClocks sharpBlack7Strip ∧ White sharpBlack7Strip 0 ∧
    (∀ t, sharpBlack7Strip 1 (t + 16) = !(sharpBlack7Strip 1 t)) ∧
    (∀ u, u < 7 → sharpBlack7Strip 1 (25 + u) = true) ∧
    ¬ Catch sharpBlack7Strip 0 8 31 := by
  have hspW := maskStrip_spec (L0 := 32) (m0 := 0) (m1 := antiMask32 0x007c) (by decide)
  have hspB := maskStrip_spec (L0 := 32) (m0 := 0) (m1 := antiMask32 0x0164) (by decide)
  have hclW : PrefixClocks sharpWhite8Strip := fun m => by
    refine ⟨maskPeriod 32 0 (antiMask32 0x007c) m, (hspW m).1, fun i hi t _ => ?_⟩
    obtain ⟨c, hc⟩ := (hspW m).2.2.1 i hi
    rw [hc, Nat.mul_comm]; exact period_mul_add _ (hspW i).2.1 c t
  have hclB : PrefixClocks sharpBlack7Strip := fun m => by
    refine ⟨maskPeriod 32 0 (antiMask32 0x0164) m, (hspB m).1, fun i hi t _ => ?_⟩
    obtain ⟨c, hc⟩ := (hspB m).2.2.1 i hi
    rw [hc, Nat.mul_comm]; exact period_mul_add _ (hspB i).2.1 c t
  have hw8 : ∀ u, u < 8 → sharpWhite8Strip 1 (7 + u) = false := by
    have hchk : ((List.range 8).all (fun u => !(sharpWhite8Strip 1 (7 + u)))) = true := by decide +kernel
    intro u hu; simpa using List.all_eq_true.mp hchk u (List.mem_range.mpr hu)
  have hb7 : ∀ u, u < 7 → sharpBlack7Strip 1 (25 + u) = true := by
    have hchk : ((List.range 7).all (fun u => sharpBlack7Strip 1 (25 + u))) = true := by decide +kernel
    intro u hu; exact List.all_eq_true.mp hchk u (List.mem_range.mpr hu)
  have hncW : catchBool sharpWhite8Strip 9 14 = false := by decide +kernel
  have hncB : catchBool sharpBlack7Strip 8 31 = false := by decide +kernel
  exact ⟨fun i t => (hspW i).2.2.2 t, hclW, fun t => Nat.zero_testBit _,
         fun t => antiMask32_flip 0x007c t, hw8, not_catch_of_catchBool_false hncW,
         fun i t => (hspB i).2.2.2 t, hclB, fun t => Nat.zero_testBit _,
         fun t => antiMask32_flip 0x0164 t, hb7, not_catch_of_catchBool_false hncB⟩

end Ruliology.CellularAutomata.Rule30FirstLossBounds
