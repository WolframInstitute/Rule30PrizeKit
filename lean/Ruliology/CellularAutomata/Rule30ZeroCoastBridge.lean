module

public import Ruliology.CellularAutomata.Rule30Prize
public import Ruliology.CellularAutomata.Rule30SpacingRenormalization
public import Ruliology.CellularAutomata.Rule30ZeroBoundary
public import Ruliology.CellularAutomata.Rule30GateTrap
public import Ruliology.CellularAutomata.Rule30PeriodTwo
public import Ruliology.CellularAutomata.Rule30PeriodTwoSideways
public import Ruliology.CellularAutomata.Rule30GateTrapLift
public import Ruliology.CellularAutomata.Rule30PeriodTwoWidth13

/-!
# Zero-Coast Physical Transition, Mass Divergence, and Equivalence with `Rule30GateTrap.Q01Gap`

This module extracts the universally quantified structural transition framework and gap-equivalence
theorems from Rule 30 Prize submission
[`R30-20261115-fdf6a3`](https://www.wolframcloud.com/obj/rule-30-prize/Agents/status/R30-20261115-fdf6a3)
in plain Lean 4.35.0 without Mathlib (leaving fixed-parameter stratum searches and finite
counterexamples with the submission).

Under the zero-boundary integer map `Rule30ZeroBoundary.IntegerForm.F`, a finite seed `y : Nat`
survives to horizon `H` (`SurvivesTo y H`) when its center-column prefix matches an admissible
`B35` reset-gate clock (`gateNext` with `age ∈ {0,1,2,3,4}`, reset periods `6` and `10`).

Main structural definitions and results:

* **Zero-coast physical transition (`PhysState`, `zeroNext`, `iterZeroNext`):**
  Every reachable finite antidiagonal state determines the next zero-bit emission uniquely via
  `piParity (physSigma s)` (`zeroNext_spec_of_match`, `iterZeroNext_isSome_iff_survives`,
  `physReachable_iff_exists_seed`).
* **Mass divergence and uniform box termination:**
  With `NoMass M H := ∀ y, popcount y ≤ M → ¬ SurvivesTo y H` and
  `MassDiverges := ∀ M, ∃ H, NoMass M H`, we prove the exact equivalences
  `massDiverges_iff_uniform_noMass_step` (`MassDiverges ↔ UniformNoMassStep`),
  `massDiverges_iff_zeroCoastBoxTermination` (`MassDiverges ↔ ZeroCoastBoxTerminationHypothesis`),
  and `finite_seeds_terminate_iff_mass_diverges` (`FiniteSeedsTerminate ↔ MassDiverges`).
* **Bridge to `Rule30GateTrap.Q01Gap` and `Rule30PeriodTwoSideways.CQ01Empty`:**
  `massDiverges_iff_Q01Gap` proves the unconditional equivalence
  `MassDiverges ↔ Rule30GateTrap.Q01Gap`, yielding `massDiverges_of_Q01` from
  `Rule30ZeroBoundary.Q01` and `CQ01Empty_of_massDiverges` via
  `Rule30GateTrap.CQ01Empty_of_Q01Gap`.

All global conjectures (`Q01`, `Q01Gap`, `CQ01`, `CQ01Empty`, `MassDiverges`,
`UniformNoMassStep`, `ZeroCoastBoxTerminationHypothesis`, `FiniteSeedsTerminate`) remain **open**
and are never assumed unconditionally.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30ZeroCoastBridge

open Rule30SpacingRenormalization
open Rule30ZeroBoundary
open Rule30ZeroBoundary.IntegerForm

def trace : Nat → Nat → List Bool
  | _, 0 => []
  | y, H + 1 => y.testBit 0 :: trace (F y) H

def gateNext (a : Nat) (g : Bool) : Option Nat :=
  match a, g with
  | 0, false => some 1
  | 1, false => some 2
  | 2, false => some 3
  | 2, true  => some 0
  | 3, false => some 4
  | 4, true  => some 0
  | _, _     => none

def nextAge (isOdd : Bool) (age : Nat) (b : Bool) : Option Nat :=
  if isOdd then (if b then some age else none)
  else gateNext age (!b)

def acceptRest : Bool → Nat → List Bool → Bool
  | _, _, [] => true
  | true, a, b :: rest => b && acceptRest false a rest
  | false, a, b :: rest =>
    match gateNext a (!b) with
    | none => false
    | some a' => acceptRest true a' rest

def accept : List Bool → Bool
  | [] => true
  | b :: rest => (!b) && acceptRest true 0 rest

def SurvivesTo (y H : Nat) : Prop :=
  accept (trace y H) = true

instance (y H : Nat) : Decidable (SurvivesTo y H) :=
  inferInstanceAs (Decidable (accept (trace y H) = true))

theorem iter_succ_apply (t y : Nat) : iter F (t + 1) y = iter F t (F y) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change F (iter F (t + 1) y) = F (iter F t (F y))
    rw [ih]

theorem iter_pred_succ_apply (t y : Nat) (ht : 1 ≤ t) :
    iter F (t - 1) (F y) = iter F t y := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  exact (iter_succ_apply k y).symm

theorem trace_length (y H : Nat) : (trace y H).length = H := by
  induction H generalizing y with
  | zero => rfl
  | succ H ih => simp [trace, ih]

theorem trace_getElem (y H t : Nat) (ht : t < H) :
    (trace y H)[t]'(by rw [trace_length]; exact ht) = (iter F t y).testBit 0 := by
  induction H generalizing y t with
  | zero => omega
  | succ H ih =>
    cases t with
    | zero => rfl
    | succ t =>
      change (trace (F y) H)[t]'(by rw [trace_length]; omega) = (iter F (t + 1) y).testBit 0
      rw [ih (F y) t (by omega), iter_succ_apply]

theorem trace_succ_right (y n : Nat) :
    trace y (n + 1) = trace y n ++ [(iter F n y).testBit 0] := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih =>
    change y.testBit 0 :: trace (F y) (n + 1) =
      (y.testBit 0 :: trace (F y) n) ++ [(iter F (n + 1) y).testBit 0]
    rw [ih (F y), iter_succ_apply]
    rfl

theorem trace_succ_pred (y m : Nat) (hm : 1 ≤ m) :
    trace y m = trace y (m - 1) ++ [(iter F (m - 1) y).testBit 0] := by
  obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  subst hk
  exact trace_succ_right y k

theorem trace_cons_pred (y m : Nat) (hm : 1 ≤ m) :
    trace y m = y.testBit 0 :: trace (F y) (m - 1) := by
  obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  subst hk
  rfl

theorem trace_take (y H1 H2 : Nat) (h : H1 ≤ H2) :
    (trace y H2).take H1 = trace y H1 := by
  induction H1 generalizing y H2 with
  | zero => simp [trace]
  | succ H1 ih =>
    cases H2 with
    | zero => omega
    | succ H2 =>
      simp [trace, ih (F y) H2 (by omega)]

theorem acceptRest_append_left (flag : Bool) (a : Nat) (w1 w2 : List Bool) :
    acceptRest flag a (w1 ++ w2) = true → acceptRest flag a w1 = true := by
  induction w1 generalizing flag a with
  | nil => intro _; simp [acceptRest]
  | cons b rest ih =>
    intro h
    cases flag with
    | true =>
      simp only [List.cons_append, acceptRest, Bool.and_eq_true] at h ⊢
      exact ⟨h.1, ih false a h.2⟩
    | false =>
      simp only [List.cons_append, acceptRest] at h ⊢
      cases hg : gateNext a (!b) with
      | none => simp [hg] at h
      | some a' =>
        simp [hg] at h
        exact ih true a' h

theorem accept_append_left (w1 w2 : List Bool) :
    accept (w1 ++ w2) = true → accept w1 = true := by
  cases w1 with
  | nil => intro _; rfl
  | cons b rest =>
    intro h
    simp only [List.cons_append, accept, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, acceptRest_append_left true 0 rest w2 h.2⟩

theorem survivesTo_mono {y H1 H2 : Nat} (hle : H1 ≤ H2) (h : SurvivesTo y H2) :
    SurvivesTo y H1 := by
  unfold SurvivesTo at h ⊢
  have htake := trace_take y H1 H2 hle
  rw [← List.take_append_drop H1 (trace y H2), htake] at h
  exact accept_append_left (trace y H1) ((trace y H2).drop H1) h

def popcountAux : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n = 0 then 0 else n % 2 + popcountAux fuel (n / 2)

def popcount (n : Nat) : Nat :=
  popcountAux n n

private theorem popcountAux_extra (n fuel1 fuel2 : Nat) (h1 : n ≤ fuel1) (h2 : n ≤ fuel2) :
    popcountAux fuel1 n = popcountAux fuel2 n := by
  induction fuel1 generalizing n fuel2 with
  | zero =>
    have hn : n = 0 := by omega
    subst hn
    cases fuel2 <;> rfl
  | succ f1 ih =>
    cases fuel2 with
    | zero =>
      have hn : n = 0 := by omega
      subst hn; rfl
    | succ f2 =>
      simp only [popcountAux]
      by_cases hn : n = 0
      · simp [hn]
      · simp only [hn, ↓reduceIte]
        have hd1 : n / 2 ≤ f1 := by omega
        have hd2 : n / 2 ≤ f2 := by omega
        rw [ih (n / 2) f2 hd1 hd2]

theorem popcount_zero : popcount 0 = 0 := rfl

theorem popcount_step {n : Nat} (hn : n ≠ 0) :
    popcount n = n % 2 + popcount (n / 2) := by
  unfold popcount
  obtain ⟨f, hf⟩ : ∃ f, n = f + 1 := ⟨n - 1, by omega⟩
  have hstep : popcountAux (f + 1) n = n % 2 + popcountAux f (n / 2) := by
    simp [popcountAux, hn]
  have heq1 : popcountAux n n = popcountAux (f + 1) n := by rw [hf]
  have heq2 : popcountAux f (n / 2) = popcountAux (n / 2) (n / 2) :=
    popcountAux_extra (n / 2) f (n / 2) (by omega) (Nat.le_refl _)
  rw [heq1, hstep, heq2]

theorem popcount_eq_zero_iff (n : Nat) : popcount n = 0 ↔ n = 0 := by
  constructor
  · intro h
    induction n using Nat.strongRecOn with
    | ind n ih =>
      by_cases hn : n = 0
      · exact hn
      · rw [popcount_step hn] at h
        have hm0 : n % 2 = 0 := by omega
        have hd0 : popcount (n / 2) = 0 := by omega
        have hlt : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)
        have hdiv : n / 2 = 0 := ih (n / 2) hlt hd0
        omega
  · rintro rfl; exact popcount_zero

theorem popcount_pos {n : Nat} (hn : 0 < n) : 0 < popcount n := by
  cases hp : popcount n with
  | zero =>
    have h0 : n = 0 := (popcount_eq_zero_iff n).mp hp
    omega
  | succ k => exact Nat.succ_pos k

private theorem mod_pow2_succ (n k : Nat) :
    n % 2 ^ (k + 1) = n % 2 + 2 * ((n / 2) % 2 ^ k) := by
  have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
  have hlt1 : n % 2 + 2 * ((n / 2) % 2 ^ k) < 2 ^ (k + 1) := by
    have ha : n % 2 < 2 := Nat.mod_lt _ (by decide)
    have hb : (n / 2) % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.pow_pos (by decide))
    rw [hpow]; omega
  have hdecomp : n = 2 ^ (k + 1) * ((n / 2) / 2 ^ k) + (n % 2 + 2 * ((n / 2) % 2 ^ k)) := by
    have h1 : n = 2 * (n / 2) + n % 2 := by omega
    have h2 : n / 2 = 2 ^ k * ((n / 2) / 2 ^ k) + (n / 2) % 2 ^ k := (Nat.div_add_mod _ _).symm
    rw [hpow]
    rw [h2] at h1
    rw [Nat.mul_add, ← Nat.mul_assoc] at h1
    omega
  calc n % 2 ^ (k + 1)
      = (2 ^ (k + 1) * ((n / 2) / 2 ^ k) + (n % 2 + 2 * ((n / 2) % 2 ^ k))) % 2 ^ (k + 1) := by
          rw [← hdecomp]
    _ = n % 2 + 2 * ((n / 2) % 2 ^ k) := by
          rw [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hlt1]

private theorem div_pow2_succ (n k : Nat) :
    n / 2 ^ (k + 1) = (n / 2) / 2 ^ k := by
  have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
  rw [hpow, Nat.div_div_eq_div_mul, Nat.mul_comm]

theorem popcount_mod_add_div (k n : Nat) :
    popcount n = popcount (n % 2 ^ k) + popcount (n / 2 ^ k) := by
  induction k generalizing n with
  | zero => simp [Nat.mod_one, popcount_zero]
  | succ k ih =>
    by_cases hn : n = 0
    · subst hn; simp [popcount_zero]
    · have hmod := mod_pow2_succ n k
      have hdiv := div_pow2_succ n k
      have hm_div : (n % 2 ^ (k + 1)) / 2 = (n / 2) % 2 ^ k := by
        rw [hmod]
        have : n % 2 < 2 := Nat.mod_lt _ (by decide)
        omega
      have hm_mod : (n % 2 ^ (k + 1)) % 2 = n % 2 := by
        rw [hmod]; omega
      rw [popcount_step hn, ih (n / 2), hdiv]
      by_cases hm : n % 2 ^ (k + 1) = 0
      · rw [hm, popcount_zero]
        have h1 : (n / 2) % 2 ^ k = 0 := by omega
        have h2 : n % 2 = 0 := by omega
        rw [h1, h2, popcount_zero]; omega
      · rw [popcount_step hm, hm_mod, hm_div]; omega

theorem popcount_mod_pow2_le (n k : Nat) : popcount (n % 2 ^ k) ≤ popcount n := by
  rw [popcount_mod_add_div k n]
  exact Nat.le_add_right _ _

theorem popcount_mod_pow2_lt {n k : Nat} (hle : 2 ^ k ≤ n) :
    popcount (n % 2 ^ k) < popcount n := by
  rw [popcount_mod_add_div k n]
  have hdiv_pos : 0 < n / 2 ^ k := Nat.div_pos hle (Nat.pow_pos (by decide))
  have hpc_pos : 0 < popcount (n / 2 ^ k) := popcount_pos hdiv_pos
  omega

theorem popcount_mod_pow2_succ (y k : Nat) :
    popcount (y % 2 ^ (k + 1)) = popcount (y % 2 ^ k) + (if y.testBit k then 1 else 0) := by
  have hpow : 2 ^ (k + 1) = 2 ^ k * 2 := by rw [Nat.pow_succ]
  have hdiv2 : y / 2 ^ (k + 1) = (y / 2 ^ k) / 2 ^ 1 := by
    rw [hpow, Nat.div_div_eq_div_mul, Nat.pow_one]
  have h1 := popcount_mod_add_div (k + 1) y
  rw [hdiv2] at h1
  have h2 := popcount_mod_add_div k y
  have hdiv_step := popcount_mod_add_div 1 (y / 2 ^ k)
  have h01 : (y / 2 ^ k) % 2 = 0 ∨ (y / 2 ^ k) % 2 = 1 := by omega
  have hb : y.testBit k = decide ((y / 2 ^ k) % 2 = 1) := by
    rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.and_comm, Nat.and_one_is_mod]
    rcases h01 with h | h <;> simp [h]
  have hpc01 : popcount ((y / 2 ^ k) % 2 ^ 1) = if y.testBit k then 1 else 0 := by
    rw [hb]
    rcases h01 with h | h <;> simp [Nat.pow_one, h] <;> decide
  omega

theorem F_testBit (y j : Nat) :
    (F y).testBit j =
      xor (y.testBit (j + 1))
          (y.testBit j || (if j = 0 then false else y.testBit (j - 1))) := by
  unfold F
  simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_shiftLeft]
  cases j with
  | zero => simp
  | succ j => simp [Nat.add_comm]

theorem F_mod_pow2 (y k : Nat) :
    (F y) % 2 ^ k = (F (y % 2 ^ (k + 1))) % 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_mod_two_pow]
  by_cases hj : j < k
  · simp only [hj, decide_true, Bool.true_and]
    rw [F_testBit, F_testBit]
    have h1 : (y % 2 ^ (k + 1)).testBit (j + 1) = y.testBit (j + 1) := by
      rw [Nat.testBit_mod_two_pow]; simp [show j + 1 < k + 1 by omega]
    have h0 : (y % 2 ^ (k + 1)).testBit j = y.testBit j := by
      rw [Nat.testBit_mod_two_pow]; simp [show j < k + 1 by omega]
    have hm : (if j = 0 then false else (y % 2 ^ (k + 1)).testBit (j - 1)) =
              (if j = 0 then false else y.testBit (j - 1)) := by
      cases j with
      | zero => rfl
      | succ j' =>
        simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
        rw [Nat.testBit_mod_two_pow]
        simp [show j' < k + 1 by omega]
    rw [h1, h0, hm]
  · simp [hj]

theorem iter_F_mod_pow2 (t y k : Nat) :
    (iter F t y) % 2 ^ k = (iter F t (y % 2 ^ (k + t))) % 2 ^ k := by
  induction t generalizing y k with
  | zero => simp [iter]
  | succ t ih =>
    rw [iter_succ_apply, iter_succ_apply]
    have h1 := ih (F y) k
    have h2 := ih (F (y % 2 ^ (k + (t + 1)))) k
    have hmod : (F y) % 2 ^ (k + t) = (F (y % 2 ^ (k + (t + 1)))) % 2 ^ (k + t) := by
      rw [show k + (t + 1) = (k + t) + 1 by omega]
      exact F_mod_pow2 y (k + t)
    rw [h1, hmod, ← h2]

theorem trace_mod_pow2 (y H : Nat) : trace (y % 2 ^ H) H = trace y H := by
  apply List.ext_getElem
  · simp [trace_length]
  · intro i hi1 _
    rw [trace_length] at hi1
    rw [trace_getElem (y % 2 ^ H) H i hi1, trace_getElem y H i hi1]
    have hpow : 1 + i ≤ H := by omega
    have htest : ∀ a b, a % 2 ^ 1 = b % 2 ^ 1 → a.testBit 0 = b.testBit 0 := by
      intro a b hab
      have ha : a.testBit 0 = ((a % 2 ^ 1).testBit 0) := by
        rw [Nat.testBit_mod_two_pow]; simp
      have hb : b.testBit 0 = ((b % 2 ^ 1).testBit 0) := by
        rw [Nat.testBit_mod_two_pow]; simp
      rw [ha, hb, hab]
    apply htest
    have hm := congrArg (fun z => (iter F i z) % 2 ^ 1)
      (show (y % 2 ^ H) % 2 ^ (1 + i) = y % 2 ^ (1 + i) by
        rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hpow)])
    rw [← iter_F_mod_pow2 i (y % 2 ^ H) 1, ← iter_F_mod_pow2 i y 1] at hm
    exact hm

theorem survivesTo_mod_pow2 (y H : Nat) :
    SurvivesTo (y % 2 ^ H) H ↔ SurvivesTo y H := by
  unfold SurvivesTo
  rw [trace_mod_pow2]

def sigmaList : List Bool → List Bool → List Bool
  | [], _ => []
  | x :: xs, [] => x :: sigmaList xs []
  | x :: xs, y :: ys => (x || y) :: sigmaList xs ys

def scanXor (acc : Bool) : List Bool → List Bool × Bool
  | [] => ([], acc)
  | s :: sig =>
    let next := xor acc s
    let r := scanXor next sig
    (next :: r.1, r.2)

def antidiag (y k : Nat) : List Bool :=
  (List.range (k + 1)).map (fun j => (iter F (k - j) y).testBit j)

theorem antidiag_length (y k : Nat) : (antidiag y k).length = k + 1 := by
  simp [antidiag]

theorem sigmaList_eq_map (f g : Nat → Bool) : ∀ m : Nat,
    sigmaList ((List.range m).map f) ((List.range m).map g) =
      (List.range m).map (fun j => f j || g j)
  | 0 => rfl
  | m + 1 => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_cons, List.map_cons,
      List.map_map, List.map_map, List.map_map, sigmaList]
    exact congrArg ((f 0 || g 0) :: ·) (sigmaList_eq_map (fun j => f (j + 1)) (fun j => g (j + 1)) m)

theorem scanXor_telescope_map (f : Nat → Bool) : ∀ m : Nat,
    scanXor (f 0) ((List.range m).map (fun j => xor (f j) (f (j + 1)))) =
      ((List.range m).map (fun j => f (j + 1)), f m)
  | 0 => rfl
  | m + 1 => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [scanXor, List.map_cons]
    have hxor : xor (f 0) (xor (f 0) (f 1)) = f 1 := by
      cases f 0 <;> cases f 1 <;> rfl
    rw [hxor]
    have ih := scanXor_telescope_map (fun j => f (j + 1)) m
    have hfn : ((fun j => xor (f j) (f (j + 1))) ∘ Nat.succ) =
        (fun j => xor (f (j + 1)) (f (j + 1 + 1))) := rfl
    rw [hfn, ih, List.map_map]
    rfl

theorem antidiag_step_spec (y n : Nat) (hn : 1 ≤ n) :
    let r := scanXor ((iter F n y).testBit 0)
      (sigmaList (antidiag y (n - 1)) (false :: (if n = 1 then [] else antidiag y (n - 2))))
    (iter F n y).testBit 0 :: r.1 = antidiag y n ∧ r.2 = y.testBit n := by
  let f : Nat → Bool := fun j => (iter F (n - j) y).testBit j
  have hd1 : antidiag y (n - 1) = (List.range n).map (fun j => (iter F (n - 1 - j) y).testBit j) := by
    unfold antidiag
    rw [show n - 1 + 1 = n by omega]
  have hd2 : (false :: (if n = 1 then [] else antidiag y (n - 2))) =
      (List.range n).map (fun j => if j = 0 then false else (iter F (n - 1 - j) y).testBit (j - 1)) := by
    apply List.ext_getElem
    · by_cases h1 : n = 1
      · subst h1; simp
      · simp [h1, antidiag]; omega
    · intro j hj1 hj2
      simp only [List.getElem_map, List.getElem_range]
      cases j with
      | zero => rfl
      | succ j =>
        have hne : n ≠ 1 := by simp only [List.length_map, List.length_range] at hj2; omega
        simp only [hne, ↓reduceIte, List.getElem_cons_succ, Nat.succ_ne_zero]
        unfold antidiag
        simp only [List.getElem_map, List.getElem_range, Nat.add_sub_cancel]
        congr 2; omega
  have hsig : sigmaList (antidiag y (n - 1)) (false :: (if n = 1 then [] else antidiag y (n - 2))) =
      (List.range n).map (fun j => xor (f j) (f (j + 1))) := by
    rw [hd1, hd2, sigmaList_eq_map]
    refine List.map_congr_left fun j hj => ?_
    rw [List.mem_range] at hj
    dsimp only [f]
    have hsplit : n - j = (n - 1 - j) + 1 := by omega
    have hpow2 : n - (j + 1) = n - 1 - j := by omega
    rw [hsplit, hpow2]
    change _ = xor ((F (iter F (n - 1 - j) y)).testBit j) ((iter F (n - 1 - j) y).testBit (j + 1))
    rw [F_testBit]
    generalize (iter F (n - 1 - j) y).testBit (j + 1) = a
    generalize ((iter F (n - 1 - j) y).testBit j || if j = 0 then false else (iter F (n - 1 - j) y).testBit (j - 1)) = c
    cases a <;> cases c <;> rfl
  dsimp only
  rw [hsig]
  have hb0 : (iter F n y).testBit 0 = f 0 := by simp [f]
  change (iter F n y).testBit 0 :: (scanXor ((iter F n y).testBit 0) _).1 = antidiag y n ∧
    (scanXor ((iter F n y).testBit 0) _).2 = y.testBit n
  rw [hb0, scanXor_telescope_map f n]
  constructor
  · unfold antidiag
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    change f 0 :: List.map (fun x => f (x + 1)) (List.range n) =
      (iter F n y).testBit 0 :: List.map (fun x => (iter F (n - (x + 1)) y).testBit (x + 1)) (List.range n)
    rw [← hb0]
  · simp [f, iter]

/-! ## 2. Parity Sum `Π(σ)`, Physical State `PhysState`, and Partial Zero-Coast Transition `zeroNext` -/

def piParity : List Bool → Bool
  | [] => false
  | s :: sig => xor s (piParity sig)

theorem scanXor_snd_eq_xor_piParity (b : Bool) (sig : List Bool) :
    (scanXor b sig).2 = xor b (piParity sig) := by
  induction sig generalizing b with
  | nil => simp [scanXor, piParity]
  | cons s sig ih =>
    simp only [scanXor, piParity]
    rw [ih (xor b s)]
    cases b <;> cases s <;> cases piParity sig <;> rfl

theorem scanXor_snd_eq_false_iff (b : Bool) (sig : List Bool) :
    (scanXor b sig).2 = false ↔ b = piParity sig := by
  rw [scanXor_snd_eq_xor_piParity]
  cases b <;> cases piParity sig <;> decide

structure PhysState where
  n : Nat
  isOdd : Bool
  age : Nat
  d1 : List Bool
  d2 : List Bool
  deriving DecidableEq, Repr

def initPhysState : PhysState :=
  { n := 1, isOdd := true, age := 0, d1 := [false], d2 := [] }

def physSigma (s : PhysState) : List Bool :=
  sigmaList s.d1 (false :: s.d2)

def physStep (s : PhysState) (b : Bool) : Option (PhysState × Bool) :=
  match nextAge s.isOdd s.age b with
  | none => none
  | some na =>
    let r := scanXor b (physSigma s)
    some ({ n := s.n + 1, isOdd := !s.isOdd, age := na, d1 := b :: r.1, d2 := s.d1 }, r.2)

def zeroNext (s : PhysState) : Option PhysState :=
  let b := piParity (physSigma s)
  match nextAge s.isOdd s.age b with
  | none => none
  | some na =>
    let r := scanXor b (physSigma s)
    some { n := s.n + 1, isOdd := !s.isOdd, age := na, d1 := b :: r.1, d2 := s.d1 }

def iterZeroNext : PhysState → Nat → Option PhysState
  | s, 0 => some s
  | s, L + 1 =>
    match zeroNext s with
    | none => none
    | some s' => iterZeroNext s' L

theorem zeroNext_eq_physStep_zero (s s' : PhysState) :
    zeroNext s = some s' ↔ physStep s (piParity (physSigma s)) = some (s', false) := by
  unfold zeroNext physStep
  cases hna : nextAge s.isOdd s.age (piParity (physSigma s)) with
  | none => simp [hna]
  | some na =>
    have hsnd : (scanXor (piParity (physSigma s)) (physSigma s)).2 = false :=
      (scanXor_snd_eq_false_iff _ _).mpr rfl
    simp [hna, hsnd]

theorem physStep_zeroSeed_iff (s s' : PhysState) (b : Bool) :
    physStep s b = some (s', false) ↔ b = piParity (physSigma s) ∧ zeroNext s = some s' := by
  constructor
  · intro h
    unfold physStep at h
    cases hna : nextAge s.isOdd s.age b with
    | none => simp [hna] at h
    | some na =>
      simp only [hna, Option.some.injEq, Prod.mk.injEq] at h
      have hb : b = piParity (physSigma s) := (scanXor_snd_eq_false_iff b (physSigma s)).mp h.2
      refine ⟨hb, ?_⟩
      apply (zeroNext_eq_physStep_zero s s').mpr
      unfold physStep
      subst hb
      simp [hna, h.1, h.2]
  · rintro ⟨rfl, hz⟩
    exact (zeroNext_eq_physStep_zero s s').mp hz

/-! ## 3. Gate Trace Automata State, Explicit Reachability, and Seed Realization -/

def acceptFinal : Bool → Nat → List Bool → Option (Bool × Nat)
  | isOdd, age, [] => some (isOdd, age)
  | isOdd, age, b :: rest =>
    match nextAge isOdd age b with
    | none => none
    | some na => acceptFinal (!isOdd) na rest

theorem acceptFinal_append (isOdd : Bool) (age : Nat) (w1 w2 : List Bool) :
    acceptFinal isOdd age (w1 ++ w2) =
      match acceptFinal isOdd age w1 with
      | none => none
      | some (o', a') => acceptFinal o' a' w2 := by
  induction w1 generalizing isOdd age with
  | nil => rfl
  | cons b w1 ih =>
    simp only [List.cons_append, acceptFinal]
    cases h : nextAge isOdd age b with
    | none => rfl
    | some na => exact ih (!isOdd) na

theorem acceptFinal_isSome_eq_acceptRest (isOdd : Bool) (age : Nat) (w : List Bool) :
    (acceptFinal isOdd age w).isSome = acceptRest isOdd age w := by
  induction w generalizing isOdd age with
  | nil => rfl
  | cons b w ih =>
    cases isOdd with
    | false =>
      simp only [acceptFinal, nextAge, Bool.false_eq_true, ↓reduceIte, acceptRest]
      cases gateNext age (!b) with
      | none => rfl
      | some a' => exact ih true a'
    | true =>
      simp only [acceptFinal, nextAge, ↓reduceIte, acceptRest]
      cases b with
      | false => rfl
      | true => exact ih false age

theorem acceptFinal_parity (isOdd : Bool) (age : Nat) (w : List Bool) (o' : Bool) (a' : Nat) :
    acceptFinal isOdd age w = some (o', a') →
      o' = if w.length % 2 = 0 then isOdd else !isOdd := by
  induction w generalizing isOdd age with
  | nil =>
    intro h
    simp only [acceptFinal, Option.some.injEq, Prod.mk.injEq] at h
    simp [h.1]
  | cons b w ih =>
    intro h
    simp only [acceptFinal] at h
    cases hna : nextAge isOdd age b with
    | none => simp [hna] at h
    | some na =>
      rw [hna] at h
      have hrec := ih (!isOdd) na h
      rw [hrec]
      rcases Nat.mod_two_eq_zero_or_one w.length with hw | hw
      · simp [List.length_cons, Nat.add_mod, hw]
      · simp [List.length_cons, Nat.add_mod, hw]

theorem acceptFinal_trace_parity (y n : Nat) (hn : 1 ≤ n) (o' : Bool) (a' : Nat)
    (h : acceptFinal true 0 (trace (F y) (n - 1)) = some (o', a')) :
    o' = decide (n % 2 = 1) := by
  have hp := acceptFinal_parity true 0 (trace (F y) (n - 1)) o' a' h
  rw [trace_length] at hp
  rcases Nat.mod_two_eq_zero_or_one n with hm | hm
  · have hm1 : (n - 1) % 2 = 1 := by omega
    simp [hp, hm, hm1]
  · have hm1 : (n - 1) % 2 = 0 := by omega
    simp [hp, hm, hm1]

def StateMatchesSeed (y : Nat) (s : PhysState) : Prop :=
  1 ≤ s.n ∧
  s.isOdd = decide (s.n % 2 = 1) ∧
  y.testBit 0 = false ∧
  acceptFinal true 0 (trace (F y) (s.n - 1)) = some (s.isOdd, s.age) ∧
  s.d1 = antidiag y (s.n - 1) ∧
  s.d2 = (if s.n = 1 then [] else antidiag y (s.n - 2))

inductive PhysReachable : PhysState → Prop
  | init : PhysReachable initPhysState
  | step {s s' : PhysState} {b bit : Bool} :
      PhysReachable s → physStep s b = some (s', bit) → PhysReachable s'

theorem stateMatchesSeed_survivesTo {y : Nat} {s : PhysState} (hm : StateMatchesSeed y s) :
    SurvivesTo y s.n := by
  obtain ⟨hn, _, hy0, hacc, _, _⟩ := hm
  obtain ⟨k, hk⟩ : ∃ k, s.n = k + 1 := ⟨s.n - 1, by omega⟩
  unfold SurvivesTo
  rw [hk, trace, accept, hy0]
  simp only [Bool.not_false, Bool.true_and]
  rw [← acceptFinal_isSome_eq_acceptRest]
  have hk' : s.n - 1 = k := by omega
  rw [← hk', hacc]
  rfl

theorem stateMatchesSeed_unique {y : Nat} {s1 s2 : PhysState}
    (hn : s1.n = s2.n) (h1 : StateMatchesSeed y s1) (h2 : StateMatchesSeed y s2) :
    s1 = s2 := by
  rcases s1 with ⟨n1, o1, a1, d11, d21⟩
  rcases s2 with ⟨n2, o2, a2, d12, d22⟩
  dsimp only at hn
  subst hn
  obtain ⟨_, ho1, _, ha1, hd11, hd21⟩ := h1
  obtain ⟨_, ho2, _, ha2, hd12, hd22⟩ := h2
  have ho : o1 = o2 := ho1.trans ho2.symm
  subst ho
  have ha : a1 = a2 := by
    have heq := ha1.symm.trans ha2
    simp only [Option.some.injEq, Prod.mk.injEq] at heq
    exact heq.2
  have hd1 : d11 = d12 := hd11.trans hd12.symm
  have hd2 : d21 = d22 := hd21.trans hd22.symm
  subst ha hd1 hd2
  rfl

theorem physStep_n_eq {s s' : PhysState} {b bit : Bool} (h : physStep s b = some (s', bit)) :
    s'.n = s.n + 1 := by
  unfold physStep at h
  cases hna : nextAge s.isOdd s.age b with
  | none => simp [hna] at h
  | some na =>
    simp only [hna, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]

theorem stateMatchesSeed_n1 {y : Nat} {s : PhysState} (h1 : s.n = 1) (hm : StateMatchesSeed y s) :
    s = initPhysState := by
  obtain ⟨_, ho, hy0, hacc, hd1, hd2⟩ := hm
  rw [h1] at ho hacc hd1 hd2
  rcases s with ⟨sn, so, sa, sd1, sd2⟩
  dsimp only at h1 ho hacc hd1 hd2
  subst h1
  have ho1 : so = true := ho
  have ha0 : sa = 0 := by
    rw [show (1 - 1 : Nat) = 0 from rfl] at hacc
    simp only [trace, acceptFinal, Option.some.injEq, Prod.mk.injEq] at hacc
    exact hacc.2.symm
  have hd1' : sd1 = [false] := by
    simp [antidiag, iter, hy0] at hd1
    exact hd1
  have hd2' : sd2 = [] := by
    simp at hd2
    exact hd2
  subst ho1 ha0 hd1' hd2'
  rfl

theorem physStep_matches_of_seed {y : Nat} {s s' : PhysState} {b bit : Bool}
    (hmatch : StateMatchesSeed y s)
    (hstep : physStep s b = some (s', bit))
    (hb_eq : (iter F s.n y).testBit 0 = b) :
    StateMatchesSeed y s' := by
  obtain ⟨hn, ho, hy0, hacc, hd1, hd2⟩ := hmatch
  unfold physStep at hstep
  cases hna : nextAge s.isOdd s.age b with
  | none => simp [hna] at hstep
  | some na =>
    simp only [hna, Option.some.injEq, Prod.mk.injEq] at hstep
    obtain ⟨rfl, _⟩ := hstep
    have had := antidiag_step_spec y s.n hn
    dsimp only at had
    rw [hb_eq] at had
    have had_d1 : (b :: (scanXor b (physSigma s)).1) = antidiag y s.n := by
      unfold physSigma
      rw [hd1, hd2]
      exact had.1
    have htr : trace (F y) s.n = trace (F y) (s.n - 1) ++ [(iter F s.n y).testBit 0] := by
      rw [trace_succ_pred (F y) s.n hn, iter_pred_succ_apply s.n y hn]
    have hacc' : acceptFinal true 0 (trace (F y) s.n) = some (!s.isOdd, na) := by
      rw [htr, acceptFinal_append, hacc]
      simp only [acceptFinal]
      rw [hb_eq, hna]
    have ho' : (!s.isOdd) = decide ((s.n + 1) % 2 = 1) := by
      rw [ho, Nat.add_mod]
      rcases Nat.mod_two_eq_zero_or_one s.n with h0 | h0 <;> simp [h0]
    have hne : s.n + 1 ≠ 1 := by omega
    refine ⟨show 1 ≤ s.n + 1 by omega, ho', hy0, ?_, ?_, ?_⟩
    · simp only [Nat.add_sub_cancel]; exact hacc'
    · simp only [Nat.add_sub_cancel]; exact had_d1
    · change s.d1 = (if s.n + 1 = 1 then [] else antidiag y (s.n + 1 - 2))
      rw [ite_eq_right_iff.mpr (fun hc => absurd hc hne), hd1, show s.n + 1 - 2 = s.n - 1 by omega]

theorem physReachable_of_matches {n y : Nat} {s : PhysState} (hn_eq : s.n = n)
    (hm : StateMatchesSeed y s) : PhysReachable s := by
  induction n generalizing s with
  | zero =>
    obtain ⟨h1, _⟩ := hm
    omega
  | succ k ih =>
    by_cases hk0 : k = 0
    · have hk0' : s.n = 1 := by omega
      rw [stateMatchesSeed_n1 hk0' hm]
      exact PhysReachable.init
    · have hk1 : 1 ≤ k := by omega
      obtain ⟨hn, ho, hy0, hacc, hd1, hd2⟩ := hm
      have htr : trace (F y) k = trace (F y) (k - 1) ++ [(iter F k y).testBit 0] := by
        rw [trace_succ_pred (F y) k hk1, iter_pred_succ_apply k y hk1]
      have hk_sub : s.n - 1 = k := by omega
      rw [hk_sub, htr, acceptFinal_append] at hacc
      cases hprev : acceptFinal true 0 (trace (F y) (k - 1)) with
      | none => simp [hprev] at hacc
      | some pa =>
        rcases pa with ⟨oPrev, aPrev⟩
        rw [hprev] at hacc
        dsimp only [acceptFinal] at hacc
        have hoPrev : oPrev = decide (k % 2 = 1) :=
          acceptFinal_trace_parity y k hk1 oPrev aPrev hprev
        cases hna : nextAge oPrev aPrev ((iter F k y).testBit 0) with
        | none => rw [hna] at hacc; cases hacc
        | some na =>
          rw [hna] at hacc
          simp only [Option.some.injEq, Prod.mk.injEq] at hacc
          let sPrev : PhysState :=
            { n := k
              isOdd := oPrev
              age := aPrev
              d1 := antidiag y (k - 1)
              d2 := if k = 1 then [] else antidiag y (k - 2) }
          have hmPrev : StateMatchesSeed y sPrev :=
            ⟨hk1, hoPrev, hy0, hprev, rfl, rfl⟩
          have hrPrev : PhysReachable sPrev := ih rfl hmPrev
          have hstep : physStep sPrev ((iter F k y).testBit 0) =
              some (s, (scanXor ((iter F k y).testBit 0) (physSigma sPrev)).2) := by
            unfold physStep
            dsimp only [sPrev]
            rw [hna]
            simp only [Option.some.injEq, Prod.mk.injEq]
            refine ⟨?_, trivial⟩
            have had := antidiag_step_spec y k hk1
            dsimp only at had
            have hd1_eq : (iter F k y).testBit 0 :: (scanXor ((iter F k y).testBit 0) (physSigma sPrev)).1 = s.d1 := by
              rw [hd1, hk_sub]
              exact had.1
            have hd2_eq : sPrev.d1 = s.d2 := by
              rw [hd2, show (if s.n = 1 then [] else antidiag y (s.n - 2)) = antidiag y (k - 1) by
                have hsne : s.n ≠ 1 := by omega
                simp [hsne, show s.n - 2 = k - 1 by omega]]
            rcases s with ⟨sn, so, sa, sd1, sd2⟩
            dsimp only at hn_eq hacc hd1_eq hd2_eq
            have h1 : k + 1 = sn := by omega
            have h2 : (!oPrev) = so := hacc.1
            have h3 : na = sa := hacc.2
            subst h1 h2 h3 hd1_eq hd2_eq
            rfl
          exact PhysReachable.step hrPrev hstep

theorem exists_seed_of_physReachable {s : PhysState} (hr : PhysReachable s) :
    ∃ y : Nat, y < 2 ^ s.n ∧ StateMatchesSeed y s := by
  induction hr with
  | init =>
    refine ⟨0, by decide, ?_⟩
    exact ⟨by decide, by decide, by decide, by simp [initPhysState, trace, acceptFinal],
      by simp [initPhysState, antidiag, iter], rfl⟩
  | @step s s' b bit hr hstep ih =>
    obtain ⟨y, hyPow, hn, ho, hy0, hacc, hd1, hd2⟩ := ih
    let y' : Nat := y + (if bit then 2 ^ s.n else 0)
    have hy'Lt : y' < 2 ^ (s.n + 1) := by
      have hpow : 2 ^ (s.n + 1) = 2 ^ s.n + 2 ^ s.n := by rw [Nat.pow_succ]; omega
      dsimp only [y']
      cases bit <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
    have hy'Mod : y' % 2 ^ s.n = y := by
      dsimp only [y']
      cases bit
      · simpa using Nat.mod_eq_of_lt hyPow
      · simp [Nat.mod_eq_of_lt hyPow]
    have hy'BitN : y'.testBit s.n = bit := by
      dsimp only [y']
      rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
      cases bit
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        rw [Nat.div_eq_of_lt hyPow]
        decide
      · simp only [↓reduceIte]
        have hd : (y + 2 ^ s.n) / 2 ^ s.n = 1 := by
          have hpos : 0 < 2 ^ s.n := Nat.pow_pos (by decide)
          have hadd : y + 2 ^ s.n = 2 ^ s.n * 1 + y := by omega
          rw [hadd, Nat.mul_add_div hpos, Nat.div_eq_of_lt hyPow]
        rw [hd]
        decide
    have htr_full : trace y' s.n = trace y s.n := by
      rw [← trace_mod_pow2 y' s.n, hy'Mod]
    have hcons : y'.testBit 0 :: trace (F y') (s.n - 1) = y.testBit 0 :: trace (F y) (s.n - 1) := by
      rw [← trace_cons_pred y' s.n hn, ← trace_cons_pred y s.n hn, htr_full]
    have hy'0 : y'.testBit 0 = false := by
      have hb0 := (List.cons.inj hcons).1
      rw [hb0, hy0]
    have htr' : trace (F y') (s.n - 1) = trace (F y) (s.n - 1) := (List.cons.inj hcons).2
    have hbitEq : bit = xor b (piParity (physSigma s)) := by
      unfold physStep at hstep
      cases hna : nextAge s.isOdd s.age b with
      | none => simp [hna] at hstep
      | some na =>
        simp only [hna, Option.some.injEq, Prod.mk.injEq] at hstep
        rw [← hstep.2, scanXor_snd_eq_xor_piParity]
    have hy'PowN : ∀ k < s.n, (iter F (s.n - 1 - k) y').testBit k = (iter F (s.n - 1 - k) y).testBit k := by
      intro k hk
      have hpow : 2 ^ (k + 1 + (s.n - 1 - k)) = 2 ^ s.n := by congr 1; omega
      have heq := congrArg (fun z => z.testBit k) (iter_F_mod_pow2 (s.n - 1 - k) y' (k + 1))
      have heq2 := congrArg (fun z => z.testBit k) (iter_F_mod_pow2 (s.n - 1 - k) y (k + 1))
      have hm1 : (iter F (s.n - 1 - k) y' % 2 ^ (k + 1)).testBit k = (iter F (s.n - 1 - k) y').testBit k := by
        rw [Nat.testBit_mod_two_pow]; simp
      have hm2 : (iter F (s.n - 1 - k) y % 2 ^ (k + 1)).testBit k = (iter F (s.n - 1 - k) y).testBit k := by
        rw [Nat.testBit_mod_two_pow]; simp
      rw [hm1] at heq
      rw [hm2] at heq2
      rw [heq, heq2, hpow, hy'Mod, Nat.mod_eq_of_lt hyPow]
    have hd1' : s.d1 = antidiag y' (s.n - 1) := by
      rw [hd1]
      unfold antidiag
      rw [show s.n - 1 + 1 = s.n by omega]
      exact (List.map_congr_left fun k hk => (hy'PowN k (List.mem_range.mp hk)).symm)
    have hd2' : s.d2 = if s.n = 1 then [] else antidiag y' (s.n - 2) := by
      by_cases h1 : s.n = 1
      · simp [h1] at hd2 ⊢; exact hd2
      · simp only [h1, ↓reduceIte] at hd2 ⊢
        rw [hd2]
        unfold antidiag
        rw [show s.n - 2 + 1 = s.n - 1 by omega]
        refine List.map_congr_left fun k hk => ?_
        rw [List.mem_range] at hk
        have hpow : (k + 1 + (s.n - 2 - k)) ≤ s.n := by omega
        have hdvd : 2 ^ (k + 1 + (s.n - 2 - k)) ∣ 2 ^ s.n := Nat.pow_dvd_pow 2 hpow
        have heq := congrArg (fun z => z.testBit k) (iter_F_mod_pow2 (s.n - 2 - k) y' (k + 1))
        have heq2 := congrArg (fun z => z.testBit k) (iter_F_mod_pow2 (s.n - 2 - k) y (k + 1))
        have hm1 : (iter F (s.n - 2 - k) y' % 2 ^ (k + 1)).testBit k = (iter F (s.n - 2 - k) y').testBit k := by
          rw [Nat.testBit_mod_two_pow]; simp
        have hm2 : (iter F (s.n - 2 - k) y % 2 ^ (k + 1)).testBit k = (iter F (s.n - 2 - k) y).testBit k := by
          rw [Nat.testBit_mod_two_pow]; simp
        rw [hm1] at heq; rw [hm2] at heq2
        have hmodSub : y' % 2 ^ (k + 1 + (s.n - 2 - k)) = y % 2 ^ (k + 1 + (s.n - 2 - k)) := by
          have hsub := Nat.mod_mod_of_dvd y' hdvd
          rw [hy'Mod] at hsub
          exact hsub.symm
        rw [heq, heq2, hmodSub]
    have hmY' : StateMatchesSeed y' s :=
      ⟨hn, ho, hy'0, by rw [htr']; exact hacc, hd1', hd2'⟩
    have had := antidiag_step_spec y' s.n hn
    dsimp only at had
    have hsigEq : sigmaList (antidiag y' (s.n - 1)) (false :: if s.n = 1 then [] else antidiag y' (s.n - 2)) =
        physSigma s := by
      unfold physSigma
      rw [hd1', hd2']
    rw [hsigEq, scanXor_snd_eq_xor_piParity, hy'BitN] at had
    have hbMatch : (iter F s.n y').testBit 0 = b := by
      have hx := had.2.trans hbitEq
      cases h0 : (iter F s.n y').testBit 0 <;> cases b <;> cases piParity (physSigma s) <;> simp_all
    have hs'n : s'.n = s.n + 1 := physStep_n_eq hstep
    exact ⟨y', by rw [hs'n]; exact hy'Lt, physStep_matches_of_seed hmY' hstep hbMatch⟩

theorem physReachable_iff_exists_seed (s : PhysState) :
    PhysReachable s ↔ ∃ y : Nat, y < 2 ^ s.n ∧ StateMatchesSeed y s :=
  ⟨exists_seed_of_physReachable, fun ⟨_, _, hm⟩ => physReachable_of_matches rfl hm⟩

/-! ## 4. `zeroNext` Official Correspondence, Mass Conservation, and `iterZeroNext` -/

theorem zeroNext_spec_of_match {y : Nat} {s : PhysState} (hm : StateMatchesSeed y s) :
    (y.testBit s.n = false →
      (zeroNext s = none → ¬ SurvivesTo y (s.n + 1)) ∧
      (∀ s', zeroNext s = some s' →
        zrow (rowOfNat y) s.n 1 = piParity (physSigma s) ∧
        SurvivesTo y (s.n + 1) ∧
        StateMatchesSeed y s' ∧
        PhysReachable s' ∧
        popcount (y % 2 ^ (s.n + 1)) = popcount (y % 2 ^ s.n))) ∧
    (SurvivesTo y (s.n + 1) → y.testBit s.n = false →
      ∃ s', zeroNext s = some s' ∧ StateMatchesSeed y s') := by
  have hmCopy := hm
  obtain ⟨hn, ho, hy0, hacc, hd1, hd2⟩ := hm
  have had := antidiag_step_spec y s.n hn
  dsimp only at had
  have hsig : physSigma s =
      sigmaList (antidiag y (s.n - 1)) (false :: if s.n = 1 then [] else antidiag y (s.n - 2)) := by
    unfold physSigma; rw [hd1, hd2]
  rw [← hsig, scanXor_snd_eq_xor_piParity] at had
  have htr : trace (F y) s.n = trace (F y) (s.n - 1) ++ [(iter F s.n y).testBit 0] := by
    rw [trace_succ_pred (F y) s.n hn, iter_pred_succ_apply s.n y hn]
  have hmass_cons : y.testBit s.n = false →
      popcount (y % 2 ^ (s.n + 1)) = popcount (y % 2 ^ s.n) := by
    intro hbit0
    rw [popcount_mod_pow2_succ, hbit0]
    rfl
  constructor
  · intro hbit0
    have hb_forced : (iter F s.n y).testBit 0 = piParity (physSigma s) := by
      have hx := had.2
      rw [hbit0] at hx
      generalize (iter F s.n y).testBit 0 = b0 at hx ⊢
      generalize piParity (physSigma s) = p0 at hx ⊢
      cases b0 <;> cases p0 <;> simp_all
    constructor
    · intro hnone hsurv
      unfold SurvivesTo at hsurv
      obtain ⟨k, hk⟩ : ∃ k, s.n + 1 = k + 1 := ⟨s.n, rfl⟩
      rw [trace, accept, hy0] at hsurv
      simp only [Bool.not_false, Bool.true_and] at hsurv
      rw [← acceptFinal_isSome_eq_acceptRest, htr, acceptFinal_append, hacc] at hsurv
      simp only [acceptFinal] at hsurv
      rw [hb_forced] at hsurv
      unfold zeroNext at hnone
      dsimp only at hnone
      cases hna : nextAge s.isOdd s.age (piParity (physSigma s)) with
      | none => simp [hna] at hsurv
      | some na => simp [hna] at hnone
    · intro s' hsome
      have hpstep : physStep s (piParity (physSigma s)) = some (s', false) :=
        (zeroNext_eq_physStep_zero s s').mp hsome
      have hm' : StateMatchesSeed y s' := physStep_matches_of_seed hmCopy hpstep hb_forced
      have hs'n : s'.n = s.n + 1 := physStep_n_eq hpstep
      have hsurv' := stateMatchesSeed_survivesTo hm'
      rw [hs'n] at hsurv'
      refine ⟨?_, hsurv', hm', physReachable_of_matches rfl hm', hmass_cons hbit0⟩
      rw [zrow_rowOfNat_col1, hb_forced]
  · intro hsurv hbit0
    have hb_forced : (iter F s.n y).testBit 0 = piParity (physSigma s) := by
      have hx := had.2
      rw [hbit0] at hx
      generalize (iter F s.n y).testBit 0 = b0 at hx ⊢
      generalize piParity (physSigma s) = p0 at hx ⊢
      cases b0 <;> cases p0 <;> simp_all
    unfold SurvivesTo at hsurv
    rw [trace, accept, hy0] at hsurv
    simp only [Bool.not_false, Bool.true_and] at hsurv
    rw [← acceptFinal_isSome_eq_acceptRest, htr, acceptFinal_append, hacc] at hsurv
    simp only [acceptFinal] at hsurv
    rw [hb_forced] at hsurv
    cases hna : nextAge s.isOdd s.age (piParity (physSigma s)) with
    | none => simp [hna] at hsurv
    | some na =>
      have hz : ∃ s', zeroNext s = some s' := by
        unfold zeroNext
        dsimp only
        rw [hna]
        exact ⟨_, rfl⟩
      obtain ⟨s', hs'⟩ := hz
      have hpstep := (zeroNext_eq_physStep_zero s s').mp hs'
      exact ⟨s', hs', physStep_matches_of_seed hmCopy hpstep hb_forced⟩

theorem iterZeroNext_isSome_iff_survives {y : Nat} {s : PhysState} (L : Nat)
    (hm : StateMatchesSeed y s)
    (hzeros : ∀ j < L, y.testBit (s.n + j) = false) :
    (iterZeroNext s L).isSome = true ↔ SurvivesTo y (s.n + L) := by
  induction L generalizing s with
  | zero =>
    simp only [iterZeroNext, Option.isSome_some, Nat.add_zero, true_iff]
    exact stateMatchesSeed_survivesTo hm
  | succ L ih =>
    have hb0 : y.testBit s.n = false := hzeros 0 (by omega)
    have hzeros' : ∀ j < L, y.testBit (s.n + 1 + j) = false := fun j hj => by
      rw [show s.n + 1 + j = s.n + (j + 1) by omega]
      exact hzeros (j + 1) (by omega)
    have hspec := zeroNext_spec_of_match hm
    cases hz : zeroNext s with
    | none =>
      simp only [iterZeroNext, hz, Option.isSome_none, Bool.false_eq_true, false_iff]
      intro hsurv
      have hsub := survivesTo_mono (show s.n + 1 ≤ s.n + (L + 1) by omega) hsurv
      exact hspec.1 hb0 |>.1 hz hsub
    | some s' =>
      obtain ⟨_, _, hm', _, _⟩ := hspec.1 hb0 |>.2 s' hz
      simp only [iterZeroNext, hz]
      have hn' : s'.n = s.n + 1 := by
        unfold zeroNext at hz
        cases hna : nextAge s.isOdd s.age (piParity (physSigma s)) with
        | none => simp [hna] at hz
        | some na =>
          simp only [hna, Option.some.injEq] at hz
          rw [← hz]
      have ih' := ih hm' (by rw [hn']; exact hzeros')
      rw [hn', show s.n + 1 + L = s.n + (L + 1) by omega] at ih'
      exact ih'

def physStateOf (y : Nat) : Nat → Option PhysState
  | 0 => none
  | 1 => if y.testBit 0 = false then some initPhysState else none
  | n + 2 =>
    match physStateOf y (n + 1) with
    | none => none
    | some s =>
      match physStep s ((iter F (n + 1) y).testBit 0) with
      | none => none
      | some (s', _) => some s'

theorem physStateOf_succ (y m : Nat) (hm : 1 ≤ m) :
    physStateOf y (m + 1) =
      match physStateOf y m with
      | none => none
      | some s =>
        match physStep s ((iter F m y).testBit 0) with
        | none => none
        | some (s', _) => some s' := by
  obtain ⟨p, rfl⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
  rfl

theorem physStateOf_sound (y K : Nat) (s : PhysState) :
    physStateOf y K = some s → K = s.n ∧ StateMatchesSeed y s := by
  induction K generalizing s with
  | zero =>
    simp [physStateOf]
  | succ k ih =>
    cases k with
    | zero =>
      simp only [physStateOf]
      intro h
      split at h
      · next hy0 =>
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨rfl, by decide, by decide, hy0, by simp [initPhysState, trace, acceptFinal],
          by simp [initPhysState, antidiag, iter, hy0], rfl⟩
      · simp at h
    | succ m =>
      change physStateOf y (m + 2) = some s → m + 2 = s.n ∧ StateMatchesSeed y s
      intro h
      unfold physStateOf at h
      cases hprev : physStateOf y (m + 1) with
      | none => rw [hprev] at h; cases h
      | some sPrev =>
        rw [hprev] at h
        dsimp only at h
        cases hp : physStep sPrev ((iter F (m + 1) y).testBit 0) with
        | none => rw [hp] at h; cases h
        | some pr =>
          rw [hp] at h
          dsimp only at h
          simp only [Option.some.injEq] at h
          subst h
          obtain ⟨hnPrev, hmPrev⟩ := ih sPrev hprev
          have hm' := physStep_matches_of_seed hmPrev hp (by rw [← hnPrev])
          have hn' : pr.1.n = sPrev.n + 1 := physStep_n_eq hp
          exact ⟨by omega, hm'⟩

theorem physStateOf_isSome_of_survives {y K : Nat} (hK : 1 ≤ K) (hsurv : SurvivesTo y K) :
    ∃ s, physStateOf y K = some s ∧ StateMatchesSeed y s ∧ s.n = K := by
  induction K with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero =>
      unfold SurvivesTo trace accept at hsurv
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hsurv
      refine ⟨initPhysState, ?_, ?_, rfl⟩
      · simp [physStateOf, hsurv.1]
      · exact ⟨by decide, by decide, hsurv.1, by simp [initPhysState, trace, acceptFinal],
          by simp [initPhysState, antidiag, iter, hsurv.1], rfl⟩
    | succ m =>
      have hsub := survivesTo_mono (by omega : m + 1 ≤ m + 2) hsurv
      obtain ⟨sPrev, hps, hmPrev, hnPrev⟩ := ih (by omega) hsub
      have htr : trace (F y) (m + 1) = trace (F y) m ++ [(iter F (m + 1) y).testBit 0] := by
        rw [trace_succ_right, iter_succ_apply]
      unfold SurvivesTo at hsurv
      rw [trace, accept, Bool.and_eq_true, Bool.not_eq_true'] at hsurv
      have haccPrev : acceptFinal true 0 (trace (F y) m) = some (sPrev.isOdd, sPrev.age) := by
        have ha := hmPrev.2.2.2.1
        rw [hnPrev, Nat.add_sub_cancel] at ha
        exact ha
      have hrest := hsurv.2
      rw [← acceptFinal_isSome_eq_acceptRest, htr, acceptFinal_append, haccPrev] at hrest
      dsimp only [acceptFinal] at hrest
      cases hna : nextAge sPrev.isOdd sPrev.age ((iter F (m + 1) y).testBit 0) with
      | none => rw [hna] at hrest; cases hrest
      | some na =>
        have hstep : ∃ pr, physStep sPrev ((iter F (m + 1) y).testBit 0) = some pr := by
          unfold physStep; rw [hna]; exact ⟨_, rfl⟩
        obtain ⟨⟨s', bit⟩, hp⟩ := hstep
        have hps' : physStateOf y (m + 2) = some s' := by
          rw [physStateOf_succ y (m + 1) (by omega), hps]
          dsimp only
          rw [hp]
        obtain ⟨hn', hm'⟩ := physStateOf_sound y (m + 2) s' hps'
        exact ⟨s', hps', hm', hn'.symm⟩

theorem physStateOf_spec (y K : Nat) (s : PhysState) :
    physStateOf y K = some s ↔ (K = s.n ∧ StateMatchesSeed y s) := by
  constructor
  · exact physStateOf_sound y K s
  · rintro ⟨hn, hm⟩
    have hK1 : 1 ≤ K := by rw [hn]; exact hm.1
    have hsurv : SurvivesTo y K := by
      have := stateMatchesSeed_survivesTo hm
      rwa [← hn] at this
    obtain ⟨s', hps', hm', hn'⟩ := physStateOf_isSome_of_survives hK1 hsurv
    have heq : s = s' := stateMatchesSeed_unique (by omega) hm hm'
    rw [heq]
    exact hps'

/-! ## 5. Uniform `NoMass(M, H)`, Prefix-Box Width, and Exact Open Equivalence -/

def NoMass (M H : Nat) : Prop :=
  ∀ y : Nat, popcount y ≤ M → ¬ SurvivesTo y H

def MassDiverges : Prop :=
  ∀ M : Nat, ∃ H : Nat, NoMass M H

def UniformNoMassStep : Prop :=
  ∀ M K : Nat, NoMass M K → ∃ B : Nat, NoMass (M + 1) B

def BoxZeroCoastTerminates (M K : Nat) : Prop :=
  ∀ y < 2 ^ K, popcount y ≤ M + 1 → ∀ s, physStateOf y K = some s →
    ∃ L : Nat, (iterZeroNext s L).isNone = true

def ZeroCoastBoxTerminationHypothesis : Prop :=
  ∀ M K : Nat, NoMass M K → BoxZeroCoastTerminates M K

theorem noMass_mono {M1 M2 H1 H2 : Nat} (hM : M2 ≤ M1) (hH : H1 ≤ H2) :
    NoMass M1 H1 → NoMass M2 H2 := by
  intro h y hy hsurv
  exact h y (Nat.le_trans hy hM) (survivesTo_mono hH hsurv)

theorem noMass_zero_two : NoMass 0 2 := by
  intro y hy hsurv
  have hy0 : y = 0 := (popcount_eq_zero_iff y).mp (by omega)
  subst hy0
  exact (by decide : ¬ SurvivesTo 0 2) hsurv

theorem noMass_ge_two {M K : Nat} (hno : NoMass M K) : 2 ≤ K := by
  exact Classical.byContradiction fun hlt => by
    have hle : K ≤ 1 := by omega
    have hs1 : SurvivesTo 0 1 := by decide
    exact hno 0 (by simp [popcount_zero]) (survivesTo_mono hle hs1)

theorem noMass_prefix_box {M K y : Nat} (hno : NoMass M K)
    (hm : popcount y ≤ M + 1) (hsurv : SurvivesTo y K) : y < 2 ^ K := by
  rcases Nat.lt_or_ge y (2 ^ K) with hlt | hge
  · exact hlt
  · exfalso
    have hltPc : popcount (y % 2 ^ K) < popcount y := popcount_mod_pow2_lt hge
    have hproj : SurvivesTo (y % 2 ^ K) K := (survivesTo_mod_pow2 y K).mpr hsurv
    exact hno (y % 2 ^ K) (by omega) hproj

private def maxNatList (f : Nat → Nat) : List Nat → Nat
  | [] => 0
  | y :: ys => max (f y) (maxNatList f ys)

private theorem le_maxNatList (f : Nat → Nat) (xs : List Nat) (y : Nat) (hy : y ∈ xs) :
    f y ≤ maxNatList f xs := by
  induction xs with
  | nil => simp at hy
  | cons x xs ih =>
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hmem
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hmem) (Nat.le_max_right _ _)

theorem iterZeroNext_none_mono {s : PhysState} {L1 L2 : Nat} (hle : L1 ≤ L2)
    (hnone : (iterZeroNext s L1).isNone = true) : (iterZeroNext s L2).isNone = true := by
  induction L1 generalizing s L2 with
  | zero => simp [iterZeroNext] at hnone
  | succ L1 ih =>
    cases L2 with
    | zero => omega
    | succ L2 =>
      simp only [iterZeroNext] at hnone ⊢
      cases hz : zeroNext s with
      | none => simp
      | some s' =>
        simp only [hz] at hnone ⊢
        exact ih (by omega) hnone

private noncomputable def deathBound (M K : Nat) (hbox : BoxZeroCoastTerminates M K) (y : Nat) : Nat :=
  if hy : y < 2 ^ K then
    if hm : popcount y ≤ M + 1 then
      match hps : physStateOf y K with
      | none => 0
      | some s => Classical.choose (hbox y hy hm s hps)
    else 0
  else 0

private theorem deathBound_terminates (M K : Nat) (hbox : BoxZeroCoastTerminates M K)
    (y : Nat) (hy : y < 2 ^ K) (hm : popcount y ≤ M + 1) (s : PhysState)
    (hps : physStateOf y K = some s) :
    (iterZeroNext s (deathBound M K hbox y)).isNone = true := by
  dsimp only [deathBound]
  simp only [hy, hm, ↓reduceDIte]
  split
  · next hnone => simp [hps] at hnone
  · next s' hps' =>
    have heq : s = s' := by rw [hps] at hps'; injection hps'
    subst heq
    exact Classical.choose_spec (hbox y hy hm s hps')

theorem noMass_step_iff_box_terminates {M K : Nat} (hno : NoMass M K) :
    (∃ B : Nat, NoMass (M + 1) B) ↔ BoxZeroCoastTerminates M K := by
  have hK2 : 2 ≤ K := noMass_ge_two hno
  constructor
  · rintro ⟨B, hB⟩ y hyLt hyMass s hps
    refine ⟨B, ?_⟩
    obtain ⟨hn, hm⟩ := (physStateOf_spec y K s).mp hps
    have hzeros : ∀ j < B, y.testBit (s.n + j) = false := fun j _ =>
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hyLt (Nat.pow_le_pow_right (by decide) (by omega)))
    have hiff := iterZeroNext_isSome_iff_survives B hm hzeros
    have hdead : ¬ SurvivesTo y (s.n + B) := fun hs =>
      hB y hyMass (survivesTo_mono (by omega) hs)
    cases hres : iterZeroNext s B with
    | none => rfl
    | some s' =>
      exfalso
      have hs : SurvivesTo y (s.n + B) := hiff.mp (by simp [hres])
      exact hdead hs
  · intro hbox
    classical
    let death := deathBound M K hbox
    let Lmax := maxNatList death (List.range (2 ^ K))
    refine ⟨K + Lmax, ?_⟩
    intro y hyMass hsurv
    have hsurvK : SurvivesTo y K := survivesTo_mono (by omega) hsurv
    have hyLt : y < 2 ^ K := noMass_prefix_box hno hyMass hsurvK
    obtain ⟨s, hps, hm, hn⟩ := physStateOf_isSome_of_survives (by omega) hsurvK
    have hLy : (iterZeroNext s (death y)).isNone = true :=
      deathBound_terminates M K hbox y hyLt hyMass s hps
    have hmem : y ∈ List.range (2 ^ K) := List.mem_range.mpr hyLt
    have hle_max : death y ≤ Lmax := le_maxNatList death (List.range (2 ^ K)) y hmem
    have hnone_max : (iterZeroNext s Lmax).isNone = true :=
      iterZeroNext_none_mono hle_max hLy
    have hzeros : ∀ j < Lmax, y.testBit (s.n + j) = false := fun j _ =>
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hyLt (Nat.pow_le_pow_right (by decide) (by omega)))
    have hiff := iterZeroNext_isSome_iff_survives Lmax hm hzeros
    rw [hn] at hiff
    have hisSome : (iterZeroNext s Lmax).isSome = true := hiff.mpr hsurv
    cases hz : iterZeroNext s Lmax with
    | none => simp [hz] at hisSome
    | some _ => simp [hz] at hnone_max

theorem massDiverges_iff_uniform_noMass_step :
    MassDiverges ↔ UniformNoMassStep := by
  constructor
  · intro hdiv M _ _
    exact hdiv (M + 1)
  · intro hstep M
    induction M with
    | zero => exact ⟨2, noMass_zero_two⟩
    | succ M ih =>
      obtain ⟨K, hK⟩ := ih
      exact hstep M K hK

theorem massDiverges_iff_zeroCoastBoxTermination :
    MassDiverges ↔ ZeroCoastBoxTerminationHypothesis := by
  rw [massDiverges_iff_uniform_noMass_step]
  constructor
  · intro hstep M K hno
    exact (noMass_step_iff_box_terminates hno).mp (hstep M K hno)
  · intro hbox M K hno
    exact (noMass_step_iff_box_terminates hno).mpr (hbox M K hno)

/-! ## 6. Exact Equivalence Between `accept (trace y H)` and `InB35` Prefixes -/

def InB35 (G : Nat → Bool) : Prop :=
  G 0 = true ∧
  (∀ r, G r = true → ∃ d, (d = 3 ∨ d = 5) ∧ G (r + d) = true ∧ (∀ j, 0 < j → j < d → G (r + j) = false))

def PrefB35 (b : Nat → Bool) (H : Nat) : Prop :=
  ∃ G, InB35 G ∧ ∀ t < H, b t = boundary G t

private def period3Gate (r : Nat) : Bool := decide (r % 3 = 0)
private def period5Gate (r : Nat) : Bool := decide (r % 5 = 0)

private theorem period3Gate_inB35 : InB35 period3Gate := by
  constructor
  · rfl
  · intro r hr
    simp only [period3Gate, decide_eq_true_eq] at hr
    refine ⟨3, Or.inl rfl, ?_, ?_⟩
    · simp only [period3Gate, decide_eq_true_eq]; omega
    · intro j hj1 hj2
      have hcases : j = 1 ∨ j = 2 := by omega
      rcases hcases with rfl | rfl <;>
        · simp only [period3Gate, decide_eq_false_iff_not]
          rw [Nat.add_mod, hr]; decide

private theorem period5Gate_inB35 : InB35 period5Gate := by
  constructor
  · rfl
  · intro r hr
    simp only [period5Gate, decide_eq_true_eq] at hr
    refine ⟨5, Or.inr rfl, ?_, ?_⟩
    · simp only [period5Gate, decide_eq_true_eq]; omega
    · intro j hj1 hj2
      have hcases : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
      rcases hcases with rfl | rfl | rfl | rfl <;>
        · simp only [period5Gate, decide_eq_false_iff_not]
          rw [Nat.add_mod, hr]; decide

private theorem list_range_add_map (a b : Nat) :
    List.range (a + b) = List.range a ++ (List.range b).map (· + a) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [← Nat.add_assoc, List.range_succ, ih, List.range_succ, List.map_append, List.map_singleton,
      List.append_assoc, Nat.add_comm b a]

private theorem b35_boundary_even (G : Nat → Bool) (r : Nat) : boundary G (2 * r) = !(G r) := by
  simp [boundary]

private theorem b35_boundary_odd (G : Nat → Bool) (r : Nat) : boundary G (2 * r + 1) = true := by
  simp [boundary]

theorem inB35_accept_block3 (G : Nat → Bool) (r0 : Nat)
    (h1 : G (r0 + 1) = false) (h2 : G (r0 + 2) = false) (h3 : G (r0 + 3) = true) :
    ((List.range 6).map (fun i => boundary G (2 * r0 + 1 + i))) =
      [true, true, true, true, true, false] := by
  simp only [List.range_succ, List.range_zero, List.map_nil, List.nil_append,
    List.map_cons, List.cons_append]
  have e0 : 2 * r0 + 1 + 0 = 2 * r0 + 1 := by omega
  have e1 : 2 * r0 + 1 + 1 = 2 * (r0 + 1) := by omega
  have e2 : 2 * r0 + 1 + 2 = 2 * (r0 + 1) + 1 := by omega
  have e3 : 2 * r0 + 1 + 3 = 2 * (r0 + 2) := by omega
  have e4 : 2 * r0 + 1 + 4 = 2 * (r0 + 2) + 1 := by omega
  have e5 : 2 * r0 + 1 + 5 = 2 * (r0 + 3) := by omega
  rw [e0, e1, e2, e3, e4, e5]
  simp [b35_boundary_even, b35_boundary_odd, h1, h2, h3]

theorem inB35_accept_block5 (G : Nat → Bool) (r0 : Nat)
    (h1 : G (r0 + 1) = false) (h2 : G (r0 + 2) = false)
    (h3 : G (r0 + 3) = false) (h4 : G (r0 + 4) = false) (h5 : G (r0 + 5) = true) :
    ((List.range 10).map (fun i => boundary G (2 * r0 + 1 + i))) =
      [true, true, true, true, true, true, true, true, true, false] := by
  simp only [List.range_succ, List.range_zero, List.map_nil, List.nil_append,
    List.map_cons, List.cons_append]
  have e0 : 2 * r0 + 1 + 0 = 2 * r0 + 1 := by omega
  have e1 : 2 * r0 + 1 + 1 = 2 * (r0 + 1) := by omega
  have e2 : 2 * r0 + 1 + 2 = 2 * (r0 + 1) + 1 := by omega
  have e3 : 2 * r0 + 1 + 3 = 2 * (r0 + 2) := by omega
  have e4 : 2 * r0 + 1 + 4 = 2 * (r0 + 2) + 1 := by omega
  have e5 : 2 * r0 + 1 + 5 = 2 * (r0 + 3) := by omega
  have e6 : 2 * r0 + 1 + 6 = 2 * (r0 + 3) + 1 := by omega
  have e7 : 2 * r0 + 1 + 7 = 2 * (r0 + 4) := by omega
  have e8 : 2 * r0 + 1 + 8 = 2 * (r0 + 4) + 1 := by omega
  have e9 : 2 * r0 + 1 + 9 = 2 * (r0 + 5) := by omega
  rw [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  simp [b35_boundary_even, b35_boundary_odd, h1, h2, h3, h4, h5]

private theorem acceptRest_append_block (w1 w2 : List Bool)
    (hw1 : w1 = [true, true, true, true, true, false] ∨
           w1 = [true, true, true, true, true, true, true, true, true, false]) :
    acceptRest true 0 (w1 ++ w2) = acceptRest true 0 w2 := by
  rcases hw1 with rfl | rfl <;> rfl

private theorem list_take_range_le {m n : Nat} (h : m ≤ n) :
    (List.range n).take m = List.range m := by
  have hs := list_range_add_map m (n - m)
  rw [show m + (n - m) = n by omega] at hs
  rw [hs, List.take_left' (by simp)]

private theorem acceptRest_take_block3 :
    ∀ m ≤ 6, acceptRest true 0 ([true, true, true, true, true, false].take m) = true := by
  decide

private theorem acceptRest_take_block5 :
    ∀ m ≤ 10, acceptRest true 0 ([true, true, true, true, true, true, true, true, true, false].take m) = true := by
  decide

theorem inB35_acceptRest_from (G : Nat → Bool) (hG : InB35 G) :
    ∀ (m r0 : Nat), G r0 = true →
      acceptRest true 0 ((List.range m).map (fun i => boundary G (2 * r0 + 1 + i))) = true := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro r0 hr0
    obtain ⟨d, hd, hsucc, hmid⟩ := hG.2 r0 hr0
    rcases hd with rfl | rfl
    · have h1 : G (r0 + 1) = false := hmid 1 (by decide) (by decide)
      have h2 : G (r0 + 2) = false := hmid 2 (by decide) (by decide)
      by_cases hm : m ≤ 6
      · have htake : (List.range m).map (fun i => boundary G (2 * r0 + 1 + i)) =
            ((List.range 6).map (fun i => boundary G (2 * r0 + 1 + i))).take m := by
          rw [← List.map_take, list_take_range_le hm]
        rw [htake, inB35_accept_block3 G r0 h1 h2 hsucc]
        exact acceptRest_take_block3 m hm
      · have hm6 : 6 ≤ m := by omega
        have hsplit : List.range m = List.range 6 ++ (List.range (m - 6)).map (· + 6) := by
          rw [← list_range_add_map]; congr 1; omega
        rw [hsplit, List.map_append, List.map_map]
        rw [inB35_accept_block3 G r0 h1 h2 hsucc]
        rw [acceptRest_append_block _ _ (Or.inl rfl)]
        have hidx' : (fun x => boundary G (2 * r0 + 1 + x)) ∘ (· + 6) =
            (fun i => boundary G (2 * (r0 + 3) + 1 + i)) := by
          funext i; simp only [Function.comp_apply]; congr 1; omega
        rw [hidx']
        exact ih (m - 6) (by omega) (r0 + 3) hsucc
    · have h1 : G (r0 + 1) = false := hmid 1 (by decide) (by decide)
      have h2 : G (r0 + 2) = false := hmid 2 (by decide) (by decide)
      have h3 : G (r0 + 3) = false := hmid 3 (by decide) (by decide)
      have h4 : G (r0 + 4) = false := hmid 4 (by decide) (by decide)
      by_cases hm : m ≤ 10
      · have htake : (List.range m).map (fun i => boundary G (2 * r0 + 1 + i)) =
            ((List.range 10).map (fun i => boundary G (2 * r0 + 1 + i))).take m := by
          rw [← List.map_take, list_take_range_le hm]
        rw [htake, inB35_accept_block5 G r0 h1 h2 h3 h4 hsucc]
        exact acceptRest_take_block5 m hm
      · have hm10 : 10 ≤ m := by omega
        have hsplit : List.range m = List.range 10 ++ (List.range (m - 10)).map (· + 10) := by
          rw [← list_range_add_map]; congr 1; omega
        rw [hsplit, List.map_append, List.map_map]
        rw [inB35_accept_block5 G r0 h1 h2 h3 h4 hsucc]
        rw [acceptRest_append_block _ _ (Or.inr rfl)]
        have hidx' : (fun x => boundary G (2 * r0 + 1 + x)) ∘ (· + 10) =
            (fun i => boundary G (2 * (r0 + 5) + 1 + i)) := by
          funext i; simp only [Function.comp_apply]; congr 1; omega
        rw [hidx']
        exact ih (m - 10) (by omega) (r0 + 5) hsucc

theorem inB35_accept_prefix (G : Nat → Bool) (hG : InB35 G) (H : Nat) :
    accept ((List.range H).map (boundary G)) = true := by
  cases H with
  | zero => rfl
  | succ H =>
    have hsplit : List.range (H + 1) = [0] ++ (List.range H).map (· + 1) := by
      have hs := list_range_add_map 1 H
      rw [Nat.add_comm 1 H] at hs
      simpa [List.range_one] using hs
    rw [hsplit, List.map_append, List.map_singleton, List.singleton_append]
    have h0 : boundary G 0 = false := by simp [boundary, hG.1]
    simp only [accept, h0, Bool.not_false, Bool.true_and, List.map_map]
    have hidx : (boundary G ∘ (· + 1)) = (fun i => boundary G (2 * 0 + 1 + i)) := by
      funext i; simp only [Function.comp_apply]; congr 1; omega
    rw [hidx]
    exact inB35_acceptRest_from G hG H 0 hG.1

private theorem prepend_block3_inB35 (G' : Nat → Bool) (hG' : InB35 G') :
    InB35 (fun r => if r < 3 then decide (r = 0) else G' (r - 3)) := by
  let G : Nat → Bool := fun r => if r < 3 then decide (r = 0) else G' (r - 3)
  constructor
  · rfl
  · intro r hr
    by_cases hr0 : r = 0
    · subst hr0
      refine ⟨3, Or.inl rfl, ?_, ?_⟩
      · simp [hG'.1]
      · intro j hj1 hj2
        have hj : j = 1 ∨ j = 2 := by omega
        rcases hj with rfl | rfl <;> simp
    · by_cases hr3 : r < 3
      · simp [hr3, hr0] at hr
      · have hgr : G' (r - 3) = true := by simpa [G, hr3] using hr
        obtain ⟨d, hd, hsucc, hmid⟩ := hG'.2 (r - 3) hgr
        refine ⟨d, hd, ?_, ?_⟩
        · have hnot : ¬ (r + d < 3) := by omega
          have hsub : r + d - 3 = r - 3 + d := by omega
          simp [hnot, hsub, hsucc]
        · intro j hj1 hj2
          have hnot : ¬ (r + j < 3) := by omega
          have hsub : r + j - 3 = r - 3 + j := by omega
          simp [hnot, hsub, hmid j hj1 hj2]

private theorem prepend_block5_inB35 (G' : Nat → Bool) (hG' : InB35 G') :
    InB35 (fun r => if r < 5 then decide (r = 0) else G' (r - 5)) := by
  let G : Nat → Bool := fun r => if r < 5 then decide (r = 0) else G' (r - 5)
  constructor
  · rfl
  · intro r hr
    by_cases hr0 : r = 0
    · subst hr0
      refine ⟨5, Or.inr rfl, ?_, ?_⟩
      · simp [hG'.1]
      · intro j hj1 hj2
        have hj : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
        rcases hj with rfl | rfl | rfl | rfl <;> simp
    · by_cases hr5 : r < 5
      · simp [hr5, hr0] at hr
      · have hgr : G' (r - 5) = true := by simpa [G, hr5] using hr
        obtain ⟨d, hd, hsucc, hmid⟩ := hG'.2 (r - 5) hgr
        refine ⟨d, hd, ?_, ?_⟩
        · have hnot : ¬ (r + d < 5) := by omega
          have hsub : r + d - 5 = r - 5 + d := by omega
          simp [hnot, hsub, hsucc]
        · intro j hj1 hj2
          have hnot : ¬ (r + j < 5) := by omega
          have hsub : r + j - 5 = r - 5 + j := by omega
          simp [hnot, hsub, hmid j hj1 hj2]

private theorem acceptRest_decomp (w : List Bool) :
    acceptRest true 0 w = true →
      (w.length ≤ 5 ∧ ∀ t (ht : t < w.length), w[t] = true) ∨
      (∃ rest, w = [true, true, true, true, true, false] ++ rest ∧ acceptRest true 0 rest = true) ∨
      (6 ≤ w.length ∧ w.length ≤ 9 ∧ ∀ t (ht : t < w.length), w[t] = true) ∨
      (∃ rest, w = [true, true, true, true, true, true, true, true, true, false] ++ rest ∧
        acceptRest true 0 rest = true) := by
  rcases w with _ | ⟨b0, w⟩
  · intro _; left; refine ⟨by decide, fun t ht => by simp at ht⟩
  rcases w with _ | ⟨b1, w⟩
  · intro h; cases b0 with
    | false => simp [acceptRest] at h
    | true => left; refine ⟨by decide, fun t ht => by
        rcases t with _ | _ <;> first | rfl | (simp at ht; try omega)⟩
  rcases w with _ | ⟨b2, w⟩
  · intro h; cases b0 <;> cases b1 <;> (simp [acceptRest, gateNext] at h; try cases h)
    left; refine ⟨by decide, fun t ht => by
      rcases t with _ | _ | _ <;> first | rfl | (simp at ht; try omega)⟩
  rcases w with _ | ⟨b3, w⟩
  · intro h; cases b0 <;> cases b1 <;> cases b2 <;> (simp [acceptRest, gateNext] at h; try cases h)
    left; refine ⟨by decide, fun t ht => by
      rcases t with _ | _ | _ | _ <;> first | rfl | (simp at ht; try omega)⟩
  rcases w with _ | ⟨b4, w⟩
  · intro h; cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
      (simp [acceptRest, gateNext] at h; try cases h)
    left; refine ⟨by decide, fun t ht => by
      rcases t with _ | _ | _ | _ | _ <;> first | rfl | (simp at ht; try omega)⟩
  rcases w with _ | ⟨b5, w⟩
  · intro h; cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;>
      (simp [acceptRest, gateNext] at h; try cases h)
    left; refine ⟨by decide, fun t ht => by
      rcases t with _ | _ | _ | _ | _ | _ <;> first | rfl | (simp at ht; try omega)⟩
  intro h
  have hpref5 : b0 = true ∧ b1 = true ∧ b2 = true ∧ b3 = true ∧ b4 = true := by
    cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;>
      simp_all [acceptRest, gateNext]
  rcases hpref5 with ⟨rfl, rfl, rfl, rfl, rfl⟩
  cases b5 with
  | false =>
    right; left
    refine ⟨w, rfl, ?_⟩
    simpa [acceptRest, gateNext] using h
  | true =>
    rcases w with _ | ⟨b6, w⟩
    · right; right; left; refine ⟨by decide, by decide, fun t ht => by
        rcases t with _ | _ | _ | _ | _ | _ | _ <;> first | rfl | (simp at ht; omega)⟩
    rcases w with _ | ⟨b7, w⟩
    · have hb6 : b6 = true := by cases b6 <;> simp_all [acceptRest, gateNext]
      subst hb6; right; right; left; refine ⟨by decide, by decide, fun t ht => by
        rcases t with _ | _ | _ | _ | _ | _ | _ | _ <;> first | rfl | (simp at ht; omega)⟩
    rcases w with _ | ⟨b8, w⟩
    · have hb67 : b6 = true ∧ b7 = true := by
        cases b6 <;> cases b7 <;> simp_all [acceptRest, gateNext]
      rcases hb67 with ⟨rfl, rfl⟩
      right; right; left; refine ⟨by decide, by decide, fun t ht => by
        rcases t with _ | _ | _ | _ | _ | _ | _ | _ | _ <;> first | rfl | (simp at ht; omega)⟩
    rcases w with _ | ⟨b9, w⟩
    · have hb678 : b6 = true ∧ b7 = true ∧ b8 = true := by
        cases b6 <;> cases b7 <;> cases b8 <;> simp_all [acceptRest, gateNext]
      rcases hb678 with ⟨rfl, rfl, rfl⟩
      right; right; left; refine ⟨by decide, by decide, fun t ht => by
        rcases t with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ <;> first | rfl | (simp at ht; omega)⟩
    have hb6789 : b6 = true ∧ b7 = true ∧ b8 = true ∧ b9 = false := by
      cases b6 <;> cases b7 <;> cases b8 <;> cases b9 <;> simp_all [acceptRest, gateNext]
    rcases hb6789 with ⟨rfl, rfl, rfl, rfl⟩
    right; right; right
    refine ⟨w, rfl, ?_⟩
    simpa [acceptRest, gateNext] using h

private theorem boundary_shift3 (G' : Nat → Bool) (k : Nat) :
    boundary (fun r => if r < 3 then decide (r = 0) else G' (r - 3)) (k + 6) =
      boundary G' k := by
  by_cases hmod : k % 2 = 0
  · obtain ⟨q, hq⟩ : ∃ q, k = 2 * q := ⟨k / 2, by omega⟩
    subst hq
    have hq' : 2 * q + 6 = 2 * (q + 3) := by omega
    rw [hq', b35_boundary_even, b35_boundary_even]
    have hnot : ¬ (q + 3 < 3) := by omega
    simp [hnot]
  · obtain ⟨q, hq⟩ : ∃ q, k = 2 * q + 1 := ⟨k / 2, by omega⟩
    subst hq
    have hq' : 2 * q + 1 + 6 = 2 * (q + 3) + 1 := by omega
    rw [hq', b35_boundary_odd, b35_boundary_odd]

private theorem boundary_shift5 (G' : Nat → Bool) (k : Nat) :
    boundary (fun r => if r < 5 then decide (r = 0) else G' (r - 5)) (k + 10) =
      boundary G' k := by
  by_cases hmod : k % 2 = 0
  · obtain ⟨q, hq⟩ : ∃ q, k = 2 * q := ⟨k / 2, by omega⟩
    subst hq
    have hq' : 2 * q + 10 = 2 * (q + 5) := by omega
    rw [hq', b35_boundary_even, b35_boundary_even]
    have hnot : ¬ (q + 5 < 5) := by omega
    simp [hnot]
  · obtain ⟨q, hq⟩ : ∃ q, k = 2 * q + 1 := ⟨k / 2, by omega⟩
    subst hq
    have hq' : 2 * q + 1 + 10 = 2 * (q + 5) + 1 := by omega
    rw [hq', b35_boundary_odd, b35_boundary_odd]

private theorem acceptRest_implies_inB35_aux (n : Nat) :
    ∀ w : List Bool, w.length = n → acceptRest true 0 w = true →
      ∃ G, InB35 G ∧ ∀ t (ht : t < w.length), w[t] = boundary G (t + 1) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro w hn hacc
    rcases acceptRest_decomp w hacc with
      ⟨hlen, htrue⟩ | ⟨rest, rfl, hrest⟩ | ⟨_, hlen, htrue⟩ | ⟨rest, rfl, hrest⟩
    · refine ⟨period3Gate, period3Gate_inB35, ?_⟩
      intro t ht
      rw [htrue t ht]
      rcases t with _ | _ | _ | _ | _ | t
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · omega
    · obtain ⟨G', hG', hmatch⟩ := ih rest.length (by simp at hn; omega) rest rfl hrest
      let G : Nat → Bool := fun r => if r < 3 then decide (r = 0) else G' (r - 3)
      refine ⟨G, prepend_block3_inB35 G' hG', ?_⟩
      intro t ht
      by_cases ht6 : t < 6
      · have hleft : ([true, true, true, true, true, false] ++ rest)[t] =
            ([true, true, true, true, true, false])[t]'(by simp; exact ht6) := by
          rw [List.getElem_append_left]
        rw [hleft]
        rcases t with _ | _ | _ | _ | _ | _ | t
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · change false = boundary G (2 * 3)
          rw [b35_boundary_even]; simp [G, hG'.1]
        · omega
      · have hlt : t - 6 < rest.length := by simp at ht; omega
        have hleft : ([true, true, true, true, true, false] ++ rest)[t] = rest[t - 6] := by
          rw [List.getElem_append_right (by simp; omega)]; simp
        rw [hleft, hmatch (t - 6) hlt]
        have hd : t + 1 = (t - 6 + 1) + 6 := by omega
        rw [hd]
        exact (boundary_shift3 G' (t - 6 + 1)).symm
    · refine ⟨period5Gate, period5Gate_inB35, ?_⟩
      intro t ht
      rw [htrue t ht]
      rcases t with _ | _ | _ | _ | _ | _ | _ | _ | _ | t
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · omega
    · obtain ⟨G', hG', hmatch⟩ := ih rest.length (by simp at hn; omega) rest rfl hrest
      let G : Nat → Bool := fun r => if r < 5 then decide (r = 0) else G' (r - 5)
      refine ⟨G, prepend_block5_inB35 G' hG', ?_⟩
      intro t ht
      by_cases ht10 : t < 10
      · have hleft : ([true, true, true, true, true, true, true, true, true, false] ++ rest)[t] =
            ([true, true, true, true, true, true, true, true, true, false])[t]'(by
              simp; exact ht10) := by
          rw [List.getElem_append_left]
        rw [hleft]
        rcases t with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | t
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · change false = boundary G (2 * 5)
          rw [b35_boundary_even]; simp [G, hG'.1]
        · omega
      · have hlt : t - 10 < rest.length := by simp at ht; omega
        have hleft :
            ([true, true, true, true, true, true, true, true, true, false] ++ rest)[t] =
              rest[t - 10] := by
          rw [List.getElem_append_right (by simp; omega)]; simp
        rw [hleft, hmatch (t - 10) hlt]
        have hd : t + 1 = (t - 10 + 1) + 10 := by omega
        rw [hd]
        exact (boundary_shift5 G' (t - 10 + 1)).symm

theorem acceptRest_implies_inB35 (w : List Bool) :
    acceptRest true 0 w = true →
      ∃ G, InB35 G ∧ ∀ t (ht : t < w.length), w[t] = boundary G (t + 1) :=
  acceptRest_implies_inB35_aux w.length w rfl

theorem survivesTo_iff_prefB35 (y H : Nat) :
    SurvivesTo y H ↔ PrefB35 (fun t => (iter F t y).testBit 0) H := by
  constructor
  · intro h
    cases H with
    | zero =>
      exact ⟨period3Gate, period3Gate_inB35, fun t ht => by omega⟩
    | succ H =>
      unfold SurvivesTo trace at h
      simp only [accept, Bool.and_eq_true, Bool.not_eq_true'] at h
      obtain ⟨hy0, hrest⟩ := h
      obtain ⟨G, hG, hmatch⟩ := acceptRest_implies_inB35 (trace (F y) H) hrest
      refine ⟨G, hG, ?_⟩
      intro t ht
      cases t with
      | zero =>
        change y.testBit 0 = boundary G 0
        rw [hy0]; simp [boundary, hG.1]
      | succ t =>
        change (iter F (t + 1) y).testBit 0 = boundary G (t + 1)
        rw [iter_succ_apply]
        have htH : t < H := by omega
        have hg := hmatch t (by rw [trace_length]; exact htH)
        rw [trace_getElem (F y) H t htH] at hg
        exact hg
  · rintro ⟨G, hG, hmatch⟩
    have htr : trace y H = (List.range H).map (boundary G) := by
      apply List.ext_getElem
      · simp [trace_length]
      · intro i hi1 _
        rw [trace_length] at hi1
        rw [trace_getElem y H i hi1]
        simp only [List.getElem_map, List.getElem_range]
        exact hmatch i hi1
    unfold SurvivesTo
    rw [htr]
    exact inB35_accept_prefix G hG H

/-! ## 7. Mass-Prefix Width Bound and Finitary Equivalence (`InB35 ↔ MassDiverges`) -/


def FiniteSeedsTerminate : Prop :=
  ∀ y : Nat, ∃ H : Nat, ¬ SurvivesTo y H

theorem mass_width_bound (M H_prev : Nat)
    (hpred : ∀ z : Nat, popcount z < M → ¬ SurvivesTo z (H_prev + 1)) :
    ∀ y H : Nat, popcount y ≤ M → H_prev + 1 ≤ H → SurvivesTo y H → y < 2 ^ (H_prev + 1) := by
  intro y H hym hle hsurv
  rcases Nat.lt_or_ge y (2 ^ (H_prev + 1)) with hlt | hge_pow
  · exact hlt
  · exfalso
    have hsub := survivesTo_mono hle hsurv
    have hproj : SurvivesTo (y % 2 ^ (H_prev + 1)) (H_prev + 1) :=
      (survivesTo_mod_pow2 y (H_prev + 1)).mpr hsub
    have hlt : popcount (y % 2 ^ (H_prev + 1)) < M :=
      Nat.lt_of_lt_of_le (popcount_mod_pow2_lt hge_pow) hym
    exact hpred (y % 2 ^ (H_prev + 1)) hlt hproj

private def maxDeathOnPrefix (death : Nat → Nat) : List Nat → Nat
  | [] => 0
  | y :: ys => max (death y) (maxDeathOnPrefix death ys)

private theorem le_maxDeathOnPrefix (death : Nat → Nat) (xs : List Nat) (y : Nat) (hy : y ∈ xs) :
    death y ≤ maxDeathOnPrefix death xs := by
  induction xs with
  | nil => simp at hy
  | cons x xs ih =>
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hmem
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hmem) (Nat.le_max_right _ _)

theorem finite_seeds_terminate_iff_mass_diverges :
    FiniteSeedsTerminate ↔ MassDiverges := by
  constructor
  · intro hterm M
    induction M with
    | zero =>
      refine ⟨2, ?_⟩
      intro y hy hsurv
      have hy0 : y = 0 := (popcount_eq_zero_iff y).mp (by omega)
      subst hy0
      have hfalse : ¬ SurvivesTo 0 2 := by decide
      exact hfalse hsurv
    | succ M ih =>
      obtain ⟨H_prev, hprev⟩ := ih
      have hpred : ∀ z : Nat, popcount z < M + 1 → ¬ SurvivesTo z (H_prev + 1) := by
        intro z hz hsurv
        exact hprev z (by omega) (survivesTo_mono (Nat.le_succ H_prev) hsurv)
      let death : Nat → Nat := fun z => Classical.choose (hterm z)
      let H_box := maxDeathOnPrefix death (List.range (2 ^ (H_prev + 1)))
      refine ⟨max (H_prev + 1) H_box, ?_⟩
      intro y hy hsurv
      have hle1 : H_prev + 1 ≤ max (H_prev + 1) H_box := Nat.le_max_left _ _
      have hlt_pow : y < 2 ^ (H_prev + 1) :=
        mass_width_bound (M + 1) H_prev hpred y (max (H_prev + 1) H_box) hy hle1 hsurv
      have hy_mem : y ∈ List.range (2 ^ (H_prev + 1)) := List.mem_range.mpr hlt_pow
      have hd_le : death y ≤ H_box := le_maxDeathOnPrefix death (List.range (2 ^ (H_prev + 1))) y hy_mem
      have hd_le_max : death y ≤ max (H_prev + 1) H_box := Nat.le_trans hd_le (Nat.le_max_right _ _)
      have hdead : ¬ SurvivesTo y (death y) := Classical.choose_spec (hterm y)
      exact hdead (survivesTo_mono hd_le_max hsurv)
  · intro hdiv y
    obtain ⟨H, hH⟩ := hdiv (popcount y)
    exact ⟨H, hH y (Nat.le_refl _)⟩

theorem inB35_empty_iff_mass_diverges :
    (∀ y : Nat, ¬ ∃ G, InB35 G ∧ ∀ t, (iter F t y).testBit 0 = boundary G t) ↔ MassDiverges := by
  rw [← finite_seeds_terminate_iff_mass_diverges]
  constructor
  · intro h y
    exact Classical.byContradiction fun hall => by
      have hall' : ∀ H, SurvivesTo y H := fun H =>
        Classical.byContradiction fun hn => hall ⟨H, hn⟩
      let b : Nat → Bool := fun t => (iter F t y).testBit 0
      let G : Nat → Bool := fun r => !(b (2 * r))
      have hex : ∃ G, InB35 G ∧ ∀ t, (iter F t y).testBit 0 = boundary G t := by
        refine ⟨G, ⟨?_, ?_⟩, ?_⟩
        · have hs1 := hall' 1
          unfold SurvivesTo trace at hs1
          simp only [accept, Bool.and_eq_true, Bool.not_eq_true'] at hs1
          change !(b 0) = true
          change !(y.testBit 0) = true
          rw [hs1.1]; rfl
        · intro r hr
          have hs := (survivesTo_iff_prefB35 y (2 * r + 11)).mp (hall' (2 * r + 11))
          obtain ⟨G0, hG0, hm⟩ := hs
          have hb_even : b (2 * r) = !(G0 r) := by
            have := hm (2 * r) (by omega)
            rw [b35_boundary_even] at this
            exact this
          have hgr0 : G0 r = true := by
            change !(b (2 * r)) = true at hr
            rw [hb_even] at hr
            cases hg : G0 r <;> simp_all
          obtain ⟨d, hd, hsucc, hmid⟩ := hG0.2 r hgr0
          refine ⟨d, hd, ?_, ?_⟩
          · have hb := hm (2 * (r + d)) (by rcases hd with rfl | rfl <;> omega)
            rw [b35_boundary_even] at hb
            change !(b (2 * (r + d))) = true
            rw [show b (2 * (r + d)) = !(G0 (r + d)) from hb, hsucc]; rfl
          · intro j hj1 hj2
            have hb := hm (2 * (r + j)) (by rcases hd with rfl | rfl <;> omega)
            rw [b35_boundary_even] at hb
            dsimp only [b] at hb
            dsimp only [G, b]
            rw [hb, hmid j hj1 hj2]; rfl
        · intro t
          by_cases hmod : t % 2 = 0
          · obtain ⟨r, rfl⟩ : ∃ r, t = 2 * r := ⟨t / 2, by omega⟩
            change b (2 * r) = boundary G (2 * r)
            rw [b35_boundary_even]
            change b (2 * r) = !(!(b (2 * r)))
            cases b (2 * r) <;> rfl
          · obtain ⟨r, rfl⟩ : ∃ r, t = 2 * r + 1 := ⟨t / 2, by omega⟩
            rw [b35_boundary_odd]
            have hs := (survivesTo_iff_prefB35 y (2 * r + 2)).mp (hall' (2 * r + 2))
            obtain ⟨G0, _, hm⟩ := hs
            have hb := hm (2 * r + 1) (by omega)
            rw [b35_boundary_odd] at hb
            exact hb
      exact h y hex
  · intro hterm y ⟨G, hG, hmatch⟩
    obtain ⟨H, hH⟩ := hterm y
    exact hH ((survivesTo_iff_prefB35 y H).mpr ⟨G, hG, fun t _ => hmatch t⟩)

/-! ## 8. Equivalence with `Q01Gap`, `Q01`, and `Rule30SpacingRenormalization.finite_transfer` -/

theorem finSupp_rowOfNat (y : Nat) : FinSupp (rowOfNat y) := by
  refine ⟨y + 1, fun k hk => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  change y.testBit m = false
  apply Nat.testBit_lt_two_pow
  have hpow : m < 2 ^ m := Nat.lt_two_pow_self
  omega



theorem inB35_implies_spaced (G : Nat → Bool) (hG : InB35 G) : Spaced G := by
  intro r
  cases hr : G r with
  | false => simp
  | true =>
    obtain ⟨d, hd, _, hmid⟩ := hG.2 r hr
    rcases hd with rfl | rfl
    · have h1 := hmid 1 (by decide) (by decide)
      have h2 := hmid 2 (by decide) (by decide)
      simp [h1, h2]
    · have h1 := hmid 1 (by decide) (by decide)
      have h2 := hmid 2 (by decide) (by decide)
      simp [h1, h2]

theorem inB35_empty_zrow_iff_mass_diverges :
    (∀ L : Nat → Bool, FinSupp L → ¬ ∃ G, InB35 G ∧ ∀ t, zrow L t 1 = boundary G t) ↔
      MassDiverges := by
  rw [← inB35_empty_iff_mass_diverges]
  constructor
  · intro hL y ⟨G, hG, hb⟩
    refine hL (rowOfNat y) (finSupp_rowOfNat y) ⟨G, hG, fun t => ?_⟩
    rw [zrow_rowOfNat_col1, hb t]
  · intro hy L ⟨W, hW⟩ ⟨G, hG, hb⟩
    let y := natOfRow L W
    refine hy y ⟨G, hG, fun t => ?_⟩
    rw [← zrow_rowOfNat_col1 y t, zrow_congr (rowOfNat_natOfRow hW) t 1, hb t]

theorem inB35_empty_iff_Q01Gap :
    (∀ y : Nat, ¬ ∃ G, InB35 G ∧ ∀ t, (iter F t y).testBit 0 = boundary G t) ↔ Ruliology.CellularAutomata.Rule30GateTrap.Q01Gap := by
  constructor
  · intro h L hfin hX
    rintro ⟨s0, hgap⟩
    have hnot : ¬ ∀ s, s0 ≤ s → zrow L (2 * s + 1) 1 = true := by
      intro hall
      apply free_not_eventuallyPeriodic hfin hX
      exact ⟨s0, 1, by decide, fun s hs => by dsimp only; rw [hall (s + 1) (by omega), hall s hs]⟩
    have hex : ∃ s1, s0 ≤ s1 ∧ !zrow L (2 * s1 + 1) 1 = true :=
      Classical.byContradiction fun hne => hnot fun s hs =>
        Classical.byContradiction fun hne1 => hne ⟨s, hs, by
          cases hz : zrow L (2 * s + 1) 1 <;> simp_all⟩
    obtain ⟨s1, hs1, htrue⟩ := hex
    let G : Nat → Bool := fun r => !zrow L (2 * (s1 + r) + 1) 1
    have hG : InB35 G := by
      refine ⟨htrue, fun r hr => ?_⟩
      have hgok := hgap (s1 + r) (by omega) hr
      rcases hgok with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4, h5⟩
      · refine ⟨3, Or.inl rfl, by simpa [G, Nat.add_assoc] using h3, fun j hj1 hj2 => ?_⟩
        have hj : j = 1 ∨ j = 2 := by omega
        rcases hj with rfl | rfl
        · simpa [G, Nat.add_assoc] using h1
        · simpa [G, Nat.add_assoc] using h2
      · refine ⟨5, Or.inr rfl, by simpa [G, Nat.add_assoc] using h5, fun j hj1 hj2 => ?_⟩
        have hj : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
        rcases hj with rfl | rfl | rfl | rfl
        · simpa [G, Nat.add_assoc] using h1
        · simpa [G, Nat.add_assoc] using h2
        · simpa [G, Nat.add_assoc] using h3
        · simpa [G, Nat.add_assoc] using h4
    obtain ⟨W, hW⟩ := hfin
    let L' := zrow L (2 * s1 + 1)
    let W' := W + (2 * s1 + 1)
    have hW' : ∀ k, W' < k → L' k = false := fun k hk => zrow_fin hW (2 * s1 + 1) k hk
    let y0 := natOfRow L' W'
    refine h y0 ⟨G, hG, fun t => ?_⟩
    rw [← zrow_rowOfNat_col1 y0 t]
    have hcongr : zrow (rowOfNat y0) t 1 = zrow L' t 1 :=
      zrow_congr (rowOfNat_natOfRow hW') t 1
    rw [hcongr]
    change zrow (zrow L (2 * s1 + 1)) t 1 = boundary G t
    rw [← zrow_shift]
    rcases Nat.mod_two_eq_zero_or_one t with hm | hm
    · obtain ⟨r, rfl⟩ : ∃ r, t = 2 * r := ⟨t / 2, by omega⟩
      have hbd : boundary G (2 * r) = !(G r) := by simp [boundary]
      rw [hbd, show 2 * s1 + 1 + 2 * r = 2 * (s1 + r) + 1 by omega]
      dsimp only [G]
      cases zrow L (2 * (s1 + r) + 1) 1 <;> rfl
    · obtain ⟨r, rfl⟩ : ∃ r, t = 2 * r + 1 := ⟨t / 2, by omega⟩
      have hbd : boundary G (2 * r + 1) = true := by simp [boundary]
      rw [hbd, show 2 * s1 + 1 + (2 * r + 1) = 2 * (s1 + r + 1) by omega]
      exact hX (s1 + r + 1)
  · intro hQ y ⟨G, hG, hb⟩
    let L := zrow (rowOfNat y) 1
    obtain ⟨W, hW⟩ := finSupp_rowOfNat y
    have hfinL : FinSupp L := ⟨W + 1, fun k hk => zrow_fin hW 1 k hk⟩
    have hXL : InX L := by
      intro s
      change zrow (zrow (rowOfNat y) 1) (2 * s) 1 = true
      rw [← zrow_shift, zrow_rowOfNat_col1, hb (1 + 2 * s)]
      rw [show 1 + 2 * s = 2 * s + 1 by omega]
      simp [boundary]
    refine hQ L hfinL hXL ⟨0, fun s _ hs => ?_⟩
    have hgr : ∀ u, (!zrow L (2 * u + 1) 1) = G (u + 1) := by
      intro u
      change (!zrow (zrow (rowOfNat y) 1) (2 * u + 1) 1) = G (u + 1)
      rw [← zrow_shift, zrow_rowOfNat_col1, hb (1 + (2 * u + 1))]
      rw [show 1 + (2 * u + 1) = 2 * (u + 1) by omega]
      have hbe : boundary G (2 * (u + 1)) = !(G (u + 1)) := by simp [boundary]
      rw [hbe]
      cases G (u + 1) <;> rfl
    dsimp only at hs ⊢
    rw [hgr s] at hs
    obtain ⟨d, hd, hnext, hmid⟩ := hG.2 (s + 1) hs
    rcases hd with rfl | rfl
    · left
      refine ⟨?_, ?_, ?_⟩
      · rw [hgr (s + 1)]; exact hmid 1 (by decide) (by decide)
      · rw [hgr (s + 2)]; exact hmid 2 (by decide) (by decide)
      · rw [hgr (s + 3)]; simpa [Nat.add_assoc] using hnext
    · right
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [hgr (s + 1)]; exact hmid 1 (by decide) (by decide)
      · rw [hgr (s + 2)]; exact hmid 2 (by decide) (by decide)
      · rw [hgr (s + 3)]; exact hmid 3 (by decide) (by decide)
      · rw [hgr (s + 4)]; exact hmid 4 (by decide) (by decide)
      · rw [hgr (s + 5)]; simpa [Nat.add_assoc] using hnext

/-- Exact equivalence between `MassDiverges` and `Rule30GateTrap.Q01Gap`. -/
theorem massDiverges_iff_Q01Gap : MassDiverges ↔ Ruliology.CellularAutomata.Rule30GateTrap.Q01Gap :=
  inB35_empty_iff_mass_diverges.symm.trans inB35_empty_iff_Q01Gap

/-- `Rule30ZeroBoundary.Q01` implies `MassDiverges`. -/
theorem massDiverges_of_Q01 (hQ : Q01) : MassDiverges :=
  massDiverges_iff_Q01Gap.mpr (fun L hf hX _ => hQ L hf hX)

/-- If `MassDiverges` holds, then `CQ01Empty` holds in `Rule30PeriodTwoSideways`. -/
theorem CQ01Empty_of_massDiverges (hM : MassDiverges) :
    Ruliology.CellularAutomata.Rule30PeriodTwoSideways.CQ01Empty :=
  Ruliology.CellularAutomata.Rule30GateTrap.CQ01Empty_of_Q01Gap
    (massDiverges_iff_Q01Gap.mp hM)

/-! ## 9. Unified Equivalence and Period-2 Closure Bridge Across `Rule30ZeroCoastBridge`, `Rule30GateTrapLift`, and `Rule30PeriodTwoWidth13` -/

/-- **Unified Equivalence and Period-2 Closure Bridge Across `Rule30ZeroCoastBridge`,
`Rule30GateTrapLift`, and `Rule30PeriodTwoWidth13`
(`massDiverges_equiv_anchored_two_core_and_period_two_bridge`).**
1. `MassDiverges ↔ ZeroCoastBoxTerminationHypothesis`,
2. `MassDiverges ↔ FiniteSeedsTerminate`,
3. `MassDiverges ↔ Ruliology.CellularAutomata.Rule30GateTrap.Q01Gap`,
4. `(Ruliology.CellularAutomata.Rule30GateTrapLift.TwoCoreThetaUnbounded ↔ Ruliology.CellularAutomata.Rule30GateTrapLift.Q01TwoCoreAnchored) ∧ (Ruliology.CellularAutomata.Rule30GateTrapLift.TwoCoreThetaUnbounded ↔ Ruliology.CellularAutomata.Rule30GateTrapLift.Q01GapCore)`,
5. If `Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.RD` and `MassDiverges` hold, then `Ruliology.CellularAutomata.Rule30PeriodTwoSideways.CQ01Empty` holds
   and the center column of Rule 30 from a single black cell is never eventually period 2. -/
theorem massDiverges_equiv_anchored_two_core_and_period_two_bridge :
    (MassDiverges ↔ ZeroCoastBoxTerminationHypothesis) ∧
    (MassDiverges ↔ FiniteSeedsTerminate) ∧
    (MassDiverges ↔ Ruliology.CellularAutomata.Rule30GateTrap.Q01Gap) ∧
    ((Ruliology.CellularAutomata.Rule30GateTrapLift.TwoCoreThetaUnbounded ↔ Ruliology.CellularAutomata.Rule30GateTrapLift.Q01TwoCoreAnchored) ∧
     (Ruliology.CellularAutomata.Rule30GateTrapLift.TwoCoreThetaUnbounded ↔ Ruliology.CellularAutomata.Rule30GateTrapLift.Q01GapCore)) ∧
    (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.RD → MassDiverges →
      Ruliology.CellularAutomata.Rule30PeriodTwoSideways.CQ01Empty ∧
      ¬ ∃ T0, ∀ t, T0 ≤ t → Rule30Prize.center (t + 2) = Rule30Prize.center t) := by
  refine ⟨massDiverges_iff_zeroCoastBoxTermination,
          finite_seeds_terminate_iff_mass_diverges.symm,
          massDiverges_iff_Q01Gap,
          Ruliology.CellularAutomata.Rule30GateTrapLift.twoCoreThetaUnbounded_iff_q01GapCore_and_imp_cq01Empty,
          fun hRD hM => ⟨CQ01Empty_of_massDiverges hM,
            Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.no_eventual_period_two_of_RD_of_Q01Gap hRD (massDiverges_iff_Q01Gap.mp hM)⟩⟩

/-! ## 10. Universal Trace-to-Seed Bijection (`seedOfTrace`), Canonical Horizon Seed Family (`survivingSeeds H`), and Exact `{6, 10}` Horizon Seed-Count Law (`∀ H ≥ 1`) -/

section UniversalSeedBijectionAndCountLaw
open Rule30ZeroBoundary.IntegerForm

/-- One-step antidiagonal seed extension: given `y < 2^H` with `trace y H = w` and a target
next trace bit `b : Bool`, appends bit `H` to `y` so that `(iter F H y').testBit 0 = b`. -/
def extendSeedForBit (y H : Nat) (b : Bool) : Nat :=
  if H = 0 then
    if b then 1 else 0
  else
    let sig := sigmaList (antidiag y (H - 1)) (false :: (if H = 1 then [] else antidiag y (H - 2)))
    let bit := xor b (piParity sig)
    y + (if bit then 2 ^ H else 0)

/-- Accumulator reconstructing the unique seed `< 2^(H + bs.length)` extending `y < 2^H`
along the remaining trace suffix `bs`. -/
def seedOfTraceAux (y H : Nat) : List Bool → Nat
  | [] => y
  | b :: bs => seedOfTraceAux (extendSeedForBit y H b) (H + 1) bs

/-- Explicit constructive inverse of `trace · H`: maps any boolean word `w : List Bool`
to the unique canonical seed `y < 2^w.length` whose length-`w.length` trace is `w`. -/
def seedOfTrace (w : List Bool) : Nat :=
  seedOfTraceAux 0 0 w

theorem antidiag_congr_mod_pow2 (y1 y2 H : Nat) (hmod : y1 % 2 ^ H = y2 % 2 ^ H) :
    ∀ k < H, antidiag y1 k = antidiag y2 k := by
  intro k hk
  unfold antidiag
  refine List.map_congr_left fun j hj => ?_
  rw [List.mem_range] at hj
  have hpow : j + 1 + (k - j) ≤ H := by omega
  have hdvd : 2 ^ (j + 1 + (k - j)) ∣ 2 ^ H := Nat.pow_dvd_pow 2 hpow
  have heq1 := congrArg (fun z => z.testBit j) (iter_F_mod_pow2 (k - j) y1 (j + 1))
  have heq2 := congrArg (fun z => z.testBit j) (iter_F_mod_pow2 (k - j) y2 (j + 1))
  rw [Nat.testBit_mod_two_pow, decide_eq_true (by omega), Bool.true_and] at heq1 heq2
  have hsub1 := Nat.mod_mod_of_dvd y1 hdvd
  have hsub2 := Nat.mod_mod_of_dvd y2 hdvd
  rw [hmod] at hsub1
  rw [heq1, heq2, ← hsub1, hsub2]

theorem extendSeedForBit_spec (y H : Nat) (hy : y < 2 ^ H) (b : Bool) :
    let y' := extendSeedForBit y H b
    y' < 2 ^ (H + 1) ∧ y' % 2 ^ H = y ∧ trace y' (H + 1) = trace y H ++ [b] := by
  by_cases hH0 : H = 0
  · subst hH0
    have hy0 : y = 0 := by omega
    subst hy0
    cases b <;> decide
  · have hH1 : 1 ≤ H := by omega
    dsimp only [extendSeedForBit]
    simp only [hH0, ↓reduceIte]
    let sig := sigmaList (antidiag y (H - 1)) (false :: (if H = 1 then [] else antidiag y (H - 2)))
    let bit := xor b (piParity sig)
    let y' := y + (if bit then 2 ^ H else 0)
    have hy'Lt : y' < 2 ^ (H + 1) := by
      have hpow : 2 ^ (H + 1) = 2 ^ H + 2 ^ H := by rw [Nat.pow_succ]; omega
      dsimp only [y']
      cases bit <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
    have hy'Mod : y' % 2 ^ H = y := by
      dsimp only [y']
      cases bit
      · simpa using Nat.mod_eq_of_lt hy
      · simp [Nat.mod_eq_of_lt hy]
    have hy'BitH : y'.testBit H = bit := by
      dsimp only [y']
      rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
      cases bit
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        rw [Nat.div_eq_of_lt hy]
        decide
      · simp only [↓reduceIte]
        have hd : (y + 2 ^ H) / 2 ^ H = 1 := by
          have hpos : 0 < 2 ^ H := Nat.pow_pos (by decide)
          have hadd : y + 2 ^ H = 2 ^ H * 1 + y := by omega
          rw [hadd, Nat.mul_add_div hpos, Nat.div_eq_of_lt hy]
        rw [hd]
        decide
    have hy'ModEq : y' % 2 ^ H = y % 2 ^ H := hy'Mod.trans (Nat.mod_eq_of_lt hy).symm
    have had1 : antidiag y' (H - 1) = antidiag y (H - 1) :=
      antidiag_congr_mod_pow2 y' y H hy'ModEq (H - 1) (by omega)
    have had2 : (if H = 1 then [] else antidiag y' (H - 2)) = (if H = 1 then [] else antidiag y (H - 2)) := by
      by_cases h1 : H = 1
      · simp [h1]
      · simp only [h1, ↓reduceIte]
        exact antidiag_congr_mod_pow2 y' y H hy'ModEq (H - 2) (by omega)
    have had := antidiag_step_spec y' H hH1
    dsimp only at had
    rw [had1, had2, scanXor_snd_eq_xor_piParity, hy'BitH] at had
    have hb_eq : (iter F H y').testBit 0 = b := by
      have hx : xor ((iter F H y').testBit 0) (piParity sig) = xor b (piParity sig) := had.2
      cases h0 : (iter F H y').testBit 0 <;> cases b <;> cases piParity sig <;> simp_all
    have htr : trace y' (H + 1) = trace y H ++ [b] := by
      rw [trace_succ_right y' H, ← trace_mod_pow2 y' H, hy'Mod, hb_eq]
    exact ⟨hy'Lt, hy'Mod, htr⟩

theorem seedOfTraceAux_spec (bs : List Bool) (y H : Nat) (hy : y < 2 ^ H) :
    seedOfTraceAux y H bs < 2 ^ (H + bs.length) ∧
    trace (seedOfTraceAux y H bs) (H + bs.length) = trace y H ++ bs := by
  induction bs generalizing y H with
  | nil =>
    simp [seedOfTraceAux, hy]
  | cons b bs ih =>
    simp only [seedOfTraceAux, List.length_cons]
    obtain ⟨hy', _, htr'⟩ := extendSeedForBit_spec y H hy b
    obtain ⟨h1, h2⟩ := ih (extendSeedForBit y H b) (H + 1) hy'
    rw [show H + 1 + bs.length = H + (bs.length + 1) by omega] at h1 h2
    rw [htr', List.append_assoc, List.singleton_append] at h2
    exact ⟨h1, h2⟩

theorem seedOfTrace_spec (w : List Bool) :
    seedOfTrace w < 2 ^ w.length ∧ trace (seedOfTrace w) w.length = w := by
  have h := seedOfTraceAux_spec w 0 0 (by decide)
  simpa [seedOfTrace, trace] using h

theorem antidiag_and_bits_eq_of_trace_eq (y1 y2 H : Nat) (htr : trace y1 H = trace y2 H) :
    ∀ n < H, antidiag y1 n = antidiag y2 n ∧ y1.testBit n = y2.testBit n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    have hb0 : (iter F n y1).testBit 0 = (iter F n y2).testBit 0 := by
      simp only [← trace_getElem y1 H n hn, ← trace_getElem y2 H n hn, htr]
    by_cases hn0 : n = 0
    · subst hn0
      have hbit0 : y1.testBit 0 = y2.testBit 0 := by simpa [iter] using hb0
      refine ⟨?_, hbit0⟩
      simp [antidiag, iter, hbit0]
    · have hn1 : 1 ≤ n := by omega
      have had1 : antidiag y1 (n - 1) = antidiag y2 (n - 1) := (ih (n - 1) (by omega) (by omega)).1
      have had2 : (if n = 1 then [] else antidiag y1 (n - 2)) = (if n = 1 then [] else antidiag y2 (n - 2)) := by
        by_cases h1 : n = 1
        · simp [h1]
        · simp only [h1, ↓reduceIte]
          exact (ih (n - 2) (by omega) (by omega)).1
      have hs1 := antidiag_step_spec y1 n hn1
      have hs2 := antidiag_step_spec y2 n hn1
      dsimp only at hs1 hs2
      rw [hb0, had1, had2] at hs1
      exact ⟨hs1.1.symm.trans hs2.1, hs1.2.symm.trans hs2.2⟩

/-- **Universal Trace-to-Seed Bijection (`trace_eq_iff_mod_pow2_eq_and_seedOfTrace_bijection`).**
For every horizon `H : Nat`, `trace · H` and `seedOfTrace` form a constructive bijection between
canonical seed prefixes `y < 2^H` and length-`H` boolean trace words `w : List Bool`:
1. `trace y1 H = trace y2 H ↔ y1 % 2^H = y2 % 2^H`,
2. `seedOfTrace w < 2^w.length ∧ trace (seedOfTrace w) w.length = w`,
3. `seedOfTrace (trace y H) = y % 2^H` (and `= y` whenever `y < 2^H`). -/
theorem trace_eq_iff_mod_pow2_eq_and_seedOfTrace_bijection (H y1 y2 : Nat) (w : List Bool) :
    (trace y1 H = trace y2 H ↔ y1 % 2 ^ H = y2 % 2 ^ H) ∧
    (seedOfTrace w < 2 ^ w.length ∧ trace (seedOfTrace w) w.length = w) ∧
    seedOfTrace (trace y1 H) = y1 % 2 ^ H := by
  have hinj : ∀ z1 z2 : Nat, trace z1 H = trace z2 H ↔ z1 % 2 ^ H = z2 % 2 ^ H := by
    intro z1 z2
    constructor
    · intro htr
      apply Nat.eq_of_testBit_eq
      intro n
      rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
      by_cases hn : n < H
      · simp [hn, (antidiag_and_bits_eq_of_trace_eq z1 z2 H htr n hn).2]
      · simp [hn]
    · intro hmod
      rw [← trace_mod_pow2 z1 H, ← trace_mod_pow2 z2 H, hmod]
  refine ⟨hinj y1 y2, seedOfTrace_spec w, ?_⟩
  obtain ⟨hlt1, htr1⟩ := seedOfTrace_spec (trace y1 H)
  rw [trace_length] at hlt1 htr1
  have hmod_eq : seedOfTrace (trace y1 H) % 2 ^ H = y1 % 2 ^ H := (hinj _ _).mp htr1
  rw [Nat.mod_eq_of_lt hlt1] at hmod_eq
  exact hmod_eq

/-- Recursive generator of all trace suffixes of length `k` accepted by `acceptRest isOdd age`. -/
def acceptRestWords : Bool → Nat → Nat → List (List Bool)
  | _, _, 0 => [[]]
  | true, a, k + 1 => (acceptRestWords false a k).map (true :: ·)
  | false, 0, k + 1 => (acceptRestWords true 1 k).map (true :: ·)
  | false, 1, k + 1 => (acceptRestWords true 2 k).map (true :: ·)
  | false, 2, k + 1 =>
      (acceptRestWords true 3 k).map (true :: ·) ++
      (acceptRestWords true 0 k).map (false :: ·)
  | false, 3, k + 1 => (acceptRestWords true 4 k).map (true :: ·)
  | false, 4, k + 1 => (acceptRestWords true 0 k).map (false :: ·)
  | false, _ + 5, _ + 1 => []

/-- Recursive generator of all accepted trace words of length `H` (`accept w = true`). -/
def acceptedWords : Nat → List (List Bool)
  | 0 => [[]]
  | k + 1 => (acceptRestWords true 0 k).map (false :: ·)

/-- Universal canonical surviving-seed list at horizon `H : Nat`. -/
def survivingSeeds (H : Nat) : List Nat :=
  (acceptedWords H).map seedOfTrace

theorem mem_acceptRestWords_iff (k : Nat) :
    ∀ (isOdd : Bool) (a : Nat) (_ha : a < 5) (w : List Bool),
      w ∈ acceptRestWords isOdd a k ↔ (w.length = k ∧ acceptRest isOdd a w = true) := by
  induction k with
  | zero =>
    intro isOdd a _ w
    simp only [acceptRestWords, List.mem_singleton]
    constructor
    · rintro rfl; exact ⟨rfl, rfl⟩
    · rintro ⟨hlen, _⟩; exact List.eq_nil_of_length_eq_zero hlen
  | succ k ih =>
    intro isOdd a _ha w
    cases isOdd with
    | true =>
      simp only [acceptRestWords, List.mem_map]
      constructor
      · rintro ⟨w', hw', rfl⟩
        obtain ⟨hl, hacc⟩ := (ih false a _ha w').mp hw'
        exact ⟨by simp [hl], by simp [acceptRest, hacc]⟩
      · rintro ⟨hlen, hacc⟩
        cases w with
        | nil => simp at hlen
        | cons b w' =>
          simp only [acceptRest, Bool.and_eq_true] at hacc
          rcases hacc with ⟨rfl, hacc'⟩
          refine ⟨w', (ih false a _ha w').mpr ⟨by simp at hlen; omega, hacc'⟩, rfl⟩
    | false =>
      match a, _ha with
      | 0, _ =>
        simp only [acceptRestWords, List.mem_map]
        constructor
        · rintro ⟨w', hw', rfl⟩
          obtain ⟨hl, hacc⟩ := (ih true 1 (by decide) w').mp hw'
          exact ⟨by simp [hl], by simp [acceptRest, gateNext, hacc]⟩
        · rintro ⟨hlen, hacc⟩
          cases w with
          | nil => simp at hlen
          | cons b w' =>
            cases b
            · simp [acceptRest, gateNext] at hacc
            · simp only [acceptRest, gateNext] at hacc
              exact ⟨w', (ih true 1 (by decide) w').mpr ⟨by simp at hlen; omega, hacc⟩, rfl⟩
      | 1, _ =>
        simp only [acceptRestWords, List.mem_map]
        constructor
        · rintro ⟨w', hw', rfl⟩
          obtain ⟨hl, hacc⟩ := (ih true 2 (by decide) w').mp hw'
          exact ⟨by simp [hl], by simp [acceptRest, gateNext, hacc]⟩
        · rintro ⟨hlen, hacc⟩
          cases w with
          | nil => simp at hlen
          | cons b w' =>
            cases b
            · simp [acceptRest, gateNext] at hacc
            · simp only [acceptRest, gateNext] at hacc
              exact ⟨w', (ih true 2 (by decide) w').mpr ⟨by simp at hlen; omega, hacc⟩, rfl⟩
      | 2, _ =>
        simp only [acceptRestWords, List.mem_append, List.mem_map]
        constructor
        · rintro (⟨w', hw', rfl⟩ | ⟨w', hw', rfl⟩)
          · obtain ⟨hl, hacc⟩ := (ih true 3 (by decide) w').mp hw'
            exact ⟨by simp [hl], by simp [acceptRest, gateNext, hacc]⟩
          · obtain ⟨hl, hacc⟩ := (ih true 0 (by decide) w').mp hw'
            exact ⟨by simp [hl], by simp [acceptRest, gateNext, hacc]⟩
        · rintro ⟨hlen, hacc⟩
          cases w with
          | nil => simp at hlen
          | cons b w' =>
            cases b
            · simp only [acceptRest, gateNext] at hacc
              exact Or.inr ⟨w', (ih true 0 (by decide) w').mpr ⟨by simp at hlen; omega, hacc⟩, rfl⟩
            · simp only [acceptRest, gateNext] at hacc
              exact Or.inl ⟨w', (ih true 3 (by decide) w').mpr ⟨by simp at hlen; omega, hacc⟩, rfl⟩
      | 3, _ =>
        simp only [acceptRestWords, List.mem_map]
        constructor
        · rintro ⟨w', hw', rfl⟩
          obtain ⟨hl, hacc⟩ := (ih true 4 (by decide) w').mp hw'
          exact ⟨by simp [hl], by simp [acceptRest, gateNext, hacc]⟩
        · rintro ⟨hlen, hacc⟩
          cases w with
          | nil => simp at hlen
          | cons b w' =>
            cases b
            · simp [acceptRest, gateNext] at hacc
            · simp only [acceptRest, gateNext] at hacc
              exact ⟨w', (ih true 4 (by decide) w').mpr ⟨by simp at hlen; omega, hacc⟩, rfl⟩
      | 4, _ =>
        simp only [acceptRestWords, List.mem_map]
        constructor
        · rintro ⟨w', hw', rfl⟩
          obtain ⟨hl, hacc⟩ := (ih true 0 (by decide) w').mp hw'
          exact ⟨by simp [hl], by simp [acceptRest, gateNext, hacc]⟩
        · rintro ⟨hlen, hacc⟩
          cases w with
          | nil => simp at hlen
          | cons b w' =>
            cases b
            · simp only [acceptRest, gateNext] at hacc
              exact ⟨w', (ih true 0 (by decide) w').mpr ⟨by simp at hlen; omega, hacc⟩, rfl⟩
            · simp [acceptRest, gateNext] at hacc
      | _ + 5, _ha => omega

theorem mem_acceptedWords_iff (H : Nat) (w : List Bool) :
    w ∈ acceptedWords H ↔ (w.length = H ∧ accept w = true) := by
  cases H with
  | zero =>
    simp only [acceptedWords, List.mem_singleton]
    constructor
    · rintro rfl; exact ⟨rfl, rfl⟩
    · rintro ⟨hlen, _⟩; exact List.eq_nil_of_length_eq_zero hlen
  | succ k =>
    simp only [acceptedWords, List.mem_map]
    constructor
    · rintro ⟨w', hw', rfl⟩
      obtain ⟨hl, hacc⟩ := (mem_acceptRestWords_iff k true 0 (by decide) w').mp hw'
      exact ⟨by simp [hl], by simp [accept, hacc]⟩
    · rintro ⟨hlen, hacc⟩
      cases w with
      | nil => simp at hlen
      | cons b w' =>
        cases b
        · simp only [accept, Bool.not_false, Bool.true_and] at hacc
          exact ⟨w', (mem_acceptRestWords_iff k true 0 (by decide) w').mpr ⟨by simp at hlen; omega, hacc⟩, rfl⟩
        · simp [accept] at hacc

/-- **Universal Canonical Seed Characterization at Every Horizon `H`
(`mem_survivingSeeds_iff_and_survivesTo_iff`).**
For every horizon `H : Nat` and every seed `y : Nat`:
1. `y ∈ survivingSeeds H ↔ (y < 2 ^ H ∧ SurvivesTo y H)`,
2. `SurvivesTo y H ↔ y % 2 ^ H ∈ survivingSeeds H`. -/
theorem mem_survivingSeeds_iff_and_survivesTo_iff (H y : Nat) :
    (y ∈ survivingSeeds H ↔ (y < 2 ^ H ∧ SurvivesTo y H)) ∧
    (SurvivesTo y H ↔ y % 2 ^ H ∈ survivingSeeds H) := by
  have h1 : ∀ z : Nat, z ∈ survivingSeeds H ↔ (z < 2 ^ H ∧ SurvivesTo z H) := by
    intro z
    unfold survivingSeeds SurvivesTo
    simp only [List.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨hlen, hacc⟩ := (mem_acceptedWords_iff H w).mp hw
      obtain ⟨hlt, htr⟩ := seedOfTrace_spec w
      rw [hlen] at hlt htr
      rw [htr]
      exact ⟨hlt, hacc⟩
    · rintro ⟨hlt, hacc⟩
      refine ⟨trace z H, (mem_acceptedWords_iff H (trace z H)).mpr ⟨trace_length z H, hacc⟩, ?_⟩
      have hbij := (trace_eq_iff_mod_pow2_eq_and_seedOfTrace_bijection H z z []).2.2
      rw [Nat.mod_eq_of_lt hlt] at hbij
      exact hbij
  refine ⟨h1 y, ?_⟩
  rw [h1 (y % 2 ^ H)]
  have hlt : y % 2 ^ H < 2 ^ H := Nat.mod_lt y (Nat.pow_pos (by decide))
  rw [← survivesTo_mod_pow2 y H]
  exact ⟨fun hs => ⟨hlt, hs⟩, fun ⟨_, hs⟩ => hs⟩

theorem acceptRestWords_zero_add_ten (k : Nat) :
    (acceptRestWords true 0 (k + 10)).length =
      (acceptRestWords true 0 (k + 4)).length + (acceptRestWords true 0 k).length := by
  have hstep1 : ∀ m, (acceptRestWords true 0 (m + 1)).length = (acceptRestWords false 0 m).length := by
    intro m; simp [acceptRestWords]
  have hstep2 : ∀ m, (acceptRestWords false 0 (m + 1)).length = (acceptRestWords true 1 m).length := by
    intro m; simp [acceptRestWords]
  have hstep3 : ∀ m, (acceptRestWords true 1 (m + 1)).length = (acceptRestWords false 1 m).length := by
    intro m; simp [acceptRestWords]
  have hstep4 : ∀ m, (acceptRestWords false 1 (m + 1)).length = (acceptRestWords true 2 m).length := by
    intro m; simp [acceptRestWords]
  have hstep5 : ∀ m, (acceptRestWords true 2 (m + 1)).length = (acceptRestWords false 2 m).length := by
    intro m; simp [acceptRestWords]
  have hstep6 : ∀ m, (acceptRestWords false 2 (m + 1)).length =
      (acceptRestWords true 3 m).length + (acceptRestWords true 0 m).length := by
    intro m; simp [acceptRestWords]
  have hstep7 : ∀ m, (acceptRestWords true 3 (m + 1)).length = (acceptRestWords false 3 m).length := by
    intro m; simp [acceptRestWords]
  have hstep8 : ∀ m, (acceptRestWords false 3 (m + 1)).length = (acceptRestWords true 4 m).length := by
    intro m; simp [acceptRestWords]
  have hstep9 : ∀ m, (acceptRestWords true 4 (m + 1)).length = (acceptRestWords false 4 m).length := by
    intro m; simp [acceptRestWords]
  have hstep10 : ∀ m, (acceptRestWords false 4 (m + 1)).length = (acceptRestWords true 0 m).length := by
    intro m; simp [acceptRestWords]
  rw [show k + 10 = (k + 9) + 1 by omega, hstep1 (k + 9),
      show k + 9 = (k + 8) + 1 by omega, hstep2 (k + 8),
      show k + 8 = (k + 7) + 1 by omega, hstep3 (k + 7),
      show k + 7 = (k + 6) + 1 by omega, hstep4 (k + 6),
      show k + 6 = (k + 5) + 1 by omega, hstep5 (k + 5),
      show k + 5 = (k + 4) + 1 by omega, hstep6 (k + 4),
      show k + 4 = (k + 3) + 1 by omega, hstep7 (k + 3),
      show k + 3 = (k + 2) + 1 by omega, hstep8 (k + 2),
      show k + 2 = (k + 1) + 1 by omega, hstep9 (k + 1),
      hstep10 k, Nat.add_comm]

/-- **Universal `{6, 10}` Horizon Seed-Count Law (`survivingSeeds_length_add_ten_and_initial_counts`).**
For every positive horizon `H ≥ 1`, the number of canonical surviving seeds `(survivingSeeds H).length`
satisfies the exact delay recurrence:
`(survivingSeeds (H + 10)).length = (survivingSeeds (H + 4)).length + (survivingSeeds H).length`,
with initial values `[1, 1, 1, 1, 1, 2, 2, 2, 2, 3]` on `H = 1..10` (yielding `1, 2, 4, 7, 12, 20, 33`
at `H = 6, 12, 18, 24, 30, 36, 42` and `55` at `H = 48`). -/
theorem survivingSeeds_length_add_ten_and_initial_counts :
    (∀ H : Nat, 1 ≤ H →
      (survivingSeeds (H + 10)).length = (survivingSeeds (H + 4)).length + (survivingSeeds H).length) ∧
    ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10].map (fun H => (survivingSeeds H).length) =
      [1, 1, 1, 1, 1, 1, 2, 2, 2, 2]) ∧
    ([6, 12, 18, 24, 30, 36, 42, 48].map (fun H => (survivingSeeds H).length) =
      [1, 2, 4, 7, 12, 20, 33, 55]) := by
  refine ⟨fun H hH => ?_, by decide, by decide⟩
  obtain ⟨k, rfl⟩ : ∃ k, H = k + 1 := ⟨H - 1, by omega⟩
  have h10 : k + 1 + 10 = (k + 10) + 1 := by omega
  have h4 : k + 1 + 4 = (k + 4) + 1 := by omega
  rw [h10, h4]
  simp only [survivingSeeds, acceptedWords, List.length_map]
  exact acceptRestWords_zero_add_ten k

theorem nodup_map_cons (b : Bool) {xs : List (List Bool)} (h : xs.Nodup) :
    (xs.map (b :: ·)).Nodup := by
  induction h with
  | nil => exact List.Pairwise.nil
  | @cons w ws hw hnodup ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map]
    refine ⟨?_, ih⟩
    rintro ⟨w', hw', hcons⟩
    injection hcons with _ heq
    subst heq
    exact hw w' hw' rfl

theorem nodup_acceptRestWords (k : Nat) :
    ∀ (isOdd : Bool) (a : Nat), (acceptRestWords isOdd a k).Nodup := by
  induction k with
  | zero =>
    intro isOdd a
    simp [acceptRestWords]
  | succ k ih =>
    intro isOdd a
    cases isOdd with
    | true =>
      exact nodup_map_cons true (ih false a)
    | false =>
      match a with
      | 0 => exact nodup_map_cons true (ih true 1)
      | 1 => exact nodup_map_cons true (ih true 2)
      | 2 =>
        simp only [acceptRestWords]
        refine List.nodup_append.mpr ⟨nodup_map_cons true (ih true 3), nodup_map_cons false (ih true 0), ?_⟩
        intro w1 hw1 w2 hw2 heq
        simp only [List.mem_map] at hw1 hw2
        rcases hw1 with ⟨u1, _, rfl⟩
        rcases hw2 with ⟨u2, _, rfl⟩
        cases heq
      | 3 => exact nodup_map_cons true (ih true 4)
      | 4 => exact nodup_map_cons false (ih true 0)
      | _ + 5 => simp [acceptRestWords]

theorem nodup_acceptedWords (H : Nat) : (acceptedWords H).Nodup := by
  cases H with
  | zero => simp [acceptedWords]
  | succ k => exact nodup_map_cons false (nodup_acceptRestWords k true 0)

theorem nodup_map_on {α β : Type} (f : α → β) {xs : List α}
    (h : xs.Nodup) (hinj : ∀ x ∈ xs, ∀ y ∈ xs, f x = f y → x = y) :
    (xs.map f).Nodup := by
  induction h with
  | nil => exact List.Pairwise.nil
  | @cons x xs hx hnodup ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map]
    refine ⟨?_, ih (fun a ha b hb hab => hinj a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem x hb) hab)⟩
    rintro ⟨y, hy, hfy⟩
    have heq : y = x := hinj y (List.mem_cons_of_mem x hy) x (List.mem_cons_self) hfy
    subst heq
    exact hx y hy rfl

/-- **Universal Duplicate-Freeness of `survivingSeeds H` (`nodup_survivingSeeds`).**
For every horizon `H : Nat`, `survivingSeeds H` is duplicate-free (`(survivingSeeds H).Nodup`),
so `(survivingSeeds H).length` is the exact cardinality of `{y < 2 ^ H | SurvivesTo y H}`. -/
theorem nodup_survivingSeeds (H : Nat) : (survivingSeeds H).Nodup := by
  unfold survivingSeeds
  refine nodup_map_on seedOfTrace (nodup_acceptedWords H) ?_
  intro w1 hw1 w2 hw2 heq
  obtain ⟨hlen1, _⟩ := (mem_acceptedWords_iff H w1).mp hw1
  obtain ⟨hlen2, _⟩ := (mem_acceptedWords_iff H w2).mp hw2
  have htr1 := (seedOfTrace_spec w1).2
  have htr2 := (seedOfTrace_spec w2).2
  rw [hlen1] at htr1
  rw [hlen2] at htr2
  rw [← htr1, ← htr2, heq]

end UniversalSeedBijectionAndCountLaw

end Rule30ZeroCoastBridge
end Ruliology.CellularAutomata
