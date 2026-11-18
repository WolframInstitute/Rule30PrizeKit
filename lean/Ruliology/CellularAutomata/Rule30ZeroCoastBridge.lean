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

/-! ## 11. Universal Deterministic Odd-to-Even Seed Extension, Reset-Gate Shift Invariance, 5-Even-Step Reset Window, and `SurvivesTo → GE2` Embedding -/

section UniversalResetShiftAndGE2Bridge
open Rule30ZeroBoundary.IntegerForm

theorem acceptRestWords_odd_succ (k : Nat) :
    ∀ a : Nat, acceptRestWords true a (2 * k + 1) =
      (acceptRestWords true a (2 * k)).map (· ++ [true]) := by
  have ht : ∀ a m, acceptRestWords true a (m + 1) = (acceptRestWords false a m).map (true :: ·) :=
    fun _ _ => rfl
  have hf0 : ∀ m, acceptRestWords false 0 (m + 1) = (acceptRestWords true 1 m).map (true :: ·) :=
    fun _ => rfl
  have hf1 : ∀ m, acceptRestWords false 1 (m + 1) = (acceptRestWords true 2 m).map (true :: ·) :=
    fun _ => rfl
  have hf2 : ∀ m, acceptRestWords false 2 (m + 1) =
      (acceptRestWords true 3 m).map (true :: ·) ++ (acceptRestWords true 0 m).map (false :: ·) :=
    fun _ => rfl
  have hf3 : ∀ m, acceptRestWords false 3 (m + 1) = (acceptRestWords true 4 m).map (true :: ·) :=
    fun _ => rfl
  have hf4 : ∀ m, acceptRestWords false 4 (m + 1) = (acceptRestWords true 0 m).map (false :: ·) :=
    fun _ => rfl
  induction k with
  | zero =>
    intro a
    simp [acceptRestWords]
  | succ k ih =>
    intro a
    have h1 : 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 := by omega
    have h2 : 2 * (k + 1) = (2 * k) + 1 + 1 := by omega
    rw [h1, h2]
    match a with
    | 0 =>
      rw [ht 0 (2 * k + 1 + 1), hf0 (2 * k + 1), ht 0 (2 * k + 1), hf0 (2 * k), ih 1]
      simp [List.map_map]
    | 1 =>
      rw [ht 1 (2 * k + 1 + 1), hf1 (2 * k + 1), ht 1 (2 * k + 1), hf1 (2 * k), ih 2]
      simp [List.map_map]
    | 2 =>
      rw [ht 2 (2 * k + 1 + 1), hf2 (2 * k + 1), ht 2 (2 * k + 1), hf2 (2 * k), ih 3, ih 0]
      simp only [List.map_append, List.map_map]
      rfl
    | 3 =>
      rw [ht 3 (2 * k + 1 + 1), hf3 (2 * k + 1), ht 3 (2 * k + 1), hf3 (2 * k), ih 4]
      simp [List.map_map]
    | 4 =>
      rw [ht 4 (2 * k + 1 + 1), hf4 (2 * k + 1), ht 4 (2 * k + 1), hf4 (2 * k), ih 0]
      simp [List.map_map]
    | _ + 5 =>
      simp [acceptRestWords]

theorem seedOfTraceAux_append (bs1 bs2 : List Bool) (y H : Nat) :
    seedOfTraceAux y H (bs1 ++ bs2) =
      seedOfTraceAux (seedOfTraceAux y H bs1) (H + bs1.length) bs2 := by
  induction bs1 generalizing y H with
  | nil => simp [seedOfTraceAux]
  | cons b bs1 ih =>
    simp only [List.cons_append, seedOfTraceAux, List.length_cons]
    rw [ih (extendSeedForBit y H b) (H + 1)]
    congr 1
    omega

theorem seedOfTrace_append_singleton (w : List Bool) (b : Bool) :
    seedOfTrace (w ++ [b]) = extendSeedForBit (seedOfTrace w) w.length b := by
  unfold seedOfTrace
  rw [seedOfTraceAux_append w [b] 0 0]
  simp [seedOfTraceAux]

/-- **Universal Deterministic Odd-to-Even Horizon Extension (`survivingSeeds_two_mul_add_two`).**
For every `m : Nat`, passing from odd horizon `2 * m + 1` to even horizon `2 * m + 2`
branches no traces and no seeds:
1. `acceptedWords (2 * m + 2) = (acceptedWords (2 * m + 1)).map (· ++ [true])`,
2. `survivingSeeds (2 * m + 2) = (survivingSeeds (2 * m + 1)).map (fun y => extendSeedForBit y (2 * m + 1) true)`,
3. `(survivingSeeds (2 * m + 2)).length = (survivingSeeds (2 * m + 1)).length`. -/
theorem survivingSeeds_two_mul_add_two (m : Nat) :
    acceptedWords (2 * m + 2) = (acceptedWords (2 * m + 1)).map (· ++ [true]) ∧
    survivingSeeds (2 * m + 2) =
      (survivingSeeds (2 * m + 1)).map (fun y => extendSeedForBit y (2 * m + 1) true) ∧
    (survivingSeeds (2 * m + 2)).length = (survivingSeeds (2 * m + 1)).length := by
  have hacc : acceptedWords (2 * m + 2) = (acceptedWords (2 * m + 1)).map (· ++ [true]) := by
    change (acceptRestWords true 0 (2 * m + 1)).map (false :: ·) =
      ((acceptRestWords true 0 (2 * m)).map (false :: ·)).map (· ++ [true])
    rw [acceptRestWords_odd_succ m 0, List.map_map, List.map_map]
    rfl
  have hseeds : survivingSeeds (2 * m + 2) =
      (survivingSeeds (2 * m + 1)).map (fun y => extendSeedForBit y (2 * m + 1) true) := by
    unfold survivingSeeds
    rw [hacc, List.map_map, List.map_map]
    refine List.map_congr_left fun w hw => ?_
    obtain ⟨hlen, _⟩ := (mem_acceptedWords_iff (2 * m + 1) w).mp hw
    rw [Function.comp_apply, Function.comp_apply, seedOfTrace_append_singleton, hlen]
  refine ⟨hacc, hseeds, ?_⟩
  rw [hseeds, List.length_map]

theorem acceptRest_odd_prefix (m : Nat) :
    ∀ (u v : List Bool) (a : Nat),
      u.length = 2 * m + 1 →
      a < 5 →
      acceptRest true a (u ++ v) = true →
      ∃ a' < 5, acceptRest false a' v = true := by
  induction m with
  | zero =>
    intro u v a hlen ha hacc
    cases u with
    | nil => simp at hlen
    | cons b1 u1 =>
      cases u1 with
      | cons _ _ => simp at hlen
      | nil =>
        simp only [List.singleton_append, acceptRest, Bool.and_eq_true] at hacc
        exact ⟨a, ha, hacc.2⟩
  | succ m ih =>
    intro u v a hlen ha hacc
    cases u with
    | nil => simp at hlen
    | cons b1 u1 =>
      cases u1 with
      | nil => simp at hlen
      | cons b2 u2 =>
        have hlen2 : u2.length = 2 * m + 1 := by simp at hlen; omega
        simp only [List.cons_append, acceptRest, Bool.and_eq_true] at hacc
        rcases hacc with ⟨_, hacc2⟩
        match a, ha, b2 with
        | 0, _, true => exact ih u2 v 1 hlen2 (by decide) (by simpa [gateNext] using hacc2)
        | 0, _, false => simp [gateNext] at hacc2
        | 1, _, true => exact ih u2 v 2 hlen2 (by decide) (by simpa [gateNext] using hacc2)
        | 1, _, false => simp [gateNext] at hacc2
        | 2, _, true => exact ih u2 v 3 hlen2 (by decide) (by simpa [gateNext] using hacc2)
        | 2, _, false => exact ih u2 v 0 hlen2 (by decide) (by simpa [gateNext] using hacc2)
        | 3, _, true => exact ih u2 v 4 hlen2 (by decide) (by simpa [gateNext] using hacc2)
        | 3, _, false => simp [gateNext] at hacc2
        | 4, _, true => simp [gateNext] at hacc2
        | 4, _, false => exact ih u2 v 0 hlen2 (by decide) (by simpa [gateNext] using hacc2)
        | _ + 5, ha, _ => omega

theorem iter_F_succ_right (A y : Nat) : iter F A (F y) = iter F (A + 1) y := by
  induction A generalizing y with
  | zero => rfl
  | succ A ih => simp [iter, ih y]

theorem iter_F_add (A B y : Nat) : iter F (A + B) y = iter F B (iter F A y) := by
  induction B with
  | zero => simp [iter]
  | succ B ih => simp [iter, ih]

theorem trace_add (y A B : Nat) :
    trace y (A + B) = trace y A ++ trace (iter F A y) B := by
  induction B with
  | zero => simp [trace]
  | succ B ih =>
    rw [Nat.add_succ, trace_succ_right, ih, trace_succ_right, List.append_assoc, iter_F_add]

theorem trace_succ_left_eq (y k : Nat) :
    trace y (k + 1) = y.testBit 0 :: trace (F y) k := by
  rw [show k + 1 = 1 + k by omega, trace_add y 1 k]; rfl

/-- **Universal Reset-Gate Shift Invariance (`survivesTo_shift_at_even_zero`).**
For every seed `y : Nat`, every even step `2 * r`, and every remaining horizon `K : Nat`:
if `SurvivesTo y (2 * r + K)` holds and `(iter F (2 * r) y).testBit 0 = false`, then
`SurvivesTo (iter F (2 * r) y) K` holds and `(iter F (2 * r) y) % 2^K ∈ survivingSeeds K`. -/
theorem survivesTo_shift_at_even_zero (y r K : Nat)
    (hsurv : SurvivesTo y (2 * r + K))
    (hzero : (iter F (2 * r) y).testBit 0 = false) :
    SurvivesTo (iter F (2 * r) y) K ∧ (iter F (2 * r) y) % 2 ^ K ∈ survivingSeeds K := by
  have hmain : SurvivesTo (iter F (2 * r) y) K := by
    cases K with
    | zero => rfl
    | succ k =>
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · simpa [iter] using hsurv
      · unfold SurvivesTo at hsurv ⊢
        have hsplit : 2 * r + (k + 1) = 1 + (2 * r - 1) + (k + 1) := by omega
        rw [hsplit, trace_add y (1 + (2 * r - 1)) (k + 1), trace_add y 1 (2 * r - 1), List.append_assoc] at hsurv
        have htr1 : trace y 1 = [y.testBit 0] := rfl
        have htr2 : trace (iter F (1 + (2 * r - 1)) y) (k + 1) =
            false :: trace (F (iter F (2 * r) y)) k := by
          rw [show 1 + (2 * r - 1) = 2 * r by omega, trace_succ_left_eq, hzero]
        rw [htr1, htr2, List.singleton_append] at hsurv
        simp only [accept, Bool.and_eq_true, Bool.not_eq_true'] at hsurv
        rcases hsurv with ⟨_, hrest⟩
        have hlen_u : (trace (iter F 1 y) (2 * r - 1)).length = 2 * (r - 1) + 1 := by
          rw [trace_length]; omega
        obtain ⟨a', ha', hv⟩ := acceptRest_odd_prefix (r - 1)
          (trace (iter F 1 y) (2 * r - 1)) (false :: trace (F (iter F (2 * r) y)) k) 0 hlen_u (by decide) hrest
        have hv0 : acceptRest true 0 (trace (F (iter F (2 * r) y)) k) = true := by
          match a', ha' with
          | 0, _ => simp [acceptRest, gateNext] at hv
          | 1, _ => simp [acceptRest, gateNext] at hv
          | 2, _ => simpa [acceptRest, gateNext] using hv
          | 3, _ => simp [acceptRest, gateNext] at hv
          | 4, _ => simpa [acceptRest, gateNext] using hv
          | _ + 5, ha' => omega
        rw [trace_succ_left_eq, hzero]
        simp [accept, hv0]
  exact ⟨hmain, (mem_survivingSeeds_iff_and_survivesTo_iff K (iter F (2 * r) y)).2.mp hmain⟩

theorem acceptRest_false_five_even_steps (a : Nat) (ha : a < 5)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool) (rest : List Bool)
    (h : acceptRest false a (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: rest) = true) :
    b0 = false ∨ b2 = false ∨ b4 = false ∨ b6 = false ∨ b8 = false := by
  cases b0
  · exact Or.inl rfl
  · cases b2
    · exact Or.inr (Or.inl rfl)
    · cases b4
      · exact Or.inr (Or.inr (Or.inl rfl))
      · cases b6
        · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
        · cases b8
          · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
          · exfalso
            revert h
            match a, ha with
            | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ =>
              cases b1 <;> cases b3 <;> cases b5 <;> cases b7 <;> simp [acceptRest, gateNext]
            | _ + 5, ha => omega

/-- **Universal 5-Even-Step (10-Step) Reset Window (`survivesTo_exists_reset_in_five_even_steps`).**
Along every surviving trajectory `SurvivesTo y (2 * r + 8 + K)` with `1 ≤ K`, at least one of the
5 consecutive even steps `2 * (r + d)` (`d ∈ {0, 1, 2, 3, 4}`) is a reset gate where
`(iter F (2 * (r + d)) y).testBit 0 = false`, `SurvivesTo (iter F (2 * (r + d)) y) (8 - 2 * d + K)` holds,
and `(iter F (2 * (r + d)) y) % 2^K ∈ survivingSeeds K`. -/
theorem survivesTo_exists_reset_in_five_even_steps (y r K : Nat) (hK : 1 ≤ K)
    (hsurv : SurvivesTo y (2 * r + 8 + K)) :
    ∃ d < 5,
      (iter F (2 * (r + d)) y).testBit 0 = false ∧
      SurvivesTo (iter F (2 * (r + d)) y) K ∧
      (iter F (2 * (r + d)) y) % 2 ^ K ∈ survivingSeeds K := by
  by_cases hz0 : (iter F (2 * r) y).testBit 0 = false
  · have hsurv0 : SurvivesTo y (2 * r + K) :=
      survivesTo_mono (by omega : 2 * r + K ≤ 2 * r + 8 + K) hsurv
    obtain ⟨hs, hm⟩ := survivesTo_shift_at_even_zero y r K hsurv0 hz0
    exact ⟨0, by decide, by simpa using hz0, by simpa using hs, by simpa using hm⟩
  · have hr : 0 < r := by
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · exfalso
        have h1 : SurvivesTo y 1 := survivesTo_mono (by omega : 1 ≤ 2 * 0 + 8 + K) hsurv
        unfold SurvivesTo trace at h1
        simp [accept, iter] at h1 hz0
        omega
      · exact hr
    have hsplit : 2 * r + 8 + K = 1 + (2 * r - 1) + (8 + K) := by omega
    have hsurv' := hsurv
    unfold SurvivesTo at hsurv'
    rw [hsplit, trace_add y (1 + (2 * r - 1)) (8 + K), trace_add y 1 (2 * r - 1), List.append_assoc] at hsurv'
    have htr1 : trace y 1 = [y.testBit 0] := rfl
    rw [htr1, List.singleton_append] at hsurv'
    simp only [accept, Bool.and_eq_true, Bool.not_eq_true'] at hsurv'
    rcases hsurv' with ⟨_, hrest⟩
    have hlen_u : (trace (iter F 1 y) (2 * r - 1)).length = 2 * (r - 1) + 1 := by
      rw [trace_length]; omega
    rw [show 1 + (2 * r - 1) = 2 * r by omega] at hrest
    obtain ⟨a', ha', hv⟩ := acceptRest_odd_prefix (r - 1)
      (trace (iter F 1 y) (2 * r - 1)) (trace (iter F (2 * r) y) (8 + K)) 0 hlen_u (by decide) hrest
    obtain ⟨k, rfl⟩ : ∃ k, K = 1 + k := ⟨K - 1, by omega⟩
    have h9 : 8 + (1 + k) = 9 + k := by omega
    rw [h9, trace_add (iter F (2 * r) y) 9 k] at hv
    let z := iter F (2 * r) y
    have htr9 : trace z 9 =
        [z.testBit 0, (iter F 1 z).testBit 0, (iter F 2 z).testBit 0,
         (iter F 3 z).testBit 0, (iter F 4 z).testBit 0, (iter F 5 z).testBit 0,
         (iter F 6 z).testBit 0, (iter F 7 z).testBit 0, (iter F 8 z).testBit 0] := rfl
    change acceptRest false a' (trace z 9 ++ trace (iter F 9 z) k) = true at hv
    rw [htr9] at hv
    simp only [List.cons_append, List.nil_append] at hv
    have hdisj := acceptRest_false_five_even_steps a' ha'
      (z.testBit 0) ((iter F 1 z).testBit 0) ((iter F 2 z).testBit 0)
      ((iter F 3 z).testBit 0) ((iter F 4 z).testBit 0) ((iter F 5 z).testBit 0)
      ((iter F 6 z).testBit 0) ((iter F 7 z).testBit 0) ((iter F 8 z).testBit 0)
      (trace (iter F 9 z) k) hv
    rcases hdisj with h0 | h2 | h4 | h6 | h8
    · exact absurd h0 hz0
    · have hz2 : (iter F (2 * (r + 1)) y).testBit 0 = false := by
        rw [show 2 * (r + 1) = 2 * r + 2 by omega, iter_F_add]; exact h2
      have hsurv2 : SurvivesTo y (2 * (r + 1) + (1 + k)) :=
        survivesTo_mono (by omega : 2 * (r + 1) + (1 + k) ≤ 2 * r + 8 + (1 + k)) hsurv
      obtain ⟨hs, hm⟩ := survivesTo_shift_at_even_zero y (r + 1) (1 + k) hsurv2 hz2
      exact ⟨1, by decide, hz2, hs, hm⟩
    · have hz4 : (iter F (2 * (r + 2)) y).testBit 0 = false := by
        rw [show 2 * (r + 2) = 2 * r + 4 by omega, iter_F_add]; exact h4
      have hsurv4 : SurvivesTo y (2 * (r + 2) + (1 + k)) :=
        survivesTo_mono (by omega : 2 * (r + 2) + (1 + k) ≤ 2 * r + 8 + (1 + k)) hsurv
      obtain ⟨hs, hm⟩ := survivesTo_shift_at_even_zero y (r + 2) (1 + k) hsurv4 hz4
      exact ⟨2, by decide, hz4, hs, hm⟩
    · have hz6 : (iter F (2 * (r + 3)) y).testBit 0 = false := by
        rw [show 2 * (r + 3) = 2 * r + 6 by omega, iter_F_add]; exact h6
      have hsurv6 : SurvivesTo y (2 * (r + 3) + (1 + k)) :=
        survivesTo_mono (by omega : 2 * (r + 3) + (1 + k) ≤ 2 * r + 8 + (1 + k)) hsurv
      obtain ⟨hs, hm⟩ := survivesTo_shift_at_even_zero y (r + 3) (1 + k) hsurv6 hz6
      exact ⟨3, by decide, hz6, hs, hm⟩
    · have hz8 : (iter F (2 * (r + 4)) y).testBit 0 = false := by
        rw [show 2 * (r + 4) = 2 * r + 8 by omega, iter_F_add]; exact h8
      have hsurv8 : SurvivesTo y (2 * (r + 4) + (1 + k)) :=
        survivesTo_mono (by omega : 2 * (r + 4) + (1 + k) ≤ 2 * r + 8 + (1 + k)) hsurv
      obtain ⟨hs, hm⟩ := survivesTo_shift_at_even_zero y (r + 4) (1 + k) hsurv8 hz8
      exact ⟨4, by decide, hz8, hs, hm⟩

def e2StateInv (o : Bool) (a q : Nat) : Prop :=
  let r := 2 * a + (if o then 0 else 1)
  q = 10 + r ∨ q = 30 + r ∨ q = 50 + r

instance (o : Bool) (a q : Nat) : Decidable (e2StateInv o a q) := by
  unfold e2StateInv; infer_instance

theorem b35_to_e2_step (o : Bool) (a : Nat) (ha : a < 5) (b : Bool) (a' : Nat)
    (hna : nextAge o a b = some a') (q : Nat) (_hq_lt : q < 60)
    (hq : e2StateInv o a q) :
    a' < 5 ∧
    (o = true → b = true) ∧
    (o = false → a = 0 → b = true) ∧
    (o = false → b = false → a' = 0) ∧
    ∃ q' : Nat, q' < 60 ∧
      Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.delta 1 q ((!o) && (!b)) = some q' ∧
      e2StateInv (!o) a' q' := by
  match a, ha with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ =>
    cases o <;> cases b <;> simp [nextAge, gateNext] at hna
    all_goals
      subst hna
      rcases hq with rfl | rfl | rfl <;>
        exact ⟨by decide, by decide, by decide, by decide, _, by decide, rfl, by decide⟩
  | _ + 5, ha => omega

theorem acceptFinal_simulates_e2 (y t : Nat) (hy0 : y.testBit 0 = false) :
    ∀ (o : Bool) (a : Nat),
      acceptFinal true 0 (trace (F y) t) = some (o, a) →
      o = decide (t % 2 = 0) ∧
      a < 5 ∧
      (o = true → Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y t = false → a = 0) ∧
      ∃ q : Nat, q < 60 ∧
        Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.run 1
          (fun s => s % 2 == 0 && !Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y s) 10 t = some q ∧
        e2StateInv o a q := by
  induction t with
  | zero =>
    intro o a hacc
    simp only [trace, acceptFinal, Option.some.injEq, Prod.mk.injEq] at hacc
    rcases hacc with ⟨rfl, rfl⟩
    have _ := hy0
    exact ⟨rfl, by decide, fun _ _ => rfl, 10, by decide, rfl, by decide⟩
  | succ t ih =>
    intro o' a' hacc
    rw [trace_succ_right (F y) t, acceptFinal_append] at hacc
    cases hprev : acceptFinal true 0 (trace (F y) t) with
    | none => simp [hprev] at hacc
    | some pa =>
      rcases pa with ⟨o, a⟩
      simp only [hprev, acceptFinal] at hacc
      have hbit_eq : (iter F t (F y)).testBit 0 = Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y (t + 1) := by
        rw [iter_F_succ_right]; rfl
      rw [hbit_eq] at hacc
      cases hna : nextAge o a (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y (t + 1)) with
      | none => simp [hna] at hacc
      | some na =>
        simp only [hna, Option.some.injEq, Prod.mk.injEq] at hacc
        rcases hacc with ⟨rfl, rfl⟩
        obtain ⟨ho, ha, _, q, hq_lt, hrun, hq⟩ := ih o a hprev
        obtain ⟨hna_lt, _, _, hfalse_a0, q', hq'_lt, hdelta, hq'⟩ :=
          b35_to_e2_step o a ha (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y (t + 1)) na hna q hq_lt hq
        have ho' : (!o) = decide ((t + 1) % 2 = 0) := by
          rw [ho]
          by_cases hmod : t % 2 = 0
          · have hmod1 : (t + 1) % 2 ≠ 0 := by omega
            simp [hmod, hmod1]
          · have hmod1 : (t + 1) % 2 = 0 := by omega
            simp [hmod, hmod1]
        have heven_eq : ((t + 1) % 2 == 0) = (!o) := by
          rw [ho']
          by_cases hmod1 : (t + 1) % 2 = 0
          · simp [hmod1]
          · have hne : ((t + 1) % 2 == 0) = false := beq_false_of_ne hmod1
            simp [hmod1, hne]
        refine ⟨ho', hna_lt, ?_, q', hq'_lt, ?_, hq'⟩
        · intro hno htr
          have hof : o = false := by cases o <;> simp_all
          exact hfalse_a0 hof htr
        · rw [Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.run_succ, hrun, Option.bind_some, heven_eq]
          exact hdelta

/-- **Universal `SurvivesTo → GE2` Horizon Embedding and `NoSeedGE2 → MassDiverges` Bridge
(`survivesTo_two_mul_imp_ge2_and_noSeedGE2_imp_massDiverges`).**
1. For every horizon `m : Nat` and every seed `y : Nat`, `SurvivesTo y (2 * m)` implies
   `Rule30PeriodTwoWidth13.GE2 (Rule30PeriodTwoWidth13.tr y) m`.
2. Every canonical surviving seed `y ∈ survivingSeeds (2 * m)` satisfies
   `y < 2 ^ (2 * m) ∧ Rule30PeriodTwoWidth13.GE2 (Rule30PeriodTwoWidth13.tr y) m`.
3. `Rule30PeriodTwoWidth13.NoSeedGE2` (and hence `MassBoundFunP GE2 g` for any `g : Nat → Nat`)
   implies `FiniteSeedsTerminate`, `MassDiverges`, `ZeroCoastBoxTerminationHypothesis`, and
   `Rule30GateTrap.Q01Gap`. -/
theorem survivesTo_two_mul_imp_ge2_and_noSeedGE2_imp_massDiverges :
    (∀ m y : Nat, SurvivesTo y (2 * m) →
      Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.GE2
        (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y) m) ∧
    (∀ m y : Nat, y ∈ survivingSeeds (2 * m) →
      y < 2 ^ (2 * m) ∧
      Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.GE2
        (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y) m) ∧
    (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.NoSeedGE2 →
      FiniteSeedsTerminate ∧ MassDiverges ∧ ZeroCoastBoxTerminationHypothesis ∧
      Ruliology.CellularAutomata.Rule30GateTrap.Q01Gap) ∧
    (∀ g : Nat → Nat,
      Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.MassBoundFunP
        Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.GE2 g →
      MassDiverges ∧ Ruliology.CellularAutomata.Rule30GateTrap.Q01Gap) := by
  have hmain : ∀ m y : Nat, SurvivesTo y (2 * m) →
      Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.GE2
        (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y) m := by
    intro m y hsurv
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · refine ⟨⟨fun h => absurd h (Nat.lt_irrefl 0), fun j hj => absurd hj (Nat.not_lt_zero j),
        fun j hj => by omega⟩, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    · have h1 : SurvivesTo y 1 := survivesTo_mono (by omega : 1 ≤ 2 * m) hsurv
      have hy0 : y.testBit 0 = false := by
        unfold SurvivesTo trace at h1
        simp only [accept, Bool.and_eq_true, Bool.not_eq_true'] at h1
        exact h1.1
      have hstate : ∀ t < 2 * m, ∃ o a, acceptFinal true 0 (trace (F y) t) = some (o, a) := by
        intro t ht
        have hst : SurvivesTo y (t + 1) := survivesTo_mono (by omega : t + 1 ≤ 2 * m) hsurv
        unfold SurvivesTo at hst
        rw [trace_succ_left_eq, hy0] at hst
        simp only [accept, Bool.not_false, Bool.true_and, ← acceptFinal_isSome_eq_acceptRest] at hst
        obtain ⟨⟨o, a⟩, hpa⟩ := Option.isSome_iff_exists.mp hst
        exact ⟨o, a, hpa⟩
      refine ⟨⟨fun _ => by simpa [Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr, iter] using hy0,
        fun j hj => ?_, fun j hj => ?_⟩, fun j hj => ?_⟩
      · obtain ⟨o1, a1, hacc1⟩ := hstate (2 * j + 1) (by omega)
        rw [trace_succ_right (F y) (2 * j), acceptFinal_append] at hacc1
        obtain ⟨o0, a0, hacc0⟩ := hstate (2 * j) (by omega)
        rw [hacc0] at hacc1
        simp only [acceptFinal] at hacc1
        have hbit_eq : (iter F (2 * j) (F y)).testBit 0 =
            Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y (2 * j + 1) := by
          rw [iter_F_succ_right]; rfl
        rw [hbit_eq] at hacc1
        obtain ⟨ho0, ha0, _, q0, hq0_lt, _, hq0⟩ := acceptFinal_simulates_e2 y (2 * j) hy0 o0 a0 hacc0
        have ho0_true : o0 = true := by simp [ho0]
        cases hna : nextAge o0 a0 (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y (2 * j + 1)) with
        | none => simp [hna] at hacc1
        | some na =>
          exact (b35_to_e2_step o0 a0 ha0 _ na hna q0 hq0_lt hq0).2.1 ho0_true
      · cases htr0 : Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y (2 * j)
        · simp only [Bool.false_or]
          obtain ⟨o0, a0, hacc0⟩ := hstate (2 * j) (by omega)
          obtain ⟨ho0, ha0, hzero0, q0, _, _, _⟩ := acceptFinal_simulates_e2 y (2 * j) hy0 o0 a0 hacc0
          have ho0_true : o0 = true := by simp [ho0]
          have ha0_eq : a0 = 0 := hzero0 ho0_true htr0
          obtain ⟨o1, a1, hacc1⟩ := hstate (2 * j + 1) (by omega)
          have hacc1' := hacc1
          rw [trace_succ_right (F y) (2 * j), acceptFinal_append, hacc0] at hacc1'
          simp only [acceptFinal, ho0_true, nextAge, ↓reduceIte] at hacc1'
          cases htr1 : (iter F (2 * j) (F y)).testBit 0
          · simp [htr1] at hacc1'
          · simp only [htr1, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hacc1'
            rcases hacc1' with ⟨rfl, rfl⟩
            obtain ⟨o2, a2, hacc2⟩ := hstate (2 * j + 2) (by omega)
            rw [show 2 * j + 2 = (2 * j + 1) + 1 by omega, trace_succ_right (F y) (2 * j + 1),
                acceptFinal_append, hacc1] at hacc2
            simp only [acceptFinal] at hacc2
            have hbit2 : (iter F (2 * j + 1) (F y)).testBit 0 =
                Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y (2 * j + 2) := by
              rw [iter_F_succ_right]; rfl
            rw [hbit2] at hacc2
            obtain ⟨_, ha1, _, q1, hq1_lt, _, hq1⟩ := acceptFinal_simulates_e2 y (2 * j + 1) hy0 false a0 hacc1
            cases hna2 : nextAge false a0 (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y (2 * j + 2)) with
            | none => simp [hna2] at hacc2
            | some na2 =>
              exact (b35_to_e2_step false a0 ha1 _ na2 hna2 q1 hq1_lt hq1).2.2.1 rfl ha0_eq
        · simp
      · obtain ⟨o, a, hacc⟩ := hstate j hj
        obtain ⟨_, _, _, q, _, hrun, _⟩ := acceptFinal_simulates_e2 y j hy0 o a hacc
        rw [hrun]; rfl
  have hseeds : ∀ m y : Nat, y ∈ survivingSeeds (2 * m) →
      y < 2 ^ (2 * m) ∧
      Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.GE2
        (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y) m := by
    intro m y hy
    obtain ⟨hlt, hs⟩ := (mem_survivingSeeds_iff_and_survivesTo_iff (2 * m) y).1.mp hy
    exact ⟨hlt, hmain m y hs⟩
  have hnoSeed : Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.NoSeedGE2 →
      FiniteSeedsTerminate ∧ MassDiverges ∧ ZeroCoastBoxTerminationHypothesis ∧
      Ruliology.CellularAutomata.Rule30GateTrap.Q01Gap := by
    intro hno
    have hfin : FiniteSeedsTerminate := by
      intro y
      have hy := hno y
      obtain ⟨m, hm⟩ : ∃ m, ¬ Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.GE2
          (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y) m :=
        Classical.not_forall.mp hy
      exact ⟨2 * m, fun hs => hm (hmain m y hs)⟩
    have hM : MassDiverges := finite_seeds_terminate_iff_mass_diverges.mp hfin
    exact ⟨hfin, hM, massDiverges_iff_zeroCoastBoxTermination.mp hM, massDiverges_iff_Q01Gap.mp hM⟩
  refine ⟨hmain, hseeds, hnoSeed, fun g hg => ?_⟩
  have hno := Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.noSeed_GE2_of_massBoundFun g hg
  exact ⟨(hnoSeed hno).2.1, (hnoSeed hno).2.2.2⟩

end UniversalResetShiftAndGE2Bridge

/-! ## 12. Universal `Zc` Even-Time Zero-Density Laws (`m ≤ 5 * Zc b m` for `GE2`, and `m ≤ 5 * Zc (tr y) m ∧ 3 * Zc (tr y) m ≤ m + 2` for `SurvivesTo`) -/

section UniversalZcDensityLaws
open Rule30ZeroBoundary.IntegerForm

def iterDelta1False : Nat → Option Nat → Option Nat
  | 0, oq => oq
  | n + 1, oq => iterDelta1False n (oq.bind (fun q => Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.delta 1 q false))

theorem delta1_ten_steps_needs_kick (q : Nat) (hq : q < 60) :
    iterDelta1False 10 (some q) = none := by
  revert q hq
  decide

theorem run1_lt_60 (k : Nat → Bool) :
    ∀ (j q : Nat),
      Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.run 1 k 10 j = some q → q < 60 := by
  intro j
  induction j with
  | zero =>
    intro q h
    simp only [Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.run, Option.some.injEq] at h
    omega
  | succ j ih =>
    intro q h
    rw [Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.run_succ] at h
    cases hr : Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.run 1 k 10 j with
    | none => simp [hr] at h
    | some q0 =>
      simp only [hr, Option.bind_some] at h
      exact Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.delta_lt 1 q0 (k (j + 1)) q h

theorem run1_add_false (k : Nat → Bool) (j : Nat) :
    ∀ (n : Nat),
      (∀ d, 1 ≤ d → d ≤ n → k (j + d) = false) →
      Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.run 1 k 10 (j + n) =
        iterDelta1False n (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.run 1 k 10 j) := by
  intro n
  induction n generalizing j with
  | zero => intro _; rfl
  | succ n ih =>
    intro hfalse
    have h1 : k (j + 1) = false := hfalse 1 (by omega) (by omega)
    have hstep : Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.run 1 k 10 (j + 1) =
        (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.run 1 k 10 j).bind
          (fun q => Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.delta 1 q false) := by
      rw [Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.run_succ, h1]
    rw [show j + (n + 1) = (j + 1) + n by omega,
        ih (j + 1) (fun d hd1 hdn => by
          rw [show j + 1 + d = j + (d + 1) by omega]
          exact hfalse (d + 1) (by omega) (by omega)),
        hstep]
    rfl

theorem ge2_five_even_steps_has_zero (b : Nat → Bool) (m : Nat)
    (hge : Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.GE2 b (m + 5)) :
    b (2 * m) = false ∨ b (2 * (m + 1)) = false ∨ b (2 * (m + 2)) = false ∨
      b (2 * (m + 3)) = false ∨ b (2 * (m + 4)) = false := by
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · exact Or.inl (hge.1.1 (by omega))
  · cases hb0 : b (2 * m)
    · exact Or.inl rfl
    · cases hb1 : b (2 * (m + 1))
      · exact Or.inr (Or.inl rfl)
      · cases hb2 : b (2 * (m + 2))
        · exact Or.inr (Or.inr (Or.inl rfl))
        · cases hb3 : b (2 * (m + 3))
          · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
          · cases hb4 : b (2 * (m + 4))
            · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
            · exfalso
              let k : Nat → Bool := fun s => s % 2 == 0 && !b s
              have hfalse : ∀ d, 1 ≤ d → d ≤ 10 → k ((2 * m - 1) + d) = false := by
                intro d hd1 hd10
                by_cases hev : ((2 * m - 1) + d) % 2 = 0
                · have hd_cases : d = 1 ∨ d = 3 ∨ d = 5 ∨ d = 7 ∨ d = 9 := by omega
                  rcases hd_cases with rfl | rfl | rfl | rfl | rfl
                  · rw [show 2 * m - 1 + 1 = 2 * m by omega]; simp [k, hb0]
                  · rw [show 2 * m - 1 + 3 = 2 * (m + 1) by omega]; simp [k, hb1]
                  · rw [show 2 * m - 1 + 5 = 2 * (m + 2) by omega]; simp [k, hb2]
                  · rw [show 2 * m - 1 + 7 = 2 * (m + 3) by omega]; simp [k, hb3]
                  · rw [show 2 * m - 1 + 9 = 2 * (m + 4) by omega]; simp [k, hb4]
                · have hbeq : (((2 * m - 1) + d) % 2 == 0) = false := beq_false_of_ne hev
                  simp [k, hbeq]
              have his0 := hge.2 (2 * m - 1) (by omega)
              change (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.run 1 k 10 (2 * m - 1)).isSome = true at his0
              obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp his0
              have hq_lt : q < 60 := run1_lt_60 k (2 * m - 1) q hq
              have his10 := hge.2 ((2 * m - 1) + 10) (by omega)
              change (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.run 1 k 10 ((2 * m - 1) + 10)).isSome = true at his10
              rw [run1_add_false k (2 * m - 1) 10 hfalse, hq, delta1_ten_steps_needs_kick q hq_lt] at his10
              simp at his10

theorem ge2_mono (b : Nat → Bool) {m1 m2 : Nat} (hle : m1 ≤ m2)
    (h : Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.GE2 b m2) :
    Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.GE2 b m1 := by
  refine ⟨⟨fun hm1 => h.1.1 (by omega), fun j hj => h.1.2.1 j (by omega),
    fun j hj => h.1.2.2 j (by omega)⟩, fun j hj => h.2 j (by omega)⟩

theorem zc_succ (b : Nat → Bool) (m : Nat) :
    Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc b (m + 1) =
      Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc b m + (if b (2 * m) = false then 1 else 0) := rfl

theorem zc_mono (b : Nat → Bool) {k1 k2 : Nat} (hle : k1 ≤ k2) :
    Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc b k1 ≤
      Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc b k2 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    rw [Nat.add_succ, zc_succ]
    omega

/-- **Universal `GE2` Even-Time Zero-Density Law and Explicit Finite-Horizon Cutoff
(`ge2_zc_step_five_and_lower_bound`).**
1. For every horizon `m : Nat` and every trace `b : Nat → Bool`, `GE2 b (m + 5)` implies
   `Zc b m + 1 ≤ Zc b (m + 5)`.
2. For every `m : Nat` and every `b : Nat → Bool`, `GE2 b m` implies `m ≤ 5 * Zc b m`.
3. Under `MassBoundFunP GE2 g`, for every `m : Nat` and `Y < 2 ^ (2 * m)`, if
   `5 * g (wtH (2 * m) Y) < m`, then `¬ GE2 (tr Y) m`. -/
theorem ge2_zc_step_five_and_lower_bound :
    (∀ (b : Nat → Bool) (m : Nat),
      Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.GE2 b (m + 5) →
      Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc b m + 1 ≤
        Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc b (m + 5)) ∧
    (∀ (b : Nat → Bool) (m : Nat),
      Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.GE2 b m →
      m ≤ 5 * Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc b m) ∧
    (∀ (g : Nat → Nat)
      (_hg : Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.MassBoundFunP
        Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.GE2 g)
      (m Y : Nat), Y < 2 ^ (2 * m) →
      5 * g (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.wtH (2 * m) Y) < m →
      ¬ Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.GE2
          (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr Y) m) := by
  have hstep : ∀ (b : Nat → Bool) (m : Nat),
      Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.GE2 b (m + 5) →
      Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc b m + 1 ≤
        Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc b (m + 5) := by
    intro b m hge
    have hdisj := ge2_five_even_steps_has_zero b m hge
    have h5 : Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc b (m + 5) =
        Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc b m +
        (if b (2 * m) = false then 1 else 0) +
        (if b (2 * (m + 1)) = false then 1 else 0) +
        (if b (2 * (m + 2)) = false then 1 else 0) +
        (if b (2 * (m + 3)) = false then 1 else 0) +
        (if b (2 * (m + 4)) = false then 1 else 0) := by
      rw [show m + 5 = m + 4 + 1 by omega, zc_succ,
          show m + 4 = m + 3 + 1 by omega, zc_succ,
          show m + 3 = m + 2 + 1 by omega, zc_succ,
          show m + 2 = m + 1 + 1 by omega, zc_succ, zc_succ]
    rw [h5]
    rcases hdisj with h' | h' | h' | h' | h' <;> simp [h'] <;> try omega
  have hlow : ∀ (b : Nat → Bool) (m : Nat),
      Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.GE2 b m →
      m ≤ 5 * Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc b m := by
    intro b m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro hge
      rcases Nat.eq_zero_or_pos m with rfl | hmpos
      · omega
      · have hb0 : b 0 = false := hge.1.1 hmpos
        have hzc1 : Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc b 1 = 1 := by
          rw [zc_succ]; simp [Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc, hb0]
        by_cases hle5 : m ≤ 5
        · have h1m : 1 ≤ Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc b m := by
            rw [← hzc1]; exact zc_mono b hmpos
          omega
        · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 5 := ⟨m - 5, by omega⟩
          have hge' : Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.GE2 b m' :=
            ge2_mono b (by omega) hge
          have ih_m' := ih m' (by omega) hge'
          have hst := hstep b m' hge
          omega
  refine ⟨hstep, hlow, fun g hg m Y hY hlt hge => ?_⟩
  have h1 := hlow (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr Y) m hge
  have h2 := hg m Y hY hge
  omega

theorem acceptRest_false_three_even_steps (a : Nat) (ha : a < 5)
    (b0 b1 b2 b3 b4 : Bool) (rest : List Bool)
    (h : acceptRest false a (b0 :: b1 :: b2 :: b3 :: b4 :: rest) = true) :
    (if b0 = false then 1 else 0) + (if b2 = false then 1 else 0) + (if b4 = false then 1 else 0) ≤ 1 := by
  revert b0 b1 b2 b3 b4 h
  match a, ha with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ =>
    intro b0 b1 b2 b3 b4 h
    cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;>
      simp [acceptRest, gateNext] at h ⊢ <;> try decide
  | _ + 5, ha => omega

/-- **Universal Two-Sided Even-Time Zero-Density Pinch for `SurvivesTo` (`survivesTo_zc_two_sided_density_pinch`).**
1. For every seed `y : Nat` and horizon `m : Nat`, `SurvivesTo y (2 * (m + 5))` implies
   `Zc (tr y) m + 1 ≤ Zc (tr y) (m + 5)`.
2. For every seed `y : Nat` and horizon `m : Nat`, `SurvivesTo y (2 * (m + 3))` implies
   `Zc (tr y) (m + 3) ≤ Zc (tr y) m + 1`.
3. For every seed `y : Nat` and horizon `m : Nat`, `SurvivesTo y (2 * m)` implies the universal
   two-sided density pinch:
   `m ≤ 5 * Zc (tr y) m ∧ 3 * Zc (tr y) m ≤ m + 2`. -/
theorem survivesTo_zc_two_sided_density_pinch :
    (∀ y m : Nat, SurvivesTo y (2 * (m + 5)) →
      Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc
        (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y) m + 1 ≤
      Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc
        (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y) (m + 5)) ∧
    (∀ y m : Nat, SurvivesTo y (2 * (m + 3)) →
      Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc
        (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y) (m + 3) ≤
      Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc
        (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y) m + 1) ∧
    (∀ y m : Nat, SurvivesTo y (2 * m) →
      m ≤ 5 * Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc
        (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y) m ∧
      3 * Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc
        (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y) m ≤ m + 2) := by
  have hstep5 : ∀ y m : Nat, SurvivesTo y (2 * (m + 5)) →
      Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc
        (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y) m + 1 ≤
      Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc
        (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y) (m + 5) := by
    intro y m hs
    exact ge2_zc_step_five_and_lower_bound.1 _ m
      (survivesTo_two_mul_imp_ge2_and_noSeedGE2_imp_massDiverges.1 (m + 5) y hs)
  have hstep3 : ∀ y m : Nat, SurvivesTo y (2 * (m + 3)) →
      Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc
        (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y) (m + 3) ≤
      Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc
        (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y) m + 1 := by
    intro y m hsurv
    have h3 : Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc
        (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y) (m + 3) =
        Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc
          (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y) m +
        (if Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y (2 * m) = false then 1 else 0) +
        (if Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y (2 * (m + 1)) = false then 1 else 0) +
        (if Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y (2 * (m + 2)) = false then 1 else 0) := by
      rw [show m + 3 = m + 2 + 1 by omega, zc_succ,
          show m + 2 = m + 1 + 1 by omega, zc_succ, zc_succ]
    rw [h3]
    rcases Nat.eq_zero_or_pos m with rfl | hmpos
    · have hs5 : SurvivesTo y 5 := survivesTo_mono (by omega : 5 ≤ 2 * (0 + 3)) hsurv
      have hmem5 : trace y 5 ∈ acceptedWords 5 :=
        (mem_acceptedWords_iff 5 (trace y 5)).mpr ⟨trace_length y 5, hs5⟩
      have haw5 : acceptedWords 5 = [[false, true, true, true, true]] := rfl
      rw [haw5, List.mem_singleton] at hmem5
      have htr5 : trace y 5 =
          [Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y 0,
           Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y 1,
           Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y 2,
           Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y 3,
           Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y 4] := rfl
      rw [htr5] at hmem5
      injection hmem5 with h0 htl1
      injection htl1 with _ htl2
      injection htl2 with h2 htl3
      injection htl3 with _ htl4
      injection htl4 with h4 _
      simp [h0, h2, h4]
    · have hs5 : SurvivesTo y (1 + (2 * m - 1) + 5) :=
        survivesTo_mono (by omega : 1 + (2 * m - 1) + 5 ≤ 2 * (m + 3)) hsurv
      unfold SurvivesTo at hs5
      rw [trace_add y (1 + (2 * m - 1)) 5, trace_add y 1 (2 * m - 1), List.append_assoc] at hs5
      have htr1 : trace y 1 = [y.testBit 0] := rfl
      rw [htr1, List.singleton_append] at hs5
      simp only [accept, Bool.and_eq_true, Bool.not_eq_true'] at hs5
      rcases hs5 with ⟨_, hrest⟩
      have hlen_u : (trace (iter F 1 y) (2 * m - 1)).length = 2 * (m - 1) + 1 := by
        rw [trace_length]; omega
      rw [show 1 + (2 * m - 1) = 2 * m by omega] at hrest
      obtain ⟨a', ha', hv⟩ := acceptRest_odd_prefix (m - 1)
        (trace (iter F 1 y) (2 * m - 1)) (trace (iter F (2 * m) y) 5) 0 hlen_u (by decide) hrest
      let z := iter F (2 * m) y
      have htr5 : trace z 5 =
          [z.testBit 0, (iter F 1 z).testBit 0, (iter F 2 z).testBit 0,
           (iter F 3 z).testBit 0, (iter F 4 z).testBit 0] := rfl
      change acceptRest false a' (trace z 5) = true at hv
      rw [htr5] at hv
      have hle1 := acceptRest_false_three_even_steps a' ha'
        (z.testBit 0) ((iter F 1 z).testBit 0) ((iter F 2 z).testBit 0)
        ((iter F 3 z).testBit 0) ((iter F 4 z).testBit 0) [] hv
      have heq0 : Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y (2 * m) = z.testBit 0 := rfl
      have heq2 : Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y (2 * (m + 1)) = (iter F 2 z).testBit 0 := by
        change (iter F (2 * m + 2) y).testBit 0 = (iter F 2 (iter F (2 * m) y)).testBit 0
        rw [iter_F_add]
      have heq4 : Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y (2 * (m + 2)) = (iter F 4 z).testBit 0 := by
        change (iter F (2 * m + 4) y).testBit 0 = (iter F 4 (iter F (2 * m) y)).testBit 0
        rw [iter_F_add]
      rw [heq0, heq2, heq4]
      omega
  refine ⟨hstep5, hstep3, fun y m => ?_⟩
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro hsurv
    have hlow : m ≤ 5 * Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc
        (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y) m :=
      ge2_zc_step_five_and_lower_bound.2.1 _ m
        (survivesTo_two_mul_imp_ge2_and_noSeedGE2_imp_massDiverges.1 m y hsurv)
    refine ⟨hlow, ?_⟩
    rcases Nat.eq_zero_or_pos m with rfl | hmpos
    · simp [Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc]
    · by_cases h1 : m = 1
      · subst h1
        rw [zc_succ]
        change 3 * (0 + (if Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y 0 = false then 1 else 0)) ≤ 3
        split <;> omega
      · by_cases h2 : m = 2
        · subst h2
          have hge2 := survivesTo_two_mul_imp_ge2_and_noSeedGE2_imp_massDiverges.1 2 y hsurv
          have hb0 : Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y 0 = false := hge2.1.1 (by decide)
          have hb02 : (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y 0 ||
              Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y 2) = true := hge2.1.2.2 0 (by decide)
          rw [hb0, Bool.false_or] at hb02
          rw [show (2 : Nat) = 1 + 1 from rfl, zc_succ, zc_succ]
          change 3 * (0 + (if Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y 0 = false then 1 else 0) +
            (if Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y 2 = false then 1 else 0)) ≤ 4
          simp [hb0, hb02]
        · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 3 := ⟨m - 3, by omega⟩
          have hs' : SurvivesTo y (2 * m') := survivesTo_mono (by omega : 2 * m' ≤ 2 * (m' + 3)) hsurv
          have ih_m' := (ih m' (by omega) hs').2
          have hst3 := hstep3 y m' hsurv
          omega

/-- **Universal Non-Emptiness, Horizon Monotonicity, and Exponential Growth Bound for
`survivingSeeds` and `GE2` (`survivingSeeds_universal_pos_mono_and_exp_lower_bound`).**
1. For every horizon `H : Nat`, `1 ≤ (survivingSeeds H).length`, and there exists `y < 2 ^ H`
   with `SurvivesTo y H`.
2. For every `m : Nat`, there exists a canonical seed `y < 2 ^ (2 * m)` satisfying
   `Rule30PeriodTwoWidth13.GE2 (tr y) m`.
3. For all horizons `H1 ≤ H2`, `(survivingSeeds H1).length ≤ (survivingSeeds H2).length`.
4. For every `k r : Nat`, `2 ^ k ≤ (survivingSeeds (10 * k + r)).length`. -/
theorem survivingSeeds_universal_pos_mono_and_exp_lower_bound :
    (∀ H : Nat, 1 ≤ (survivingSeeds H).length ∧ ∃ y < 2 ^ H, SurvivesTo y H) ∧
    (∀ m : Nat, ∃ y < 2 ^ (2 * m),
      Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.GE2
        (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y) m) ∧
    (∀ H1 H2 : Nat, H1 ≤ H2 → (survivingSeeds H1).length ≤ (survivingSeeds H2).length) ∧
    (∀ k r : Nat, 2 ^ k ≤ (survivingSeeds (10 * k + r)).length) := by
  have hpos_step : ∀ H : Nat, 1 ≤ (survivingSeeds H).length ∧
      (survivingSeeds H).length ≤ (survivingSeeds (H + 1)).length := by
    intro H
    induction H using Nat.strongRecOn with
    | ind H ih =>
      match H with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 => decide
      | H' + 11 =>
        have hrec0 := survivingSeeds_length_add_ten_and_initial_counts.1 (H' + 1) (by omega)
        have hrec1 := survivingSeeds_length_add_ten_and_initial_counts.1 (H' + 2) (by omega)
        have ih1 := ih (H' + 1) (by omega)
        have ih5 := ih (H' + 5) (by omega)
        rw [show H' + 11 + 1 = (H' + 2) + 10 by omega,
            show H' + 11 = (H' + 1) + 10 by omega,
            hrec0, hrec1,
            show H' + 1 + 4 = H' + 5 by omega,
            show H' + 2 + 4 = H' + 5 + 1 by omega,
            show H' + 2 = H' + 1 + 1 by omega]
        omega
  have hmono : ∀ H1 H2 : Nat, H1 ≤ H2 → (survivingSeeds H1).length ≤ (survivingSeeds H2).length := by
    intro H1 H2 hle
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    induction d with
    | zero => exact Nat.le_refl _
    | succ d ih =>
      exact Nat.le_trans (ih (by omega)) (hpos_step (H1 + d)).2
  have hpos : ∀ H : Nat, 1 ≤ (survivingSeeds H).length ∧ ∃ y < 2 ^ H, SurvivesTo y H := by
    intro H
    have hp := (hpos_step H).1
    refine ⟨hp, ?_⟩
    cases hlist : survivingSeeds H with
    | nil => rw [hlist] at hp; simp at hp
    | cons y ys =>
      have hy : y ∈ survivingSeeds H := by rw [hlist]; simp
      exact ⟨y, (mem_survivingSeeds_iff_and_survivesTo_iff H y).1.mp hy⟩
  have hge2_ex : ∀ m : Nat, ∃ y < 2 ^ (2 * m),
      Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.GE2
        (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y) m := by
    intro m
    obtain ⟨y, hlt, hs⟩ := (hpos (2 * m)).2
    exact ⟨y, hlt, survivesTo_two_mul_imp_ge2_and_noSeedGE2_imp_massDiverges.1 m y hs⟩
  have hexp0 : ∀ k : Nat, 2 ^ k ≤ (survivingSeeds (10 * k)).length := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · decide
      · have hrec := survivingSeeds_length_add_ten_and_initial_counts.1 (10 * k) (by omega)
        rw [show 10 * (k + 1) = 10 * k + 10 by omega, hrec]
        have hmono4 := hmono (10 * k) (10 * k + 4) (by omega)
        rw [Nat.pow_succ]
        omega
  have hexp : ∀ k r : Nat, 2 ^ k ≤ (survivingSeeds (10 * k + r)).length := by
    intro k r
    exact Nat.le_trans (hexp0 k) (hmono (10 * k) (10 * k + r) (by omega))
  exact ⟨hpos, hge2_ex, hmono, hexp⟩

end UniversalZcDensityLaws

/-! ## 13. Elementary Weight-Budget Kőnig Equivalence (`NoSeedGE2 ↔ ∃ g, MassBoundFunP GE2 g`) and Finite-List Closure Equivalences for `survivingSeeds`, `MassDiverges`, and `Q01Gap` -/

section UniversalKonigEquivalence
open Rule30ZeroBoundary.IntegerForm

theorem popcount_mod_pow2_eq_wtH (y : Nat) :
    ∀ H : Nat, popcount (y % 2 ^ H) = Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.wtH H y
  | 0 => by simp [Nat.mod_one, popcount_zero, Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.wtH]
  | H + 1 => by
    rw [popcount_mod_pow2_succ, Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.wtH,
        popcount_mod_pow2_eq_wtH y H]

theorem popcount_eq_wtH_of_lt {y H : Nat} (hlt : y < 2 ^ H) :
    popcount y = Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.wtH H y := by
  rw [← popcount_mod_pow2_eq_wtH y H, Nat.mod_eq_of_lt hlt]

theorem testBit_false_of_wtH_le (Y : Nat) :
    ∀ {H1 H2 : Nat}, H1 ≤ H2 →
      Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.wtH H2 Y ≤
        Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.wtH H1 Y →
      ∀ i, H1 ≤ i → i < H2 → Y.testBit i = false := by
  intro H1 H2 hle hw
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  induction d with
  | zero =>
    intro i hi1 hi2
    omega
  | succ d ih =>
    have hstep : Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.wtH (H1 + d + 1) Y =
        Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.wtH (H1 + d) Y +
          (if Y.testBit (H1 + d) = true then 1 else 0) := rfl
    rw [Nat.add_succ, hstep] at hw
    have hle_d : Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.wtH H1 Y ≤
        Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.wtH (H1 + d) Y :=
      Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.wtH_mono Y (by omega)
    have hbit_top : Y.testBit (H1 + d) = false := by
      cases htb : Y.testBit (H1 + d)
      · rfl
      · simp [htb] at hw
        omega
    have hw_d : Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.wtH (H1 + d) Y ≤
        Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.wtH H1 Y := by omega
    intro i hi1 hi2
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi2) with hlt | rfl
    · exact ih (by omega) hw_d i hi1 hlt
    · exact hbit_top

theorem eq_of_mod_eq_of_wtH_le {H1 H2 Y X0 : Nat} (hle : H1 ≤ H2)
    (hY : Y < 2 ^ H2) (hmod : Y % 2 ^ H1 = X0)
    (hw : Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.wtH H2 Y ≤
      Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.wtH H1 X0) :
    Y = X0 := by
  have hX0_lt : X0 < 2 ^ H1 := by
    rw [← hmod]
    exact Nat.mod_lt Y (Nat.two_pow_pos H1)
  have hwt_eq : Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.wtH H1 X0 =
      Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.wtH H1 Y := by
    rw [← hmod, Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.wtH_mod]
  rw [hwt_eq] at hw
  have hzero_mid := testBit_false_of_wtH_le Y hle hw
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi1 : i < H1
  · rw [← hmod, Nat.testBit_mod_two_pow, decide_eq_true hi1, Bool.true_and]
  · have hX0_false : X0.testBit i = false := by
      apply Nat.testBit_lt_two_pow
      exact Nat.lt_of_lt_of_le hX0_lt (Nat.pow_le_pow_right (by decide) (by omega))
    rw [hX0_false]
    by_cases hi2 : i < H2
    · exact hzero_mid i (by omega) hi2
    · apply Nat.testBit_lt_two_pow
      exact Nat.lt_of_lt_of_le hY (Nat.pow_le_pow_right (by decide) (by omega))

theorem mod_two_pow_mod_two_pow (Y a b : Nat) (hab : a ≤ b) :
    (Y % 2 ^ b) % 2 ^ a = Y % 2 ^ a := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hi : i < a
  · have hib : i < b := Nat.lt_of_lt_of_le hi hab
    simp [hi, hib]
  · simp [hi]

/-- Recursive weight-budget Kőnig horizon bound using `Rule30PeriodTwoWidth13.sumBelow`. -/
def konigBound (stopH : Nat → Nat) : Nat → Nat → Nat → Nat
  | 0, m0, X0 => m0 + stopH X0 + 1
  | r + 1, m0, X0 =>
    let M0 := m0 + stopH X0 + 1
    M0 + Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.sumBelow
      (fun X1 => konigBound stopH r M0 X1) (2 ^ (2 * M0))

theorem konigBound_spec (P : (Nat → Bool) → Nat → Prop)
    (hP : Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.PrefixDet P)
    (hmono : ∀ b {m1 m2 : Nat}, m1 ≤ m2 → P b m2 → P b m1)
    (stopH : Nat → Nat) (hstop : ∀ X : Nat, ¬ P (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr X) (stopH X)) :
    ∀ (r m0 X0 m Y : Nat),
      m0 ≤ m → Y < 2 ^ (2 * m) → Y % 2 ^ (2 * m0) = X0 →
      P (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr Y) m →
      Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.wtH (2 * m) Y ≤
        Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.wtH (2 * m0) X0 + r →
      m < konigBound stopH r m0 X0 := by
  intro r
  induction r with
  | zero =>
    intro m0 X0 m Y hm0 hY hmod hPY hw
    simp only [konigBound, Nat.add_zero] at hw ⊢
    refine Classical.byContradiction fun hge => ?_
    have hle_m : m0 + stopH X0 + 1 ≤ m := by omega
    have hY_eq : Y = X0 :=
      eq_of_mod_eq_of_wtH_le (by omega : 2 * m0 ≤ 2 * m) hY hmod hw
    subst hY_eq
    have hstop_m : P (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr Y) (stopH Y) :=
      hmono _ (by omega) hPY
    exact hstop Y hstop_m
  | succ r ih =>
    intro m0 X0 m Y hm0 hY hmod hPY hw
    simp only [konigBound]
    let M0 := m0 + stopH X0 + 1
    refine Classical.byContradiction fun hge => ?_
    have hM0_le_m : M0 ≤ m := by omega
    let X1 := Y % 2 ^ (2 * M0)
    have hX1_lt : X1 < 2 ^ (2 * M0) := Nat.mod_lt Y (Nat.two_pow_pos (2 * M0))
    have hX1_mod : X1 % 2 ^ (2 * m0) = X0 := by
      dsimp [X1]
      rw [mod_two_pow_mod_two_pow Y (2 * m0) (2 * M0) (by omega)]
      exact hmod
    have hPY_M0 : P (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr Y) M0 :=
      hmono _ hM0_le_m hPY
    have hPX1_M0 : P (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr X1) M0 := by
      apply hP (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr Y)
        (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr X1) M0
      · intro t ht
        exact (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr_mod Y (2 * M0) t ht).symm
      · exact hPY_M0
    have hwt_gt : Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.wtH (2 * m0) X0 + 1 ≤
        Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.wtH (2 * M0) X1 := by
      refine Classical.byContradiction fun hle_wt => ?_
      have hX1_eq : X1 = X0 :=
        eq_of_mod_eq_of_wtH_le (by omega : 2 * m0 ≤ 2 * M0) hX1_lt hX1_mod (by omega)
      rw [hX1_eq] at hPX1_M0
      exact hstop X0 (hmono _ (by omega : stopH X0 ≤ M0) hPX1_M0)
    have hw_X1 : Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.wtH (2 * m) Y ≤
        Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.wtH (2 * M0) X1 + r := by omega
    have hm_lt : m < konigBound stopH r M0 X1 :=
      ih M0 X1 m Y hM0_le_m hY rfl hPY hw_X1
    have hsum_le : konigBound stopH r M0 X1 ≤
        Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.sumBelow
          (fun X1 => konigBound stopH r M0 X1) (2 ^ (2 * M0)) :=
      Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.le_sumBelow
        (fun X1 => konigBound stopH r M0 X1) (2 ^ (2 * M0)) X1 hX1_lt
    dsimp [M0] at hsum_le hm_lt
    omega

theorem zc_le_horizon (b : Nat → Bool) :
    ∀ m : Nat, Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc b m ≤ m
  | 0 => by simp [Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc]
  | m + 1 => by
    rw [zc_succ]
    have ih := zc_le_horizon b m
    split <;> omega

/-- **Language-Generic Kőnig Equivalence (`no_finite_seed_iff_massBoundFun`).**
For any prefix-determined, monotone language `P` inside `GValid`, the absence of an infinite
finite-weight seed (`∀ X : Nat, ¬ ∀ m : Nat, P (tr X) m`) is equivalent to the existence of a
bounding function `g : Nat → Nat` satisfying `MassBoundFunP P g`, and also to a direct horizon
bound `m ≤ g (wtH (2 * m) Y)`. -/
theorem no_finite_seed_iff_massBoundFun (P : (Nat → Bool) → Nat → Prop)
    (hP : Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.PrefixDet P)
    (hPG : ∀ b m, P b m → Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.GValid b m)
    (hmono : ∀ b {m1 m2 : Nat}, m1 ≤ m2 → P b m2 → P b m1) :
    ((∀ X : Nat, ¬ ∀ m : Nat, P (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr X) m) ↔
      ∃ g : Nat → Nat, Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.MassBoundFunP P g) ∧
    ((∀ X : Nat, ¬ ∀ m : Nat, P (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr X) m) ↔
      ∃ g : Nat → Nat, ∀ m Y : Nat, Y < 2 ^ (2 * m) →
        P (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr Y) m →
        m ≤ g (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.wtH (2 * m) Y)) := by
  have h_to_hbound :
      (∀ X : Nat, ¬ ∀ m : Nat, P (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr X) m) →
      ∃ g : Nat → Nat, ∀ m Y : Nat, Y < 2 ^ (2 * m) →
        P (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr Y) m →
        m ≤ g (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.wtH (2 * m) Y) := by
    intro hno
    have hex : ∀ X : Nat, ∃ m : Nat, ¬ P (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr X) m :=
      fun X => Classical.not_forall.mp (hno X)
    let stopH : Nat → Nat := fun X => Classical.choose (hex X)
    have hstop : ∀ X : Nat, ¬ P (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr X) (stopH X) :=
      fun X => Classical.choose_spec (hex X)
    refine ⟨fun w => konigBound stopH w 0 0, fun m Y hY hPY => ?_⟩
    have hlt := konigBound_spec P hP hmono stopH hstop
      (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.wtH (2 * m) Y) 0 0 m Y
      (Nat.zero_le m) hY (Nat.mod_one Y) hPY (by simp [Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.wtH])
    dsimp only
    omega
  have hbound_to_mass :
      (∃ g : Nat → Nat, ∀ m Y : Nat, Y < 2 ^ (2 * m) →
        P (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr Y) m →
        m ≤ g (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.wtH (2 * m) Y)) →
      ∃ g : Nat → Nat, Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.MassBoundFunP P g := by
    rintro ⟨g, hg⟩
    exact ⟨g, fun m Y hY hPY => Nat.le_trans (zc_le_horizon _ m) (hg m Y hY hPY)⟩
  have hmass_to_no :
      (∃ g : Nat → Nat, Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.MassBoundFunP P g) →
      (∀ X : Nat, ¬ ∀ m : Nat, P (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr X) m) := by
    rintro ⟨g, hg⟩ X
    exact Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.no_finite_seed_fun P hP hPG g hg X
  exact ⟨⟨fun h => hbound_to_mass (h_to_hbound h), hmass_to_no⟩,
    ⟨h_to_hbound, fun h => hmass_to_no (hbound_to_mass h)⟩⟩

/-- **Complete Kőnig Equivalence and Period-2 Closure for `GE2`
(`noSeed_GE2_iff_exists_massBoundFun_and_horizon_bound`).**
Formalizes the Kőnig equivalence noted in `Rule30PeriodTwoWidth13`:
1. `NoSeedGE2 ↔ (∃ g : Nat → Nat, MassBoundFunP GE2 g)`.
2. `NoSeedGE2 ↔ (∃ g : Nat → Nat, ∀ m Y : Nat, Y < 2 ^ (2 * m) → GE2 (tr Y) m → m ≤ g (wtH (2 * m) Y))`.
3. Any horizon-weight bound `∀ m Y, Y < 2 ^ (2 * m) → GE2 (tr Y) m → m ≤ g (wtH (2 * m) Y)`
   simultaneously closes `NoSeedGE2`, `MassDiverges`, `Rule30GateTrap.Q01Gap`, and excludes
   eventual period 2 of the official Rule 30 center column for every transient. -/
theorem noSeed_GE2_iff_exists_massBoundFun_and_horizon_bound :
    (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.NoSeedGE2 ↔
      ∃ g : Nat → Nat,
        Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.MassBoundFunP
          Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.GE2 g) ∧
    (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.NoSeedGE2 ↔
      ∃ g : Nat → Nat, ∀ m Y : Nat, Y < 2 ^ (2 * m) →
        Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.GE2
          (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr Y) m →
        m ≤ g (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.wtH (2 * m) Y)) ∧
    (∀ g : Nat → Nat,
      (∀ m Y : Nat, Y < 2 ^ (2 * m) →
        Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.GE2
          (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr Y) m →
        m ≤ g (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.wtH (2 * m) Y)) →
      Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.NoSeedGE2 ∧
      MassDiverges ∧
      Ruliology.CellularAutomata.Rule30GateTrap.Q01Gap ∧
      ¬ ∃ T0, ∀ t, T0 ≤ t →
        Ruliology.CellularAutomata.Rule30Prize.center (t + 2) =
          Ruliology.CellularAutomata.Rule30Prize.center t) := by
  have hkonig := no_finite_seed_iff_massBoundFun
    Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.GE2
    Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.prefixDet_GE2
    (fun _ _ h => h.1)
    (fun b _ _ hle h => ge2_mono b hle h)
  refine ⟨hkonig.1, hkonig.2, fun g hg => ?_⟩
  have hno : Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.NoSeedGE2 :=
    hkonig.2.mpr ⟨g, hg⟩
  have hbridge := survivesTo_two_mul_imp_ge2_and_noSeedGE2_imp_massDiverges.2.2.1 hno
  exact ⟨hno, hbridge.2.1, hbridge.2.2.2,
    Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.not_eventually_period_two_of_noSeed_GE2 hno⟩

/-- **Complete Finite-List Kőnig Equivalence for `survivingSeeds`, `MassDiverges`, and `Q01Gap`
(`massDiverges_and_q01Gap_iff_survivingSeeds_konig`).**
1. For every seed `y : Nat` and horizon `H : Nat`,
   `popcount (y % 2 ^ H) = Rule30PeriodTwoWidth13.wtH H y`, and for `y < 2 ^ H`,
   `popcount y = Rule30PeriodTwoWidth13.wtH H y`.
2. For every `M H : Nat`, `NoMass M H ↔ (∀ y ∈ survivingSeeds H, M < popcount y)`.
3. `MassDiverges` and `Rule30GateTrap.Q01Gap` are equivalent to the finite-list weight-divergence
   law on `survivingSeeds H`: `∀ M : Nat, ∃ H : Nat, ∀ y ∈ survivingSeeds H, M < popcount y`.
4. `MassDiverges` and `Rule30GateTrap.Q01Gap` are equivalent to the functional Kőnig bound on
   `survivingSeeds H`: `∃ g : Nat → Nat, ∀ H : Nat, ∀ y ∈ survivingSeeds H, H ≤ g (popcount y)`. -/
theorem massDiverges_and_q01Gap_iff_survivingSeeds_konig :
    (∀ y H : Nat, popcount (y % 2 ^ H) = Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.wtH H y) ∧
    (∀ M H : Nat, NoMass M H ↔ (∀ y ∈ survivingSeeds H, M < popcount y)) ∧
    (MassDiverges ↔
      (∀ M : Nat, ∃ H : Nat, ∀ y ∈ survivingSeeds H, M < popcount y)) ∧
    (Ruliology.CellularAutomata.Rule30GateTrap.Q01Gap ↔
      (∀ M : Nat, ∃ H : Nat, ∀ y ∈ survivingSeeds H, M < popcount y)) ∧
    (MassDiverges ↔
      (∃ g : Nat → Nat, ∀ H : Nat, ∀ y ∈ survivingSeeds H, H ≤ g (popcount y))) := by
  have hnomass_iff : ∀ M H : Nat, NoMass M H ↔ (∀ y ∈ survivingSeeds H, M < popcount y) := by
    intro M H
    constructor
    · intro hno y hy
      obtain ⟨_, hs⟩ := (mem_survivingSeeds_iff_and_survivesTo_iff H y).1.mp hy
      refine Classical.byContradiction fun hle => ?_
      exact hno y (by omega) hs
    · intro hlist y hpc hs
      have hmem : y % 2 ^ H ∈ survivingSeeds H :=
        (mem_survivingSeeds_iff_and_survivesTo_iff H y).2.mp hs
      have hgt := hlist (y % 2 ^ H) hmem
      have hle_pc := popcount_mod_pow2_le y H
      omega
  have hfin_iff : MassDiverges ↔
      (∀ M : Nat, ∃ H : Nat, ∀ y ∈ survivingSeeds H, M < popcount y) := by
    unfold MassDiverges
    constructor
    · intro hM M
      obtain ⟨H, hH⟩ := hM M
      exact ⟨H, (hnomass_iff M H).mp hH⟩
    · intro hlist M
      obtain ⟨H, hH⟩ := hlist M
      exact ⟨H, (hnomass_iff M H).mpr hH⟩
  have hq01_iff : Ruliology.CellularAutomata.Rule30GateTrap.Q01Gap ↔
      (∀ M : Nat, ∃ H : Nat, ∀ y ∈ survivingSeeds H, M < popcount y) :=
    Iff.trans massDiverges_iff_Q01Gap.symm hfin_iff
  have hkonig_iff : MassDiverges ↔
      (∃ g : Nat → Nat, ∀ H : Nat, ∀ y ∈ survivingSeeds H, H ≤ g (popcount y)) := by
    rw [hfin_iff]
    constructor
    · intro hlist
      let H_of : Nat → Nat := fun M => Classical.choose (hlist M)
      have hH_of : ∀ M : Nat, ∀ y ∈ survivingSeeds (H_of M), M < popcount y :=
        fun M => Classical.choose_spec (hlist M)
      refine ⟨fun w => Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.sumBelow H_of (w + 1),
        fun H y hy => ?_⟩
      dsimp only
      have hbound_le : H_of (popcount y) ≤
          Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.sumBelow H_of (popcount y + 1) :=
        Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.le_sumBelow H_of (popcount y + 1)
          (popcount y) (by omega)
      refine Classical.byContradiction fun hgt => ?_
      have hle_H : H_of (popcount y) ≤ H := by omega
      obtain ⟨_, hs⟩ := (mem_survivingSeeds_iff_and_survivesTo_iff H y).1.mp hy
      have hs_sub : SurvivesTo y (H_of (popcount y)) := survivesTo_mono hle_H hs
      have hmem_sub : y % 2 ^ (H_of (popcount y)) ∈ survivingSeeds (H_of (popcount y)) :=
        (mem_survivingSeeds_iff_and_survivesTo_iff (H_of (popcount y)) y).2.mp hs_sub
      have hwt_gt := hH_of (popcount y) (y % 2 ^ (H_of (popcount y))) hmem_sub
      have hwt_le := popcount_mod_pow2_le y (H_of (popcount y))
      omega
    · rintro ⟨g, hg⟩ M
      refine ⟨Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.sumBelow g (M + 1) + 1,
        fun y hy => ?_⟩
      refine Classical.byContradiction fun hle => ?_
      have h_le_g : Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.sumBelow g (M + 1) + 1 ≤
          g (popcount y) := hg _ y hy
      have hg_le_sum : g (popcount y) ≤
          Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.sumBelow g (M + 1) :=
        Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.le_sumBelow g (M + 1)
          (popcount y) (by omega)
      omega
  exact ⟨popcount_mod_pow2_eq_wtH, hnomass_iff, hfin_iff, hq01_iff, hkonig_iff⟩

end UniversalKonigEquivalence

/-! ## 14. Universal Inward Distinction Wavefront (`inward_distinction_wavefront_and_first_trace_diff`), 1D Deterministic Void-Collapse (`voidOrbit`), and Forced Weight-Step Equivalences -/

section UniversalWavefrontAndVoidCollapse
open Rule30ZeroBoundary.IntegerForm

theorem f_step_agree_and_flip {x1 x2 m : Nat}
    (hmod : x1 % 2 ^ (m + 1) = x2 % 2 ^ (m + 1))
    (hdiff : x1.testBit (m + 1) ≠ x2.testBit (m + 1)) :
    (F x1) % 2 ^ m = (F x2) % 2 ^ m ∧
    (F x1).testBit m = !(F x2).testBit m := by
  have hbit_lt : ∀ i < m + 1, x1.testBit i = x2.testBit i := by
    intro i hi
    have h1 : (x1 % 2 ^ (m + 1)).testBit i = x1.testBit i := by
      rw [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and]
    have h2 : (x2 % 2 ^ (m + 1)).testBit i = x2.testBit i := by
      rw [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and]
    rw [← h1, ← h2, hmod]
  constructor
  · apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    by_cases hi : i < m
    · simp only [decide_eq_true hi, Bool.true_and]
      rw [Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.testBit_F,
          Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.testBit_F,
          hbit_lt (i + 1) (by omega), hbit_lt i (by omega), hbit_lt (i - 1) (by omega)]
    · simp [hi]
  · rw [Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.testBit_F,
        Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.testBit_F,
        hbit_lt m (by omega), hbit_lt (m - 1) (by omega)]
    have htop : x1.testBit (m + 1) = !x2.testBit (m + 1) := by
      cases h1 : x1.testBit (m + 1) <;> cases h2 : x2.testBit (m + 1) <;> simp_all
    rw [htop]
    cases x2.testBit (m + 1) <;>
      cases (x2.testBit m || (decide (m ≥ 1) && x2.testBit (m - 1))) <;> rfl

/-- **Universal Inward Distinction Wavefront and First Center-Trace Divergence
(`inward_distinction_wavefront_and_first_trace_diff`).**
For any two seeds `y1 y2 : Nat` and bit depth `k : Nat`, if `y1 % 2 ^ k = y2 % 2 ^ k` and
`y1.testBit k ≠ y2.testBit k`, then:
1. For every step `d ≤ k`, `(iter F d y1) % 2 ^ (k - d) = (iter F d y2) % 2 ^ (k - d)` and
   `(iter F d y1).testBit (k - d) = !(iter F d y2).testBit (k - d)`.
2. At `d = k`, `trace y1 k = trace y2 k` and `(iter F k y1).testBit 0 = !(iter F k y2).testBit 0`. -/
theorem inward_distinction_wavefront_and_first_trace_diff (y1 y2 k : Nat)
    (hmod : y1 % 2 ^ k = y2 % 2 ^ k) (hdiff : y1.testBit k ≠ y2.testBit k) :
    (∀ d : Nat, d ≤ k →
      (iter F d y1) % 2 ^ (k - d) = (iter F d y2) % 2 ^ (k - d) ∧
      (iter F d y1).testBit (k - d) = !(iter F d y2).testBit (k - d)) ∧
    (trace y1 k = trace y2 k ∧
      (iter F k y1).testBit 0 = !(iter F k y2).testBit 0) := by
  have hwave : ∀ d : Nat, d ≤ k →
      (iter F d y1) % 2 ^ (k - d) = (iter F d y2) % 2 ^ (k - d) ∧
      (iter F d y1).testBit (k - d) = !(iter F d y2).testBit (k - d) := by
    intro d
    induction d with
    | zero =>
      intro _
      simp only [iter, Nat.sub_zero]
      refine ⟨hmod, ?_⟩
      cases h1 : y1.testBit k <;> cases h2 : y2.testBit k <;> simp_all
    | succ d ih =>
      intro hle
      obtain ⟨hmod_d, hflip_d⟩ := ih (by omega)
      have hsub : k - d = (k - (d + 1)) + 1 := by omega
      rw [hsub] at hmod_d hflip_d
      have hdiff_d : (iter F d y1).testBit ((k - (d + 1)) + 1) ≠
          (iter F d y2).testBit ((k - (d + 1)) + 1) := by
        rw [hflip_d]
        cases (iter F d y2).testBit (k - (d + 1) + 1) <;> decide
      have hstep := f_step_agree_and_flip hmod_d hdiff_d
      exact hstep
  have htr_eq : trace y1 k = trace y2 k := by
    rw [← trace_mod_pow2 y1 k, ← trace_mod_pow2 y2 k, hmod]
  have hk0 := (hwave k (Nat.le_refl k)).2
  rw [Nat.sub_self] at hk0
  exact ⟨hwave, htr_eq, hk0⟩

def voidOrbit (y K L : Nat) : Option PhysState :=
  (physStateOf y K).bind (fun s => iterZeroNext s L)

/-- **1D Deterministic Void-Collapse and Forced Weight-Step Theorem
(`survivingSeeds_void_crash_forces_weight_step`).**
For every horizon `K ≥ 1`, every canonical seed `y ∈ survivingSeeds K`, and every lookahead `L : Nat`:
1. `SurvivesTo y (K + L) ↔ (voidOrbit y K L).isSome = true`.
2. If `voidOrbit y K L = none` (the deterministic 1D Zero-Void trajectory crashes in `L` steps),
   then `¬ SurvivesTo y (K + L)`, and every surviving extension `z ∈ survivingSeeds (K + L)` with
   `z % 2 ^ K = y` is forced to activate at least one new `1`-bit in `[K, K + L)`:
   `popcount y + 1 ≤ popcount z ∧ Rule30PeriodTwoWidth13.wtH K y + 1 ≤ Rule30PeriodTwoWidth13.wtH (K + L) z`. -/
theorem survivingSeeds_void_crash_forces_weight_step (K L y : Nat)
    (hK : 1 ≤ K) (hy : y ∈ survivingSeeds K) :
    (SurvivesTo y (K + L) ↔ (voidOrbit y K L).isSome = true) ∧
    (voidOrbit y K L = none →
      ¬ SurvivesTo y (K + L) ∧
      ∀ z ∈ survivingSeeds (K + L), z % 2 ^ K = y →
        popcount y + 1 ≤ popcount z ∧
        Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.wtH K y + 1 ≤
          Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.wtH (K + L) z) := by
  obtain ⟨hlt_y, hsurv_y⟩ := (mem_survivingSeeds_iff_and_survivesTo_iff K y).1.mp hy
  obtain ⟨s, hps, hmatch, hn⟩ := physStateOf_isSome_of_survives hK hsurv_y
  have hzeros : ∀ j < L, y.testBit (s.n + j) = false := by
    intro j _
    apply Nat.testBit_lt_two_pow
    rw [hn]
    exact Nat.lt_of_lt_of_le hlt_y (Nat.pow_le_pow_right (by decide) (by omega))
  have hiff := iterZeroNext_isSome_iff_survives L hmatch hzeros
  rw [hn] at hiff
  have hvo : voidOrbit y K L = iterZeroNext s L := by
    unfold voidOrbit
    rw [hps]
    rfl
  rw [← hvo] at hiff
  refine ⟨hiff.symm, fun hnone => ?_⟩
  have hnot_surv : ¬ SurvivesTo y (K + L) := by
    intro hs
    have his := hiff.mpr hs
    rw [hnone] at his
    simp at his
  refine ⟨hnot_surv, fun z hz hmod => ?_⟩
  obtain ⟨hlt_z, hsurv_z⟩ := (mem_survivingSeeds_iff_and_survivesTo_iff (K + L) z).1.mp hz
  have hwt_y : popcount y = Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.wtH K y :=
    popcount_eq_wtH_of_lt hlt_y
  have hwt_z : popcount z = Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.wtH (K + L) z :=
    popcount_eq_wtH_of_lt hlt_z
  have hgt : Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.wtH K y + 1 ≤
      Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.wtH (K + L) z := by
    refine Classical.byContradiction fun hle => ?_
    have hz_eq_y : z = y :=
      eq_of_mod_eq_of_wtH_le (by omega : K ≤ K + L) hlt_z hmod (by omega)
    rw [hz_eq_y] at hsurv_z
    exact hnot_surv hsurv_z
  rw [hwt_y, hwt_z]
  exact ⟨hgt, hgt⟩

/-- **Exact 1D Void-Crash Equivalence for `FiniteSeedsTerminate`, `MassDiverges`, and `Q01Gap`
(`q01Gap_and_massDiverges_iff_survivingSeeds_void_crash`).**
Proves unconditionally that `FiniteSeedsTerminate`, `MassDiverges`, and `Rule30GateTrap.Q01Gap`
are equivalent to the statement that for every horizon `K ≥ 1` and every canonical seed
`y ∈ survivingSeeds K`, its 1D deterministic Void orbit `voidOrbit y K L` eventually hits `none`. -/
theorem q01Gap_and_massDiverges_iff_survivingSeeds_void_crash :
    (FiniteSeedsTerminate ↔
      (∀ K : Nat, 1 ≤ K → ∀ y ∈ survivingSeeds K, ∃ L : Nat, voidOrbit y K L = none)) ∧
    (MassDiverges ↔
      (∀ K : Nat, 1 ≤ K → ∀ y ∈ survivingSeeds K, ∃ L : Nat, voidOrbit y K L = none)) ∧
    (Ruliology.CellularAutomata.Rule30GateTrap.Q01Gap ↔
      (∀ K : Nat, 1 ≤ K → ∀ y ∈ survivingSeeds K, ∃ L : Nat, voidOrbit y K L = none)) := by
  have hfin_iff : FiniteSeedsTerminate ↔
      (∀ K : Nat, 1 ≤ K → ∀ y ∈ survivingSeeds K, ∃ L : Nat, voidOrbit y K L = none) := by
    constructor
    · intro hfin K hK y hy
      obtain ⟨H, hH⟩ := hfin y
      refine ⟨H, ?_⟩
      have hnot_KL : ¬ SurvivesTo y (K + H) := fun hs =>
        hH (survivesTo_mono (by omega : H ≤ K + H) hs)
      have hiff := (survivingSeeds_void_crash_forces_weight_step K H y hK hy).1
      cases hvo : voidOrbit y K H with
      | none => rfl
      | some _ =>
        exfalso
        exact hnot_KL (hiff.mpr (by simp [hvo]))
    · intro hcrash y
      let K := y + 1
      have hK : 1 ≤ K := by omega
      have hlt : y < 2 ^ K :=
        Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by decide) (by omega))
      by_cases hsK : SurvivesTo y K
      · have hy : y ∈ survivingSeeds K :=
          (mem_survivingSeeds_iff_and_survivesTo_iff K y).1.mpr ⟨hlt, hsK⟩
        obtain ⟨L, hnone⟩ := hcrash K hK y hy
        exact ⟨K + L, ((survivingSeeds_void_crash_forces_weight_step K L y hK hy).2 hnone).1⟩
      · exact ⟨K, hsK⟩
  have hmass_iff : MassDiverges ↔
      (∀ K : Nat, 1 ≤ K → ∀ y ∈ survivingSeeds K, ∃ L : Nat, voidOrbit y K L = none) :=
    Iff.trans finite_seeds_terminate_iff_mass_diverges.symm hfin_iff
  have hq01_iff : Ruliology.CellularAutomata.Rule30GateTrap.Q01Gap ↔
      (∀ K : Nat, 1 ≤ K → ∀ y ∈ survivingSeeds K, ∃ L : Nat, voidOrbit y K L = none) :=
    Iff.trans massDiverges_iff_Q01Gap.symm hmass_iff
  exact ⟨hfin_iff, hmass_iff, hq01_iff⟩

end UniversalWavefrontAndVoidCollapse

/-! ## 15. Constructive All-Horizon `ge2Seeds m` Generator, Finite-List `NoSeedGE2` Kőnig Equivalence, and Variable-Step `{6, 10}` Void Return Map (`voidMacroStep`, `iterVoidMacro`) -/

section GE2SeedsAndVoidMacroReturnMap
open Rule30ZeroBoundary.IntegerForm

def gValidDecide (b : Nat → Bool) (m : Nat) : Bool :=
  (decide (m = 0) || !b 0) &&
  (List.range m).all (fun j => b (2 * j + 1)) &&
  (List.range (m - 1)).all (fun j => b (2 * j) || b (2 * j + 2))

def e2RunDecide (b : Nat → Bool) (m : Nat) : Bool :=
  (List.range (2 * m)).all (fun j =>
    (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.run 1
      (fun s => s % 2 == 0 && !b s) 10 j).isSome)

def ge2Decide (m Y : Nat) : Bool :=
  gValidDecide (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr Y) m &&
  e2RunDecide (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr Y) m

/-- Constructive all-horizon list of canonical seeds `Y < 2 ^ (2 * m)` satisfying `GE2 (tr Y) m`. -/
def ge2Seeds (m : Nat) : List Nat :=
  (List.range (2 ^ (2 * m))).filter (fun Y => ge2Decide m Y)

theorem gValidDecide_eq_true_iff (b : Nat → Bool) (m : Nat) :
    gValidDecide b m = true ↔ Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.GValid b m := by
  unfold gValidDecide Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.GValid
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range]
  constructor
  · rintro ⟨⟨h0, hodd⟩, hpair⟩
    refine ⟨?_, hodd, ?_⟩
    · intro hm
      cases hdec : decide (m = 0)
      · simp [hdec] at h0
        exact h0
      · have hm0 : m = 0 := of_decide_eq_true hdec
        omega
    · intro j hj
      exact hpair j (by omega)
  · rintro ⟨h0, hodd, hpair⟩
    refine ⟨⟨?_, hodd⟩, ?_⟩
    · by_cases hm : m = 0
      · simp [hm]
      · have hpos : 0 < m := by omega
        simp [hm, h0 hpos]
    · intro j hj
      exact hpair j (by omega)

theorem e2RunDecide_eq_true_iff (b : Nat → Bool) (m : Nat) :
    e2RunDecide b m = true ↔ Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.E2Run b m := by
  unfold e2RunDecide Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.E2Run
  simp [List.all_eq_true, List.mem_range]

theorem ge2Decide_eq_true_iff (m Y : Nat) :
    ge2Decide m Y = true ↔
      Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.GE2
        (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr Y) m := by
  unfold ge2Decide Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.GE2
  rw [Bool.and_eq_true, gValidDecide_eq_true_iff, e2RunDecide_eq_true_iff]

/-- **Universal `ge2Seeds m` Specification and Finite-List Kőnig Equivalence for `NoSeedGE2`
(`mem_ge2Seeds_iff_and_noSeed_GE2_konig`).**
1. For every `m Y : Nat`, `Y ∈ ge2Seeds m ↔ (Y < 2 ^ (2 * m) ∧ GE2 (tr Y) m)`.
2. For every `m X : Nat`, `GE2 (tr X) m ↔ X % 2 ^ (2 * m) ∈ ge2Seeds m`.
3. For every `m : Nat`, `∀ y ∈ survivingSeeds (2 * m), y ∈ ge2Seeds m`.
4. `NoSeedGE2 ↔ (∀ M : Nat, ∃ m : Nat, ∀ Y ∈ ge2Seeds m, M < popcount Y)`.
5. `NoSeedGE2 ↔ (∃ g : Nat → Nat, ∀ m : Nat, ∀ Y ∈ ge2Seeds m, m ≤ g (popcount Y))`. -/
theorem mem_ge2Seeds_iff_and_noSeed_GE2_konig :
    (∀ m Y : Nat,
      Y ∈ ge2Seeds m ↔
        (Y < 2 ^ (2 * m) ∧
          Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.GE2
            (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr Y) m)) ∧
    (∀ m X : Nat,
      Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.GE2
        (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr X) m ↔
        X % 2 ^ (2 * m) ∈ ge2Seeds m) ∧
    (∀ m : Nat, ∀ y ∈ survivingSeeds (2 * m), y ∈ ge2Seeds m) ∧
    (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.NoSeedGE2 ↔
      (∀ M : Nat, ∃ m : Nat, ∀ Y ∈ ge2Seeds m, M < popcount Y)) ∧
    (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.NoSeedGE2 ↔
      (∃ g : Nat → Nat, ∀ m : Nat, ∀ Y ∈ ge2Seeds m, m ≤ g (popcount Y))) := by
  have hmem : ∀ m Y : Nat,
      Y ∈ ge2Seeds m ↔
        (Y < 2 ^ (2 * m) ∧
          Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.GE2
            (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr Y) m) := by
    intro m Y
    simp [ge2Seeds, List.mem_filter, List.mem_range, ge2Decide_eq_true_iff]
  have hmod : ∀ m X : Nat,
      Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.GE2
        (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr X) m ↔
        X % 2 ^ (2 * m) ∈ ge2Seeds m := by
    intro m X
    rw [hmem]
    have hlt : X % 2 ^ (2 * m) < 2 ^ (2 * m) := Nat.mod_lt X (Nat.two_pow_pos (2 * m))
    constructor
    · intro hG
      refine ⟨hlt, ?_⟩
      apply Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.prefixDet_GE2
        (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr X)
        (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr (X % 2 ^ (2 * m))) m
      · intro t ht
        exact (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr_mod X (2 * m) t ht).symm
      · exact hG
    · rintro ⟨_, hGY⟩
      apply Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.prefixDet_GE2
        (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr (X % 2 ^ (2 * m)))
        (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr X) m
      · intro t ht
        exact Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr_mod X (2 * m) t ht
      · exact hGY
  have hincl : ∀ m : Nat, ∀ y ∈ survivingSeeds (2 * m), y ∈ ge2Seeds m := by
    intro m y hy
    obtain ⟨hlt, hs⟩ := (mem_survivingSeeds_iff_and_survivesTo_iff (2 * m) y).1.mp hy
    have hge2 := survivesTo_two_mul_imp_ge2_and_noSeedGE2_imp_massDiverges.1 m y hs
    exact (hmem m y).mpr ⟨hlt, hge2⟩
  have hkonig_g : Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.NoSeedGE2 ↔
      (∃ g : Nat → Nat, ∀ m : Nat, ∀ Y ∈ ge2Seeds m, m ≤ g (popcount Y)) := by
    rw [noSeed_GE2_iff_exists_massBoundFun_and_horizon_bound.2.1]
    constructor
    · rintro ⟨g, hg⟩
      refine ⟨g, fun m Y hY => ?_⟩
      obtain ⟨hlt, hge2⟩ := (hmem m Y).mp hY
      rw [popcount_eq_wtH_of_lt hlt]
      exact hg m Y hlt hge2
    · rintro ⟨g, hg⟩
      refine ⟨g, fun m Y hlt hge2 => ?_⟩
      have hY : Y ∈ ge2Seeds m := (hmem m Y).mpr ⟨hlt, hge2⟩
      rw [← popcount_eq_wtH_of_lt hlt]
      exact hg m Y hY
  have hkonig_M : Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.NoSeedGE2 ↔
      (∀ M : Nat, ∃ m : Nat, ∀ Y ∈ ge2Seeds m, M < popcount Y) := by
    rw [hkonig_g]
    constructor
    · rintro ⟨g, hg⟩ M
      refine ⟨Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.sumBelow g (M + 1) + 1,
        fun Y hY => ?_⟩
      refine Classical.byContradiction fun hle => ?_
      have h_le_g := hg _ Y hY
      have hg_le_sum :=
        Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.le_sumBelow g (M + 1)
          (popcount Y) (by omega)
      omega
    · intro hlist
      let m_of : Nat → Nat := fun M => Classical.choose (hlist M)
      have hm_of : ∀ M : Nat, ∀ Y ∈ ge2Seeds (m_of M), M < popcount Y :=
        fun M => Classical.choose_spec (hlist M)
      refine ⟨fun w => Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.sumBelow m_of (w + 1),
        fun m Y hY => ?_⟩
      dsimp only
      have hbound_le : m_of (popcount Y) ≤
          Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.sumBelow m_of (popcount Y + 1) :=
        Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.le_sumBelow m_of (popcount Y + 1)
          (popcount Y) (by omega)
      refine Classical.byContradiction fun hgt => ?_
      have hle_m : m_of (popcount Y) ≤ m := by omega
      obtain ⟨_, hge2⟩ := (hmem m Y).mp hY
      have hge2_sub : Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.GE2
          (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr Y) (m_of (popcount Y)) :=
        ge2_mono _ hle_m hge2
      have hmem_sub : Y % 2 ^ (2 * m_of (popcount Y)) ∈ ge2Seeds (m_of (popcount Y)) :=
        (hmod (m_of (popcount Y)) Y).mp hge2_sub
      have hwt_gt := hm_of (popcount Y) (Y % 2 ^ (2 * m_of (popcount Y))) hmem_sub
      have hwt_le := popcount_mod_pow2_le Y (2 * m_of (popcount Y))
      omega
  exact ⟨hmem, hmod, hincl, hkonig_M, hkonig_g⟩

/-- Variable-step `{6, 10}` Void return map between ground-state resets (`isOdd = true ∧ age = 0`, matching `initPhysState`). -/
def voidMacroStep (s : PhysState) : Option (PhysState × Nat) :=
  match iterZeroNext s 6 with
  | none => none
  | some s6 =>
    if s6.isOdd && s6.age == 0 then
      some (s6, 6)
    else
      match iterZeroNext s 10 with
      | none => none
      | some s10 =>
        if s10.isOdd && s10.age == 0 then
          some (s10, 10)
        else
          none

/-- `k`-cycle iteration of the variable-step `{6, 10}` Void return map. -/
def iterVoidMacro (s : PhysState) : Nat → Option PhysState
  | 0 => some s
  | k + 1 =>
    match voidMacroStep s with
    | none => none
    | some (s', _) => iterVoidMacro s' k

theorem iterZeroNext_one (s : PhysState) : iterZeroNext s 1 = zeroNext s := by
  unfold iterZeroNext
  cases zeroNext s <;> rfl

theorem iterZeroNext_add (s : PhysState) (a b : Nat) :
    iterZeroNext s (a + b) = (iterZeroNext s a).bind (fun s' => iterZeroNext s' b) := by
  induction a generalizing s with
  | zero => simp [iterZeroNext]
  | succ a ih =>
    rw [Nat.succ_add]
    simp only [iterZeroNext]
    cases zeroNext s with
    | none => rfl
    | some s1 => exact ih s1

theorem zeroNext_n_isOdd_and_age {s s' : PhysState} (h : zeroNext s = some s') :
    s'.n = s.n + 1 ∧
    s'.isOdd = !s.isOdd ∧
    nextAge s.isOdd s.age (piParity (physSigma s)) = some s'.age := by
  unfold zeroNext at h
  cases hna : nextAge s.isOdd s.age (piParity (physSigma s)) with
  | none => simp [hna] at h
  | some na =>
    simp only [hna, Option.some.injEq] at h
    rw [← h]
    exact ⟨rfl, rfl, rfl⟩

theorem iterZeroNext_n_eq :
    ∀ (L : Nat) {s s' : PhysState}, iterZeroNext s L = some s' → s'.n = s.n + L
  | 0, s, s', h => by
    simp only [iterZeroNext, Option.some.injEq] at h
    rw [← h, Nat.add_zero]
  | L + 1, s, s', h => by
    simp only [iterZeroNext] at h
    cases hz : zeroNext s with
    | none => simp [hz] at h
    | some s1 =>
      rw [hz] at h
      have hn1 := (zeroNext_n_isOdd_and_age hz).1
      have ih := iterZeroNext_n_eq L h
      omega

theorem nextAge_step_from {o : Bool} {a a' : Nat} {b : Bool}
    (h : nextAge o a b = some a') :
    (o = true ∧ a = 0 → a' = 0) ∧
    (o = false ∧ a = 0 → a' = 1) ∧
    (o = true ∧ a = 1 → a' = 1) ∧
    (o = false ∧ a = 1 → a' = 2) ∧
    (o = true ∧ a = 2 → a' = 2) ∧
    (o = false ∧ a = 2 → a' = 0 ∨ a' = 3) ∧
    (o = true ∧ a = 3 → a' = 3) ∧
    (o = false ∧ a = 3 → a' = 4) ∧
    (o = true ∧ a = 4 → a' = 4) ∧
    (o = false ∧ a = 4 → a' = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨rfl, rfl⟩; cases b <;> simp [nextAge] at h; exact h.symm
  · rintro ⟨rfl, rfl⟩; cases b <;> simp [nextAge, gateNext] at h; exact h.symm
  · rintro ⟨rfl, rfl⟩; cases b <;> simp [nextAge] at h; exact h.symm
  · rintro ⟨rfl, rfl⟩; cases b <;> simp [nextAge, gateNext] at h; exact h.symm
  · rintro ⟨rfl, rfl⟩; cases b <;> simp [nextAge] at h; exact h.symm
  · rintro ⟨rfl, rfl⟩
    cases b <;> simp [nextAge, gateNext] at h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  · rintro ⟨rfl, rfl⟩; cases b <;> simp [nextAge] at h; exact h.symm
  · rintro ⟨rfl, rfl⟩; cases b <;> simp [nextAge, gateNext] at h; exact h.symm
  · rintro ⟨rfl, rfl⟩; cases b <;> simp [nextAge] at h; exact h.symm
  · rintro ⟨rfl, rfl⟩; cases b <;> simp [nextAge, gateNext] at h; exact h.symm

theorem voidMacroStep_complete_of_reset {s s10 : PhysState}
    (ho : s.isOdd = true) (ha : s.age = 0)
    (h10 : iterZeroNext s 10 = some s10) :
    (voidMacroStep s).isSome = true := by
  have hsplit : iterZeroNext s 10 = (iterZeroNext s 6).bind (fun s6 => iterZeroNext s6 4) :=
    iterZeroNext_add s 6 4
  rw [h10] at hsplit
  cases h6 : iterZeroNext s 6 with
  | none => rw [h6] at hsplit; cases hsplit
  | some s6 =>
    rw [h6] at hsplit
    dsimp only [Option.bind] at hsplit
    rcases s1_eq : zeroNext s with _ | s1
    · simp [iterZeroNext, s1_eq] at h6
    have h6_1 : iterZeroNext s1 5 = some s6 := by simpa [iterZeroNext, s1_eq] using h6
    rcases s2_eq : zeroNext s1 with _ | s2
    · simp [iterZeroNext, s2_eq] at h6_1
    have h6_2 : iterZeroNext s2 4 = some s6 := by simpa [iterZeroNext, s2_eq] using h6_1
    rcases s3_eq : zeroNext s2 with _ | s3
    · simp [iterZeroNext, s3_eq] at h6_2
    have h6_3 : iterZeroNext s3 3 = some s6 := by simpa [iterZeroNext, s3_eq] using h6_2
    rcases s4_eq : zeroNext s3 with _ | s4
    · simp [iterZeroNext, s4_eq] at h6_3
    have h6_4 : iterZeroNext s4 2 = some s6 := by simpa [iterZeroNext, s4_eq] using h6_3
    rcases s5_eq : zeroNext s4 with _ | s5
    · simp [iterZeroNext, s5_eq] at h6_4
    have h6_5 : zeroNext s5 = some s6 := by
      rw [← iterZeroNext_one s5]
      simpa [iterZeroNext, s5_eq] using h6_4
    obtain ⟨_, ho1, hna1⟩ := zeroNext_n_isOdd_and_age s1_eq
    obtain ⟨_, ho2, hna2⟩ := zeroNext_n_isOdd_and_age s2_eq
    obtain ⟨_, ho3, hna3⟩ := zeroNext_n_isOdd_and_age s3_eq
    obtain ⟨_, ho4, hna4⟩ := zeroNext_n_isOdd_and_age s4_eq
    obtain ⟨_, ho5, hna5⟩ := zeroNext_n_isOdd_and_age s5_eq
    obtain ⟨_, ho6, hna6⟩ := zeroNext_n_isOdd_and_age h6_5
    have h_o1 : s1.isOdd = false := by rw [ho1, ho]; rfl
    have h_o2 : s2.isOdd = true := by rw [ho2, h_o1]; rfl
    have h_o3 : s3.isOdd = false := by rw [ho3, h_o2]; rfl
    have h_o4 : s4.isOdd = true := by rw [ho4, h_o3]; rfl
    have h_o5 : s5.isOdd = false := by rw [ho5, h_o4]; rfl
    have h_o6 : s6.isOdd = true := by rw [ho6, h_o5]; rfl
    have ha1 := (nextAge_step_from hna1).1 ⟨ho, ha⟩
    have ha2 := (nextAge_step_from hna2).2.1 ⟨h_o1, ha1⟩
    have ha3 := (nextAge_step_from hna3).2.2.1 ⟨h_o2, ha2⟩
    have ha4 := (nextAge_step_from hna4).2.2.2.1 ⟨h_o3, ha3⟩
    have ha5 := (nextAge_step_from hna5).2.2.2.2.1 ⟨h_o4, ha4⟩
    have ha6 := (nextAge_step_from hna6).2.2.2.2.2.1 ⟨h_o5, ha5⟩
    rcases ha6 with ha6 | ha6
    · unfold voidMacroStep
      rw [h6]
      simp [h_o6, ha6]
    · have hrem : iterZeroNext s6 4 = some s10 := hsplit.symm
      rcases s7_eq : zeroNext s6 with _ | s7
      · simp [iterZeroNext, s7_eq] at hrem
      have hrem1 : iterZeroNext s7 3 = some s10 := by simpa [iterZeroNext, s7_eq] using hrem
      rcases s8_eq : zeroNext s7 with _ | s8
      · simp [iterZeroNext, s8_eq] at hrem1
      have hrem2 : iterZeroNext s8 2 = some s10 := by simpa [iterZeroNext, s8_eq] using hrem1
      rcases s9_eq : zeroNext s8 with _ | s9
      · simp [iterZeroNext, s9_eq] at hrem2
      have hrem3 : zeroNext s9 = some s10 := by
        rw [← iterZeroNext_one s9]
        simpa [iterZeroNext, s9_eq] using hrem2
      obtain ⟨_, ho7, hna7⟩ := zeroNext_n_isOdd_and_age s7_eq
      obtain ⟨_, ho8, hna8⟩ := zeroNext_n_isOdd_and_age s8_eq
      obtain ⟨_, ho9, hna9⟩ := zeroNext_n_isOdd_and_age s9_eq
      obtain ⟨_, ho10, hna10⟩ := zeroNext_n_isOdd_and_age hrem3
      have h_o7 : s7.isOdd = false := by rw [ho7, h_o6]; rfl
      have h_o8 : s8.isOdd = true := by rw [ho8, h_o7]; rfl
      have h_o9 : s9.isOdd = false := by rw [ho9, h_o8]; rfl
      have h_o10 : s10.isOdd = true := by rw [ho10, h_o9]; rfl
      have ha7 := (nextAge_step_from hna7).2.2.2.2.2.2.1 ⟨h_o6, ha6⟩
      have ha8 := (nextAge_step_from hna8).2.2.2.2.2.2.2.1 ⟨h_o7, ha7⟩
      have ha9 := (nextAge_step_from hna9).2.2.2.2.2.2.2.2.1 ⟨h_o8, ha8⟩
      have ha10 := (nextAge_step_from hna10).2.2.2.2.2.2.2.2.2 ⟨h_o9, ha9⟩
      unfold voidMacroStep
      rw [h6, h10]
      simp [h_o6, ha6, h_o10, ha10]

theorem voidMacroStep_spec {s s' : PhysState} {dt : Nat}
    (h : voidMacroStep s = some (s', dt)) :
    (dt = 6 ∨ dt = 10) ∧
    iterZeroNext s dt = some s' ∧
    s'.n = s.n + dt ∧
    s'.isOdd = true ∧ s'.age = 0 := by
  unfold voidMacroStep at h
  cases h6 : iterZeroNext s 6 with
  | none => simp [h6] at h
  | some s6 =>
    rw [h6] at h
    dsimp only at h
    split at h
    · next hcond6 =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond6
      exact ⟨Or.inl rfl, h6, iterZeroNext_n_eq 6 h6, hcond6.1, hcond6.2⟩
    · cases h10 : iterZeroNext s 10 with
      | none => simp [h10] at h
      | some s10 =>
        rw [h10] at h
        dsimp only at h
        split at h
        · next hcond10 =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          simp only [Bool.and_eq_true, beq_iff_eq] at hcond10
          exact ⟨Or.inr rfl, h10, iterZeroNext_n_eq 10 h10, hcond10.1, hcond10.2⟩
        · simp at h

/-- **Variable-Step `{6, 10}` Void Return Map and Two-Sided Time-Dilation Laws
(`voidMacroStep_and_iterVoidMacro_dilation_laws`).**
1. Every macro-step `voidMacroStep s = some (s', dt)` advances the inward horizon by a quantized
   step `dt ∈ {6, 10}`, satisfies `iterZeroNext s dt = some s'`, `s'.n = s.n + dt`, and returns
   to the post-reset ground state `s'.isOdd = true ∧ s'.age = 0` (matching `initPhysState`).
2. From any post-reset ground state `s.isOdd = true ∧ s.age = 0`, `(iterZeroNext s 10).isSome = true`
   implies `(voidMacroStep s).isSome = true` (so `voidMacroStep s = none → iterZeroNext s 10 = none`).
3. Every `k`-cycle macro-orbit `iterVoidMacro s k = some s'` corresponds to a microscopic Void
   orbit `iterZeroNext s L = some s'` with exact two-sided time-dilation bounds `6 * k ≤ L ≤ 10 * k`
   and `s'.n = s.n + L`.
4. From any post-reset ground state `s.isOdd = true ∧ s.age = 0`, `(iterZeroNext s (10 * k)).isSome = true`
   implies `(iterVoidMacro s k).isSome = true`. -/
theorem voidMacroStep_and_iterVoidMacro_dilation_laws :
    (∀ s s' : PhysState, ∀ dt : Nat,
      voidMacroStep s = some (s', dt) →
        (dt = 6 ∨ dt = 10) ∧
        iterZeroNext s dt = some s' ∧
        s'.n = s.n + dt ∧
        s'.isOdd = true ∧ s'.age = 0) ∧
    (∀ s : PhysState, s.isOdd = true → s.age = 0 →
      (iterZeroNext s 10).isSome = true → (voidMacroStep s).isSome = true) ∧
    (∀ k : Nat, ∀ s s' : PhysState,
      iterVoidMacro s k = some s' →
        ∃ L : Nat, 6 * k ≤ L ∧ L ≤ 10 * k ∧
          iterZeroNext s L = some s' ∧ s'.n = s.n + L) ∧
    (∀ k : Nat, ∀ s : PhysState,
      s.isOdd = true → s.age = 0 →
      (iterZeroNext s (10 * k)).isSome = true →
      (iterVoidMacro s k).isSome = true) := by
  have hmacro_complete : ∀ s : PhysState, s.isOdd = true → s.age = 0 →
      (iterZeroNext s 10).isSome = true → (voidMacroStep s).isSome = true := by
    intro s ho ha his
    obtain ⟨s10, h10⟩ := Option.isSome_iff_exists.mp his
    exact voidMacroStep_complete_of_reset ho ha h10
  have hiter_sound : ∀ k : Nat, ∀ s s' : PhysState,
      iterVoidMacro s k = some s' →
        ∃ L : Nat, 6 * k ≤ L ∧ L ≤ 10 * k ∧
          iterZeroNext s L = some s' ∧ s'.n = s.n + L := by
    intro k
    induction k with
    | zero =>
      intro s s' h
      simp only [iterVoidMacro, Option.some.injEq] at h
      subst h
      exact ⟨0, by omega, by omega, rfl, by omega⟩
    | succ k ih =>
      intro s s' h
      simp only [iterVoidMacro] at h
      cases hm : voidMacroStep s with
      | none => simp [hm] at h
      | some pr =>
        rcases pr with ⟨s1, dt⟩
        rw [hm] at h
        obtain ⟨hdt, hstep1, hn1, _, _⟩ := voidMacroStep_spec hm
        obtain ⟨L2, hL2_lo, hL2_hi, hstep2, hn2⟩ := ih s1 s' h
        refine ⟨dt + L2, ?_, ?_, ?_, by omega⟩
        · rcases hdt with rfl | rfl <;> omega
        · rcases hdt with rfl | rfl <;> omega
        · rw [iterZeroNext_add, hstep1]
          exact hstep2
  have hiter_complete : ∀ k : Nat, ∀ s : PhysState,
      s.isOdd = true → s.age = 0 →
      (iterZeroNext s (10 * k)).isSome = true →
      (iterVoidMacro s k).isSome = true := by
    intro k
    induction k with
    | zero =>
      intro s _ _ _
      rfl
    | succ k ih =>
      intro s ho ha his
      have his0 := his
      have h10k : 10 * (k + 1) = 10 + 10 * k := by omega
      rw [h10k, iterZeroNext_add] at his
      cases h10 : iterZeroNext s 10 with
      | none => rw [h10] at his; simp at his
      | some s10 =>
        have hms_some := voidMacroStep_complete_of_reset ho ha h10
        obtain ⟨⟨s1, dt⟩, hms⟩ := Option.isSome_iff_exists.mp hms_some
        obtain ⟨hdt, hstep1, _, ho1, ha1⟩ := voidMacroStep_spec hms
        simp only [iterVoidMacro, hms]
        apply ih s1 ho1 ha1
        have hle : dt + 10 * k ≤ 10 * (k + 1) := by
          rcases hdt with rfl | rfl <;> omega
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
        rw [hd, iterZeroNext_add, iterZeroNext_add, hstep1] at his0
        dsimp only [Option.bind] at his0
        cases hsub : iterZeroNext s1 (10 * k) with
        | none => rw [hsub] at his0; simp at his0
        | some _ => rfl
  exact ⟨fun _ _ _ h => voidMacroStep_spec h, hmacro_complete, hiter_sound, hiter_complete⟩

end GE2SeedsAndVoidMacroReturnMap

/-! ## 16. Exact Assembly-Index / Even-Time Zero Count (`Zc`) Increment and Macro-Cycle Termination Equivalences for `iterVoidMacro` (`voidMacroStep_zc_increment`, `iterVoidMacro_zc_increment_and_density_laws`, `survivingSeeds_reset_iterVoidMacro_zc_and_crash_iff`) -/

section VoidMacroZcIncrement
open Rule30ZeroBoundary.IntegerForm

theorem gateNext_eq_some_iff_bit {a a' : Nat} {b : Bool} (h : gateNext a b = some a') :
    (a' = 0 → b = true) ∧ (a' ≠ 0 → b = false) := by
  cases a with
  | zero =>
    cases b <;> simp [gateNext] at h
    subst h; decide
  | succ a1 =>
    cases a1 with
    | zero =>
      cases b <;> simp [gateNext] at h
      subst h; decide
    | succ a2 =>
      cases a2 with
      | zero =>
        cases b <;> simp [gateNext] at h <;> subst h <;> decide
      | succ a3 =>
        cases a3 with
        | zero =>
          cases b <;> simp [gateNext] at h
          subst h; decide
        | succ a4 =>
          cases a4 with
          | zero =>
            cases b <;> simp [gateNext] at h
            subst h; decide
          | succ a5 =>
            cases b <;> simp [gateNext] at h

theorem zeroNext_match_and_tr_bit {y : Nat} {s s' : PhysState}
    (hm : StateMatchesSeed y s) (hb0 : y.testBit s.n = false)
    (hz : zeroNext s = some s') :
    StateMatchesSeed y s' ∧
    s'.n = s.n + 1 ∧
    s'.isOdd = !s.isOdd ∧
    nextAge s.isOdd s.age (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y s.n) =
      some s'.age := by
  have hspec := (zeroNext_spec_of_match hm).1 hb0 |>.2 s' hz
  obtain ⟨hzrow, _, hm', _, _⟩ := hspec
  obtain ⟨hn', ho', hna⟩ := zeroNext_n_isOdd_and_age hz
  have htr_eq : Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y s.n =
      piParity (physSigma s) := by
    rw [← hzrow]
    exact (zrow_rowOfNat_col1 y s.n).symm
  rw [htr_eq]
  exact ⟨hm', hn', ho', hna⟩

theorem zc_step_of_even_zeroNext {y j : Nat} {s s' : PhysState}
    (hm : StateMatchesSeed y s) (hn : s.n = 2 * j) (ho : s.isOdd = false)
    (hb0 : y.testBit s.n = false) (hz : zeroNext s = some s') :
    (s'.age = 0 →
      Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc
        (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y) (j + 1) =
      Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc
        (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y) j + 1) ∧
    (s'.age ≠ 0 →
      Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc
        (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y) (j + 1) =
      Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc
        (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y) j) := by
  obtain ⟨_, _, _, hna⟩ := zeroNext_match_and_tr_bit hm hb0 hz
  rw [ho, hn] at hna
  dsimp only [nextAge] at hna
  have hbit := gateNext_eq_some_iff_bit hna
  constructor
  · intro ha0
    have htr_false : Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y (2 * j) = false := by
      simpa using hbit.1 ha0
    simp [Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc, htr_false]
  · intro hne0
    have htr_true : Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y (2 * j) = true := by
      simpa using hbit.2 hne0
    simp [Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc, htr_true]

/-- **Single Macro-Step `Zc` Increment Theorem (`voidMacroStep_zc_increment`).**
From any post-reset ground state `s` (`StateMatchesSeed y s`, `s.n = 2 * m + 1`, `s.isOdd = true`,
`s.age = 0`), a single macro-step `voidMacroStep s = some (s', dt)` in the Zero Void (`∀ j < dt,
y.testBit (s.n + j) = false`) advances the half-horizon by `dm ∈ {3, 5}` (`dt = 2 * dm`,
`s'.n = 2 * (m + dm) + 1`), preserves `StateMatchesSeed y s'` and `s'.isOdd = true ∧ s'.age = 0`,
and increments the even-time zero count `Zc (tr y)` by exactly `+1`:
`Zc (tr y) (m + dm + 1) = Zc (tr y) (m + 1) + 1`. -/
theorem voidMacroStep_zc_increment {y m dt : Nat} {s s' : PhysState}
    (hm : StateMatchesSeed y s) (hn : s.n = 2 * m + 1)
    (ho : s.isOdd = true) (ha : s.age = 0)
    (hzeros : ∀ j < dt, y.testBit (s.n + j) = false)
    (hms : voidMacroStep s = some (s', dt)) :
    ∃ dm : Nat,
      (dm = 3 ∨ dm = 5) ∧
      dt = 2 * dm ∧
      StateMatchesSeed y s' ∧
      s'.n = 2 * (m + dm) + 1 ∧
      s'.isOdd = true ∧
      s'.age = 0 ∧
      Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc
        (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y) (m + dm + 1) =
      Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc
        (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y) (m + 1) + 1 := by
  obtain ⟨hdt, hiter, hn', ho', ha'⟩ := voidMacroStep_spec hms
  rcases hdt with rfl | rfl
  · rcases s1_eq : zeroNext s with _ | s1
    · simp [iterZeroNext, s1_eq] at hiter
    have h6_1 : iterZeroNext s1 5 = some s' := by simpa [iterZeroNext, s1_eq] using hiter
    rcases s2_eq : zeroNext s1 with _ | s2
    · simp [iterZeroNext, s2_eq] at h6_1
    have h6_2 : iterZeroNext s2 4 = some s' := by simpa [iterZeroNext, s2_eq] using h6_1
    rcases s3_eq : zeroNext s2 with _ | s3
    · simp [iterZeroNext, s3_eq] at h6_2
    have h6_3 : iterZeroNext s3 3 = some s' := by simpa [iterZeroNext, s3_eq] using h6_2
    rcases s4_eq : zeroNext s3 with _ | s4
    · simp [iterZeroNext, s4_eq] at h6_3
    have h6_4 : iterZeroNext s4 2 = some s' := by simpa [iterZeroNext, s4_eq] using h6_3
    rcases s5_eq : zeroNext s4 with _ | s5
    · simp [iterZeroNext, s5_eq] at h6_4
    have h6_5 : zeroNext s5 = some s' := by
      rw [← iterZeroNext_one s5]
      simpa [iterZeroNext, s5_eq] using h6_4
    have hb0 : y.testBit s.n = false := hzeros 0 (by omega)
    obtain ⟨hm1, hn1, ho1, hna1⟩ := zeroNext_match_and_tr_bit hm hb0 s1_eq
    have hb1 : y.testBit s1.n = false := by rw [hn1]; exact hzeros 1 (by omega)
    obtain ⟨hm2, hn2, ho2, hna2⟩ := zeroNext_match_and_tr_bit hm1 hb1 s2_eq
    have hb2 : y.testBit s2.n = false := by rw [hn2, hn1]; exact hzeros 2 (by omega)
    obtain ⟨hm3, hn3, ho3, hna3⟩ := zeroNext_match_and_tr_bit hm2 hb2 s3_eq
    have hb3 : y.testBit s3.n = false := by rw [hn3, hn2, hn1]; exact hzeros 3 (by omega)
    obtain ⟨hm4, hn4, ho4, hna4⟩ := zeroNext_match_and_tr_bit hm3 hb3 s4_eq
    have hb4 : y.testBit s4.n = false := by rw [hn4, hn3, hn2, hn1]; exact hzeros 4 (by omega)
    obtain ⟨hm5, hn5, ho5, hna5⟩ := zeroNext_match_and_tr_bit hm4 hb4 s5_eq
    have hb5 : y.testBit s5.n = false := by rw [hn5, hn4, hn3, hn2, hn1]; exact hzeros 5 (by omega)
    obtain ⟨hm6, hn6, ho6, _⟩ := zeroNext_match_and_tr_bit hm5 hb5 h6_5
    have h_o1 : s1.isOdd = false := by rw [ho1, ho]; rfl
    have h_o2 : s2.isOdd = true := by rw [ho2, h_o1]; rfl
    have h_o3 : s3.isOdd = false := by rw [ho3, h_o2]; rfl
    have h_o4 : s4.isOdd = true := by rw [ho4, h_o3]; rfl
    have h_o5 : s5.isOdd = false := by rw [ho5, h_o4]; rfl
    have ha1 := (nextAge_step_from hna1).1 ⟨ho, ha⟩
    have ha2 := (nextAge_step_from hna2).2.1 ⟨h_o1, ha1⟩
    have ha3 := (nextAge_step_from hna3).2.2.1 ⟨h_o2, ha2⟩
    have ha4 := (nextAge_step_from hna4).2.2.2.1 ⟨h_o3, ha3⟩
    have hzc1 := (zc_step_of_even_zeroNext hm1 (by omega : s1.n = 2 * (m + 1)) h_o1 hb1 s2_eq).2 (by omega)
    have hzc2 := (zc_step_of_even_zeroNext hm3 (by omega : s3.n = 2 * (m + 2)) h_o3 hb3 s4_eq).2 (by omega)
    have hzc3 := (zc_step_of_even_zeroNext hm5 (by omega : s5.n = 2 * (m + 3)) h_o5 hb5 h6_5).1 ha'
    rw [Nat.add_assoc] at hzc1 hzc2
    refine ⟨3, Or.inl rfl, rfl, hm6, by omega, ho', ha', ?_⟩
    rw [hzc3, hzc2, hzc1]
  · unfold voidMacroStep at hms
    cases h6 : iterZeroNext s 6 with
    | none => simp [h6] at hms
    | some s6 =>
      rw [h6] at hms
      dsimp only at hms
      split at hms
      · next hcond6 =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hms
        omega
      · next hnot6 =>
        have hsplit : iterZeroNext s 10 = (iterZeroNext s 6).bind (fun u => iterZeroNext u 4) :=
          iterZeroNext_add s 6 4
        rw [hiter, h6] at hsplit
        dsimp only [Option.bind] at hsplit
        have hrem : iterZeroNext s6 4 = some s' := hsplit.symm
        rcases s1_eq : zeroNext s with _ | s1
        · simp [iterZeroNext, s1_eq] at h6
        have h6_1 : iterZeroNext s1 5 = some s6 := by simpa [iterZeroNext, s1_eq] using h6
        rcases s2_eq : zeroNext s1 with _ | s2
        · simp [iterZeroNext, s2_eq] at h6_1
        have h6_2 : iterZeroNext s2 4 = some s6 := by simpa [iterZeroNext, s2_eq] using h6_1
        rcases s3_eq : zeroNext s2 with _ | s3
        · simp [iterZeroNext, s3_eq] at h6_2
        have h6_3 : iterZeroNext s3 3 = some s6 := by simpa [iterZeroNext, s3_eq] using h6_2
        rcases s4_eq : zeroNext s3 with _ | s4
        · simp [iterZeroNext, s4_eq] at h6_3
        have h6_4 : iterZeroNext s4 2 = some s6 := by simpa [iterZeroNext, s4_eq] using h6_3
        rcases s5_eq : zeroNext s4 with _ | s5
        · simp [iterZeroNext, s5_eq] at h6_4
        have h6_5 : zeroNext s5 = some s6 := by
          rw [← iterZeroNext_one s5]
          simpa [iterZeroNext, s5_eq] using h6_4
        rcases s7_eq : zeroNext s6 with _ | s7
        · simp [iterZeroNext, s7_eq] at hrem
        have hrem1 : iterZeroNext s7 3 = some s' := by simpa [iterZeroNext, s7_eq] using hrem
        rcases s8_eq : zeroNext s7 with _ | s8
        · simp [iterZeroNext, s8_eq] at hrem1
        have hrem2 : iterZeroNext s8 2 = some s' := by simpa [iterZeroNext, s8_eq] using hrem1
        rcases s9_eq : zeroNext s8 with _ | s9
        · simp [iterZeroNext, s9_eq] at hrem2
        have hrem3 : zeroNext s9 = some s' := by
          rw [← iterZeroNext_one s9]
          simpa [iterZeroNext, s9_eq] using hrem2
        have hb0 : y.testBit s.n = false := hzeros 0 (by omega)
        obtain ⟨hm1, hn1, ho1, hna1⟩ := zeroNext_match_and_tr_bit hm hb0 s1_eq
        have hb1 : y.testBit s1.n = false := by rw [hn1]; exact hzeros 1 (by omega)
        obtain ⟨hm2, hn2, ho2, hna2⟩ := zeroNext_match_and_tr_bit hm1 hb1 s2_eq
        have hb2 : y.testBit s2.n = false := by rw [hn2, hn1]; exact hzeros 2 (by omega)
        obtain ⟨hm3, hn3, ho3, hna3⟩ := zeroNext_match_and_tr_bit hm2 hb2 s3_eq
        have hb3 : y.testBit s3.n = false := by rw [hn3, hn2, hn1]; exact hzeros 3 (by omega)
        obtain ⟨hm4, hn4, ho4, hna4⟩ := zeroNext_match_and_tr_bit hm3 hb3 s4_eq
        have hb4 : y.testBit s4.n = false := by rw [hn4, hn3, hn2, hn1]; exact hzeros 4 (by omega)
        obtain ⟨hm5, hn5, ho5, hna5⟩ := zeroNext_match_and_tr_bit hm4 hb4 s5_eq
        have hb5 : y.testBit s5.n = false := by rw [hn5, hn4, hn3, hn2, hn1]; exact hzeros 5 (by omega)
        obtain ⟨hm6, hn6, ho6, hna6⟩ := zeroNext_match_and_tr_bit hm5 hb5 h6_5
        have hb6 : y.testBit s6.n = false := by rw [hn6, hn5, hn4, hn3, hn2, hn1]; exact hzeros 6 (by omega)
        obtain ⟨hm7, hn7, ho7, hna7⟩ := zeroNext_match_and_tr_bit hm6 hb6 s7_eq
        have hb7 : y.testBit s7.n = false := by rw [hn7, hn6, hn5, hn4, hn3, hn2, hn1]; exact hzeros 7 (by omega)
        obtain ⟨hm8, hn8, ho8, hna8⟩ := zeroNext_match_and_tr_bit hm7 hb7 s8_eq
        have hb8 : y.testBit s8.n = false := by rw [hn8, hn7, hn6, hn5, hn4, hn3, hn2, hn1]; exact hzeros 8 (by omega)
        obtain ⟨hm9, hn9, ho9, hna9⟩ := zeroNext_match_and_tr_bit hm8 hb8 s9_eq
        have hb9 : y.testBit s9.n = false := by rw [hn9, hn8, hn7, hn6, hn5, hn4, hn3, hn2, hn1]; exact hzeros 9 (by omega)
        obtain ⟨hm10, hn10, _, _⟩ := zeroNext_match_and_tr_bit hm9 hb9 hrem3
        have h_o1 : s1.isOdd = false := by rw [ho1, ho]; rfl
        have h_o2 : s2.isOdd = true := by rw [ho2, h_o1]; rfl
        have h_o3 : s3.isOdd = false := by rw [ho3, h_o2]; rfl
        have h_o4 : s4.isOdd = true := by rw [ho4, h_o3]; rfl
        have h_o5 : s5.isOdd = false := by rw [ho5, h_o4]; rfl
        have h_o6 : s6.isOdd = true := by rw [ho6, h_o5]; rfl
        have h_o7 : s7.isOdd = false := by rw [ho7, h_o6]; rfl
        have h_o8 : s8.isOdd = true := by rw [ho8, h_o7]; rfl
        have h_o9 : s9.isOdd = false := by rw [ho9, h_o8]; rfl
        have ha1 := (nextAge_step_from hna1).1 ⟨ho, ha⟩
        have ha2 := (nextAge_step_from hna2).2.1 ⟨h_o1, ha1⟩
        have ha3 := (nextAge_step_from hna3).2.2.1 ⟨h_o2, ha2⟩
        have ha4 := (nextAge_step_from hna4).2.2.2.1 ⟨h_o3, ha3⟩
        have ha5 := (nextAge_step_from hna5).2.2.2.2.1 ⟨h_o4, ha4⟩
        have ha6 := (nextAge_step_from hna6).2.2.2.2.2.1 ⟨h_o5, ha5⟩
        have ha6_3 : s6.age = 3 := by
          rcases ha6 with ha6_0 | ha6_3
          · exfalso; apply hnot6; simp [h_o6, ha6_0]
          · exact ha6_3
        have ha7 := (nextAge_step_from hna7).2.2.2.2.2.2.1 ⟨h_o6, ha6_3⟩
        have ha8 := (nextAge_step_from hna8).2.2.2.2.2.2.2.1 ⟨h_o7, ha7⟩
        have hzc1 := (zc_step_of_even_zeroNext hm1 (by omega : s1.n = 2 * (m + 1)) h_o1 hb1 s2_eq).2 (by omega)
        have hzc2 := (zc_step_of_even_zeroNext hm3 (by omega : s3.n = 2 * (m + 2)) h_o3 hb3 s4_eq).2 (by omega)
        have hzc3 := (zc_step_of_even_zeroNext hm5 (by omega : s5.n = 2 * (m + 3)) h_o5 hb5 h6_5).2 (by omega)
        have hzc4 := (zc_step_of_even_zeroNext hm7 (by omega : s7.n = 2 * (m + 4)) h_o7 hb7 s8_eq).2 (by omega)
        have hzc5 := (zc_step_of_even_zeroNext hm9 (by omega : s9.n = 2 * (m + 5)) h_o9 hb9 hrem3).1 ha'
        rw [Nat.add_assoc] at hzc1 hzc2 hzc3 hzc4
        refine ⟨5, Or.inr rfl, rfl, hm10, by omega, ho', ha', ?_⟩
        rw [hzc5, hzc4, hzc3, hzc2, hzc1]

/-- **Exact Assembly-Index (`Zc`) Increment and Two-Sided Density Laws Across `k` Cycles of `iterVoidMacro`
(`iterVoidMacro_zc_increment_and_density_laws`).**
For every cycle count `k : Nat`, seed `y : Nat`, half-horizon `m : Nat`, and states `s s' : PhysState`,
if `StateMatchesSeed y s`, `s.n = 2 * m + 1`, `s.isOdd = true`, `s.age = 0`,
`∀ j < 10 * k, y.testBit (s.n + j) = false`, and `iterVoidMacro s k = some s'`, then there exists
an exact half-horizon advance `dm : Nat` such that:
1. `3 * k ≤ dm ∧ dm ≤ 5 * k`,
2. `StateMatchesSeed y s' ∧ s'.n = 2 * (m + dm) + 1 ∧ s'.isOdd = true ∧ s'.age = 0`,
3. `Zc (tr y) (m + dm + 1) = Zc (tr y) (m + 1) + k` (every macro-cycle increments the even-time
   zero count `Zc` by exactly `+1`), and
4. For `s = initPhysState` (`m = 0`) and any `y` with `∀ j < 10 * k + 1, y.testBit j = false`,
   `iterVoidMacro initPhysState k = some s'` implies `Zc (tr y) (dm + 1) = k + 1`. -/
theorem iterVoidMacro_zc_increment_and_density_laws :
    (∀ k y m : Nat, ∀ s s' : PhysState,
      StateMatchesSeed y s →
      s.n = 2 * m + 1 →
      s.isOdd = true →
      s.age = 0 →
      (∀ j < 10 * k, y.testBit (s.n + j) = false) →
      iterVoidMacro s k = some s' →
        ∃ dm : Nat,
          3 * k ≤ dm ∧ dm ≤ 5 * k ∧
          StateMatchesSeed y s' ∧
          s'.n = 2 * (m + dm) + 1 ∧
          s'.isOdd = true ∧
          s'.age = 0 ∧
          Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc
            (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y) (m + dm + 1) =
          Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc
            (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y) (m + 1) + k) ∧
    (∀ k y : Nat, ∀ s' : PhysState,
      (∀ j < 10 * k + 1, y.testBit j = false) →
      iterVoidMacro initPhysState k = some s' →
        ∃ dm : Nat,
          3 * k ≤ dm ∧ dm ≤ 5 * k ∧
          s'.n = 2 * dm + 1 ∧
          Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc
            (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y) (dm + 1) = k + 1) := by
  have hmain : ∀ k y m : Nat, ∀ s s' : PhysState,
      StateMatchesSeed y s →
      s.n = 2 * m + 1 →
      s.isOdd = true →
      s.age = 0 →
      (∀ j < 10 * k, y.testBit (s.n + j) = false) →
      iterVoidMacro s k = some s' →
        ∃ dm : Nat,
          3 * k ≤ dm ∧ dm ≤ 5 * k ∧
          StateMatchesSeed y s' ∧
          s'.n = 2 * (m + dm) + 1 ∧
          s'.isOdd = true ∧
          s'.age = 0 ∧
          Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc
            (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y) (m + dm + 1) =
          Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc
            (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y) (m + 1) + k := by
    intro k
    induction k with
    | zero =>
      intro y m s s' hm hn ho ha _ hiter
      simp only [iterVoidMacro, Option.some.injEq] at hiter
      subst hiter
      exact ⟨0, by omega, by omega, hm, by omega, ho, ha, by simp⟩
    | succ k ih =>
      intro y m s s' hm hn ho ha hzeros hiter
      simp only [iterVoidMacro] at hiter
      cases hms : voidMacroStep s with
      | none => simp [hms] at hiter
      | some pr =>
        rcases pr with ⟨s1, dt⟩
        rw [hms] at hiter
        have hdt_le : dt ≤ 10 := by
          rcases (voidMacroStep_spec hms).1 with rfl | rfl <;> omega
        have hz_dt : ∀ j < dt, y.testBit (s.n + j) = false := fun j hj =>
          hzeros j (by omega)
        obtain ⟨dm1, hdm1_35, hdt_eq, hm1, hn1, ho1, ha1, hzc1⟩ :=
          voidMacroStep_zc_increment hm hn ho ha hz_dt hms
        have hz_rem : ∀ j < 10 * k, y.testBit (s1.n + j) = false := by
          intro j hj
          rw [hn1, show 2 * (m + dm1) + 1 + j = s.n + (dt + j) by omega]
          exact hzeros (dt + j) (by omega)
        obtain ⟨dm2, hdm2_lo, hdm2_hi, hm', hn', ho', ha', hzc2⟩ :=
          ih y (m + dm1) s1 s' hm1 hn1 ho1 ha1 hz_rem hiter
        refine ⟨dm1 + dm2, ?_, ?_, hm', ?_, ho', ha', ?_⟩
        · rcases hdm1_35 with rfl | rfl <;> omega
        · rcases hdm1_35 with rfl | rfl <;> omega
        · rw [← Nat.add_assoc]; exact hn'
        · rw [show m + (dm1 + dm2) + 1 = m + dm1 + dm2 + 1 by omega]
          omega
  refine ⟨hmain, fun k y s' hzeros hiter => ?_⟩
  have hy0 : y.testBit 0 = false := hzeros 0 (by omega)
  have hm0 : StateMatchesSeed y initPhysState :=
    ⟨by decide, by decide, hy0, by simp [initPhysState, trace, acceptFinal],
      by simp [initPhysState, antidiag, iter, hy0], rfl⟩
  have hz0 : ∀ j < 10 * k, y.testBit (initPhysState.n + j) = false := by
    intro j hj
    change y.testBit (1 + j) = false
    exact hzeros (1 + j) (by omega)
  obtain ⟨dm, hlo, hhi, _, hn', _, _, hzc⟩ :=
    hmain k y 0 initPhysState s' hm0 rfl rfl rfl hz0 hiter
  have hzc0 : Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc
      (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y) 1 = 1 := by
    have htr0 : Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y 0 = false := hy0
    simp [Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc, htr0]
  refine ⟨dm, hlo, hhi, by simpa using hn', ?_⟩
  simpa [hzc0, Nat.add_comm] using hzc

/-- **Macro-Cycle Void Termination Equivalence and Canonical Seed `Zc` Evolution
(`survivingSeeds_reset_iterVoidMacro_zc_and_crash_iff`).**
1. For any post-reset ground state `s` (`s.isOdd = true ∧ s.age = 0`), microscopic Void termination
   `∃ L, iterZeroNext s L = none` holds if and only if macro-cycle Void termination
   `∃ k, iterVoidMacro s k = none` holds.
2. For any canonical surviving seed `y ∈ survivingSeeds (2 * m + 1)` whose state
   `physStateOf y (2 * m + 1) = some s` is in the ground state (`s.age = 0`), if
   `iterVoidMacro s k = some s'`, then there exists `dm` with `3 * k ≤ dm ≤ 5 * k` such that
   `y ∈ survivingSeeds (2 * (m + dm) + 1)` and
   `Zc (tr y) (m + dm + 1) = Zc (tr y) (m + 1) + k`. -/
theorem survivingSeeds_reset_iterVoidMacro_zc_and_crash_iff :
    (∀ s : PhysState, s.isOdd = true → s.age = 0 →
      ((∃ L : Nat, iterZeroNext s L = none) ↔
        (∃ k : Nat, iterVoidMacro s k = none))) ∧
    (∀ m k y : Nat, ∀ s s' : PhysState,
      y ∈ survivingSeeds (2 * m + 1) →
      physStateOf y (2 * m + 1) = some s →
      s.age = 0 →
      iterVoidMacro s k = some s' →
        ∃ dm : Nat,
          3 * k ≤ dm ∧ dm ≤ 5 * k ∧
          y ∈ survivingSeeds (2 * (m + dm) + 1) ∧
          Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc
            (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y) (m + dm + 1) =
          Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.Zc
            (Ruliology.CellularAutomata.Rule30PeriodTwoWidth13.tr y) (m + 1) + k) := by
  have hlaws := voidMacroStep_and_iterVoidMacro_dilation_laws
  refine ⟨fun s ho ha => ?_, fun m k y s s' hy hps ha hiter => ?_⟩
  · constructor
    · rintro ⟨L, hnone⟩
      refine ⟨L, ?_⟩
      cases hm : iterVoidMacro s L with
      | none => rfl
      | some s' =>
        exfalso
        obtain ⟨L', hlo, _, hstep, _⟩ := hlaws.2.2.1 L s s' hm
        have hle : L ≤ L' := by omega
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
        rw [hd, iterZeroNext_add, hnone] at hstep
        simp at hstep
    · rintro ⟨k, hnone⟩
      refine ⟨10 * k, ?_⟩
      cases h10k : iterZeroNext s (10 * k) with
      | none => rfl
      | some _ =>
        exfalso
        have his : (iterVoidMacro s k).isSome = true :=
          hlaws.2.2.2 k s ho ha (by simp [h10k])
        rw [hnone] at his
        simp at his
  · obtain ⟨hlt_y, _⟩ := (mem_survivingSeeds_iff_and_survivesTo_iff (2 * m + 1) y).1.mp hy
    obtain ⟨hn_eq, hm⟩ := physStateOf_sound y (2 * m + 1) s hps
    have hn : s.n = 2 * m + 1 := hn_eq.symm
    have ho : s.isOdd = true := by
      have ho_mod := hm.2.1
      rw [hn, show (2 * m + 1) % 2 = 1 by omega] at ho_mod
      exact ho_mod
    have hzeros : ∀ j < 10 * k, y.testBit (s.n + j) = false := by
      intro j _
      apply Nat.testBit_lt_two_pow
      rw [hn]
      exact Nat.lt_of_lt_of_le hlt_y (Nat.pow_le_pow_right (by decide) (by omega))
    obtain ⟨dm, hlo, hhi, hm', hn', _, _, hzc⟩ :=
      iterVoidMacro_zc_increment_and_density_laws.1 k y m s s' hm hn ho ha hzeros hiter
    have hsurv' : SurvivesTo y (2 * (m + dm) + 1) := by
      have hs := stateMatchesSeed_survivesTo hm'
      rwa [hn'] at hs
    have hlt' : y < 2 ^ (2 * (m + dm) + 1) :=
      Nat.lt_of_lt_of_le hlt_y (Nat.pow_le_pow_right (by decide) (by omega))
    have hy' : y ∈ survivingSeeds (2 * (m + dm) + 1) :=
      (mem_survivingSeeds_iff_and_survivesTo_iff (2 * (m + dm) + 1) y).1.mpr ⟨hlt', hsurv'⟩
    exact ⟨dm, hlo, hhi, hy', hzc⟩

end VoidMacroZcIncrement

/-! ## 17. First-Active-Bit Inward Rescue Wavefront, 8-Step Ground-State Synchronization, and Pure Ground-State Macro-Cycle Closure Equivalence (`void_crash_forces_first_active_bit_and_trace_flip`, `void_odd_state_reaches_ground_reset_within_eight`, `q01Gap_and_massDiverges_iff_reset_iterVoidMacro_crash`) -/

section FirstActiveBitAndMacroClosure
open Rule30ZeroBoundary.IntegerForm

theorem exists_first_diff_bit_of_mod_eq {y z K L : Nat}
    (hmod : z % 2 ^ K = y % 2 ^ K) (hne : z % 2 ^ (K + L) ≠ y % 2 ^ (K + L)) :
    ∃ k : Nat,
      K ≤ k ∧ k < K + L ∧
      z % 2 ^ k = y % 2 ^ k ∧
      z.testBit k ≠ y.testBit k := by
  induction L with
  | zero =>
    exfalso
    rw [Nat.add_zero] at hne
    exact hne hmod
  | succ L ih =>
    by_cases hmod_L : z % 2 ^ (K + L) = y % 2 ^ (K + L)
    · refine ⟨K + L, by omega, by omega, hmod_L, ?_⟩
      intro hbit_eq
      apply hne
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
      by_cases hi : i < K + (L + 1)
      · simp only [decide_eq_true hi, Bool.true_and]
        by_cases hiL : i < K + L
        · have h1 : (z % 2 ^ (K + L)).testBit i = z.testBit i := by
            rw [Nat.testBit_mod_two_pow, decide_eq_true hiL, Bool.true_and]
          have h2 : (y % 2 ^ (K + L)).testBit i = y.testBit i := by
            rw [Nat.testBit_mod_two_pow, decide_eq_true hiL, Bool.true_and]
          rw [← h1, ← h2, hmod_L]
        · have hieq : i = K + L := by omega
          rw [hieq, hbit_eq]
      · simp [hi]
    · obtain ⟨k, hk_lo, hk_hi, hk_mod, hk_diff⟩ := ih hmod_L
      exact ⟨k, hk_lo, by omega, hk_mod, hk_diff⟩

/-- **First-Active-Bit Inward Rescue Wavefront Theorem
(`void_crash_forces_first_active_bit_and_trace_flip`).**
Whenever `voidOrbit y K L = none` for a canonical surviving seed `y ∈ survivingSeeds K` (`K ≥ 1`),
every surviving extension `z ∈ survivingSeeds (K + L)` with `z % 2 ^ K = y` has a first active
rescue bit at depth `k ∈ [K, K + L)` such that:
1. `K ≤ k ∧ k < K + L`, `z % 2 ^ k = y`, `z.testBit k = true`, and `y.testBit k = false`,
2. For every step `d ≤ k`, `(iter F d z) % 2 ^ (k - d) = (iter F d y) % 2 ^ (k - d)` and
   `(iter F d z).testBit (k - d) = !(iter F d y).testBit (k - d)`, and
3. `trace z k = trace y k ∧ (iter F k z).testBit 0 = !(iter F k y).testBit 0` (the rescue bit at
   depth `k` reaches the center column at exact time `t = k` and flips the center trace bit). -/
theorem void_crash_forces_first_active_bit_and_trace_flip (K L y z : Nat)
    (hK : 1 ≤ K) (hy : y ∈ survivingSeeds K) (hnone : voidOrbit y K L = none)
    (hz : z ∈ survivingSeeds (K + L)) (hmod : z % 2 ^ K = y) :
    popcount y + 1 ≤ popcount z ∧
    ∃ k : Nat,
      K ≤ k ∧ k < K + L ∧
      z % 2 ^ k = y ∧
      z.testBit k = true ∧
      y.testBit k = false ∧
      (∀ d : Nat, d ≤ k →
        (iter F d z) % 2 ^ (k - d) = (iter F d y) % 2 ^ (k - d) ∧
        (iter F d z).testBit (k - d) = !(iter F d y).testBit (k - d)) ∧
      trace z k = trace y k ∧
      (iter F k z).testBit 0 = !(iter F k y).testBit 0 := by
  have hstep := (survivingSeeds_void_crash_forces_weight_step K L y hK hy).2 hnone
  have hpop : popcount y + 1 ≤ popcount z := (hstep.2 z hz hmod).1
  obtain ⟨hlt_y, _⟩ := (mem_survivingSeeds_iff_and_survivesTo_iff K y).1.mp hy
  obtain ⟨hlt_z, hsurv_z⟩ := (mem_survivingSeeds_iff_and_survivesTo_iff (K + L) z).1.mp hz
  have hlt_y_KL : y < 2 ^ (K + L) :=
    Nat.lt_of_lt_of_le hlt_y (Nat.pow_le_pow_right (by decide) (by omega))
  have hne : z % 2 ^ (K + L) ≠ y % 2 ^ (K + L) := by
    rw [Nat.mod_eq_of_lt hlt_z, Nat.mod_eq_of_lt hlt_y_KL]
    intro heq
    rw [heq] at hsurv_z
    exact hstep.1 hsurv_z
  have hmod_yy : z % 2 ^ K = y % 2 ^ K := by rw [hmod, Nat.mod_eq_of_lt hlt_y]
  obtain ⟨k, hk_lo, hk_hi, hk_mod, hk_diff⟩ := exists_first_diff_bit_of_mod_eq hmod_yy hne
  have hy_lt_k : y < 2 ^ k :=
    Nat.lt_of_lt_of_le hlt_y (Nat.pow_le_pow_right (by decide) hk_lo)
  have hy_bit_k : y.testBit k = false := Nat.testBit_lt_two_pow hy_lt_k
  have hz_bit_k : z.testBit k = true := by
    cases hzk : z.testBit k
    · exfalso; apply hk_diff; rw [hzk, hy_bit_k]
    · rfl
  have hzk_eq_y : z % 2 ^ k = y := by
    rw [hk_mod, Nat.mod_eq_of_lt hy_lt_k]
  have hwave := inward_distinction_wavefront_and_first_trace_diff z y k hk_mod hk_diff
  exact ⟨hpop, k, hk_lo, hk_hi, hzk_eq_y, hz_bit_k, hy_bit_k, hwave.1, hwave.2.1, hwave.2.2⟩

/-- **Universal 8-Step Ground-State Synchronization Theorem
(`void_odd_state_reaches_ground_reset_within_eight`).**
From any odd-horizon state `s : PhysState` with `s.isOdd = true` and `s.age < 5`, if
`(iterZeroNext s 8).isSome = true`, then there exists `j ≤ 4` and `s' : PhysState` such that
`iterZeroNext s (2 * j) = some s'`, `s'.isOdd = true`, and `s'.age = 0`. -/
theorem gateNext_some_age_lt_five {a a' : Nat} {z : Bool} (h : gateNext a z = some a') :
    a < 5 := by
  rcases a with _ | _ | _ | _ | _ | a5 <;> cases z <;> simp [gateNext] at h <;> omega

theorem void_odd_state_reaches_ground_reset_within_eight (s : PhysState)
    (ho : s.isOdd = true)
    (his : (iterZeroNext s 8).isSome = true) :
    ∃ j : Nat, j ≤ 4 ∧ ∃ s' : PhysState,
      iterZeroNext s (2 * j) = some s' ∧ s'.isOdd = true ∧ s'.age = 0 := by
  obtain ⟨s8, h8⟩ := Option.isSome_iff_exists.mp his
  rcases s1_eq : zeroNext s with _ | s1
  · simp [iterZeroNext, s1_eq] at h8
  have h8_1 : iterZeroNext s1 7 = some s8 := by simpa [iterZeroNext, s1_eq] using h8
  rcases s2_eq : zeroNext s1 with _ | s2
  · simp [iterZeroNext, s2_eq] at h8_1
  have h8_2 : iterZeroNext s2 6 = some s8 := by simpa [iterZeroNext, s2_eq] using h8_1
  rcases s3_eq : zeroNext s2 with _ | s3
  · simp [iterZeroNext, s3_eq] at h8_2
  have h8_3 : iterZeroNext s3 5 = some s8 := by simpa [iterZeroNext, s3_eq] using h8_2
  rcases s4_eq : zeroNext s3 with _ | s4
  · simp [iterZeroNext, s4_eq] at h8_3
  have h8_4 : iterZeroNext s4 4 = some s8 := by simpa [iterZeroNext, s4_eq] using h8_3
  rcases s5_eq : zeroNext s4 with _ | s5
  · simp [iterZeroNext, s5_eq] at h8_4
  have h8_5 : iterZeroNext s5 3 = some s8 := by simpa [iterZeroNext, s5_eq] using h8_4
  rcases s6_eq : zeroNext s5 with _ | s6
  · simp [iterZeroNext, s6_eq] at h8_5
  have h8_6 : iterZeroNext s6 2 = some s8 := by simpa [iterZeroNext, s6_eq] using h8_5
  rcases s7_eq : zeroNext s6 with _ | s7
  · simp [iterZeroNext, s7_eq] at h8_6
  have h8_7 : zeroNext s7 = some s8 := by
    rw [← iterZeroNext_one s7]
    simpa [iterZeroNext, s7_eq] using h8_6
  obtain ⟨_, ho1, hna1⟩ := zeroNext_n_isOdd_and_age s1_eq
  obtain ⟨_, ho2, hna2⟩ := zeroNext_n_isOdd_and_age s2_eq
  obtain ⟨_, ho3, hna3⟩ := zeroNext_n_isOdd_and_age s3_eq
  obtain ⟨_, ho4, hna4⟩ := zeroNext_n_isOdd_and_age s4_eq
  obtain ⟨_, ho5, hna5⟩ := zeroNext_n_isOdd_and_age s5_eq
  obtain ⟨_, ho6, hna6⟩ := zeroNext_n_isOdd_and_age s6_eq
  obtain ⟨_, ho7, hna7⟩ := zeroNext_n_isOdd_and_age s7_eq
  obtain ⟨_, ho8, hna8⟩ := zeroNext_n_isOdd_and_age h8_7
  have h_o1 : s1.isOdd = false := by rw [ho1, ho]; rfl
  have h_o2 : s2.isOdd = true := by rw [ho2, h_o1]; rfl
  have h_o3 : s3.isOdd = false := by rw [ho3, h_o2]; rfl
  have h_o4 : s4.isOdd = true := by rw [ho4, h_o3]; rfl
  have h_o5 : s5.isOdd = false := by rw [ho5, h_o4]; rfl
  have h_o6 : s6.isOdd = true := by rw [ho6, h_o5]; rfl
  have h_o7 : s7.isOdd = false := by rw [ho7, h_o6]; rfl
  have h_o8 : s8.isOdd = true := by rw [ho8, h_o7]; rfl
  have hit0 : iterZeroNext s 0 = some s := rfl
  have hit2 : iterZeroNext s 2 = some s2 := by simp [iterZeroNext, s1_eq, s2_eq]
  have hit4 : iterZeroNext s 4 = some s4 := by simp [iterZeroNext, s1_eq, s2_eq, s3_eq, s4_eq]
  have hit6 : iterZeroNext s 6 = some s6 := by
    simp [iterZeroNext, s1_eq, s2_eq, s3_eq, s4_eq, s5_eq, s6_eq]
  have hit8 : iterZeroNext s 8 = some s8 := h8
  have ha1_eq : s1.age = s.age := by
    rw [ho] at hna1
    cases hbit : Ruliology.CellularAutomata.Rule30ZeroCoastBridge.piParity (physSigma s) <;>
      simp [nextAge, hbit] at hna1
    exact hna1.symm
  have ha_lt5 : s.age < 5 := by
    rw [h_o1] at hna2
    dsimp only [nextAge] at hna2
    have hlt1 := gateNext_some_age_lt_five hna2
    omega
  have hage_cases : s.age = 0 ∨ s.age = 1 ∨ s.age = 2 ∨ s.age = 3 ∨ s.age = 4 := by omega
  rcases hage_cases with ha0 | ha1 | ha2 | ha3 | ha4
  · exact ⟨0, by omega, s, hit0, ho, ha0⟩
  · have a1 := (nextAge_step_from hna1).2.2.1 ⟨ho, ha1⟩
    have a2 := (nextAge_step_from hna2).2.2.2.1 ⟨h_o1, a1⟩
    have a3 := (nextAge_step_from hna3).2.2.2.2.1 ⟨h_o2, a2⟩
    have a4 := (nextAge_step_from hna4).2.2.2.2.2.1 ⟨h_o3, a3⟩
    rcases a4 with a4_0 | a4_3
    · exact ⟨2, by omega, s4, hit4, h_o4, a4_0⟩
    · have a5 := (nextAge_step_from hna5).2.2.2.2.2.2.1 ⟨h_o4, a4_3⟩
      have a6 := (nextAge_step_from hna6).2.2.2.2.2.2.2.1 ⟨h_o5, a5⟩
      have a7 := (nextAge_step_from hna7).2.2.2.2.2.2.2.2.1 ⟨h_o6, a6⟩
      have a8 := (nextAge_step_from hna8).2.2.2.2.2.2.2.2.2 ⟨h_o7, a7⟩
      exact ⟨4, by omega, s8, hit8, h_o8, a8⟩
  · have a1 := (nextAge_step_from hna1).2.2.2.2.1 ⟨ho, ha2⟩
    have a2 := (nextAge_step_from hna2).2.2.2.2.2.1 ⟨h_o1, a1⟩
    rcases a2 with a2_0 | a2_3
    · exact ⟨1, by omega, s2, hit2, h_o2, a2_0⟩
    · have a3 := (nextAge_step_from hna3).2.2.2.2.2.2.1 ⟨h_o2, a2_3⟩
      have a4 := (nextAge_step_from hna4).2.2.2.2.2.2.2.1 ⟨h_o3, a3⟩
      have a5 := (nextAge_step_from hna5).2.2.2.2.2.2.2.2.1 ⟨h_o4, a4⟩
      have a6 := (nextAge_step_from hna6).2.2.2.2.2.2.2.2.2 ⟨h_o5, a5⟩
      exact ⟨3, by omega, s6, hit6, h_o6, a6⟩
  · have a1 := (nextAge_step_from hna1).2.2.2.2.2.2.1 ⟨ho, ha3⟩
    have a2 := (nextAge_step_from hna2).2.2.2.2.2.2.2.1 ⟨h_o1, a1⟩
    have a3 := (nextAge_step_from hna3).2.2.2.2.2.2.2.2.1 ⟨h_o2, a2⟩
    have a4 := (nextAge_step_from hna4).2.2.2.2.2.2.2.2.2 ⟨h_o3, a3⟩
    exact ⟨2, by omega, s4, hit4, h_o4, a4⟩
  · have a1 := (nextAge_step_from hna1).2.2.2.2.2.2.2.2.1 ⟨ho, ha4⟩
    have a2 := (nextAge_step_from hna2).2.2.2.2.2.2.2.2.2 ⟨h_o1, a1⟩
    exact ⟨1, by omega, s2, hit2, h_o2, a2⟩

/-- **Pure Ground-State Macro-Cycle Closure Equivalence
(`q01Gap_and_massDiverges_iff_reset_iterVoidMacro_crash`).**
Proves unconditionally that `FiniteSeedsTerminate`, `MassDiverges`, and `Rule30GateTrap.Q01Gap`
are equivalent to macro-cycle Void termination (`∃ k, iterVoidMacro s k = none`) restricted
purely to canonical surviving seeds `y ∈ survivingSeeds (2 * m + 1)` at post-reset ground states
(`physStateOf y (2 * m + 1) = some s` with `s.age = 0`). -/
theorem q01Gap_and_massDiverges_iff_reset_iterVoidMacro_crash :
    (FiniteSeedsTerminate ↔
      (∀ m : Nat, ∀ y ∈ survivingSeeds (2 * m + 1), ∀ s : PhysState,
        physStateOf y (2 * m + 1) = some s → s.age = 0 →
        ∃ k : Nat, iterVoidMacro s k = none)) ∧
    (MassDiverges ↔
      (∀ m : Nat, ∀ y ∈ survivingSeeds (2 * m + 1), ∀ s : PhysState,
        physStateOf y (2 * m + 1) = some s → s.age = 0 →
        ∃ k : Nat, iterVoidMacro s k = none)) ∧
    (Ruliology.CellularAutomata.Rule30GateTrap.Q01Gap ↔
      (∀ m : Nat, ∀ y ∈ survivingSeeds (2 * m + 1), ∀ s : PhysState,
        physStateOf y (2 * m + 1) = some s → s.age = 0 →
        ∃ k : Nat, iterVoidMacro s k = none)) := by
  have hfin_iff : FiniteSeedsTerminate ↔
      (∀ m : Nat, ∀ y ∈ survivingSeeds (2 * m + 1), ∀ s : PhysState,
        physStateOf y (2 * m + 1) = some s → s.age = 0 →
        ∃ k : Nat, iterVoidMacro s k = none) := by
    constructor
    · intro hfin m y hy s hps ha
      obtain ⟨L, hnone⟩ := q01Gap_and_massDiverges_iff_survivingSeeds_void_crash.1.mp hfin
        (2 * m + 1) (by omega) y hy
      unfold voidOrbit at hnone
      rw [hps] at hnone
      dsimp only [Option.bind] at hnone
      obtain ⟨hn_eq, hm⟩ := physStateOf_sound y (2 * m + 1) s hps
      have ho : s.isOdd = true := by
        have ho_mod := hm.2.1
        rw [← hn_eq, show (2 * m + 1) % 2 = 1 by omega] at ho_mod
        exact ho_mod
      exact (survivingSeeds_reset_iterVoidMacro_zc_and_crash_iff.1 s ho ha).mp ⟨L, hnone⟩
    · intro hreset y
      let m0 := y + 1
      have hlt0 : y < 2 ^ (2 * m0 + 1) :=
        Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by decide) (by omega))
      by_cases hs8 : SurvivesTo y (2 * m0 + 1 + 8)
      · have hs0 : SurvivesTo y (2 * m0 + 1) :=
          survivesTo_mono (by omega : 2 * m0 + 1 ≤ 2 * m0 + 1 + 8) hs8
        obtain ⟨s0, hps0, hm0, hn0⟩ := physStateOf_isSome_of_survives (by omega) hs0
        have ho0 : s0.isOdd = true := by
          have ho_mod := hm0.2.1
          rw [hn0, show (2 * m0 + 1) % 2 = 1 by omega] at ho_mod
          exact ho_mod
        have hzeros8 : ∀ j < 8, y.testBit (s0.n + j) = false := by
          intro j _
          apply Nat.testBit_lt_two_pow
          rw [hn0]
          exact Nat.lt_of_lt_of_le hlt0 (Nat.pow_le_pow_right (by decide) (by omega))
        have his8 : (iterZeroNext s0 8).isSome = true := by
          have hiff8 := iterZeroNext_isSome_iff_survives 8 hm0 hzeros8
          rw [hn0] at hiff8
          exact hiff8.mpr hs8
        obtain ⟨j, hj_le, s', hstep2j, ho', ha'⟩ :=
          void_odd_state_reaches_ground_reset_within_eight s0 ho0 his8
        let m1 := m0 + j
        have hn' : s'.n = 2 * m1 + 1 := by
          have hneq := iterZeroNext_n_eq (2 * j) hstep2j
          omega
        have hm' : StateMatchesSeed y s' := by
          have hsurv_m1 : SurvivesTo y (2 * m1 + 1) :=
            survivesTo_mono (by omega : 2 * m1 + 1 ≤ 2 * m0 + 1 + 8) hs8
          obtain ⟨s_can, hps_can, hm_can, hn_can⟩ :=
            physStateOf_isSome_of_survives (by omega) hsurv_m1
          -- Show iterZeroNext preserves StateMatchesSeed via zeroNext_spec_of_match
          have hiter_match : ∀ (d : Nat) {u v : PhysState},
              StateMatchesSeed y u →
              (∀ i < d, y.testBit (u.n + i) = false) →
              iterZeroNext u d = some v →
              StateMatchesSeed y v := by
            intro d
            induction d with
            | zero =>
              intro u v hmu _ h0
              simp only [iterZeroNext, Option.some.injEq] at h0
              rwa [← h0]
            | succ d ih =>
              intro u v hmu hz_d hsucc
              simp only [iterZeroNext] at hsucc
              cases hzu : zeroNext u with
              | none => simp [hzu] at hsucc
              | some u1 =>
                rw [hzu] at hsucc
                have hbu : y.testBit u.n = false := hz_d 0 (by omega)
                have hmu1 := ((zeroNext_spec_of_match hmu).1 hbu).2 u1 hzu |>.2.2.1
                have hnu1 := (zeroNext_n_isOdd_and_age hzu).1
                apply ih hmu1 _ hsucc
                intro i hi
                rw [hnu1, show u.n + 1 + i = u.n + (i + 1) by omega]
                exact hz_d (i + 1) (by omega)
          exact hiter_match (2 * j) hm0 (fun i hi => hzeros8 i (by omega)) hstep2j
        have hps' : physStateOf y (2 * m1 + 1) = some s' :=
          (physStateOf_spec y (2 * m1 + 1) s').mpr ⟨hn'.symm, hm'⟩
        have hsurv_m1 : SurvivesTo y (2 * m1 + 1) := by
          have hs := stateMatchesSeed_survivesTo hm'
          rwa [hn'] at hs
        have hlt_m1 : y < 2 ^ (2 * m1 + 1) :=
          Nat.lt_of_lt_of_le hlt0 (Nat.pow_le_pow_right (by decide) (by omega))
        have hy_mem : y ∈ survivingSeeds (2 * m1 + 1) :=
          (mem_survivingSeeds_iff_and_survivesTo_iff (2 * m1 + 1) y).1.mpr ⟨hlt_m1, hsurv_m1⟩
        obtain ⟨k, hmacro_none⟩ := hreset m1 y hy_mem s' hps' ha'
        obtain ⟨L, hzero_none⟩ :=
          (survivingSeeds_reset_iterVoidMacro_zc_and_crash_iff.1 s' ho' ha').mpr ⟨k, hmacro_none⟩
        have hvo_none : voidOrbit y (2 * m1 + 1) L = none := by
          unfold voidOrbit
          rw [hps']
          exact hzero_none
        exact ⟨2 * m1 + 1 + L,
          ((survivingSeeds_void_crash_forces_weight_step (2 * m1 + 1) L y (by omega) hy_mem).2 hvo_none).1⟩
      · exact ⟨2 * m0 + 1 + 8, hs8⟩
  have hmass_iff : MassDiverges ↔
      (∀ m : Nat, ∀ y ∈ survivingSeeds (2 * m + 1), ∀ s : PhysState,
        physStateOf y (2 * m + 1) = some s → s.age = 0 →
        ∃ k : Nat, iterVoidMacro s k = none) :=
    Iff.trans finite_seeds_terminate_iff_mass_diverges.symm hfin_iff
  have hq01_iff : Ruliology.CellularAutomata.Rule30GateTrap.Q01Gap ↔
      (∀ m : Nat, ∀ y ∈ survivingSeeds (2 * m + 1), ∀ s : PhysState,
        physStateOf y (2 * m + 1) = some s → s.age = 0 →
        ∃ k : Nat, iterVoidMacro s k = none) :=
    Iff.trans massDiverges_iff_Q01Gap.symm hmass_iff
  exact ⟨hfin_iff, hmass_iff, hq01_iff⟩

end FirstActiveBitAndMacroClosure

end Rule30ZeroCoastBridge
end Ruliology.CellularAutomata
