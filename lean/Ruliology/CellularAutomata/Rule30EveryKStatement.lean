module

public import Ruliology.CellularAutomata.Rule30ZeroBoundary
public import Ruliology.CellularAutomata.Rule30UniversalLeftSide

/-!
# Inverse ticks for every k: the statement

The kit numbers physical cells from the white wall, with cell 1 beside it.
In a band, bit 0 is the last black cell, and bit j is j cells towards the wall.
The band and the integer encoding of a physical row therefore read in opposite
directions. This module states the target and its hypothesis; `Rule30EveryKInverse` proves the implication.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30EveryKStatement

open Rule30ZeroBoundary Rule30ZeroBoundary.IntegerForm

abbrev bandStep := Rule30UniversalLeftSide.stepK
abbrev bandAt := Rule30UniversalLeftSide.rowAt

/-- Odd residues are exactly the width-w words with a black outer edge. -/
def OddBand (w v : Nat) : Prop := v < 2 ^ w ∧ v.testBit 0 = true

/-- Closed black run of length 3m+1. Bit j is the unconstrained symbol
read immediately after the shallow zero to finish agreement of the pair. -/
def resetAt (v j m : Nat) : Bool :=
  !(v.testBit (j + 1)) && !(v.testBit (j + 3*m + 3)) &&
    (List.range (3*m + 1)).all (fun i => v.testBit (j + 2 + i))

/-- First complete factor, scanning from the deepest available bit towards
the edge. Its two zeros, black run and following symbol all lie in the band. -/
def firstReset (v available : Nat) : Option Nat :=
  (List.range available).reverse.find? fun j =>
    (List.range (available / 3 + 1)).any fun m =>
      decide (j + 3*m + 4 ≤ available) && resetAt v j m

/-- The reference at layer d is d ticks *earlier* on the same cycle. Agreement
from wheel j outwards leaves j bits (0 through j-1) after the edge retreats.
Width w supplies sufficient fuel since a complete factor strictly spends width. -/
def schedule (w v period : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | fuel + 1, d, available =>
    let phase := (period - d % period) % period
    match firstReset (bandAt w v phase) available with
    | none => 0
    | some j => 1 + schedule w v period fuel (d + 1) j

def phaseCapacity (w v period : Nat) : Nat := schedule w v period w 0 w

/-- Find the first positive return. At positive width there are 2^(w-1)
odd residues, so failure within that many steps excludes exactly transients. -/
def returnPeriod (w v : Nat) : Option Nat :=
  let rec walk : Nat → Nat → Nat → Option Nat
    | 0, _, _ => none
    | fuel + 1, current, elapsed =>
      let next := bandStep w current
      if next = v then some (elapsed + 1) else walk fuel next (elapsed + 1)
  walk (2 ^ (w - 1)) v 0

/-- Worst one-layer schedule across every cycle and every phase. Enumerating
all odd initial words includes each periodic phase separately. Width zero is
excluded from CAP. This finite specification favours clarity over runtime. -/
def K1 : Nat → Nat
  | 0 => 0
  | n + 1 =>
    (List.range (2 ^ n)).foldl (fun worst i =>
      let v := 2*i + 1
      match returnPeriod (n + 1) v with
      | none => worst
      | some period => min worst (phaseCapacity (n + 1) v period)) (n + 1)

def CAP : Prop := ∀ k : Nat, ∃ w : Nat, 0 < w ∧ k ≤ K1 w

/-- The target in the kit's physical-row convention, with arbitrary
predecessor V and equality only on positive cells. -/
def PhysicalEdge (k age : Nat) : Prop :=
  ∀ (L : Nat → Bool) (m t : Nat), 1 ≤ m → L m = true →
    (∀ i, m < i → L i = false) → age ≤ t →
    ∀ V : Nat → Bool, (∀ i, 1 ≤ i → zrow V k i = zrow L t i) →
      V (m + t - k) = true ∧ ∀ i, m + t - k < i → V i = false

/-- Definitionally the kit's `Rule30LateTwins.Top`, spelled out here
on the same bits. -/
def Top (Y m : Nat) : Prop :=
  Y.testBit m = true ∧ ∀ i, m < i → Y.testBit i = false

/-- Every predecessor has a finite representative: a natural number whose row agrees with it. -/
def FinitePredecessor (k age : Nat) : Prop :=
  ∀ (Y t : Nat), Y ≠ 0 → age ≤ t → ∀ L : Nat → Bool,
    (∀ i, 1 ≤ i → zrow L k i = rowOfNat (iter F t Y) i) →
      ∃ A : Nat, (∀ i, 1 ≤ i → rowOfNat A i = L i) ∧
        iter F k A = iter F t Y ∧ Top A (Y.log2 + t - k)

/-- Every wall history occurs. Histories are specified in forward time at cell 1. -/
def AllHistories (k age : Nat) : Prop :=
  ∀ (Y t : Nat), Y ≠ 0 → age ≤ t → ∀ bits : Fin k → Bool,
    ∃ A : Nat, iter F k A = iter F t Y ∧ Top A (Y.log2 + t - k) ∧
      ∀ i : Fin k, rowOfNat (iter F i.val A) 1 = bits i

def TargetAt (k age : Nat) : Prop :=
  PhysicalEdge k age ∧ FinitePredecessor k age ∧ AllHistories k age

def EveryK (age : Nat → Nat) : Prop := ∀ k, TargetAt k (age k)

/-- Read an integer row's outer band in wheel order. Only full bands of
nonzero rows are used in the convergence statement below. -/
def topBand (w Y : Nat) : Nat :=
  (List.range w).foldl (fun word j =>
    if j ≤ Y.log2 ∧ Y.testBit (Y.log2 - j) = true then word + 2^j else word) 0

def Settled (w age : Nat) : Prop :=
  ∀ (Y t : Nat), Y ≠ 0 → age ≤ t →
    let output := iter F t Y
    let v := topBand w output
    w ≤ output.log2 + 1 ∧ OddBand w v ∧ ∃ q : Nat, 0 < q ∧ bandAt w v q = v

/-- The sharper form: any established uniform settling age at a witness
width may be used. First reset starts with free registers at the deep end. -/
def CapacityAtSettlingAge : Prop :=
  ∀ (k w age : Nat), 0 < w → k ≤ K1 w → Settled w age → TargetAt k age

/-- After w-1 ticks every nonzero seed has a full band. A further 2^w
ticks suffice by a finite-state bound. No unique cycle is assumed. -/
def settlingBound (w : Nat) : Nat := w - 1 + 2^w

/-- The least positive witness at or below any supplied witness. The fallback
is the supplied witness itself. CAP provides the endpoint of the finite search. -/
noncomputable def widthFor (capacity : CAP) (k : Nat) : Nat :=
  let witness := Classical.choose (capacity k)
  ((List.range witness).find? (fun w => decide (0 < w ∧ k ≤ K1 w))).getD witness

/-- The conditional every-k statement. Its age depends only on k through the
least capacity witness. CAP remains the open mathematical hypothesis. -/
def ConditionalEveryK : Prop :=
  ∀ capacity : CAP, EveryK (fun k => settlingBound (widthFor capacity k))

/-! ## Zero-allocation `fastFirstReset`, strict cut bound, unconditional `TargetAt 0 0`, and age monotonicity -/

/-- Zero-list-allocation scan for a valid `3*m' + 1` black run starting at `m' ≥ m`,
assuming `v.testBit (j + 1) = false` and `∀ i < 3 * m, v.testBit (j + 2 + i) = true`. -/
def scanResetM (v available j m : Nat) : Nat → Bool
  | 0 => false
  | fuel + 1 =>
    if j + 3 * m + 4 ≤ available then
      if v.testBit (j + 3 * m + 2) then
        if !(v.testBit (j + 3 * m + 3)) then true
        else if v.testBit (j + 3 * m + 4) then scanResetM v available j (m + 1) fuel
        else false
      else false
    else false

def fastHasResetAt (v available j : Nat) : Bool :=
  if j + 4 ≤ available then
    if v.testBit (j + 1) then false
    else scanResetM v available j 0 ((available - j) / 3 + 1)
  else false

def scanResetJ (v available : Nat) : Nat → Option Nat
  | 0 => none
  | rem + 1 =>
    if fastHasResetAt v available rem then some rem
    else scanResetJ v available rem

def fastFirstReset (v available : Nat) : Option Nat :=
  scanResetJ v available available

theorem scanResetM_iff (v available j m fuel : Nat)
    (hfuel : available < j + 3 * (m + fuel) + 4)
    (hb1 : v.testBit (j + 1) = false)
    (hpref : ∀ i : Nat, i < 3 * m → v.testBit (j + 2 + i) = true) :
    scanResetM v available j m fuel = true ↔
      ∃ m' : Nat, m ≤ m' ∧ j + 3 * m' + 4 ≤ available ∧ resetAt v j m' = true := by
  induction fuel generalizing m with
  | zero =>
    simp only [scanResetM, Bool.false_eq_true, false_iff]
    rintro ⟨m', hm', hle, _⟩
    omega
  | succ fuel ih =>
    unfold scanResetM
    by_cases hbound : j + 3 * m + 4 ≤ available
    · rw [ite_eq_left hbound]
      by_cases hb2 : v.testBit (j + 3 * m + 2) = true
      · rw [ite_eq_left hb2]
        by_cases hb3 : (!(v.testBit (j + 3 * m + 3))) = true
        · rw [ite_eq_left hb3]
          simp only [true_iff]
          refine ⟨m, Nat.le_refl m, hbound, ?_⟩
          unfold resetAt
          rw [hb1, hb3]
          simp only [Bool.not_false, Bool.true_and, List.all_eq_true, List.mem_range]
          intro i hi
          by_cases him : i < 3 * m
          · exact hpref i him
          · have hieq : i = 3 * m := by omega
            subst hieq
            simpa [show j + 2 + 3 * m = j + 3 * m + 2 by omega] using hb2
        · rw [ite_eq_right hb3]
          have hb3_true : v.testBit (j + 3 * m + 3) = true := by
            revert hb3; cases v.testBit (j + 3 * m + 3) <;> decide
          have hnot_m : resetAt v j m = false := by
            unfold resetAt; rw [hb3_true]; simp
          by_cases hb4 : v.testBit (j + 3 * m + 4) = true
          · rw [ite_eq_left hb4]
            have hpref' : ∀ i : Nat, i < 3 * (m + 1) → v.testBit (j + 2 + i) = true := by
              intro i hi
              by_cases him : i < 3 * m
              · exact hpref i him
              · have hcases : i = 3 * m ∨ i = 3 * m + 1 ∨ i = 3 * m + 2 := by omega
                rcases hcases with rfl | rfl | rfl
                · simpa [show j + 2 + 3 * m = j + 3 * m + 2 by omega] using hb2
                · simpa [show j + 2 + (3 * m + 1) = j + 3 * m + 3 by omega] using hb3_true
                · simpa [show j + 2 + (3 * m + 2) = j + 3 * m + 4 by omega] using hb4
            rw [ih (m + 1) (by omega) hpref']
            constructor
            · rintro ⟨m', hm', hle, hr⟩
              exact ⟨m', by omega, hle, hr⟩
            · rintro ⟨m', hm', hle, hr⟩
              have hne : m' ≠ m := by rintro rfl; rw [hnot_m] at hr; cases hr
              exact ⟨m', by omega, hle, hr⟩
          · rw [ite_eq_right hb4]
            simp only [Bool.false_eq_true, false_iff]
            rintro ⟨m', hm', _, hr⟩
            by_cases heq : m' = m
            · subst heq; rw [hnot_m] at hr; cases hr
            · have _hgt : m + 1 ≤ m' := by omega
              unfold resetAt at hr
              obtain ⟨_, hall⟩ := Bool.and_eq_true_iff.mp hr
              have hit := List.all_eq_true.mp hall (3 * m + 2) (List.mem_range.mpr (by omega))
              rw [show j + 2 + (3 * m + 2) = j + 3 * m + 4 by omega] at hit
              exact hb4 hit
      · rw [ite_eq_right hb2]
        simp only [Bool.false_eq_true, false_iff]
        rintro ⟨m', hm', _, hr⟩
        unfold resetAt at hr
        obtain ⟨_, hall⟩ := Bool.and_eq_true_iff.mp hr
        have hit := List.all_eq_true.mp hall (3 * m) (List.mem_range.mpr (by omega))
        rw [show j + 2 + 3 * m = j + 3 * m + 2 by omega] at hit
        exact hb2 hit
    · rw [ite_eq_right hbound]
      simp only [Bool.false_eq_true, false_iff]
      rintro ⟨m', hm', hle, _⟩
      omega

theorem fastHasResetAt_eq (v available j : Nat) :
    fastHasResetAt v available j =
      ((List.range (available / 3 + 1)).any fun m =>
        decide (j + 3 * m + 4 ≤ available) && resetAt v j m) := by
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true]
  unfold fastHasResetAt
  by_cases hj4 : j + 4 ≤ available
  · rw [ite_eq_left hj4]
    by_cases hb1 : v.testBit (j + 1) = true
    · rw [ite_eq_left hb1]
      simp only [Bool.false_eq_true, false_iff]
      rintro ⟨m, _, hm⟩
      obtain ⟨_, hr⟩ := Bool.and_eq_true_iff.mp hm
      unfold resetAt at hr; rw [hb1] at hr; simp at hr
    · rw [ite_eq_right hb1]
      have hb1_false : v.testBit (j + 1) = false := by
        revert hb1; cases v.testBit (j + 1) <;> decide
      rw [scanResetM_iff v available j 0 ((available - j) / 3 + 1) (by omega) hb1_false
        (fun i hi => by omega)]
      constructor
      · rintro ⟨m, _, hle, hr⟩
        exact ⟨m, List.mem_range.mpr (by omega), Bool.and_eq_true_iff.mpr ⟨decide_eq_true hle, hr⟩⟩
      · rintro ⟨m, _, hm⟩
        obtain ⟨hle, hr⟩ := Bool.and_eq_true_iff.mp hm
        exact ⟨m, Nat.zero_le m, of_decide_eq_true hle, hr⟩
  · rw [ite_eq_right hj4]
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨m, _, hm⟩
    have hle := of_decide_eq_true (Bool.and_eq_true_iff.mp hm).1
    omega

theorem scanResetJ_eq_find (v available rem : Nat) :
    scanResetJ v available rem =
      (List.range rem).reverse.find? fun j =>
        (List.range (available / 3 + 1)).any fun m =>
          decide (j + 3 * m + 4 ≤ available) && resetAt v j m := by
  induction rem with
  | zero => simp [scanResetJ]
  | succ rem ih =>
    rw [List.range_succ (n := rem), List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.find?_cons]
    unfold scanResetJ
    rw [fastHasResetAt_eq, ih]
    cases ((List.range (available / 3 + 1)).any fun m =>
      decide (rem + 3 * m + 4 ≤ available) && resetAt v rem m) <;> rfl

/-- **Zero-Allocation `fastFirstReset` Equivalence and Strict 4-Bit Width Contraction (`fastFirstReset_eq_and_bound`).** -/
theorem fastFirstReset_eq_and_bound :
    (∀ v available : Nat, fastFirstReset v available = firstReset v available) ∧
    (∀ v available j : Nat, firstReset v available = some j → j + 4 ≤ available) := by
  refine ⟨fun v available => scanResetJ_eq_find v available available, fun v available j h => ?_⟩
  unfold firstReset at h
  have hh := List.find?_some h
  obtain ⟨m, _, hm⟩ := List.any_eq_true.mp hh
  have hle := of_decide_eq_true (Bool.and_eq_true_iff.mp hm).1
  omega

private theorem top_of_nonzero {X : Nat} (hX : X ≠ 0) : Top X X.log2 := by
  refine ⟨Nat.testBit_log2 hX, fun i hi => ?_⟩
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le Nat.lt_log2_self
    (Nat.pow_le_pow_right (by decide) (by omega)))

private theorem F_top_step {X : Nat} (hX : X ≠ 0) :
    F X ≠ 0 ∧ (F X).log2 = X.log2 + 1 := by
  have htop := top_of_nonzero hX
  have hbit : (F X).testBit (X.log2 + 1) = true := by
    rw [testBit_F_succ, htop.2 (X.log2 + 2) (by omega), htop.2 (X.log2 + 1) (by omega), htop.1]
    rfl
  have hhigh : ∀ i, X.log2 + 1 < i → (F X).testBit i = false := by
    intro i hi
    obtain ⟨d, rfl⟩ : ∃ d, i = d + 1 := ⟨i - 1, by omega⟩
    rw [testBit_F_succ, htop.2 (d + 2) (by omega), htop.2 (d + 1) (by omega), htop.2 d (by omega)]
    rfl
  have hne : F X ≠ 0 := by
    intro h0; rw [h0, Nat.zero_testBit] at hbit; cases hbit
  have hlt1 : F X < 2 ^ (X.log2 + 2) := by
    apply Classical.byContradiction
    intro hge
    have hge' : 2 ^ (X.log2 + 2) ≤ F X := Nat.not_lt.mp hge
    have hle_log : X.log2 + 2 ≤ (F X).log2 := (Nat.le_log2 hne).mpr hge'
    have htb := Nat.testBit_log2 hne
    rw [hhigh (F X).log2 (by omega)] at htb
    cases htb
  have hge1 : 2 ^ (X.log2 + 1) ≤ F X := Nat.ge_two_pow_of_testBit hbit
  exact ⟨hne, Nat.le_antisymm (Nat.lt_succ_iff.mp ((Nat.log2_lt hne).mpr hlt1))
    ((Nat.le_log2 hne).mpr hge1)⟩

private theorem iter_step_out (t x : Nat) : iter F (t + 1) x = F (iter F t x) := rfl

private theorem iter_F_top (Y t : Nat) (hY : Y ≠ 0) :
    iter F t Y ≠ 0 ∧ (iter F t Y).log2 = Y.log2 + t := by
  induction t with
  | zero => exact ⟨hY, rfl⟩
  | succ t ih =>
    have hstep := F_top_step ih.1
    rw [iter_step_out]
    exact ⟨hstep.1, by rw [hstep.2, ih.2]; omega⟩

/-- **Unconditional `TargetAt 0 0` and Age Monotonicity of `TargetAt` (`targetAt_zero_and_mono_age`).** -/
theorem targetAt_zero_and_mono_age :
    TargetAt 0 0 ∧
    ∀ (k age₁ age₂ : Nat), age₁ ≤ age₂ → TargetAt k age₁ → TargetAt k age₂ := by
  refine ⟨⟨?_, ?_, ?_⟩, fun k age₁ age₂ hle ⟨hp, hf, ha⟩ => ⟨?_, ?_, ?_⟩⟩
  · intro L m t hm hLm hLfin _ht V hV
    have hedge := zrow_edge hm hLm hLfin t
    refine ⟨?_, fun i hi => ?_⟩
    · have h1 := hV (m + t) (by omega)
      rw [zrow_zero_of_pos V (by omega)] at h1
      simpa [Nat.sub_zero, h1] using hedge.1
    · have h1 := hV i (by omega)
      rw [zrow_zero_of_pos V (by omega)] at h1
      simpa [Nat.sub_zero, h1] using hedge.2 i (by omega)
  · intro Y t hY _ht L hL
    obtain ⟨hne, hlog⟩ := iter_F_top Y t hY
    refine ⟨iter F t Y, fun i hi => ?_, rfl, ?_⟩
    · have h1 := hL i hi
      rw [zrow_zero_of_pos L hi] at h1
      exact h1.symm
    · rw [Nat.sub_zero, ← hlog]
      exact top_of_nonzero hne
  · intro Y t hY _ht bits
    obtain ⟨hne, hlog⟩ := iter_F_top Y t hY
    refine ⟨iter F t Y, rfl, ?_, fun i => Fin.elim0 i⟩
    rw [Nat.sub_zero, ← hlog]
    exact top_of_nonzero hne
  · intro L m t hm hLm hfin ht2 V hV
    exact hp L m t hm hLm hfin (by omega) V hV
  · intro Y t hY ht2 L hL
    exact hf Y t hY (by omega) L hL
  · intro Y t hY ht2 bits
    exact ha Y t hY (by omega) bits

end Ruliology.CellularAutomata.Rule30EveryKStatement
