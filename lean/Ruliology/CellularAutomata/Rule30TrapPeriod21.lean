module

public import Ruliology.CellularAutomata.Rule30Certificates.TrapPeriod21
public import Ruliology.CellularAutomata.Rule30EtherThreeTrap
public import Ruliology.CellularAutomata.Rule30PeriodicHalfline

/-!
# The 001 trap has no full period21 right extension

An actual right-half history entering a correctly aligned `t001` state cannot
have temporal period21 in every column. The proof retains the full Rule30
recurrence, checks every trap state's full head value, and normalizes any entry
label to zero. A kernel-checked closed predecessor cycle supplies the obstruction.
-/

@[expose] public section

/-! A physical bridge for the label-zero 001-trap head pair.
The period21 hypothesis applies to EVERY right column at ALL times. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Ruliology.CellularAutomata.Rule30TrapPeriod21.Physical
open Ruliology.CellularAutomata.Rule30Period21Profiles Ruliology.CellularAutomata.Rule30Certificates.TrapPeriod21
open Ruliology.CellularAutomata Rule30Ether Rule30StripCertificates

def encode (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => encode f n ||| ((f n).toNat <<< n)

theorem testBit_encode (f : Nat → Bool) :
    ∀ n k, (encode f n).testBit k = (decide (k < n) && f k)
  | 0, k => by simp [encode]
  | n + 1, k => by
    rw [encode, Nat.testBit_or, testBit_encode f n k, Nat.testBit_shiftLeft,
      testBit_toNat]
    by_cases hk : k < n
    · simp [hk, show k < n + 1 by omega, show ¬ n ≤ k by omega]
    · by_cases he : k = n
      · subst k; simp
      · simp [hk, show ¬ k < n + 1 by omega, show k - n ≠ 0 by omega]

theorem encode_lt (f : Nat → Bool) (n : Nat) : encode f n < 2 ^ n :=
  Nat.lt_pow_two_of_testBit _ fun k hk => by
    rw [testBit_encode]
    simp [show ¬ k < n by omega]

theorem testBit_rotate (a : Nat) (ha : a < modulus) (k : Nat) (hk : k < 21) :
    (rotate a).testBit k = a.testBit ((k + 1) % 21) := by
  rw [rotate, Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_shiftLeft,
    testBit_toNat]
  by_cases he : k = 20
  · subst k
    have h21 : a.testBit 21 = false := Nat.testBit_lt_two_pow ha
    simp [h21]
  · have hlt : k < 20 := by omega
    simp [show ¬ 20 ≤ k by omega, Nat.mod_eq_of_lt (show k + 1 < 21 by omega),
      Nat.add_comm]

def column (F : Nat → Nat → Bool) (j : Nat) : Nat := encode (fun t => F t j) 21

theorem column_lt (F : Nat → Nat → Bool) (j : Nat) : column F j < modulus :=
  encode_lt _ _

theorem column_bit (F : Nat → Nat → Bool) (j k : Nat) (hk : k < 21) :
    (column F j).testBit k = F k j := by
  rw [column, testBit_encode]
  simp [hk]

theorem column_step (F : Nat → Nat → Bool) (hF : IsR30 F)
    (hper : ∀ t j, F (t + 21) j = F t j) (j : Nat) :
    step (column F (j + 1), column F (j + 2)) = (column F j, column F (j + 1)) := by
  apply Prod.ext
  · apply Nat.eq_of_testBit_eq
    intro k
    change ((rotate (column F (j + 1)) ^^^
      (column F (j + 1) ||| column F (j + 2))) % 2 ^ 21).testBit k =
      (column F j).testBit k
    rw [Nat.testBit_mod_two_pow]
    by_cases hk : k < 21
    · rw [decide_eq_true hk, Bool.true_and, Nat.testBit_xor, Nat.testBit_or,
        testBit_rotate _ (column_lt _ _) _ hk,
        column_bit _ _ _ (Nat.mod_lt _ (by decide)),
        column_bit _ _ _ hk, column_bit _ _ _ hk, column_bit _ _ _ hk]
      have ht : F ((k + 1) % 21) (j + 1) = F (k + 1) (j + 1) := by
        by_cases he : k = 20
        · subst k
          simpa using (hper 0 (j + 1)).symm
        · rw [Nat.mod_eq_of_lt (by omega)]
      rw [ht, hF k j]
      change xor (xor (F k j) (F k (j + 1) || F k (j + 2)))
        (F k (j + 1) || F k (j + 2)) = F k j
      cases F k j <;> cases (F k (j + 1) || F k (j + 2)) <;> rfl
    · rw [decide_eq_false hk, Bool.false_and, column, testBit_encode]
      simp [hk]
  · rfl

theorem column_eq_literal (F : Nat → Nat → Bool) (j a : Nat)
    (ha : a < modulus) (h : ∀ k, k < 21 → F k j = a.testBit k) : column F j = a := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 21
  · rw [column_bit _ _ _ hk, h k hk]
  · have hb : a.testBit k = false := by
      rw [← Nat.mod_eq_of_lt ha]
      change (a % 2 ^ 21).testBit k = false
      rw [Nat.testBit_mod_two_pow]
      simp [hk]
    rw [column, testBit_encode, hb]
    simp [hk]

/-- No full actual right-half history has common period21 and the specified label-zero
trap head pair. No finite-support premise or unrestricted exterior input is substituted. -/
theorem no_period21_history (F : Nat → Nat → Bool) (hF : IsR30 F)
    (hper : ∀ t j, F (t + 21) j = F t j)
    (h0 : ∀ k, k < 21 → F k 0 = (1198372 : Nat).testBit k)
    (h1 : ∀ k, k < 21 → F k 1 = (1591590 : Nat).testBit k) : False := by
  let s : Nat → State := fun j => (column F j, column F (j + 1))
  apply no_bounded_inverse s
  · apply Prod.ext
    · exact column_eq_literal F 0 1198372 (by decide) h0
    · exact column_eq_literal F 1 1591590 (by decide) h1
  · intro j
    exact ⟨column_lt _ _, column_lt _ _⟩
  · intro j
    simpa only [s, Nat.add_assoc] using column_step F hF hper j

end Ruliology.CellularAutomata.Rule30TrapPeriod21.Physical


/-! The named t001 bridge: full head projection, including black driver phases,
and normalization of any correctly entered label to zero. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Ruliology.CellularAutomata.Rule30TrapPeriod21
open Ruliology.CellularAutomata Rule30Ether Rule30EtherThree

theorem full_head_check : allBelowT (fun i =>
    (t001.st i).testBit 0 == (1591590 : Nat).testBit (t001.lab i)) t001.n = true := by
  decide +kernel

theorem full_head {i : Nat} (hi : i < t001.n) :
    (t001.st i).testBit 0 = (1591590 : Nat).testBit (t001.lab i) := by
  have := allBelowT_spec full_head_check i hi
  simpa only [beq_iff_eq] using this

theorem driver_check : allBelowT (fun k =>
    wordAt3 w001 k == (1198372 : Nat).testBit k) 21 = true := by
  decide +kernel

theorem driver_bits (k : Nat) (hk : k < 21) :
    wordAt3 w001 k = (1198372 : Nat).testBit k := by
  have := allBelowT_spec driver_check k hk
  simpa only [beq_iff_eq] using this

/-- Any actual right-half history that enters a correctly aligned t001 state cannot
have common temporal period21 on the whole right half. This includes every entry label;
it does not assert absorption or rule out an aperiodic exterior. -/
theorem no_period21_trapped (F : Nat → Nat → Bool) (hF : IsR30 F)
    (hper : ∀ t j, F (t + 21) j = F t j)
    (T : Nat) (hc : ∀ t, T ≤ t → F t 0 = wordAt3 t001.w (t - T))
    (t1 i : Nat) (ht1 : T ≤ t1) (hi : i < t001.n)
    (hph : (t1 - T) % 3 = t001.lab i % 3)
    (hr : EncF F t001.b t1 0 (t001.st i)) : False := by
  have inv := PTrap.invariant t001 t001_check hF T hc t1 i ht1 hi hph hr
  have hl : t001.lab i < 21 := (PTrap.step t001 t001_check hi false).2.2.2.1
  let q := 21 - t001.lab i
  let b := t1 + q
  have hq : t001.lab i + q = 21 := by dsimp [q]; omega
  let H : Nat → Nat → Bool := fun t p => F (b + t) p
  have hH : IsR30 H := by
    intro t p
    dsimp [H]
    simpa only [Nat.add_assoc] using hF (b + t) p
  have hHp : ∀ t j, H (t + 21) j = H t j := by
    intro t j
    dsimp [H]
    simpa only [Nat.add_assoc] using hper (b + t) j
  apply Ruliology.CellularAutomata.Rule30TrapPeriod21.Physical.no_period21_history H hH hHp
  · intro k hk
    change F (b + k) 0 = _
    rw [hc (b + k) (by dsimp [b]; omega)]
    have hmod : (b + k - T) % 3 = k % 3 := by dsimp [b]; omega
    change wordAt3 w001 (b + k - T) = _
    rw [show wordAt3 w001 (b + k - T) = wordAt3 w001 k by
      unfold wordAt3
      rw [hmod]]
    exact driver_bits k hk
  · intro k hk
    change F (b + k) 1 = _
    obtain ⟨j, hj, hrow, hlabel⟩ := inv (q + k)
    have hlabel' : t001.lab j = k := by
      change t001.lab j = (t001.lab i + (q + k)) % 21 at hlabel
      rw [show t001.lab i + (q + k) = 21 + k by omega,
        Nat.add_mod_left, Nat.mod_eq_of_lt hk] at hlabel
      exact hlabel
    calc F (b + k) 1 = (t001.st j).testBit 0 := by
           simpa only [b, Nat.add_assoc] using (encF_head hrow (by decide)).symm
         _ = (1591590 : Nat).testBit (t001.lab j) := full_head hj
         _ = (1591590 : Nat).testBit k := by rw [hlabel']

end Ruliology.CellularAutomata.Rule30TrapPeriod21


/-! Column-dependent onsets and arbitrary positive common periods. -/
namespace Ruliology.CellularAutomata.Rule30TrapPeriod21

open Ruliology.CellularAutomata Rule30Ether Rule30EtherThree
open Rule30PeriodicHalfline

/-- Different, unbounded spatial onsets do not evade the period21 trap obstruction. -/
theorem no_eventual_period21_trapped (F : Nat → Nat → Bool) (hF : IsR30 F)
    (hper : ∀ j, ∃ S, ∀ t, S ≤ t → F (t+21) j = F t j)
    (T : Nat) (hc : ∀ t, T ≤ t → F t 0 = wordAt3 t001.w (t-T))
    (t1 i : Nat) (ht1 : T ≤ t1) (hi : i < t001.n)
    (hph : (t1-T) % 3 = t001.lab i % 3)
    (hr : EncF F t001.b t1 0 (t001.st i)) : False := by
  classical
  let onset : Nat → Nat := fun j => Classical.choose (hper j)
  have ho : ∀ j t, onset j ≤ t → F (t+21) j = F t j :=
    fun j => Classical.choose_spec (hper j)
  let G := representative F 21 onset
  have hG : IsR30 G := representative_isR30 F hF 21 (by decide) onset ho
  have hGp : ∀ t j, G (t+21) j = G t j :=
    representative_periodic F 21 (by decide) onset ho
  have h0 : ∀ t, T ≤ t → F (t+21) 0 = F t 0 := by
    intro t ht
    rw [hc (t+21) (by omega), hc t ht]
    unfold wordAt3
    congr 1
    omega
  have hcG : ∀ t, T ≤ t → G t 0 = wordAt3 t001.w (t-T) := by
    intro t ht
    exact (representative_agrees_from F 21 onset 0 T h0 t ht).trans (hc t ht)
  obtain ⟨S,hS⟩ := representative_finite_agreement F 21 onset ho t001.b
  obtain ⟨j,hj,hrow,hlab⟩ :=
    PTrap.invariant t001 t001_check hF T hc t1 i ht1 hi hph hr S
  have hrowG : EncF G t001.b (t1+S) 0 (t001.st j) := by
    refine ⟨hrow.1, ?_⟩
    intro k hk
    change (t001.st j).testBit k = representative F 21 onset (t1+S) (0+1+k)
    rw [hS (0+1+k) (by omega) (t1+S) (by omega)]
    exact hrow.2 k hk
  have hphase : (t1+S-T) % 3 = t001.lab j % 3 := by
    rw [hlab, show t1+S-T = (t1-T)+S by omega]
    exact PTrap.phase_lab t001 t001_check _ _ hph S
  exact Rule30TrapPeriod21.no_period21_trapped G hG hGp T hcG (t1+S) j
    (by omega) hj hphase hrowG

theorem trapped_head_period21 (F : Nat → Nat → Bool) (hF : IsR30 F)
    (T : Nat) (hc : ∀ t, T≤t → F t 0=wordAt3 t001.w (t-T))
    (t1 i : Nat) (ht1 : T≤t1) (hi : i<t001.n)
    (hph : (t1-T)%3=t001.lab i%3) (hr : EncF F t001.b t1 0 (t001.st i)) :
    ∀ t, t1≤t → F (t+21) 1=F t 1 := by
  have inv := PTrap.invariant t001 t001_check hF T hc t1 i ht1 hi hph hr
  intro t ht
  obtain ⟨j,hj,hjrow,hjlab⟩ := inv (t-t1)
  obtain ⟨k,hk,hkrow,hklab⟩ := inv (t+21-t1)
  have ej : F t 1=(1591590:Nat).testBit (t001.lab j) := by
    calc F t 1 = (t001.st j).testBit 0 := by
           simpa only [show t1+(t-t1)=t by omega] using (encF_head hjrow (by decide)).symm
         _ = _ := Rule30TrapPeriod21.full_head hj
  have ek : F (t+21) 1=(1591590:Nat).testBit (t001.lab k) := by
    calc F (t+21) 1 = (t001.st k).testBit 0 := by
           simpa only [show t1+(t+21-t1)=t+21 by omega] using (encF_head hkrow (by decide)).symm
         _ = _ := Rule30TrapPeriod21.full_head hk
  rw [ej,ek,hjlab,hklab]
  congr 1
  change (t001.lab i+(t+21-t1))%21=(t001.lab i+(t-t1))%21
  omega

/-- No positive common eventual period exists on every column of a trapped history. -/
theorem no_common_eventual_period_trapped (F : Nat → Nat → Bool) (hF : IsR30 F)
    (p : Nat) (hp : 0<p) (hper : ∀ j, ∃ S, ∀ t, S≤t → F (t+p) j=F t j)
    (T : Nat) (hc : ∀ t, T≤t → F t 0=wordAt3 t001.w (t-T))
    (t1 i : Nat) (ht1 : T≤t1) (hi : i<t001.n)
    (hph : (t1-T)%3=t001.lab i%3) (hr : EncF F t001.b t1 0 (t001.st i)) : False := by
  have h0 : ∃ S, ∀ t, S≤t → F (t+21) 0=F t 0 := by
    refine ⟨T, ?_⟩
    intro t ht
    rw [hc (t+21) (by omega),hc t ht]
    unfold wordAt3
    congr 1
    omega
  have h1 : ∃ S, ∀ t, S≤t → F (t+21) 1=F t 1 :=
    ⟨t1,trapped_head_period21 F hF T hc t1 i ht1 hi hph hr⟩
  exact Rule30TrapPeriod21.no_eventual_period21_trapped F hF
    (eventual_common_period_head_rigidity F hF p hp hper 21 h0 h1)
    T hc t1 i ht1 hi hph hr


/-! Spatially distinct adjacent pairs differ arbitrarily late, with no exterior clock. -/
open Ruliology.CellularAutomata Rule30Ether Rule30EtherThree
open Rule30Period21Profiles Rule30PeriodicHalfline
open Rule30TrapPeriod21.Physical

def decode21 (a : State) : Pair :=
  (fun t => a.1.testBit (t % 21), fun t => a.2.testBit (t % 21))

def Bounded (a : State) : Prop := a.1 < modulus ∧ a.2 < modulus

theorem step_bounded (a : State) (h : Bounded a) : Bounded (step a) :=
  ⟨Nat.mod_lt _ (by decide), h.1⟩

theorem decode21_step (a : State) (ha : Bounded a) :
    predecessor (decode21 a) = decode21 (step a) := by
  apply Prod.ext
  · funext t
    change xor (a.1.testBit ((t+1)%21))
      (a.1.testBit (t%21) || a.2.testBit (t%21)) =
      ((rotate a.1 ^^^ (a.1 ||| a.2)) % 2^21).testBit (t%21)
    rw [Nat.testBit_mod_two_pow, decide_eq_true (Nat.mod_lt t (by decide)),
      Bool.true_and, Nat.testBit_xor, Nat.testBit_or,
      testBit_rotate a.1 ha.1 (t%21) (Nat.mod_lt t (by decide))]
    congr 2
    omega
  · rfl

theorem decode21_injective (a b : State) (ha : Bounded a) (hb : Bounded b)
    (he : decode21 a = decode21 b) : a = b := by
  have bit_eq (u v : Nat) (hu : u < modulus) (hv : v < modulus)
      (h : ∀ t, u.testBit (t%21) = v.testBit (t%21)) : u=v := by
    apply Nat.eq_of_testBit_eq
    intro k
    by_cases hk : k<21
    · simpa only [Nat.mod_eq_of_lt hk] using h k
    · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hu
          (Nat.pow_le_pow_right (by decide) (show 21≤k by omega))),
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv
          (Nat.pow_le_pow_right (by decide) (show 21≤k by omega)))]
  apply Prod.ext
  · exact bit_eq a.1 b.1 ha.1 hb.1 (fun t => congrArg (fun p : Pair => p.1 t) he)
  · exact bit_eq a.2 b.2 ha.2 hb.2 (fun t => congrArg (fun p : Pair => p.2 t) he)

theorem decode21_advance (n : Nat) (a : State) (ha : Bounded a) :
    advance predecessor n (decode21 a) = decode21 (advance step n a) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [advance, decode21_step a ha, ih (step a) (step_bounded a ha)]
    rfl

theorem decoded_head_no_return (n : Nat) (hn : 0<n) :
    advance predecessor n (decode21 (1198372,1591590)) ≠
      decode21 (1198372,1591590) := by
  intro h
  have hb : Bounded (1198372,1591590) := by
    constructor <;> decide
  have hi := advance_preserves step Bounded step_bounded n (1198372,1591590) hb
  rw [decode21_advance n _ hb] at h
  exact Rule30Certificates.TrapPeriod21.head_no_return n hn
    (decode21_injective _ _ hi hb h)

def actualPair (F : Nat → Nat → Bool) (j : Nat) : Pair :=
  (fun t => F t j, fun t => F t (j+1))

theorem actualPair_predecessor (F : Nat → Nat → Bool) (hF : IsR30 F) (j : Nat) :
    predecessor (actualPair F (j+1)) = actualPair F j := by
  apply Prod.ext
  · funext t
    change xor (F (t+1) (j+1)) (F t (j+1) || F t (j+2)) = F t j
    rw [hF t j]
    unfold Rule30Jen.rule
    cases F t j <;> cases (F t (j+1) || F t (j+2)) <;> rfl
  · rfl

/-- Only the two prescribed head traces are periodic; no exterior clock is assumed. -/
theorem normalized_pairs_ne (F : Nat → Nat → Bool) (hF : IsR30 F)
    (h0 : ∀ t, F t 0 = (1198372:Nat).testBit (t%21))
    (h1 : ∀ t, F t 1 = (1591590:Nat).testBit (t%21))
    (i j : Nat) (hij : i<j) : actualPair F i ≠ actualPair F j := by
  intro he
  obtain ⟨n,hn,hr⟩ := inverse_collision predecessor (actualPair F)
    (actualPair_predecessor F hF) hij he
  have hh : actualPair F 0 = decode21 (1198372,1591590) := by
    apply Prod.ext
    · funext t; exact h0 t
    · funext t; exact h1 t
  rw [hh] at hr
  exact decoded_head_no_return n hn hr

/-- Any aligned t001 entry supplies arbitrarily late normalized head phases. -/
theorem trapped_normalized_after (F : Nat → Nat → Bool) (hF : IsR30 F)
    (T : Nat) (hc : ∀ t, T≤t → F t 0=wordAt3 t001.w (t-T))
    (t1 i : Nat) (ht1 : T≤t1) (hi : i<t001.n)
    (hph : (t1-T)%3=t001.lab i%3) (hr : EncF F t001.b t1 0 (t001.st i))
    (B : Nat) : ∃ b, B≤b ∧
      (∀ t, F (b+t) 0=(1198372:Nat).testBit (t%21)) ∧
      (∀ t, F (b+t) 1=(1591590:Nat).testBit (t%21)) := by
  have inv := PTrap.invariant t001 t001_check hF T hc t1 i ht1 hi hph hr
  have hl : t001.lab i<21 := (PTrap.step t001 t001_check hi false).2.2.2.1
  let q := 21-t001.lab i
  let b := t1+q+21*B
  have hq : t001.lab i+q=21 := by dsimp [q]; omega
  refine ⟨b, by dsimp [b]; omega, ?_, ?_⟩
  · intro t
    rw [hc (b+t) (by dsimp [b]; omega)]
    change wordAt3 w001 (b+t-T) = _
    rw [show wordAt3 w001 (b+t-T)=wordAt3 w001 (t%21) by
      unfold wordAt3
      congr 1
      dsimp [b]
      omega]
    exact Rule30TrapPeriod21.driver_bits (t%21) (Nat.mod_lt t (by decide))
  · intro t
    obtain ⟨j,hj,hrow,hlabel⟩ := inv (q+21*B+t)
    have hlabel' : t001.lab j=t%21 := by
      change t001.lab j=(t001.lab i+(q+21*B+t))%21 at hlabel
      omega
    calc F (b+t) 1 = (t001.st j).testBit 0 := by
           simpa only [b, Nat.add_assoc] using (encF_head hrow (by decide)).symm
         _ = (1591590:Nat).testBit (t001.lab j) := Rule30TrapPeriod21.full_head hj
         _ = (1591590:Nat).testBit (t%21) := by rw [hlabel']

/-- Distinct spatial pairs disagree arbitrarily late; no temporal period is assumed. -/
theorem trapped_pairs_differ_arbitrarily_late (F : Nat → Nat → Bool) (hF : IsR30 F)
    (T : Nat) (hc : ∀ t, T≤t → F t 0=wordAt3 t001.w (t-T))
    (t1 i : Nat) (ht1 : T≤t1) (hi : i<t001.n)
    (hph : (t1-T)%3=t001.lab i%3) (hr : EncF F t001.b t1 0 (t001.st i))
    (j k : Nat) (hjk : j<k) (B : Nat) :
    ∃ t, B≤t ∧ (F t j,F t (j+1)) ≠ (F t k,F t (k+1)) := by
  classical
  apply Classical.byContradiction
  intro hn
  have he : ∀ t, B≤t → (F t j,F t (j+1)) = (F t k,F t (k+1)) := by
    intro t ht
    apply Classical.byContradiction
    intro hne
    exact hn ⟨t,ht,hne⟩
  obtain ⟨b,hb,h0,h1⟩ := trapped_normalized_after F hF T hc t1 i ht1 hi hph hr B
  let H : Nat → Nat → Bool := fun t p => F (b+t) p
  have hH : IsR30 H := by
    intro t p
    dsimp [H]
    simpa only [Nat.add_assoc] using hF (b+t) p
  apply normalized_pairs_ne H hH h0 h1 j k hjk
  apply Prod.ext
  · funext t
    exact congrArg Prod.fst (he (b+t) (by omega))
  · funext t
    exact congrArg Prod.snd (he (b+t) (by omega))

end Ruliology.CellularAutomata.Rule30TrapPeriod21
