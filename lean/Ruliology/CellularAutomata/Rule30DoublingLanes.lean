module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes
public import Ruliology.CellularAutomata.Rule30RelaxedWindows
public import Ruliology.CellularAutomata.Rule30EveryKLine

/-!
# Bit-sliced doubling-lane checker and unconditional closure for `e ≤ 4`

For any `FirstLoss d a e` and `NextWhite d a b` on a recurrent strip with `PrefixClocks`, every
wheel in `[a, b]` inherits temporal period `L = 2 ^ (e + 1)` (`period_between_whites`), and
time-shifting by `2 ^ e` flips bit `2 ^ e - 1` of `d (a + 1)` while preserving `[a, b]` catches.
Running `2 ^ n` anti-periodic half-words in parallel via `Nat`/`List`/`Bool` recursors closes all
`65,814` anti-periodic drivers for `0 ≤ e ≤ 4` (`L ≤ 32`) unconditionally (`catch_of_firstLoss_le_four`),
reducing `DLMinusOne` iff-style (`dlMinusOne_iff_from_five`) and both wall and whole-line `EveryK`
to `e ≥ 5` (`L ≥ 64`).
-/

@[expose] public section

set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

namespace Ruliology.CellularAutomata.Rule30DoublingLanes

open Ruliology.CellularAutomata
open Rule30AgedLeftDiagonals Rule30EveryKStatement
open Ruliology.CellularAutomata.Rule30RecurrentStrip (Clock Reset)
open Ruliology.CellularAutomata.Rule30RootedWhiteReturns (Column)
open Ruliology.CellularAutomata.Rule30ResetCompactness (LInfinity cap_of_unbounded_resets)
open Ruliology.CellularAutomata.Rule30RelaxedWindows
open Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes
  (band pat yFree pat_spec pats_getD pack testBit_pack pack_lt getD_tail headD_eq)

/-! ## 1. Bit-sliced kernel engine -/

noncomputable def endCarry : List Nat → List Nat → Nat → Nat := fun p2 =>
  List.rec (motive := fun _ => List Nat → Nat → Nat)
    (fun _ acc => acc)
    (fun a _ ih p1 acc =>
      ih (List.tail p1) (Nat.xor a (Nat.lor (List.headD p1 0) acc)))
    p2

noncomputable def emitCol : List Nat → List Nat → Nat → List Nat := fun p2 =>
  List.rec (motive := fun _ => List Nat → Nat → List Nat)
    (fun _ _ => [])
    (fun a _ ih p1 acc =>
      acc :: ih (List.tail p1) (Nat.xor a (Nat.lor (List.headD p1 0) acc)))
    p2

noncomputable def orAll : List Nat → Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ ih => Nat.lor x ih)

noncomputable def andAll (all1 : Nat) : List Nat → Nat :=
  List.rec (motive := fun _ => Nat) all1 (fun x _ ih => Nat.land x ih)

noncomputable def maskList (m : Nat) : List Nat → List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun x _ ih => Nat.land m x :: ih)

noncomputable def stepDFA (all1 active : Nat) :
    List Nat → List Nat → List Nat → List Nat → List Nat → List Nat →
      List Nat × List Nat × List Nat × List Nat × List Nat := fun p1 =>
  List.rec
    (motive := fun _ => List Nat → List Nat → List Nat → List Nat → List Nat →
      List Nat × List Nat × List Nat × List Nat × List Nat)
    (fun _ _ _ _ _ => ([], [], [], [], []))
    (fun z _ ih z0 m1 m2 m0 caught =>
      let z0h := List.headD z0 0
      let m1h := List.headD m1 0
      let m2h := List.headD m2 0
      let m0h := List.headD m0 0
      let ch  := List.headD caught 0
      let nz  := Nat.xor all1 z
      let ch' := Nat.lor ch (Nat.land active (Nat.land m1h nz))
      let m1' := Nat.land (Nat.lor z0h m0h) z
      let m2' := Nat.land m1h z
      let m0' := Nat.land m2h z
      let r := ih (List.tail z0) (List.tail m1) (List.tail m2) (List.tail m0) (List.tail caught)
      (nz :: r.1, m1' :: r.2.1, m2' :: r.2.2.1, m0' :: r.2.2.2.1, ch' :: r.2.2.2.2))
    p1

noncomputable def runLanes (all1 : Nat) (fuel : Nat) :
    Nat → List Nat → List Nat → List Nat → List Nat → List Nat → List Nat → List Nat → Bool :=
  Nat.rec
    (motive := fun _ => Nat → List Nat → List Nat → List Nat → List Nat → List Nat → List Nat → List Nat → Bool)
    (fun active _ _ _ _ _ _ caught =>
      band (Nat.beq active 0) (Nat.beq (andAll all1 caught) all1))
    (fun _ ih active p2 p1 z0 m1 m2 m0 caught =>
      let dfa := stepDFA all1 active p1 z0 m1 m2 m0 caught
      let allCaught := andAll all1 dfa.2.2.2.2
      let still := Nat.land active (Nat.land (orAll p1) (Nat.xor all1 allCaught))
      Bool.rec
        (let p2s := maskList still p2
         let p1s := maskList still p1
         let z_start := endCarry p2s p1s 0
         let nxt := emitCol p2s p1s z_start
         band (Nat.beq (endCarry p2s p1s z_start) z_start)
           (ih still p1 nxt dfa.1 dfa.2.1 dfa.2.2.1 dfa.2.2.2.1 dfa.2.2.2.2))
        (Nat.beq allCaught all1)
        (Nat.beq still 0))
    fuel

noncomputable def initCol (e n c all1 : Nat) : List Nat :=
  let P := Nat.pow 2 e
  let m := Nat.sub P 1
  let pats := (List.range n).map (pat n)
  let lo := ((List.range m).map (yFree n c all1 pats)) ++ [0]
  lo ++ lo.map (Nat.xor all1)

noncomputable def check (e fuel n c : Nat) : Bool :=
  let P := Nat.pow 2 e
  let L := Nat.mul 2 P
  let all1 := Nat.sub (Nat.pow 2 (Nat.pow 2 n)) 1
  runLanes all1 fuel all1 (List.replicate L 0) (initCol e n c all1)
    (List.replicate L all1) (List.replicate L 0) (List.replicate L 0)
    (List.replicate L 0) (List.replicate L 0)

/-! ## 2. Equational & bitwise projection lemmas -/

theorem band_eq_true (a b : Bool) : band a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem endCarry_nil (p1 : List Nat) (acc : Nat) : endCarry [] p1 acc = acc := rfl
theorem endCarry_cons (a : Nat) (as p1 : List Nat) (acc : Nat) :
    endCarry (a :: as) p1 acc = endCarry as p1.tail (a ^^^ (p1.headD 0 ||| acc)) := rfl

theorem emitCol_nil (p1 : List Nat) (acc : Nat) : emitCol [] p1 acc = [] := rfl
theorem emitCol_cons (a : Nat) (as p1 : List Nat) (acc : Nat) :
    emitCol (a :: as) p1 acc = acc :: emitCol as p1.tail (a ^^^ (p1.headD 0 ||| acc)) := rfl

theorem emitCol_length : ∀ (p2 p1 : List Nat) (acc : Nat), (emitCol p2 p1 acc).length = p2.length
  | [], _, _ => rfl
  | a :: as, p1, acc => by simp [emitCol_cons, emitCol_length as p1.tail _]

theorem emitCol_head {p2 p1 : List Nat} (acc : Nat) (h : 0 < p2.length) :
    (emitCol p2 p1 acc).getD 0 0 = acc := by
  cases p2 with
  | nil => simp at h
  | cons a as => rfl

theorem emitCol_step : ∀ (p2 p1 : List Nat) (acc p t : Nat), t + 1 < p2.length →
    ((emitCol p2 p1 acc).getD (t + 1) 0).testBit p =
      xor ((p2.getD t 0).testBit p)
        (((p1.getD t 0).testBit p) || ((emitCol p2 p1 acc).getD t 0).testBit p)
  | [], _, _, _, _, ht => by simp at ht
  | a :: as, p1, acc, p, 0, ht => by
    cases as with
    | nil => simp at ht
    | cons a2 as2 =>
      simp only [emitCol_cons, List.getD_cons_zero, List.getD_cons_succ, headD_eq,
        Nat.testBit_xor, Nat.testBit_or]
  | a :: as, p1, acc, p, t + 1, ht => by
    simp only [emitCol_cons, List.getD_cons_succ]
    rw [emitCol_step as p1.tail _ p t (by simp at ht; omega), getD_tail]

theorem emitCol_last : ∀ (p2 p1 : List Nat) (acc p : Nat), 0 < p2.length →
    (endCarry p2 p1 acc).testBit p =
      xor ((p2.getD (p2.length - 1) 0).testBit p)
        (((p1.getD (p2.length - 1) 0).testBit p) ||
          ((emitCol p2 p1 acc).getD (p2.length - 1) 0).testBit p)
  | [], _, _, _, h => by simp at h
  | [a], p1, acc, p, _ => by
    change (endCarry [a] p1 acc).testBit p =
      xor (a.testBit p) (((p1.getD 0 0).testBit p) || ((emitCol [a] p1 acc).getD 0 0).testBit p)
    rw [endCarry_cons, endCarry_nil, emitCol_cons, List.getD_cons_zero, headD_eq,
        Nat.testBit_xor, Nat.testBit_or]
  | a :: b :: as, p1, acc, p, _ => by
    have ih := emitCol_last (b :: as) p1.tail (a ^^^ (p1.headD 0 ||| acc)) p (by simp)
    simpa [endCarry_cons, emitCol_cons, getD_tail] using ih

theorem orAll_testBit_true : ∀ (xs : List Nat) (p : Nat),
    (orAll xs).testBit p = true ↔ ∃ t, t < xs.length ∧ (xs.getD t 0).testBit p = true
  | [], p => by simp [orAll]
  | x :: xs, p => by
    show (x ||| orAll xs).testBit p = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, orAll_testBit_true xs p]
    constructor
    · rintro (hx | ⟨t, ht, hxt⟩)
      · exact ⟨0, by simp, hx⟩
      · exact ⟨t + 1, by simp; omega, hxt⟩
    · rintro ⟨t, ht, hxt⟩
      cases t with
      | zero => exact Or.inl hxt
      | succ t => exact Or.inr ⟨t, by simp at ht; omega, hxt⟩

theorem andAll_testBit_false (all1 : Nat) : ∀ (xs : List Nat) (p s0 : Nat),
    s0 < xs.length → (xs.getD s0 0).testBit p = false → (andAll all1 xs).testBit p = false
  | [], _, _, hs, _ => by simp at hs
  | x :: xs, p, 0, _, hf => by
    change x.testBit p = false at hf
    show (x &&& andAll all1 xs).testBit p = false
    rw [Nat.testBit_and, hf, Bool.false_and]
  | x :: xs, p, s0 + 1, hs, hf => by
    show (x &&& andAll all1 xs).testBit p = false
    rw [Nat.testBit_and, andAll_testBit_false all1 xs p s0 (by simp at hs; omega) hf, Bool.and_false]

theorem maskList_length (m : Nat) : ∀ xs : List Nat, (maskList m xs).length = xs.length
  | [] => rfl
  | x :: xs => by
    show ((m &&& x) :: maskList m xs).length = (x :: xs).length
    simp [maskList_length m xs]

theorem maskList_getD (m : Nat) : ∀ (xs : List Nat) (t p : Nat),
    ((maskList m xs).getD t 0).testBit p = (m.testBit p && (xs.getD t 0).testBit p)
  | [], t, p => by simp [maskList]
  | x :: xs, 0, p => by show (m &&& x).testBit p = _; rw [Nat.testBit_and]; rfl
  | x :: xs, t + 1, p => by show ((maskList m xs).getD t 0).testBit p = _; exact maskList_getD m xs t p

theorem stepDFA_nil (all1 active : Nat) (z0 m1 m2 m0 caught : List Nat) :
    stepDFA all1 active [] z0 m1 m2 m0 caught = ([], [], [], [], []) := rfl

theorem stepDFA_cons (all1 active z : Nat) (zs z0 m1 m2 m0 caught : List Nat) :
    stepDFA all1 active (z :: zs) z0 m1 m2 m0 caught =
      let r := stepDFA all1 active zs z0.tail m1.tail m2.tail m0.tail caught.tail
      ((all1 ^^^ z) :: r.1,
       ((z0.headD 0 ||| m0.headD 0) &&& z) :: r.2.1,
       (m1.headD 0 &&& z) :: r.2.2.1,
       (m2.headD 0 &&& z) :: r.2.2.2.1,
       (caught.headD 0 ||| (active &&& (m1.headD 0 &&& (all1 ^^^ z)))) :: r.2.2.2.2) := rfl

theorem stepDFA_spec (all1 active : Nat) :
    ∀ (p1 z0 m1 m2 m0 caught : List Nat),
      let r := stepDFA all1 active p1 z0 m1 m2 m0 caught
      r.1.length = p1.length ∧ r.2.1.length = p1.length ∧ r.2.2.1.length = p1.length ∧
      r.2.2.2.1.length = p1.length ∧ r.2.2.2.2.length = p1.length ∧
      ∀ t p, t < p1.length →
        (r.1.getD t 0).testBit p = xor (all1.testBit p) ((p1.getD t 0).testBit p) ∧
        (r.2.1.getD t 0).testBit p =
          (((z0.getD t 0).testBit p || (m0.getD t 0).testBit p) && (p1.getD t 0).testBit p) ∧
        (r.2.2.1.getD t 0).testBit p = ((m1.getD t 0).testBit p && (p1.getD t 0).testBit p) ∧
        (r.2.2.2.1.getD t 0).testBit p = ((m2.getD t 0).testBit p && (p1.getD t 0).testBit p) ∧
        (r.2.2.2.2.getD t 0).testBit p =
          ((caught.getD t 0).testBit p ||
            (active.testBit p && ((m1.getD t 0).testBit p &&
              xor (all1.testBit p) ((p1.getD t 0).testBit p))))
  | [], _, _, _, _, _ => by simp [stepDFA_nil]
  | z :: zs, z0, m1, m2, m0, caught => by
    obtain ⟨hl1, hl2, hl3, hl4, hl5, hbit⟩ :=
      stepDFA_spec all1 active zs z0.tail m1.tail m2.tail m0.tail caught.tail
    rw [stepDFA_cons]
    refine ⟨by simp [hl1], by simp [hl2], by simp [hl3], by simp [hl4], by simp [hl5], fun t p ht => ?_⟩
    cases t with
    | zero =>
      simp only [List.getD_cons_zero, headD_eq, Nat.testBit_xor, Nat.testBit_or, Nat.testBit_and,
        and_self]
    | succ t =>
      have ih := hbit t p (by simp at ht; omega)
      simpa only [List.getD_cons_succ, getD_tail] using ih

/-! ## 3. Period propagation across `[a, b]` and half-period shift symmetry -/

theorem period_mul_add (f : Column) {p : Nat} (hp : PeriodFrom f 0 p) :
    ∀ k t, f (t + k * p) = f t
  | 0, t => by simp
  | k + 1, t => by
    rw [show t + (k + 1) * p = (t + k * p) + p by rw [Nat.succ_mul]; omega,
        hp _ (Nat.zero_le _), period_mul_add f hp k t]

theorem period_next_of_nonwhite {d : Nat → Column} (hd : Recurrence d) (clocks : PrefixClocks d)
    {i L : Nat} (hp0 : PeriodFrom (d i) 0 L) (hp1 : PeriodFrom (d (i + 1)) 0 L)
    (hnw : ¬ White d (i + 1)) : PeriodFrom (d (i + 2)) 0 L := by
  have ⟨t0, ht0⟩ : ∃ t0, d (i + 1) t0 = true := by
    refine Classical.byContradiction fun h => hnw fun t => ?_
    cases hb : d (i + 1) t
    · rfl
    · exact absurd ⟨t, hb⟩ h
  have htail : ∀ u, d (i + 2) (t0 + 1 + u + L) = d (i + 2) (t0 + 1 + u) := by
    intro u
    induction u with
    | zero =>
      simp only [Nat.add_zero]
      rw [show t0 + 1 + L = (t0 + L) + 1 by omega, hd.2.2 i (t0 + L), hd.2.2 i t0,
          hp0 t0 (Nat.zero_le _), hp1 t0 (Nat.zero_le _), ht0]
      simp
    | succ u ih =>
      rw [show t0 + 1 + (u + 1) + L = (t0 + 1 + u + L) + 1 by omega,
          show t0 + 1 + (u + 1) = (t0 + 1 + u) + 1 by omega,
          hd.2.2 i (t0 + 1 + u + L), hd.2.2 i (t0 + 1 + u),
          hp0 (t0 + 1 + u) (Nat.zero_le _), hp1 (t0 + 1 + u) (Nat.zero_le _), ih]
  obtain ⟨q, hq, hcq⟩ := clocks (i + 2)
  have hp2q : PeriodFrom (d (i + 2)) 0 q := hcq (i + 2) (Nat.le_refl _)
  intro t _
  have hge : t0 + 1 ≤ t + (t0 + 1) * q := by
    have : 1 * (t0 + 1) ≤ q * (t0 + 1) := Nat.mul_le_mul_right (t0 + 1) hq
    rw [Nat.one_mul, Nat.mul_comm] at this; omega
  have h1 := period_mul_add (d (i + 2)) hp2q (t0 + 1) t
  have h2 := period_mul_add (d (i + 2)) hp2q (t0 + 1) (t + L)
  have h3 := htail (t + (t0 + 1) * q - (t0 + 1))
  rw [show t0 + 1 + (t + (t0 + 1) * q - (t0 + 1)) = t + (t0 + 1) * q by omega] at h3
  rw [show t + L + (t0 + 1) * q = t + (t0 + 1) * q + L by omega] at h2
  exact h2.symm.trans (h3.trans h1)

/-- Every wheel in a white-to-white interval `[a, b]` inherits any temporal period of `d (a + 1)`. -/
theorem period_between_whites {d : Nat → Column} (hd : Recurrence d) (clocks : PrefixClocks d)
    {a b L : Nat} (hwa : White d a) (hp1 : PeriodFrom (d (a + 1)) 0 L) (hab : NextWhite d a b) :
    ∀ i, a ≤ i → i ≤ b → PeriodFrom (d i) 0 L := by
  suffices h : ∀ k, a + k ≤ b → PeriodFrom (d (a + k)) 0 L by
    intro i hai hib
    simpa [show a + (i - a) = i by omega] using h (i - a) (by omega)
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hk
    rcases k with _ | _ | k
    · intro t _; simp [hwa t, hwa (t + L)]
    · exact hp1
    · by_cases heq : a + (k + 2) = b
      · rw [heq]; intro t _; simp [hab.2.1 t, hab.2.1 (t + L)]
      · exact period_next_of_nonwhite hd clocks
          (ih k (by omega) (by omega)) (ih (k + 1) (by omega) (by omega))
          (hab.2.2 (a + k + 1) (by omega) (by omega))

/-! ## 4. Soundness of `runLanes` and `check` -/

theorem runLanes_zero (all1 active : Nat) (p2 p1 z0 m1 m2 m0 caught : List Nat) :
    runLanes all1 0 active p2 p1 z0 m1 m2 m0 caught =
      band (Nat.beq active 0) (Nat.beq (andAll all1 caught) all1) := rfl

theorem runLanes_succ (all1 fuel active : Nat) (p2 p1 z0 m1 m2 m0 caught : List Nat) :
    runLanes all1 (fuel + 1) active p2 p1 z0 m1 m2 m0 caught =
      let dfa := stepDFA all1 active p1 z0 m1 m2 m0 caught
      let allCaught := andAll all1 dfa.2.2.2.2
      let still := active &&& (orAll p1 &&& (all1 ^^^ allCaught))
      Bool.rec
        (let p2s := maskList still p2
         let p1s := maskList still p1
         let z_start := endCarry p2s p1s 0
         let nxt := emitCol p2s p1s z_start
         band (Nat.beq (endCarry p2s p1s z_start) z_start)
           (runLanes all1 fuel still p1 nxt dfa.1 dfa.2.1 dfa.2.2.1 dfa.2.2.2.1 dfa.2.2.2.2))
        (Nat.beq allCaught all1)
        (Nat.beq still 0) := rfl

/-- Once lane `p` is inactive (`active.testBit p = false`) with tick `s0` still uncaught,
`runLanes` can never succeed. -/
theorem runLanes_dead_false (all1 p s0 L : Nat) (hALL : all1.testBit p = true) (hs0 : s0 < L) :
    ∀ fuel active p2 p1 z0 m1 m2 m0 caught,
      p2.length = L → p1.length = L → caught.length = L →
      active.testBit p = false → (caught.getD s0 0).testBit p = false →
      runLanes all1 fuel active p2 p1 z0 m1 m2 m0 caught = true → False := by
  intro fuel
  induction fuel with
  | zero =>
    intro active p2 p1 z0 m1 m2 m0 caught _ _ hcl _ hcf hrun
    rw [runLanes_zero, band_eq_true, Nat.beq_eq, Nat.beq_eq] at hrun
    have hf := andAll_testBit_false all1 caught p s0 (by omega) hcf
    rw [hrun.2, hALL] at hf; exact absurd hf (by decide)
  | succ fuel ih =>
    intro active p2 p1 z0 m1 m2 m0 caught hp2 hp1 hcl hact hcf hrun
    rw [runLanes_succ] at hrun
    dsimp only at hrun
    have hd := stepDFA_spec all1 active p1 z0 m1 m2 m0 caught
    have hcf' : ((stepDFA all1 active p1 z0 m1 m2 m0 caught).2.2.2.2.getD s0 0).testBit p = false := by
      rw [(hd.2.2.2.2.2 s0 p (by omega)).2.2.2.2, hcf, hact]; rfl
    have hac_false : (andAll all1 (stepDFA all1 active p1 z0 m1 m2 m0 caught).2.2.2.2).testBit p = false :=
      andAll_testBit_false all1 _ p s0 (by omega) hcf'
    let still := active &&& (orAll p1 &&& (all1 ^^^ andAll all1 (stepDFA all1 active p1 z0 m1 m2 m0 caught).2.2.2.2))
    cases hst : Nat.beq still 0
    · rw [hst] at hrun
      dsimp only at hrun
      rw [band_eq_true] at hrun
      have hst_p : still.testBit p = false := by simp [still, Nat.testBit_and, hact]
      refine ih still p1 _ _ _ _ _ _ hp1 ?_ (by omega) hst_p hcf' hrun.2
      rw [emitCol_length, maskList_length]; exact hp2
    · rw [hst] at hrun
      dsimp only at hrun
      rw [Nat.beq_eq] at hrun
      rw [hrun, hALL] at hac_false; exact absurd hac_false (by decide)

/-- Trailing black run length of `f` on `a + 1 .. a + k` anchored at `f a = false`. -/
def trailingOnes (f : Nat → Bool) (a : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => if f (a + k + 1) then trailingOnes f a k + 1 else 0

theorem trailingOnes_spec (f : Nat → Bool) (a : Nat) (ha : f a = false) :
    ∀ k, let r := trailingOnes f a k
      r ≤ k ∧ f (a + k - r) = false ∧ ∀ u, u < r → f (a + k - r + 1 + u) = true
  | 0 => ⟨Nat.le_refl 0, ha, fun _ hu => absurd hu (Nat.not_lt_zero _)⟩
  | k + 1 => by
    obtain ⟨hr, hf0, hones⟩ := trailingOnes_spec f a ha k
    dsimp only [trailingOnes]
    cases hfk : f (a + k + 1)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨Nat.zero_le _, by simpa [Nat.add_assoc] using hfk, fun _ hu => absurd hu (Nat.not_lt_zero _)⟩
    · simp only [↓reduceIte]
      refine ⟨by omega, by rw [show a + (k + 1) - (trailingOnes f a k + 1) = a + k - trailingOnes f a k by omega]; exact hf0, ?_⟩
      intro u hu
      by_cases hul : u < trailingOnes f a k
      · rw [show a + (k + 1) - (trailingOnes f a k + 1) + 1 + u = a + k - trailingOnes f a k + 1 + u by omega]
        exact hones u hul
      · have : u = trailingOnes f a k := by omega
        subst this
        rw [show a + (k + 1) - (trailingOnes f a k + 1) + 1 + trailingOnes f a k = a + k + 1 by omega]
        exact hfk

/-- Uniqueness of the `L`-periodic next column when `col1` has at least one `true` bit. -/
theorem emitCol_eq_next {d : Nat → Column} (hd : Recurrence d) (clocks : PrefixClocks d)
    {i L p acc : Nat} {p2 p1 : List Nat} (hL : 0 < L)
    (hp2_len : p2.length = L) (hp1_len : p1.length = L)
    (hp0 : PeriodFrom (d i) 0 L) (hp1 : PeriodFrom (d (i + 1)) 0 L)
    (hcol2 : ∀ t, t < L → (p2.getD t 0).testBit p = d i t)
    (hcol1 : ∀ t, t < L → (p1.getD t 0).testBit p = d (i + 1) t)
    (ht0_ex : ∃ t0, t0 < L ∧ d (i + 1) t0 = true)
    (hcert : (endCarry p2 p1 acc).testBit p = acc.testBit p) :
    PeriodFrom (d (i + 2)) 0 L ∧
      ∀ t, t < L → ((emitCol p2 p1 acc).getD t 0).testBit p = d (i + 2) t := by
  obtain ⟨t0, ht0L, ht0⟩ := ht0_ex
  have hnw : ¬ White d (i + 1) := fun hw => absurd ( (hw t0).symm.trans ht0 ) (by decide)
  have hp2_per := period_next_of_nonwhite hd clocks hp0 hp1 hnw
  refine ⟨hp2_per, ?_⟩
  let Z : Nat → Bool := fun u => ((emitCol p2 p1 acc).getD (u % L) 0).testBit p
  have hZ_step : ∀ u, Z (u + 1) = xor (d i u) (d (i + 1) u || Z u) := by
    intro u
    let r := u % L
    have hrL : r < L := Nat.mod_lt u hL
    have hu_eq : u = r + L * (u / L) := (Nat.mod_add_div u L).symm
    have hdi : d i u = d i r := by
      rw [hu_eq, Nat.mul_comm]; exact period_mul_add (d i) hp0 (u / L) r
    have hdi1 : d (i + 1) u = d (i + 1) r := by
      rw [hu_eq, Nat.mul_comm]; exact period_mul_add (d (i + 1)) hp1 (u / L) r
    rw [hdi, hdi1, ← hcol2 r hrL, ← hcol1 r hrL]
    by_cases hr1 : r + 1 < L
    · have hmod1 : (u + 1) % L = r + 1 := by
        rw [hu_eq, show r + L * (u / L) + 1 = (r + 1) + L * (u / L) by omega,
            Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr1]
      dsimp only [Z]; rw [hmod1]
      exact emitCol_step p2 p1 acc p r (by omega)
    · have hreq : r = L - 1 := by omega
      have hmod0 : (u + 1) % L = 0 := by
        rw [hu_eq, show r + L * (u / L) + 1 = L * (u / L + 1) by rw [Nat.mul_succ]; omega,
            Nat.mul_mod_right]
      dsimp only [Z]; change ((emitCol p2 p1 acc).getD ((u + 1) % L) 0).testBit p = xor ((p2.getD r 0).testBit p) (((p1.getD r 0).testBit p) || ((emitCol p2 p1 acc).getD r 0).testBit p)
      rw [hmod0, emitCol_head acc (by omega), ← hcert, hreq]
      simpa [hp2_len] using emitCol_last p2 p1 acc p (by omega)
  have hZ_tail : ∀ u, Z (t0 + 1 + u) = d (i + 2) (t0 + 1 + u) := by
    intro u
    induction u with
    | zero => simp only [Nat.add_zero]; rw [hZ_step t0, hd.2.2 i t0, ht0]; simp
    | succ u ih =>
      rw [show t0 + 1 + (u + 1) = (t0 + 1 + u) + 1 by omega,
          hZ_step (t0 + 1 + u), hd.2.2 i (t0 + 1 + u), ih]
  intro t htL
  have h1 : Z (t + L) = Z t := by dsimp only [Z]; rw [Nat.add_mod_right]
  have h2 : d (i + 2) (t + L) = d (i + 2) t := hp2_per t (Nat.zero_le _)
  have h3 := hZ_tail (t + L - (t0 + 1))
  rw [show t0 + 1 + (t + L - (t0 + 1)) = t + L by omega, h1, h2] at h3
  simpa [Z, Nat.mod_eq_of_lt htL] using h3

/-- **One-lane soundness of `runLanes`:** if `¬ Catch d a b s0`, lane `p` forces `False`. -/
theorem runLanes_sound {d : Nat → Column} (hd : Recurrence d) (clocks : PrefixClocks d)
    {a b L all1 p s0 : Nat} (hL : 0 < L) (hALL : all1.testBit p = true) (hs0 : s0 < L)
    (hwa : White d a) (hab : NextWhite d a b) (hnc : ¬ Catch d a b s0) :
    ∀ fuel k active p2 p1 z0 m1 m2 m0 caught,
      a + k + 1 ≤ b →
      p2.length = L → p1.length = L → z0.length = L → m1.length = L →
      m2.length = L → m0.length = L → caught.length = L →
      PeriodFrom (d (a + k)) 0 L → PeriodFrom (d (a + k + 1)) 0 L →
      (∀ t, t < L → (p2.getD t 0).testBit p = d (a + k) t) →
      (∀ t, t < L → (p1.getD t 0).testBit p = d (a + k + 1) t) →
      active.testBit p = true →
      (let r := trailingOnes (fun i => d i s0) a k
       (z0.getD s0 0).testBit p = decide (r = 0) ∧
       (m1.getD s0 0).testBit p = decide (r % 3 = 1) ∧
       (m2.getD s0 0).testBit p = decide (r % 3 = 2) ∧
       (m0.getD s0 0).testBit p = decide (0 < r ∧ r % 3 = 0)) →
      (caught.getD s0 0).testBit p = false →
      runLanes all1 fuel active p2 p1 z0 m1 m2 m0 caught = true → False := by
  intro fuel
  induction fuel with
  | zero =>
    intro k active p2 p1 z0 m1 m2 m0 caught _ _ _ _ _ _ _ _ _ _ _ _ hact _ _ hrun
    rw [runLanes_zero, band_eq_true, Nat.beq_eq] at hrun
    rw [hrun.1, Nat.zero_testBit] at hact; exact absurd hact (by decide)
  | succ fuel ih =>
    intro k active p2 p1 z0 m1 m2 m0 caught hkb hp2 hp1 hz0 hm1 hm2 hm0 hcl
      hper0 hper1 hcol2 hcol1 hact ⟨hz0b, hm1b, hm2b, hm0b⟩ hcf hrun
    rw [runLanes_succ] at hrun
    dsimp only at hrun
    have hd_spec := stepDFA_spec all1 active p1 z0 m1 m2 m0 caught
    obtain ⟨hl1, hl2, hl3, hl4, hl5, hbits⟩ := hd_spec
    obtain ⟨hb_nz, hb_m1, hb_m2, hb_m0, hb_ch⟩ := hbits s0 p (by omega)
    let rk := trailingOnes (fun i => d i s0) a k
    have hp1_s0 : (p1.getD s0 0).testBit p = d (a + k + 1) s0 := hcol1 s0 hs0
    -- Show `caught` at `s0` in lane `p` stays `false` because `m1 && !z` would give `Catch d a b s0`
    have hcf' : ((stepDFA all1 active p1 z0 m1 m2 m0 caught).2.2.2.2.getD s0 0).testBit p = false := by
      rw [hb_ch, hcf, hact, hm1b, hALL, hp1_s0, Bool.false_or, Bool.true_and]
      cases hbit : d (a + k + 1) s0
      · simp only [Bool.xor_false]
        by_cases hmod : rk % 3 = 1
        · obtain ⟨hrk_le, hleft, hmid⟩ := trailingOnes_spec (fun i => d i s0) a (hwa s0) k
          exfalso; apply hnc
          refine ⟨a + k - rk, rk, by omega, by omega, hmod, hleft, hmid, ?_⟩
          simpa [show a + k - rk + 1 + rk = a + k + 1 by omega] using hbit
        · rw [Bool.and_true]; exact decide_eq_false hmod
      · simp
    have hac_false : (andAll all1 (stepDFA all1 active p1 z0 m1 m2 m0 caught).2.2.2.2).testBit p = false :=
      andAll_testBit_false all1 _ p s0 (by omega) hcf'
    let dfa := stepDFA all1 active p1 z0 m1 m2 m0 caught
    let still := active &&& (orAll p1 &&& (all1 ^^^ andAll all1 dfa.2.2.2.2))
    cases hst0 : Nat.beq still 0
    · rw [hst0] at hrun
      dsimp only at hrun
      rw [band_eq_true, Nat.beq_eq] at hrun
      have hst_eq : still.testBit p = (orAll p1).testBit p := by
        simp [still, dfa, Nat.testBit_and, Nat.testBit_xor, hact, hALL, hac_false]
      cases hor : (orAll p1).testBit p
      · have hst_p : still.testBit p = false := hst_eq.trans hor
        exact runLanes_dead_false all1 p s0 L hALL hs0 fuel still p1 _ _ _ _ _ _
          hp1 (by rw [emitCol_length, maskList_length]; exact hp2) (by omega) hst_p hcf' hrun.2
      · have hst_p : still.testBit p = true := hst_eq.trans hor
        have ht0_ex : ∃ t0, t0 < L ∧ d (a + k + 1) t0 = true := by
          obtain ⟨t0, ht0_lt, ht0_b⟩ := (orAll_testBit_true p1 p).mp hor
          exact ⟨t0, by omega, (hcol1 t0 (by omega)).symm.trans ht0_b⟩
        have hnw1 : ¬ White d (a + k + 1) := by
          obtain ⟨t0, _, ht0_b⟩ := ht0_ex
          intro hw; exact absurd ((hw t0).symm.trans ht0_b) (by decide)
        have hkb' : a + (k + 1) + 1 ≤ b := by
          by_cases heq : a + k + 1 = b
          · exfalso; apply hnw1; rw [heq]; exact hab.2.1
          · omega
        let p2s := maskList still p2
        let p1s := maskList still p1
        let z_start := endCarry p2s p1s 0
        have hp2s_col : ∀ t, t < L → (p2s.getD t 0).testBit p = d (a + k) t := by
          intro t ht; rw [maskList_getD, hst_p, Bool.true_and]; exact hcol2 t ht
        have hp1s_col : ∀ t, t < L → (p1s.getD t 0).testBit p = d (a + k + 1) t := by
          intro t ht; rw [maskList_getD, hst_p, Bool.true_and]; exact hcol1 t ht
        have hcert_p : (endCarry p2s p1s z_start).testBit p = z_start.testBit p := by
          rw [hrun.1]
        obtain ⟨hper2, hnxt_col⟩ := emitCol_eq_next hd clocks hL
          (by rw [maskList_length]; exact hp2) (by rw [maskList_length]; exact hp1)
          hper0 hper1 hp2s_col hp1s_col ht0_ex hcert_p
        refine ih (k + 1) still p1 (emitCol p2s p1s z_start) dfa.1 dfa.2.1 dfa.2.2.1 dfa.2.2.2.1 dfa.2.2.2.2
          hkb' hp1 (by rw [emitCol_length, maskList_length]; exact hp2)
          (hl1.trans hp1) (hl2.trans hp1) (hl3.trans hp1) (hl4.trans hp1) (hl5.trans hp1)
          hper1 hper2 hcol1
          (fun t ht => by simpa [show a + k + 2 = a + (k + 1) + 1 by omega] using hnxt_col t ht)
          hst_p ?_ hcf' hrun.2
        dsimp only
        have htr1 : trailingOnes (fun i => d i s0) a (k + 1) =
            if d (a + k + 1) s0 then rk + 1 else 0 := rfl
        rw [htr1, hb_nz, hb_m1, hb_m2, hb_m0, hALL, hp1_s0, hz0b, hm1b, hm2b, hm0b]
        by_cases hbit : d (a + k + 1) s0 = true
        · rw [hbit]
          simp only [↓reduceIte, Bool.xor_true, Bool.not_true, Bool.and_true]
          refine ⟨rfl, ?_, ?_, ?_⟩
          · change (decide (rk = 0) || decide (0 < rk ∧ rk % 3 = 0)) = decide ((rk + 1) % 3 = 1)
            rw [← Bool.decide_or]
            exact decide_eq_decide.mpr ⟨by omega, by omega⟩
          · change decide (rk % 3 = 1) = decide ((rk + 1) % 3 = 2)
            exact decide_eq_decide.mpr ⟨by omega, by omega⟩
          · change decide (rk % 3 = 2) = decide (0 < rk + 1 ∧ (rk + 1) % 3 = 0)
            exact decide_eq_decide.mpr ⟨by omega, by omega⟩
        · rw [Bool.not_eq_true] at hbit; rw [hbit]; simp
    · rw [hst0] at hrun
      dsimp only at hrun
      rw [Nat.beq_eq] at hrun
      rw [hrun, hALL] at hac_false; exact absurd hac_false (by decide)

theorem initCol_spec (e n c all1 p : Nat) (_hn : n ≤ 2 ^ e - 1) (hp : p < 2 ^ n)
    (hALL : all1.testBit p = true) {f : Column}
    (hflip : ∀ t, f (t + 2 ^ e) = !(f t)) (htop : f (2 ^ e - 1) = false)
    (hp_eq : p = pack f n) (hc_eq : c = pack (fun s => f (n + s)) (2 ^ e - 1 - n)) :
    (initCol e n c all1).length = 2 * 2 ^ e ∧
      ∀ t, t < 2 * 2 ^ e → ((initCol e n c all1).getD t 0).testBit p = f t := by
  let P := 2 ^ e
  have hP : 1 ≤ P := Nat.two_pow_pos e
  let m := P - 1
  let pats := (List.range n).map (pat n)
  let lo := ((List.range m).map (yFree n c all1 pats)) ++ [0]
  have hlo_len : lo.length = P := by simp [lo, m]; omega
  have hlo_bit : ∀ t, t < P → (lo.getD t 0).testBit p = f t := by
    intro t ht
    rw [List.getD_eq_getElem?_getD]
    by_cases htm : t < m
    · rw [List.getElem?_append_left (by simp [htm]), List.getElem?_map, List.getElem?_range htm]
      dsimp only [Option.map, Option.getD, yFree]
      by_cases htn : t < n
      · rw [ite_eq_left htn, pats_getD n t htn, pat_spec n t p htn hp, hp_eq, testBit_pack]
        simp [htn]
      · rw [ite_eq_right htn, hc_eq, testBit_pack]
        have hsub : t - n < 2 ^ e - 1 - n := by dsimp only [m, P] at htm; omega
        have hf_eq : f (n + (t - n)) = f t := by rw [show n + (t - n) = t by omega]
        rw [decide_eq_true hsub, Bool.true_and, hf_eq]
        cases f t
        · simp
        · simpa using hALL
    · have hteq : t = P - 1 := by omega
      subst hteq
      rw [List.getElem?_append_right (by simp [m])]
      simpa [m] using htop
  refine ⟨by simp [initCol]; omega, fun t ht => ?_⟩
  change ((lo ++ lo.map (Nat.xor all1)).getD t 0).testBit p = f t
  rw [List.getD_eq_getElem?_getD]
  by_cases htP : t < P
  · rw [List.getElem?_append_left (by rw [hlo_len]; exact htP)]
    rw [← List.getD_eq_getElem?_getD]
    exact hlo_bit t htP
  · rw [List.getElem?_append_right (by rw [hlo_len]; omega), List.getElem?_map]
    have hsub : t - P < P := by omega
    have hget : lo[t - P]? = some (lo.getD (t - P) 0) := by
      rw [List.getD_eq_getElem?_getD]
      cases hq : lo[t - P]? with
      | none => exfalso; have := List.getElem?_eq_none_iff.mp hq; omega
      | some v => rfl
    rw [hlo_len, hget]
    dsimp only [Option.map, Option.getD]
    show (all1 ^^^ lo.getD (t - P) 0).testBit p = f t
    rw [Nat.testBit_xor, hALL, hlo_bit (t - P) hsub]
    have hf2 := hflip (t - P)
    rw [show t - P + 2 ^ e = t by omega] at hf2
    rw [hf2]; cases f (t - P) <;> rfl

/-- Time-shifting a strip by `S` preserves `Recurrence`, `PrefixClocks`, `FirstLoss`, and `NextWhite`. -/
def shiftStrip (d : Nat → Column) (S : Nat) : Nat → Column := fun i t => d i (t + S)

theorem shiftStrip_props {d : Nat → Column} (hd : Recurrence d) (clocks : PrefixClocks d)
    {a e b : Nat} (loss : FirstLoss d a e) (hab : NextWhite d a b) (S : Nat) :
    Recurrence (shiftStrip d S) ∧ PrefixClocks (shiftStrip d S) ∧
    FirstLoss (shiftStrip d S) a e ∧ NextWhite (shiftStrip d S) a b := by
  refine ⟨⟨fun t => ?_, fun t => ?_, fun i t => ?_⟩, fun m => ?_,
          { clock := ?_, least := ?_, white := fun t => loss.white (t + S), flip := fun t => ?_ },
          ⟨hab.1, fun t => hab.2.1 (t + S), fun i hai hib hwi => hab.2.2 i hai hib fun t => ?_⟩⟩
  · show d 0 (t + 1 + S) = d 0 (t + S)
    rw [show t + 1 + S = (t + S) + 1 by omega]; exact hd.1 (t + S)
  · show d 1 (t + 1 + S) = (d 0 (t + S) || d 1 (t + S))
    rw [show t + 1 + S = (t + S) + 1 by omega]; exact hd.2.1 (t + S)
  · show d (i + 2) (t + 1 + S) = _
    rw [show t + 1 + S = (t + S) + 1 by omega]; exact hd.2.2 i (t + S)
  · obtain ⟨q, hq, hcq⟩ := clocks m
    exact ⟨q, hq, fun i hi t _ => by
      show d i (t + q + S) = d i (t + S)
      rw [show t + q + S = (t + S) + q by omega]; exact hcq i hi (t + S) (Nat.zero_le _)⟩
  · intro i hi t _
    show d i (t + 2 ^ e + S) = d i (t + S)
    rw [show t + 2 ^ e + S = (t + S) + 2 ^ e by omega]
    exact loss.clock i hi (t + S) (Nat.zero_le _)
  · intro q hq hcq; apply loss.least q hq; intro i hi t _
    obtain ⟨r, hr, hcr⟩ := clocks i
    have hper_r : PeriodFrom (d i) 0 r := hcr i (Nat.le_refl _)
    have hge : S ≤ t + S * r := by
      have : S * 1 ≤ S * r := Nat.mul_le_mul_left S hr; omega
    have h1 := period_mul_add (d i) hper_r S t
    have h2 := period_mul_add (d i) hper_r S (t + q)
    have h3 := hcq i hi (t + S * r - S) (Nat.zero_le _)
    dsimp only [shiftStrip] at h3
    rw [show t + S * r - S + q + S = t + q + S * r by omega,
        show t + S * r - S + S = t + S * r by omega] at h3
    exact h2.symm.trans (h3.trans h1)
  · show d (a + 1) (t + 2 ^ e + S) = !(d (a + 1) (t + S))
    rw [show t + 2 ^ e + S = (t + S) + 2 ^ e by omega]; exact loss.flip (t + S)
  · obtain ⟨r, hr, hcr⟩ := clocks i
    have hper_r : PeriodFrom (d i) 0 r := hcr i (Nat.le_refl _)
    have hge : S ≤ t + S * r := by
      have : S * 1 ≤ S * r := Nat.mul_le_mul_left S hr; omega
    rw [← period_mul_add (d i) hper_r S t]
    simpa [shiftStrip, show t + S * r - S + S = t + S * r by omega] using hwi (t + S * r - S)

/-- **Soundness of chunked doubling-lane verification (`catch_of_checks`):** if every chunk `< 2^(2^e-1-n)`
passes, every `FirstLoss d a e` and `NextWhite d a b` catches all ticks `s`. -/
theorem catch_of_checks (e fuel n : Nat) (hn : n ≤ 2 ^ e - 1)
    (hc : ∀ c, c < 2 ^ (2 ^ e - 1 - n) → check e fuel n c = true)
    {d : Nat → Column} (hd : Recurrence d) (clocks : PrefixClocks d)
    {a b : Nat} (loss : FirstLoss d a e) (hab : NextWhite d a b) (s : Nat) :
    Catch d a b s := by
  let P := 2 ^ e
  let L := 2 * P
  have hL : 0 < L := by dsimp only [L, P]; have := Nat.two_pow_pos e; omega
  have hp1_orig : PeriodFrom (d (a + 1)) 0 L := fun t _ => by
    show d (a + 1) (t + 2 * 2 ^ e) = d (a + 1) t
    rw [show t + 2 * 2 ^ e = (t + 2 ^ e) + 2 ^ e by omega, loss.flip, loss.flip, Bool.not_not]
  have hper_ab := period_between_whites hd clocks loss.white hp1_orig hab
  -- Reduce to `s % L` and shift by `0` or `2 ^ e` so `d' (a + 1) (2 ^ e - 1) = false`
  let S := if d (a + 1) (P - 1) then P else 0
  let d' := shiftStrip d S
  obtain ⟨hd', clocks', loss', hab'⟩ := shiftStrip_props hd clocks loss hab S
  have htop : d' (a + 1) (P - 1) = false := by
    dsimp only [d', shiftStrip, S]
    cases hb : d (a + 1) (P - 1)
    · simp [hb]
    · simp only [↓reduceIte]; rw [loss.flip, hb]; rfl
  -- Suffices to show `Catch d' a b s'` where `s' = (s + S) % L` (since `S + S = 0` or `2P = L`!)
  let t_back := if d (a + 1) (P - 1) then (s + P) % L else s % L
  suffices hcatch' : Catch d' a b t_back by
    obtain ⟨j, len, hj, hjlen, hmod, h0, hmid, h1⟩ := hcatch'
    have heq_col : ∀ i, a ≤ i → i ≤ b → d' i t_back = d i s := by
      intro i hai hib
      have hpi := hper_ab i hai hib
      dsimp only [d', shiftStrip, S, t_back]
      cases hb : d (a + 1) (P - 1)
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        have hs : s = s % L + (s / L) * L := by rw [Nat.mul_comm]; exact (Nat.mod_add_div s L).symm
        conv => rhs; rw [hs]
        exact (period_mul_add (d i) hpi (s / L) (s % L)).symm
      · simp only [↓reduceIte]
        have hsP : (s + P) % L + P = (s + P) % L + ((s + P) / L) * L + P - ((s + P) / L) * L := by omega
        have h1' := period_mul_add (d i) hpi ((s + P) / L) ((s + P) % L + P)
        rw [show (s + P) % L + P + (s + P) / L * L = ((s + P) % L + L * ((s + P) / L)) + P by
              rw [Nat.mul_comm]; omega,
            Nat.mod_add_div (s + P) L, show s + P + P = s + L by dsimp only [L]; omega,
            hpi s (Nat.zero_le _)] at h1'
        exact h1'.symm
    refine ⟨j, len, hj, hjlen, hmod, (heq_col j hj (by omega)).symm.trans h0,
      fun u hu => (heq_col _ (by omega) (by omega)).symm.trans (hmid u hu),
      (heq_col _ (by omega) hjlen).symm.trans h1⟩
  refine Classical.byContradiction fun hnc => ?_
  let lane := pack (d' (a + 1)) n
  let chunk := pack (fun u => d' (a + 1) (n + u)) (2 ^ e - 1 - n)
  have hlane : lane < 2 ^ n := pack_lt _ _
  have hchunk : chunk < 2 ^ (2 ^ e - 1 - n) := pack_lt _ _
  let all1 := 2 ^ 2 ^ n - 1
  have hALL : all1.testBit lane = true := by rw [Nat.testBit_two_pow_sub_one]; simpa using hlane
  obtain ⟨hlen_init, hbit_init⟩ :=
    initCol_spec e n chunk all1 lane hn hlane hALL loss'.flip htop rfl rfl
  have hp1' : PeriodFrom (d' (a + 1)) 0 L := fun t _ => by
    have hf1 := loss'.flip (t + 2 ^ e); have hf2 := loss'.flip t
    dsimp only [d', L, P] at *; rw [show t + 2 * 2 ^ e = t + 2 ^ e + 2 ^ e by omega, hf1, hf2, Bool.not_not]
  have hs0_lt : t_back < L := by
    dsimp only [t_back]; split <;> exact Nat.mod_lt _ hL
  have hrep0 : ∀ t, t < L → ((List.replicate L 0).getD t 0).testBit lane = false := by
    intro t ht; rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, ite_eq_left ht]; exact Nat.zero_testBit lane
  have hrep1 : ∀ t, t < L → ((List.replicate L all1).getD t 0).testBit lane = true := by
    intro t ht; rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, ite_eq_left ht]; exact hALL
  exact runLanes_sound hd' clocks' hL hALL hs0_lt loss'.white hab' hnc fuel 0 all1
    (List.replicate L 0) (initCol e n chunk all1)
    (List.replicate L all1) (List.replicate L 0) (List.replicate L 0)
    (List.replicate L 0) (List.replicate L 0)
    (by have := hab'.1; omega) (by simp) hlen_init (by simp) (by simp) (by simp) (by simp) (by simp)
    (fun t _ => (loss'.white (t + L)).trans (loss'.white t).symm) hp1'
    (fun t ht => (hrep0 t ht).trans (loss'.white t).symm)
    hbit_init hALL
    ⟨hrep1 t_back hs0_lt, hrep0 t_back hs0_lt, hrep0 t_back hs0_lt, hrep0 t_back hs0_lt⟩
    (hrep0 t_back hs0_lt) (hc chunk hchunk)

def ChunksOK (e fuel n lo cnt : Nat) : Prop :=
  ∀ c, lo ≤ c → c < lo + cnt → check e fuel n c = true

theorem chunksOK_one {e fuel n c : Nat} (h : check e fuel n c = true) : ChunksOK e fuel n c 1 :=
  fun c' h1 h2 => by rw [show c' = c by omega]; exact h

theorem chunksOK_append {e fuel n lo a b : Nat} (h1 : ChunksOK e fuel n lo a)
    (h2 : ChunksOK e fuel n (lo + a) b) : ChunksOK e fuel n lo (a + b) := fun c hc1 hc2 => by
  rcases Nat.lt_or_ge c (lo + a) with h | h
  · exact h1 c hc1 h
  · exact h2 c h (by omega)

theorem catch_of_chunks (e fuel n : Nat) (hn : n ≤ 2 ^ e - 1)
    (h : ChunksOK e fuel n 0 (2 ^ (2 ^ e - 1 - n)))
    {d : Nat → Column} (hd : Recurrence d) (clocks : PrefixClocks d)
    {a b : Nat} (loss : FirstLoss d a e) (hab : NextWhite d a b) (s : Nat) :
    Catch d a b s :=
  catch_of_checks e fuel n hn (fun c hc => h c (Nat.zero_le _) (by omega)) hd clocks loss hab s

/-! ## 5. Unconditional closure for `0 ≤ e ≤ 4` (`65,814` anti-periodic drivers) & `e ≥ 5` reductions -/

theorem check_e0 : check 0 6 0 0 = true := by decide +kernel
theorem check_e1 : check 1 13 1 0 = true := by decide +kernel
theorem check_e2 : check 2 34 3 0 = true := by decide +kernel
theorem check_e3 : check 3 44 7 0 = true := by decide +kernel

theorem check_e4 : check 4 70 15 0 = true := by decide +kernel

/-- **Unconditional Single-Interval Doubling Capture for `e ≤ 4` (`L ≤ 32`):**
on every recurrent strip with `PrefixClocks`, every `FirstLoss d a e` with `e ≤ 4` catches every
tick `s : Nat` before the very next white wheel `b`. -/
theorem catch_of_firstLoss_le_four {d : Nat → Column} (hd : Recurrence d)
    (clocks : PrefixClocks d) {a e b : Nat} (he : e ≤ 4)
    (loss : FirstLoss d a e) (hab : NextWhite d a b) (s : Nat) :
    Catch d a b s := by
  have hcases : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl
  · exact catch_of_chunks 0 6 0 (by decide) (chunksOK_one check_e0) hd clocks loss hab s
  · exact catch_of_chunks 1 13 1 (by decide) (chunksOK_one check_e1) hd clocks loss hab s
  · exact catch_of_chunks 2 34 3 (by decide) (chunksOK_one check_e2) hd clocks loss hab s
  · exact catch_of_chunks 3 44 7 (by decide) (chunksOK_one check_e3) hd clocks loss hab s
  · exact catch_of_chunks 4 70 15 (by decide) (chunksOK_one check_e4) hd clocks loss hab s

/-- Single-interval doubling hypothesis restricted to exponents `e ≥ e0`. -/
def DLFrom (e0 : Nat) : Prop :=
  ∀ (d : Nat → Column), Recurrence d → d 0 0 = true → PrefixClocks d →
    ∀ a e b, e0 ≤ e → FirstLoss d a e → NextWhite d a b → ∀ s, Catch d a b s

/-- Two-interval relaxed doubling hypothesis restricted to exponents `e ≥ e0`. -/
def DLMinusOneFrom (e0 : Nat) : Prop :=
  ∀ (d : Nat → Column), Recurrence d → d 0 0 = true → PrefixClocks d →
    ∀ a e b c, e0 ≤ e → FirstLoss d a e → NextWhite d a b → NextWhite d b c → ∀ s, Catch d a c s

/-- **Exact Single-Interval Equivalence (`DL ↔ DLFrom 5`):**
because all `e ≤ 4` (`L ≤ 32`) catch unconditionally in `[a, b]`, single-interval `DL` holds across
all exponents if and only if it holds for `e ≥ 5` (`L ≥ 64`). -/
theorem dl_iff_from_five : DL ↔ DLFrom 5 := by
  constructor
  · intro h d hd h0 clocks a e b _ loss hab s
    exact h d hd h0 clocks a e b loss hab s
  · intro h d hd h0 clocks a e b loss hab s
    by_cases he : 5 ≤ e
    · exact h d hd h0 clocks a e b he loss hab s
    · exact catch_of_firstLoss_le_four hd clocks (by omega) loss hab s

/-- **Exact Equivalence (`DLMinusOne ↔ DLMinusOneFrom 5`):**
because all `e ≤ 4` (`L ≤ 32`) catch unconditionally in `[a, b]`, `DLMinusOne` holds if and only
if two-interval capture holds for `e ≥ 5` (`L ≥ 64`). -/
theorem dlMinusOne_iff_from_five : DLMinusOne ↔ DLMinusOneFrom 5 := by
  constructor
  · intro h d hd h0 clocks a e b _c _ loss hab hbc s
    exact h d hd h0 clocks a e b _c loss hab hbc s
  · intro h d hd h0 clocks a e b c loss hab hbc s
    by_cases he : 5 ≤ e
    · exact h d hd h0 clocks a e b c he loss hab hbc s
    · have hc1 := catch_of_firstLoss_le_four hd clocks (by omega) loss hab s
      exact (catch_split (Nat.le_of_lt hab.1) (Nat.le_of_lt hbc.1) (hab.2.1 s)).mpr (Or.inl hc1)

theorem dlMinusOne_of_dlFrom_five (h : DLFrom 5) : DLMinusOne :=
  dlMinusOne_iff_from_five.mpr fun d hd h0 clocks a e b _c he loss hab hbc s =>
    (catch_split (Nat.le_of_lt hab.1) (Nat.le_of_lt hbc.1) (hab.2.1 s)).mpr
      (Or.inl (h d hd h0 clocks a e b he loss hab s))

theorem lInfinity_of_dlFrom_five (h : DLFrom 5) : LInfinity :=
  lInfinity_of_dlMinusOne (dlMinusOne_of_dlFrom_five h)

theorem everyK_of_dlFrom_five (h : DLFrom 5) :
    EveryK (fun k => settlingBound (widthFor (cap_of_unbounded_resets
      (lInfinity_of_dlFrom_five h)) k)) :=
  everyK_of_dlMinusOne (dlMinusOne_of_dlFrom_five h)

theorem every_k_line_of_dlFrom_five (h : DLFrom 5) (k : Nat) :
    ∃ age : Nat, ∀ (x : Int → Bool) (lo : Int), x lo = true → (∀ p, p < lo → x p = false) →
      ∀ t, age ≤ t → ∀ V : Int → Bool,
        (∀ p, Rule30Realization.evol V k p = Rule30Realization.evol x t p) →
          V (lo - t + k) = true ∧ ∀ p, p < lo - t + k → V p = false :=
  Rule30EveryKLine.every_k_line_of_dlMinusOne (dlMinusOne_of_dlFrom_five h) k

end Ruliology.CellularAutomata.Rule30DoublingLanes
