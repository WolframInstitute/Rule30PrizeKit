module

public import Ruliology.CellularAutomata.Rule30EtherTwoCellAux

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30Ether

open Rule30Jen Rule30StripCertificates

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
# A packed evaluator for two-cell absorption and its soundness proof

A row of the driven right half is packed into a `Nat`: bit `p` is cell `p` for `p ≥ 0`, with bit
`0` carrying the driver value.  One step is a handful of bit operations on a `Nat`, which the
kernel evaluates far faster than a list recurrence.  This file proves that the packed recurrence
computes the true orbit on every column inside the light cone, and derives the soundness of a
packed family check for the two-cell right half.
-/

/-- The driver value as a `Nat` bit. -/
def dN (d : Bool) : Nat := if d then 1 else 0

/-- The low `W` bits. -/
def maskB (W : Nat) : Nat := (1 <<< W) - 1

/-- One packed step.  `d` is the driver value at the **new** time.  Bit `0` is replaced by `d`;
bits `1 .. W-1` follow rule 30; bits `≥ W` are white. -/
def stepN (d : Bool) (W : Nat) (row : Nat) : Nat :=
  let v := (row <<< 1) ^^^ (row ||| (row >>> 1))
  (((v >>> 1) <<< 1) &&& maskB W) ||| dN d

/-- `t` packed steps of the driven right half with driver `c`. -/
def runN (c : Nat → Bool) (W : Nat) : Nat → Nat → Nat
  | 0, row => row
  | n + 1, row => stepN (c (n + 1)) W (runN c W n row)

/-! ### Bit lemmas -/

theorem testBit_dN (d : Bool) (j : Nat) : (dN d).testBit j = (decide (j = 0) && d) := by
  unfold dN
  cases d with
  | false => simp
  | true =>
    rw [if_pos rfl]
    have h1 : (1 : Nat) = 2 ^ 0 := rfl
    rw [h1, Nat.testBit_two_pow]
    by_cases hj : j = 0
    · simp [hj]
    · simp only [hj, decide_false, Bool.false_and]
      exact decide_eq_false_iff_not.2 (fun h => hj h.symm)

theorem testBit_maskB {W p : Nat} (hp : p < W) : (maskB W).testBit p = true := by
  unfold maskB
  have h : (1 <<< W : Nat) = 2 ^ W := by rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [h, Nat.testBit_two_pow_sub_one]
  simp [hp]

theorem testBit_shiftl_one (p i : Nat) : ((1 <<< p).testBit i) = decide (i = p) := by
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]
  by_cases h : i = p
  · simp [h]
  · simp only [h, decide_false, decide_false, BEq.beq]
    exact decide_eq_false_iff_not.2 (fun hh => h hh.symm)

theorem testBit_shift_pair_clear (v : Nat) : (((v >>> 1) <<< 1)).testBit 0 = false := by
  rw [Nat.testBit_shiftLeft]
  simp

theorem testBit_shift_pair {v p : Nat} (hp : 1 ≤ p) :
    (((v >>> 1) <<< 1)).testBit p = v.testBit p := by
  rw [Nat.testBit_shiftLeft]
  simp only [show decide (p ≥ 1) = true from by simp [hp], Bool.true_and]
  rw [Nat.testBit_shiftRight]
  congr 1
  omega

/-- Bit `p` of one packed step, for `1 ≤ p < W`. -/
theorem stepN_testBit {d : Bool} {W row p : Nat} (h1 : 1 ≤ p) (hp : p < W) :
    (stepN d W row).testBit p =
      ((row.testBit (p - 1)) ^^ ((row.testBit p) || (row.testBit (p + 1)))) := by
  unfold stepN
  rw [Nat.testBit_or, Nat.testBit_and, testBit_shift_pair h1, testBit_maskB hp, Bool.and_true,
    Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, testBit_dN]
  simp only [h1, decide_true, Bool.true_and, Nat.add_comm 1 p,
    show p ≠ 0 by omega, decide_false, Bool.false_and, Bool.false_or, Bool.or_false]

/-- Bit `0` of one packed step is the driver value. -/
theorem stepN_testBit_zero (d : Bool) (W row : Nat) (hW : 1 ≤ W) :
    (stepN d W row).testBit 0 = d := by
  unfold stepN
  rw [Nat.testBit_or, Nat.testBit_and, testBit_shift_pair_clear, Bool.false_and, Bool.false_or,
    testBit_dN]
  simp

/-! ### Correctness of the packed recurrence -/

theorem runN_spec {c x : Nat → Bool} {init W : Nat}
    (hinit0 : init.testBit 0 = c 0)
    (hinit : ∀ i, 1 ≤ i → i < W → init.testBit i = x i)
    (hW : ∀ i, W ≤ i → x i = false) :
    ∀ t p, p + t < W → (runN c W t init).testBit p = drv c x t p := by
  intro t
  induction t with
  | zero =>
    intro p hp
    rw [runN]
    rcases Nat.eq_zero_or_pos p with hp0 | hp1
    · subst hp0
      rw [hinit0]
      rfl
    · rw [hinit p hp1 hp]
      exact (drv_init c x p hp1).symm
  | succ t ih =>
    intro p hp
    rw [runN]
    rcases Nat.eq_zero_or_pos p with hp0 | hp1
    · subst hp0
      rw [stepN_testBit_zero _ _ _ (by omega)]
      rfl
    · rw [stepN_testBit hp1 (by omega), ih (p - 1) (by omega), ih p (by omega),
        ih (p + 1) (by omega)]
      obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
      rw [show drv c x (t + 1) (p' + 1) =
        rule (drv c x t p') (drv c x t (p' + 1)) (drv c x t (p' + 2)) from rfl]
      rfl

/-! ### The packed family check -/

/-- The packed initial row: driver at bit `0`, black cells at `p` and `q`. -/
def initN (p q φ : Nat) : Nat := dN (wordAt w0001 φ) ||| (1 <<< p) ||| (1 <<< q)

theorem testBit_initN_zero {p q φ : Nat} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    (initN p q φ).testBit 0 = wordAt w0001 φ := by
  unfold initN
  have hp0 : ((1 <<< p).testBit 0) = false := by
    rw [testBit_shiftl_one]
    exact decide_eq_false_iff_not.2 (by omega)
  have hq0 : ((1 <<< q).testBit 0) = false := by
    rw [testBit_shiftl_one]
    exact decide_eq_false_iff_not.2 (by omega)
  rw [Nat.testBit_or, Nat.testBit_or, testBit_dN, hp0, hq0]
  simp

theorem testBit_initN {p q φ i : Nat} (hp : 1 ≤ p) (hq : 1 ≤ q) (hi : 1 ≤ i) :
    (initN p q φ).testBit i = delta2 p q i := by
  unfold initN delta2
  rw [Nat.testBit_or, Nat.testBit_or, testBit_dN, testBit_shiftl_one, testBit_shiftl_one]
  have hi0 : ¬ i = 0 := by omega
  simp only [hi0, decide_false, Bool.false_and, Bool.false_or]
  by_cases hip : i = p <;> by_cases hiq : i = q <;> simp [hip, hiq]

/-- Packed family check at time `t`: ether columns `1..k` (alignment `(j0, φ)`) and a wall strip
`k+1 .. k+13`.  The width is chosen so the whole window is inside the light cone. -/
def famRowN (p q φ t k j0 : Nat) : Bool :=
  let W := max q (k + 13 + t) + 2
  let row := runN (fun n => wordAt w0001 (n + φ)) W t (initN p q φ)
  ((j0 + k) % 7 == 2) && (j0 == 5 || j0 == 6) &&
  (List.range k).all (fun i => row.testBit (i + 1) == ether (j0 + i + 1) (t + φ)) &&
  wallStates.contains (((t + φ) % 4, (List.range 13).map (fun i => row.testBit (k + i + 1))))

/-- **Soundness of the packed family check**, with the witness data exposed. -/
theorem famRowN_data {j0 p q φ t k : Nat} (hp : 1 ≤ p) (hpq : p < q)
    (h : famRowN p q φ t k j0 = true) :
    (j0 = 5 ∨ j0 = 6) ∧ (j0 + k) % 7 = 2 ∧
      (∀ r, 1 ≤ r → r ≤ k →
        drv (fun n => wordAt w0001 (n + φ)) (delta2 p q) t r = ether (j0 + r) (t + φ)) ∧
      ((t + φ) % 4, rowOf (drv (fun n => wordAt w0001 (n + φ)) (delta2 p q)) t k 13)
        ∈ wallStates := by
  have hq1 : 1 ≤ q := by omega
  have hrow : ∀ r, 1 ≤ r → r + t ≤ max q (k + 13 + t) + 1 →
      (runN (fun n => wordAt w0001 (n + φ)) (max q (k + 13 + t) + 2) t (initN p q φ)).testBit r =
        drv (fun n => wordAt w0001 (n + φ)) (delta2 p q) t r := by
    intro r hr1 hrt
    refine runN_spec (c := fun n => wordAt w0001 (n + φ)) (x := delta2 p q) (W := max q (k+13+t)+2)
      (init := initN p q φ) ?_ ?_ ?_ t r (by omega)
    · rw [testBit_initN_zero hp hq1, Nat.zero_add]
    · intro i hi1 hiW
      rw [testBit_initN hp hq1 hi1]
    · intro i hiW
      have hqi : q < i := by omega
      exact delta2_eq_false (by omega) (by omega)
  unfold famRowN at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hk, hjok⟩, hE⟩, hW⟩ := h
  have hj : j0 = 5 ∨ j0 = 6 := by
    simpa only [Bool.or_eq_true, beq_iff_eq] using hjok
  refine ⟨hj, beq_iff_eq.1 hk, ?_, ?_⟩
  · intro r hr1 hrk
    have hmem := List.all_eq_true.1 hE (r - 1) (List.mem_range.2 (by omega))
    have hbit := beq_iff_eq.1 hmem
    rw [show r - 1 + 1 = r by omega] at hbit
    rw [← hrow r hr1 (by omega), hbit]
    exact ether_congr (by omega) (by omega)
  · have hwall : rowOf (drv (fun n => wordAt w0001 (n + φ)) (delta2 p q)) t k 13 =
        (List.range 13).map
          (fun i => (runN (fun n => wordAt w0001 (n + φ)) (max q (k + 13 + t) + 2) t
            (initN p q φ)).testBit (k + i + 1)) := by
      rw [rowOf_eq_map]
      apply List.map_congr_left
      intro i hi
      have hi13 : i < 13 := List.mem_range.1 hi
      exact (hrow (k + i + 1) (by omega) (by omega)).symm
    rw [hwall]
    exact List.contains_iff_mem.1 hW

theorem famRowN_sound {j0 p q φ t k : Nat} (hp : 1 ≤ p) (hpq : p < q)
    (h : famRowN p q φ t k j0 = true) :
    (j0 = 5 ∨ j0 = 6) ∧
      InFamily (drv (fun n => wordAt w0001 (n + φ)) (delta2 p q)) j0 φ t := by
  obtain ⟨hj, hk, hE, hW⟩ := famRowN_data hp hpq h
  exact ⟨hj, k, hk, hE, hW⟩

/-- A data row `(t, k, j0)`: the family is reached at time `t` with run length `k` and alignment
`j0`.  `checkRange` verifies every entry against the packed recurrence. -/
def checkRange (data : List (Nat × Nat × Nat)) (p φ : Nat) : Bool :=
  (List.range data.length).all (fun i =>
    let d := data.getD i (0, 6, 3)
    famRowN p (p + 1 + i) φ d.1 d.2.1 d.2.2)

/-- **Soundness of a range check.** -/
theorem checkRange_sound {data : List (Nat × Nat × Nat)} {p φ q : Nat}
    (hp : 1 ≤ p) (h : checkRange data p φ = true) (hpq : p < q)
    (hq : q < p + 1 + data.length) :
    let d := data.getD (q - p - 1) (0, 6, 3)
    (d.2.2 = 5 ∨ d.2.2 = 6) ∧
      InFamily (drv (fun n => wordAt w0001 (n + φ)) (delta2 p q)) d.2.2 φ d.1 := by
  intro
  have hi : q - p - 1 < data.length := by omega
  have hall := List.all_eq_true.1 h (q - p - 1) (List.mem_range.2 hi)
  have hqeq : p + 1 + (q - p - 1) = q := by omega
  rw [hqeq] at hall
  exact famRowN_sound hp hpq hall

end Rule30Ether
end Ruliology.CellularAutomata
