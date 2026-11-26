module

public import Ruliology.CellularAutomata.Rule30ZeroBoundary

/-!
# A five-sample decoder for the free phase beside 001

Under the zero-wall reduction for 001, depth one has triples (white, free, black).
The complements of the first five forbidden gate words in Rule30PeriodThreeEntry.words001
already suffice. In a window of nine free bits, five readings of depth 12 (one per
triple at phase two) recover the middle free bit. The reconstruction holds for
the actual zero-boundary evolution, with arbitrary window start and initial row.

The paper interpretation of the local code is that a complete run pair of free
bits 1^h 0^l emits 0^3 1^(h-3) 0 1^(l-1) when the output is aligned with the
last input of its five-bit window. Thus there are four white readings per pair.
Their signed contributions along an inward diagonal telescope to the endpoint
difference. Repeated loss at this one depth does not give a spatial induction.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30PeriodThreeDepthTwelve

open Rule30ZeroBoundary (zrow zrow_inv zrow_wall)

/-- Pack a time word with the first reading in the low bit. -/
def pack (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n+1 => (pack (fun i => f (i+1)) n <<< 1) ||| (f 0).toNat

private theorem pack_bit (f : Nat → Bool) (n i : Nat) (h : i < n) :
    (pack f n).testBit i = f i := by
  induction n generalizing f i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => cases e : f 0 <;> simp [pack, e]
    | succ i =>
      have hi := ih (fun j => f (j+1)) i (by omega)
      have one : Nat.testBit 1 (i+1) = false := by
        cases e : Nat.testBit 1 (i+1) with
        | false => rfl
        | true => have := Nat.testBit_one_eq_true_iff_self_eq_zero.mp e; omega
      cases e : f 0 <;> simpa [pack, e, Nat.testBit_shiftLeft, one] using hi

/-- The five forbidden factors on the left free stream, in chronological order. -/
def allowed (w : Nat) : Bool :=
  let avoids (pat width : Nat) := (List.range (10-width)).all fun j =>
    ((w >>> j) % 2^width) != pat
  -- The low-bit-first factors are 101, 010, 0110, 00000, 111111.
  avoids 5 3 && avoids 2 3 && avoids 6 4 && avoids 0 5 && avoids 63 6

/-- Phase pattern of depth one from a packed window of free bits. -/
def tripleBit (w j : Nat) : Bool :=
  if j % 3 = 1 then w.testBit (j / 3) else decide (j % 3 = 2)

private def pair (trace : Nat) : Nat → Nat × Nat
  | 0 => (0, trace)
  | n+1 =>
    let (r,s) := pair trace n
    (s, (s >>> 1) ^^^ (s ||| r))

private theorem pair_sound (L : Nat → Bool) (t w n : Nat)
    (h : ∀ j, j < n → zrow L (t+j) 1 = w.testBit j) (d : Nat) :
    ∀ j, d+j < n →
      (pair w d).1.testBit j = zrow L (t+j) d ∧
      (pair w d).2.testBit j = zrow L (t+j) (d+1) := by
  induction d with
  | zero =>
    intro j hj
    exact ⟨by simp [pair, zrow_wall], (h j (by omega)).symm⟩
  | succ d ih =>
    intro j hj
    obtain ⟨r,s⟩ := ih j (by omega)
    have next := (ih (j+1) (by omega)).2
    refine ⟨s, ?_⟩
    simp only [pair, Nat.testBit_xor, Nat.testBit_shiftRight, Nat.testBit_or]
    rw [Nat.add_comm 1 j, next, s, r, zrow_inv L (t+j) d]
    rfl

/-- Five depth-12 readings, ordered earliest first. -/
def decode (b c d e f : Bool) : Bool :=
  let code := 16*b.toNat + 8*c.toNat + 4*d.toNat + 2*e.toNat + f.toNat
  ![8,12,14,16,17,24,28].contains code

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem table : ∀ w : Fin 512, allowed w.val = true →
    let q := (pair (pack (tripleBit w.val) 27) 11).2
    decode (q.testBit 2) (q.testBit 5) (q.testBit 8) (q.testBit 11) (q.testBit 14) =
      w.val.testBit 4 := by decide

/-- Recover the middle free bit of nine legal triples from the five
phase-two readings at depth 12 in the same physical history. -/
theorem recover_middle (L : Nat → Bool) (t : Nat) (w : Fin 512)
    (hw : allowed w.val = true)
    (trace : ∀ j, j < 27 → zrow L (t+j) 1 = tripleBit w.val j) :
    let q := fun j => zrow L (t+j) 12
    decode (q 2) (q 5) (q 8) (q 11) (q 14) = zrow L (t+13) 1 := by
  have h j (hj : j < 27) : zrow L (t+j) 1 = (pack (tripleBit w.val) 27).testBit j :=
    (trace j hj).trans (pack_bit _ _ _ hj).symm
  have eqn := table w hw
  dsimp only at eqn ⊢
  have read (j : Nat) (hj : 11+j < 27) := (pair_sound L t _ 27 h 11 j hj).2
  rw [read 2 (by decide), read 5 (by decide), read 8 (by decide),
      read 11 (by decide), read 14 (by decide)] at eqn
  exact eqn.trans (trace 13 (by decide)).symm

/-- A period in the late depth-12 observations transfers with the same period
to the free bits four triples later. The window start may have any offset. -/
theorem transfer_period (L : Nat → Bool) (start K P : Nat)
    (legalTail : ∀ k, K ≤ k → ∃ w : Fin 512, allowed w.val = true ∧
      ∀ j, j < 27 → zrow L (start+3*k+j) 1 = tripleBit w.val j)
    (period : ∀ k, K ≤ k →
      zrow L (start+3*(k+P)+2) 12 = zrow L (start+3*k+2) 12)
    (k : Nat) (hk : K ≤ k) :
    zrow L (start+3*(k+4+P)+1) 1 = zrow L (start+3*(k+4)+1) 1 := by
  let q := fun m j => zrow L (start+3*m+j) 12
  have observed (m : Nat) (hm : K ≤ m) :
      decode (q m 2) (q m 5) (q m 8) (q m 11) (q m 14) = zrow L (start+3*m+13) 1 := by
    obtain ⟨w, hw, ht⟩ := legalTail m hm
    exact recover_middle L (start+3*m) w hw ht
  have left := observed (k+P) (by omega)
  have right := observed k hk
  have eqRead (j : Nat) : q (k+P) (3*j+2) = q k (3*j+2) := by
    dsimp only [q]
    rw [show start+3*(k+P)+(3*j+2) = start+3*(k+j+P)+2 by omega,
        show start+3*k+(3*j+2) = start+3*(k+j)+2 by omega]
    exact period (k+j) (by omega)
  rw [eqRead 0, eqRead 1, eqRead 2, eqRead 3, eqRead 4] at left
  rw [show start+3*(k+4+P)+1 = start+3*(k+P)+13 by omega,
      show start+3*(k+4)+1 = start+3*k+13 by omega]
  exact left.symm.trans right

/-! ## Tail determination, column-1 periodicity lifting, and infinite support of periodic depth-12 trajectories -/

/-- Predicate that from triple `K` onward, column `1` follows `tripleBit` of `allowed` 9-bit windows. -/
def LegalTail (L : Nat → Bool) (start K : Nat) : Prop :=
  ∀ k, K ≤ k → ∃ w : Fin 512, allowed w.val = true ∧
    ∀ j, j < 27 → zrow L (start + 3 * k + j) 1 = tripleBit w.val j

/-- **Exact free-tail recovery from phase-2 depth-12 readings (`recover_free_tail_from_depth12`).** -/
theorem recover_free_tail_from_depth12 (L : Nat → Bool) (start K k : Nat)
    (hL : LegalTail L start K) (hk : K ≤ k) :
    zrow L (start + 3 * (k + 4) + 1) 1 =
      decode (zrow L (start + 3 * k + 2) 12)
             (zrow L (start + 3 * k + 5) 12)
             (zrow L (start + 3 * k + 8) 12)
             (zrow L (start + 3 * k + 11) 12)
             (zrow L (start + 3 * k + 14) 12) := by
  obtain ⟨w, hw, ht⟩ := hL k hk
  have hr := recover_middle L (start + 3 * k) w hw ht
  rw [show start + 3 * (k + 4) + 1 = start + 3 * k + 13 by omega]
  exact hr.symm

/-- **Uniqueness of the column-1 tail from phase-2 depth-12 samples (`depth12_uniquely_determines_col1_tail`):**
two starts `L1, L2` with `LegalTail` from `(start, K)` and identical phase-2 depth-12 readings from
`K` onward agree on **every** column-1 tick `t ≥ start + 3 * (K + 4)`. -/
theorem depth12_uniquely_determines_col1_tail (L1 L2 : Nat → Bool) (start K : Nat)
    (h1 : LegalTail L1 start K) (h2 : LegalTail L2 start K)
    (heq12 : ∀ k, K ≤ k → zrow L1 (start + 3 * k + 2) 12 = zrow L2 (start + 3 * k + 2) 12)
    (t : Nat) (ht : start + 3 * (K + 4) ≤ t) :
    zrow L1 t 1 = zrow L2 t 1 := by
  let d := t - (start + 3 * (K + 4))
  let m := d / 3
  let r := d % 3
  have hdecomp : t = start + 3 * (K + 4 + m) + r := by dsimp [d, m, r]; omega
  rw [hdecomp]
  have hr : r = 0 ∨ r = 1 ∨ r = 2 := by dsimp [r]; omega
  rcases hr with r0 | r1 | r2
  · rw [r0, Nat.add_zero]
    obtain ⟨w1, _, ht1⟩ := h1 (K + 4 + m) (by omega)
    obtain ⟨w2, _, ht2⟩ := h2 (K + 4 + m) (by omega)
    have e1 := ht1 0 (by decide)
    have e2 := ht2 0 (by decide)
    rw [Nat.add_zero] at e1 e2
    exact e1.trans e2.symm
  · rw [r1]
    rw [show K + 4 + m = (K + m) + 4 by omega,
        recover_free_tail_from_depth12 L1 start K (K + m) h1 (by omega),
        recover_free_tail_from_depth12 L2 start K (K + m) h2 (by omega)]
    have step12 (j : Nat) :
        zrow L1 (start + 3 * (K + m) + (3 * j + 2)) 12 =
          zrow L2 (start + 3 * (K + m) + (3 * j + 2)) 12 := by
      rw [show start + 3 * (K + m) + (3 * j + 2) = start + 3 * (K + m + j) + 2 by omega]
      exact heq12 (K + m + j) (by omega)
    rw [step12 0,
        show start + 3 * (K + m) + 5 = start + 3 * (K + m) + (3 * 1 + 2) by omega, step12 1,
        show start + 3 * (K + m) + 8 = start + 3 * (K + m) + (3 * 2 + 2) by omega, step12 2,
        show start + 3 * (K + m) + 11 = start + 3 * (K + m) + (3 * 3 + 2) by omega, step12 3,
        show start + 3 * (K + m) + 14 = start + 3 * (K + m) + (3 * 4 + 2) by omega, step12 4]
  · rw [r2]
    obtain ⟨w1, _, ht1⟩ := h1 (K + 4 + m) (by omega)
    obtain ⟨w2, _, ht2⟩ := h2 (K + 4 + m) (by omega)
    exact (ht1 2 (by decide)).trans (ht2 2 (by decide)).symm

/-- **Full column-1 eventual periodicity from phase-2 depth-12 periodicity
(`eventuallyPeriodic_col1_of_periodic_depth12`).** -/
theorem eventuallyPeriodic_col1_of_periodic_depth12 (L : Nat → Bool) (start K P : Nat)
    (hP : 0 < P) (hL : LegalTail L start K)
    (period : ∀ k, K ≤ k → zrow L (start + 3 * (k + P) + 2) 12 = zrow L (start + 3 * k + 2) 12) :
    Rule30Jen.EventuallyPeriodic (fun t => zrow L t 1) := by
  refine ⟨start + 3 * (K + 4), 3 * P, by omega, fun t ht => ?_⟩
  let d := t - (start + 3 * (K + 4))
  let m := d / 3
  let r := d % 3
  have ht1 : t = start + 3 * (K + m + 4) + r := by dsimp [d, m, r]; omega
  have ht2 : t + 3 * P = start + 3 * (K + m + 4 + P) + r := by dsimp [d, m, r]; omega
  dsimp only
  rw [ht2, ht1]
  have hr : r = 0 ∨ r = 1 ∨ r = 2 := by dsimp [r]; omega
  rcases hr with r0 | r1 | r2
  · rw [r0, Nat.add_zero, Nat.add_zero]
    obtain ⟨w1, _, h1⟩ := hL (K + m + 4 + P) (by omega)
    obtain ⟨w2, _, h2⟩ := hL (K + m + 4) (by omega)
    have e1 := h1 0 (by decide)
    have e2 := h2 0 (by decide)
    rw [Nat.add_zero] at e1 e2
    exact e1.trans e2.symm
  · rw [r1]
    exact transfer_period L start K P hL period (K + m) (by omega)
  · rw [r2]
    obtain ⟨w1, _, h1⟩ := hL (K + m + 4 + P) (by omega)
    obtain ⟨w2, _, h2⟩ := hL (K + m + 4) (by omega)
    exact (h1 2 (by decide)).trans (h2 2 (by decide)).symm

/-- **`LegalTail` forces at least one initial black cell (`exists_black_of_legalTail`).** -/
theorem exists_black_of_legalTail (L : Nat → Bool) (start K : Nat)
    (hL : LegalTail L start K) : ∃ k, 1 ≤ k ∧ L k = true := by
  apply Classical.byContradiction
  intro hall
  have hz : ∀ k, 0 < k → L k = false := by
    intro k hk
    cases hLk : L k with
    | false => rfl
    | true => exact False.elim (hall ⟨k, hk, hLk⟩)
  have hfin0 := Rule30ZeroBoundary.zrow_fin hz (start + 3 * K + 2) 1
  -- Wait: `zrow_fin` requires `0 + t < 1`, whereas `all-zero` stays all-zero at ALL `t` and `k`!
  have hallz : ∀ t k, zrow L t k = false := by
    intro t
    induction t with
    | zero =>
      intro k
      cases k with
      | zero => exact zrow_wall L 0
      | succ k => exact hz (k + 1) (by omega)
    | succ t ih =>
      intro k
      cases k with
      | zero => exact zrow_wall L (t + 1)
      | succ k =>
        have hinv := zrow_inv L t k
        -- `zrow_inv L t k` says `zrow L t (k + 2) = ((zrow L (t + 1) (k + 1)).xor (zrow L t k || zrow L t (k + 1)))`
        rw [ih (k + 2), ih k, ih (k + 1)] at hinv
        cases hcell : zrow L (t + 1) (k + 1)
        · rfl
        · rw [hcell] at hinv
          exact Bool.noConfusion hinv
  obtain ⟨w, _, hw⟩ := hL K (Nat.le_refl K)
  have htrue : zrow L (start + 3 * K + 2) 1 = true := hw 2 (by decide)
  rw [hallz] at htrue
  exact Bool.noConfusion htrue

/-- **No finitely supported start has a periodic phase-2 depth-12 tail (`not_finSupp_of_periodic_depth12`):**
combining `eventuallyPeriodic_col1_of_periodic_depth12`, `exists_black_of_legalTail`, and
`Rule30ZeroBoundary.col_not_eventually_periodic` rules out `FinSupp L` unconditionally for every `0 < P`. -/
theorem not_finSupp_of_periodic_depth12 (L : Nat → Bool) (start K P : Nat)
    (hP : 0 < P) (hL : LegalTail L start K)
    (period : ∀ k, K ≤ k → zrow L (start + 3 * (k + P) + 2) 12 = zrow L (start + 3 * k + 2) 12) :
    ¬ Rule30ZeroBoundary.FinSupp L := by
  rintro ⟨W, hW⟩
  obtain ⟨k0, hk0, htrue0⟩ := exists_black_of_legalTail L start K hL
  -- Find rightmost black cell `m ≤ max W k0`
  have haux : ∀ B, (∃ k, 1 ≤ k ∧ k ≤ B ∧ L k = true) → (∀ k, B < k → L k = false) →
      ∃ m, 1 ≤ m ∧ L m = true ∧ ∀ k, m < k → L k = false := by
    intro B
    induction B with
    | zero => rintro ⟨k, hk1, hk0, _⟩ _; omega
    | succ B ih =>
      intro hex hB
      cases hLB : L (B + 1) with
      | true => exact ⟨B + 1, by omega, hLB, hB⟩
      | false =>
        apply ih
        · obtain ⟨k, hk1, hkle, hLk⟩ := hex
          have hne : k ≠ B + 1 := fun heq => by rw [heq, hLB] at hLk; exact Bool.noConfusion hLk
          exact ⟨k, hk1, by omega, hLk⟩
        · intro k hk
          by_cases heq : k = B + 1
          · subst heq; exact hLB
          · exact hB k (by omega)
  have hB : ∀ k, W + k0 < k → L k = false := fun k hk => hW k (by omega)
  obtain ⟨m, hm, hedge, hz⟩ := haux (W + k0) ⟨k0, hk0, by omega, htrue0⟩ hB
  exact Rule30ZeroBoundary.col_not_eventually_periodic hm hedge hz
    (eventuallyPeriodic_col1_of_periodic_depth12 L start K P hP hL period)

end Ruliology.CellularAutomata.Rule30PeriodThreeDepthTwelve
