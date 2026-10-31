module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryLanes
public import Ruliology.CellularAutomata.Rule30EtherThreeLeft
public import Ruliology.CellularAutomata.Rule30PeriodFourSkeleton

/-!
# The words `0^(P-1) 1`, the statement `QP P`, and a bit-sliced checker for every period `P`

If the center column is eventually `(0^(P-1) 1)^∞` for some `P ≥ 2` (one black cell per period),
then two consecutive center cells are never both black, so the left half evolves as if column `0`
were white (`Rule30DrivenLeft.cell_eq_L_effective`), and at the black steps of the center column
left permutivity forces column `-1` black. So the word is excluded by the left-only
statement `QP P`: **no start of the zero-driven left half with a leftmost black cell keeps column
`-1` black at every `P`-th step**. `QP 2` is `Rule30PeriodTwo.Q01` and `QP 3` is
`Rule30EtherThree.Q001`. `QP P` is **open** for every `P ≥ 2`.

* `not_eventually_oneBlack_of_QP`, `not_eventuallyWord_oneBlack_of_QP`: for every `P ≥ 2`, `QP P`
  excludes `(0^(P-1) 1)^∞` as a tail of the center column, whatever the transient.
* `QP_two_iff_Q01`, `QP_three_iff_Q001`: the kit's statements for the periods `2` and `3`.
  `C3_0001_of_QP_four`: `QP 4` implies `Rule30PeriodFourSkeleton.C3 w0001`, the weaker statement
  that already excludes `0001`. For `P ≥ 10` the word is excluded outright, up to rotation, by
  `Rule30WhiteEndNine`, so the reduction is new for `P = 5, …, 9`.
* `QP_iff_zrow`, `QP_iff_any_phase`: `QP P` for the zero-boundary left half
  `Rule30ZeroBoundary.zrow`, from phase `0` or from any phase, as `Rule30ZeroBoundary.Q01_iff_staged`
  and `Rule30ZeroBoundary.Q01_iff_any_phase` give it for `P = 2`.

**The checker.** `Rule30ZeroBoundaryLanes` checks `Q01` (the even steps) for all starts of bounded
width. Here it is generalized to the multiples of any period `P ≥ 2`, on the same anti-diagonal
recurrence (`Rule30ZeroBoundaryLanes.scanN`, `Rule30ZeroBoundaryLanes.level`). A start supported at
depths `1, …, W` that keeps depth `1` black at the levels `k` with `k % P = 0` is fixed by its
free bits `y k`, `k % P ≠ 0`: the `nfree W P` free bits with `k + 1 ≤ W` (numbered by `fidx`) are
arbitrary, and every later free bit is forced by `L (k + 1) = 0`. `checkP W P K n c` runs `2 ^ n`
choices of the first `n` free bits at once, one per bit position of each natural number, and the
chunk index `c` fixes the others; a lane dies when some `L (k + 1)` with `W < k + 1` is black at a
level `k` with `k % P = 0`.

* `runP_sound`, `qP_of_checks`, `qP_of_chunks`: if every chunk passes, every start supported at
  depths `≤ W` has a white cell at depth `1` at some step `t < K` with `t % P = 0`.
* `bounded_of_chunks`, `QP_restricted_of_chunks`: the same for `Rule30DrivenLeft.L`, and as `QP P`
  restricted to leftmost black cells at depth `≤ W`.
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30ZeroBoundaryPeriodLanes

open Rule30Jen Rule30Prize Rule30DrivenLeft Rule30ZeroBoundary Rule30ZeroBoundaryLanes

/-! ## The statement `QP P` and the reduction -/

/-- **`QP P`** (open for every `P ≥ 2`). No start of the zero-driven left half with a leftmost
black cell (at `-m`, `m ≥ 1`, white beyond) keeps column `-1` black at every `P`-th step. -/
def QP (P : Nat) : Prop :=
  ∀ (m : Nat) (s : Int → Bool), 0 < m → (∀ p : Int, p < -(m : Int) → s p = false) →
    s (-(m : Int)) = true → ¬ ∀ k, L (fun _ => false) s (P * k) (-1) = true

/-- **`QP 2` is `Rule30PeriodTwo.Q01`**, the staged form of `Q01`. -/
theorem QP_two_iff_staged : QP 2 ↔ Rule30PeriodTwo.Q01 := Iff.rfl

/-- **`QP 2` is `Q01`** (`Rule30ZeroBoundary.Q01_iff_staged`). -/
theorem QP_two_iff_Q01 : QP 2 ↔ Rule30ZeroBoundary.Q01 :=
  QP_two_iff_staged.trans Rule30ZeroBoundary.Q01_iff_staged.symm

/-- **`QP 3` is `Q001`** (`Rule30EtherThree.Q001`), the kit's statement for the word `001`. -/
theorem QP_three_iff_Q001 : QP 3 ↔ Rule30EtherThree.Q001 := Iff.rfl

/-- **The reduction.** For every `P ≥ 2`, `QP P` excludes the repeating word `0^(P-1) 1` as a
tail of the center column, whatever the transient. -/
theorem not_eventually_oneBlack_of_QP {P : Nat} (hP : 2 ≤ P) (hQ : QP P) :
    ¬ ∃ T, ∀ t, T ≤ t → center t = decide ((t - T) % P = P - 1) := by
  rintro ⟨T, hT⟩
  let T' := T + (P - 1) + P
  have hfun : (fun k => center (T' + k) && center (T' + k + 1)) = fun _ => false := by
    funext k
    rw [hT (T' + k) (by omega), hT (T' + k + 1) (by omega)]
    have hm := Nat.mod_lt (T' + k - T) (by omega : 0 < P)
    by_cases h : (T' + k - T) % P = P - 1
    · have h2 : (T' + k + 1 - T) % P = 0 := by
        rw [show T' + k + 1 - T = (T' + k - T) + 1 by omega, Nat.add_mod, h,
          Nat.mod_eq_of_lt (show 1 < P by omega)]
        rw [show P - 1 + 1 = P by omega, Nat.mod_self]
      rw [h2]; simp; omega
    · simp [h]
  have hblack : ∀ k, (T' + P * k - T) % P = P - 1 := by
    intro k
    rw [show T' + P * k - T = (P - 1) + P * (k + 1) by
      simp only [T']; rw [Nat.mul_succ]; omega]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  refine hQ T' (fun p => cell T' p) (by omega) (fun p hp => cell_eq_false_of_lt T' p hp)
    (cell_left_edge T') (fun k => ?_)
  have e := cell_eq_L_effective T' (P * k) (-1) (by omega)
  rw [hfun] at e
  rw [e]
  have c0 : cell (T' + P * k) 0 = true := by
    have := hT (T' + P * k) (by omega)
    rw [show center (T' + P * k) = cell (T' + P * k) 0 from rfl] at this
    rw [this, hblack k]; simp
  have c1 : cell (T' + P * k + 1) 0 = false := by
    have := hT (T' + P * k + 1) (by omega)
    rw [show center (T' + P * k + 1) = cell (T' + P * k + 1) 0 from rfl] at this
    rw [this]
    have h2 : (T' + P * k + 1 - T) % P = 0 := by
      rw [show T' + P * k + 1 - T = (T' + P * k - T) + 1 by omega, Nat.add_mod, hblack k,
        Nat.mod_eq_of_lt (show 1 < P by omega), show P - 1 + 1 = P by omega, Nat.mod_self]
    rw [h2]; simp; omega
  have := cell_left (T' + P * k) 0
  rw [show (0 : Int) - 1 = -1 by rfl, show (0 : Int) + 1 = 1 by rfl, c0, c1] at this
  rw [this]; rfl

/-- The word `0^(P-1) 1`. -/
def oneBlack (P : Nat) : List Bool := List.replicate (P - 1) false ++ [true]

theorem oneBlack_length {P : Nat} (hP : 1 ≤ P) : (oneBlack P).length = P := by
  simp only [oneBlack, List.length_append, List.length_replicate, List.length_singleton]
  omega

theorem oneBlack_getD {P i : Nat} (hP : 1 ≤ P) (hi : i < P) :
    (oneBlack P).getD i false = decide (i = P - 1) := by
  unfold oneBlack
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < P - 1
  · rw [List.getElem?_append_left (by simp only [List.length_replicate]; exact h),
      List.getElem?_replicate_of_lt h]
    simp only [Option.getD_some]
    exact (decide_eq_false (by omega)).symm
  · rw [List.getElem?_append_right (by simp only [List.length_replicate]; omega)]
    simp only [List.length_replicate, show i - (P - 1) = 0 by omega]
    simp only [List.getElem?_cons_zero, Option.getD_some]
    exact (decide_eq_true (by omega)).symm

/-- **The reduction, as an eventual word.** For every `P ≥ 2`, `QP P` excludes
`Rule30StripCertificates.EventuallyWord (oneBlack P)`. -/
theorem not_eventuallyWord_oneBlack_of_QP {P : Nat} (hP : 2 ≤ P) (hQ : QP P) :
    ¬ Rule30StripCertificates.EventuallyWord (oneBlack P) := by
  rintro ⟨T, hT⟩
  apply not_eventually_oneBlack_of_QP hP hQ
  refine ⟨T, fun t ht => ?_⟩
  rw [show center t = cell t 0 from rfl, hT t ht, oneBlack_length (by omega),
    oneBlack_getD (by omega) (Nat.mod_lt _ (by omega))]

/-! ## `QP P` for the zero-boundary left half -/

/-- **`QP P` in zero-boundary form**: no finitely supported start keeps depth `1` black at every
`P`-th step. For `P = 2` this is `Rule30ZeroBoundary.Q01_iff_staged`. -/
theorem QP_iff_zrow (P : Nat) :
    QP P ↔ ∀ L : Nat → Bool, FinSupp L → ¬ ∀ s, zrow L (P * s) 1 = true := by
  constructor
  · intro hS L ⟨W, hW⟩ hX
    have h1 : L 1 = true := by
      have h0 := hX 0
      rwa [Nat.mul_zero, zrow_zero_of_pos L (Nat.le_refl 1)] at h0
    obtain ⟨m, hm, hedge, hfin⟩ := last_black h1 W hW
    let s : Int → Bool := fun p => if p < 0 then L (-p).toNat else false
    have hsL : ∀ k : Nat, 1 ≤ k → s (-(k : Int)) = L k := by
      intro k hk
      show (if -(k : Int) < 0 then L (-(-(k : Int))).toNat else false) = L k
      rw [ite_eq_left (by omega), show (-(-(k : Int))).toNat = k by omega]
    refine hS m s (by omega) (fun p hp => ?_) ?_ fun k => ?_
    · show (if p < 0 then L (-p).toNat else false) = false
      rw [ite_eq_left (by omega)]; exact hfin _ (by omega)
    · rw [hsL m hm]; exact hedge
    · rw [show (-1 : Int) = -((1 : Nat) : Int) by rfl, L_eq_zrow s (P * k) 1 (Nat.le_refl 1),
        zrow_congr (L' := L) hsL]
      exact hX k
  · intro hQ m s hm hs0 _ hc
    refine hQ (fun k => s (-(k : Int))) ⟨m, fun k hk => hs0 _ (by omega)⟩ fun k => ?_
    rw [← L_eq_zrow s (P * k) 1 (Nat.le_refl 1)]
    exact hc k

/-- **`QP P` at any phase**: `QP P` holds iff no finitely supported start keeps depth `1` black at
the steps `T, T + P, T + 2 P, …` for some `T`. For `P = 2` this is
`Rule30ZeroBoundary.Q01_iff_any_phase`. -/
theorem QP_iff_any_phase (P : Nat) :
    QP P ↔ ∀ (L : Nat → Bool) (T : Nat), FinSupp L → ¬ ∀ s, zrow L (T + P * s) 1 = true := by
  rw [QP_iff_zrow]
  constructor
  · rintro hQ L T ⟨W, hW⟩ hc
    refine hQ (zrow L T) ⟨W + T, fun k hk => zrow_fin hW T k hk⟩ fun s => ?_
    rw [← zrow_shift]; exact hc s
  · intro h L hfin hX
    exact h L 0 hfin fun s => by rw [Nat.zero_add]; exact hX s

/-- **`QP 4` implies `C3 w0001`**, the left-only statement with which
`Rule30PeriodFourSkeleton.not_eventually_0001_of_C3` excludes `0001`: a finitely supported start
whose column `-1` eventually fits the pattern of `0001` is black at the phase `3` steps. -/
theorem C3_0001_of_QP_four (hQ : QP 4) : Rule30PeriodFourSkeleton.C3 Rule30Ether.w0001 := by
  rintro s ⟨M, hM⟩ ⟨K, hK⟩
  have hdrv : (fun k => Rule30Ether.wordAt
      (Rule30PeriodFourSkeleton.effWord Rule30Ether.w0001) k) = fun _ => false := by
    funext k
    rw [Rule30PeriodFourSkeleton.effWord_0001]
    unfold Rule30Ether.wordAt
    have h4 : k % 4 < 4 := Nat.mod_lt _ (by decide)
    have : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
    rcases this with h | h | h | h <;> rw [h] <;> rfl
  refine (QP_iff_any_phase 4).1 hQ (fun k => s (-(k : Int))) (4 * K + 3)
    ⟨M, fun k hk => hM _ (by omega)⟩ fun j => ?_
  have hk := hK (4 * K + 3 + 4 * j) (by omega)
  rw [hdrv, Rule30PeriodFourSkeleton.fits_0001,
    show (4 * K + 3 + 4 * j) % 4 = 3 by omega] at hk
  simp only [show (3 : Nat) ≠ 0 by decide, show (3 : Nat) ≠ 2 by decide, ite_false, ite_true,
    beq_iff_eq] at hk
  rw [← L_eq_zrow s (4 * K + 3 + 4 * j) 1 (Nat.le_refl 1)]
  exact hk

/-! ## The checker, for every period `P`

### Indexing the free levels

Level `k` of the reconstruction is forced black when `k % P = 0`. The other levels below the
width are free; `fidx P k` numbers them `0, 1, 2, …` and `lev P` is the inverse numbering. -/

/-- The number of the free level `k` (`k % P ≠ 0`). -/
def fidx (P k : Nat) : Nat := Nat.sub (Nat.sub k (Nat.div k P)) 1

/-- The level of the free bit number `s`. -/
def lev (P s : Nat) : Nat := s + s / (P - 1) + 1

/-- The number of free levels `k` with `k + 1 ≤ W`. -/
def nfree (W P : Nat) : Nat := (W - 1) - (W - 1) / P

theorem lev_fidx {P t : Nat} (hP : 2 ≤ P) (ht : t % P ≠ 0) : lev P (fidx P t) = t := by
  have hd := Nat.div_add_mod t P
  have hm := Nat.mod_lt t (show 0 < P by omega)
  obtain ⟨Q, rfl⟩ : ∃ Q, P = Q + 1 := ⟨P - 1, by omega⟩
  generalize ha : t / (Q + 1) = a at hd
  generalize hr : t % (Q + 1) = r at hd hm ht
  have hQa : (Q + 1) * a = Q * a + a := by rw [Nat.succ_mul]
  have hf : fidx (Q + 1) t = (r - 1) + a * Q := by
    unfold fidx
    show t - t / (Q + 1) - 1 = _
    rw [ha, Nat.mul_comm a Q]
    omega
  unfold lev
  rw [hf, show Q + 1 - 1 = Q by omega, Nat.add_mul_div_right _ _ (by omega : 0 < Q),
    Nat.div_eq_of_lt (by omega), Nat.mul_comm a Q]
  omega

theorem fidx_lt {W P t : Nat} (hP : 2 ≤ P) (ht : t % P ≠ 0) (hW : t + 1 ≤ W) :
    fidx P t < nfree W P := by
  have hd := Nat.div_add_mod t P
  have hd' := Nat.div_add_mod (W - 1) P
  have hm := Nat.mod_lt t (show 0 < P by omega)
  have hm' := Nat.mod_lt (W - 1) (show 0 < P by omega)
  have hle : t / P ≤ (W - 1) / P := Nat.div_le_div_right (by omega)
  obtain ⟨d, hdd⟩ : ∃ d, (W - 1) / P = t / P + d := ⟨(W - 1) / P - t / P, by omega⟩
  rw [hdd, Nat.mul_add] at hd'
  have hPd : d ≤ P * d := Nat.le_mul_of_pos_left d (by omega)
  have key : d = 0 ∨ d + (P - 1) ≤ P * d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · exact Or.inl h
    · right
      obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
      rw [Nat.mul_succ]
      have : e ≤ P * e := Nat.le_mul_of_pos_left e (by omega)
      omega
  unfold fidx nfree
  show t - t / P - 1 < W - 1 - (W - 1) / P
  rw [hdd]
  have htp : t / P ≤ P * (t / P) := Nat.le_mul_of_pos_left _ (by omega)
  rcases key with h | h
  · subst h; omega
  · omega

/-! ### The kernel computation -/

/-- One level. `k % P = 0`: `y k = 1`. Otherwise, with `k + 1 ≤ W`: free bit `fidx P k`.
Otherwise: the bit that makes `L (k + 1) = 0`. Written with the recursor and raw `Nat`
primitives, as `Rule30ZeroBoundaryLanes.stepR`, so that the kernel evaluates it quickly. -/
noncomputable def stepP (W P n c ALL : Nat) (pats : List Nat) (k : Nat) (R Rm : List Nat) :
    List Nat × Nat :=
  Bool.rec
    (Bool.rec
      (let r := scanN 0 R (0 :: Rm); (r.2 :: mapX r.2 r.1, r.2))
      (let y := yFree n c ALL pats (fidx P k); let r := scanN y R (0 :: Rm); (y :: r.1, r.2))
      (Nat.ble (Nat.add k 1) W))
    (let r := scanN ALL R (0 :: Rm); (ALL :: r.1, r.2))
    (Nat.beq (Nat.mod k P) 0)

/-- Run `fuel` levels; a lane dies when some `L (k + 1)` with `W < k + 1` is black at a level
`k` with `k % P = 0`. -/
noncomputable def runP (W P n c ALL : Nat) (pats : List Nat) (fuel : Nat) :
    Nat → List Nat → List Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → List Nat → List Nat → Nat → Bool)
    (fun _ _ _ alive => Nat.beq alive 0)
    (fun _ ih k R Rm alive =>
      let st := stepP W P n c ALL pats k R Rm
      ih (Nat.add k 1) st.1 R
        (Bool.rec alive (Nat.land alive (Nat.xor ALL st.2))
          (band (Nat.beq (Nat.mod k P) 0) (Nat.blt W (Nat.add k 1)))))
    fuel

/-- The check for chunk `c`: `2 ^ n` lanes, `K` levels, period `P`, width `W`. -/
noncomputable def checkP (W P K n c : Nat) : Bool :=
  runP W P n c (2 ^ 2 ^ n - 1) ((List.range n).map (pat n)) K 0 [] [] (2 ^ 2 ^ n - 1)

theorem runP_zero (W P n c ALL : Nat) (pats : List Nat) (k : Nat) (R Rm : List Nat)
    (alive : Nat) : runP W P n c ALL pats 0 k R Rm alive = Nat.beq alive 0 := rfl

theorem runP_succ (W P n c ALL : Nat) (pats : List Nat) (f k : Nat) (R Rm : List Nat)
    (alive : Nat) :
    runP W P n c ALL pats (f + 1) k R Rm alive =
      runP W P n c ALL pats f (k + 1) (stepP W P n c ALL pats k R Rm).1 R
        (Bool.rec alive (alive &&& (ALL ^^^ (stepP W P n c ALL pats k R Rm).2))
          (band (Nat.beq (k % P) 0) (Nat.blt W (k + 1)))) := rfl

theorem stepP_black (W P n c ALL : Nat) (pats : List Nat) (k : Nat) (R Rm : List Nat)
    (h : k % P = 0) :
    stepP W P n c ALL pats k R Rm =
      (ALL :: (scanN ALL R (0 :: Rm)).1, (scanN ALL R (0 :: Rm)).2) := by
  have hb : Nat.beq (Nat.mod k P) 0 = true := by rw [Nat.beq_eq]; exact h
  unfold stepP; rw [hb]

theorem stepP_free (W P n c ALL : Nat) (pats : List Nat) (k : Nat) (R Rm : List Nat)
    (h : k % P ≠ 0) (hW : k + 1 ≤ W) :
    stepP W P n c ALL pats k R Rm =
      (yFree n c ALL pats (fidx P k) :: (scanN (yFree n c ALL pats (fidx P k)) R (0 :: Rm)).1,
        (scanN (yFree n c ALL pats (fidx P k)) R (0 :: Rm)).2) := by
  have hb : Nat.beq (Nat.mod k P) 0 = false := by
    cases hq : Nat.beq (Nat.mod k P) 0
    · rfl
    · rw [Nat.beq_eq] at hq; exact absurd hq h
  have hb2 : Nat.ble (Nat.add k 1) W = true := by rw [Nat.ble_eq]; exact hW
  unfold stepP; rw [hb, hb2]

theorem stepP_forced (W P n c ALL : Nat) (pats : List Nat) (k : Nat) (R Rm : List Nat)
    (h : k % P ≠ 0) (hW : W < k + 1) :
    stepP W P n c ALL pats k R Rm =
      ((scanN 0 R (0 :: Rm)).2 :: mapX (scanN 0 R (0 :: Rm)).2 (scanN 0 R (0 :: Rm)).1,
        (scanN 0 R (0 :: Rm)).2) := by
  have hb : Nat.beq (Nat.mod k P) 0 = false := by
    cases hq : Nat.beq (Nat.mod k P) 0
    · rfl
    · rw [Nat.beq_eq] at hq; exact absurd hq h
  have hb2 : Nat.ble (Nat.add k 1) W = false := by
    cases hq : Nat.ble (Nat.add k 1) W
    · rfl
    · rw [Nat.ble_eq] at hq; exact absurd hq (by show ¬ k + 1 ≤ W; omega)
  unfold stepP; rw [hb, hb2]

/-! ### Soundness -/

/-- **Soundness of `runP` for one lane.** Let `y` be the boundary column of a start that is white
beyond depth `W`, has the free bits of lane `p` and is black at the levels `t` with `t % P = 0`
that the run visits. A run from level `k`, with the anti-diagonals `R` and `Rm` of `y` and lane `p`
alive, cannot report that every lane dies. -/
theorem runP_sound (W P n c ALL : Nat) (pats : List Nat) (y : Nat → Bool) (p : Nat)
    (hALL : ALL.testBit p = true)
    (hfree : ∀ t, t % P ≠ 0 → t + 1 ≤ W → (yFree n c ALL pats (fidx P t)).testBit p = y t)
    (hwid : ∀ d, W < d → recon y d 0 = false) :
    ∀ fuel k R Rm alive,
      runP W P n c ALL pats fuel k R Rm alive = true →
      (∀ t, k ≤ t → t < k + fuel → t % P = 0 → y t = true) →
      R.map (fun v => v.testBit p) = AD y k 0 k →
      Rm.map (fun v => v.testBit p) = AD y (k - 1) 0 (k - 1) →
      alive.testBit p = true → False := by
  intro fuel
  induction fuel with
  | zero =>
    intro k R Rm alive hrun _ _ _ halive
    rw [runP_zero, Nat.beq_eq] at hrun
    rw [hrun, Nat.zero_testBit] at halive
    exact absurd halive (by decide)
  | succ fuel ih =>
    intro k R Rm alive hrun hblk hR hRm halive
    rw [runP_succ] at hrun
    have hblk' : ∀ t, k + 1 ≤ t → t < k + 1 + fuel → t % P = 0 → y t = true :=
      fun t h1 h2 h3 => hblk t (by omega) (by omega) h3
    have hRm' : R.map (fun v => v.testBit p) = AD y (k + 1 - 1) 0 (k + 1 - 1) := by
      rw [show k + 1 - 1 = k by omega]; exact hR
    by_cases hk : k % P = 0
    · -- black level
      rw [stepP_black W P n c ALL pats k R Rm hk] at hrun
      have hY : ALL.testBit p = y k := by rw [hALL, hblk k (by omega) (by omega) hk]
      have hl := level y p k R Rm ALL hR hRm hY
      refine ih (k + 1) _ R _ hrun hblk' hl.1 hRm' ?_
      have hb : Nat.beq (k % P) 0 = true := by rw [Nat.beq_eq]; exact hk
      rw [hb]
      by_cases hW : W < k + 1
      · have hb2 : Nat.blt W (k + 1) = true := by rw [Nat.blt_eq]; exact hW
        rw [hb2]
        show (alive &&& (ALL ^^^ (scanN ALL R (0 :: Rm)).2)).testBit p = true
        rw [Nat.testBit_and, Nat.testBit_xor, hl.2, hwid (k + 1) hW, hALL, halive]
        rfl
      · have hb2 : Nat.blt W (k + 1) = false := by
          cases hq : Nat.blt W (k + 1)
          · rfl
          · rw [Nat.blt_eq] at hq; exact absurd hq hW
        rw [hb2]
        exact halive
    · have hb : Nat.beq (k % P) 0 = false := by
        cases hq : Nat.beq (k % P) 0
        · rfl
        · rw [Nat.beq_eq] at hq; exact absurd hq hk
      by_cases hW : k + 1 ≤ W
      · -- free bit
        rw [stepP_free W P n c ALL pats k R Rm hk hW] at hrun
        have hl := level y p k R Rm _ hR hRm (hfree k hk hW)
        refine ih (k + 1) _ R _ hrun hblk' hl.1 hRm' ?_
        rw [hb]
        exact halive
      · -- forced bit
        rw [stepP_forced W P n c ALL pats k R Rm hk (by omega)] at hrun
        let Y' : Nat := if y k then 2 ^ p else 0
        have hY' : Y'.testBit p = y k := by
          show (if y k then 2 ^ p else 0).testBit p = y k
          cases y k
          · simp
          · simp
        have hl' := level y p k R Rm Y' hR hRm hY'
        rw [hwid (k + 1) (by omega), scanN_lin, Nat.testBit_xor, hY'] at hl'
        have hT : (scanN 0 R (0 :: Rm)).2.testBit p = y k := by
          have h2 := hl'.2
          revert h2
          cases y k <;> cases (scanN 0 R (0 :: Rm)).2.testBit p <;> simp
        have hl := level y p k R Rm (scanN 0 R (0 :: Rm)).2 hR hRm hT
        rw [scanN_lin R (0 :: Rm) (scanN 0 R (0 :: Rm)).2] at hl
        refine ih (k + 1) _ R _ hrun hblk' hl.1 hRm' ?_
        rw [hb]
        exact halive

/-- **Soundness of the chunked check.** If every chunk passes, every start supported at depths
`≤ W` has a white cell at depth `1` at some step `t < K` with `t % P = 0`. -/
theorem qP_of_checks (W P K n : Nat) (hP : 2 ≤ P) (hn : n ≤ nfree W P)
    (hc : ∀ c, c < 2 ^ (nfree W P - n) → checkP W P K n c = true)
    (x : Nat → Bool) (hx : ∀ k, W < k → x k = false) :
    ∃ t, t < K ∧ t % P = 0 ∧ zrow x t 1 = false := by
  refine Classical.byContradiction fun hne => ?_
  have hall : ∀ t, t < K → t % P = 0 → zrow x t 1 = true := by
    intro t ht he
    cases hz : zrow x t 1
    · exact absurd ⟨t, ht, he, hz⟩ hne
    · rfl
  let y : Nat → Bool := fun t => zrow x t 1
  let p := pack (fun s => y (lev P s)) n
  let c := pack (fun s => y (lev P (n + s))) (nfree W P - n)
  have hcheck := hc c (pack_lt _ _)
  have hp : p < 2 ^ n := pack_lt _ _
  have hALL : (2 ^ 2 ^ n - 1).testBit p = true := by
    rw [Nat.testBit_two_pow_sub_one]; simpa using hp
  refine runP_sound W P n c (2 ^ 2 ^ n - 1) ((List.range n).map (pat n)) y p hALL ?_ ?_ K 0 [] []
    (2 ^ 2 ^ n - 1) hcheck (fun t _ ht he => hall t (by omega) he) rfl rfl hALL
  · intro t ht htW
    have hlev := lev_fidx hP ht
    have hlt := fidx_lt hP ht htW
    unfold yFree
    by_cases hs : fidx P t < n
    · rw [ite_eq_left hs, pats_getD n _ hs, pat_spec n _ p hs hp, testBit_pack]
      simp [hs, hlev, y]
    · rw [ite_eq_right hs, testBit_pack]
      have hsn : fidx P t - n < nfree W P - n := by omega
      have hyy : y (lev P (n + (fidx P t - n))) = y t := by
        rw [show n + (fidx P t - n) = fidx P t by omega, hlev]
      simp only [hsn, decide_true, Bool.true_and, hyy]
      cases y t
      · simp
      · simpa using hALL
  · intro d hd
    have e := history_eq_recon x d 0
    rw [zrow_zero_of_pos x (by omega), hx d hd] at e
    exact e.symm

/-! ### Combining chunks -/

/-- The chunks `lo, …, lo + cnt - 1` pass. -/
def ChunksOKP (W P K n lo cnt : Nat) : Prop :=
  ∀ c, lo ≤ c → c < lo + cnt → checkP W P K n c = true

theorem chunksOKP_one {W P K n c : Nat} (h : checkP W P K n c = true) : ChunksOKP W P K n c 1 :=
  fun c' h1 h2 => by rw [show c' = c by omega]; exact h

theorem chunksOKP_append {W P K n lo a b : Nat} (h1 : ChunksOKP W P K n lo a)
    (h2 : ChunksOKP W P K n (lo + a) b) : ChunksOKP W P K n lo (a + b) := fun c hc1 hc2 => by
  rcases Nat.lt_or_ge c (lo + a) with h | h
  · exact h1 c hc1 h
  · exact h2 c h (by omega)

/-- **Soundness from a combined range certificate.** If the chunks `0, …, 2 ^ (nfree W P - n) - 1`
pass, every start supported at depths `≤ W` has a white cell at depth `1` at some step `t < K`
with `t % P = 0`. -/
theorem qP_of_chunks (W P K n : Nat) (hP : 2 ≤ P) (hn : n ≤ nfree W P)
    (h : ChunksOKP W P K n 0 (2 ^ (nfree W P - n)))
    (x : Nat → Bool) (hx : ∀ k, W < k → x k = false) :
    ∃ t, t < K ∧ t % P = 0 ∧ zrow x t 1 = false :=
  qP_of_checks W P K n hP hn (fun c hc => h c (Nat.zero_le c) (by omega)) x hx

/-- **The check for `Rule30DrivenLeft.L`.** If the chunks pass, every start of the zero-driven left
half supported on the positions `-W, …, -1` has a white cell in column `-1` at some step
`P * k < K`. -/
theorem bounded_of_chunks (W P K n : Nat) (hP : 2 ≤ P) (hn : n ≤ nfree W P)
    (h : ChunksOKP W P K n 0 (2 ^ (nfree W P - n)))
    (s : Int → Bool) (hs : ∀ p : Int, p < -(W : Int) → s p = false) :
    ∃ k, P * k < K ∧ L (fun _ => false) s (P * k) (-1) = false := by
  obtain ⟨t, htK, htP, hz⟩ := qP_of_chunks W P K n hP hn h (fun k => s (-(k : Int)))
    (fun k hk => hs _ (by omega))
  have ht : P * (t / P) = t := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero htP)
  refine ⟨t / P, by rw [ht]; exact htK, ?_⟩
  rw [ht]
  have e := L_eq_zrow s t 1 (Nat.le_refl 1)
  rw [show (-((1 : Nat) : Int)) = -1 by rfl] at e
  rw [e]; exact hz

/-- **The checker proves `QP P` up to width `W`.** If the chunks pass, no start whose leftmost
black cell is at depth `m ≤ W` keeps column `-1` black at every `P`-th step: this is `QP P`
restricted to `m ≤ W`. -/
theorem QP_restricted_of_chunks {W P K n : Nat} (hP : 2 ≤ P) (hn : n ≤ nfree W P)
    (h : ChunksOKP W P K n 0 (2 ^ (nfree W P - n)))
    (m : Nat) (hm : m ≤ W) (s : Int → Bool) (hs : ∀ p : Int, p < -(m : Int) → s p = false) :
    ¬ ∀ k, L (fun _ => false) s (P * k) (-1) = true := by
  intro hall
  obtain ⟨k, _, hk⟩ := bounded_of_chunks W P K n hP hn h s (fun p hp => hs p (by omega))
  rw [hall k] at hk
  exact absurd hk (by decide)

end Rule30ZeroBoundaryPeriodLanes
end Ruliology.CellularAutomata
