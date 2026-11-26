module

public import Ruliology.CellularAutomata.Rule30ZeroCoastBridge

/-!
# The gate trap at every width: a ladder of reductions to `CQ01Empty`

`Rule30GateTrap` traps the window of the columns `1..16` of a right half driven by the
alternating column, and `Rule30GateTrapLift` widens it to eighteen columns. Here the window has
any width `W`. A *lift path of width `W`* (`LiftPath`) is a sequence of windows of `W` cells whose
first window begins, in its first sixteen cells, with a window of `trap`, and which follows the
double step `step2` with arbitrary exterior inputs.

* A lift path of width `W'` cut to its first `W` cells, `16 ≤ W ≤ W'`, is a lift path of width `W`
  (`liftPath_take`). Its first sixteen cells stay in the trap (`LiftPath.take16_mem`), so a
  sequence read by a lift path keeps the gaps `3` and `5` of `Rule30GateTrap` (`ReadsLift.gapOK`).
* A right half whose window enters the trap at an odd time `2 s0 + 1` reads `u R` from `s0` on
  along its own windows of `W` columns (`readsLift_u`).

The reductions:

* `Q01GapLift W` (**open**): no finitely supported constrained start of the zero-boundary left
  half has free bits whose complement, from some step on, is read by a lift path of width `W`.
  `Rule30GateTrap.Q01Gap` gives it for every `W ≥ 16` (`Q01GapLift_of_Q01Gap`), and it weakens
  as `W` grows (`Q01GapLift_mono`). For `W ≥ 16` it gives `¬ FinSupp (Psi R)` for every right half
  whose window enters the trap (`not_finSupp_Psi_of_Q01GapLift`), hence `CQ01Empty`
  (`CQ01Empty_of_Q01GapLift`).
* `Q01GapLiftCore W` (**open**): the same with `Rule30GateTrapLift.TwoCoreOK` required as well.
  It follows from `Q01GapLift W` and from `Rule30GateTrapLift.Q01TwoCore`, and for `W ≥ 16` it
  gives `CQ01Empty` (`CQ01Empty_of_Q01GapLiftCore`). The anchor is twenty steps after entry:
  `u ∅` reads `5, 3, 3` from step `146`, so for `R = ∅` the core words are used from step `156`
  (time `313`) on, where `Rule30GateTrapWords.TwoWordsOK_of_entry` and
  `Rule30GateTrapLift.no_3535353_of_entry` apply.
* `MassDivergesLift W` (**open**): for every `M` there is `H` such that no natural number `y`
  with `popcount y ≤ M` has a zero-coast trace (`Rule30ZeroBoundary.IntegerForm.F`) that is
  black at the odd times `t < H` and, at each even time `2 k < H`, the complement of the first
  cell of the `k`-th window of one lift path of width `W` (`AcceptLift`). It gives `Q01GapLift W`
  (`Q01GapLift_of_massDivergesLift`), hence `CQ01Empty` for `W ≥ 16`
  (`CQ01Empty_of_massDivergesLift`), and it weakens as `W` grows (`MassDivergesLift_mono`).

So `Q01Gap → Q01GapLift 16 → Q01GapLift W → Q01GapLiftCore W → CQ01Empty` for `16 ≤ W`, and
`MassDivergesLift W → Q01GapLift W`. Nothing here decides `Q01Gap`, `Q01GapLift`,
`MassDivergesLift`, `CQ01Empty` or Problem 1.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30GateTrapLadder

open Rule30StripCertificates Rule30Ether Rule30PeriodTwoCoupled Rule30GateTrap Rule30ZeroBoundary
open Rule30ZeroBoundary.IntegerForm

/-! ## Lists -/

theorem lin3_length : ∀ l : List Bool, (lin3 l).length = l.length - 2
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | a :: b :: c :: rest => by
    show (xor a (b || c) :: lin3 (b :: c :: rest)).length = _
    rw [List.length_cons, lin3_length (b :: c :: rest)]
    simp

theorem lin3_take : ∀ (l : List Bool) (m : Nat), (lin3 l).take m = lin3 (l.take (m + 2))
  | [], m => by cases m <;> rfl
  | [_], m => by cases m <;> rfl
  | [_, _], m => by cases m <;> rfl
  | _ :: _ :: _ :: _, 0 => rfl
  | a :: b :: c :: rest, m + 1 => by
    show xor a (b || c) :: (lin3 (b :: c :: rest)).take m = lin3 (a :: b :: c :: rest.take m)
    rw [lin3_take (b :: c :: rest) m]
    rfl

theorem step2_length (w : List Bool) (x1 x2 : Bool) : (step2 w x1 x2).length = w.length := by
  unfold step2
  rw [lin3_length, List.length_cons, List.length_append, lin3_length]
  simp

theorem take_succ_getD : ∀ (l : List Bool) (m : Nat), m < l.length →
    l.take (m + 1) = l.take m ++ [l.getD m false]
  | [], _, h => by simp at h
  | _ :: _, 0, _ => rfl
  | a :: l, m + 1, h => by
    have h' : m < l.length := by simp at h; omega
    show a :: l.take (m + 1) = a :: l.take m ++ [(a :: l).getD (m + 1) false]
    rw [take_succ_getD l m h', List.getD_cons_succ]
    rfl

/-- The first `m` cells after a double step come from the first `m` cells before it, with the
cell `m + 1` and the intermediate cell `m + 1` as the exterior inputs. -/
theorem step2_take (w : List Bool) (x1 x2 : Bool) (m : Nat) (hm : m < w.length) :
    (step2 w x1 x2).take m =
      step2 (w.take m) (w.getD m false) ((lin3 (false :: (w ++ [x1]))).getD m false) := by
  have hA : (lin3 (false :: (w ++ [x1]))).length = w.length := by
    rw [lin3_length]; simp
  unfold step2
  rw [lin3_take]
  congr 1
  show true :: (lin3 (false :: (w ++ [x1])) ++ [x2]).take (m + 1) = _
  congr 1
  rw [List.take_append_of_le_length (by omega), take_succ_getD _ m (by omega)]
  congr 1
  rw [lin3_take]
  show lin3 (false :: (w ++ [x1]).take (m + 1)) = _
  rw [List.take_append_of_le_length (by omega), take_succ_getD _ m hm]

theorem step2_take_exists (v : List Bool) (x1 x2 : Bool) (m : Nat) (hm : m ≤ v.length) :
    ∃ y1 y2, (step2 v x1 x2).take m = step2 (v.take m) y1 y2 := by
  rcases Nat.lt_or_eq_of_le hm with h | h
  · exact ⟨_, _, step2_take v x1 x2 m h⟩
  · refine ⟨x1, x2, ?_⟩
    rw [List.take_of_length_le (by rw [step2_length]; omega), List.take_of_length_le (by omega)]

theorem seg_take : ∀ (n m : Nat) (f : Nat → Bool), m ≤ n → (seg f n).take m = seg f m
  | _, 0, _, _ => by simp [seg]
  | 0, _ + 1, _, h => by omega
  | n + 1, m + 1, f, h => by
    show f 0 :: (seg (fun i => f (i + 1)) n).take m = f 0 :: seg (fun i => f (i + 1)) m
    rw [seg_take n m _ (by omega)]

theorem headD_take (l : List Bool) (m : Nat) (hm : 1 ≤ m) :
    (l.take m).headD false = l.headD false := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  cases l <;> rfl

/-! ## Lift paths -/

/-- A lift path of width `W`: windows of `W` cells, the first one beginning with a window of
`trap`, each obtained from the previous one by the double step with some exterior inputs. -/
def LiftPath (W : Nat) (ws : Nat → List Bool) : Prop :=
  (ws 0).length = W ∧ (ws 0).take 16 ∈ trap ∧ ∀ k, ∃ x1 x2, ws (k + 1) = step2 (ws k) x1 x2

theorem LiftPath.length {W : Nat} {ws : Nat → List Bool} (h : LiftPath W ws) :
    ∀ k, (ws k).length = W
  | 0 => h.1
  | k + 1 => by
    obtain ⟨x1, x2, e⟩ := h.2.2 k
    rw [e, step2_length]
    exact LiftPath.length h k

/-- The first sixteen cells of a lift path stay in the trap. -/
theorem LiftPath.take16_mem {W : Nat} {ws : Nat → List Bool} (h : LiftPath W ws) (hW : 16 ≤ W) :
    ∀ k, (ws k).take 16 ∈ trap
  | 0 => h.2.1
  | k + 1 => by
    obtain ⟨x1, x2, e⟩ := h.2.2 k
    obtain ⟨y1, y2, e'⟩ := step2_take_exists (ws k) x1 x2 16 (by rw [h.length k]; exact hW)
    have hm := LiftPath.take16_mem h hW k
    have hl : (step2 ((ws k).take 16) y1 y2).length = 16 := by
      rw [step2_length, List.length_take, h.length k]; omega
    rw [e, e']
    exact mem_of_inM hl (allSucc_spec (List.all_eq_true.1 trapClosed_ok _ hm) y1 y2)

/-- A lift path of width `W'` cut to its first `W` cells is a lift path of width `W`. -/
theorem liftPath_take {W W' : Nat} (hW : 16 ≤ W) (hWW : W ≤ W') {ws : Nat → List Bool}
    (h : LiftPath W' ws) : LiftPath W (fun k => (ws k).take W) := by
  refine ⟨?_, ?_, fun k => ?_⟩
  · show ((ws 0).take W).length = W
    rw [List.length_take, h.1]; omega
  · show ((ws 0).take W).take 16 ∈ trap
    rw [List.take_take, Nat.min_eq_left hW]
    exact h.2.1
  · obtain ⟨x1, x2, e⟩ := h.2.2 k
    obtain ⟨y1, y2, e'⟩ := step2_take_exists (ws k) x1 x2 W (by rw [h.length k]; exact hWW)
    exact ⟨y1, y2, by show (ws (k + 1)).take W = _; rw [e, e']⟩

theorem LiftPath.next {ws : Nat → List Bool} (hp : LiftPath 16 ws) {L : List (List Bool)}
    {P : List Bool → Bool} (hc : L.all (allSucc P) = true) {k : Nat} (hk : ws k ∈ L) :
    P (ws (k + 1)) = true := by
  obtain ⟨x1, x2, e⟩ := hp.2.2 k
  rw [e]
  exact allSucc_spec (List.all_eq_true.1 hc _ hk) x1 x2

/-- `g` is read from step `s0` on by a lift path of width `W`: the first cell of the `k`-th window
is `g (s0 + k)`. -/
def ReadsLift (W : Nat) (g : Nat → Bool) (s0 : Nat) : Prop :=
  ∃ ws, LiftPath W ws ∧ ∀ k, (ws k).headD false = g (s0 + k)

theorem ReadsLift.take {W W' : Nat} (hW : 16 ≤ W) (hWW : W ≤ W') {g : Nat → Bool} {s0 : Nat}
    (h : ReadsLift W' g s0) : ReadsLift W g s0 := by
  obtain ⟨ws, hp, hh⟩ := h
  exact ⟨_, liftPath_take hW hWW hp, fun k => by
    show ((ws k).take W).headD false = _
    rw [headD_take _ _ (by omega)]; exact hh k⟩

/-- **Gaps along a lift path.** A sequence read by a lift path of width `W ≥ 16` from `s0` on has
each black cell, from `s0` on, followed by the next one at distance `3` or `5`. -/
theorem ReadsLift.gapOK {W : Nat} {g : Nat → Bool} {s0 : Nat} (hW : 16 ≤ W)
    (h : ReadsLift W g s0) : ∀ s, s0 ≤ s → GapOK g s := by
  obtain ⟨ws, hp, hh⟩ := ReadsLift.take (W := 16) (Nat.le_refl _) hW h
  have hlen := hp.length
  have hmem : ∀ k, ws k ∈ trap := fun k => by
    have := hp.take16_mem (Nat.le_refl _) k
    rwa [List.take_of_length_le (Nat.le_of_eq (hlen k))] at this
  intro s hs hg
  obtain ⟨k, rfl⟩ : ∃ k, s = s0 + k := ⟨s - s0, by omega⟩
  have hd : ∀ j, (ws (k + j)).headD false = g (s0 + k + j) := fun j => by
    rw [hh (k + j), Nat.add_assoc]
  -- one double step: white, in `layer1`
  have q1 := List.all_eq_true.1 afterBlack_ok _ (hmem k)
  rw [show (ws k).headD false = true by rw [← Nat.add_zero k, hd 0, Nat.add_zero]; exact hg] at q1
  simp only [Bool.not_true, Bool.false_or] at q1
  obtain ⟨x1, x2, e1⟩ := hp.2.2 k
  have r1 := allSucc_spec q1 x1 x2
  rw [← e1] at r1
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at r1
  have m1 : ws (k + 1) ∈ layer1 := mem_of_inM (hlen _) r1.2
  -- two double steps: white, in `layer2`
  have r2 := hp.next secondStep_ok m1
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at r2
  have m2 : ws (k + 1 + 1) ∈ layer2 := mem_of_inM (hlen _) r2.2
  -- three double steps: black (a gap of `3`), or white and in `layer3`
  have r3 := hp.next thirdStep_ok m2
  have g1 : g (s0 + k + 1) = false := by rw [← hd 1]; exact r1.1
  have g2 : g (s0 + k + 2) = false := by rw [← hd 2]; exact r2.1
  cases h3 : (ws (k + 1 + 1 + 1)).headD false with
  | true =>
    left
    refine ⟨g1, g2, ?_⟩
    rw [← hd 3]; exact h3
  | false =>
    right
    rw [h3, Bool.false_or] at r3
    have m3 : ws (k + 1 + 1 + 1) ∈ layer3 := mem_of_inM (hlen _) r3
    have r4 := hp.next fourthStep_ok m3
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at r4
    have m4 : ws (k + 1 + 1 + 1 + 1) ∈ layer4 := mem_of_inM (hlen _) r4.2
    have r5 := hp.next fifthStep_ok m4
    refine ⟨g1, g2, ?_, ?_, ?_⟩
    · rw [← hd 3]; exact h3
    · rw [← hd 4]; exact r4.1
    · rw [← hd 5]; exact r5

/-! ## The windows of a driven right half -/

/-- The window of `R` of the columns `1..W` at time `t`. -/
def winW (R : Nat → Bool) (W t : Nat) : List Bool := rowOf (drv altCol R) t 0 W

theorem winW_length (R : Nat → Bool) (W t : Nat) : (winW R W t).length = W := length_seg _ _

theorem winW_take16 (R : Nat → Bool) {W : Nat} (hW : 16 ≤ W) (t : Nat) :
    (winW R W t).take 16 = win R t := by
  unfold winW win rowOf
  exact seg_take W 16 _ hW

theorem winW_head (R : Nat → Bool) {W : Nat} (hW : 1 ≤ W) (t : Nat) :
    (winW R W t).headD false = drv altCol R t 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, W = j + 1 := ⟨W - 1, by omega⟩
  exact rowOf_head _ t 0 j

/-- From an odd time, the window of `W` columns two steps later is a double step of the window,
with the two values of column `W + 1` as the exterior inputs. -/
theorem winW_step2 (R : Nat → Bool) (W t : Nat) (ht : t % 2 = 1) :
    ∃ x1 x2, winW R W (t + 2) = step2 (winW R W t) x1 x2 := by
  have h1 := rowOf_succ (drv_isR30 altCol R) t 0 W
  have h2 := rowOf_succ (drv_isR30 altCol R) (t + 1) 0 W
  rw [drv_col0] at h1 h2
  have a1 : altCol t = false := by unfold altCol; simp [ht]
  have a2 : altCol (t + 1) = true := by unfold altCol; simp; omega
  rw [a1] at h1
  rw [a2] at h2
  refine ⟨drv altCol R t (0 + W + 1), drv altCol R (t + 1) (0 + W + 1), ?_⟩
  unfold winW step2
  rw [show t + 2 = t + 1 + 1 by omega, h2, h1]

/-- The windows of `W` columns of a right half, from an odd time at which its window is in the
trap, form a lift path. -/
theorem winW_liftPath (R : Nat → Bool) {W t0 : Nat} (hW : 16 ≤ W) (h0 : t0 % 2 = 1)
    (hw : win R t0 ∈ trap) : LiftPath W (fun k => winW R W (t0 + 2 * k)) := by
  refine ⟨winW_length _ _ _, ?_, fun k => ?_⟩
  · show (winW R W (t0 + 2 * 0)).take 16 ∈ trap
    rw [Nat.mul_zero, Nat.add_zero, winW_take16 R hW]
    exact hw
  · obtain ⟨x1, x2, e⟩ := winW_step2 R W (t0 + 2 * k) (by omega)
    exact ⟨x1, x2, by
      show winW R W (t0 + 2 * (k + 1)) = _
      rw [show t0 + 2 * (k + 1) = t0 + 2 * k + 2 by omega]
      exact e⟩

/-- A right half whose window is in the trap at the odd time `2 s0 + 1` reads `u R` from `s0` on
along its windows of `W` columns. -/
theorem readsLift_u (R : Nat → Bool) {W s0 : Nat} (hW : 16 ≤ W) (hw : win R (2 * s0 + 1) ∈ trap) :
    ReadsLift W (Rule30PeriodTwoSideways.u R) s0 := by
  refine ⟨_, winW_liftPath R hW (by omega) hw, fun k => ?_⟩
  show (winW R W (2 * s0 + 1 + 2 * k)).headD false = drv altCol R (2 * (s0 + k) + 1) 1
  rw [winW_head R (by omega), show 2 * s0 + 1 + 2 * k = 2 * (s0 + k) + 1 by omega]

/-- The complement of the free bits of `Psi R` is `u R`. -/
theorem psi_comp (R : Nat → Bool) :
    (fun s => !zrow (Rule30PeriodTwoSideways.Psi R) (2 * s + 1) 1) =
      Rule30PeriodTwoSideways.u R := by
  funext s; rw [Rule30PeriodTwoSideways.Psi_free]; simp; rfl

/-! ## `Q01GapLift` -/

/-- **`Q01GapLift W`** (**open**): no finitely supported constrained start of the zero-boundary
left half has free bits whose complement, from some step on, is read by a lift path of width `W`. -/
def Q01GapLift (W : Nat) : Prop := ∀ L : Nat → Bool, FinSupp L → InX L →
  ¬ ∃ s0, ReadsLift W (fun s => !zrow L (2 * s + 1) 1) s0

/-- **`Q01Gap` gives `Q01GapLift W`** for every `W ≥ 16`. -/
theorem Q01GapLift_of_Q01Gap {W : Nat} (hW : 16 ≤ W) (hQ : Q01Gap) : Q01GapLift W :=
  fun L hf hX ⟨s0, hr⟩ => hQ L hf hX ⟨s0, hr.gapOK hW⟩

/-- **The ladder.** For `16 ≤ W ≤ W'`, `Q01GapLift W` gives `Q01GapLift W'`. -/
theorem Q01GapLift_mono {W W' : Nat} (hW : 16 ≤ W) (hWW : W ≤ W') (hQ : Q01GapLift W) :
    Q01GapLift W' :=
  fun L hf hX ⟨s0, hr⟩ => hQ L hf hX ⟨s0, hr.take hW hWW⟩

/-- **`Q01GapLift W` gives `CQ01` for every right half whose window enters the trap**, for every
`W ≥ 16`. -/
theorem not_finSupp_Psi_of_Q01GapLift {W : Nat} (hW : 16 ≤ W) (hQ : Q01GapLift W)
    (R : Nat → Bool) {t0 : Nat} (h0 : t0 % 2 = 1) (hw : win R t0 ∈ trap) :
    ¬ FinSupp (Rule30PeriodTwoSideways.Psi R) := by
  intro hfin
  refine hQ _ hfin (Rule30PeriodTwoSideways.Psi_inX R) ⟨t0 / 2, ?_⟩
  rw [psi_comp]
  exact readsLift_u R hW (by rwa [show 2 * (t0 / 2) + 1 = t0 by omega])

/-- **`CQ01Empty` follows from `Q01GapLift W`** for every `W ≥ 16`. -/
theorem CQ01Empty_of_Q01GapLift {W : Nat} (hW : 16 ≤ W) (hQ : Q01GapLift W) :
    Rule30PeriodTwoSideways.CQ01Empty :=
  not_finSupp_Psi_of_Q01GapLift hW hQ _ (t0 := 293) (by decide) entry_empty

/-! ## `Q01GapLiftCore`: the lift together with the three core words -/

/-- **`Q01GapLiftCore W`** (**open**): no finitely supported constrained start of the
zero-boundary left half has free bits whose complement, from some step on, is read by a lift path
of width `W` and satisfies `Rule30GateTrapLift.TwoCoreOK` at every step. -/
def Q01GapLiftCore (W : Nat) : Prop := ∀ L : Nat → Bool, FinSupp L → InX L →
  ¬ ∃ s0, ReadsLift W (fun s => !zrow L (2 * s + 1) 1) s0 ∧
    ∀ s, s0 ≤ s → Rule30GateTrapLift.TwoCoreOK (fun s => !zrow L (2 * s + 1) 1) s

theorem Q01GapLiftCore_of_Q01GapLift {W : Nat} (hQ : Q01GapLift W) : Q01GapLiftCore W :=
  fun L hf hX ⟨s0, hr, _⟩ => hQ L hf hX ⟨s0, hr⟩

theorem Q01GapLiftCore_of_Q01TwoCore {W : Nat} (hQ : Rule30GateTrapLift.Q01TwoCore) :
    Q01GapLiftCore W :=
  fun L hf hX ⟨s0, _, hc⟩ => hQ L hf hX ⟨s0, hc⟩

/-- **`Q01GapLiftCore W` gives `CQ01` for every right half whose window enters the trap**, for
every `W ≥ 16`. The anchor is twenty steps after the entry time. -/
theorem not_finSupp_Psi_of_Q01GapLiftCore {W : Nat} (hW : 16 ≤ W) (hQ : Q01GapLiftCore W)
    (R : Nat → Bool) {t0 : Nat} (h0 : t0 % 2 = 1) (hw : win R t0 ∈ trap) :
    ¬ FinSupp (Rule30PeriodTwoSideways.Psi R) := by
  intro hfin
  refine hQ _ hfin (Rule30PeriodTwoSideways.Psi_inX R) ?_
  rw [psi_comp]
  refine ⟨(t0 + 19) / 2, ?_, fun s hs => ?_⟩
  · have hw' := win_mem_trap R h0 hw 10
    exact readsLift_u R hW (by rwa [show 2 * ((t0 + 19) / 2) + 1 = t0 + 2 * 10 by omega])
  · exact ⟨Rule30GateTrapWords.TwoWordsOK_of_entry R h0 hw s (by omega),
      Rule30GateTrapLift.no_3535353_of_entry R h0 hw s (by omega)⟩

/-- **`CQ01Empty` follows from `Q01GapLiftCore W`** for every `W ≥ 16`; for `R = ∅` the anchor is
step `156` (time `313`). -/
theorem CQ01Empty_of_Q01GapLiftCore {W : Nat} (hW : 16 ≤ W) (hQ : Q01GapLiftCore W) :
    Rule30PeriodTwoSideways.CQ01Empty :=
  not_finSupp_Psi_of_Q01GapLiftCore hW hQ _ (t0 := 293) (by decide) entry_empty

/-! ## Mass divergence on the ladder -/

/-- `y` is accepted by a lift path of width `W` for `H` steps: its zero-coast trace is black at
the odd times `t < H`, and at each even time `t < H` it is the complement of the first cell of the
window `t / 2` of one lift path. -/
def AcceptLift (W y H : Nat) : Prop :=
  ∃ ws, LiftPath W ws ∧ ∀ t, t < H →
    (iter F t y).testBit 0 = if t % 2 = 1 then true else !(ws (t / 2)).headD false

/-- **`MassDivergesLift W`** (**open**): for every `M` there is `H` such that no natural number of
popcount at most `M` is accepted by a lift path of width `W` for `H` steps. -/
def MassDivergesLift (W : Nat) : Prop :=
  ∀ M : Nat, ∃ H : Nat, ∀ y : Nat, Rule30ZeroCoastBridge.popcount y ≤ M → ¬ AcceptLift W y H

theorem AcceptLift.take {W W' : Nat} (hW : 16 ≤ W) (hWW : W ≤ W') {y H : Nat}
    (h : AcceptLift W' y H) : AcceptLift W y H := by
  obtain ⟨ws, hp, hh⟩ := h
  refine ⟨_, liftPath_take hW hWW hp, fun t ht => ?_⟩
  rw [hh t ht]
  show _ = if t % 2 = 1 then true else !((ws (t / 2)).take W).headD false
  rw [headD_take _ _ (by omega)]

/-- **The mass ladder.** For `16 ≤ W ≤ W'`, `MassDivergesLift W` gives `MassDivergesLift W'`. -/
theorem MassDivergesLift_mono {W W' : Nat} (hW : 16 ≤ W) (hWW : W ≤ W')
    (h : MassDivergesLift W) : MassDivergesLift W' := fun M => by
  obtain ⟨H, hH⟩ := h M
  exact ⟨H, fun y hy ha => hH y hy (ha.take hW hWW)⟩

/-- **`MassDivergesLift W` gives `Q01GapLift W`.** A finite start read by a lift path from step
`s0` on, run to the time `2 s0 + 1` and read as a natural number, is accepted for every `H`. -/
theorem Q01GapLift_of_massDivergesLift {W : Nat} (hM : MassDivergesLift W) : Q01GapLift W := by
  rintro L hf hX ⟨s0, ws, hp, hh⟩
  obtain ⟨W0, hW0⟩ := Rule30GateTrapLift.finSupp_zrow hf (2 * s0 + 1)
  obtain ⟨H, hH⟩ := hM (Rule30ZeroCoastBridge.popcount (natOfRow (zrow L (2 * s0 + 1)) W0))
  apply hH _ (Nat.le_refl _)
  refine ⟨ws, hp, fun t _ => ?_⟩
  have hrow : ∀ k, 1 ≤ k →
      rowOfNat (natOfRow (zrow L (2 * s0 + 1)) W0) k = zrow L (2 * s0 + 1) k :=
    rowOfNat_natOfRow hW0
  have hcol : (iter F t (natOfRow (zrow L (2 * s0 + 1)) W0)).testBit 0 =
      zrow L (2 * s0 + 1 + t) 1 := by
    rw [← zrow_rowOfNat_col1, zrow_congr hrow t 1, ← zrow_shift]
  rw [hcol]
  rcases Nat.mod_two_eq_zero_or_one t with h2 | h2
  · obtain ⟨k, rfl⟩ : ∃ k, t = 2 * k := ⟨t / 2, by omega⟩
    rw [ite_eq_right (by omega), show 2 * k / 2 = k by omega, hh k,
      show 2 * s0 + 1 + 2 * k = 2 * (s0 + k) + 1 by omega]
    simp
  · obtain ⟨k, rfl⟩ : ∃ k, t = 2 * k + 1 := ⟨t / 2, by omega⟩
    rw [ite_eq_left h2, show 2 * s0 + 1 + (2 * k + 1) = 2 * (s0 + k + 1) by omega]
    exact hX (s0 + k + 1)

/-- **`CQ01Empty` follows from `MassDivergesLift W`** for every `W ≥ 16`. -/
theorem CQ01Empty_of_massDivergesLift {W : Nat} (hW : 16 ≤ W) (hM : MassDivergesLift W) :
    Rule30PeriodTwoSideways.CQ01Empty :=
  CQ01Empty_of_Q01GapLift hW (Q01GapLift_of_massDivergesLift hM)

/-- **The ladder in one statement.** For `16 ≤ W ≤ W'`: `Q01Gap` gives `Q01GapLift W`,
`Q01GapLift W` gives `Q01GapLift W'`, `MassDivergesLift W` gives `Q01GapLift W`, and each of
`Q01GapLift W'`, `Q01GapLiftCore W'` gives `CQ01Empty`. -/
theorem ladder {W W' : Nat} (hW : 16 ≤ W) (hWW : W ≤ W') :
    (Q01Gap → Q01GapLift W) ∧ (Q01GapLift W → Q01GapLift W') ∧
      (MassDivergesLift W → Q01GapLift W) ∧
      (Q01GapLift W' → Rule30PeriodTwoSideways.CQ01Empty) ∧
      (Q01GapLiftCore W' → Rule30PeriodTwoSideways.CQ01Empty) :=
  ⟨Q01GapLift_of_Q01Gap hW, Q01GapLift_mono hW hWW, Q01GapLift_of_massDivergesLift,
    CQ01Empty_of_Q01GapLift (Nat.le_trans hW hWW), CQ01Empty_of_Q01GapLiftCore (Nat.le_trans hW hWW)⟩

/-! ## Shift invariance, horizon monotonicity, and the conditional `Q01GapLift`-to-`CQ01` dichotomy bridge -/

/-- **Shift invariance of width-`W` lift paths (`LiftPath_shift`):** shifting any width-`W` lift
path (`W ≥ 16`) by `d` double steps preserves `LiftPath W`. -/
theorem LiftPath_shift {W : Nat} (hW : 16 ≤ W) {ws : Nat → List Bool}
    (hp : LiftPath W ws) (d : Nat) : LiftPath W (fun k => ws (d + k)) := by
  refine ⟨hp.length d, ?_, fun k => ?_⟩
  · show (ws (d + 0)).take 16 ∈ trap
    rw [Nat.add_zero]
    exact hp.take16_mem hW d
  · exact hp.2.2 (d + k)

/-- **Zero-horizon acceptance (`AcceptLift_zero`):** every seed `y` is accepted by a width-`W` lift
path (`W ≥ 16`) for horizon `0`. -/
theorem AcceptLift_zero {W y : Nat} (hW : 16 ≤ W) : AcceptLift W y 0 := by
  refine ⟨fun k => winW Rule30PeriodTwoSideways.empty W (293 + 2 * k),
    winW_liftPath Rule30PeriodTwoSideways.empty hW (by decide) entry_empty, fun t ht => ?_⟩
  omega

/-- **Horizon monotonicity (`AcceptLift_mono_horizon`):** `AcceptLift W y H2` implies `AcceptLift W y H1` for `H1 ≤ H2`. -/
theorem AcceptLift_mono_horizon {W y H1 H2 : Nat} (hle : H1 ≤ H2)
    (h : AcceptLift W y H2) : AcceptLift W y H1 := by
  obtain ⟨ws, hp, ht⟩ := h
  exact ⟨ws, hp, fun t ht1 => ht t (by omega)⟩

/-- **Even-step shift invariance (`AcceptLift_shift_even`):** advancing `y` by `2 * d` zero-coast
steps shifts `AcceptLift W y H` to `AcceptLift W (iter F (2 * d) y) (H - 2 * d)`. -/
theorem AcceptLift_shift_even {W y H d : Nat} (hW : 16 ≤ W)
    (h : AcceptLift W y H) : AcceptLift W (iter F (2 * d) y) (H - 2 * d) := by
  obtain ⟨ws, hp, ht⟩ := h
  refine ⟨fun k => ws (d + k), LiftPath_shift hW hp d, fun t htH => ?_⟩
  have hlt : 2 * d + t < H := by omega
  have hrow := ht (2 * d + t) hlt
  rw [← Rule30ZeroCoastBridge.iter_F_add, hrow]
  by_cases hodd : (2 * d + t) % 2 = 1
  · have htodd : t % 2 = 1 := by omega
    simp [hodd, htodd]
  · have hteven : t % 2 = 0 := by omega
    simp only [hodd, ↓reduceIte, hteven]
    have hdiv : (2 * d + t) / 2 = d + t / 2 := by omega
    rw [hdiv]
    rfl

/-- **Full two-sided `CQ01` from open right-half dichotomy and open `Q01GapLift W`
(`CQ01_of_dichotomy_and_Q01GapLift`):** upgrades `CQ01Empty_of_Q01GapLift` from `CQ01Empty` to full
two-sided `CQ01` at every width `W ≥ 16` under the right-half trap-or-periodic dichotomy. -/
theorem CQ01_of_dichotomy_and_Q01GapLift {W : Nat} (hW : 16 ≤ W)
    (hdich : ∀ R : Nat → Bool, FinSupp R →
      (∃ t0, t0 % 2 = 1 ∧ win R t0 ∈ trap) ∨ Rule30Jen.EventuallyPeriodic (Rule30PeriodTwoSideways.u R))
    (hQ : Q01GapLift W) :
    Rule30PeriodTwoCoupled.CQ01 := by
  rw [Rule30PeriodTwoSideways.CQ01_iff_Psi]
  intro R hfin
  rcases hdich R hfin with ⟨t0, h0, hw⟩ | hper
  · exact not_finSupp_Psi_of_Q01GapLift hW hQ R h0 hw
  · exact Rule30PeriodTwoSideways.not_finSupp_Psi_of_eventuallyPeriodic R hper

end Ruliology.CellularAutomata.Rule30GateTrapLadder
