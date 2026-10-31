module

public import Ruliology.CellularAutomata.Rule30Certificates.GateTrap
public import Ruliology.CellularAutomata.Rule30PeriodTwoSideways
public import Ruliology.CellularAutomata.Rule30DrivenPrefix
public import Ruliology.CellularAutomata.Rule30SpacingRenormalization
public import Ruliology.CellularAutomata.Rule30ZeroBoundary

/-!
# A trap for the gate of the alternating-driven right half, and `CQ01Empty` from `Q01Gap`

`Rule30PeriodTwoSideways.u R s` is column `1`, at the odd time `2 s + 1`, of the right half `R`
driven by the alternating column `1, 0, 1, 0, …`. Its complement is the sequence of free bits of
the candidate left row `Psi R`, and the milestone `CQ01Empty` says that `Psi ∅` has infinitely many
black cells.

**The trap.** The windows of the columns `1..16` at the odd times can fall into a set `trap` of
`829` windows that is closed under the double step whatever column `17` does
(`Rule30Certificates/GateTrap`, kernel checks), so a right half that enters it stays in it whatever
it does further right. Inside the trap, after a black cell of column `1` the next one comes three
or five double steps later.

* `gaps_of_entry`: if the window of `R` is in `trap` at an odd time `t0`, then every black cell of
  `u R` after `t0` is followed by the next one at distance `3` or `5`.
* `u_empty_gaps`: the window of `R = ∅` is in `trap` at time `293`, so from `s = 146` on every
  black cell of `u ∅` is followed by the next one at distance `3` or `5`. It is black at `146`
  (`u_empty_146`), so after that cell `u ∅` is a concatenation of the blocks `001` and `00001`.
* `u_empty_window`, `emptyGate_window`, `u_empty_spaced`: from `s = 146` on, `u ∅` satisfies the gate
  window `Rule30DrivenPrefix.Window`, and the gate `emptyGate r = u ∅ (146 + r)` satisfies
  `Rule30SpacingRenormalization.Spaced`. By `u_empty_transform_not_spaced` its transform is not
  spaced: the eight-column translation of `Rule30SpacingRenormalization` applies to this gate once,
  not twice.

**The reduction.** `Q01Gap` (**open**): no finitely supported constrained start of the
zero-boundary left half has free bits whose complement, from some step on, has each black cell
followed by the next one at distance `3` or `5`. It follows from `Rule30ZeroBoundary.Q01` (`Q01Gap_of_Q01`), which excludes every
finitely supported constrained start, and it gives `¬ FinSupp (Psi R)` for every right half whose
window enters the trap (`not_finSupp_Psi_of_Q01Gap`), in particular `CQ01Empty`
(`CQ01Empty_of_Q01Gap`). Nothing here excludes period 2.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30GateTrap

open Rule30StripCertificates Rule30Ether Rule30PeriodTwoCoupled Rule30ZeroBoundary

/-! ## Bitmaps -/

theorem mask_spec : ∀ (L : List (List Bool)) (n : Nat), (mask L).testBit n = true →
    ∃ s ∈ L, encList s = n
  | [], n, h => by simp [mask] at h
  | s' :: rest, n, h => by
    simp only [mask, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · rw [Nat.testBit_two_pow] at h
      exact ⟨s', List.mem_cons_self, by simpa using h⟩
    · obtain ⟨s, hs, he⟩ := mask_spec rest n h
      exact ⟨s, List.mem_cons_of_mem _ hs, he⟩

theorem encList_injective : ∀ (a b : List Bool), a.length = b.length → encList a = encList b → a = b
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | x :: a, y :: b, hl, he => by
    simp only [encList] at he
    have hx : x = y := by cases x <;> cases y <;> simp at he ⊢ <;> omega
    subst hx
    have : encList a = encList b := by cases x <;> simp at he <;> omega
    rw [encList_injective a b (by simpa using hl) this]

theorem length_of_mem_decode {LN : List Nat} {s : List Bool} (h : s ∈ LN.map decode) :
    s.length = 16 := by
  obtain ⟨n, _, rfl⟩ := List.mem_map.1 h
  exact length_seg _ _

/-- A window of length `16` whose bit is set in the bitmap of a list of codes is in the list. -/
theorem mem_of_inM {LN : List Nat} {w : List Bool} (hw : w.length = 16)
    (h : inM (mask (LN.map decode)) w = true) : w ∈ LN.map decode := by
  obtain ⟨s, hs, he⟩ := mask_spec _ _ h
  have : s = w := encList_injective s w (by rw [hw]; exact length_of_mem_decode hs) he
  exact this ▸ hs

theorem allSucc_spec {P : List Bool → Bool} {s : List Bool} (h : allSucc P s = true)
    (x1 x2 : Bool) : P (step2 s x1 x2) = true := by
  unfold allSucc at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  cases x1 <;> cases x2 <;> assumption

/-! ## The driven right half -/

section Driven
variable (R : Nat → Bool)

/-- The window of `R`: the columns `1..16` of the right half `R` driven by the alternating column,
at time `t`. -/
def win (t : Nat) : List Bool := rowOf (drv altCol R) t 0 16

theorem win_length (t : Nat) : (win R t).length = 16 := length_seg _ _

theorem win_head (t : Nat) : (win R t).headD false = drv altCol R t 1 := rowOf_head _ t 0 15

/-- From an odd time, the window two steps later is a double step of the window. -/
theorem win_step2 (t : Nat) (ht : t % 2 = 1) :
    ∃ x1 x2, win R (t + 2) = step2 (win R t) x1 x2 := by
  have h1 := rowOf_succ (drv_isR30 altCol R) t 0 16
  have h2 := rowOf_succ (drv_isR30 altCol R) (t + 1) 0 16
  rw [drv_col0] at h1 h2
  have a1 : altCol t = false := by unfold altCol; simp [ht]
  have a2 : altCol (t + 1) = true := by unfold altCol; simp; omega
  rw [a1] at h1
  rw [a2] at h2
  refine ⟨drv altCol R t 17, drv altCol R (t + 1) 17, ?_⟩
  unfold win step2
  rw [show t + 2 = t + 1 + 1 by omega, h2, h1]

theorem win_next {L : List (List Bool)} {P : List Bool → Bool} (hc : L.all (allSucc P) = true)
    {t : Nat} (ht : t % 2 = 1) (hw : win R t ∈ L) : P (win R (t + 2)) = true := by
  obtain ⟨x1, x2, e⟩ := win_step2 R t ht
  rw [e]
  exact allSucc_spec (List.all_eq_true.1 hc _ hw) x1 x2

/-- A window that enters the trap at an odd time stays in it at every later odd time. -/
theorem win_mem_trap {t0 : Nat} (h0 : t0 % 2 = 1) (hw : win R t0 ∈ trap) :
    ∀ n, win R (t0 + 2 * n) ∈ trap
  | 0 => hw
  | n + 1 => by
    have ih := win_mem_trap h0 hw n
    have := win_next R trapClosed_ok (by omega) ih
    rw [show t0 + 2 * (n + 1) = t0 + 2 * n + 2 by omega]
    exact mem_of_inM (win_length _ _) this

theorem u_eq_head (s : Nat) :
    Rule30PeriodTwoSideways.u R s = (win R (2 * s + 1)).headD false := by
  rw [win_head]; rfl

/-- **The trap.** If the window of `R` is in `trap` at an odd time `t0`, then every black cell of
`u R` at a step `s` with `t0 ≤ 2 s + 1` is followed by the next black cell at distance `3` or `5`. -/
theorem gaps_of_entry {t0 : Nat} (h0 : t0 % 2 = 1) (hw : win R t0 ∈ trap) (s : Nat)
    (hs : t0 ≤ 2 * s + 1) (h : Rule30PeriodTwoSideways.u R s = true) :
    (Rule30PeriodTwoSideways.u R (s + 1) = false ∧ Rule30PeriodTwoSideways.u R (s + 2) = false ∧
      Rule30PeriodTwoSideways.u R (s + 3) = true) ∨
    (Rule30PeriodTwoSideways.u R (s + 1) = false ∧ Rule30PeriodTwoSideways.u R (s + 2) = false ∧
      Rule30PeriodTwoSideways.u R (s + 3) = false ∧ Rule30PeriodTwoSideways.u R (s + 4) = false ∧
      Rule30PeriodTwoSideways.u R (s + 5) = true) := by
  have hw0 : win R (2 * s + 1) ∈ trap := by
    have := win_mem_trap R h0 hw ((2 * s + 1 - t0) / 2)
    rwa [show t0 + 2 * ((2 * s + 1 - t0) / 2) = 2 * s + 1 by omega] at this
  rw [u_eq_head] at h
  simp only [u_eq_head]
  -- one double step: white, in `layer1`
  have q1 := List.all_eq_true.1 afterBlack_ok _ hw0
  rw [h] at q1
  simp only [Bool.not_true, Bool.false_or] at q1
  have r1 : (!(win R (2 * s + 1 + 2)).headD false &&
      inM (mask layer1) (win R (2 * s + 1 + 2))) = true := by
    obtain ⟨x1, x2, e'⟩ := win_step2 R (2 * s + 1) (by omega)
    rw [e']; exact allSucc_spec q1 x1 x2
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at r1
  have m1 : win R (2 * (s + 1) + 1) ∈ layer1 := by
    rw [show 2 * (s + 1) + 1 = 2 * s + 1 + 2 by omega]; exact mem_of_inM (win_length _ _) r1.2
  have h1 : (win R (2 * (s + 1) + 1)).headD false = false := by
    rw [show 2 * (s + 1) + 1 = 2 * s + 1 + 2 by omega]; exact r1.1
  -- two double steps: white, in `layer2`
  have r2 := win_next R secondStep_ok (t := 2 * (s + 1) + 1) (by omega) m1
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at r2
  rw [show 2 * (s + 1) + 1 + 2 = 2 * (s + 2) + 1 by omega] at r2
  have m2 : win R (2 * (s + 2) + 1) ∈ layer2 := mem_of_inM (win_length _ _) r2.2
  -- three double steps: black (gap `3`), or white and in `layer3`
  have r3 := win_next R thirdStep_ok (t := 2 * (s + 2) + 1) (by omega) m2
  rw [show 2 * (s + 2) + 1 + 2 = 2 * (s + 3) + 1 by omega] at r3
  cases h3 : (win R (2 * (s + 3) + 1)).headD false with
  | true => exact Or.inl ⟨h1, r2.1, rfl⟩
  | false =>
    rw [h3, Bool.false_or] at r3
    have m3 : win R (2 * (s + 3) + 1) ∈ layer3 := mem_of_inM (win_length _ _) r3
    have r4 := win_next R fourthStep_ok (t := 2 * (s + 3) + 1) (by omega) m3
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at r4
    rw [show 2 * (s + 3) + 1 + 2 = 2 * (s + 4) + 1 by omega] at r4
    have m4 : win R (2 * (s + 4) + 1) ∈ layer4 := mem_of_inM (win_length _ _) r4.2
    have r5 := win_next R fifthStep_ok (t := 2 * (s + 4) + 1) (by omega) m4
    rw [show 2 * (s + 4) + 1 + 2 = 2 * (s + 5) + 1 by omega] at r5
    exact Or.inr ⟨h1, r2.1, rfl, r4.1, r5⟩

end Driven

/-! ## The empty right half -/

/-- `n` steps of the driven right half from time `t`, read on the window, are `evolve`. -/
theorem rowOf_evolve (R : Nat → Bool) : ∀ (n t b : Nat),
    rowOf (drv altCol R) (t + n) 0 b = evolve t n (rowOf (drv altCol R) t 0 (b + n))
  | 0, t, b => rfl
  | n + 1, t, b => by
    have h1 := rowOf_succ (drv_isR30 altCol R) t 0 (b + n)
    rw [drv_col0] at h1
    have e1 : rowOf (drv altCol R) t 0 (b + n) ++ [drv altCol R t (0 + (b + n) + 1)] =
        rowOf (drv altCol R) t 0 (b + n + 1) := by unfold rowOf; rw [seg_succ]
    rw [e1] at h1
    show rowOf (drv altCol R) (t + (n + 1)) 0 b =
      evolve (t + 1) n (lin3 (altCol t :: rowOf (drv altCol R) t 0 (b + (n + 1))))
    rw [show b + (n + 1) = b + n + 1 by omega, ← h1, show t + (n + 1) = t + 1 + n by omega]
    exact rowOf_evolve R n (t + 1) b

private theorem seg_all_false : ∀ (n : Nat) (f : Nat → Bool), (∀ i, f i = false) →
    seg f n = List.replicate n false
  | 0, _, _ => rfl
  | n + 1, f, h => by
    show f 0 :: seg (fun i => f (i + 1)) n = false :: List.replicate n false
    rw [h 0, seg_all_false n _ (fun i => h (i + 1))]

theorem rowOf_empty_zero (n : Nat) :
    rowOf (drv altCol Rule30PeriodTwoSideways.empty) 0 0 n = List.replicate n false := by
  unfold rowOf
  exact seg_all_false n _ (fun i => by rw [drv_init _ _ _ (by omega)]; rfl)

theorem win_empty_293 : win Rule30PeriodTwoSideways.empty 293 = decode entryCode := by
  unfold win
  rw [show (293 : Nat) = 0 + 293 from rfl, rowOf_evolve, rowOf_empty_zero]
  exact evolve_293

/-- The window of the empty right half is in the trap at time `293`. -/
theorem entry_empty : win Rule30PeriodTwoSideways.empty 293 ∈ trap := by
  rw [win_empty_293]; exact entry_mem

/-- `u ∅` is black at `s = 146`, so `u_empty_gaps` is not vacuous. -/
theorem u_empty_146 : Rule30PeriodTwoSideways.u Rule30PeriodTwoSideways.empty 146 = true := by
  rw [u_eq_head, show 2 * 146 + 1 = 293 from rfl, win_empty_293]; decide

/-- **The empty right half.** From `s = 146` on, every black cell of `u ∅` is followed by the next
one at distance `3` or `5`; with `u_empty_146`, after its black cell at `146`, `u ∅` is a
concatenation of the blocks `001` and `00001`. -/
theorem u_empty_gaps (s : Nat) (hs : 146 ≤ s)
    (h : Rule30PeriodTwoSideways.u Rule30PeriodTwoSideways.empty s = true) :
    let v := Rule30PeriodTwoSideways.u Rule30PeriodTwoSideways.empty
    (v (s + 1) = false ∧ v (s + 2) = false ∧ v (s + 3) = true) ∨
    (v (s + 1) = false ∧ v (s + 2) = false ∧ v (s + 3) = false ∧ v (s + 4) = false ∧
      v (s + 5) = true) :=
  gaps_of_entry _ (by decide) entry_empty s (by omega) h

/-! ## The gate of the empty right half -/

/-- From `s = 146` on, `u ∅` has a black cell in every five consecutive steps. -/
theorem u_empty_black_within (n : Nat) :
    ∃ b, 146 ≤ b ∧ b ≤ 146 + n ∧ 146 + n ≤ b + 4 ∧
      Rule30PeriodTwoSideways.u Rule30PeriodTwoSideways.empty b = true := by
  induction n with
  | zero => exact ⟨146, Nat.le_refl _, Nat.le_refl _, by omega, u_empty_146⟩
  | succ n ih =>
    obtain ⟨b, hb1, hb2, hb3, hb⟩ := ih
    by_cases hc : 146 + (n + 1) ≤ b + 4
    · exact ⟨b, hb1, by omega, hc, hb⟩
    · rcases u_empty_gaps b hb1 hb with ⟨_, _, h3⟩ | ⟨_, _, _, _, h5⟩
      · exact ⟨b + 3, by omega, by omega, by omega, h3⟩
      · exact ⟨b + 5, by omega, by omega, by omega, h5⟩

/-- **`u ∅` satisfies the gate window of `Rule30DrivenPrefix` at every `r ≥ 146`.**
`Rule30DrivenPrefix.Window` is the local window for exact spacings three or five. -/
theorem u_empty_window (r : Nat) (hr : 146 ≤ r) :
    Rule30DrivenPrefix.Window (Rule30PeriodTwoSideways.u Rule30PeriodTwoSideways.empty) r := by
  unfold Rule30DrivenPrefix.Window
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases h : Rule30PeriodTwoSideways.u Rule30PeriodTwoSideways.empty r with
    | false => rfl
    | true =>
      rcases u_empty_gaps r hr h with ⟨h1, _, _⟩ | ⟨h1, _, _, _, _⟩ <;> rw [h1] <;> rfl
  · cases h : Rule30PeriodTwoSideways.u Rule30PeriodTwoSideways.empty r with
    | false => rfl
    | true =>
      rcases u_empty_gaps r hr h with ⟨_, h2, _⟩ | ⟨_, h2, _, _, _⟩ <;> rw [h2] <;> rfl
  · intro h
    rcases u_empty_gaps r hr h with ⟨_, _, h3⟩ | ⟨_, _, h3, h4, h5⟩
    · left
      have h3' : Rule30PeriodTwoSideways.u Rule30PeriodTwoSideways.empty (r + 3) = true := h3
      rcases u_empty_gaps (r + 3) (by omega) h3' with ⟨h4, h5, _⟩ | ⟨h4, h5, _, _, _⟩
      · exact ⟨h3, by simpa only [Nat.add_assoc] using h4, by simpa only [Nat.add_assoc] using h5⟩
      · exact ⟨h3, by simpa only [Nat.add_assoc] using h4, by simpa only [Nat.add_assoc] using h5⟩
    · right; exact ⟨h3, h4, h5⟩
  · obtain ⟨b, hb1, hb2, hb3, hb⟩ := u_empty_black_within (r + 4 - 146)
    obtain ⟨i, rfl⟩ : ∃ i, b = r + i := ⟨b - r, by omega⟩
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> simp_all

/-- The gate of the empty right half from step `146` on. -/
def emptyGate (r : Nat) : Bool :=
  Rule30PeriodTwoSideways.u Rule30PeriodTwoSideways.empty (146 + r)

/-- **`emptyGate` satisfies the gate window of `Rule30DrivenPrefix` at every `r`.** -/
theorem emptyGate_window (r : Nat) : Rule30DrivenPrefix.Window emptyGate r := by
  have h := u_empty_window (146 + r) (by omega)
  unfold Rule30DrivenPrefix.Window at h ⊢
  simpa only [emptyGate, Nat.add_assoc] using h

/-- **The spacing hypothesis of `Rule30SpacingRenormalization` holds for `emptyGate`.** -/
theorem u_empty_spaced : Rule30SpacingRenormalization.Spaced emptyGate := fun r =>
  ⟨(emptyGate_window r).1, (emptyGate_window r).2.1⟩

/-- **The translation cannot be iterated on this gate.** By `transform_spaced_iff`, the transform
of `emptyGate` is not spaced, since `u ∅` keeps having black cells. -/
theorem u_empty_transform_not_spaced :
    ¬ Rule30SpacingRenormalization.Spaced (Rule30SpacingRenormalization.transform emptyGate) := by
  intro h
  have hz := (Rule30SpacingRenormalization.transform_spaced_iff _ u_empty_spaced).1 h
  obtain ⟨b, hb1, hb2, hb3, hb⟩ := u_empty_black_within 8
  have h2 : emptyGate (b - 150 + 4) = false := hz (b - 150)
  unfold emptyGate at h2
  rw [show 146 + (b - 150 + 4) = b by omega, hb] at h2
  exact Bool.noConfusion h2

/-! ## The reduction -/

/-- At `s`, the bit sequence `g` is white, or black with the next black cell at distance `3`
or `5`. -/
def GapOK (g : Nat → Bool) (s : Nat) : Prop :=
  g s = true → (g (s + 1) = false ∧ g (s + 2) = false ∧ g (s + 3) = true) ∨
    (g (s + 1) = false ∧ g (s + 2) = false ∧ g (s + 3) = false ∧ g (s + 4) = false ∧
      g (s + 5) = true)

/-- **`Q01Gap`** (**open**): no finitely supported constrained start of the zero-boundary left
half has free bits whose complement, from some step on, has each black cell followed by the next
one at distance `3` or `5`. -/
def Q01Gap : Prop := ∀ L : Nat → Bool, FinSupp L → InX L →
  ¬ ∃ s0, ∀ s, s0 ≤ s → GapOK (fun s => !zrow L (2 * s + 1) 1) s

/-- **`Q01` implies `Q01Gap`**: `Q01` excludes every finitely supported constrained start. -/
theorem Q01Gap_of_Q01 (h : Q01) : Q01Gap := fun L hf hX _ => h L hf hX

/-- **`Q01Gap` gives `CQ01` for every right half whose window enters the trap**: the candidate
left row `Psi R` has infinitely many black cells. -/
theorem not_finSupp_Psi_of_Q01Gap (hQ : Q01Gap) (R : Nat → Bool) {t0 : Nat} (h0 : t0 % 2 = 1)
    (hw : win R t0 ∈ trap) : ¬ FinSupp (Rule30PeriodTwoSideways.Psi R) := by
  intro hfin
  refine hQ _ hfin (Rule30PeriodTwoSideways.Psi_inX R) ⟨t0, fun s hs => ?_⟩
  have e : (fun s => !zrow (Rule30PeriodTwoSideways.Psi R) (2 * s + 1) 1) =
      Rule30PeriodTwoSideways.u R := by
    funext s; rw [Rule30PeriodTwoSideways.Psi_free]; simp; rfl
  rw [e]
  exact gaps_of_entry R h0 hw s (by omega)

/-- **`CQ01Empty` follows from `Q01Gap`.** -/
theorem CQ01Empty_of_Q01Gap (hQ : Q01Gap) : Rule30PeriodTwoSideways.CQ01Empty :=
  not_finSupp_Psi_of_Q01Gap hQ _ (t0 := 293) (by decide) entry_empty

end Ruliology.CellularAutomata.Rule30GateTrap
