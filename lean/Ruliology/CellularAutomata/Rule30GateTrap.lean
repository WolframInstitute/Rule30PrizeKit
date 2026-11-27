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

/-! ## Universal `Spaced` law for every trap-entering right half and initial profile of `emptyGate` -/

/-- **Universal `Spaced` Renormalization Law for Every Trap-Entering Right Half (`u_spaced_of_trap_entry`):**
if the 16-column window of `R` is in `trap` at an odd time `t0`, then for every `s0` with
`t0 ≤ 2 * s0 + 1`, the gate `fun r => u R (s0 + r)` satisfies `Rule30SpacingRenormalization.Spaced`. -/
theorem u_spaced_of_trap_entry (R : Nat → Bool) {t0 s0 : Nat} (h0 : t0 % 2 = 1)
    (hw : win R t0 ∈ trap) (hs0 : t0 ≤ 2 * s0 + 1) :
    Rule30SpacingRenormalization.Spaced (fun r => Rule30PeriodTwoSideways.u R (s0 + r)) := by
  intro r
  refine ⟨?_, ?_⟩
  · show (Rule30PeriodTwoSideways.u R (s0 + r) && Rule30PeriodTwoSideways.u R (s0 + (r + 1))) = false
    cases h : Rule30PeriodTwoSideways.u R (s0 + r) with
    | false => rfl
    | true =>
      rw [show s0 + (r + 1) = (s0 + r) + 1 by omega]
      rcases gaps_of_entry R h0 hw (s0 + r) (by omega) h with ⟨h1, _, _⟩ | ⟨h1, _, _, _, _⟩ <;> rw [h1] <;> rfl
  · show (Rule30PeriodTwoSideways.u R (s0 + r) && Rule30PeriodTwoSideways.u R (s0 + (r + 2))) = false
    cases h : Rule30PeriodTwoSideways.u R (s0 + r) with
    | false => rfl
    | true =>
      rw [show s0 + (r + 2) = (s0 + r) + 2 by omega]
      rcases gaps_of_entry R h0 hw (s0 + r) (by omega) h with ⟨_, h2, _⟩ | ⟨_, h2, _, _, _⟩ <;> rw [h2] <;> rfl

/-- **Exact Initial Three-Step Profile of `emptyGate` (`emptyGate_initial_values`).** -/
theorem emptyGate_initial_values :
    emptyGate 0 = true ∧ emptyGate 1 = false ∧ emptyGate 2 = false := by
  have h0 : emptyGate 0 = true := u_empty_146
  rcases u_empty_gaps 146 (Nat.le_refl _) u_empty_146 with ⟨h1, h2, _⟩ | ⟨h1, h2, _, _, _⟩
  · exact ⟨h0, h1, h2⟩
  · exact ⟨h0, h1, h2⟩

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

/-! ## Exact 75-state observer DFA, two-sided topological entropy pinch, and zero-boundary survival decay -/

def emitPath : List Bool → List (Bool × Bool) → List Bool
  | _, [] => []
  | s, (x1, x2) :: rest => s.headD false :: emitPath (step2 s x1 x2) rest

def runPath : List Bool → List (Bool × Bool) → List Bool
  | s, [] => s
  | s, (x1, x2) :: rest => runPath (step2 s x1 x2) rest

def TrapPath (w : List Bool) : Prop :=
  ∃ s ∈ trap, ∃ inp : List (Bool × Bool), inp.length = w.length ∧ emitPath s inp = w

def trapCodesPack : Nat := 0x6fd7cfd78fd70fd797d717d7f3977397b3973397ed976d97cd978d970d97f5977597b5973597d597559795971597a5972597c597459785970597f1977197d19791971197e1976197a1972197419781970197df675f679f671f67f3677367d36793671367e3676367a3672367436783670367fe677e67be673e67ee676e67ce678e670e67f6677667b6673667d667566796671667a6672667c667466786670667fc677c67dc679c671c67ec676c67ac672c67f867b8673867586798671867f0677067b0673067e0676067c06780670067f7a7b7a737a757a797a717a77da7dda79da71da7ada72da7cda74da78da70da7f9a7b9a739a7d9a759a799a719a7fea7bea73ea7dea75ea79ea71ea7cea74ea78ea70ea7f6a776a7b6a736a7e6a766a7c6a786a706a7faa77aa7baa73aa7daa75aa79aa71aa7eaa76aa7aaa72aa7caa74aa78aa70aa7f2a772a7b2a732a792a712a7e2a762a7a2a722a7c2a742a782a702a7f4a774a7d4a7e4a764a7a4a724a744a784a704a7c107b4de34def3ce73ceb3ce33cee3ce63cebdce3dce6dcecdce8dce0dced5ce55ce95ce15cee5cea5ce25cec5ce45ce85ce05ceff8e7f8ebf8e3f8eef8e6f8ecf8e8f8e0f8ef78e778eb78e378ed78e578e978e178ee78e678ea78e278eed8ead8e2d8ecd8e4d8ef98eb98e398ed98e598e998e198eb18e318e618ec18e818e018efe8ebe8e3e8ede8e5e8e9e8e1e8ef68e768eb68e368ee68e668ec68e868e068efa8e7a8eba8e3a8eda8e9a8e1a8eea8e6a8eaa8e2a8eca8e4a8e8a8e0a8ef28e728ed28e528e928e128ee28e628ea28e228ec28e428e828e028efc8ebc8e3c8edc8e5c8e9c8e1c8ef48e748eb48ee48e648ec48e848e048e788ed88e988e188ea88e288e888e088ef08e708eb08e308ed08e508e908e108ea08e208ec08e408e808e008efe3abe3a3e3ade3a5e3a9e3a1e3af63a763ab63ac63a863a063a7a3ada3a9a3a1a3aaa3a2a3aca3a4a3a8a3a0a3af8dab8da38dad8da58da98da18daf0da70dab0daff1a7f1abf1af71a771ab71a371ad71a571a971a171ae71aa71a271ac71a471a871a071ade1a5e1a9e1a1e1ab61a361a661ac61a861a061aea1aaa1a2a1aca1a4a1a8a1a0a1af76a776ad76a976a176ae76a676aa76a276a476a876a076adb6a5b6a9b6a1b6ae36a636ac36a836a036add6a5d6a9d6aed6aad6a2d6acd6a4d6a8d6a0d6af56ab56a356a556a956a156a656ac56a856a056a996a196ae96aa96a296af16a716ab16a316ad16a916a116ae16a616aa16a216af26ab26a326ad26a526a926a126aa26a226ac26a426a826a026afc6abc6a3c6adc6a5c6a9c6a1c6af46a746ab46a346ae46a646ac46a846a046af86a786ab86a386ad86a986a186ae86a686aa86a286ac86a486a886a086ad06a506a906a106ae06aa06a206ac06a406a806a006aa9c229c2c9c249c2ff5c7f5cbf5c3f5c975c175ccd5c4d5c8d5c0d5cf95cb95c395cd95c595c995c195cf15c715cb15ce15c615cc15c815c015cfe5cbe5c3e5cde5c5e5c9e5cee5cae5c2e5cce5c4e5c8e5c0e5cf65c765cb65c365ce65c665cc65c865c065cfa5c7a5cba5c3a5cda5c9a5c1a5cea5c6a5caa5c2a5cca5c4a5c8a5c0a5cf25c725cb25c325cd25c525c925c125ce25c625ca25c225cc25c425c825c025cf45c745cd45c945c145ce45c645ca45c245c445cf85c785cb85c385ce85c685cc85c885c085cf05c705cb05c305cd05c905c105ca05c205cc05c405c805cfe9c7e9cbe9cee9c6e9cce9cf69c769cb69c369cd69c569c969c169ce69ca69c269cc69c469c869c069cf164d1645164ef78af782f78fd78bd783d78f5787578b5783578d57895781578e5786578a5782578c57885780578f9787978d97899781978e9786978a9782978497889780978a3b823b883b803b8ffe87fe8dfe89fe81fe8efe86fe8afe82fe8cfe84fe88fe80fe8fbe8bbe83be8dbe85be89be81be8fde87de8bde83de8dde85de89de81de8ede86de8cde88de80de8f5e875e8b5e835e8d5e855e895e815e8e5e865e8a5e825e8c5e845e885e879e8d9e899e819e8e9e869e8a9e829e8c9e849e889e809e8e1e861e8a1e821e8f7a877a8d7a897a817a8e7a867a8a7a827a847a887a807a8cda84da88da80da8d9a859a899a819a8b1a831a861a8c1a881a801a87ea8dea89ea81ea8aea82ea8cea84ea88ea80ea8faa87aa8baa83aa8daa85aa89aa81aa8eaa86aa8caa88aa80aa8f2a872a8b2a832a8d2a852a892a812a8a2a822a8c2a842a882a802a8b8a838a868a8c8a888a808a890a810a8e0a8a0a820a8c0a840a880a800a8
def trapSuccPack : Nat := 0x741cf739ce745d2745d274dd374dd375dd7759d5745d1745d1749d2751d3705c0705c0705c0709c2709c2709c26f9be6f9bf735cc735cc735cc72dcb70dc470dc4715c5715c5729ca721c7721c7721c7721c7729ca729ca729ca715c5715c6715c6715c6715c6715c570dc370dc3711c4719c56f5bd6f5bd6f1bc6f1bd701c1701c1701c1701c0725c9725c9719c6711c36c1af6c1af6c1af6c5b16b5ae6b5ae6adab6adab6b1ac6b9ad6edba6edba6edba6e5b96e5b96e5b96e1b86e1b96d9b76d9b66d5b56d5b56d1b46cdb29e67a9e67a9e67a9e6799ee7b9ee7b9f27c9fa7d9b66c9b66c9b66c9ba6e9aa6b9aa6b9a2689a2689a6699ae6a9ca719ca719ca719c2709c2709c2709be6f9be709de789de779da769da769d6759d27381a0581a0581a0581e0781e0781e0782208822098320b8320b8320b82a0a8360e8360e83e0f83e0f84e1384a1184a1184a1184a1184e1384e1384e1383e0f83e1083e1083e1083e1083e0f8360d8360d83a0e8420f7f9fe7f9fe7f5fd7f5fe7fe007fe007fe007fdff812048120480e0380a0188e2288e2288e22896258a2298a2298b62d8b62d8ba2e8c22f8c22f8c22f8c22f8ba2e8ba2e8ba2e8b62d8b62e962579625796a5a96a5a9765d9765e9765e9765d94e5394e539525495a5594650946509465094a5294a5294a5293a4e93a4f92a4992a4992a49922489164691646912449124490e4390a419324b9324b9364d9364d926499264a9264a9264991e4791e479224892a499825f9866198a6398a6399264992649966599e669966599665992649926595e5895e5895e5895e57966599665997a5e9725b8761c8761c87e1f87e1f88220882218822188221882218822086218862188661986e1a8ca318ca318ce338ce338d2348d2358d2358d2358d2358d2348da368da368de378e6388ea3b8ea3b8ea3b8ea3a8f23c8f23c902408fe3e8fe3e8fe3e8fe3e9024090240902408f23c8f23d89624896248962488e2389a2789a278be2f8be2f8b22c8ae2a8ae2a8ae2a8ae2a8b22c8b22c8b22c8be2f8be308be308be308be308be2f89a2689a2689e278a6288a6288a6288a62889e2789e2789e2789a2689a2788a2388a2388a2388a2289224892248a62989e2686618866188661886e1b86e1b86e1b85a1685a1785214852148561585e1687e1e87e1e87e1e8761d8761d8761d8721c8721d8b62e8b62e8b62e8b62d8a2288a2288962588e227e9f97e9f97e9f97f1fc7ddf87ddf87c9f17c9f17c9f17c1f07c1f07c1f07bdef7bdf07cdf47cdf37edfb7edfb7e1f87d9f59fe809fe802d0b42d0b42c8b22c8b32e8b92e8b92e8b92ecbb2ecbb2ecbb2dcb72dcb82fcbe2fcbe2fcbe2f4bd310c4310c4314c5314c6324c831cc72f0bd2f0bd2f8be2f8be30cc3304c02f8bf2f8bf2f8bf2f8be2f0bc2f0bc2f4bd2fcbe2e0b72e0b72d8b62d8b62d4b52d4b62e4ba2e4ba2e4ba2e4b9308c2308c22fcbf2f4bc47d1e47d1e47d1e481204812048120485214852249524495244952448d2349927499274a1284a1284b12c4ad2a4ad2a4ad2a4ad2a4b12c4b12c4b12c4a1284a1294a1294a1294a1294a128499264992649d274a5284c12f4c12f4c12f4b92e4b92e4b92e4b52d4b52e4d9354d9354d1344d1344cd334cd344c5324c5324c5324c5313c8f13c8f13d0f43d0f43dcf73dcf83dcf83dcf83dcf83dcf73b4ed3b4ed3b8ee3c0ef40100401003ecfb3ecfc46919461184350e4350e42d0b42d0b4290a4250842508425084290a4290a42d0b42d0c42d0c42d0c42d0c42d0b4350d4350d4390e4410f4711b4711b4711b4751d4751d4751d465194651a3f0fb3f0fb3f0fb3e8fa3f4fe3f4fe419064190640d034090140901409014090140d0340d0340d03419064190741907419073f4fd3f4fd3f8fe400ff400ff400ff400ff3f8fe3f8fe3f8fe3f4fd3f4fe3e4fa3e4fa3e4fa3e4f93ecfb3ecfb401003f8fd3b8ed3b8ed3b8ed3c0f03acec3acec3acec3aceb3a4e93a4e93a8ea3b0eb3d0f33d0f33d0f33c8f23c8f23c8f23c4f13c4f2411054110541105411043fcff3fcff3f0fc3e8f935cd635cd6360d8360d8364d9364da364da364da364da364d936cdb36cdb370dc378dd34cd234cd234cd2354d5354d5354d5330cb330cb330cb328ca334ce334ce350d4350d4344d1340cf394e4398e639ce839ce8380e0380e0384e138ce2384e1384e1380e0380e137cdf37cdf38ce3384e045915459154591545d1745d1745d1744d1344d1444d1444d1444d1444d1344511445114491245113409024090240501405023d4f63d4f63d4f63d4f53bcef3bcef3b0ec3a8e927c9e27c9e280a0280a028ca328ca428ca428ca428ca428ca32a0a82a0a82a4a92acaa2b4ac2b4ac2b4ac2b8ae2b8ae2b8ae25496254962709c2709c26c9b268992689926c9b2709d2709d25495254952589626097258962589625495254962489324893248932489225094250942609825895298a5298a529ca729ca72a8aa2a8ab2a8ab2a8ab2a8ab2a8aa284a1284a1288a2290a32c0af2c0af2c0af2c4b12c4b12c4b10400f0400f0400f04812048120481209c2609c2609c260a4290a4290a429090240902509025090250902509024088220882208c23094240b42c0b42c0ac2b0ac2b0a82a0a82b0b82f0b82f0b82f0b82e0cc330cc330c8320c43018c6418c6418c6418c631a4691a4691a86a1b06b1e4791e4791d0741d0751545414c5315857158571745d1745d1705c16c5a164581645815c5715c5715856158571485314853148531485215054150541645915c561fc7e1fc7e1fc7e200801f07d1f07d1e87a1e87a1ec7b1f47c210832108321083208822088220882204812048221486214852308c2308c22c8b228892308d2308d2308d2308c214852148521886220871a0671a0671a067198661d8771d8771c0701c0701bc6f1b86d1c0711c0711c0711c0701d8761d8761e4781e4781dc771dc771d8761d8771946619466194661946519c6719c671b06c1a8691a8691a8691b06c1b06c19c6719c6819c6819c671946519465198661a0671805f1785e18462184621ac6b1ac6b1a068198651384e1384e13c4f14450144501445013c4f13c4f1384e1384f15c5615c5615c5616459164591645915054150551505515055148521485214c53154541d4741d4741d4741cc731cc731cc731c8721c8730140401404018060180600802008030080300803008030080200000000000040100c02020080200801c0701c080340e0340e0340e0340d0300c0300c02c0b028090781d0781d07c1f07c1f080200802108021080210802108020098260982609c270a4280681906819068190701c0701c0701c05c1705c180481104811048110401004c1404c1406c1b06c1b060180581512849128491284912c4b12c4b12c4b1304c1304d1304d1304d1144511445118461204712047120471204711846118461184611445114461084310843108431084211044110441204811845100411004110041100400f83e0f83e0fc3f104400f43c0f43c0ec3b0ec3b0e83a0e83b0e0390e0390e0390e0380dc370dc370d8360d434244912449124090240912388f2388f2388f2388e65d9665d9665d96661986619866198665996659a66d9b66d9b6719c6799d61987619876198761986621886218862d8b629895dd765dd765e1785e1785ed7b5ed7c5ed7c5ed7c5ed7c5ed7b5c9725c9725cd735d5745f97d5f97d5f97d5fd7f5fd7f5fd7f65594655946559464d936258a6258a61585615856118460d82559555595555d5755d575615856159561595615956159561585695a5695a5755c5755c56d5b56d5b5695a5695b5795f5795f5795f5795e58160581605916458d6258d6258d6258d62591645916459164581605816152548525485254851d475294b5294b54d5354d535415053d4e53d4e53d4e53d4e54150541505415054d5354d5454d5454d545294a5294a52d4b5354c5354c5354c5354c52d4b52d4b52d4b5294a5294b5194751947519475194652148521485354d52d4a5013f5013f5013f5054150541505414f53d4f53e4f53e4f53e4f53e4f53d4ed3b4ed3b4f13c4f93d51544515445154450d4350d4350d435094250943545525455254552545515314c5314c5254951d465c16f5c16f5c16f5c5715b56e5b56e5ad6b5ad6b5b16c5b96d5a1675a1675a16759966599665996659565595665a56a5a56969da669da669da66a1a86a1a86a1a86a5a96a5aa695a4695a4695a468da367da067da0685a1685a1695a568da26459064590645906499264992649926398e6398f6398f6398f6318c6318c6358d63d8e605816058160180601815e57a5e57a5e57a5e5795d1745d17478de278de278de2791e4791e4791e479de679de679de6795e57a1e97a1e97b5ec7b5ec7b5ec7b9ee7b9ee7b9ee7a9ea7a9eb7a9eb7a9eb7a9eb7a9ea7a1e87a1e87a5e97adea76dda76dda765d9765d9761d8761d9771dd771dd771dd771dc785e1785e1781e077dde4e9394e9394dd384dd384dd384dd37cdb35cdb35cd334cd334ccf33ccf34cbf2ecbf2ecc330cc330cc731cc732caf2acaf2acaf2acb72dcb72dcb72dca328ca329ca329ca329c9b26c9b26c9f27ca728c8f22c8f22c8f22c8721c8721c8721c8320c8321c9325c9325cb32ccb32cca729c9f26c731bc731bc731bc771dc7b1fc7b1fc5f17c5f17c6318c6b19c6b19c6b19c6b19c6318c6318c6318c5f17c5f18c5315c5314c5b16c5b16c6b1ac6317ce338ce338cdf37cdf38cf33ccf33ccef3bceb39b5ad5b5ad5b5ad5b5ed7b62d9b62d9b6adab6adab6edbb76dcb76dcb76dcb76dcb6edbb6edbb6edbb6adab6adbb7adfb7adfb7adfb7adeb82e0b82e0b8ee3b8ae1ba6e8ba6e8baaeabaaeabaeebbaeecbaeecbaeecbaeecbaeebb92e4b92e4b96e5b9ee6bf2fbbf2fbbf2fbbf6fdbf6fdbf6fdbfafebfaffbfaffbfaffbfaffbfafec0300c0300c0701c0f02c0f02c0f02c0f02c0701bcef4bcef4bd6f5bd6f5beafabe2f7be2f7be2f7be2f7beafabeafabeafabd6f5bd6f6bd6f6bd6f6bd6f6bd6f5bcef3bcef3bd2f4bdaf5bc2efbc2efbc2efbbaeebbaeebbaeebb6edbb6eebc6f2bc6f2bc6f2bc6f1be6f9be6f9c330bc370dc3b0fc3b0fc1f07c1f07c2308c2b09c2b09c2b09c2b09c2308c2308c2308c1f07c1f08c1305c1305c1305c1304c1b06c1b06c2b0ac2307c4f12c4f12c4f12c4711c4711c4711c4310c4311b0ec2b0ec2b0ec2b12c4b02c1b02c1afabeafabeafebfb06c0b22c7b22c7b22c7b1ac6b1ac6b1ac6b16c5b16c6b26cab26c9b3aceb3aceb36cdb32cbb3ed0b3ed0b3ed0b3ecfb46d1b46d1b52d4b4ed2a6299a6299a6299a6298a4290a4290a4691a4e92a86a1a86a1a729ca729daeab9ae2b8abeb0abeb0ab6adab6adab2acaaeaaaaeaaab2acab6aeab6aeabeafabeafac2b0acab1ac2b0ac2b0abeafabeb0adeb8adeb8adeb8adeb7ae6b9ae6b9af6bdaf2bba8ea2a8ea2a8ea2a96a5a96a5a96a5aa2a8aa2a9aa2a9aa2a9aa2a9aa2a8a7a9ea7a9ea7e9fa86a0a86a0a86a0a86a0a7e9fa6a9ba6a9ba729ca729ca86a1a7e9ea4690a4690a4690a4e93a4e93a4e93a3a8ea3a8fa3a8fa3a8fa3a8fa3a8ea328ca328ca368da3e8ea5695a5695a5294a5295a9aa7a9aa7a9aa7a9aa6a82a0a82a0a769da6e9aa2689a2689a2a8aa2a8ba2287a1a86a0a83a0a83a1284a1284a2288a1a85aceb3aceb3ad2b4adab5a96a4a96a4a8ea3a8ea3a8aa2a8aa3a5a97a5a97a5a97a5a96a4a92a4a92a3e8fa368c
def trapDfaStepPack : Nat := 0x3d004b004a1f0049000048004700462f45004400431f000042004100403f003e00003d003c003b003a0039003800370036003534000033003200310024002630002f2e002d2c00002b002a002900280027002625151924001c00232200002100201f00001e001d001c001b001a1918170016150014001300120011000a0e10000f0b000e0d000c0b0a000900080507000605040302
def trapDfaMasksList : List Nat := [0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 0x1ffffffffffffffffffffffffffffffffffffffffffffffc0000000000000000000000000000000000007fffff000000000007ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 0x1ffffffffffffffffffffffffffffffffffff800000fffffffffff80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x1ffffffffffffffffffffffffffffffffffffffffffffffc0000000000000000000000000000000000007fffff000000000007ffffffffffffffffffffffffffff80000000000000000000000000000000007f19ffffffffffffffe7c2fffffffff003c3ffff7fff, 0x7fffffffffffffffffffffffffffffffffff800000fffffffffff80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x7fffffffffffffffffffffffffffffffff8cfe0000000002301e183ffc0000000ffefc00058000, 0x1f87fffeffff07fffffe7fffffffffffc779bffffffffffc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007f19ffffffffffffffe7c2fffffffff003c3ffff7fff, 0x7fffffffffffffffffffffffffffffffe38cfe0000000002301e183ffc0000000ffefc00058000, 0x782fcf0000fff0dde1c000000000003b87ffefec0000000000000000000000000000000000000000007fffff000000000007ffffffffffffffffffffffffffff800000000000000000000000000000000000000000000000000000000000000000000000000000, 0x1f87fffeffff07fffffe7fffffffffffc779bffffffffffc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x7fff80fffffffffffc71fffffffffffe7fff800000fffffb3ffff80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x782fcf0000fff0dde1c000000000003b87ffefec0000000000000000000000000000000000000000007fffff000000000007fffffffffffffffffffffffffff8000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x7f19ffffffffffffffe7c2fffffffff003c3ffff7fff, 0x1ffff0000000001f3ff9ffc000f9c1180000000000007ffc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x7fffffc7fffffffffffffffffffffbff838cfe0000000002301e183ffc0000000f0efc00058000, 0x7f19fffc3fffffffffe7c2fffffffff003c3ffff7fff, 0x3e001fcffe00007307ec03fff7e000000000000000000000000000000000fefc00000000, 0x782fcf0000fff0dde1c000000000003a07ffefec0000000000000000000000000000000000000000007ffc3f000000000007ffffffffffffffffffff1ffffff8000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x7fffeffff07fffffe7fffffffffffc779bffffffffffc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x3b81832fc00000000000000000000000000000000000000000007ffff30000000000003f8007c0000000786003f9ffc000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x7f19df7c3fffffffffe7c2fffffffff003c3f7877fff, 0x1ffff0000000001f03f9ffc000f9c1180000000000007ffc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x7fff80fffffffffffc71fffffffffffe7fff800000003ffb3ffff80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x7f19fff01e7e03c0006000003ffc00000000097f1e0f, 0x133ff9fc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x7fffeffff07fffffe7fffffffffffc779bfffffcffffc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x1fcffe00007307ec03fff7e000000000000000000000000000000000fefc00000000, 0x7fffffc7fffffffffffffffffffffbff8000000000000002301e183ffc0000000f0efc00058000, 0x7fffeffb00000f878000fffe07fffc00000c100fff1fc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x3e001bcffc00000000000000000000000000000000000000000000000000000000000000, 0x7fff80fffffffffffc71ffffffcffffe7fff800000003ffb3ffff80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x3b81832fc00000000000000000000000000000000000000000007ffff30000000000003f8007c000000078600019ffc000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xfff0dde1c000000000003a07ffefec0000000000000000000000000000000000000000007ffc3f000000000007ffffffffffffffffffff1ffffff8000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xffffffc77e0001f3affffffc00097f800000003ffb3f3ff80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x3f9ffc000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x7f19fff01e7e03c0006000003ffc0000000000001e0f, 0x1ffff0000000001f03f9ffc000f9c1180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x7fffffc7fe6ffffffffe007fec0000000000000000000000001e183ffc0000000f0efc00058000, 0x3ffc00000000097f0000, 0x7fffeffb00000f878000fffe07fffc000000000c4b1fc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x1fcffe00007307ec03fff7e000000000000000000000000000000000000000000000, 0xfff005e1c000000000003a07ffefec000000000000000000000000000000000000000000000000000000000007ffffffcffcf9fc001fff1ffffff8000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x7fffc00000c1003bf0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xffffffc77e0000612fffcffc00097f800000003ffb3f3ff80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x7ffff30000000000003f8007c000000078600019ffc000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x3fffffffffe7c2fffffffff003c3f7870000, 0x1ffff0000000001f03f9ffc000f801180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xffdb8000000001f3affff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xf07fffffe7fffffffffffc701bfefff0fc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x1fcffe00007307c003fff7e000000000000000000000000000000000000000000000, 0x1fffc00000fffe1f7e0000000000000000000000000000000000000000000000000000000000, 0x7fff80ffffffffff3071ffffff0ffffe60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x7ffff30000000000003f80000000000078600019ffc000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x38063cf9fc0000001ffffc78000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x7fffffc7007fcfff9ffffffffffffbff8000000000000000000000000000000000000000000000, 0x7f19fff01e7e0000000000003ffc0000000000001e0f, 0x7f19e7c2ffffffc3f0000000000000, 0x7ffc3f000000000007fffffffffffffffff3071ffffff8000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x7fffeffb000000000000fffe07fffc000000000c4b1fc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xf07ffc7fe6000001fffffc701bc02300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x7f19df7c3fffffffffe7c2fffffffff0000361877fff, 0xffffffc77e0000612fffc00000097f800000003ffb3f3ff80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x7fff80ffdb803f8130709fffbf0ffffe60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x7fffeffff07fffffe7fffffffffffc779bcfff3cffffc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x7fffffc7fe6ffffffffe0000000000000000000000000000001e183ffc0000000f0efc00058000, 0x1fffc6001bcfff9ffffffffffffbff8000000000000000000000000000000000000000000000, 0xfff005e1c000000000003a07ffefec000000000000000000000000000000000000000000000000000000000000007ff80ffcf9fc001fff1ffffff8000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x7ffc3f000000000007ff803ff63fffffffe0031ffffff8000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x31e000ffffe7c2fffffffff003c3f7870000, 0x7f19df7c1e7fffff1fe7c2fffffffff0000000077fff, 0xf07ffe7fe60003cffffffc701bfefff0fc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x7fffeffff07fffffe7fffffffffffc779bcff33cfbffc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x7fff80ffdb87ffff3071ffffff0ffffe60000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x7e1fffc7007fcfff9ffffffffffffbff8000000000000000000000000000000000000000000000, 0x7ffc3f000000000007fffffff63ffffffff3071ffffff8000000000000000000000000000000000000000000000000000000000000000000000000000000]
def trapDfaRepsPack : Nat := 0x13b00b701fd0282028e00000010013b013b00b7000f028201fd01ab0000029c0282013b0034000000b7013b014601fd00e900b5028e021401ff0010014601ab028c013b00b502820010000f01ff0000014601ab013b014601ab00fa0282000f002202820226000001ab01be000001460282013b00220000000f01be0000013b01ab02820137000f0000000f01ab000001ab00000000
def trapDfaWtPack : Nat := 0x1f701cb01a3025c017f0227015e01f7026501cb022f025c01a301fe0227017f01d101f7015e01a801cb0140018301a301240161017f010b0142015e018301fe00f40265016101d100df022f014201a800cc01fe031c021e029600ba01d102d601ef025c00aa01a8029601c40227021e025c039301ef0227034301c4027a039302fa02b703df03430531038802fa0773033909820b9c

def trapCodeAt (i : Nat) : Nat := (trapCodesPack >>> (16 * i)) % 65536

def succ4At (i : Nat) (x1 x2 : Bool) : Nat :=
  let idx := 4 * i + (if x1 then 2 else 0) + (if x2 then 1 else 0)
  (trapSuccPack >>> (10 * idx)) % 1024

def trapDfaStep (q : Nat) (b : Bool) : Option Nat :=
  let v := (trapDfaStepPack >>> (16 * q + (if b then 8 else 0))) % 256
  if v = 0 then none else some (v - 1)

def trapDfaMaskAt (q : Nat) : Nat := trapDfaMasksList.getD q 0
def trapDfaHas (q i : Nat) : Bool := (trapDfaMaskAt q).testBit i
def trapDfaRepAt (q : Nat) : Nat := (trapDfaRepsPack >>> (16 * q)) % 65536
def trapDfaWtAt (q : Nat) : Nat := (trapDfaWtPack >>> (16 * q)) % 65536

def stepMaskFrom : Nat → Nat → Bool → Nat
  | 0, _, _ => 0
  | k + 1, m, b =>
    let prev := stepMaskFrom k m b
    if m.testBit k && ((trapCodeAt k % 2 == 1) == b) then
      prev ||| (2 ^ succ4At k false false) ||| (2 ^ succ4At k false true)
           ||| (2 ^ succ4At k true false) ||| (2 ^ succ4At k true true)
    else prev

def trapDfaRun : Nat → List Bool → Option Nat
  | q, [] => some q
  | q, b :: bs => match trapDfaStep q b with
    | some q' => trapDfaRun q' bs
    | none => none

def trapDfaAccepts (q : Nat) (w : List Bool) : Bool := (trapDfaRun q w).isSome

def trapDfaWords (q : Nat) : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 =>
    let l0 := match trapDfaStep q false with
      | some q' => (trapDfaWords q' n).map (false :: ·)
      | none => []
    let l1 := match trapDfaStep q true with
      | some q' => (trapDfaWords q' n).map (true :: ·)
      | none => []
    l0 ++ l1

private theorem trap_eq_packed :
    trap = (List.range 829).map (fun i => decode (trapCodeAt i)) := by decide +kernel

private theorem trapSucc4_ok :
    (List.range 829).all (fun i =>
      let w := decode (trapCodeAt i)
      let j00 := succ4At i false false
      let j01 := succ4At i false true
      let j10 := succ4At i true false
      let j11 := succ4At i true true
      j00 < 829 && j01 < 829 && j10 < 829 && j11 < 829 &&
      (encList (step2 w false false) == trapCodeAt j00) &&
      (encList (step2 w false true) == trapCodeAt j01) &&
      (encList (step2 w true false) == trapCodeAt j10) &&
      (encList (step2 w true true) == trapCodeAt j11)) = true := by decide +kernel

private theorem trapDfa_exact_ok :
    (List.range 75).all (fun q =>
      let m := trapDfaMaskAt q
      let rep := trapDfaRepAt q
      rep < 829 && m.testBit rep &&
      ([false, true].all (fun b =>
        let img := stepMaskFrom 829 m b
        match trapDfaStep q b with
        | none => img == 0
        | some q' => q' < 75 && (trapDfaMaskAt q' == img)))) = true := by decide +kernel

private theorem trapDfa_init_all :
    (List.range 829).all (fun i => trapDfaHas 0 i) = true := by decide +kernel

private theorem trapDfa_weights_ok :
    (List.range 75).all (fun q =>
      let wq := trapDfaWtAt q
      let s0 := match trapDfaStep q false with | some q' => trapDfaWtAt q' | none => 0
      let s1 := match trapDfaStep q true with | some q' => trapDfaWtAt q' | none => 0
      1 ≤ wq && 31 * (s0 + s1) ≤ 34 * wq) = true := by decide +kernel

private theorem seg_testBit_encList_loc : ∀ (w : List Bool), seg (fun i => (encList w).testBit i) w.length = w
  | [] => rfl
  | x :: l => by
    have h0 : (encList (x :: l)).testBit 0 = x := by cases x <;> simp [encList] <;> omega
    have h1 : (fun i => (encList (x :: l)).testBit (i + 1)) = (fun i => (encList l).testBit i) := by
      funext i; rw [Nat.testBit_succ]; congr 1; cases x <;> simp [encList] <;> omega
    show (encList (x :: l)).testBit 0 :: seg (fun i => (encList (x :: l)).testBit (i + 1)) l.length = x :: l
    rw [h0, h1, seg_testBit_encList_loc l]

private theorem decode_encList_loc {w : List Bool} (hw : w.length = 16) : decode (encList w) = w := by
  have h := seg_testBit_encList_loc w; rw [hw] at h; exact h

private theorem length_step2_loc (s : List Bool) (hs : s.length = 16) (x1 x2 : Bool) :
    (step2 s x1 x2).length = 16 := by
  rcases s with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨a8, _ | ⟨a9, _ | ⟨a10, _ | ⟨a11, _ | ⟨a12, _ | ⟨a13, _ | ⟨a14, _ | ⟨a15, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp at hs
  rfl

private theorem headD_decode (c : Nat) : (decode c).headD false = (c % 2 == 1) := by
  show c.testBit 0 = (c % 2 == 1)
  rw [Nat.testBit_zero]; cases h : (c % 2 == 1) <;> simp_all

private theorem trapSucc4_spec {i : Nat} (hi : i < 829) (x1 x2 : Bool) :
    succ4At i x1 x2 < 829 ∧
    step2 (decode (trapCodeAt i)) x1 x2 = decode (trapCodeAt (succ4At i x1 x2)) := by
  have h := List.all_eq_true.mp trapSucc4_ok i (List.mem_range.mpr hi)
  dsimp only at h; simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  have hlen : (step2 (decode (trapCodeAt i)) x1 x2).length = 16 := length_step2_loc _ (length_seg _ _) x1 x2
  cases x1 <;> cases x2
  · exact ⟨h.1.1.1.1.1.1.1, (decode_encList_loc hlen).symm.trans (congrArg decode h.1.1.1.2)⟩
  · exact ⟨h.1.1.1.1.1.1.2, (decode_encList_loc hlen).symm.trans (congrArg decode h.1.1.2)⟩
  · exact ⟨h.1.1.1.1.1.2, (decode_encList_loc hlen).symm.trans (congrArg decode h.1.2)⟩
  · exact ⟨h.1.1.1.1.2, (decode_encList_loc hlen).symm.trans (congrArg decode h.2)⟩

private theorem mem_trap_iff_idx (s : List Bool) :
    s ∈ trap ↔ ∃ i, i < 829 ∧ decode (trapCodeAt i) = s := by
  rw [trap_eq_packed, List.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, List.mem_range.mp hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, List.mem_range.mpr hi, rfl⟩

private theorem stepMaskFrom_spec (n m : Nat) (b : Bool) (j : Nat) :
    (stepMaskFrom n m b).testBit j = true ↔
      ∃ k, k < n ∧ m.testBit k = true ∧ (trapCodeAt k % 2 == 1) = b ∧ ∃ x1 x2, succ4At k x1 x2 = j := by
  induction n with
  | zero => simp [stepMaskFrom]
  | succ k ih =>
    simp only [stepMaskFrom]
    by_cases hc : (m.testBit k && ((trapCodeAt k % 2 == 1) == b)) = true
    · simp only [hc, ↓reduceIte, Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow, decide_eq_true_eq]
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      constructor
      · rintro ((((hprev | h00) | h01) | h10) | h11)
        · obtain ⟨u, hu, hm, hb, x1, x2, hs⟩ := ih.mp hprev; exact ⟨u, by omega, hm, hb, x1, x2, hs⟩
        · exact ⟨k, by omega, hc.1, hc.2, false, false, h00⟩
        · exact ⟨k, by omega, hc.1, hc.2, false, true, h01⟩
        · exact ⟨k, by omega, hc.1, hc.2, true, false, h10⟩
        · exact ⟨k, by omega, hc.1, hc.2, true, true, h11⟩
      · rintro ⟨u, hu, hm, hb, x1, x2, hs⟩
        by_cases huk : u = k
        · subst huk; subst hs; cases x1 <;> cases x2 <;> simp
        · left; left; left; left; exact ih.mpr ⟨u, by omega, hm, hb, x1, x2, hs⟩
    · have hfalse : (m.testBit k && ((trapCodeAt k % 2 == 1) == b)) = false := Bool.eq_false_iff.mpr hc
      simp only [hfalse, Bool.false_eq_true, ↓reduceIte]
      constructor
      · intro hp; obtain ⟨u, hu, hm, hb, x1, x2, hs⟩ := ih.mp hp; exact ⟨u, by omega, hm, hb, x1, x2, hs⟩
      · rintro ⟨u, hu, hm, hb, x1, x2, hs⟩
        have huk : u ≠ k := fun e => hc (by subst e; simp [hm, hb])
        exact ih.mpr ⟨u, by omega, hm, hb, x1, x2, hs⟩

private theorem trapDfa_step_lt {q q' : Nat} {b : Bool} (hq : q < 75) (hst : trapDfaStep q b = some q') : q' < 75 := by
  have h := List.all_eq_true.mp trapDfa_exact_ok q (List.mem_range.mpr hq)
  dsimp only at h; simp only [Bool.and_eq_true] at h
  have hb := List.all_eq_true.mp h.2 b (by cases b <;> simp)
  rw [hst] at hb; simp only [Bool.and_eq_true, decide_eq_true_eq] at hb; exact hb.1

private theorem trapDfa_sound_step {q i : Nat} (hq : q < 75) (hi : i < 829)
    (hm : trapDfaHas q i = true) (x1 x2 : Bool) :
    ∃ q', q' < 75 ∧ trapDfaStep q ((decode (trapCodeAt i)).headD false) = some q' ∧
      trapDfaHas q' (succ4At i x1 x2) = true := by
  let b := (decode (trapCodeAt i)).headD false
  have h := List.all_eq_true.mp trapDfa_exact_ok q (List.mem_range.mpr hq)
  dsimp only at h; simp only [Bool.and_eq_true] at h
  have hb := List.all_eq_true.mp h.2 b (by cases b <;> simp)
  have himg : (stepMaskFrom 829 (trapDfaMaskAt q) b).testBit (succ4At i x1 x2) = true :=
    (stepMaskFrom_spec 829 (trapDfaMaskAt q) b _).mpr ⟨i, hi, hm, (headD_decode _).symm, x1, x2, rfl⟩
  cases hst : trapDfaStep q b with
  | none => rw [hst] at hb; simp only [beq_iff_eq] at hb; rw [hb] at himg; simp at himg
  | some q' =>
    rw [hst] at hb; simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hb
    exact ⟨q', hb.1, rfl, by unfold trapDfaHas; rw [hb.2]; exact himg⟩

private theorem trapDfa_sound_aux (inp : List (Bool × Bool)) :
    ∀ q i, q < 75 → i < 829 → trapDfaHas q i = true →
      ∃ q', q' < 75 ∧ trapDfaRun q (emitPath (decode (trapCodeAt i)) inp) = some q' := by
  induction inp with
  | nil => intro q i hq _ _; exact ⟨q, hq, rfl⟩
  | cons p rest ih =>
    intro q i hq hi hm; rcases p with ⟨x1, x2⟩
    obtain ⟨q', hq', hst, hm'⟩ := trapDfa_sound_step hq hi hm x1 x2
    obtain ⟨hnext_lt, hnext_eq⟩ := trapSucc4_spec hi x1 x2
    simp only [emitPath, trapDfaRun, hst, hnext_eq]
    exact ih q' (succ4At i x1 x2) hq' hnext_lt hm'

private theorem trapDfa_complete_step {q q' j : Nat} {b : Bool}
    (hq : q < 75) (hst : trapDfaStep q b = some q') (_hj : j < 829)
    (hm' : trapDfaHas q' j = true) :
    q' < 75 ∧ ∃ i x1 x2, i < 829 ∧ trapDfaHas q i = true ∧
      (decode (trapCodeAt i)).headD false = b ∧ succ4At i x1 x2 = j := by
  have h := List.all_eq_true.mp trapDfa_exact_ok q (List.mem_range.mpr hq)
  dsimp only at h; simp only [Bool.and_eq_true] at h
  have hb := List.all_eq_true.mp h.2 b (by cases b <;> simp)
  rw [hst] at hb; simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hb
  unfold trapDfaHas at hm'; rw [hb.2] at hm'
  obtain ⟨i, hi, hmi, hbi, x1, x2, hsu⟩ := (stepMaskFrom_spec 829 (trapDfaMaskAt q) b j).mp hm'
  exact ⟨hb.1, i, x1, x2, hi, hmi, (headD_decode _).trans hbi, hsu⟩

private theorem trapDfa_complete_aux (w : List Bool) :
    ∀ q q', q < 75 → trapDfaRun q w = some q' →
      q' < 75 ∧ ∀ j, j < 829 → trapDfaHas q' j = true →
        ∃ i, i < 829 ∧ trapDfaHas q i = true ∧
          ∃ inp : List (Bool × Bool), inp.length = w.length ∧
            emitPath (decode (trapCodeAt i)) inp = w ∧
            runPath (decode (trapCodeAt i)) inp = decode (trapCodeAt j) := by
  induction w with
  | nil =>
    intro q q' hq hrun; simp only [trapDfaRun, Option.some.injEq] at hrun; subst hrun
    exact ⟨hq, fun j hj hm => ⟨j, hj, hm, [], rfl, rfl, rfl⟩⟩
  | cons b bs ih =>
    intro q q' hq hrun; simp only [trapDfaRun] at hrun
    cases hst : trapDfaStep q b with
    | none => rw [hst] at hrun; cases hrun
    | some q1 =>
      rw [hst] at hrun
      obtain ⟨hq', hrec⟩ := ih q1 q' (trapDfa_step_lt hq hst) hrun
      refine ⟨hq', fun j hj hm' => ?_⟩
      obtain ⟨i1, hi1, hm1, inp', hlen', hemit', hrun'⟩ := hrec j hj hm'
      obtain ⟨_, i0, x1, x2, hi0, hm0, hhead0, hsucc0⟩ := trapDfa_complete_step hq hst hi1 hm1
      have hstep_eq : step2 (decode (trapCodeAt i0)) x1 x2 = decode (trapCodeAt i1) := by
        have hsp := (trapSucc4_spec hi0 x1 x2).2; rwa [hsucc0] at hsp
      refine ⟨i0, hi0, hm0, (x1, x2) :: inp', by simp [hlen'], ?_, ?_⟩
      · simp only [emitPath, hhead0, hstep_eq, hemit']
      · simp only [runPath, hstep_eq, hrun']

theorem trapPath_iff_trapDfaAccepts (w : List Bool) :
    TrapPath w ↔ trapDfaAccepts 0 w = true := by
  constructor
  · rintro ⟨s, hs, inp, hlen, hemit⟩
    obtain ⟨i, hi, rfl⟩ := (mem_trap_iff_idx s).mp hs
    have hm0 : trapDfaHas 0 i = true := List.all_eq_true.mp trapDfa_init_all i (List.mem_range.mpr hi)
    obtain ⟨q', _, hrun⟩ := trapDfa_sound_aux inp 0 i (by decide) hi hm0
    rw [hemit] at hrun; simp [trapDfaAccepts, hrun]
  · intro hacc
    unfold trapDfaAccepts at hacc
    cases hrun : trapDfaRun 0 w with
    | none => rw [hrun] at hacc; exact Bool.noConfusion hacc
    | some q' =>
      obtain ⟨hq', hrec⟩ := trapDfa_complete_aux w 0 q' (by decide) hrun
      have hrep := List.all_eq_true.mp trapDfa_exact_ok q' (List.mem_range.mpr hq')
      dsimp only at hrep; simp only [Bool.and_eq_true, decide_eq_true_eq] at hrep
      obtain ⟨i0, hi0, _, inp, hlen, hemit, _⟩ := hrec (trapDfaRepAt q') hrep.1.1 hrep.1.2
      exact ⟨decode (trapCodeAt i0), (mem_trap_iff_idx _).mpr ⟨i0, hi0, rfl⟩, inp, hlen, hemit⟩

private theorem step2_mem_trap {w : List Bool} (hw : w ∈ trap) (x1 x2 : Bool) : step2 w x1 x2 ∈ trap := by
  obtain ⟨i, hi, rfl⟩ := (mem_trap_iff_idx w).mp hw
  obtain ⟨hj, heq⟩ := trapSucc4_spec hi x1 x2
  exact (mem_trap_iff_idx _).mpr ⟨succ4At i x1 x2, hj, heq.symm⟩

theorem trap_u_accepted_by_trapDfa (R : Nat → Bool) {t0 s0 : Nat} (h0 : t0 % 2 = 1)
    (hw : win R t0 ∈ trap) (hs0 : t0 ≤ 2 * s0 + 1) (n : Nat) :
    trapDfaAccepts 0 ((List.range n).map (fun k => Rule30PeriodTwoSideways.u R (s0 + k))) = true := by
  rw [← trapPath_iff_trapDfaAccepts]
  have hstay_loc : ∀ d, win R (t0 + 2 * d) ∈ trap := by
    intro d; induction d with
    | zero => simpa using hw
    | succ d ih =>
      obtain ⟨x1, x2, hst⟩ := win_step2 R (t := t0 + 2 * d) (by omega)
      rw [show t0 + 2 * (d + 1) = t0 + 2 * d + 2 by omega, hst]
      exact step2_mem_trap ih x1 x2
  have hwin : win R (2 * s0 + 1) ∈ trap := by
    have h := hstay_loc ((2 * s0 + 1 - t0) / 2)
    rwa [show t0 + 2 * ((2 * s0 + 1 - t0) / 2) = 2 * s0 + 1 by omega] at h
  have hbuild : ∀ m s, win R (2 * s + 1) ∈ trap →
      ∃ inp : List (Bool × Bool), inp.length = m ∧
        emitPath (win R (2 * s + 1)) inp = (List.range m).map (fun k => Rule30PeriodTwoSideways.u R (s + k)) := by
    intro m; induction m with
    | zero => intro s _; exact ⟨[], rfl, rfl⟩
    | succ m ih =>
      intro s hws
      obtain ⟨x1, x2, hst⟩ := win_step2 R (t := 2 * s + 1) (by omega)
      have hstep_eq : step2 (win R (2 * s + 1)) x1 x2 = win R (2 * (s + 1) + 1) := by
        rw [show 2 * (s + 1) + 1 = 2 * s + 1 + 2 by omega]; exact hst.symm
      have hnext : win R (2 * (s + 1) + 1) ∈ trap := hstep_eq ▸ step2_mem_trap hws x1 x2
      obtain ⟨inp', hlen', hemit'⟩ := ih (s + 1) hnext
      refine ⟨(x1, x2) :: inp', by simp [hlen'], ?_⟩
      rw [emitPath, hstep_eq, hemit', List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      apply List.map_congr_left; intro k _; simp only [Function.comp_apply]; congr 1; omega
  obtain ⟨inp, hlen, hemit⟩ := hbuild n s0 hwin
  exact ⟨win R (2 * s0 + 1), hwin, inp, by simpa using hlen, hemit⟩

theorem mem_trapDfaWords_iff (n : Nat) :
    ∀ q w, w ∈ trapDfaWords q n ↔ w.length = n ∧ trapDfaAccepts q w = true := by
  induction n with
  | zero => intro q w; cases w <;> simp [trapDfaWords, trapDfaAccepts, trapDfaRun]
  | succ n ih =>
    intro q w; constructor
    · intro hw; simp only [trapDfaWords, List.mem_append] at hw
      rcases hw with h0 | h1
      · cases hst : trapDfaStep q false with
        | none => rw [hst] at h0; simp at h0
        | some q' => rw [hst] at h0; obtain ⟨u, hu, rfl⟩ := List.mem_map.mp h0; obtain ⟨hl, ha⟩ := (ih q' u).mp hu; exact ⟨by simp [hl], by simp [trapDfaAccepts, trapDfaRun, hst]; exact ha⟩
      · cases hst : trapDfaStep q true with
        | none => rw [hst] at h1; simp at h1
        | some q' => rw [hst] at h1; obtain ⟨u, hu, rfl⟩ := List.mem_map.mp h1; obtain ⟨hl, ha⟩ := (ih q' u).mp hu; exact ⟨by simp [hl], by simp [trapDfaAccepts, trapDfaRun, hst]; exact ha⟩
    · rintro ⟨hlen, hacc⟩; cases w with
      | nil => simp at hlen
      | cons b bs =>
        simp only [trapDfaAccepts, trapDfaRun] at hacc
        cases hst : trapDfaStep q b with
        | none => rw [hst] at hacc; simp at hacc
        | some q' =>
          rw [hst] at hacc; have hm := (ih q' bs).mpr ⟨by simpa using hlen, hacc⟩
          simp only [trapDfaWords, List.mem_append]; cases b
          · left; rw [hst]; exact List.mem_map_of_mem hm
          · right; rw [hst]; exact List.mem_map_of_mem hm

private theorem trapDfa_weighted_bound (n : Nat) :
    ∀ q, q < 75 → (trapDfaWords q n).length * 31 ^ n ≤ trapDfaWtAt q * 34 ^ n := by
  induction n with
  | zero =>
    intro q hq
    have h := List.all_eq_true.mp trapDfa_weights_ok q (List.mem_range.mpr hq)
    dsimp only at h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    simp [trapDfaWords]; exact h.1
  | succ n ih =>
    intro q hq
    have hw := List.all_eq_true.mp trapDfa_weights_ok q (List.mem_range.mpr hq)
    dsimp only at hw; simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
    have h0 : (match trapDfaStep q false with | some q' => (trapDfaWords q' n).length | none => 0) * 31 ^ n ≤
        (match trapDfaStep q false with | some q' => trapDfaWtAt q' | none => 0) * 34 ^ n := by
      cases hst : trapDfaStep q false with | none => simp | some q' => exact ih q' (trapDfa_step_lt hq hst)
    have h1 : (match trapDfaStep q true with | some q' => (trapDfaWords q' n).length | none => 0) * 31 ^ n ≤
        (match trapDfaStep q true with | some q' => trapDfaWtAt q' | none => 0) * 34 ^ n := by
      cases hst : trapDfaStep q true with | none => simp | some q' => exact ih q' (trapDfa_step_lt hq hst)
    have hlen : (trapDfaWords q (n + 1)).length =
        (match trapDfaStep q false with | some q' => (trapDfaWords q' n).length | none => 0) +
        (match trapDfaStep q true with | some q' => (trapDfaWords q' n).length | none => 0) := by
      simp only [trapDfaWords, List.length_append]; congr 1 <;> cases trapDfaStep q _ <;> simp
    rw [hlen, Nat.pow_succ, Nat.pow_succ]
    calc ((match trapDfaStep q false with | some q' => (trapDfaWords q' n).length | none => 0) +
          (match trapDfaStep q true with | some q' => (trapDfaWords q' n).length | none => 0)) * (31 ^ n * 31)
        = ((match trapDfaStep q false with | some q' => (trapDfaWords q' n).length | none => 0) * 31 ^ n +
           (match trapDfaStep q true with | some q' => (trapDfaWords q' n).length | none => 0) * 31 ^ n) * 31 := by
          rw [← Nat.mul_assoc, Nat.add_mul]
      _ ≤ ((match trapDfaStep q false with | some q' => trapDfaWtAt q' | none => 0) * 34 ^ n +
           (match trapDfaStep q true with | some q' => trapDfaWtAt q' | none => 0) * 34 ^ n) * 31 :=
          Nat.mul_le_mul_right 31 (Nat.add_le_add h0 h1)
      _ = (31 * ((match trapDfaStep q false with | some q' => trapDfaWtAt q' | none => 0) +
                 (match trapDfaStep q true with | some q' => trapDfaWtAt q' | none => 0))) * 34 ^ n := by
          rw [← Nat.add_mul, Nat.mul_right_comm, Nat.mul_comm _ 31]
      _ ≤ (34 * trapDfaWtAt q) * 34 ^ n := Nat.mul_le_mul_right _ hw.2
      _ = trapDfaWtAt q * (34 ^ n * 34) := by rw [Nat.mul_comm 34 _, Nat.mul_assoc, Nat.mul_comm 34 (34 ^ n)]

theorem trapDfa_wordCount_le_34_31 (n : Nat) :
    (trapDfaWords 0 n).length * 31 ^ n ≤ 2972 * 34 ^ n := by
  have h0 : trapDfaWtAt 0 = 2972 := by decide +kernel
  rw [← h0]; exact trapDfa_weighted_bound n 0 (by decide)

def trapLoopInp0 : List (Bool × Bool) := [(false,true), (false,false), (false,false), (false,false), (false,false), (false,false), (false,false), (false,true), (false,true), (false,false), (true,false), (false,false), (true,false), (false,false), (false,false), (true,false), (false,false), (false,false), (false,false), (false,false), (false,false), (false,false), (false,false)]
def trapLoopInp1 : List (Bool × Bool) := [(true,false), (false,false), (false,false), (true,false), (false,true), (false,true), (false,false), (false,false), (false,false), (false,false), (true,false), (false,false), (false,false), (false,false), (false,false), (true,false), (true,false), (false,false), (false,false), (true,false), (false,false), (false,false), (false,false)]
def trapLoopTile0 : List Bool := emitPath (decode 1960) trapLoopInp0
def trapLoopTile1 : List Bool := emitPath (decode 1960) trapLoopInp1

private theorem trapLoops_check :
    runPath (decode 1960) trapLoopInp0 = decode 1960 ∧
    runPath (decode 1960) trapLoopInp1 = decode 1960 ∧
    trapLoopTile0.length = 23 ∧ trapLoopTile1.length = 23 ∧
    trapLoopTile0 ≠ trapLoopTile1 ∧
    trapCodeAt 66 = 1960 := by decide +kernel

def trapCode (bs : List Bool) : List Bool :=
  bs.flatMap (fun b => if b then trapLoopTile1 else trapLoopTile0)

private theorem emitPath_append (s : List Bool) (a b : List (Bool × Bool)) :
    emitPath s (a ++ b) = emitPath s a ++ emitPath (runPath s a) b := by
  induction a generalizing s with | nil => rfl | cons p rest ih => rcases p with ⟨x1, x2⟩; simp [emitPath, runPath, ih]

private theorem runPath_append (s : List Bool) (a b : List (Bool × Bool)) :
    runPath s (a ++ b) = runPath (runPath s a) b := by
  induction a generalizing s with | nil => rfl | cons p rest ih => rcases p with ⟨x1, x2⟩; simp [runPath, ih]

private theorem trapCode_in_trap (bs : List Bool) :
    (trapCode bs).length = 23 * bs.length ∧
    emitPath (decode 1960) (bs.flatMap (fun b => if b then trapLoopInp1 else trapLoopInp0)) = trapCode bs ∧
    runPath (decode 1960) (bs.flatMap (fun b => if b then trapLoopInp1 else trapLoopInp0)) = decode 1960 ∧
    (bs.flatMap (fun b => if b then trapLoopInp1 else trapLoopInp0)).length = 23 * bs.length := by
  induction bs with
  | nil => simp [trapCode, emitPath, runPath]
  | cons b bs ih =>
    obtain ⟨hl, he, hr, hil⟩ := ih
    have h0 := trapLoops_check
    have hcons : trapCode (b :: bs) = (if b then trapLoopTile1 else trapLoopTile0) ++ trapCode bs := rfl
    cases b
    · refine ⟨by rw [hcons, List.length_append, hl, List.length_cons]; simp [h0.2.2.1]; omega, ?_, ?_, ?_⟩
      · rw [hcons]; simp only [List.flatMap_cons, Bool.false_eq_true, ↓reduceIte, emitPath_append, h0.1, he]; rfl
      · simp only [List.flatMap_cons, Bool.false_eq_true, ↓reduceIte, runPath_append, h0.1, hr]
      · simp only [List.flatMap_cons, Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_cons, hil]; have : trapLoopInp0.length = 23 := rfl; omega
    · refine ⟨by rw [hcons, List.length_append, hl, List.length_cons]; simp [h0.2.2.2.1]; omega, ?_, ?_, ?_⟩
      · rw [hcons]; simp only [List.flatMap_cons, ↓reduceIte, emitPath_append, h0.2.1, he]; rfl
      · simp only [List.flatMap_cons, ↓reduceIte, runPath_append, h0.2.1, hr]
      · simp only [List.flatMap_cons, ↓reduceIte, List.length_append, List.length_cons, hil]; have : trapLoopInp1.length = 23 := rfl; omega

theorem list_append_eq_of_length_eq {α : Type} {a b c d : List α}
    (hl : a.length = c.length) (h : a ++ b = c ++ d) : a = c ∧ b = d := by
  induction a generalizing c with
  | nil => cases c with | nil => exact ⟨rfl, h⟩ | cons _ _ => simp at hl
  | cons x xs ih =>
    cases c with | nil => simp at hl | cons y ys =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := ih (by simpa using hl) h.2; exact ⟨by rw [h.1, h1], h2⟩

private theorem trapCode_injective : ∀ (a b : List Bool), a.length = b.length → trapCode a = trapCode b → a = b
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | x :: xs, y :: ys, hlen, heq => by
    have h0 := trapLoops_check
    have htx : (if x then trapLoopTile1 else trapLoopTile0).length = 23 := by cases x <;> simp [h0.2.2.1, h0.2.2.2.1]
    have hty : (if y then trapLoopTile1 else trapLoopTile0).length = 23 := by cases y <;> simp [h0.2.2.1, h0.2.2.2.1]
    simp only [trapCode, List.flatMap_cons] at heq
    obtain ⟨hhd, htl⟩ := list_append_eq_of_length_eq (htx.trans hty.symm) heq
    have hxy : x = y := by
      cases x <;> cases y
      · rfl
      · exact absurd hhd h0.2.2.2.2.1
      · exact absurd hhd.symm h0.2.2.2.2.1
      · rfl
    rw [hxy, trapCode_injective xs ys (by simpa using hlen) htl]

private def allBoolLists : Nat → List (List Bool)
  | 0 => [[]]
  | k + 1 => (allBoolLists k).map (false :: ·) ++ (allBoolLists k).map (true :: ·)

private theorem allBoolLists_props (k : Nat) :
    (allBoolLists k).length = 2 ^ k ∧ (allBoolLists k).Nodup ∧ ∀ bs ∈ allBoolLists k, bs.length = k := by
  induction k with
  | zero => simp [allBoolLists]
  | succ k ih =>
    obtain ⟨hl, hn, hmem⟩ := ih
    refine ⟨by simp [allBoolLists, hl, Nat.pow_succ]; omega, ?_, ?_⟩
    · apply List.nodup_append.mpr
      refine ⟨List.Pairwise.map (false :: ·) (fun _ _ hne heq => hne (List.cons.inj heq).2) hn, List.Pairwise.map (true :: ·) (fun _ _ hne heq => hne (List.cons.inj heq).2) hn, ?_⟩
      intro x hx y hy hxy; subst hxy; obtain ⟨u, _, rfl⟩ := List.mem_map.mp hx; obtain ⟨v, _, hv⟩ := List.mem_map.mp hy; cases hv
    · intro bs hbs; simp only [allBoolLists, List.mem_append, List.mem_map] at hbs
      rcases hbs with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩ <;> simp [hmem u hu]

private theorem nodup_length_le_of_subset {α : Type} [DecidableEq α] : ∀ (xs ys : List α), xs.Nodup → (∀ x ∈ xs, x ∈ ys) → xs.length ≤ ys.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, ys, hnd, hsub => by
    obtain ⟨hx_not, hnd_xs⟩ := List.nodup_cons.mp hnd
    have hmem : x ∈ ys := hsub x List.mem_cons_self
    have hrec := nodup_length_le_of_subset xs (ys.erase x) hnd_xs (fun z hz =>
      (List.mem_erase_of_ne (fun heq => hx_not (by subst heq; exact hz))).mpr (hsub z (List.mem_cons_of_mem _ hz)))
    have her : (ys.erase x).length + 1 = ys.length := by
      rw [List.length_erase_of_mem hmem]; have hpos : 0 < ys.length := List.length_pos_of_mem hmem; omega
    simp only [List.length_cons]; omega

theorem trap_free_binary_code_lower_bound (k : Nat) :
    2 ^ k ≤ (trapDfaWords 0 (23 * k)).length := by
  obtain ⟨hlen, hnd, hmemk⟩ := allBoolLists_props k
  let coded := (allBoolLists k).map trapCode
  have hnd_coded : coded.Nodup := by
    have aux : ∀ (l : List (List Bool)), l.Nodup → (∀ bs ∈ l, bs.length = k) → (l.map trapCode).Nodup := by
      intro l; induction l with
      | nil => intro _ _; exact List.nodup_nil
      | cons a rest ih =>
        intro hnd_l hmk_l; obtain ⟨ha, hnd_r⟩ := List.nodup_cons.mp hnd_l
        apply List.nodup_cons.mpr; refine ⟨?_, ih hnd_r (fun z hz => hmk_l z (List.mem_cons_of_mem _ hz))⟩
        intro hmem_c; obtain ⟨b, hb, hcb⟩ := List.mem_map.mp hmem_c
        exact ha ((trapCode_injective b a ((hmk_l b (List.mem_cons_of_mem _ hb)).trans (hmk_l a List.mem_cons_self).symm) hcb) ▸ hb)
    exact aux (allBoolLists k) hnd hmemk
  have hsub : ∀ w ∈ coded, w ∈ trapDfaWords 0 (23 * k) := by
    intro w hw; obtain ⟨bs, hbs, rfl⟩ := List.mem_map.mp hw
    have hbsk : bs.length = k := hmemk bs hbs
    obtain ⟨hcl, hce, _, hcil⟩ := trapCode_in_trap bs
    have htp : TrapPath (trapCode bs) :=
      ⟨decode 1960, (mem_trap_iff_idx _).mpr ⟨66, by decide, by rw [trapLoops_check.2.2.2.2.2]⟩,
       bs.flatMap (fun b => if b then trapLoopInp1 else trapLoopInp0), by rw [hcil, hcl], hce⟩
    exact (mem_trapDfaWords_iff (23 * k) 0 (trapCode bs)).mpr ⟨by rw [hcl, hbsk], (trapPath_iff_trapDfaAccepts _).mp htp⟩
  have hle := nodup_length_le_of_subset coded (trapDfaWords 0 (23 * k)) hnd_coded hsub
  simpa [coded, hlen] using hle

def zTrace (y : Nat) : Nat → List Bool
  | 0 => []
  | H + 1 => y.testBit 0 :: zTrace (Rule30ZeroBoundary.IntegerForm.F y) H

def zTraceInX : List Bool → Bool
  | [] => true
  | [_] => false
  | e :: _ :: rest => (!e) && zTraceInX rest

def zTraceOddNot : List Bool → List Bool
  | [] => []
  | [_] => []
  | _ :: o :: rest => (!o) :: zTraceOddNot rest

def trapSeeds (n : Nat) : List Nat :=
  (List.range (2 ^ (2 * n))).filter (fun y => zTraceInX (zTrace y (2 * n)) && trapDfaAccepts 0 (zTraceOddNot (zTrace y (2 * n))))

private theorem zTrace_F_bit_flip (t : Nat) : ∀ y1 y2 m : Nat,
    (∀ j, j < m + t → y1.testBit j = y2.testBit j) → y1.testBit (m + t) = !(y2.testBit (m + t)) →
    (∀ j, j < m → (Rule30ZeroBoundary.IntegerForm.iter Rule30ZeroBoundary.IntegerForm.F t y1).testBit j =
                  (Rule30ZeroBoundary.IntegerForm.iter Rule30ZeroBoundary.IntegerForm.F t y2).testBit j) ∧
    (Rule30ZeroBoundary.IntegerForm.iter Rule30ZeroBoundary.IntegerForm.F t y1).testBit m =
      !((Rule30ZeroBoundary.IntegerForm.iter Rule30ZeroBoundary.IntegerForm.F t y2).testBit m) := by
  induction t with
  | zero => intro y1 y2 m hag hfl; simpa [Rule30ZeroBoundary.IntegerForm.iter] using ⟨hag, hfl⟩
  | succ t ih =>
    intro y1 y2 m hag hfl
    have hs := ih y1 y2 (m + 1) (fun j hj => hag j (by omega)) (by simpa [show m + 1 + t = m + (t + 1) by omega] using hfl)
    refine ⟨fun j hj => ?_, ?_⟩
    · change (Rule30ZeroBoundary.IntegerForm.F _).testBit j = (Rule30ZeroBoundary.IntegerForm.F _).testBit j
      cases j with
      | zero => rw [Rule30ZeroBoundary.IntegerForm.testBit_F_zero, Rule30ZeroBoundary.IntegerForm.testBit_F_zero, hs.1 0 (by omega), hs.1 1 (by omega)]
      | succ k => rw [Rule30ZeroBoundary.IntegerForm.testBit_F_succ, Rule30ZeroBoundary.IntegerForm.testBit_F_succ, hs.1 k (by omega), hs.1 (k + 1) (by omega), hs.1 (k + 2) (by omega)]
    · change (Rule30ZeroBoundary.IntegerForm.F _).testBit m = !((Rule30ZeroBoundary.IntegerForm.F _).testBit m)
      cases m with
      | zero =>
        rw [Rule30ZeroBoundary.IntegerForm.testBit_F_zero, Rule30ZeroBoundary.IntegerForm.testBit_F_zero, hs.1 0 (by omega), hs.2]
        cases (Rule30ZeroBoundary.IntegerForm.iter Rule30ZeroBoundary.IntegerForm.F t y2).testBit 0 <;>
          cases (Rule30ZeroBoundary.IntegerForm.iter Rule30ZeroBoundary.IntegerForm.F t y2).testBit 1 <;> rfl
      | succ k =>
        rw [Rule30ZeroBoundary.IntegerForm.testBit_F_succ, Rule30ZeroBoundary.IntegerForm.testBit_F_succ, hs.1 k (by omega), hs.1 (k + 1) (by omega), hs.2]
        cases (Rule30ZeroBoundary.IntegerForm.iter Rule30ZeroBoundary.IntegerForm.F t y2).testBit k <;>
          cases (Rule30ZeroBoundary.IntegerForm.iter Rule30ZeroBoundary.IntegerForm.F t y2).testBit (k + 1) <;>
            cases (Rule30ZeroBoundary.IntegerForm.iter Rule30ZeroBoundary.IntegerForm.F t y2).testBit (k + 2) <;> rfl

private theorem zTrace_getD (H : Nat) : ∀ y t, t < H →
    (zTrace y H).getD t false = (Rule30ZeroBoundary.IntegerForm.iter Rule30ZeroBoundary.IntegerForm.F t y).testBit 0 := by
  induction H with
  | zero => intro _ _ ht; omega
  | succ H ih =>
    intro y t ht; cases t with
    | zero => rfl
    | succ t =>
      have hiter : ∀ k z, Rule30ZeroBoundary.IntegerForm.iter Rule30ZeroBoundary.IntegerForm.F (k + 1) z =
          Rule30ZeroBoundary.IntegerForm.iter Rule30ZeroBoundary.IntegerForm.F k (Rule30ZeroBoundary.IntegerForm.F z) := by
        intro k z; induction k with | zero => rfl | succ k ihk => show Rule30ZeroBoundary.IntegerForm.F _ = Rule30ZeroBoundary.IntegerForm.F _; rw [ihk]
      rw [hiter t y]; exact ih (Rule30ZeroBoundary.IntegerForm.F y) t (by omega)

private theorem zTrace_injective {H y1 y2 : Nat} (h1 : y1 < 2 ^ H) (h2 : y2 < 2 ^ H)
    (heq : zTrace y1 H = zTrace y2 H) : y1 = y2 := by
  apply Nat.eq_of_testBit_eq; intro k
  by_cases hk : k < H
  · induction k using Nat.strongRecOn with
    | ind k ih =>
      cases hb1 : y1.testBit k <;> cases hb2 : y2.testBit k
      · rfl
      · have hfl := (zTrace_F_bit_flip k y1 y2 0 (fun j hj => ih j (by omega) (by omega)) (by simp [hb1, hb2])).2
        have htr : (zTrace y1 H).getD k false = (zTrace y2 H).getD k false := congrArg (fun l => l.getD k false) heq
        rw [zTrace_getD H y1 k hk, zTrace_getD H y2 k hk, hfl] at htr
        cases (Rule30ZeroBoundary.IntegerForm.iter Rule30ZeroBoundary.IntegerForm.F k y2).testBit 0 <;> simp at htr
      · have hfl := (zTrace_F_bit_flip k y1 y2 0 (fun j hj => ih j (by omega) (by omega)) (by simp [hb1, hb2])).2
        have htr : (zTrace y1 H).getD k false = (zTrace y2 H).getD k false := congrArg (fun l => l.getD k false) heq
        rw [zTrace_getD H y1 k hk, zTrace_getD H y2 k hk, hfl] at htr
        cases (Rule30ZeroBoundary.IntegerForm.iter Rule30ZeroBoundary.IntegerForm.F k y2).testBit 0 <;> simp at htr
      · rfl
  · have hpow : 2 ^ H ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

private theorem zTrace_eq_of_inX_oddNot : ∀ (a b : List Bool),
    zTraceInX a = true → zTraceInX b = true → zTraceOddNot a = zTraceOddNot b → a = b
  | [], [], _, _, _ => rfl
  | [_], _, ha, _, _ => by simp [zTraceInX] at ha
  | _, [_], _, hb, _ => by simp [zTraceInX] at hb
  | [], _ :: _ :: _, _, _, h => by simp [zTraceOddNot] at h
  | _ :: _ :: _, [], _, _, h => by simp [zTraceOddNot] at h
  | e1 :: o1 :: r1, e2 :: o2 :: r2, ha, hb, h => by
    simp only [zTraceInX, Bool.and_eq_true, Bool.not_eq_true'] at ha hb
    simp only [zTraceOddNot, List.cons.injEq] at h
    have ho : o1 = o2 := by cases o1 <;> cases o2 <;> simp_all
    rw [ha.1, hb.1, ho, zTrace_eq_of_inX_oddNot r1 r2 ha.2 hb.2 h.2]

private theorem zTraceOddNot_length (y n : Nat) : (zTraceOddNot (zTrace y (2 * n))).length = n := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih => rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]; simp only [zTrace, zTraceOddNot, List.length_cons, ih]

theorem trap_zeroBoundary_seed_decay (n : Nat) :
    (trapSeeds n).length * 31 ^ n ≤ 2972 * 34 ^ n := by
  let f : Nat → List Bool := fun y => zTraceOddNot (zTrace y (2 * n))
  have hnd_s : (trapSeeds n).Nodup := (List.nodup_range).filter _
  have hnd_img : ((trapSeeds n).map f).Nodup := by
    have aux : ∀ (l : List Nat), l.Nodup → (∀ y ∈ l, y < 2 ^ (2 * n) ∧ zTraceInX (zTrace y (2 * n)) = true) → (l.map f).Nodup := by
      intro l; induction l with
      | nil => intro _ _; exact List.nodup_nil
      | cons a rest ih =>
        intro hnd_l hok; obtain ⟨ha, hnd_r⟩ := List.nodup_cons.mp hnd_l
        apply List.nodup_cons.mpr; refine ⟨?_, ih hnd_r (fun z hz => hok z (List.mem_cons_of_mem _ hz))⟩
        intro hmem; obtain ⟨b, hb, hfb⟩ := List.mem_map.mp hmem
        have h1 := hok b (List.mem_cons_of_mem _ hb); have h2 := hok a List.mem_cons_self
        exact ha ((zTrace_injective h1.1 h2.1 (zTrace_eq_of_inX_oddNot _ _ h1.2 h2.2 hfb)) ▸ hb)
    apply aux (trapSeeds n) hnd_s
    intro y hy; simp only [trapSeeds, List.mem_filter, List.mem_range, Bool.and_eq_true] at hy; exact ⟨hy.1, hy.2.1⟩
  have hsub : ∀ w ∈ (trapSeeds n).map f, w ∈ trapDfaWords 0 n := by
    intro w hw; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hw
    simp only [trapSeeds, List.mem_filter, Bool.and_eq_true] at hy
    exact (mem_trapDfaWords_iff n 0 (f y)).mpr ⟨zTraceOddNot_length y n, hy.2.2⟩
  have hle : (trapSeeds n).length ≤ (trapDfaWords 0 n).length := by
    simpa [List.length_map] using nodup_length_le_of_subset ((trapSeeds n).map f) (trapDfaWords 0 n) hnd_img hsub
  exact Nat.le_trans (Nat.mul_le_mul_right _ hle) (trapDfa_wordCount_le_34_31 n)

end Ruliology.CellularAutomata.Rule30GateTrap
