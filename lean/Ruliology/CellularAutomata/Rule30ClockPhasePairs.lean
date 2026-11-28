module

public import Ruliology.CellularAutomata.Rule30RelaxedWindows

/-!
# An isolated black cell within seven wheels after a first clock loss

On a recurrent strip (`Recurrence d`, `PrefixClocks d`) with a first clock loss `FirstLoss d a e` and next permanently
white wheel `NextWhite d a b`:

* `five_ticks`: every five consecutive ticks contain one at which wheels `j`, `j + 1`, `j + 2` read white, black,
  white, with `a ≤ j` and `j + 2 ≤ min(b, a + 7)`, for every `e` and from every tick.
* `three_pairs`: among three consecutive ticks and their translates by `2 ^ e`, one has such a singleton by
  `min(b, a + 6)`.
* `cofinal_singletons`: on a strip with a black edge, one fixed tick of any five sees such singletons at first
  losses beyond every depth.

The proof follows the driver wheel `a + 1` from `firstLoss_cascade_and_immediate_catch`: a fall of the driver gives a
singleton at the ending tick. Two black readings or three white readings make a wheel toggle beside a white
one, forcing a singleton at its fall or one tick later at the next wheel (`toggle_catch`). With `Rule30FirstLossBounds` the catalogue already gives a reset in every fifteen
ticks within nine wheels. The prescribed tick of `DLMinusOne` stays open.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30ClockPhasePairs

open Ruliology.CellularAutomata
open Rule30AgedLeftDiagonals Rule30RootedWhiteReturns Rule30RelaxedWindows

/-- The three cells belong to the closed interval from a through min(b,a+w). -/
def IsolatedAt (d : Nat → Column) (a b s : Nat) (w : Nat := 6) : Prop :=
  ∃ j, a ≤ j ∧ j+2 ≤ b ∧ j+2 ≤ a+w ∧
    d j s = false ∧ d (j+1) s = true ∧ d (j+2) s = false

theorem IsolatedAt.catch {d a b s w} (h : IsolatedAt d a b s w) : Catch d a b s := by
  obtain ⟨j, hja, hjb, _, left, mid, right⟩ := h
  refine ⟨j, 1, hja, hjb, by decide, left, ?_, right⟩
  intro k hk
  have : k = 0 := by omega
  simpa [this] using mid

private theorem on_fall {d : Nat → Column} {a b t : Nat}
    (black : ∀ s, d (a+2) s = true)
    (delay : ∀ s, d (a+3) (s+1) = !(d (a+1) s)) (room : a+4 ≤ b)
    (old : d (a+1) t = true) (new : d (a+1) (t+1) = false) :
    IsolatedAt d a b (t+1) := by
  exact ⟨a+1, by omega, by omega, by omega, new, black _, by simp [delay, old]⟩

private theorem IsolatedAt.widen {d a b s w v} (h : IsolatedAt d a b s w) (le : w ≤ v) :
    IsolatedAt d a b s v := by
  obtain ⟨j, ha, hb, hw, bits⟩ := h
  exact ⟨j, ha, hb, by omega, bits⟩

private theorem toggle_catch {d : Nat → Column} (hd : Recurrence d)
    {a b z w t : Nat} (white : White d b) (left : a ≤ z) (room : z+1 ≤ b)
    (depth : z+3 ≤ a+w) (zero : ∀ k, k < 2 → d z (t+k) = false)
    (toggle : ∀ k, k < 2 → d (z+1) (t+k+1) = !(d (z+1) (t+k))) :
    ∃ k, k < 3 ∧ IsolatedAt d a b (t+k) w := by
  obtain ⟨k, hk, high, low⟩ : ∃ k, k < 2 ∧ d (z+1) (t+k) = true ∧
      d (z+1) (t+k+1) = false := by
    cases h : d (z+1) t with
    | true => exact ⟨0, by decide, h, by simpa [h] using toggle 0 (by decide)⟩
    | false =>
      have h' : d (z+1) (t+1) = true := by
        simpa [h] using toggle 0 (by decide)
      exact ⟨1, by decide, h', by rw [toggle 1 (by decide), h']; rfl⟩
  have h4 : b ≠ z+1 := fun h => by rw [h] at white; exact absurd high (by simp [white _])
  cases next : d (z+2) (t+k) with
  | false => exact ⟨k, by omega, z, left, by omega, by omega, zero k hk, high, next⟩
  | true =>
    have h5 : b ≠ z+2 := fun h => by rw [h] at white; exact absurd next (by simp [white _])
    refine ⟨k+1, by omega, z+1, by omega, by omega, by omega, low, ?_, ?_⟩
    · rw [show t+(k+1)=t+k+1 by omega, hd.2.2 z, zero k hk, high]; rfl
    · rw [show t+(k+1)=t+k+1 by omega, hd.2.2 (z+1), high, next]; rfl

private theorem black_two {d : Nat → Column} (hd : Recurrence d)
    {a b t : Nat} (white : White d b) (room : a+4 ≤ b)
    (black : ∀ s, d (a+2) s = true)
    (delay : ∀ s, d (a+3) (s+1) = !(d (a+1) s))
    (driver : ∀ k, k < 2 → d (a+1) (t+k) = true) :
    ∃ k, k < 3 ∧ IsolatedAt d a b (t+1+k) := by
  have three (k : Nat) (hk : k < 2) : d (a+3) (t+1+k) = false := by
    rw [show t+1+k=t+k+1 by omega, delay, driver k hk]; rfl
  have toggle (k : Nat) (hk : k < 2) :
      d (a+4) (t+1+k+1) = !(d (a+4) (t+1+k)) := by
    rw [hd.2.2 (a+2) (t+1+k), black, three k hk]
    cases d (a+4) (t+1+k) <;> rfl
  exact toggle_catch hd white (by omega : a ≤ a+3) room (by omega) three toggle

private theorem white_three {d : Nat → Column} (hd : Recurrence d)
    {a b t : Nat} (white : White d b) (room : a+4 ≤ b)
    (black : ∀ s, d (a+2) s = true)
    (delay : ∀ s, d (a+3) (s+1) = !(d (a+1) s))
    (driver : ∀ k, k < 3 → d (a+1) (t+k) = false)
    (fourLive : ¬ White d (a+4)) :
    ∃ k, k < 3 ∧ IsolatedAt d a b (t+2+k) 7 := by
  have three (k : Nat) (hk : k < 3) : d (a+3) (t+1+k) = true := by
    rw [show t+1+k=t+k+1 by omega, delay, driver k hk]; rfl
  have four (k : Nat) (hk : k < 2) : d (a+4) (t+2+k) = false := by
    rw [show t+2+k=t+1+k+1 by omega, hd.2.2 (a+2), black, three k (by omega)]; rfl
  have toggle (k : Nat) (hk : k < 2) : d (a+5) (t+2+k+1) = !(d (a+5) (t+2+k)) := by
    have h3 : d (a+3) (t+2+k) = true := by
      rw [show t+2+k=t+1+(k+1) by omega]
      exact three (k+1) (by omega)
    rw [hd.2.2 (a+3), h3, four k hk]; cases d (a+5) (t+2+k) <;> rfl
  have h4 : b ≠ a+4 := fun h => fourLive (h ▸ white)
  exact toggle_catch hd white (by omega : a ≤ a+4) (by omega) (by omega) four toggle

private theorem three_after {d : Nat → Column} (hd : Recurrence d) (clocks : PrefixClocks d)
    {a e b : Nat} (loss : FirstLoss d a e) (hab : NextWhite d a b) (t : Nat) :
    ∃ k, k < 3 ∧ (IsolatedAt d a b (t+1+k) ∨ IsolatedAt d a b (t+1+k+2^e)) := by
  obtain ⟨black, delay, room, _⟩ := firstLoss_cascade_and_immediate_catch hd clocks loss hab
  by_cases change : ∃ k, k < 3 ∧ d (a+1) (t+k) ≠ d (a+1) (t+k+1)
  · obtain ⟨k, hk, diff⟩ := change
    refine ⟨k, hk, ?_⟩
    cases old : d (a+1) (t+k) <;> cases new : d (a+1) (t+k+1) <;>
      try exact False.elim (diff (old.trans new.symm))
    · right
      have old' := loss.flip (t+k)
      have new' := loss.flip (t+k+1)
      rw [old] at old'; rw [new] at new'
      rw [show t+1+k+2^e=t+k+2^e+1 by omega]
      exact on_fall black delay room old' (by simpa [Nat.add_right_comm] using new')
    · left
      rw [show t+1+k=t+k+1 by omega]
      exact on_fall black delay room old new
  · have flat (k : Nat) (hk : k ≤ 3) : d (a+1) (t+k) = d (a+1) t := by
      induction k with
      | zero => rfl
      | succ k ih =>
        have same : d (a+1) (t+k) = d (a+1) (t+k+1) :=
          Classical.byContradiction fun h => change ⟨k, by omega, h⟩
        exact same.symm.trans (ih (by omega))
    cases first : d (a+1) t with
    | true =>
      obtain ⟨k, hk, hits⟩ := black_two hd hab.2.1 room black delay
        (fun k hk => (flat k (by omega)).trans first)
      exact ⟨k, hk, Or.inl hits⟩
    | false =>
      have other (k : Nat) (hk : k ≤ 3) : d (a+1) (t+2^e+k) = true := by
        rw [show t+2^e+k=t+k+2^e by omega, loss.flip, flat k hk, first]; rfl
      obtain ⟨k, hk, hits⟩ := black_two hd hab.2.1 room black delay (fun k hk => other k (by omega))
      exact ⟨k, hk, Or.inr (by rwa [show t+1+k+2^e=t+2^e+1+k by omega])⟩

private theorem move_back {d : Nat → Column} {a b p u w : Nat}
    (clock : Rule30RecurrentStrip.Clock d b p) (h : IsolatedAt d a b (u+p) w) :
    IsolatedAt d a b u w := by
  obtain ⟨j, hja, hjb, hjw, l, m, r⟩ := h
  exact ⟨j,hja,hjb,hjw,(clock j (by omega) u (by omega)).symm.trans l,
    (clock (j+1) (by omega) u (by omega)).symm.trans m,
    (clock (j+2) hjb u (by omega)).symm.trans r⟩

/-- At any clock loss, three consecutive antipodal phase pairs contain a singleton
inside the first white interval and no later than wheel a+6. -/
theorem three_pairs {d : Nat → Column} (hd : Recurrence d) (clocks : PrefixClocks d)
    {a e b : Nat} (loss : FirstLoss d a e) (hab : NextWhite d a b) (s : Nat) :
    ∃ k, k < 3 ∧ (IsolatedAt d a b (s+k) ∨ IsolatedAt d a b (s+k+2^e)) := by
  obtain ⟨p, hp, clock⟩ := clocks b
  obtain ⟨k, hk, hit⟩ := three_after hd clocks loss hab (s+p-1)
  rw [show s+p-1+1+k=s+k+p by omega, show s+k+p+2^e=s+k+2^e+p by omega] at hit
  exact ⟨k, hk, hit.elim (fun h => Or.inl (move_back clock h)) (fun h => Or.inr (move_back clock h))⟩

private theorem five_after {d : Nat → Column} (hd : Recurrence d) (clocks : PrefixClocks d)
    {a e b : Nat} (loss : FirstLoss d a e) (hab : NextWhite d a b) (t : Nat) :
    ∃ k, k < 5 ∧ IsolatedAt d a b (t+1+k) 7 := by
  obtain ⟨black, delay, room, _, _, toggle4⟩ := firstLoss_cascade_and_immediate_catch hd clocks loss hab
  by_cases fall : ∃ k, k < 3 ∧ d (a+1) (t+k) = true ∧ d (a+1) (t+k+1) = false
  · obtain ⟨k, hk, high, low⟩ := fall
    refine ⟨k, by omega, ?_⟩
    rw [show t+1+k=t+k+1 by omega]
    exact (on_fall black delay room high low).widen (by decide)
  · have up (k : Nat) (hk : k < 3) (high : d (a+1) (t+k) = true) : d (a+1) (t+k+1) = true := by
      cases low : d (a+1) (t+k+1) with
      | true => rfl
      | false => exact False.elim (fall ⟨k,hk,high,low⟩)
    cases bit : d (a+1) (t+2) with
    | true =>
      have driver (k : Nat) (hk : k < 2) : d (a+1) (t+2+k) = true := by
        rcases (show k=0 ∨ k=1 by omega) with rfl | rfl
        · exact bit
        · exact up 2 (by decide) bit
      obtain ⟨k, hk, hit⟩ := black_two hd hab.2.1 room black delay driver
      refine ⟨k+2, by omega, ?_⟩
      rw [show t+1+(k+2)=t+2+1+k by omega]
      exact hit.widen (by decide)
    | false =>
      have d1 : d (a+1) (t+1) = false := by
        cases h : d (a+1) (t+1) <;> simp_all [up 1 (by decide)]
      have d0 : d (a+1) t = false := by
        cases h : d (a+1) t with
        | false => rfl
        | true => exact absurd (up 0 (by decide) h) (by simp [d1])
      have driver (k : Nat) (hk : k < 3) : d (a+1) (t+k) = false := by
        rcases (show k=0 ∨ k=1 ∨ k=2 by omega) with rfl | rfl | rfl
        · exact d0
        · exact d1
        · exact bit
      have fourLive : ¬ White d (a+4) := by
        intro white
        have high := loss.flip t
        rw [d0] at high
        have hf := toggle4 (t+2^e) high
        rw [white _, white _] at hf
        contradiction
      obtain ⟨k, hk, hit⟩ := white_three hd hab.2.1 room black delay driver fourLive
      exact ⟨k+1, by omega, by rwa [show t+1+(k+1)=t+2+k by omega]⟩

/-- Every five consecutive actual ticks contain an isolated black in the first white interval,
no later than wheel a+7. This holds at every dyadic clock, without a phase shift. -/
theorem five_ticks {d : Nat → Column} (hd : Recurrence d) (clocks : PrefixClocks d)
    {a e b : Nat} (loss : FirstLoss d a e) (hab : NextWhite d a b) (s : Nat) :
    ∃ k, k < 5 ∧ IsolatedAt d a b (s+k) 7 := by
  obtain ⟨p, hp, clock⟩ := clocks b
  obtain ⟨k, hk, hit⟩ := five_after hd clocks loss hab (s+p-1)
  rw [show s+p-1+1+k=s+k+p by omega] at hit
  exact ⟨k, hk, move_back clock hit⟩

/-- A fixed tick among every five sees singleton resets arbitrarily far along one rooted
strip, each attached to a first loss and certified inside its first seven wheels. -/
theorem cofinal_singletons {d : Nat → Column} (hd : Recurrence d) (edge : d 0 0 = true)
    (clocks : PrefixClocks d) (s : Nat) :
    ∃ k, k < 5 ∧ ∀ lo, ∃ a e b, lo ≤ a ∧ FirstLoss d a e ∧ NextWhite d a b ∧
      IsolatedAt d a b (s+k) 7 := by
  let event (k a : Nat) := ∃ e b, FirstLoss d a e ∧ NextWhite d a b ∧ IsolatedAt d a b (s+k) 7
  apply Classical.byContradiction
  intro absent
  have cap (k : Nat) (hk : k < 5) : ∃ lo, ∀ a, lo ≤ a → ¬ event k a := by
    apply Classical.byContradiction
    intro unbounded
    apply absent
    refine ⟨k, hk, fun lo => Classical.byContradiction fun miss => unbounded ?_⟩
    exact ⟨lo, fun a ha ⟨e, b, fl, nw, hit⟩ => miss ⟨a, e, b, ha, fl, nw, hit⟩⟩
  obtain ⟨l0,h0⟩ := cap 0 (by decide)
  obtain ⟨l1,h1⟩ := cap 1 (by decide)
  obtain ⟨l2,h2⟩ := cap 2 (by decide)
  obtain ⟨l3,h3⟩ := cap 3 (by decide)
  obtain ⟨l4,h4⟩ := cap 4 (by decide)
  obtain ⟨a, e, ha, fl⟩ := unbounded_first_losses hd edge clocks (l0+l1+l2+l3+l4)
  obtain ⟨b, nw⟩ := exists_next_white hd edge clocks a
  obtain ⟨k, hk, hit⟩ := five_ticks hd clocks fl nw s
  have witnessed : event k a := ⟨e,b,fl,nw,hit⟩
  rcases (show k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 by omega) with rfl | rfl | rfl | rfl | rfl
  · exact h0 a (by omega) witnessed
  · exact h1 a (by omega) witnessed
  · exact h2 a (by omega) witnessed
  · exact h3 a (by omega) witnessed
  · exact h4 a (by omega) witnessed


end Ruliology.CellularAutomata.Rule30ClockPhasePairs
