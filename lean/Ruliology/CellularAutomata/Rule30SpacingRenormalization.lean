module

public import Ruliology.CellularAutomata.Rule30ZeroBoundary
public import Ruliology.CellularAutomata.Rule30Prize

/-!
# An eight-column reconstruction identity and the condition needed to iterate it

The boundary history is `!G 0, 1, !G 1, 1, ...`. If the black gate
positions have spacing at least three, shifting reconstruction eight columns
left replaces `G r` by `G (r+2) xor G (r+4)`. This condition is not asserted
to hold after that replacement, or for every driven right half.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30SpacingRenormalization

open Rule30ZeroBoundary

def boundary (G : Nat → Bool) (t : Nat) : Bool :=
  if t % 2 = 0 then !G (t / 2) else true

def transform (G : Nat → Bool) (r : Nat) : Bool := xor (G (r+2)) (G (r+4))

def Spaced (G : Nat → Bool) : Prop :=
  ∀ r, (G r && G (r+1)) = false ∧ (G r && G (r+2)) = false

/-- The even/odd pair of a reconstructed column. -/
def pair (G : Nat → Bool) : Nat → Nat → Bool × Bool
  | 0, _ => (false, false)
  | 1, r => (!G r, true)
  | k+2, r =>
      (xor (pair G (k+1) r).2 ((pair G (k+1) r).1 || (pair G k r).1),
       xor (pair G (k+1) (r+1)).1 ((pair G (k+1) r).2 || (pair G k r).2))

theorem boundary_even (G : Nat → Bool) (r : Nat) : boundary G (2*r) = !G r := by
  simp [boundary, show 2*r % 2 = 0 by omega,
    show 2*r / 2 = r by omega]

theorem boundary_odd (G : Nat → Bool) (r : Nat) : boundary G (2*r+1) = true := by
  simp [boundary]

/-- The pair recurrence is exactly the kit's scalar reconstruction. -/
theorem pair_recon (G : Nat → Bool) : ∀ k r,
    pair G k r = (recon (boundary G) k (2*r), recon (boundary G) k (2*r+1))
  | 0, r => rfl
  | 1, r => by simp [pair, recon, boundary_even, boundary_odd]
  | k+2, r => by
      rw [pair, pair_recon G (k+1) r, pair_recon G (k+1) (r+1), pair_recon G k r]
      simp only [recon_two, show 2*r+1+1 = 2*(r+1) by omega]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ninth_pair (G : Nat → Bool) (h : Spaced G) (r : Nat) :
    pair G 9 r = pair (transform G) 1 r := by
  have h0 := h r
  have h1 := h (r+1)
  have h2 := h (r+2)
  have h3 := h (r+3)
  simp only [Nat.add_assoc] at h1 h2 h3
  simp only [pair, transform, Nat.add_assoc]
  cases ha : G r <;> cases hb : G (r+1) <;> cases hc : G (r+2) <;>
    cases hd : G (r+3) <;> cases he : G (r+4) <;> simp_all

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem tenth_pair (G : Nat → Bool) (h : Spaced G) (r : Nat) :
    pair G 10 r = pair (transform G) 2 r := by
  have h0 := h r
  have h1 := h (r+1)
  have h2 := h (r+2)
  have h3 := h (r+3)
  have h4 := h (r+4)
  simp only [Nat.add_assoc] at h1 h2 h3 h4
  simp only [pair, transform, Nat.add_assoc]
  cases ha : G r <;> cases hb : G (r+1) <;> cases hc : G (r+2) <;>
    cases hd : G (r+3) <;> cases he : G (r+4) <;> cases hf : G (r+5) <;> simp_all

/-- An exact eight-column translation, with an explicit spacing premise. -/
theorem pair_translate (G : Nat → Bool) (h : Spaced G) : ∀ m r,
    pair G (m+9) r = pair (transform G) (m+1) r := by
  have key : ∀ m, (∀ r, pair G (m+9) r = pair (transform G) (m+1) r) ∧
      (∀ r, pair G (m+10) r = pair (transform G) (m+2) r) := by
    intro m
    induction m with
    | zero => exact ⟨ninth_pair G h, tenth_pair G h⟩
    | succ m ih =>
        refine ⟨ih.2, fun r => ?_⟩
        change
          (xor (pair G (m+10) r).2 ((pair G (m+10) r).1 || (pair G (m+9) r).1),
           xor (pair G (m+10) (r+1)).1 ((pair G (m+10) r).2 || (pair G (m+9) r).2)) =
          (xor (pair (transform G) (m+2) r).2
             ((pair (transform G) (m+2) r).1 || (pair (transform G) (m+1) r).1),
           xor (pair (transform G) (m+2) (r+1)).1
             ((pair (transform G) (m+2) r).2 || (pair (transform G) (m+1) r).2))
        rw [ih.2 r, ih.2 (r+1), ih.1 r]
  exact fun m => (key m).1

/-- The scalar statement holds at every time, not only at time zero. -/
theorem reconstruction_translate (G : Nat → Bool) (h : Spaced G) (m t : Nat) :
    recon (boundary G) (m+9) t = recon (boundary (transform G)) (m+1) t := by
  have hp := pair_translate G h m (t/2)
  rw [pair_recon, pair_recon] at hp
  rcases Nat.mod_two_eq_zero_or_one t with ht | ht
  · have he : t = 2*(t/2) := by omega
    rw [he]
    exact congrArg Prod.fst hp
  · have he : t = 2*(t/2)+1 := by omega
    rw [he]
    exact congrArg Prod.snd hp

/-- An explicit support bound drops by eight under the translation. -/
theorem support_transfer (G : Nat → Bool) (h : Spaced G) (W : Nat)
    (hW : ∀ k, W < k → lam (boundary G) k = false) :
    ∀ k, W-8 < k → lam (boundary (transform G)) k = false := by
  intro k hk
  obtain ⟨m, rfl⟩ : ∃ m, k = m+1 := ⟨k-1, by omega⟩
  unfold lam
  rw [← reconstruction_translate G h]
  exact hW _ (by omega)

/-- A finite reconstructed initial row remains finite after the translation. -/
theorem finite_transfer (G : Nat → Bool) (h : Spaced G)
    (hf : FinSupp (lam (boundary G))) : FinSupp (lam (boundary (transform G))) := by
  obtain ⟨W, hW⟩ := hf
  exact ⟨W-8, support_transfer G h W hW⟩

/-- The spacing premise survives one transform exactly for gates white beyond
index three. Thus an infinite gate cannot support a second application. -/
theorem transform_spaced_iff (G : Nat → Bool) (h : Spaced G) :
    Spaced (transform G) ↔ ∀ r, G (r+4) = false := by
  constructor
  · intro ht r
    have ha := (h (r+2)).2
    have hb := (h (r+4)).2
    have hc := (ht r).2
    simp only [transform, Nat.add_assoc] at hc ha hb
    cases h2 : G (r+2) <;> cases h4 : G (r+4) <;> cases h6 : G (r+6) <;> simp_all
  · intro hz
    have he : transform G = fun r => G (r+2) := by
      funext r
      simp [transform, hz r]
    rw [he]
    intro r
    simpa only [Nat.add_assoc] using h (r+2)

/-- Spacing is not preserved: a period-five gate supplies a counterexample. -/
def periodFive (r : Nat) : Bool := r % 5 == 0

theorem periodFive_spaced : Spaced periodFive := by
  intro r
  have hr := Nat.mod_lt r (by decide : 0 < 5)
  have h1 : (r+1)%5 = (r%5+1)%5 := by omega
  have h2 : (r+2)%5 = (r%5+2)%5 := by omega
  simp only [periodFive]
  rw [h1, h2]
  have hs : r%5=0 ∨ r%5=1 ∨ r%5=2 ∨ r%5=3 ∨ r%5=4 := by omega
  rcases hs with hh | hh | hh | hh | hh <;> rw [hh] <;> decide

theorem transform_not_spaced : ¬ Spaced (transform periodFive) := by
  intro h
  have hh := (h 1).2
  change true = false at hh
  exact Bool.noConfusion hh

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- Dropping the spacing premise for the second step gives a false identity,
already at depth seventeen and time zero for the period-five gate. -/
theorem second_translation_fails :
    recon (boundary periodFive) 17 0 ≠
      recon (boundary (transform (transform periodFive))) 1 0 := by
  decide

/-! ## Exact 12-column closed-form hierarchy, depth-12 3-gap detector, and `Theta` renormalization bridge -/

/-- **Unconditional Depth-2 Pair Formula (`pair_two`):**
for any gate `G : Nat → Bool`, `pair G 2 r = (G r, G (r + 1))`. -/
theorem pair_two (G : Nat → Bool) (r : Nat) :
    pair G 2 r = (G r, G (r + 1)) := by
  simp only [pair]
  cases G r <;> cases G (r + 1) <;> rfl

/-- **Unconditional Depth-3 Pair Synchronization (`pair_three`):**
for any gate `G : Nat → Bool`, the even-time and odd-time components at depth `3` are identically
equal to `(!G (r + 1), !G (r + 1))`. -/
theorem pair_three (G : Nat → Bool) (r : Nat) :
    pair G 3 r = (!G (r + 1), !G (r + 1)) := by
  simp only [pair]
  cases G r <;> cases G (r + 1) <;> cases G (r + 2) <;> rfl

/-- **Unconditional Depth-4 Collision-Detector Formula (`pair_four`):**
for any gate `G : Nat → Bool`, the even-time component at depth `4` is the exact `11`-collision
detector `G r && G (r + 1)`, while the odd-time component is the shifted gate `G (r + 2)`. -/
theorem pair_four (G : Nat → Bool) (r : Nat) :
    pair G 4 r = (G r && G (r + 1), G (r + 2)) := by
  simp only [pair]
  cases G r <;> cases G (r + 1) <;> cases G (r + 2) <;> cases G (r + 3) <;> rfl

/-- **Zero XOR-Collision and Pure Disjunction Law of `transform` under `Spaced` (`transform_eq_or`):**
when `Spaced G` holds, `G (r + 2)` and `G (r + 4)` are never simultaneously `true`, so
`transform G r = xor (G (r + 2)) (G (r + 4))` equals `G (r + 2) || G (r + 4)`. -/
theorem transform_eq_or (G : Nat → Bool) (h : Spaced G) (r : Nat) :
    (G (r + 2) && G (r + 4)) = false ∧ transform G r = (G (r + 2) || G (r + 4)) := by
  have h2 := (h (r + 2)).2
  rw [show r + 2 + 2 = r + 4 by omega] at h2
  refine ⟨h2, ?_⟩
  unfold transform
  revert h2
  cases G (r + 2) <;> cases G (r + 4) <;> decide

/-- **Depth-4 Pair Formula under `Spaced` (`pair_four_spaced`):**
under `Spaced G`, the even-time bit at depth `4` vanishes identically (`false`), and the odd-time
bit is `G (r + 2)`. -/
theorem pair_four_spaced (G : Nat → Bool) (h : Spaced G) (r : Nat) :
    pair G 4 r = (false, G (r + 2)) := by
  rw [pair_four, (h r).1]

/-- **Depth-5 Pair Formula under `Spaced` (`pair_five_spaced`):**
under `Spaced G`, `pair G 5 r = (!(G (r + 1) || G (r + 2)), !G (r + 1))`. -/
theorem pair_five_spaced (G : Nat → Bool) (h : Spaced G) (r : Nat) :
    pair G 5 r = (!(G (r + 1) || G (r + 2)), !G (r + 1)) := by
  have h0 := h r
  have h1 := h (r + 1)
  simp only [Nat.add_assoc] at h1
  simp only [pair, Nat.add_assoc]
  cases ha : G r <;> cases hb : G (r + 1) <;> cases hc : G (r + 2) <;> cases hd : G (r + 3) <;> simp_all

/-- **Depth-6 Pair Formula under `Spaced` (`pair_six_spaced`):**
under `Spaced G`, `pair G 6 r = (G (r + 2), G (r + 1) || G (r + 2) || G (r + 3))`. -/
theorem pair_six_spaced (G : Nat → Bool) (h : Spaced G) (r : Nat) :
    pair G 6 r = (G (r + 2), G (r + 1) || G (r + 2) || G (r + 3)) := by
  have h0 := h r
  have h1 := h (r + 1)
  have h2 := h (r + 2)
  simp only [Nat.add_assoc] at h1 h2
  simp only [pair, Nat.add_assoc]
  cases ha : G r <;> cases hb : G (r + 1) <;> cases hc : G (r + 2) <;>
    cases hd : G (r + 3) <;> cases he : G (r + 4) <;> simp_all

/-- **Depth-7 Pair Formula under `Spaced` (`pair_seven_spaced`):**
under `Spaced G`, `pair G 7 r = (!(G (r + 2) || G (r + 3)), !G (r + 3))`. -/
theorem pair_seven_spaced (G : Nat → Bool) (h : Spaced G) (r : Nat) :
    pair G 7 r = (!(G (r + 2) || G (r + 3)), !G (r + 3)) := by
  have h0 := h r
  have h1 := h (r + 1)
  have h2 := h (r + 2)
  simp only [Nat.add_assoc] at h1 h2
  simp only [pair, Nat.add_assoc]
  cases ha : G r <;> cases hb : G (r + 1) <;> cases hc : G (r + 2) <;>
    cases hd : G (r + 3) <;> cases he : G (r + 4) <;> simp_all

/-- **Depth-8 All-White Even-Column Formula under `Spaced` (`pair_eight_spaced`):**
under `Spaced G`, the even-time bit at depth `8` vanishes identically (`false`), and the odd-time
bit is `G (r + 3) || G (r + 4)`. -/
theorem pair_eight_spaced (G : Nat → Bool) (h : Spaced G) (r : Nat) :
    pair G 8 r = (false, G (r + 3) || G (r + 4)) := by
  have h0 := h r
  have h1 := h (r + 1)
  have h2 := h (r + 2)
  have h3 := h (r + 3)
  simp only [Nat.add_assoc] at h1 h2 h3
  simp only [pair, Nat.add_assoc]
  cases ha : G r <;> cases hb : G (r + 1) <;> cases hc : G (r + 2) <;>
    cases hd : G (r + 3) <;> cases he : G (r + 4) <;> simp_all

/-- **Depth-9 Closed-Form Disjunction Formula under `Spaced` (`pair_nine_spaced`):**
under `Spaced G`, `pair G 9 r = (!(G (r + 2) || G (r + 4)), true)`. -/
theorem pair_nine_spaced (G : Nat → Bool) (h : Spaced G) (r : Nat) :
    pair G 9 r = (!(G (r + 2) || G (r + 4)), true) := by
  rw [ninth_pair G h r]
  simp only [pair, (transform_eq_or G h r).2]

/-- **Depth-10 Closed-Form Disjunction Formula under `Spaced` (`pair_ten_spaced`):**
under `Spaced G`, `pair G 10 r = (G (r + 2) || G (r + 4), G (r + 3) || G (r + 5))`. -/
theorem pair_ten_spaced (G : Nat → Bool) (h : Spaced G) (r : Nat) :
    pair G 10 r = (G (r + 2) || G (r + 4), G (r + 3) || G (r + 5)) := by
  rw [tenth_pair G h r, pair_two (transform G) r,
    (transform_eq_or G h r).2, (transform_eq_or G h (r + 1)).2]

/-- **Depth-11 Exact Even-Odd Synchronization under `Spaced` (`pair_eleven_spaced`):**
under `Spaced G`, the even-time and odd-time components at depth `11` are identically equal to
`!(G (r + 3) || G (r + 5))`. -/
theorem pair_eleven_spaced (G : Nat → Bool) (h : Spaced G) (r : Nat) :
    pair G 11 r = (!(G (r + 3) || G (r + 5)), !(G (r + 3) || G (r + 5))) := by
  have hp := pair_translate G h 2 r
  rw [show 2 + 9 = 11 by rfl, show 2 + 1 = 3 by rfl, pair_three (transform G) r,
    (transform_eq_or G h (r + 1)).2] at hp
  simpa only [Nat.add_assoc] using hp

/-- **Depth-12 Exact 3-Gap Detector Formula under `Spaced` (`pair_twelve_spaced`):**
under `Spaced G`, the even-time component at depth `12` is `G (r + 2) && G (r + 5)` (which is `true`
iff `G` has black cells at `r + 2` and `r + 5` separated by two white cells, i.e. an exact gap of `3`),
while the odd-time component is `G (r + 4) || G (r + 6)`. -/
theorem pair_twelve_spaced (G : Nat → Bool) (h : Spaced G) (r : Nat) :
    pair G 12 r = (G (r + 2) && G (r + 5), G (r + 4) || G (r + 6)) := by
  have hp := pair_translate G h 3 r
  rw [show 3 + 9 = 12 by rfl, show 3 + 1 = 4 by rfl, pair_four (transform G) r,
    (transform_eq_or G h r).2, (transform_eq_or G h (r + 1)).2,
    (transform_eq_or G h (r + 2)).2] at hp
  simp only [Nat.add_assoc] at hp
  rw [hp]
  have h2 := h (r + 2)
  have h3 := h (r + 3)
  have h4 := h (r + 4)
  simp only [Nat.add_assoc] at h2 h3 h4
  cases ha : G (r + 2) <;> cases hb : G (r + 3) <;> cases hc : G (r + 4) <;>
    cases hd : G (r + 5) <;> simp_all

/-- **Exact Characterization of Depth-12 Even-Time Black Cells as 3-Gaps (`recon_twelve_even_eq_true_iff_gap_three`):**
under `Spaced G`, `recon (boundary G) 12 (2 * r) = true` if and only if `G (r + 2) = true`,
`G (r + 3) = false`, `G (r + 4) = false`, and `G (r + 5) = true`. -/
theorem recon_twelve_even_eq_true_iff_gap_three (G : Nat → Bool) (h : Spaced G) (r : Nat) :
    recon (boundary G) 12 (2 * r) = true ↔
      (G (r + 2) = true ∧ G (r + 3) = false ∧ G (r + 4) = false ∧ G (r + 5) = true) := by
  have hp := congrArg Prod.fst (pair_recon G 12 r)
  rw [pair_twelve_spaced G h r] at hp
  simp only at hp
  rw [← hp]
  constructor
  · intro hand
    simp only [Bool.and_eq_true] at hand
    have h2 := h (r + 2)
    simp only [Nat.add_assoc, hand.1, Bool.true_and] at h2
    exact ⟨hand.1, h2.1, h2.2, hand.2⟩
  · rintro ⟨h2, _, _, h5⟩
    rw [h2, h5]; rfl

/-! ### Exact Bridge to `Rule30ZeroBoundary.Theta` and `alt` -/

/-- **Time-Shift Alignment of `boundary G` and `Rule30ZeroBoundary.alt` (`boundary_succ_eq_alt`):**
shifting `boundary G` forward by `1` time step aligns its even/odd phases with `alt (fun s => !G (s + 1))`. -/
theorem boundary_succ_eq_alt (G : Nat → Bool) (t : Nat) :
    boundary G (t + 1) = alt (fun s => !G (s + 1)) t := by
  rcases Nat.mod_two_eq_zero_or_one t with ht | ht
  · have he : t = 2 * (t / 2) := by omega
    rw [he, show 2 * (t / 2) + 1 = 2 * (t / 2) + 1 from rfl, boundary_odd]
    unfold alt
    rw [ite_eq_left (by omega)]
  · have ho : t = 2 * (t / 2) + 1 := by omega
    rw [ho, show 2 * (t / 2) + 1 + 1 = 2 * (t / 2 + 1) by omega, boundary_even]
    unfold alt
    rw [ite_eq_right (by omega), show (2 * (t / 2) + 1) / 2 = t / 2 by omega]

/-- **Reconstruction at Time `1` Equals `Theta` (`recon_boundary_one_eq_Theta`):**
for every gate `G : Nat → Bool` and depth `k : Nat`, `recon (boundary G) k 1 = Theta (fun s => !G (s + 1)) k`. -/
theorem recon_boundary_one_eq_Theta (G : Nat → Bool) (k : Nat) :
    recon (boundary G) k 1 = Theta (fun s => !G (s + 1)) k := by
  have hs := recon_shift (boundary G) 1 k 0
  rw [Nat.add_zero] at hs
  have hfun : (fun s => boundary G (s + 1)) = alt (fun s => !G (s + 1)) :=
    funext (boundary_succ_eq_alt G)
  rw [hs, hfun]
  rfl

/-- **Exact 8-Depth `Theta` Renormalization Identity (`Theta_spaced_translate`):**
for any gate `G : Nat → Bool` satisfying `Spaced G` and every `m : Nat`,
`Theta (fun s => !G (s + 1)) (m + 9) = Theta (fun s => !transform G (s + 1)) (m + 1)`. -/
theorem Theta_spaced_translate (G : Nat → Bool) (h : Spaced G) (m : Nat) :
    Theta (fun s => !G (s + 1)) (m + 9) = Theta (fun s => !transform G (s + 1)) (m + 1) := by
  rw [← recon_boundary_one_eq_Theta G (m + 9), ← recon_boundary_one_eq_Theta (transform G) (m + 1)]
  exact reconstruction_translate G h m 1

/-- **Explicit `Theta` Support-Width Drop by 8 under `Spaced` (`Theta_support_transfer`):**
if `Theta (fun s => !G (s + 1))` is white beyond depth `W`, then `Theta (fun s => !transform G (s + 1))`
is white beyond depth `W - 8`. -/
theorem Theta_support_transfer (G : Nat → Bool) (h : Spaced G) (W : Nat)
    (hW : ∀ k, W < k → Theta (fun s => !G (s + 1)) k = false) :
    ∀ k, W - 8 < k → Theta (fun s => !transform G (s + 1)) k = false := by
  intro k hk
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [← Theta_spaced_translate G h m]
  exact hW (m + 9) (by omega)

/-- **Finite-Support Transfer for `Theta` under `Spaced` (`Theta_finite_transfer`):**
if `Spaced G` holds and `Theta (fun s => !G (s + 1))` is finitely supported, then
`Theta (fun s => !transform G (s + 1))` is also finitely supported. -/
theorem Theta_finite_transfer (G : Nat → Bool) (h : Spaced G)
    (hf : FinSupp (Theta (fun s => !G (s + 1)))) :
    FinSupp (Theta (fun s => !transform G (s + 1))) := by
  obtain ⟨W, hW⟩ := hf
  exact ⟨W - 8, Theta_support_transfer G h W hW⟩

end Ruliology.CellularAutomata.Rule30SpacingRenormalization
