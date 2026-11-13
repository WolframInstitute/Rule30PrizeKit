module

public import Ruliology.CellularAutomata.Rule30SpacingRenormalization

/-!
# The exact premise of the eight-column return

The full eight-column return holds exactly under a weaker spacing condition.
For a spaced gate, that condition survives transformation exactly when the
gate is white from index five onward. Thus every spaced gate with arbitrarily
late black observations blocks the second return. No claim is made here about
which gates arise from a finite driven right half.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30ExactReturn

open Rule30SpacingRenormalization

def ReturnAt (G : Nat → Bool) (r : Nat) : Prop :=
  pair G 9 r=pair (transform G) 1 r ∧ pair G 10 r=pair (transform G) 2 r

def ExactReturn (G : Nat → Bool) : Prop := ∀ r, ReturnAt G r

/-- Only the distance-two pair starting at zero is exempted from spacing. -/
def NearSpaced (G : Nat → Bool) : Prop :=
  (∀ r, (G r && G (r+1))=false) ∧
  (∀ r, (G (r+1) && G (r+3))=false)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem return_at_constraints (G : Nat → Bool) (r : Nat) (h : ReturnAt G r) :
    (G r && G (r+1))=false ∧ (G (r+1) && G (r+3))=false := by
  simp only [ReturnAt,pair,transform,Nat.add_assoc] at h
  cases ha : G r <;> cases hb : G (r+1) <;> cases hc : G (r+2) <;>
    cases hd : G (r+3) <;> cases he : G (r+4) <;> cases hf : G (r+5) <;> simp_all

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem return_at_of_near (G : Nat → Bool) (r : Nat) (h : NearSpaced G) :
    ReturnAt G r := by
  have ha0 := h.1 r
  have ha1 := h.1 (r+1)
  have ha2 := h.1 (r+2)
  have ha3 := h.1 (r+3)
  have ha4 := h.1 (r+4)
  have hd0 := h.2 r
  have hd1 := h.2 (r+1)
  have hd2 := h.2 (r+2)
  simp only [Nat.add_assoc] at ha1 ha2 ha3 ha4 hd1 hd2
  simp only [ReturnAt,pair,transform,Nat.add_assoc]
  cases ha : G r <;> cases hb : G (r+1) <;> cases hc : G (r+2) <;>
    cases hd : G (r+3) <;> cases he : G (r+4) <;> cases hf : G (r+5) <;> simp_all

/-- Exact global characterization; stronger input spacing is unnecessary. -/
theorem exactReturn_iff_nearSpaced (G : Nat → Bool) : ExactReturn G ↔ NearSpaced G := by
  constructor
  · intro h
    exact ⟨fun r => (return_at_constraints G r (h r)).1,
      fun r => (return_at_constraints G r (h r)).2⟩
  · exact fun h r => return_at_of_near G r h

/-- The exact two-column condition is sufficient at every reconstructed depth. -/
theorem translate_of_exactReturn (G : Nat → Bool) (h : ExactReturn G) : ∀ m r,
    pair G (m+9) r=pair (transform G) (m+1) r := by
  have key : ∀ m,
      (∀ r, pair G (m+9) r=pair (transform G) (m+1) r) ∧
      (∀ r, pair G (m+10) r=pair (transform G) (m+2) r) := by
    intro m
    induction m with
    | zero => exact ⟨fun r => (h r).1,fun r => (h r).2⟩
    | succ m ih =>
        refine ⟨ih.2,fun r => ?_⟩
        change
          (xor (pair G (m+10) r).2 ((pair G (m+10) r).1 || (pair G (m+9) r).1),
           xor (pair G (m+10) (r+1)).1 ((pair G (m+10) r).2 || (pair G (m+9) r).2)) =
          (xor (pair (transform G) (m+2) r).2
             ((pair (transform G) (m+2) r).1 || (pair (transform G) (m+1) r).1),
           xor (pair (transform G) (m+2) (r+1)).1
             ((pair (transform G) (m+2) r).2 || (pair (transform G) (m+1) r).2))
        rw [ih.2 r,ih.2 (r+1),ih.1 r]
  exact fun m => (key m).1

theorem translation_iff_nearSpaced (G : Nat → Bool) :
    (∀ m r, pair G (m+9) r=pair (transform G) (m+1) r) ↔ NearSpaced G := by
  rw [← exactReturn_iff_nearSpaced]
  exact ⟨fun h r => ⟨h 0 r,h 1 r⟩,translate_of_exactReturn G⟩

theorem returnAt_transformed_forces_white (G : Nat → Bool) (h : Spaced G) (r : Nat)
    (hr : ReturnAt (transform G) r) : G (r+5)=false := by
  have ha := (h (r+3)).2
  have hb := (h (r+5)).2
  have hc := (return_at_constraints (transform G) r hr).2
  simp only [transform,Nat.add_assoc] at ha hb hc
  cases h3 : G (r+3) <;> cases h5 : G (r+5) <;> cases h7 : G (r+7) <;> simp_all

/-- Even the exact weaker premise survives only for a gate white from index five. -/
theorem transformed_exactReturn_iff (G : Nat → Bool) (h : Spaced G) :
    ExactReturn (transform G) ↔ ∀ r, G (r+5)=false := by
  rw [exactReturn_iff_nearSpaced]
  constructor
  · intro hn r
    have ha := (h (r+3)).2
    have hb := (h (r+5)).2
    have hc := hn.2 r
    simp only [transform,Nat.add_assoc] at ha hb hc
    cases h3 : G (r+3) <;> cases h5 : G (r+5) <;> cases h7 : G (r+7) <;> simp_all
  · intro hz
    constructor
    · intro r
      have ha := (h (r+2)).1
      have hb := (h (r+3)).1
      have hc := hz r
      simp only [transform,Nat.add_assoc] at ha hb hc ⊢
      cases h2 : G (r+2) <;> cases h3 : G (r+3) <;> cases h4 : G (r+4) <;> simp_all
    · intro r
      have ha := hz r
      have hb := hz (r+2)
      simp only [transform,Nat.add_assoc] at ha hb ⊢
      simp [ha,hb]

/-- The obstruction persists arbitrarily far in time, not just at an initial exception. -/
theorem infinite_gate_fails_arbitrarily_late (G : Nat → Bool) (h : Spaced G)
    (hi : ∀ N, ∃ s, N≤s ∧ G s=true) (N : Nat) :
    ∃ r, N≤r ∧ ¬ ReturnAt (transform G) r := by
  obtain ⟨s,hs,hb⟩ := hi (N+5)
  refine ⟨s-5,by omega,fun hr => ?_⟩
  have hz := returnAt_transformed_forces_white G h (s-5) hr
  rw [show s-5+5=s by omega,hb] at hz
  contradiction

theorem infinite_gate_blocks_second_return (G : Nat → Bool) (h : Spaced G)
    (hi : ∀ N, ∃ s, N≤s ∧ G s=true) : ¬ ExactReturn (transform G) := by
  intro hr
  have hz := (transformed_exactReturn_iff G h).mp hr
  obtain ⟨s,hs,hb⟩ := hi 5
  have he := hz (s-5)
  rw [show s-5+5=s by omega,hb] at he
  contradiction

def lastAllowed (r : Nat) : Bool := r==4

theorem lastAllowed_spaced : Spaced lastAllowed := by
  intro r
  simp only [lastAllowed,beq_iff_eq,Bool.and_eq_false_imp]
  constructor <;> intro hr <;> simp_all <;> omega

/-- Sharp boundary case: the weaker return can hold where spacing fails. -/
theorem lastAllowed_transformed_return : ExactReturn (transform lastAllowed) := by
  apply (transformed_exactReturn_iff lastAllowed lastAllowed_spaced).mpr
  intro r
  simp [lastAllowed]

theorem lastAllowed_transformed_not_spaced : ¬ Spaced (transform lastAllowed) := by
  intro h
  have hz := (transform_spaced_iff lastAllowed lastAllowed_spaced).mp h 0
  change true=false at hz
  contradiction

/-! ## Exact decomposition of `Spaced` via `NearSpaced` and positive-shift spacing -/

/-- **Exact Decomposition `Spaced G ↔ NearSpaced G ∧ (G 0 && G 2) = false` and Positive-Shift Spacing (`spaced_iff_nearSpaced_and_shift_spaced`).** -/
theorem spaced_iff_nearSpaced_and_shift_spaced (G : Nat → Bool) :
    (Spaced G ↔ NearSpaced G ∧ (G 0 && G 2) = false) ∧
    (NearSpaced G → ∀ d : Nat, 1 ≤ d → Spaced (fun r => G (d + r))) := by
  refine ⟨⟨fun hs => ⟨⟨fun r => (hs r).1, fun r => ?_⟩, (hs 0).2⟩,
           fun ⟨hn, h02⟩ r => ⟨hn.1 r, ?_⟩⟩,
          fun hn d hd r => ⟨?_, ?_⟩⟩
  · have h2 := (hs (r + 1)).2
    simpa only [Nat.add_assoc] using h2
  · cases r with
    | zero => simpa using h02
    | succ r =>
      have h2 := hn.2 r
      simpa only [Nat.add_assoc] using h2
  · show (G (d + r) && G (d + (r + 1))) = false
    rw [show d + (r + 1) = (d + r) + 1 by omega]
    exact hn.1 (d + r)
  · show (G (d + r) && G (d + (r + 2))) = false
    have h2 := hn.2 (d - 1 + r)
    rw [show d - 1 + r + 1 = d + r by omega, show d - 1 + r + 3 = d + (r + 2) by omega] at h2
    exact h2

end Ruliology.CellularAutomata.Rule30ExactReturn
