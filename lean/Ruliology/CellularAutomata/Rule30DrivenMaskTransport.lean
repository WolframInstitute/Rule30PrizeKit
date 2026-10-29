module
public import Ruliology.CellularAutomata.Rule30Jen
public import Ruliology.CellularAutomata.Rule30Prize
public import Ruliology.CellularAutomata.Rule30MaskedJen
public import Ruliology.CellularAutomata.Rule30DrivenLeft

/-! Arbitrary-driver masking and a CONDITIONAL all-period prize bridge.
For arbitrary c and s, transport to e(t)=c(t)&&c(t+1) holds exactly when
the left cell is black at every10 transition. Full black-time consistency
is equivalent under either driver. This generalizes the actual-center
specialization in Rule30DrivenLeft.cell_eq_L_effective; no periodicity or
finite-start hypothesis is imposed on transport.

PeriodicMaskExclusion is an explicit open sufficient condition, NOT a theorem
or axiom. Its conditional bridge restarts a hypothetical periodic center,
uses the actual finite left edge, and retains the open hypothesis. This module
does not prove Problem1 or identify the assertion with the catalog LHC by fiat.

Contributed by Troy Lowry with OpenAI Codex, following a written paper review
by independent Claude/swarm. The elementary masking observation is already
in Rule30MaskedJen; no priority claim is made for that observation. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30DrivenMaskTransport
open Ruliology.CellularAutomata Rule30Jen Rule30Prize Rule30DrivenLeft

def effective (c : Nat → Bool) (t : Nat) : Bool := c t && c (t+1)
def Consistent (c : Nat → Bool) (s : Int → Bool) : Prop :=
  ∀ t, c t=true → L c s t (-1)= !c (t+1)
def EffectiveConsistent (c : Nat → Bool) (s : Int → Bool) : Prop :=
  ∀ t, c t=true → L (effective c) s t (-1)= !c (t+1)
def FallingPins (c : Nat → Bool) (s : Int → Bool) : Prop :=
  ∀ t, c t=true → c (t+1)=false → L c s t (-1)=true

theorem driven_eq_of_mask (a b : Nat → Bool) (s : Int → Bool)
    (hm : ∀ t, (L a s t (-1)||a t)=(L a s t (-1)||b t)) :
    ∀ t p, p<0 → L a s t p=L b s t p := by
  intro t
  induction t with
  | zero => intro p hp;rw [L_zero hp,L_zero hp]
  | succ t ih =>
    intro p hp
    rw [L_succ hp,L_succ hp,←ih (p-1) (by omega),←ih p hp]
    by_cases he : p=(-1 : Int)
    · subst p
      rw [show (-1 : Int)+1=0 by rfl,L_col0,L_col0]
      unfold rule
      rw [hm t]
    · rw [←ih (p+1) (by omega)]

theorem falling_transport (c : Nat → Bool) (s : Int → Bool) (h : FallingPins c s) :
    ∀ t p, p<0 → L c s t p=L (effective c) s t p := by
  apply driven_eq_of_mask
  intro t
  cases h0 : c t <;> cases h1 : c (t+1)
  · simp [effective,h0,h1]
  · simp [effective,h0,h1]
  · rw [h t h0 h1];simp [effective,h0,h1]
  · simp [effective,h0,h1]

theorem effective_falling_transport (c : Nat → Bool) (s : Int → Bool)
    (h : ∀ t, c t=true → c (t+1)=false → L (effective c) s t (-1)=true) :
    ∀ t p, p<0 → L (effective c) s t p=L c s t p := by
  apply driven_eq_of_mask
  intro t
  cases h0 : c t <;> cases h1 : c (t+1)
  · simp [effective,h0,h1]
  · simp [effective,h0,h1]
  · rw [h t h0 h1];simp [effective,h0,h1]
  · simp [effective,h0,h1]

theorem falling_of_transport (c : Nat → Bool) (s : Int → Bool)
    (h : ∀ t p, p<0 → L c s t p=L (effective c) s t p) : FallingPins c s := by
  intro t hc hn
  have h2 := h t (-2) (by omega)
  have h1 := h t (-1) (by omega)
  have he := h (t+1) (-1) (by omega)
  rw [L_succ (by omega),L_succ (by omega),
    show (-1 : Int)-1 = -2 by rfl,show (-1 : Int)+1 = 0 by rfl,
    L_col0,L_col0,←h2,←h1] at he
  cases ha : L c s t (-2) <;> cases hb : L c s t (-1) <;>
    first | rfl | simp [rule,effective,hc,hn,ha,hb] at he

/-- Exact arbitrary-driver criterion, with no periodicity/finite-start hypothesis. -/
theorem transport_iff_falling (c : Nat → Bool) (s : Int → Bool) :
    (∀ t p, p<0 → L c s t p=L (effective c) s t p) ↔ FallingPins c s :=
  ⟨falling_of_transport c s,falling_transport c s⟩

theorem consistent_falling (c : Nat → Bool) (s : Int → Bool) (h : Consistent c s) :
    FallingPins c s := by
  intro t h0 h1
  simpa only [h1,Bool.not_false] using h t h0

theorem consistent_transport (c : Nat → Bool) (s : Int → Bool) (h : Consistent c s) :
    ∀ t p, p<0 → L c s t p=L (effective c) s t p :=
  falling_transport c s (consistent_falling c s h)

theorem consistency_iff (c : Nat → Bool) (s : Int → Bool) :
    Consistent c s ↔ EffectiveConsistent c s := by
  constructor
  · intro h t ht
    rw [←consistent_transport c s h t (-1) (by omega)]
    exact h t ht
  · intro h
    have he := effective_falling_transport c s (fun t h0 h1 => by
      simpa only [h1,Bool.not_false] using h t h0)
    intro t ht
    rw [←he t (-1) (by omega)]
    exact h t ht

def FiniteNonzeroLeft (s : Int → Bool) : Prop :=
  ∃ m : Nat, 0<m ∧ (∀ p : Int, p < -(m : Int) → s p=false) ∧ s (-(m : Int))=true
def BothValues (c : Nat → Bool) : Prop :=
  (∃ t, c t=false) ∧ (∃ t, c t=true)

/-- Explicit strong assertion, NOT a theorem or an assumed axiom. -/
def PeriodicMaskExclusion : Prop :=
  ∀ (c : Nat → Bool) (s : Int → Bool) (P : Nat),
    0<P → (∀ t, c (t+P)=c t) → BothValues c →
      FiniteNonzeroLeft s → ¬EffectiveConsistent c s

theorem actual_consistent (T : Nat) :
    Consistent (fun t => center (T+t)) (fun p => cell T p) := by
  intro t ht
  simp only [center] at ht ⊢
  rw [cell_eq_L T t (-1) (by omega)]
  simpa only [show (0 : Int)-1 = -1 by rfl,center,Nat.add_assoc] using
    Rule30MaskedJen.left_of_black (T+t) 0 ht

theorem tail_both_values (T : Nat) : BothValues (fun t => center (T+t)) := by
  classical
  have hne (b : Bool) : ∃ t, center (T+t)≠b := by
    by_cases hh : ∃ t, center (T+t)≠b
    · exact hh
    · have hn (t : Nat) : center (T+t)=b :=
        Classical.byContradiction (fun he => hh ⟨t,he⟩)
      apply False.elim
      apply center_not_eventually_constant
      refine ⟨T,b,fun t ht => ?_⟩
      simpa only [Nat.add_sub_of_le ht] using hn (t-T)
  constructor
  · obtain ⟨t,ht⟩ := hne true
    exact ⟨t,by cases he : center (T+t) <;> simp_all⟩
  · obtain ⟨t,ht⟩ := hne false
    exact ⟨t,by cases he : center (T+t) <;> simp_all⟩

/-- This checks the all-period bridge, not its open exclusion hypothesis. -/
theorem problem1_of_periodic_mask_exclusion (h : PeriodicMaskExclusion) : Problem1 := by
  rintro ⟨T0,P,hP,hper⟩
  let T := T0+1
  have hp : ∀ t, center (T+(t+P))=center (T+t) := by
    intro t
    simpa only [Nat.add_assoc] using hper (T+t) (by dsimp [T];omega)
  have hs : FiniteNonzeroLeft (fun p => cell T p) :=
    ⟨T,by dsimp [T];omega,fun p hh => cell_eq_false_of_lt T p hh,cell_left_edge T⟩
  exact h (fun t => center (T+t)) (fun p => cell T p) P hP hp
    (tail_both_values T) hs ((consistency_iff _ _).mp (actual_consistent T))

end Ruliology.CellularAutomata.Rule30DrivenMaskTransport
