module

public import Ruliology.CellularAutomata.Rule30Prize

/-!
Every autonomous observable of one fixed finite window is constant,
when its update is required on all finite Rule 30 input blocks.
The observable codomain and its autonomous update are arbitrary.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30LocalFactor

def Word : Nat → Type
  | 0 => Unit
  | n+1 => Bool × Word n

abbrev gate := Rule30Jen.rule

theorem undo (d b c : Bool) : gate (gate d b c) b c = d := by
  cases d <;> cases b <;> cases c <;> decide

def trim : {n : Nat} → Word (n+1) → Word n
  | 0, _ => ()
  | _+1, w => (w.1, trim w.2)

def step : {n : Nat} → Word (n+2) → Word n
  | 0, _ => ()
  | _+1, w => (gate w.1 w.2.1 w.2.2.1, step w.2)

def middle {n : Nat} (w : Word (n+2)) : Word n := trim w.2

def lift : {n : Nat} → Word n → Word 2 → Word (n+2)
  | 0, _, bc => bc
  | _+1, w, bc =>
      let t := lift w.2 bc
      (gate w.1 t.1 t.2.1, t)

theorem step_lift {n : Nat} (w : Word n) (bc : Word 2) :
    step (lift w bc) = w := by
  induction n with
  | zero => cases w; rfl
  | succ n ih =>
      cases w with
      | mk b w => simp only [lift, step, undo, ih]; rfl

theorem forget_first {Y : Type} {n : Nat}
    (g : Word (n+1) → Y) (H : Y → Y)
    (closed : ∀ z : Word (n+3), g (step z) = H (g (middle z)))
    (b : Bool) (w : Word n) : g (b,w) = g (false,w) := by
  let t : Word (n+2) := lift w (false,false,())
  have ht : step t = w := step_lift w (false,false,())
  have hb := closed (gate b t.1 t.2.1, t)
  have hf := closed (gate false t.1 t.2.1, t)
  simp only [step, undo, ht, middle] at hb hf
  exact hb.trans hf.symm

theorem autonomous_is_constant {Y : Type} (n : Nat)
    (g : Word n → Y) (H : Y → Y)
    (closed : ∀ z : Word (n+2), g (step z) = H (g (middle z))) :
    ∀ u v : Word n, g u = g v := by
  induction n with
  | zero => intro u v; cases u; cases v; rfl
  | succ n ih =>
      let smaller : Word n → Y := fun w => g (false,w)
      have forget := forget_first g H closed
      have smaller_closed : ∀ z : Word (n+2),
          smaller (step z) = H (smaller (middle z)) := by
        intro z
        have hc := closed (false,z)
        change g (gate false z.1 z.2.1, step z) =
          H (g (z.1,middle z)) at hc
        rw [forget (gate false z.1 z.2.1) (step z),
          forget z.1 (middle z)] at hc
        exact hc
      have hs := ih smaller smaller_closed
      intro u v
      cases u with
      | mk b u =>
          cases v with
          | mk c v =>
              exact (forget b u).trans ((hs u v).trans (forget c v).symm)

/-! ### Exact two-sided bijection between `Word (n + 2)` and `Word n × Word 2`, 4-predecessor fiber parameterization, and fixed-point necessity for autonomous updates -/

/-- Extracts the rightmost two bits of a word in `Word (n + 2)`. -/
def rightTwo : {n : Nat} → Word (n + 2) → Word 2
  | 0, bc => bc
  | _ + 1, w => rightTwo w.2

/-- **Rightmost 2-Bit Recovery After `lift` (`rightTwo_lift`):**
for every `w : Word n` and `bc : Word 2`, `rightTwo (lift w bc) = bc`. -/
theorem rightTwo_lift {n : Nat} (w : Word n) (bc : Word 2) :
    rightTwo (lift w bc) = bc := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih w.2

/-- **Exact Left-Inverse Predecessor Reconstruction (`lift_step_rightTwo`):**
for every `z : Word (n + 2)`, reconstructing from `step z` and `rightTwo z` recovers `z`
(`lift (step z) (rightTwo z) = z`). -/
theorem lift_step_rightTwo {n : Nat} (z : Word (n + 2)) :
    lift (step z) (rightTwo z) = z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases z with ⟨d, w⟩
    have hw := ih w
    change (gate (gate d w.1 w.2.1) (lift (step w) (rightTwo w)).1
      (lift (step w) (rightTwo w)).2.1, lift (step w) (rightTwo w)) = (d, w)
    rw [hw, undo]

/-- **Exact Predecessor Fiber Characterization (`step_eq_iff_eq_lift`):**
for every `z : Word (n + 2)` and `w : Word n`, `step z = w` if and only if
`z = lift w (rightTwo z)`. -/
theorem step_eq_iff_eq_lift {n : Nat} (z : Word (n + 2)) (w : Word n) :
    step z = w ↔ z = lift w (rightTwo z) := by
  constructor
  · rintro rfl
    exact (lift_step_rightTwo z).symm
  · intro hz
    rw [hz, step_lift]

/-- **Joint Injectivity of `lift` (`lift_eq_iff`):**
`lift w₁ bc₁ = lift w₂ bc₂` if and only if `w₁ = w₂ ∧ bc₁ = bc₂`. -/
theorem lift_eq_iff {n : Nat} (w₁ w₂ : Word n) (bc₁ bc₂ : Word 2) :
    lift w₁ bc₁ = lift w₂ bc₂ ↔ w₁ = w₂ ∧ bc₁ = bc₂ := by
  constructor
  · intro h
    have hw : step (lift w₁ bc₁) = step (lift w₂ bc₂) := congrArg step h
    have hbc : rightTwo (lift w₁ bc₁) = rightTwo (lift w₂ bc₂) := congrArg rightTwo h
    rw [step_lift, step_lift] at hw
    rw [rightTwo_lift, rightTwo_lift] at hbc
    exact ⟨hw, hbc⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The all-false word of length `n`. -/
def zeroWord : (n : Nat) → Word n
  | 0 => ()
  | n + 1 => (false, zeroWord n)

/-- **Fixed-Point Necessity for Autonomous Observables (`autonomous_value_is_fixed_point`):**
if `g : Word n → Y` updates autonomously via `H : Y → Y` (`∀ z : Word (n + 2), g (step z) = H (g (middle z))`),
then for every word `u : Word n`, `g u` is a fixed point of `H` (`H (g u) = g u`). -/
theorem autonomous_value_is_fixed_point {Y : Type} (n : Nat)
    (g : Word n → Y) (H : Y → Y)
    (closed : ∀ z : Word (n + 2), g (step z) = H (g (middle z)))
    (u : Word n) :
    H (g u) = g u := by
  have hconst := autonomous_is_constant n g H closed
  have hz := closed (zeroWord (n + 2))
  rw [hconst (step (zeroWord (n + 2))) u, hconst (middle (zeroWord (n + 2))) u] at hz
  exact hz.symm

/-- **Non-Existence of Autonomous Observables for Fixed-Point-Free Updates
(`no_autonomous_of_fixed_point_free`):** if `H : Y → Y` has no fixed point (`∀ y, H y ≠ y`),
then for every `n : Nat` and `g : Word n → Y`, `g` cannot satisfy
`∀ z : Word (n + 2), g (step z) = H (g (middle z))`. -/
theorem no_autonomous_of_fixed_point_free {Y : Type} (n : Nat)
    (g : Word n → Y) (H : Y → Y) (hfree : ∀ y : Y, H y ≠ y) :
    ¬ ∀ z : Word (n + 2), g (step z) = H (g (middle z)) := by
  intro closed
  exact hfree (g (zeroWord n)) (autonomous_value_is_fixed_point n g H closed (zeroWord n))

end Ruliology.CellularAutomata.Rule30LocalFactor
