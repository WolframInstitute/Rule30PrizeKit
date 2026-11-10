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

end Ruliology.CellularAutomata.Rule30LocalFactor
