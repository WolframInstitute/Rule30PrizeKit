module
public import Ruliology.CellularAutomata.Rule30ZeroBoundary

/-! Packed sideways reconstruction and soundness of a spatial synchronization certificate for a two-tick edit. -/

@[expose] public section
namespace Ruliology.CellularAutomata.Rule30ResetSwap
open Ruliology.CellularAutomata.Rule30ZeroBoundary

abbrev Trace := Nat → Bool
abbrev Pair := Nat × Nat

/-- The two temporal columns at kit depths j and j+1, starting at the white wall. -/
def side (u : Trace) (j t : Nat) : Bool × Bool := (recon u j t, recon u (j+1) t)
theorem side_zero (u : Trace) (t : Nat) : side u 0 t=(false,u t) := rfl
theorem side_succ (u : Trace) (j t : Nat) :
    side u (j+1) t = ((side u j t).2, xor (side u j (t+1)).2 ((side u j t).2 || (side u j t).1)) :=
  Prod.ext rfl (recon_two u j t)

abbrev seed := lam
theorem realizes (u : Trace) (t j : Nat) : zrow (seed u) t j = (side u j t).1 := zrow_lam u t j
theorem of_wall (L : Trace) (j t : Nat) :
    side (fun s => zrow L s 1) j t = (zrow L t j,zrow L t (j+1)) :=
  Prod.ext (history_eq_recon L j t).symm (history_eq_recon L (j+1) t).symm

def advance (s : Pair) : Pair := (s.2, (s.2 >>> 1) ^^^ (s.2 ||| s.1))
def walk : Nat → Pair → Pair
  | 0,s => s
  | j+1,s => walk j (advance s)

theorem walk_succ (s : Pair) (j : Nat) : walk (j+1) s = advance (walk j s) := by
  induction j generalizing s with
  | zero => rfl
  | succ j ih => exact ih (advance s)

def bits (p : Pair) (t : Nat) := (p.1.testBit t,p.2.testBit t)
def Fits (u : Trace) (n a : Nat) := ∀ t, t<n → u t=a.testBit t

theorem packed {u : Trace} {n a : Nat} (h : Fits u n a) (j t : Nat) (ht : j+t<n) :
    bits (walk j (0,a)) t = side u j t := by
  induction j generalizing t with
  | zero => simp [walk, bits, side_zero, h t (by omega)]
  | succ j ih =>
    have x := ih t (by omega)
    have y := ih (t+1) (by omega)
    have p := congrArg Prod.fst x
    have q := congrArg Prod.snd x
    have r := congrArg Prod.snd y
    simp only [bits] at p q r
    simp only [walk_succ, advance, bits, side_succ, Nat.testBit_xor, Nat.testBit_or,
      Nat.testBit_shiftRight, Nat.add_comm 1 t,p,q,r]

def toggle (u : Trace) (t : Nat) := xor (u t) ((1088 : Nat).testBit t)

theorem tail_eq (u : Trace) (j t : Nat) (ht : 11 ≤ t) :
    side (toggle u) j t = side u j t := by
  induction j generalizing t with
  | zero =>
    have bound : 1088 < 2^t := Nat.lt_of_lt_of_le (by decide : 1088 < 2^11)
      (Nat.pow_le_pow_right (by decide) ht)
    simp [side_zero,toggle,Nat.testBit_lt_two_pow bound]
  | succ j ih => simp only [side_succ,ih t ht,ih (t+1) (by omega)]

def Good (n a j : Nat) : Bool :=
  let x := walk j (0,a)
  let y := walk j (0,a ^^^ 1088)
  decide (j≤174 ∧ j+11≤n ∧ x.1%2048=y.1%2048 ∧ x.2%2048=y.2%2048)

theorem good_sync {u : Trace} {n a j : Nat} (hf : Fits u n a) (hg : Good n a j=true) :
    ∀ d t, side (toggle u) (j+d) t = side u (j+d) t := by
  have ⟨_,hn,h₁,h₂⟩ := of_decide_eq_true hg
  have low {x y : Nat} (h : x%2048=y%2048) {t : Nat} (ht : t<11) :
      x.testBit t=y.testBit t := by
    have g := congrArg (fun v : Nat => v.testBit t) h
    change (x%2^11).testBit t=(y%2^11).testBit t at g
    rw [Nat.testBit_mod_two_pow,Nat.testBit_mod_two_pow] at g
    simpa only [decide_eq_true ht, Bool.true_and] using g
  have hf' : Fits (toggle u) n (a ^^^ 1088) := by
    intro t ht; simp [toggle,Nat.testBit_xor,hf t ht]
  intro d
  induction d with
  | zero =>
    intro t
    by_cases ht : t<11
    · rw [Nat.add_zero,←packed hf' j t (by omega),←packed hf j t (by omega)]
      exact Prod.ext (low h₁ ht).symm (low h₂ ht).symm
    · exact tail_eq u j t (by omega)
  | succ d ih =>
    intro t
    change side (toggle u) ((j+d)+1) t = side u ((j+d)+1) t
    simp only [side_succ,ih t,ih (t+1)]

def appendGap (s : Pair) (ten : Bool) : Pair :=
  let d := if ten then 10 else 6
  (s.1+d, s.2 ^^^ (((2^(d-1))-1) <<< s.1))

/-- s stores (known length, temporal bits). Its last bit is a reset.
Append d-1 ones followed by the next zero, for d either six or ten. -/
def path (g : Nat → Bool) (s : Pair) : Nat → Pair
  | 0 => s
  | k+1 => path (fun i => g (i+1)) (appendGap s (g 0)) k

inductive Tree where
  | hit (j : Nat)
  | fork (six ten : Tree)

def valid : Tree → Pair → Bool
  | .hit j,s => Good s.1 s.2 j
  | .fork l r,s => valid l (appendGap s false) && valid r (appendGap s true)

end Ruliology.CellularAutomata.Rule30ResetSwap
