module
public import Ruliology.CellularAutomata.Rule30ZeroBoundary

/-! An exact finite-predecessor criterion, with explicit run updates.
This module does not prove the all-time first-predecessor closure claim. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30InverseRuns
open Rule30ZeroBoundary Rule30Prize

inductive State where | a | b | c

def step : State → Bool → State
  | .a, false => .a
  | .b, false => .b
  | .c, false => .b
  | .a, true => .b
  | .b, true => .c
  | .c, true => .a

def collapse (p q : Bool) : State :=
  if q then .b else if p then .c else .a

theorem collapse_a (p q : Bool) :
    collapse p q = .a ↔ p = false ∧ q = false := by
  cases p <;> cases q <;> simp [collapse]

theorem collapse_step (p q ell : Bool) :
    collapse q (xor ell (p || q)) = step (collapse p q) ell := by
  cases p <;> cases q <;> cases ell <;> rfl

theorem false_preserves_acceptance (s : State) :
    step s false = .a ↔ s = .a := by
  cases s <;> simp [step]

def readCells (s : State) (f : Nat → Bool) : Nat → State
  | 0 => s
  | n+1 => step (readCells s f n) (f n)

theorem collapse_back (y : Nat → Bool) (n : Nat) :
    collapse (back true y n) (back true y (n+1)) =
      readCells .b (fun i => y (i+1)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change collapse (back true y (n+1)) (back true y (n+2)) =
        step (readCells .b (fun i => y (i+1)) n) (y (n+1))
      rw [← ih]
      have hb : back true y (n+2) =
          xor (y (n+1)) (back true y (n+1) || back true y n) := rfl
      rw [hb]
      simpa only [Bool.or_comm] using
        collapse_step (back true y n) (back true y (n+1)) (y (n+1))

theorem finite_inverse_iff_prefix (y : Nat → Bool) (W : Nat)
    (hy : ∀ k, W < k → y k = false) :
    FinSupp (back true y) ↔ readCells .b (fun i => y (i+1)) W = .a := by
  rw [back_fin_iff true (n := W+2) (by omega) (fun k hk => hy k (by omega))]
  rw [show W+2-1=W+1 by omega]
  calc
    (back true y (W+1)=false ∧ back true y (W+2)=false) ↔
        collapse (back true y (W+1)) (back true y (W+2)) = .a :=
      (collapse_a _ _).symm
    _ ↔ readCells .b (fun i => y (i+1)) (W+1) = .a := by
      have h : collapse (back true y (W+1)) (back true y (W+2)) =
          readCells .b (fun i => y (i+1)) (W+1) := by
        simpa only [Nat.add_assoc] using collapse_back y (W+1)
      rw [h]
    _ ↔ readCells .b (fun i => y (i+1)) W = .a := by
      change step (readCells .b (fun i => y (i+1)) W) (y (W+1)) = .a ↔ _
      rw [hy (W+1) (by omega)]
      exact false_preserves_acceptance _

def scan (s : State) : List Bool → State
  | [] => s
  | x::xs => scan (step s x) xs

theorem scan_append (s : State) (xs ys : List Bool) :
    scan s (xs ++ ys) = scan (scan s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => simpa only [List.cons_append, scan] using ih (step s x)

theorem scan_range (s : State) (f : Nat → Bool) (n : Nat) :
    scan s ((List.range n).map f) = readCells s f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [List.range_succ, List.map_append, List.map_singleton,
        scan_append, scan, ih, readCells]

theorem finite_inverse_iff_scan (y : Nat → Bool) (W : Nat)
    (hy : ∀ k, W < k → y k = false) :
    FinSupp (back true y) ↔
      scan .b ((List.range W).map (fun i => y (i+1))) = .a := by
  rw [scan_range]
  exact finite_inverse_iff_prefix y W hy

def norm : State → State | .a => .a | _ => .b

theorem scan_zeros (s : State) (z : Nat) :
    scan s (List.replicate (z+1) false) = norm s := by
  induction z generalizing s with
  | zero => cases s <;> rfl
  | succ z ih =>
      rw [List.replicate_succ, scan, ih]
      cases s <;> rfl

theorem scan_ones (s : State) (n : Nat) :
    scan s (List.replicate n true) =
      if n%3=0 then s else if n%3=1 then step s true else step (step s true) true := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ, scan, ih]
      have hcases : n%3=0 ∨ n%3=1 ∨ n%3=2 := by omega
      rcases hcases with h | h | h
      · have hn : (n+1)%3=1 := by omega
        cases s <;> simp [h, hn, step]
      · have hn : (n+1)%3=2 := by omega
        cases s <;> simp [h, hn, step]
      · have hn : (n+1)%3=0 := by omega
        cases s <;> simp [h, hn, step]

def ofFlag : Bool → State | false => .b | true => .a
def update (n : Nat) (q : Bool) : Bool :=
  if n%3=0 then q else if n%3=1 then false else !q

theorem scan_run (q : Bool) (n z : Nat) :
    scan (ofFlag q)
      (List.replicate n true ++ List.replicate (z+1) false) = ofFlag (update n q) := by
  rw [scan_append, scan_ones, scan_zeros]
  have hcases : n%3=0 ∨ n%3=1 ∨ n%3=2 := by omega
  rcases hcases with h | h | h <;> cases q <;>
    simp [h, ofFlag, update, norm, step]

def encoded : List (Nat × Nat) → List Bool
  | [] => []
  | (n,z)::xs =>
      (List.replicate n true ++ List.replicate (z+1) false) ++ encoded xs
def flags (q : Bool) : List (Nat × Nat) → Bool
  | [] => q
  | (n,_)::xs => flags (update n q) xs

theorem scan_blocks (q : Bool) (xs : List (Nat × Nat)) :
    scan (ofFlag q) (encoded xs) = ofFlag (flags q xs) := by
  induction xs generalizing q with
  | nil => rfl
  | cons p xs ih =>
      rcases p with ⟨n,z⟩
      change scan (ofFlag q)
        ((List.replicate n true ++ List.replicate (z+1) false) ++ encoded xs) =
        ofFlag (flags (update n q) xs)
      rw [scan_append, scan_run, ih]

/-- Concrete run representation of the input, with at least one zero after each run. -/
theorem finite_inverse_run_blocks (y : Nat → Bool) (W : Nat)
    (xs : List (Nat × Nat)) (hy : ∀ k, W < k → y k = false)
    (hword : (List.range W).map (fun i => y (i+1)) = encoded xs) :
    FinSupp (back true y) ↔ flags false xs = true := by
  rw [finite_inverse_iff_scan y W hy, hword]
  have hs : scan .b (encoded xs) = ofFlag (flags false xs) := scan_blocks false xs
  rw [hs]
  cases flags false xs <;> simp [ofFlag]

end Ruliology.CellularAutomata.Rule30InverseRuns

