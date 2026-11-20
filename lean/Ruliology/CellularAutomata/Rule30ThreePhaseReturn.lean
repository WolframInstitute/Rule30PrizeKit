module

public import Ruliology.CellularAutomata.Rule30Prize

/-! Three temporal bits of two adjacent wheels, followed by two bit masks
recording open runs of lengths one and two modulo three at the three ticks.
Bit zero is the earliest tick. -/
@[expose] public section

namespace Ruliology.CellularAutomata.Rule30ThreePhaseReturn
abbrev C := BitVec 3
structure State where
  prev : C
  cur : C
  one : C
  two : C
  deriving DecidableEq, Repr

def start (x : C) : State := ⟨x,7,~~~x,x⟩

def step (z : State) (c : C) : Option State :=
  if ((c >>> 1) &&& 3) != ((z.prev ^^^ (z.cur ||| c)) &&& 3) then none
  else if (z.one &&& ~~~c) != 0 then none
  else some ⟨z.cur,c,c &&& ~~~(z.one ||| z.two),c &&& z.one⟩

def scan (z : State) : List C → Option State
  | [] => some z
  | c::cs => (step z c).bind (fun w => scan w cs)

private def states : List State := [
  ⟨0,2,2,0⟩,
  ⟨0,5,5,0⟩,
  ⟨0,7,7,0⟩,
  ⟨1,4,4,0⟩,
  ⟨1,5,5,0⟩,
  ⟨1,7,6,1⟩,
  ⟨2,7,5,2⟩,
  ⟨3,0,0,0⟩,
  ⟨3,1,0,0⟩,
  ⟨3,7,4,3⟩,
  ⟨4,6,2,4⟩,
  ⟨4,7,3,4⟩,
  ⟨5,7,2,5⟩,
  ⟨6,7,1,2⟩,
  ⟨6,7,1,6⟩,
  ⟨7,0,0,0⟩,
  ⟨7,1,0,0⟩,
  ⟨7,3,0,1⟩,
  ⟨7,7,0,3⟩,
  ⟨7,7,0,7⟩]

private theorem starts : ∀ x : C, start x ∈ states := by decide +kernel

private theorem stable : ∀ z ∈ states, ∀ c : C,
    (step z c).all (fun w => decide (w ∈ states)) = true := by
  intro z hz
  simp only [states,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

private theorem zero_trap : ∀ z ∈ states, ∀ a b c : C, scan z [0,a,b,c] = none := by
  intro z hz
  simp only [states,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

private theorem trap_after (xs : List C) (z : State) (hz : z ∈ states) (a b c : C) :
    scan z (xs ++ [0,a,b,c]) = none := by
  induction xs generalizing z with
  | nil => exact zero_trap z hz a b c
  | cons x xs ih =>
    simp only [List.cons_append,scan]
    cases he : step z x with
    | none => rfl
    | some w =>
      have h := stable z hz x
      simp [he] at h
      exact ih w h

/-- No reset-free recurrence path in three simultaneous phases from the first
white/black anchor can pass a second white column and three more wheels. -/
theorem three_phase_return (x : C) (between : List C) (a b c : C) :
    scan (start x) (between ++ [0,a,b,c]) = none :=
  trap_after between _ (starts x) a b c

end Ruliology.CellularAutomata.Rule30ThreePhaseReturn
