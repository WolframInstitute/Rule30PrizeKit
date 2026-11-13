module
public import Ruliology.CellularAutomata.Rule30ResetFreeCore

/-! Completeness of the mod-three run coloring on a reset-free one-sided row. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30ResetFreeRuns
set_option maxRecDepth 30000
set_option maxHeartbeats 10000000

/-- No finite spatial word0 1^n 0 with n=1mod3. -/
def AvoidReset (f : Nat → Bool) : Prop := ∀ i n,
  f i=false → f (i+n+1)=false →
  (∀ j,j<n → f (i+j+1)=true) → n%3≠1

def scan (f : Nat → Bool) (z : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => if f (z+n+1) then (scan f z n+1)%3 else 0

theorem scan_lt (f : Nat → Bool) (z : Nat) : ∀ n,scan f z n<3 := by
  intro n
  cases n with
  | zero => change (0:Nat)<3;decide
  | succ n =>
    simp only [scan]
    split
    · exact Nat.mod_lt _ (by decide)
    · decide

theorem scan_at_zero (f : Nat → Bool) (z : Nat) :
    ∀ n,f (z+n)=false → scan f z n=0 := by
  intro n hn
  cases n with
  | zero => rfl
  | succ n =>
    have h : f (z+n+1)=false := by simpa only [Nat.add_succ] using hn
    simp only [scan,h,Bool.false_eq_true,↓reduceIte]

/-- The scan remembers the length of the current run after some actual zero. -/
theorem scan_origin (f : Nat → Bool) (z : Nat) (hz : f z=false) :
    ∀ n,∃ r,r≤n ∧ f (z+r)=false ∧
      (∀ j,r<j → j≤n → f (z+j)=true) ∧ scan f z n=(n-r)%3 := by
  intro n
  induction n with
  | zero =>
    refine ⟨0,by omega,by simpa using hz,?_,rfl⟩
    intro j hj hbound
    omega
  | succ n ih =>
    cases current : f (z+n+1) with
    | false =>
      refine ⟨n+1,by omega,by simpa only [Nat.add_succ] using current,?_,?_⟩
      · intro j hj hbound;omega
      · simp [scan,current]
    | true =>
      obtain ⟨r,hr,hzero,hones,hscan⟩ := ih
      refine ⟨r,by omega,hzero,?_,?_⟩
      · intro j hj hbound
        by_cases old : j≤n
        · exact hones j hj old
        · have eqj : j=n+1 := by omega
          rw [eqj]
          simpa only [Nat.add_succ] using current
      · simp only [scan,current,↓reduceIte,hscan]
        have diff : n+1-r=(n-r)+1 := by omega
        simp [diff,Nat.add_mod]

theorem scan_before_zero (f : Nat → Bool) (avoid : AvoidReset f)
    (z : Nat) (hz : f z=false) (n : Nat) (next : f (z+n+1)=false) :
    scan f z n≠1 := by
  obtain ⟨r,hr,hzero,hones,hscan⟩ := scan_origin f z hz n
  have endpoint : z+r+(n-r)+1=z+n+1 := by omega
  have ones : ∀ j,j<n-r → f (z+r+j+1)=true := by
    intro j hj
    have h := hones (r+j+1) (by omega) (by omega)
    simpa only [show z+(r+j+1)=z+r+j+1 by omega] using h
  have no := avoid (z+r) (n-r) hzero (by rw [endpoint];exact next) ones
  rw [hscan]
  exact no

def ColoredFrom (f : Nat → Bool) (K : Nat) (r : Nat → Nat) : Prop :=
  ∀ p,K≤p → r p<3 ∧
    (f p=false → r p=0) ∧
    (f (p-1)=false → f p=true → r p=1) ∧
    (f (p+1)=false → r p≠1) ∧
    r (p+1)=(if f (p+1) then (r p+1)%3 else 0)

theorem colored_after_zero (f : Nat → Bool) (avoid : AvoidReset f)
    (z : Nat) (hz : f z=false) :
    ColoredFrom f (z+1) (fun p => scan f z (p-z)) := by
  intro p hp
  dsimp only
  have restore : z+(p-z)=p := by omega
  refine ⟨scan_lt f z _,?_,?_,?_,?_⟩
  · intro zero
    exact scan_at_zero f z (p-z) (by rw [restore];exact zero)
  · intro previous current
    obtain ⟨m,hm⟩ : ∃ m,p-z=m+1 := ⟨p-z-1,by omega⟩
    have before : z+m=p-1 := by omega
    have position : z+m+1=p := by omega
    rw [hm]
    simp only [scan,position,current,↓reduceIte]
    rw [scan_at_zero f z m (by rw [before];exact previous)]
  · intro next
    exact scan_before_zero f avoid z hz (p-z) (by rw [show z+(p-z)+1=p+1 by omega];exact next)
  · have increment : p+1-z=(p-z)+1 := by omega
    rw [increment]
    simp only [scan,restore]

/-- Every reset-free row admits a faithful run coloring after a finite prefix.
Constant-one rows use an arbitrary mod-three phase. -/
theorem exists_coloring (f : Nat → Bool) (avoid : AvoidReset f) :
    ∃ K,1≤K ∧ ∃ r : Nat → Nat,ColoredFrom f K r := by
  classical
  by_cases haszero : ∃ z,f z=false
  · obtain ⟨z,hz⟩ := haszero
    exact ⟨z+1,by omega,_,colored_after_zero f avoid z hz⟩
  · have allone : ∀ p,f p=true := by
      intro p
      cases eq : f p with
      | false => exact False.elim (haszero ⟨p,eq⟩)
      | true => rfl
    refine ⟨1,by omega,fun p => p%3,?_⟩
    intro p hp
    refine ⟨Nat.mod_lt _ (by decide),?_,?_,?_,?_⟩
    · rw [allone];intro h;cases h
    · rw [allone];intro h;cases h
    · rw [allone];intro h;cases h
    · simp [allone,Nat.add_mod]

/-! ## Shift invariance of `AvoidReset`, constant-row satisfaction, and uniqueness of `ColoredFrom` after any zero -/

/-- **Shift Invariance of `AvoidReset`, Constant-Row Satisfaction, and Uniqueness of `ColoredFrom` After Any Zero (`avoidReset_shift_and_coloredFrom_unique_after_zero`).** -/
theorem avoidReset_shift_and_coloredFrom_unique_after_zero
    (f : Nat → Bool) (d K z m : Nat) (b : Bool) (r1 r2 : Nat → Nat) :
    (AvoidReset f → AvoidReset (fun i => f (d + i))) ∧
    AvoidReset (fun _ => b) ∧
    (ColoredFrom f K r1 → ColoredFrom f K r2 → K ≤ z → f z = false →
      r1 (z + m) = r2 (z + m)) := by
  refine ⟨fun hav i n hi hn hones => ?_, fun i n hi hn hones => ?_, fun hc1 hc2 hKz hfz => ?_⟩
  · exact hav (d + i) n hi (by simpa only [Nat.add_assoc] using hn)
      (fun j hj => by simpa only [Nat.add_assoc] using hones j hj)
  · cases b
    · cases n with
      | zero => decide
      | succ n => have h0 := hones 0 (by omega); cases h0
    · cases hi
  · induction m with
    | zero =>
      rw [Nat.add_zero, (hc1 z hKz).2.1 hfz, (hc2 z hKz).2.1 hfz]
    | succ m ih =>
      rw [show z + (m + 1) = (z + m) + 1 by omega,
          (hc1 (z + m) (by omega)).2.2.2.2,
          (hc2 (z + m) (by omega)).2.2.2.2, ih]

end Ruliology.CellularAutomata.Rule30ResetFreeRuns
