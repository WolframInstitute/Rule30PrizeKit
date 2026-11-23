module
public import Ruliology.CellularAutomata.Rule30DensityEscape

/-! On the single seed the count deficits at the 3/4 and 9/10 corners grow at least
logarithmically. A sufficiently long zero-loss interval repeats two neighbouring columns
four or ten ticks apart. Propagating those equalities left reaches the later seed edge and
gives a contradiction. Iterating the resulting deadline gives a lower bound at every later tick. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30DensityEscape
open Rule30Jen Rule30SourceDensityRegion

private theorem triangle {a b d : Nat} (lt : a<b) (j : Int) (reach : j-(d:Int)=-(b:Int))
    (initialEq : ∀ k,k≤d → cell (a+k) j=cell (b+k) j ∧ cell (a+k) (j+1)=cell (b+k) (j+1)) : False := by
  have shell (z : Nat) :
      ∀ k, k+z≤d → cell (a+k) (j-z)=cell (b+k) (j-z) ∧
        cell (a+k) (j-z+1)=cell (b+k) (j-z+1) := by
    induction z with
    | zero => simpa using initialEq
    | succ z ih =>
      intro k hk
      have h:=ih k (by omega)
      constructor
      · rw [show j-((z+1:Nat):Int)=j-(z:Int)-1 by omega,
          cell_left (a+k) (j-z),cell_left (b+k) (j-z)]
        rw [Nat.add_assoc,Nat.add_assoc,(ih (k+1) (by omega)).1,h.1,h.2]
      · simpa only [show j-((z+1:Nat):Int)+1=j-(z:Int) by omega] using h.1
  have impossible := (shell d 0 (by omega)).1
  simp only [Nat.add_zero,reach] at impossible
  rw [cell_eq_false_of_lt a _ (by omega),cell_left_edge b] at impossible
  contradiction

private theorem abounds (j : Int) : -(j.natAbs:Int)≤j ∧ j≤(j.natAbs:Int) := by
  cases j <;> simp <;> omega

/-- At every spatial band and every sufficiently late starting age, a strict loss
occurs by the indicated explicit deadline. Both endpoint ages are absolute. -/
theorem loss_in_interval (m : Bool) (j : Int) (s : Nat) (late : j.natAbs≤s) :
    ∃ t, s≤t ∧ t<2*s+j.natAbs+2*period m+3 ∧
      0<loss m (band cell j t) (band cell j (t+1)) := by
  apply Classical.byContradiction
  intro deny
  let p:=period m
  have hp : 0<p := by cases m <;> decide
  let a:=s+1
  let b:=s+1+p
  let d:=((b:Int)+j).toNat
  have jb:=abounds j
  have de : (d:Int)=(b:Int)+j := by dsimp [d,b];omega
  apply triangle (a:=a) (b:=b) (d:=d) (by dsimp [a,b];omega) j (by omega)
  intro k hk
  have h:=tight_columns (u:=cell) (fun _ _=>rfl) m j (s+k) (fun i hi=>by
    have nonneg:=(band_edge (u:=cell) (fun _ _=>rfl) m j (s+k+i)).1
    apply Classical.byContradiction
    intro ne
    apply deny
    refine ⟨s+k+i,by omega,?_,by omega⟩
    dsimp [b,p] at de
    omega)
  dsimp [a,b,p];simpa only [show s+k+1+period m=s+1+period m+k by omega,
      show s+k+1=s+1+k by omega,show s+1+k+period m=s+1+period m+k by omega] using And.intro h.1.symm h.2.symm

private theorem accum_mono (m : Bool) (j : Int) {a b : Nat} (le : a≤b) :
    accumulated m cell j a ≤ accumulated m cell j b := by
  induction b with
  | zero => have : a=0 := by omega
            rw [this];omega
  | succ b ih =>
    by_cases eq : a=b+1
    · rw [eq];omega
    · have h:=ih (by omega)
      have v:=(band_edge (u:=cell) (fun _ _=>rfl) m j b).1
      rw [accumulated_step];omega

def deadline (m : Bool) (j : Int) : Nat → Nat
  | 0 => j.natAbs
  | k+1 => 2*deadline m j k+j.natAbs+2*period m+3

private theorem large (m : Bool) (j : Int) (k : Nat) : j.natAbs≤deadline m j k := by
  cases k <;> simp only [deadline] <;> omega

private theorem gained (m : Bool) (j : Int) (k : Nat) : (k:Int) ≤ accumulated m cell j (deadline m j k) := by
  induction k with
  | zero =>
    have h:=accum_mono m j (a:=0) (b:=deadline m j 0) (by omega)
    have hz : accumulated m cell j 0=0 := by simp [accumulated,black,ends,Rule30SourceObservables.count]
    omega
  | succ k ih =>
    obtain ⟨t,lo,hi,gain⟩:=loss_in_interval m j (deadline m j k) (large m j k)
    have h₁:=accum_mono m j lo
    have h₂:=accum_mono m j (a:=t+1) (b:=deadline m j (k+1)) (by simp only [deadline];omega)
    rw [accumulated_step] at h₂
    omega

/-- At the kth deadline and every later tick, the count deficit at the chosen corner is at least
`k - 4` or `k - 6`, respectively. The density ratios may still converge to the corner. -/
theorem singleton_margin (m : Bool) (j : Int) (k n : Nat) (hn : deadline m j k≤n) :
    (k:Int)-(if m then 6 else 4) ≤ base m*(n:Int)+weight m*ends cell j 0 n-slope m*black cell j 0 n := by
  have a:=gained m j k
  have b:=accum_mono m j hn
  have init:=(range_potential m (band cell j 0)).2
  have final:=(range_potential m (band cell j n)).1
  unfold accumulated at b;unfold accumulated at a
  omega

theorem margin_three_quarters (j : Int) (k n : Nat) (hn : deadline false j k≤n) :
    (k:Int)-4 ≤ 2*(n:Int)+7*ends cell j 0 n-5*black cell j 0 n := singleton_margin false j k n hn

theorem margin_nine_tenths (j : Int) (k n : Nat) (hn : deadline true j k≤n) :
    (k:Int)-6 ≤ 6*(n:Int)+3*ends cell j 0 n-8*black cell j 0 n := singleton_margin true j k n hn
end Ruliology.CellularAutomata.Rule30DensityEscape
