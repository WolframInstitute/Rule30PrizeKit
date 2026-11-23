module
public import Ruliology.CellularAutomata.Rule30SourceDensityRegion

/-! For the two corners with black densities 3/4 and 9/10, six-cell potentials give a
nonnegative loss at every tick. The kernel checks every possible zero-loss transition.
After six or twelve consecutive zero-loss transitions, respectively, the pair of columns
one tick into the interval agrees with the same pair four or ten ticks later. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30DensityEscape
open Rule30Jen (rule cell)
open Rule30SourceDensityRegion
open Rule30SourceObservables (source bit count)

abbrev W := Fin 64
def pack (a b c d e f : Bool) : W :=
  Fin.ofNat 64 (a.toNat+2*b.toNat+4*c.toNat+8*d.toNat+16*e.toNat+32*f.toNat)
def period (high : Bool) : Nat := if high then 10 else 4
def slope (high : Bool) : Int := if high then 8 else 5
def weight (high : Bool) : Int := if high then 3 else 7
def base (high : Bool) : Int := if high then 6 else 2

def lowPot : Array Nat := #[0,0,1,4,1,0,1,3,0,0,1,3,1,0,2,3,0,0,1,4,1,0,2,3,0,0,1,3,1,0,2,3,0,0,1,4,1,0,1,3,0,0,1,3,1,0,2,3,0,0,1,4,1,0,2,3,0,0,1,3,1,0,2,3]
def lowNext : Array (List W) := #[
  [],[3,35],[7,39],[4,36],[15,47],[],[11,43],[8,9,40,41],
  [],[],[27,59],[24,25,56,57],[23,55],[],[19,51],[16,17,48,49],
  [],[],[31,63],[28,60],[23,55],[],[19,51],[16,17,48,49],
  [],[],[11,43],[8,9,40,41],[7,39],[],[3,35],[0,1,32,33],
  [],[51],[55],[52],[63],[],[59],[56,57],
  [],[],[43],[40,41],[39],[],[35],[32,33],
  [],[],[31],[28],[23],[],[19],[16,17],
  [],[],[11],[8,9],[7],[],[3],[0,1]]
def highPot : Array Nat := #[0,1,0,2,0,0,0,4,0,2,0,6,0,0,0,5,0,3,0,2,0,0,0,5,0,4,0,4,0,0,0,3,0,1,0,2,0,0,0,6,0,2,0,4,0,0,0,3,0,3,0,2,0,0,0,5,0,4,0,4,0,0,0,3]
def highNext : Array (List W) := #[
  [],[3,35],[39],[4,5,36,37],[],[],[11],[9,41],
  [],[31,63],[],[25,57],[],[],[],[17,49],
  [],[27,59],[],[28,29,60,61],[],[],[],[17,49],
  [],[15],[11],[9,41],[39],[],[],[1,33],
  [],[51],[],[52,53],[],[],[],[57],
  [],[47],[],[41],[39],[],[],[33],
  [],[27],[],[28,29],[],[],[],[17],
  [],[15],[11],[9],[],[],[],[1]]

def potential (m : Bool) (x : W) : Int := ((if m then highPot else lowPot).getD x.val 0 : Nat)
def next (m : Bool) (x : W) : List W := (if m then highNext else lowNext).getD x.val []
def loss (m : Bool) (x y : W) : Int :=
  potential m x - potential m y + base m + weight m * bit (source (x.val.testBit 0) (x.val.testBit 1))
    - slope m * bit (x.val.testBit 0)
theorem range_potential : ∀ m x, 0 ≤ potential m x ∧ potential m x ≤ (if m then 6 else 4) := by decide +kernel

private theorem edge : ∀ m l a b c d e f r : Bool,
    let x:=pack a b c d e f
    let y:=pack (rule l a b) (rule a b c) (rule b c d) (rule c d e) (rule d e f) (rule e f r)
    0 ≤ loss m x y ∧ (loss m x y=0 → y ∈ next m x) := by decide +kernel

def band (u : History) (j : Int) (t : Nat) :=
  pack (u t j) (u t (j+1)) (u t (j+2)) (u t (j+3)) (u t (j+4)) (u t (j+5))

theorem band_edge {u : History} (hu : Evolution u) (m : Bool) (j : Int) (t : Nat) :
    0 ≤ loss m (band u j t) (band u j (t+1)) ∧
    (loss m (band u j t) (band u j (t+1))=0 → band u j (t+1) ∈ next m (band u j t)) := by
  unfold band
  rw [hu,hu,hu,hu,hu,hu]
  simpa only [show j+1-1=j by omega,show j+1+1=j+2 by omega,show j+2-1=j+1 by omega,show j+2+1=j+3 by omega,show j+3-1=j+2 by omega,show j+3+1=j+4 by omega,show j+4-1=j+3 by omega,show j+4+1=j+5 by omega,show j+5-1=j+4 by omega,show j+5+1=j+6 by omega] using edge m (u t (j-1)) (u t j) (u t (j+1)) (u t (j+2)) (u t (j+3))
    (u t (j+4)) (u t (j+5)) (u t (j+6))

private def test (m : Bool) (label : Nat) : Nat → W → Bool
  | 0,x => (next m x).isEmpty || decide (x.val%4=label)
  | n+1,x => (next m x).all (test m label n)

private theorem check : ∀ (m : Bool) (x : W),
    (next m x).all (fun v=>test m (v.val%4) (period m) v)=true := by decide +kernel

private theorem test_sound {m label} (path : Nat→W) (t n : Nat)
    (ok : test m label n (path t)=true)
    (tight : ∀ i,i≤n → path (t+i+1) ∈ next m (path (t+i))) :
    (path (t+n)).val%4=label := by
  induction n generalizing t with
  | zero =>
    have mem:=tight 0 (by omega)
    simp only [Nat.add_zero] at mem ⊢
    cases h : next m (path t) with
    | nil => simp [h] at mem
    | cons y ys => simpa [test,h] using ok
  | succ n ih =>
    have mem:=tight 0 (by omega)
    simp only [Nat.add_zero] at mem
    have pass := List.all_eq_true.mp ok (path (t+1)) mem
    simpa only [show t+1+n=t+(n+1) by omega] using ih (t+1) pass (fun i hi=>by
      simpa only [show t+1+i=t+(i+1) by omega] using tight (i+1) (by omega))

theorem tight_repeat (m : Bool) (path : Nat→W) (t : Nat)
    (tight : ∀ i,i<period m+2 → path (t+i+1) ∈ next m (path (t+i))) :
    (path (t+1+period m)).val%4=(path (t+1)).val%4 := by
  have first:=tight 0 (by omega)
  simp only [Nat.add_zero] at first
  exact test_sound path (t+1) (period m) (List.all_eq_true.mp (check m (path t)) _ first) (fun i hi=>by
    simpa only [show t+1+i=t+(i+1) by omega] using tight (i+1) (by omega))

private theorem unpack : ∀ a b c d e f g h i j k l : Bool,
    (pack a b c d e f).val%4=(pack g h i j k l).val%4 → a=g ∧ b=h := by decide +kernel
private theorem two_bits : ∀ a b c d e f : Bool,
    (pack a b c d e f).val.testBit 0=a ∧ (pack a b c d e f).val.testBit 1=b := by decide +kernel

theorem tight_columns {u : History} (hu : Evolution u) (m : Bool) (j : Int) (t : Nat)
    (flat : ∀ i,i<period m+2 → loss m (band u j (t+i)) (band u j (t+i+1))=0) :
    u (t+1+period m) j=u (t+1) j ∧ u (t+1+period m) (j+1)=u (t+1) (j+1) :=
  unpack _ _ _ _ _ _ _ _ _ _ _ _ (tight_repeat m (band u j) t
    (fun i hi=>(band_edge hu m j (t+i)).2 (flat i hi)))

def accumulated (m : Bool) (u : History) (j : Int) (n : Nat) : Int :=
  potential m (band u j 0)-potential m (band u j n) + base m*(n:Int)
    + weight m*ends u j 0 n - slope m*black u j 0 n

theorem accumulated_step (m : Bool) (u : History) (j : Int) (t : Nat) :
    accumulated m u j (t+1)=accumulated m u j t+loss m (band u j t) (band u j (t+1)) := by
  have b:=two_bits (u t j) (u t (j+1)) (u t (j+2)) (u t (j+3)) (u t (j+4)) (u t (j+5))
  change (band u j t).val.testBit 0=u t j ∧ (band u j t).val.testBit 1=u t (j+1) at b
  simp only [accumulated,black,ends,count,Int.natCast_succ,Int.mul_add,Int.mul_one,
    Nat.zero_add,loss,b.1,b.2];omega

end Ruliology.CellularAutomata.Rule30DensityEscape
