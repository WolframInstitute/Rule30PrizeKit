module
public import Ruliology.CellularAutomata.Rule30DensityControl

/-! Finite controllers choose the next observed bit before seeing the free right boundary bit. Potential differences certify both block counts. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30DensityControl
open Rule30Jen

structure Node where
  word : Nat
  ctrl : Bool
  z : Nat
  o : Nat
  hx : Nat
  hy : Nat
  deriving Inhabited
structure Mode where
  width : Nat
  denominator : Nat
  black : Nat
  source : Nat
  cap : Nat
  start : Nat
  states : Array Node

def lookup (m : Mode) (i : Nat) := m.states.getD i default
def pick (q : Node) (e : Bool) := if e then q.o else q.z
def blackWeight (r : Row) : Int := (r 0).toNat
def sourceWeight (r : Row) : Int := (r 0 && !(r 1)).toNat
def unpack (q : Node) (j : Nat) := q.word.testBit j
def Fit (m : Mode) (r : Row) (i : Nat) := ∀ j,j<m.width → r j=unpack (lookup m i) j
def predicted (W : Nat) (q : Node) (e : Bool) : Nat → Bool
  | 0 => q.ctrl
  | j+1 => rule (unpack q j) (unpack q (j+1)) (if j+2=W then e else unpack q (j+2))

def GoodMode (m : Mode) : Prop :=
  2≤m.width ∧ 0<m.denominator ∧ m.start<m.states.size ∧
  ∀ i : Fin m.states.size, ∀ e : Bool,
    let q := lookup m i.val
    let j := pick q e
    let v := lookup m j
    j<m.states.size ∧ q.hx≤m.cap ∧ q.hy≤m.cap ∧
    (∀ k : Fin m.width, unpack v k.val=predicted m.width q e k.val) ∧
    (m.denominator:Int)*blackWeight (unpack q)-m.black=(q.hx:Int)-v.hx ∧
    (m.denominator:Int)*sourceWeight (unpack q)-m.source=(q.hy:Int)-v.hy

def run (m : Mode) (r : Row) : Nat → Nat × Row
  | 0 => (m.start,r)
  | t+1 =>
    let prev := run m r t
    let q := lookup m prev.1
    (pick q (prev.2 m.width),next prev.2 q.ctrl)

theorem run_open (m : Mode) (r : Row) (n : Nat) : OpenStep (run m r n).2 (run m r (n+1)).2 :=
  fun _ => rfl

private theorem fit_step {m : Mode} (good : GoodMode m) {r : Row} {i : Nat}
    (hi : i<m.states.size) (fit : Fit m r i) :
    let q := lookup m i
    let j := pick q (r m.width)
    j<m.states.size ∧ Fit m (next r q.ctrl) j := by
  obtain ⟨h,_,_,cells,_,_⟩ := good.2.2.2 ⟨i,hi⟩ (r m.width)
  refine ⟨h,?_⟩;intro k hk
  rw [cells ⟨k,hk⟩]
  cases k with
  | zero => rfl
  | succ k =>
    simp only [next,predicted,fit k (by omega),fit (k+1) hk]
    by_cases eq : k+2=m.width
    · simp [eq]
    · simp [eq,fit (k+2) (by omega)]

theorem run_fit {m : Mode} (good : GoodMode m) (r : Row) (initial : Fit m r m.start) (t : Nat) :
    (run m r t).1<m.states.size ∧ Fit m (run m r t).2 (run m r t).1 := by
  induction t with
  | zero => exact ⟨good.2.2.1,initial⟩
  | succ t ih => exact fit_step good ih.1 ih.2

def total (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n+1 => total f n+f n

/-- Each discrepancy is an endpoint potential difference, uniformly over complete starting rows and all future exterior bits. -/
theorem discrepancy {m : Mode} (good : GoodMode m) (r : Row) (initial : Fit m r m.start) (t : Nat) :
    (m.denominator:Int)*total (fun n => blackWeight (run m r n).2) t-m.black*(t:Int)=
      ((lookup m m.start).hx:Int)-(lookup m (run m r t).1).hx ∧
    (m.denominator:Int)*total (fun n => sourceWeight (run m r n).2) t-m.source*(t:Int)=
      ((lookup m m.start).hy:Int)-(lookup m (run m r t).1).hy := by
  induction t with
  | zero => simp [total,run]
  | succ t ih =>
    have ⟨within,fit⟩ := run_fit good r initial t
    obtain ⟨_,_,_,_,dx,dy⟩ := good.2.2.2 ⟨(run m r t).1,within⟩ ((run m r t).2 m.width)
    have b : blackWeight (run m r t).2=blackWeight (unpack (lookup m (run m r t).1)) := by
      unfold blackWeight;rw [fit 0 (by have := good.1;omega)]
    have s : sourceWeight (run m r t).2=sourceWeight (unpack (lookup m (run m r t).1)) := by
      unfold sourceWeight;rw [fit 0 (by have := good.1;omega),fit 1 (by have := good.1;omega)]
    simp only [total,Int.natCast_add,Int.natCast_one,Int.mul_add,Int.mul_one,b,s]
    rw [show (run m r (t+1)).1=pick (lookup m (run m r t).1) ((run m r t).2 m.width) by rfl]
    dsimp only at dx dy
    obtain ⟨ix,iy⟩ := ih
    constructor <;> omega

/-- Throughout a controlled block both integer discrepancies have absolute value at most the recorded cap. -/
theorem block_bounds {m : Mode} (good : GoodMode m) (r : Row) (initial : Fit m r m.start) (t : Nat) :
    let X := (m.denominator:Int)*total (fun n => blackWeight (run m r n).2) t-m.black*(t:Int)
    let A := (m.denominator:Int)*total (fun n => sourceWeight (run m r n).2) t-m.source*(t:Int)
    (-(m.cap:Int)≤X ∧ X≤m.cap ∧ -(m.cap:Int)≤A ∧ A≤m.cap) := by
  obtain ⟨ex,ea⟩ := discrepancy good r initial t
  have si := good.2.2.2 ⟨m.start,good.2.2.1⟩ false
  have ti := good.2.2.2 ⟨(run m r t).1,(run_fit good r initial t).1⟩ false
  obtain ⟨_,sx,sa,_⟩ := si
  obtain ⟨_,tx,ta,_⟩ := ti
  dsimp only at sx sa tx ta ⊢
  omega

theorem install (m : Mode) (r : Row) : ∃ v,Reach m.width r v ∧ Fit m v m.start :=
  steer_prefix r (unpack (lookup m m.start)) m.width

end Ruliology.CellularAutomata.Rule30DensityControl
