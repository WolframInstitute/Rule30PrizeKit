module
public import Ruliology.CellularAutomata.Rule30SourceDensityRegion

/-! Five space-time periodic histories realize the corners of the black-count and run-end polygon.
The kernel checks the Rule 30 update on every cell of each finite ring through a full period,
then counts the black cells and run ends at the observed bond. Three intervals of one history
attain the additive constants in the three inequalities. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30SourceDensityRegion
open Rule30Jen (rule)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- An ordinary full-line spacetime history with an explicit temporal period
and prescribed black and 10 counts over one period at sites 0 and 1. -/
def Corner (p c a : Nat) : Prop := ∃ u : History, Evolution u ∧
    (∀ t, u (t+p)=u t) ∧ black u 0 0 p=(c:Int) ∧ ends u 0 0 p=(a:Int)

private def rows0 : Array Nat := #[0]
private def film0 (t : Nat) (i : Int) := (rows0.getD (t%1) 0).testBit ((i%1).toNat)
private theorem wrap0 : ((List.range 1).all fun t => (List.range 1).all fun i =>
    film0 (t+1) i == rule (film0 t ((i:Int)-1)) (film0 t i) (film0 t ((i:Int)+1)))=true := by decide +kernel
private theorem step0 : Evolution film0 := by
  intro t i
  let ti:=t%1
  let j:=(i%1).toNat
  have ht : ti<1 := Nat.mod_lt _ (by decide)
  have hj : j<1 := by dsimp [j];omega
  have atCell:=List.all_eq_true.mp (List.all_eq_true.mp wrap0 ti (List.mem_range.mpr ht)) j (List.mem_range.mpr hj)
  have eq:=beq_iff_eq.mp atCell
  have index : (j:Int)=i%1 := by dsimp [j];omega
  simpa only [film0,ti,index,show (t%1+1)%1=(t+1)%1 by omega,
    show (t%1)%1=t%1 by omega,show (i%1)%1=i%1 by omega,
    show (i%1-1)%1=(i-1)%1 by omega,show (i%1+1)%1=(i+1)%1 by omega] using eq

theorem corner0 : Corner 1 0 0 := by
  refine ⟨film0,step0,fun t=>?_,by decide +kernel,by decide +kernel⟩
  funext i;unfold film0;rw [show (t+1)%1=t%1 by omega]

private def rows1 : Array Nat := #[1086,3651,996]
private def film1 (t : Nat) (i : Int) := (rows1.getD (t%3) 0).testBit ((i%12).toNat)
private theorem wrap1 : ((List.range 3).all fun t => (List.range 12).all fun i =>
    film1 (t+1) i == rule (film1 t ((i:Int)-1)) (film1 t i) (film1 t ((i:Int)+1)))=true := by decide +kernel
private theorem step1 : Evolution film1 := by
  intro t i
  let ti:=t%3
  let j:=(i%12).toNat
  have ht : ti<3 := Nat.mod_lt _ (by decide)
  have hj : j<12 := by dsimp [j];omega
  have atCell:=List.all_eq_true.mp (List.all_eq_true.mp wrap1 ti (List.mem_range.mpr ht)) j (List.mem_range.mpr hj)
  have eq:=beq_iff_eq.mp atCell
  have index : (j:Int)=i%12 := by dsimp [j];omega
  simpa only [film1,ti,index,show (t%3+1)%3=(t+1)%3 by omega,
    show (t%3)%3=t%3 by omega,show (i%12)%12=i%12 by omega,
    show (i%12-1)%12=(i-1)%12 by omega,show (i%12+1)%12=(i+1)%12 by omega] using eq

theorem corner1 : Corner 3 1 0 := by
  refine ⟨film1,step1,fun t=>?_,by decide +kernel,by decide +kernel⟩
  funext i;unfold film1;rw [show (t+3)%3=t%3 by omega]

private def rows2 : Array Nat := #[63,1,67,100]
private def film2 (t : Nat) (i : Int) := (rows2.getD (t%4) 0).testBit ((i%7).toNat)
private theorem wrap2 : ((List.range 4).all fun t => (List.range 7).all fun i =>
    film2 (t+1) i == rule (film2 t ((i:Int)-1)) (film2 t i) (film2 t ((i:Int)+1)))=true := by decide +kernel
private theorem step2 : Evolution film2 := by
  intro t i
  let ti:=t%4
  let j:=(i%7).toNat
  have ht : ti<4 := Nat.mod_lt _ (by decide)
  have hj : j<7 := by dsimp [j];omega
  have atCell:=List.all_eq_true.mp (List.all_eq_true.mp wrap2 ti (List.mem_range.mpr ht)) j (List.mem_range.mpr hj)
  have eq:=beq_iff_eq.mp atCell
  have index : (j:Int)=i%7 := by dsimp [j];omega
  simpa only [film2,ti,index,show (t%4+1)%4=(t+1)%4 by omega,
    show (t%4)%4=t%4 by omega,show (i%7)%7=i%7 by omega,
    show (i%7-1)%7=(i-1)%7 by omega,show (i%7+1)%7=(i+1)%7 by omega] using eq

theorem corner2 : Corner 4 3 1 := by
  refine ⟨film2,step2,fun t=>?_,by decide +kernel,by decide +kernel⟩
  funext i;unfold film2;rw [show (t+4)%4=t%4 by omega]

private def rows3 : Array Nat := #[22364166761352886330248667905436134650317087919,943260612036182369894495806319073627262730145,25243588250845306632945480358184787135387500723,38002158838135629437645119658196073906492981660,15259041586202999734043493176161320457643975399,15125989181040382708526709206527425412287510073,15608807197675132236311395596094114999849702223,14454267534527582520094306874066992432633109873,16334798694532088711177678668394574799844590875,12991227405587955460699643260428529581349301673]
private def film3 (t : Nat) (i : Int) := (rows3.getD (t%10) 0).testBit ((i%155).toNat)
private theorem wrap3 : ((List.range 10).all fun t => (List.range 155).all fun i =>
    film3 (t+1) i == rule (film3 t ((i:Int)-1)) (film3 t i) (film3 t ((i:Int)+1)))=true := by decide +kernel
private theorem step3 : Evolution film3 := by
  intro t i
  let ti:=t%10
  let j:=(i%155).toNat
  have ht : ti<10 := Nat.mod_lt _ (by decide)
  have hj : j<155 := by dsimp [j];omega
  have atCell:=List.all_eq_true.mp (List.all_eq_true.mp wrap3 ti (List.mem_range.mpr ht)) j (List.mem_range.mpr hj)
  have eq:=beq_iff_eq.mp atCell
  have index : (j:Int)=i%155 := by dsimp [j];omega
  simpa only [film3,ti,index,show (t%10+1)%10=(t+1)%10 by omega,
    show (t%10)%10=t%10 by omega,show (i%155)%155=i%155 by omega,
    show (i%155-1)%155=(i-1)%155 by omega,show (i%155+1)%155=(i+1)%155 by omega] using eq

theorem corner3 : Corner 10 9 4 := by
  refine ⟨film3,step3,fun t=>?_,by decide +kernel,by decide +kernel⟩
  funext i;unfold film3;rw [show (t+10)%10=t%10 by omega]

private def rows4 : Array Nat := #[1]
private def film4 (t : Nat) (i : Int) := (rows4.getD (t%1) 0).testBit ((i%2).toNat)
private theorem wrap4 : ((List.range 1).all fun t => (List.range 2).all fun i =>
    film4 (t+1) i == rule (film4 t ((i:Int)-1)) (film4 t i) (film4 t ((i:Int)+1)))=true := by decide +kernel
private theorem step4 : Evolution film4 := by
  intro t i
  let ti:=t%1
  let j:=(i%2).toNat
  have ht : ti<1 := Nat.mod_lt _ (by decide)
  have hj : j<2 := by dsimp [j];omega
  have atCell:=List.all_eq_true.mp (List.all_eq_true.mp wrap4 ti (List.mem_range.mpr ht)) j (List.mem_range.mpr hj)
  have eq:=beq_iff_eq.mp atCell
  have index : (j:Int)=i%2 := by dsimp [j];omega
  simpa only [film4,ti,index,show (t%1+1)%1=(t+1)%1 by omega,
    show (t%1)%1=t%1 by omega,show (i%2)%2=i%2 by omega,
    show (i%2-1)%2=(i-1)%2 by omega,show (i%2+1)%2=(i+1)%2 by omega] using eq

theorem corner4 : Corner 1 1 1 := by
  refine ⟨film4,step4,fun t=>?_,by decide +kernel,by decide +kernel⟩
  funext i;unfold film4;rw [show (t+1)%1=t%1 by omega]

theorem optimal_startup : ∃ u : History, Evolution u ∧
    3*black u 0 2 3-5*ends u 0 2 3-3=3 ∧
    2*black u 0 8 9-2*ends u 0 8 9-9=1 ∧
    6*black u 0 4 9-ends u 0 4 9-5*9=5 :=
  ⟨film3,step3,by decide +kernel,by decide +kernel,by decide +kernel⟩

end Ruliology.CellularAutomata.Rule30SourceDensityRegion
