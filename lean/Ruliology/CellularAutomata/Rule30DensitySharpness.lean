module
public import Ruliology.CellularAutomata.Rule30SourceDensityCorners

/-! A uniform linear bound on black and run-end counts over all nonzero finite seeds must hold
at the five periodic corners with zero additive constant. For any prescribed number of periods,
a finite seed copies the periodic history inside the observation cone. A black cell beyond the
cone makes the seed nonzero. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30SourceDensityRegion
open Rule30Jen Rule30Realization
open Rule30SourceObservables (count source)

private theorem periodic_count {f : Nat→Bool} {p : Nat} (per : ∀ t,f (t+p)=f t) (k : Nat) :
    count f (k*p)=(k:Int)*count f p := by
  have shifts (k t : Nat) : f (k*p+t)=f t := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show (k+1)*p+t=(k*p+t)+p by simp [Nat.add_mul];omega,per,ih]
  induction k with
  | zero => simp [count]
  | succ k ih =>
    have same := shifts k
    rw [Nat.add_mul,Nat.one_mul,Rule30SourceObservables.count_add,ih]
    simp only [same,Int.natCast_succ,Int.add_mul,Int.one_mul]

theorem repeated_corner {p c a} (corner : Corner p c a) :
    ∃ u : History, Evolution u ∧ ∀ k : Nat,
      black u 0 0 (k*p)=(k:Int)*(c:Int) ∧ ends u 0 0 (k*p)=(k:Int)*(a:Int) := by
  obtain ⟨u,hu,per,hc,ha⟩:=corner
  refine ⟨u,hu,fun k=>?_⟩
  change count (fun t=>u (0+t) 0) p=(c:Int) at hc
  change count (fun t=>source (u (0+t) 0) (u (0+t) (0+1))) p=(a:Int) at ha
  simp only [Nat.zero_add,Int.zero_add] at hc ha
  constructor
  · simpa only [black,Nat.zero_add,hc] using periodic_count (f:=fun t=>u t 0)
      (fun t=>congrFun (per t) 0) k
  · simpa only [ends,Nat.zero_add,Int.zero_add,ha] using periodic_count (p:=p)
      (f:=fun t=>source (u t 0) (u t 1)) (fun t=>by rw [per t]) k

def finiteCopy (u : History) (N : Nat) (i : Int) : Bool :=
  if i=(N:Int)+2 then true else if -(N:Int)≤i ∧ i≤(N:Int)+1 then u 0 i else false
private theorem agrees {u : History} (hu : Evolution u) (N t : Nat) (i : Int)
    (lo : -(N:Int)+t≤i) (hi : i≤(N:Int)+1-t) : evol (finiteCopy u N) t i=u t i := by
  induction t generalizing i with
  | zero =>
    change finiteCopy u N i=u 0 i
    simp [finiteCopy,show i≠(N:Int)+2 by omega,show -(N:Int)≤i by omega,show i≤(N:Int)+1 by omega]
  | succ t ih =>
    change rule _ _ _=_
    rw [hu,ih (i-1) (by omega) (by omega),ih i (by omega) (by omega),ih (i+1) (by omega) (by omega)]

private theorem count_agrees {f g : Nat→Bool} (n : Nat) (h: ∀ t,t<n → f t=g t) :
    count f n=count g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [count,h n (by omega),ih (fun t ht=>h t (by omega))]

def FiniteBound (α β γ K : Int) : Prop := ∀ x : Int→Bool,
    (∃ N : Nat, ∀ i,(i < -(N:Int) ∨ (N:Int)<i) → x i=false) → (∃i,x i=true) →
    ∀ n : Nat, α*black (evol x) 0 0 n+β*ends (evol x) 0 0 n≤γ*(n:Int)+K

theorem finite_corner_bound {α β γ K : Int} (bound : FiniteBound α β γ K)
    {p c a} (corner : Corner p c a) : α*(c:Int)+β*(a:Int)≤γ*(p:Int) := by
  obtain ⟨u,hu,reps⟩:=repeated_corner corner
  let k:=K.natAbs+1
  let N:=k*p
  have copy:=bound (finiteCopy u N) ⟨N+2,fun i hi=>by
    simp [finiteCopy,show i≠(N:Int)+2 by omega,show ¬(-(N:Int)≤i ∧ i≤(N:Int)+1) by omega]⟩
    ⟨(N:Int)+2,by simp [finiteCopy]⟩ N
  have same (i : Int) (lo : 0≤i) (hi : i≤1) (t : Nat) (ht : t<N) :
      evol (finiteCopy u N) t i=u t i := agrees hu N t i (by omega) (by omega)
  have cb : black (evol (finiteCopy u N)) 0 0 N=black u 0 0 N :=
    count_agrees N (fun t ht=>by simpa only [Nat.zero_add] using same 0 (by decide) (by decide) t ht)
  have ca : ends (evol (finiteCopy u N)) 0 0 N=ends u 0 0 N :=
    count_agrees N (fun t ht=>by simp only [Nat.zero_add,Int.zero_add,same 0 (by decide) (by decide) t ht,same 1 (by decide) (by decide) t ht])
  rw [cb,ca] at copy
  obtain ⟨bc,ac⟩:=reps k
  dsimp only [N] at copy
  rw [bc,ac,Int.natCast_mul] at copy
  have coef : (k:Int)*(α*c+β*a-γ*p)≤K := by
    simp only [Int.mul_sub,Int.mul_add]
    have h1 : (k:Int)*(α*c)=α*(k*c) := by ac_rfl
    have h2 : (k:Int)*(β*a)=β*(k*a) := by ac_rfl
    have h3 : (k:Int)*(γ*p)=γ*(k*p) := by ac_rfl
    rw [h1,h2,h3];omega
  apply Classical.byContradiction
  intro no
  have ge:=Int.mul_le_mul_of_nonneg_left (show 1≤α*(c:Int)+β*(a:Int)-γ*(p:Int) by omega) (show (0:Int)≤k by omega)
  have large : K<(k:Int) := by dsimp [k];cases K <;> simp <;> omega
  simp only [Int.mul_one] at ge;omega

theorem polygon_necessary {α β γ K : Int} (h : FiniteBound α β γ K) :
    0≤γ ∧ α≤3*γ ∧ 3*α+β≤4*γ ∧ 9*α+4*β≤10*γ ∧ α+β≤γ := by
  have z:=finite_corner_bound h corner0
  have a:=finite_corner_bound h corner1
  have b:=finite_corner_bound h corner2
  have c:=finite_corner_bound h corner3
  have d:=finite_corner_bound h corner4
  omega
end Ruliology.CellularAutomata.Rule30SourceDensityRegion
