module
public import Ruliology.CellularAutomata.Rule30DensityCornerHistories

/-! One history at every rational point of the polygon, from an arbitrary right half.

`corners_from_any_right_half` holds one corner for ever. Here the five controllers are run one after
another. `schedule` takes any sequence of certified controllers and any durations: some full-line
configuration with the prescribed right half spends `width` steering ticks and then the stated number of
controlled ticks in each, and in every controlled stretch both counts stay within the cap of that corner.

`mixtures_from_any_right_half` then chooses the durations. Epoch `e` gives corner `i` exactly `w i * e`
controlled ticks. The 69 steering ticks and the caps cost a bounded error in each epoch, epoch `e` lasts
`69 + K*e` ticks, so after `n` ticks the two counts differ by at most a multiple of `sqrt (n+1)` from
`n` times their target densities. The targets form the weighted average of the five corners with
weights `w 0, ..., w 4` of positive sum `K`. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30SourceDensityRegion
open Rule30Jen Rule30Realization
open Rule30SourceObservables (count source bit)
open Rule30DensityControl

/-- The rows of one controlled phase: from any complete row, `m.width` steering ticks and then the
controller for ever. This is the half of `physical_mode` that comes before the realization, with its proof. -/
private theorem mode_stream {m : Mode} (good : GoodMode m) (r : Row) :
    ∃ z : Nat → Row, z 0=r ∧ (∀ t, OpenStep (z t) (z (t+1))) ∧ ∀ n,
      -(m.cap:Int)≤(m.denominator:Int)*total (fun t => blackWeight (z (m.width+t))) n-m.black*(n:Int) ∧
      (m.denominator:Int)*total (fun t => blackWeight (z (m.width+t))) n-m.black*(n:Int)≤m.cap ∧
      -(m.cap:Int)≤(m.denominator:Int)*total (fun t => sourceWeight (z (m.width+t))) n-m.source*(n:Int) ∧
      (m.denominator:Int)*total (fun t => sourceWeight (z (m.width+t))) n-m.source*(n:Int)≤m.cap := by
  obtain ⟨v,path,fit⟩ := install m r
  obtain ⟨z,z0,zEnd,zStep⟩ := realize_segment path
  let s (t : Nat) := if t<m.width then z t else (Rule30DensityControl.run m v (t-m.width)).2
  have early (t : Nat) (h : t≤m.width) : s t=z t := by
    by_cases e : t=m.width
    · subst t;simp [s,Rule30DensityControl.run,zEnd]
    · simp [s,show t<m.width by omega]
  have late (t : Nat) : s (m.width+t)=(Rule30DensityControl.run m v t).2 := by
    simp [s,show ¬m.width+t<m.width by omega]
  have phys (t : Nat) : OpenStep (s t) (s (t+1)) := by
    by_cases old : t<m.width
    · rw [early t (by omega),early (t+1) (by omega)];exact zStep t old
    · obtain ⟨n,rfl⟩ : ∃ n,t=m.width+n := ⟨t-m.width,by omega⟩
      rw [late,show m.width+n+1=m.width+(n+1) by omega,late];exact run_open m v n
  refine ⟨s,by rw [early 0 (Nat.zero_le _),z0],phys,fun n => ?_⟩
  simpa only [late] using block_bounds good v fit n

/-- The first tick of phase `k`, when phase `i` lasts `len i` ticks. -/
def startTick (len : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k+1 => startTick len k+len k

private theorem startTick_mono (len : Nat → Nat) {k j : Nat} (h : k≤j) :
    startTick len k≤startTick len j := by
  induction j with
  | zero =>
    have e : k=0 := by omega
    subst e;exact Nat.le_refl _
  | succ j ih =>
    by_cases e : k=j+1
    · subst e;exact Nat.le_refl _
    · have := ih (by omega)
      simp only [startTick];omega

private theorem startTick_ge (len : Nat → Nat) (pos : ∀ k, 0<len k) (k : Nat) : k≤startTick len k := by
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
    have := pos k
    simp only [startTick];omega

/-- The stream that follows phases `0, ..., k` and then stays in phase `k` for ever. -/
private def stage (ext : Nat → Row → Nat → Row) (len : Nat → Nat) (r : Row) : Nat → Nat → Row
  | 0 => ext 0 r
  | k+1 => fun t => if t≤startTick len (k+1) then stage ext len r k t
      else ext (k+1) (stage ext len r k (startTick len (k+1))) (t-startTick len (k+1))

/-- The row on which phase `k` starts. -/
private def phaseRow (ext : Nat → Row → Nat → Row) (len : Nat → Nat) (r : Row) : Nat → Row
  | 0 => r
  | k+1 => stage ext len r k (startTick len (k+1))

private theorem stage_from (ext : Nat → Row → Nat → Row) (len : Nat → Nat) (r : Row)
    (ext0 : ∀ k ρ, ext k ρ 0=ρ) (k t : Nat) (h : startTick len k≤t) :
    stage ext len r k t=ext k (phaseRow ext len r k) (t-startTick len k) := by
  cases k with
  | zero => simp [stage,phaseRow,startTick]
  | succ k =>
    by_cases e : t=startTick len (k+1)
    · subst e;simp [stage,phaseRow,ext0]
    · simp [stage,phaseRow,show ¬t≤startTick len (k+1) by omega]

private theorem stage_step (ext : Nat → Row → Nat → Row) (len : Nat → Nat) (r : Row)
    (ext0 : ∀ k ρ, ext k ρ 0=ρ) (extStep : ∀ k ρ t, OpenStep (ext k ρ t) (ext k ρ (t+1))) (k t : Nat) :
    OpenStep (stage ext len r k t) (stage ext len r k (t+1)) := by
  induction k with
  | zero => exact extStep 0 r t
  | succ k ih =>
    by_cases h : t+1≤startTick len (k+1)
    · have a : stage ext len r (k+1) t=stage ext len r k t := by
        simp [stage,show t≤startTick len (k+1) by omega]
      have b : stage ext len r (k+1) (t+1)=stage ext len r k (t+1) := by simp [stage,h]
      rw [a,b];exact ih
    · rw [stage_from ext len r ext0 (k+1) t (by omega),stage_from ext len r ext0 (k+1) (t+1) (by omega),
        show t+1-startTick len (k+1)=t-startTick len (k+1)+1 by omega]
      exact extStep _ _ _

private theorem stage_stable (ext : Nat → Row → Nat → Row) (len : Nat → Nat) (r : Row) {k j : Nat}
    (h : k≤j) (t : Nat) (ht : t≤startTick len (k+1)) : stage ext len r j t=stage ext len r k t := by
  induction j with
  | zero =>
    have e : k=0 := by omega
    subst e;rfl
  | succ j ih =>
    by_cases e : k=j+1
    · subst e;rfl
    · have m := startTick_mono len (show k+1≤j+1 by omega)
      have a : stage ext len r (j+1) t=stage ext len r j t := by
        simp [stage,show t≤startTick len (j+1) by omega]
      rw [a];exact ih (by omega)

/-- Phases glue: if every phase can start from any row and obeys the interior rule, one stream runs phase
`k` for `len k` ticks, each phase starting on the row where the one before stopped. -/
private theorem glue (ext : Nat → Row → Nat → Row) (len : Nat → Nat) (r : Row)
    (ext0 : ∀ k ρ, ext k ρ 0=ρ) (extStep : ∀ k ρ t, OpenStep (ext k ρ t) (ext k ρ (t+1)))
    (pos : ∀ k, 0<len k) :
    ∃ (s ρ : Nat → Row), s 0=r ∧ (∀ t, OpenStep (s t) (s (t+1))) ∧
      ∀ k o, o≤len k → s (startTick len k+o)=ext k (ρ k) o := by
  let s (t : Nat) := stage ext len r t t
  have eq (k t : Nat) (ht : t≤startTick len (k+1)) : s t=stage ext len r k t := by
    by_cases h : k≤t
    · exact stage_stable ext len r h t ht
    · exact (stage_stable ext len r (show t≤k by omega) t
        (by have := startTick_ge len pos (t+1);omega)).symm
  refine ⟨s,phaseRow ext len r,?_,?_,?_⟩
  · exact ext0 0 r
  · intro t
    have a := eq (t+1) t (by have := startTick_ge len pos (t+1+1);omega)
    rw [a];exact stage_step ext len r ext0 extStep (t+1) t
  · intro k o ho
    rw [eq k (startTick len k+o) (by simp only [startTick];omega),
      stage_from ext len r ext0 k _ (by omega),show startTick len k+o-startTick len k=o by omega]

private theorem total_agrees {f g : Nat → Int} (n : Nat) (h : ∀ t, t<n → f t=g t) :
    total f n=total g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [total];rw [ih (fun t ht => h t (by omega)),h n (by omega)]

private theorem total_as_count (f : Nat → Bool) (n : Nat) :
    total (fun t => ((f t).toNat : Int)) n=count f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have step : ((f n).toNat : Int)=bit (f n) := by cases f n <;> rfl
    simp only [total,count,ih,step]

/-- Over the `n` ticks from tick `s`, both counts of `x` at sites `0` and `1` are within `cap` of the
corner `(c/D, a/D)`. -/
def Near (x : Int → Bool) (D c a cap s n : Nat) : Prop :=
  -(cap : Int)≤(D : Int)*black (evol x) 0 s n-(c : Int)*(n : Int) ∧
  (D : Int)*black (evol x) 0 s n-(c : Int)*(n : Int)≤(cap : Int) ∧
  -(cap : Int)≤(D : Int)*ends (evol x) 0 s n-(a : Int)*(n : Int) ∧
  (D : Int)*ends (evol x) 0 s n-(a : Int)*(n : Int)≤(cap : Int)

/-- **Any schedule of controllers, from any right half.** Phase `k` spends `(m k).width` steering ticks and
then `L k` controlled ticks. One full-line configuration with the prescribed right half follows the whole
schedule: throughout the controlled part of every phase both counts stay within that controller's cap. -/
theorem schedule (m : Nat → Mode) (good : ∀ k, GoodMode (m k)) (L : Nat → Nat) (r : Nat → Bool) :
    ∃ x : Int → Bool, (∀ j : Nat, evol x 0 j=r j) ∧ ∀ k n, n≤L k →
      Near x (m k).denominator (m k).black (m k).source (m k).cap
        (startTick (fun i => (m i).width+L i) k+(m k).width) n := by
  let ext (k : Nat) (ρ : Row) : Nat → Row := Classical.choose (mode_stream (good k) ρ)
  have spec (k : Nat) (ρ : Row) := Classical.choose_spec (mode_stream (good k) ρ)
  obtain ⟨s,ρ,s0,phys,rows⟩ := glue ext (fun i => (m i).width+L i) r (fun k ρ => (spec k ρ).1)
    (fun k ρ => (spec k ρ).2.1) (fun k => by have := (good k).1;omega)
  obtain ⟨x,actual⟩ := realize_stream s phys
  have at0 (t : Nat) : evol x t 0=s t 0 := by simpa using actual t 0
  have at1 (t : Nat) : evol x t 1=s t 1 := by simpa using actual t 1
  refine ⟨x,fun j => by rw [actual 0 j,s0],?_⟩
  intro k n hn
  have h := (spec k (ρ k)).2.2 n
  have row (t : Nat) (ht : t<n) : ext k (ρ k) ((m k).width+t)=
      s (startTick (fun i => (m i).width+L i) k+(m k).width+t) := by
    rw [Nat.add_assoc]
    exact (rows k _ (by show _≤(m k).width+L k;omega)).symm
  have hb : total (fun t => blackWeight (ext k (ρ k) ((m k).width+t))) n=
      black (evol x) 0 (startTick (fun i => (m i).width+L i) k+(m k).width) n := by
    rw [black,← total_as_count]
    exact total_agrees n (fun t ht => by simp only [row t ht,blackWeight,at0])
  have he : total (fun t => sourceWeight (ext k (ρ k) ((m k).width+t))) n=
      ends (evol x) 0 (startTick (fun i => (m i).width+L i) k+(m k).width) n := by
    rw [ends,← total_as_count]
    exact total_agrees n (fun t ht => by simp only [row t ht,sourceWeight,source,Int.zero_add,at0,at1])
  rw [hb,he] at h
  exact h

/-- The five controllers, in the order of the corners `(0,0)`, `(1/3,0)`, `(3/4,1/4)`, `(9/10,2/5)`, `(1,1)`. -/
def cornerMode : Nat → Mode
  | 0 => zero
  | 1 => oneThird
  | 2 => threeQuarters
  | 3 => nineTenths
  | _ => one

theorem cornerMode_good : ∀ i, GoodMode (cornerMode i)
  | 0 => zero_policy
  | 1 => oneThird_policy
  | 2 => threeQuarters_policy
  | 3 => nineTenths_policy
  | _+4 => one_policy

private theorem count_range (f : Nat → Bool) (n : Nat) : 0≤count f n ∧ count f n≤n := by
  induction n with
  | zero => simp [count]
  | succ n ih =>
    have b := Rule30SourceObservables.bit_bounds (f n)
    simp only [count];omega

private theorem count_three (f : Nat → Bool) (T W L : Nat) :
    count f (T+W+L)=count f T+count (fun t => f (T+t)) W+count (fun t => f (T+W+t)) L := by
  have a := Rule30SourceObservables.count_add f T (W+L)
  have b := Rule30SourceObservables.count_add (fun t => f (T+t)) W L
  simp only [Nat.add_assoc] at a b ⊢
  omega

/-- One phase in its own units: the steering ticks cost at most `D*W`, the controlled ticks at most `cap`. -/
private def PhaseBound (W D c a cap : Nat) (dC dA : Int) (L : Nat) : Prop :=
  -(cap:Int)≤(D:Int)*dC-(c:Int)*(L:Int) ∧ (D:Int)*dC-(c:Int)*(L:Int)≤(D:Int)*(W:Int)+(cap:Int) ∧
  -(cap:Int)≤(D:Int)*dA-(a:Int)*(L:Int) ∧ (D:Int)*dA-(a:Int)*(L:Int)≤(D:Int)*(W:Int)+(cap:Int)

private theorem phase_arith {D c cap W L X I c0 c1 : Int} (hD : 0≤D) (h : c1=c0+I+X) (i0 : 0≤I) (i1 : I≤W)
    (x0 : -cap≤D*X-c*L) (x1 : D*X-c*L≤cap) :
    -cap≤D*(c1-c0)-c*L ∧ D*(c1-c0)-c*L≤D*W+cap := by
  have p1 : 0≤D*I := Int.mul_nonneg hD i0
  have p2 : D*I≤D*W := Int.mul_le_mul_of_nonneg_left i1 hD
  have e : D*(c1-c0)=D*I+D*X := by
    rw [h,← Int.mul_add];congr 1;omega
  rw [e];omega

private theorem near_phase {x : Int → Bool} {D c a cap T W L : Nat} (near : Near x D c a cap (T+W) L) :
    PhaseBound W D c a cap (black (evol x) 0 0 (T+W+L)-black (evol x) 0 0 T)
      (ends (evol x) 0 0 (T+W+L)-ends (evol x) 0 0 T) L := by
  simp only [Near,black,ends] at near
  obtain ⟨b1,b2,e1,e2⟩ := near
  have hD : (0:Int)≤(D:Int) := Int.natCast_nonneg D
  have kb := count_three (fun t => evol x t 0) T W L
  have rb := count_range (fun t => evol x (T+t) 0) W
  have ke := count_three (fun t => source (evol x t 0) (evol x t (0+1))) T W L
  have re := count_range (fun t => source (evol x (T+t) 0) (evol x (T+t) (0+1))) W
  have hb := phase_arith hD kb rb.1 rb.2 b1 b2
  have he := phase_arith hD ke re.1 re.2 e1 e2
  simp only [PhaseBound,black,ends,Nat.zero_add]
  exact ⟨hb.1,hb.2,he.1,he.2⟩

/-- One epoch: the five phases `5e, ..., 5e+4`, where corner `i` gets `w i * e` controlled ticks. -/
private theorem epoch_step (w : Nat → Nat) (T : Nat → Nat) (C A : Nat → Int)
    (tick : ∀ k, T (k+1)=T k+((cornerMode (k%5)).width+w (k%5)*(k/5)))
    (step : ∀ k, PhaseBound (cornerMode (k%5)).width (cornerMode (k%5)).denominator
      (cornerMode (k%5)).black (cornerMode (k%5)).source (cornerMode (k%5)).cap
      (C (k+1)-C k) (A (k+1)-A k) (w (k%5)*(k/5))) (e : Nat) :
    T (5*e+5)=T (5*e)+69+(w 0*e+w 1*e+w 2*e+w 3*e+w 4*e) ∧
    -177≤60*(C (5*e+5)-C (5*e))-
      (20*((w 1*e : Nat) : Int)+45*((w 2*e : Nat) : Int)+54*((w 3*e : Nat) : Int)+60*((w 4*e : Nat) : Int)) ∧
    60*(C (5*e+5)-C (5*e))-
      (20*((w 1*e : Nat) : Int)+45*((w 2*e : Nat) : Int)+54*((w 3*e : Nat) : Int)+60*((w 4*e : Nat) : Int))≤4317 ∧
    -177≤60*(A (5*e+5)-A (5*e))-
      (15*((w 2*e : Nat) : Int)+24*((w 3*e : Nat) : Int)+60*((w 4*e : Nat) : Int)) ∧
    60*(A (5*e+5)-A (5*e))-
      (15*((w 2*e : Nat) : Int)+24*((w 3*e : Nat) : Int)+60*((w 4*e : Nat) : Int))≤4317 := by
  have m0 : (5*e)%5=0 := by omega
  have m1 : (5*e+1)%5=1 := by omega
  have m2 : (5*e+2)%5=2 := by omega
  have m3 : (5*e+3)%5=3 := by omega
  have m4 : (5*e+4)%5=4 := by omega
  have d0 : (5*e)/5=e := by omega
  have d1 : (5*e+1)/5=e := by omega
  have d2 : (5*e+2)/5=e := by omega
  have d3 : (5*e+3)/5=e := by omega
  have d4 : (5*e+4)/5=e := by omega
  have t0 := tick (5*e)
  have t1 := tick (5*e+1)
  have t2 := tick (5*e+2)
  have t3 := tick (5*e+3)
  have t4 := tick (5*e+4)
  rw [m0,d0] at t0
  rw [m1,d1] at t1
  rw [m2,d2] at t2
  rw [m3,d3] at t3
  rw [m4,d4] at t4
  have u0 : T (5*e+1)=T (5*e)+(2+w 0*e) := t0
  have u1 : T (5*e+2)=T (5*e+1)+(6+w 1*e) := t1
  have u2 : T (5*e+3)=T (5*e+2)+(21+w 2*e) := t2
  have u3 : T (5*e+4)=T (5*e+3)+(37+w 3*e) := t3
  have u4 : T (5*e+5)=T (5*e+4)+(3+w 4*e) := t4
  have s0 := step (5*e)
  have s1 := step (5*e+1)
  have s2 := step (5*e+2)
  have s3 := step (5*e+3)
  have s4 := step (5*e+4)
  rw [m0,d0] at s0
  rw [m1,d1] at s1
  rw [m2,d2] at s2
  rw [m3,d3] at s3
  rw [m4,d4] at s4
  have v0 : PhaseBound 2 1 0 0 0 (C (5*e+1)-C (5*e)) (A (5*e+1)-A (5*e)) (w 0*e) := s0
  have v1 : PhaseBound 6 3 1 0 3 (C (5*e+2)-C (5*e+1)) (A (5*e+2)-A (5*e+1)) (w 1*e) := s1
  have v2 : PhaseBound 21 4 3 1 3 (C (5*e+3)-C (5*e+2)) (A (5*e+3)-A (5*e+2)) (w 2*e) := s2
  have v3 : PhaseBound 37 10 9 4 12 (C (5*e+4)-C (5*e+3)) (A (5*e+4)-A (5*e+3)) (w 3*e) := s3
  have v4 : PhaseBound 3 1 1 1 0 (C (5*e+5)-C (5*e+4)) (A (5*e+5)-A (5*e+4)) (w 4*e) := s4
  obtain ⟨b01,b02,a01,a02⟩ := v0
  obtain ⟨b11,b12,a11,a12⟩ := v1
  obtain ⟨b21,b22,a21,a22⟩ := v2
  obtain ⟨b31,b32,a31,a32⟩ := v3
  obtain ⟨b41,b42,a41,a42⟩ := v4
  refine ⟨by omega,by omega,by omega,by omega,by omega⟩

private theorem epoch_arith {K P e c0 c1 t0 t1 : Int} (hK : 0≤K) (hP0 : 0≤P) (hP : P≤60*K)
    (ht : t1=t0+69+K*e) (lo : -177≤60*(c1-c0)-e*P) (hi : 60*(c1-c0)-e*P≤4317)
    (i1 : -(4317*K*e)≤60*K*c0-P*t0) (i2 : 60*K*c0-P*t0≤4317*K*e) :
    -(4317*K*(e+1))≤60*K*c1-P*t1 ∧ 60*K*c1-P*t1≤4317*K*(e+1) := by
  have p1 : 0≤K*(60*(c1-c0)-e*P+177) := Int.mul_nonneg hK (by omega)
  have p2 : 0≤K*(4317-(60*(c1-c0)-e*P)) := Int.mul_nonneg hK (by omega)
  subst ht
  constructor <;> grind

/-- At the start of epoch `e` the scaled count `60*K*c` differs from `P*t` by at most `4317*K*e`. -/
private def EpochBound (K P : Nat) (c : Int) (t e : Nat) : Prop :=
  -(4317*(K:Int)*(e:Int))≤60*(K:Int)*c-(P:Int)*(t:Int) ∧ 60*(K:Int)*c-(P:Int)*(t:Int)≤4317*(K:Int)*(e:Int)

private theorem epochs (w : Nat → Nat) (T : Nat → Nat) (C A : Nat → Int) (T0 : T 0=0) (C0 : C 0=0)
    (A0 : A 0=0)
    (tick : ∀ k, T (k+1)=T k+((cornerMode (k%5)).width+w (k%5)*(k/5)))
    (step : ∀ k, PhaseBound (cornerMode (k%5)).width (cornerMode (k%5)).denominator
      (cornerMode (k%5)).black (cornerMode (k%5)).source (cornerMode (k%5)).cap
      (C (k+1)-C k) (A (k+1)-A k) (w (k%5)*(k/5))) (e : Nat) :
    T (5*(e+1))=T (5*e)+69+(w 0+w 1+w 2+w 3+w 4)*e ∧
    EpochBound (w 0+w 1+w 2+w 3+w 4) (20*w 1+45*w 2+54*w 3+60*w 4) (C (5*e)) (T (5*e)) e ∧
    EpochBound (w 0+w 1+w 2+w 3+w 4) (15*w 2+24*w 3+60*w 4) (A (5*e)) (T (5*e)) e := by
  have time (e : Nat) : T (5*(e+1))=T (5*e)+69+(w 0+w 1+w 2+w 3+w 4)*e := by
    have h : T (5*(e+1))=T (5*e)+69+(w 0*e+w 1*e+w 2*e+w 3*e+w 4*e) := (epoch_step w T C A tick step e).1
    rw [h];simp only [Nat.add_mul]
  refine ⟨time e,?_⟩
  induction e with
  | zero => simp [EpochBound,T0,C0,A0]
  | succ e ih =>
    obtain ⟨_,cl,ch,al,ah⟩ := epoch_step w T C A tick step e
    obtain ⟨⟨c1,c2⟩,⟨a1,a2⟩⟩ := ih
    have hK : (0:Int)≤((w 0+w 1+w 2+w 3+w 4 : Nat) : Int) := Int.natCast_nonneg _
    have timeI : ((T (5*(e+1)) : Nat) : Int)=
        (T (5*e) : Int)+69+((w 0+w 1+w 2+w 3+w 4 : Nat) : Int)*(e : Int) := by
      exact_mod_cast time e
    have pc : (e : Int)*((20*w 1+45*w 2+54*w 3+60*w 4 : Nat) : Int)=
        20*((w 1*e : Nat) : Int)+45*((w 2*e : Nat) : Int)+54*((w 3*e : Nat) : Int)+60*((w 4*e : Nat) : Int) := by
      push_cast;grind
    have pa : (e : Int)*((15*w 2+24*w 3+60*w 4 : Nat) : Int)=
        15*((w 2*e : Nat) : Int)+24*((w 3*e : Nat) : Int)+60*((w 4*e : Nat) : Int) := by
      push_cast;grind
    rw [← pc] at cl ch
    rw [← pa] at al ah
    have rc := epoch_arith hK (Int.natCast_nonneg _) (by omega) timeI cl ch c1 c2
    have ra := epoch_arith hK (Int.natCast_nonneg _) (by omega) timeI al ah a1 a2
    have e1 : ((e+1 : Nat) : Int)=(e : Int)+1 := by omega
    refine ⟨?_,?_⟩
    · unfold EpochBound;rw [e1];exact rc
    · unfold EpochBound;rw [e1];exact ra

private theorem inside_arith {K P e c0 b d t0 : Int} (hK : 0≤K) (hP0 : 0≤P) (hP : P≤60*K) (he : 0≤e)
    (b0 : 0≤b) (b1 : b≤d) (d1 : d≤69+K*e)
    (i1 : -(4317*K*e)≤60*K*c0-P*t0) (i2 : 60*K*c0-P*t0≤4317*K*e) :
    -(K*(60*K+4317)*(e+1))≤60*K*(c0+b)-P*(t0+d) ∧ 60*K*(c0+b)-P*(t0+d)≤K*(60*K+4317)*(e+1) := by
  have p1 : 0≤K*(d-b) := Int.mul_nonneg hK (by omega)
  have p2 : 0≤(60*K-P)*d := Int.mul_nonneg (by omega) (by omega)
  have p3 : 0≤P*d := Int.mul_nonneg hP0 (by omega)
  have p4 : 0≤K*(69+K*e-d) := Int.mul_nonneg hK (by omega)
  have p5 : 0≤K*K := Int.mul_nonneg hK hK
  have p6 : 0≤K*b := Int.mul_nonneg hK b0
  have p7 : 0≤K*K*e := Int.mul_nonneg p5 he
  have p8 : 0≤K*e := Int.mul_nonneg hK he
  constructor <;> grind

private theorem square_arith {E G e n : Int} (hG : 0≤G) (lo : -(G*(e+1))≤E) (hi : E≤G*(e+1))
    (root : (e+1)*(e+1)≤2*(n+1)) : E^2≤2*G^2*(n+1) := by
  have p1 : 0≤(G*(e+1)-E)*(G*(e+1)+E) := Int.mul_nonneg (by omega) (by omega)
  have p2 : 0≤G*G*(2*(n+1)-(e+1)*(e+1)) := Int.mul_nonneg (Int.mul_nonneg hG hG) (by omega)
  grind

private theorem locate (τ : Nat → Nat) (τ0 : τ 0=0) (grow : ∀ e, τ e<τ (e+1)) (n : Nat) :
    ∃ e, τ e≤n ∧ n<τ (e+1) := by
  induction n with
  | zero => exact ⟨0,by omega,by have := grow 0;omega⟩
  | succ n ih =>
    obtain ⟨e,h1,h2⟩ := ih
    by_cases h : n+1<τ (e+1)
    · exact ⟨e,by omega,h⟩
    · exact ⟨e+1,by omega,by have := grow (e+1);omega⟩

private theorem root_bound (K : Nat) (hK : 0<K) (τ : Nat → Nat) (τ0 : τ 0=0)
    (step : ∀ e, τ (e+1)=τ e+69+K*e) (e : Nat) : (e+1)*(e+1)≤2*τ e+2 := by
  induction e with
  | zero => rw [τ0];decide
  | succ e ih =>
    have h := step e
    have g : e≤K*e := Nat.le_mul_of_pos_left e hK
    have x : (e+1+1)*(e+1+1)=(e+1)*(e+1)+2*e+3 := by
      rw [Nat.add_mul,Nat.mul_add];omega
    omega

/-- The scaled count `60*K*count` differs from `P*n` by at most `K*(60*K+4317)*sqrt(2*n+2)`.
Squaring both sides expresses the estimate using integers. -/
def RootClose (K P : Nat) (count : Int) (n : Nat) : Prop :=
  (60*(K:Int)*count-(P:Int)*(n:Int))^2≤2*((K:Int)*(60*(K:Int)+4317))^2*((n:Int)+1)

private theorem close_of_epoch {K P : Nat} {c0 b : Int} {t0 d e : Nat} (hP : P≤60*K)
    (inv : EpochBound K P c0 t0 e) (b0 : 0≤b) (b1 : b≤d) (d1 : (d:Int)≤69+(K:Int)*(e:Int))
    (root : (e+1)*(e+1)≤2*(t0+d)+2) : RootClose K P (c0+b) (t0+d) := by
  obtain ⟨i1,i2⟩ := inv
  have hK : (0:Int)≤(K:Int) := Int.natCast_nonneg K
  have h := inside_arith hK (Int.natCast_nonneg P) (by omega) (Int.natCast_nonneg e) b0 b1 d1 i1 i2
  have r : (((e+1)*(e+1) : Nat) : Int)≤((2*(t0+d)+2 : Nat) : Int) := Int.ofNat_le.mpr root
  push_cast at r
  unfold RootClose
  rw [show ((t0+d : Nat) : Int)=(t0:Int)+(d:Int) by omega]
  exact square_arith (Int.mul_nonneg hK (by omega)) h.1 h.2 (by omega)

private theorem black_two (u : History) (j : Int) (a d : Nat) :
    black u j 0 (a+d)=black u j 0 a+black u j a d := by
  simp only [black,Nat.zero_add]
  exact Rule30SourceObservables.count_add (fun t => u t j) a d

private theorem ends_two (u : History) (j : Int) (a d : Nat) :
    ends u j 0 (a+d)=ends u j 0 a+ends u j a d := by
  simp only [ends,Nat.zero_add]
  exact Rule30SourceObservables.count_add (fun t => source (u t j) (u t (j+1))) a d

/-- **Every rational point of the polygon, from any right half.** Give the five corners the weights
`w 0, ..., w 4`, with sum `K > 0`. Then every prescribed right half belongs to a full-line configuration whose
black count and run-end count at sites `0` and `1`, over the first `n` ticks for every `n`, are within
`K*(60*K+4317)*sqrt(2*n+2)/(60*K)` of `n` times the weighted average of the corners. So both densities converge,
to `(20*w 1+45*w 2+54*w 3+60*w 4)/(60*K)` and `(15*w 2+24*w 3+60*w 4)/(60*K)`. -/
theorem mixtures_from_any_right_half (w : Nat → Nat) (pos : 0<w 0+w 1+w 2+w 3+w 4) (r : Nat → Bool) :
    ∃ x : Int → Bool, (∀ j : Nat, evol x 0 j=r j) ∧ ∀ n : Nat,
      RootClose (w 0+w 1+w 2+w 3+w 4) (20*w 1+45*w 2+54*w 3+60*w 4) (black (evol x) 0 0 n) n ∧
      RootClose (w 0+w 1+w 2+w 3+w 4) (15*w 2+24*w 3+60*w 4) (ends (evol x) 0 0 n) n := by
  obtain ⟨x,right,sched⟩ := schedule (fun k => cornerMode (k%5)) (fun k => cornerMode_good _)
    (fun k => w (k%5)*(k/5)) r
  refine ⟨x,right,fun n => ?_⟩
  let T := startTick (fun i => (cornerMode (i%5)).width+w (i%5)*(i/5))
  have tick (k : Nat) : T (k+1)=T k+((cornerMode (k%5)).width+w (k%5)*(k/5)) := rfl
  have step (k : Nat) : PhaseBound (cornerMode (k%5)).width (cornerMode (k%5)).denominator
      (cornerMode (k%5)).black (cornerMode (k%5)).source (cornerMode (k%5)).cap
      (black (evol x) 0 0 (T (k+1))-black (evol x) 0 0 (T k))
      (ends (evol x) 0 0 (T (k+1))-ends (evol x) 0 0 (T k)) (w (k%5)*(k/5)) := by
    have h := near_phase (sched k (w (k%5)*(k/5)) (Nat.le_refl _))
    rw [tick k,← Nat.add_assoc];exact h
  have all := epochs w T (fun k => black (evol x) 0 0 (T k)) (fun k => ends (evol x) 0 0 (T k))
    rfl rfl rfl tick step
  have grow (e : Nat) : T (5*e)<T (5*(e+1)) := by
    have h := (all e).1
    omega
  obtain ⟨e,h1,h2⟩ := locate (fun e => T (5*e)) rfl grow n
  have h1' : T (5*e)≤n := h1
  have h2' : n<T (5*(e+1)) := h2
  obtain ⟨time,cb,ca⟩ := all e
  have root := root_bound (w 0+w 1+w 2+w 3+w 4) pos (fun e => T (5*e)) rfl (fun e => (all e).1) e
  have root' : (e+1)*(e+1)≤2*T (5*e)+2 := root
  obtain ⟨d,rfl⟩ : ∃ d, n=T (5*e)+d := ⟨n-T (5*e),by omega⟩
  have rb : 0≤black (evol x) 0 (T (5*e)) d ∧ black (evol x) 0 (T (5*e)) d≤d := count_range _ d
  have re : 0≤ends (evol x) 0 (T (5*e)) d ∧ ends (evol x) 0 (T (5*e)) d≤d := count_range _ d
  have d1 : (d:Int)≤69+((w 0+w 1+w 2+w 3+w 4 : Nat) : Int)*(e : Int) := by
    have timeI : ((T (5*(e+1)) : Nat) : Int)=
        (T (5*e) : Int)+69+((w 0+w 1+w 2+w 3+w 4 : Nat) : Int)*(e : Int) := by
      exact_mod_cast time
    omega
  rw [black_two,ends_two]
  exact ⟨close_of_epoch (by omega) cb rb.1 rb.2 d1 (by omega),
    close_of_epoch (by omega) ca re.1 re.2 d1 (by omega)⟩

end Ruliology.CellularAutomata.Rule30SourceDensityRegion
