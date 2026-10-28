module

public import Ruliology.CellularAutomata.Rule30ZeroBoundary
public import Ruliology.CellularAutomata.Rule30StripCertificates

/-!
# Delayed temporal defects force unbounded spatial tail periods

Let `pure t = decide (t % 4 ≠ 1)`, the column whose even entries are black
and whose free odd entries alternate 0,1. The family `input j` changes
only time `8*j+5` from white to black. Equivalently, its free sequence is
alternating except for a black bit at index `4*j+2`, giving one run 111.
The free sequence avoids 00,11111,010110 and 1011010, for every j.

Every `Theta (free j)` is a valid constrained start and is eventually
periodic in *space*. Nevertheless every eventual spatial period P>0
satisfies `j < 2^P` (`theta_delay_lt_pow_period`). Thus the explicit
choice j=2^M has no eventual period at most M, even with an arbitrary
spatial transient (`theta_explicit_large_periods`).

Proof: a 312-cell table establishes the base defect's recurrent spatial
tail, different from the pure background. Outer locality and temporal
shift equivariance show that different delays have different tails modulo
finite prefixes. A P-periodic tail has at most 2^P residue words. Periods
are inherited by earlier delays, so j>=2^P would force a tail collision.
Temporal periodicity gives eventual spatial periodicity by a separate
finite-profile argument, uniformly in the temporal preperiod.

These are synthetic temporal inputs, not proved finite-right responses or
the canonical single-seed center column. Each spatial member is periodic;
the periods across the family are unbounded.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30DelayedDefectPeriods
open Ruliology.CellularAutomata
open Rule30ZeroBoundary Rule30StripCertificates

def TailEq (f g : Nat → Bool) : Prop := ∃ D, ∀ d, D≤d → f d=g d

def SpatialPeriod (P : Nat) (f : Nat → Bool) : Prop :=
  ∃ D, ∀ d, D≤d → f (d+P)=f d

theorem seg_eq (n : Nat) (f g : Nat → Bool) (h : seg f n=seg g n) :
    ∀ i, i<n → f i=g i := by
  induction n generalizing f g with
  | zero => intro i hi; omega
  | succ n ih =>
    change f 0 :: seg (fun i => f (i+1)) n = g 0 :: seg (fun i => g (i+1)) n at h
    obtain ⟨h0,ht⟩ := List.cons.inj h
    intro i hi
    cases i with
    | zero => exact h0
    | succ i => exact ih _ _ ht i (by omega)

theorem finite_bound (f : Nat → Nat) (N : Nat) :
    ∃ D, ∀ j, j≤N → f j≤D := by
  induction N with
  | zero =>
    refine ⟨f 0,fun j hj => ?_⟩
    have h : j=0 := by omega
    subst j
    exact Nat.le_refl _
  | succ N ih =>
    obtain ⟨D,hD⟩ := ih
    refine ⟨D+f (N+1),fun j hj => ?_⟩
    by_cases h : j≤N
    · have := hD j h; omega
    · have : j=N+1 := by omega
      subst j; omega

theorem agree_from_window (f g : Nat → Bool) (D P : Nat) (hP : 0<P)
    (hf : ∀ d, D≤d → f (d+P)=f d) (hg : ∀ d, D≤d → g (d+P)=g d)
    (hwin : seg (fun i => f (D+i)) P = seg (fun i => g (D+i)) P) : TailEq f g := by
  have hall : ∀ i, f (D+i)=g (D+i) := by
    intro i
    induction i using Nat.strongRecOn with
    | ind i ih =>
      by_cases hi : i<P
      · exact seg_eq P _ _ hwin i hi
      · rw [show D+i=(D+(i-P))+P by omega,hf _ (by omega),hg _ (by omega)]
        exact ih (i-P) (by omega)
  refine ⟨D,fun d hd => ?_⟩
  simpa [show D+(d-D)=d by omega] using hall (d-D)

/-- Infinitely many distinct tail classes cannot share one eventual period. -/
theorem no_common_period_of_distinct (rows : Nat → Nat → Bool)
    (hd : ∀ m n, m<n → ¬TailEq (rows m) (rows n)) (P : Nat) (hP : 0<P) :
    ¬∀ j, SpatialPeriod P (rows j) := by
  intro hp
  classical
  let threshold (j : Nat) := Classical.choose (hp j)
  have hthreshold (j : Nat) : ∀ d, threshold j≤d → rows j (d+P)=rows j d :=
    Classical.choose_spec (hp j)
  obtain ⟨D,hD⟩ := finite_bound threshold (2^P)
  let window (j : Nat) := seg (fun i => rows j (D+i)) P
  obtain ⟨m,n,hmn,hn,hwin⟩ := Rule30Jen.pigeonhole P window
    (fun j => length_seg P _)
  apply hd m n hmn
  exact agree_from_window _ _ D P hP
    (fun d h => hthreshold m d (by have := hD m (by omega); omega))
    (fun d h => hthreshold n d (by have := hD n hn; omega)) hwin

theorem tail_recon_time {a b : Nat → Bool}
    (h : TailEq (fun d => recon a d 0) (fun d => recon b d 0)) (t : Nat) :
    TailEq (fun d => recon a d t) (fun d => recon b d t) := by
  obtain ⟨D,hD⟩ := h
  refine ⟨D+1+t,fun d hd => ?_⟩
  have hlocal := zrow_local (L:=lam a) (L':=lam b) (a:=D+1)
    (by omega) (fun k hk => hD k (by omega)) t d hd
  simpa only [zrow_lam] using hlocal


open Ruliology.CellularAutomata
open Rule30ZeroBoundary Rule30StripCertificates

theorem periodic_window_ext (T P : Nat) (hP : 0<P) (f g : Nat → Bool)
    (hf : ∀ t, T≤t → f (t+P)=f t) (hg : ∀ t, T≤t → g (t+P)=g t)
    (hwin : ∀ t, t<T+P → f t=g t) : ∀ t, f t=g t := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    by_cases ht : t<T+P
    · exact hwin t ht
    · rw [show t=(t-P)+P by omega,hf _ (by omega),hg _ (by omega)]
      exact ih (t-P) (by omega)

theorem recon_time_period (a : Nat → Bool) (T P : Nat)
    (hper : ∀ t, T≤t → a (t+P)=a t) (d t : Nat) (ht : T≤t) :
    recon a d (t+P)=recon a d t := by
  rw [recon_shift]
  apply recon_local
  intro j hj
  simpa [Nat.add_assoc] using hper (t+j) (by omega)

def profile (a : Nat → Bool) (W d : Nat) :=
  seg (fun i => if i<W then recon a d i else recon a (d+1) (i-W)) (2*W)

theorem profile_eq (a : Nat → Bool) (T P : Nat) (hP : 0<P)
    (hper : ∀ t, T≤t → a (t+P)=a t) (m n : Nat)
    (h : profile a (T+P) m=profile a (T+P) n) :
    (∀ t, recon a m t=recon a n t) ∧
    (∀ t, recon a (m+1) t=recon a (n+1) t) := by
  have hfirst : ∀ t, t<T+P → recon a m t=recon a n t := by
    intro t ht
    have he := seg_eq (2*(T+P)) _ _ h t (by omega)
    simpa only [ite_eq_left ht] using he
  have hsecond : ∀ t, t<T+P → recon a (m+1) t=recon a (n+1) t := by
    intro t ht
    have he := seg_eq (2*(T+P)) _ _ h (T+P+t) (by omega)
    simpa only [ite_eq_right (show ¬T+P+t<T+P by omega),Nat.add_sub_cancel_left] using he
  exact ⟨periodic_window_ext T P hP _ _ (recon_time_period a T P hper m)
      (recon_time_period a T P hper n) hfirst,
    periodic_window_ext T P hP _ _ (recon_time_period a T P hper (m+1))
      (recon_time_period a T P hper (n+1)) hsecond⟩

/-- An eventually periodic temporal input reconstructs an eventually
periodic spatial start. The bound may depend on the temporal transient. -/
theorem spatial_of_temporal (a : Nat → Bool) (T P : Nat) (hP : 0<P)
    (hper : ∀ t, T≤t → a (t+P)=a t) :
    Rule30Jen.EventuallyPeriodic (fun d => recon a d 0) := by
  obtain ⟨m,n,hmn,hn,he⟩ := Rule30Jen.pigeonhole (2*(T+P)) (profile a (T+P))
    (fun d => length_seg _ _)
  have hpair := profile_eq a T P hP hper m n he
  have key : ∀ q, (∀ t, recon a (m+q) t=recon a (n+q) t) ∧
      (∀ t, recon a (m+q+1) t=recon a (n+q+1) t) := by
    intro q
    induction q with
    | zero => simpa using hpair
    | succ q ih =>
      refine ⟨?_,fun t => ?_⟩
      · simpa [Nat.add_assoc] using ih.2
      · rw [show m+(q+1)+1=m+q+2 by omega,
          show n+(q+1)+1=n+q+2 by omega,recon_two,recon_two,ih.2,ih.2,ih.1]
  refine ⟨m,n-m,by omega,fun d hd => ?_⟩
  have h := (key (d-m)).1 0
  rw [show m+(d-m)=d by omega,show n+(d-m)=d+(n-m) by omega] at h
  exact h.symm


open Ruliology.CellularAutomata
open Rule30ZeroBoundary

def columns : List (List Bool) := [
  [false, false, false, false, false, false, false, false, false, false, false, false],
  [true, false, true, true, true, true, true, true, true, false, true, true],
  [true, true, false, false, false, false, false, false, true, true, false, false],
  [false, true, true, true, true, true, true, false, false, true, true, false],
  [false, false, false, false, false, false, true, false, false, false, true, false],
  [false, true, true, true, true, false, true, false, false, false, true, false],
  [true, false, false, false, true, true, true, false, false, true, true, false],
  [true, true, true, false, false, false, true, false, true, false, true, false],
  [false, false, true, false, true, false, true, true, true, false, true, true],
  [true, false, true, true, true, true, false, false, true, true, false, false],
  [true, true, false, false, false, true, true, false, false, true, true, false],
  [false, true, true, true, false, false, true, false, false, false, true, false],
  [false, false, false, true, false, false, true, false, false, false, true, false],
  [false, true, false, true, false, true, true, false, false, true, true, false],
  [true, true, true, true, true, false, true, false, true, false, true, false],
  [false, false, false, false, true, false, true, true, true, false, true, true],
  [true, true, true, false, true, true, false, false, true, true, false, false],
  [false, false, true, true, false, true, true, false, false, true, true, false],
  [true, false, false, true, false, false, true, false, false, false, true, false],
  [true, false, false, true, false, false, true, false, false, false, true, false],
  [true, false, true, true, false, true, true, false, false, true, true, false],
  [true, true, false, true, true, false, true, false, true, false, true, false],
  [false, true, false, false, true, false, true, true, true, false, true, true],
  [false, true, false, false, true, true, false, false, true, true, false, false],
  [true, true, false, true, false, true, true, false, false, true, true, false],
  [false, true, true, true, false, false, true, false, false, false, true, false]
]
def timeAt (t : Nat) := if t<8 then t else 8+(t-8)%4
def timeNext (t : Nat) := if t=11 then 8 else t+1
def spaceAt (d : Nat) := if d<12 then d else 12+(d-12)%14
def spaceNext (d : Nat) := if d=25 then 12 else d+1
def raw (d t : Nat) := (columns.getD d []).getD t false
def model (d t : Nat) := raw (spaceAt d) (timeAt t)
def base (t : Nat) := model 1 t
def pure (t : Nat) := decide (t%4≠1)

theorem timeAt_lt (t : Nat) : timeAt t<12 := by unfold timeAt; split <;> omega
theorem spaceAt_lt (d : Nat) : spaceAt d<26 := by unfold spaceAt; split <;> omega
theorem timeAt_succ (t : Nat) : timeAt (t+1)=timeNext (timeAt t) := by
  unfold timeAt timeNext
  split <;> split <;> split <;> omega
theorem spaceAt_succ (d : Nat) : spaceAt (d+1)=spaceNext (spaceAt d) := by
  unfold spaceAt spaceNext
  split <;> split <;> split <;> omega

theorem table_rule : ∀ d, d<26 → ∀ t, t<12 →
    raw (spaceNext (spaceNext d)) t =
      xor (raw (spaceNext d) (timeNext t)) (raw (spaceNext d) t || raw d t) := by
  have checked : (List.range 26).all (fun d => (List.range 12).all fun t =>
    raw (spaceNext (spaceNext d)) t ==
      xor (raw (spaceNext d) (timeNext t)) (raw (spaceNext d) t || raw d t)) = true := by decide
  intro d hd t ht
  exact beq_iff_eq.mp (List.all_eq_true.mp
    (List.all_eq_true.mp checked d (List.mem_range.mpr hd)) t (List.mem_range.mpr ht))

theorem model_rule (d t : Nat) : model (d+2) t =
    xor (model (d+1) (t+1)) (model (d+1) t || model d t) := by
  unfold model
  rw [show d+2=(d+1)+1 by omega,spaceAt_succ,spaceAt_succ,timeAt_succ]
  exact table_rule _ (spaceAt_lt d) _ (timeAt_lt t)

theorem model_zero (t : Nat) : model 0 t=false := by
  have h : ∀ t, t<12 → raw 0 t=false := by decide
  exact h _ (timeAt_lt t)

theorem model_eq_recon : ∀ d t, model d t=recon base d t := by
  have key : ∀ d, (∀ t, model d t=recon base d t) ∧
      (∀ t, model (d+1) t=recon base (d+1) t) := by
    intro d
    induction d with
    | zero => exact ⟨fun t => model_zero t,fun t => rfl⟩
    | succ d ih =>
      refine ⟨ih.2,fun t => ?_⟩
      rw [show d+1+1=d+2 by omega,model_rule,recon_two,ih.2,ih.2,ih.1]
  exact fun d t => (key d).1 t

theorem base_tail (t : Nat) (ht : 8≤t) : base t=pure t := by
  have h : ∀ q, q<4 → raw 1 (8+q)=decide (q≠1) := by decide
  unfold base model
  rw [show spaceAt 1=1 by decide,show timeAt t=8+t%4 by unfold timeAt; split <;> omega]
  simpa [pure] using h (t%4) (by omega)

theorem base_shift_eight : (fun t => base (t+8))=pure := by
  funext t
  rw [base_tail _ (by omega)]
  have hm : (t+8)%4=t%4 := by omega
  simp [pure,hm]

theorem base_formula (t : Nat) : base t=if t=5 then true else pure t := by
  by_cases ht : t<8
  · have h : ∀ t, t<8 → base t=if t=5 then true else pure t := by decide
    exact h t ht
  · rw [base_tail t (by omega),ite_eq_right (by omega)]

theorem pure_not_tail_base : ¬TailEq (fun d => recon pure d 0) (fun d => recon base d 0) := by
  rintro ⟨D,hD⟩
  let d := 14*D+15
  have hd : D≤d := by dsimp [d]; omega
  have hs : spaceAt d=15 := by unfold spaceAt; dsimp [d]; split <;> omega
  have hbase : recon base d 0=false := by
    rw [←model_eq_recon]
    unfold model
    rw [hs]
    decide
  have hpure : recon pure d 0=true := by
    have he : recon base d (0+8)=recon pure d 0 := by
      rw [recon_shift,base_shift_eight]
    rw [←he,←model_eq_recon]
    unfold model
    rw [hs]
    decide
  have h := hD d hd
  change recon pure d 0=recon base d 0 at h
  rw [hpure,hbase] at h
  exact Bool.noConfusion h

/-- An otherwise alternating free input with one `111` run delayed by 4j
free symbols. All family members have the same eventual alternating tail. -/
def input (j t : Nat) : Bool := if t=8*j+5 then true else pure t

theorem input_self_shift (j : Nat) : (fun t => input j (t+8*j))=base := by
  funext t
  have hm : (t+8*j)%4=t%4 := by omega
  have he : t+8*j=8*j+5 ↔ t=5 := by omega
  simp [input,base_formula,pure,hm,he]

theorem input_earlier_shift (j k : Nat) (hjk : j<k) :
    (fun t => input j (t+8*k))=pure := by
  funext t
  have he : t+8*k≠8*j+5 := by omega
  have hm : (t+8*k)%4=t%4 := by omega
  simp [input,he,pure,hm]

theorem pairwise_tail_distinct (j k : Nat) (hjk : j<k) :
    ¬TailEq (fun d => recon (input j) d 0) (fun d => recon (input k) d 0) := by
  intro h
  have ht := tail_recon_time h (8*k)
  have he (a : Nat → Bool) : (fun d => recon a d (8*k))=
      (fun d => recon (fun s => a (s+8*k)) d 0) := by
    funext d
    simpa only [Nat.zero_add] using recon_shift a (8*k) d 0
  rw [he,he,input_self_shift,input_earlier_shift j k hjk] at ht
  exact pure_not_tail_base ht

/-- No fixed spatial period, however large, covers every delayed-defect
reconstruction even after allowing a different transient for every input. -/
theorem no_common_spatial_period (P : Nat) (hP : 0<P) :
    ¬∀ j, SpatialPeriod P (fun d => recon (input j) d 0) :=
  no_common_period_of_distinct _ pairwise_tail_distinct P hP


open Ruliology.CellularAutomata
open Rule30ZeroBoundary

def commonMul : Nat → Nat
  | 0 => 1
  | n+1 => (n+1)*commonMul n

theorem commonMul_pos (n : Nat) : 0<commonMul n := by
  induction n with
  | zero => decide
  | succ n ih => exact Nat.mul_pos (by omega) ih

theorem dvd_commonMul (p n : Nat) (hp : 0<p) (hn : p≤n) : p∣commonMul n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : p=n+1
    · exact ⟨commonMul n,by simp [commonMul,he]⟩
    · obtain ⟨q,hq⟩ := ih (by omega)
      refine ⟨(n+1)*q,?_⟩
      simp [commonMul,hq,Nat.mul_left_comm]

theorem spatial_period_multiple {f : Nat → Bool} {P Q : Nat}
    (h : SpatialPeriod P f) (hq : P∣Q) : SpatialPeriod Q f := by
  obtain ⟨D,hD⟩ := h
  obtain ⟨q,rfl⟩ := hq
  exact ⟨D,fun d hd => by simpa [Nat.mul_comm] using Rule30Jen.periodic_mul hD q d hd⟩

theorem input_tail (j t : Nat) (ht : 8*j+8≤t) : input j t=pure t := by
  simp [input,show t≠8*j+5 by omega]

theorem input_time_period (j t : Nat) (ht : 8*j+8≤t) : input j (t+4)=input j t := by
  rw [input_tail j (t+4) (by omega),input_tail j t ht]
  have hm : (t+4)%4=t%4 := by omega
  simp [Ruliology.CellularAutomata.Rule30DelayedDefectPeriods.pure,hm]

theorem family_spatial_periodic (j : Nat) :
    Rule30Jen.EventuallyPeriodic (fun d => recon (input j) d 0) :=
  spatial_of_temporal _ (8*j+8) 4 (by decide) (input_time_period j)

theorem no_uniform_period_bound (M : Nat) :
    ¬∀ j, ∃ P, 0<P ∧ P≤M ∧ SpatialPeriod P (fun d => recon (input j) d 0) := by
  intro h
  apply no_common_spatial_period (commonMul M) (commonMul_pos M)
  intro j
  obtain ⟨P,hP,hM,hper⟩ := h j
  exact spatial_period_multiple hper (dvd_commonMul P M hP hM)

/-- Every delayed-defect row is eventually spatially periodic, but their
least possible eventual periods exceed every uniform finite bound. -/
theorem arbitrarily_large_periods (M : Nat) :
    ∃ j, Rule30Jen.EventuallyPeriodic (fun d => recon (input j) d 0) ∧
      ∀ P, 0<P → P≤M → ¬SpatialPeriod P (fun d => recon (input j) d 0) := by
  classical
  have hex : ∃ j, ¬∃ P, 0<P ∧ P≤M ∧ SpatialPeriod P (fun d => recon (input j) d 0) := by
    apply Classical.byContradiction
    intro h
    apply no_uniform_period_bound M
    intro j
    apply Classical.byContradiction
    intro hp
    exact h ⟨j,hp⟩
  obtain ⟨j,hj⟩ := hex
  exact ⟨j,family_spatial_periodic j,fun P hp hM hper => hj ⟨P,hp,hM,hper⟩⟩

def free (j s : Nat) : Bool := input j (2*s+1)

theorem input_even (j s : Nat) : input j (2*s)=true := by
  have he : 2*s≠8*j+5 := by omega
  have hm : (2*s)%4≠1 := by omega
  simp [input,he,Ruliology.CellularAutomata.Rule30DelayedDefectPeriods.pure,hm]

theorem free_formula (j s : Nat) :
    free j s=if s=4*j+2 then true else decide (s%2=1) := by
  have he : 2*s+1=8*j+5 ↔ s=4*j+2 := by omega
  have hm : (2*s+1)%4≠1 ↔ s%2=1 := by omega
  simp only [free,input,Ruliology.CellularAutomata.Rule30DelayedDefectPeriods.pure,he,hm]

theorem free_true_iff (j s : Nat) : free j s=true ↔ s=4*j+2 ∨ s%2=1 := by
  by_cases hs : s=4*j+2 <;> simp [free_formula,hs]

theorem free_false_iff (j s : Nat) : free j s=false ↔ s≠4*j+2 ∧ s%2=0 := by
  by_cases hs : s=4*j+2
  · simp [free_formula,hs]
  · by_cases hm : s%2=1
    · simp [free_formula,hs,hm]
    · have hm0 : s%2=0 := by omega
      simp [free_formula,hs,hm0]

theorem free_no_double_zero (j s : Nat) (h : free j s=false) : free j (s+1)=true := by
  have h0 := (free_false_iff j s).mp h
  exact (free_true_iff j (s+1)).mpr (Or.inr (by omega))

theorem free_no_five_ones (j s : Nat) :
    ¬(free j s=true ∧ free j (s+1)=true ∧ free j (s+2)=true ∧
      free j (s+3)=true ∧ free j (s+4)=true) := by
  rintro ⟨h0,h1,h2,h3,h4⟩
  have h0' := (free_true_iff j s).mp h0
  have h1' := (free_true_iff j (s+1)).mp h1
  have h2' := (free_true_iff j (s+2)).mp h2
  have h3' := (free_true_iff j (s+3)).mp h3
  have h4' := (free_true_iff j (s+4)).mp h4
  omega

theorem free_no_010110 (j s : Nat) :
    ¬(free j s=false ∧ free j (s+1)=true ∧ free j (s+2)=false ∧
      free j (s+3)=true ∧ free j (s+4)=true ∧ free j (s+5)=false) := by
  rintro ⟨h0,h1,h2,h3,h4,h5⟩
  have h0' := (free_false_iff j s).mp h0
  have h5' := (free_false_iff j (s+5)).mp h5
  omega

theorem free_no_1011010 (j s : Nat) :
    ¬(free j s=true ∧ free j (s+1)=false ∧ free j (s+2)=true ∧
      free j (s+3)=true ∧ free j (s+4)=false ∧ free j (s+5)=true ∧ free j (s+6)=false) := by
  rintro ⟨h0,h1,h2,h3,h4,h5,h6⟩
  have h1' := (free_false_iff j (s+1)).mp h1
  have h4' := (free_false_iff j (s+4)).mp h4
  omega


open Ruliology.CellularAutomata
open Rule30ZeroBoundary Rule30StripCertificates

theorem collision_of_periodic_prefix (rows : Nat → Nat → Bool) (P : Nat) (hP : 0<P)
    (hp : ∀ j, j≤2^P → SpatialPeriod P (rows j)) :
    ∃ m n, m<n ∧ n≤2^P ∧ TailEq (rows m) (rows n) := by
  classical
  let threshold (j : Nat) := if hj : j≤2^P then Classical.choose (hp j hj) else 0
  have hthreshold (j : Nat) (hj : j≤2^P) :
      ∀ d, threshold j≤d → rows j (d+P)=rows j d := by
    simpa only [threshold,dite_eq_left hj] using Classical.choose_spec (hp j hj)
  obtain ⟨D,hD⟩ := finite_bound threshold (2^P)
  let window (j : Nat) := seg (fun i => rows j (D+i)) P
  obtain ⟨m,n,hmn,hn,hwin⟩ := Rule30Jen.pigeonhole P window
    (fun j => length_seg P _)
  refine ⟨m,n,hmn,hn,agree_from_window _ _ D P hP ?_ ?_ hwin⟩
  · intro d hd
    apply hthreshold m (by omega) d
    have := hD m (by omega)
    omega
  · intro d hd
    apply hthreshold n hn d
    have := hD n hn
    omega

theorem spatial_period_time {a : Nat → Bool} {P : Nat}
    (h : SpatialPeriod P (fun d => recon a d 0)) (t : Nat) :
    SpatialPeriod P (fun d => recon a d t) := by
  obtain ⟨D,hD⟩ := h
  refine ⟨D+1+t,fun d hd => ?_⟩
  have ht := zrow_translate (L:=lam a) (L':=lam a) (d:=P) (a:=D+1)
    (by omega) (fun k hk => hD k (by omega)) t d hd
  simpa only [zrow_lam] using ht

theorem input_shift_index (i j : Nat) (hij : i≤j) :
    (fun t => input j (t+8*(j-i)))=input i := by
  funext t
  have he : t+8*(j-i)=8*j+5 ↔ t=8*i+5 := by omega
  have hm : (t+8*(j-i))%4=t%4 := by omega
  simp only [input,Ruliology.CellularAutomata.Rule30DelayedDefectPeriods.pure,he,hm]

theorem period_inherited {P i j : Nat} (hij : i≤j)
    (h : SpatialPeriod P (fun d => recon (input j) d 0)) :
    SpatialPeriod P (fun d => recon (input i) d 0) := by
  have ht := spatial_period_time h (8*(j-i))
  have he : (fun d => recon (input j) d (8*(j-i)))=
      (fun d => recon (input i) d 0) := by
    funext d
    simpa only [Nat.zero_add,input_shift_index i j hij] using
      recon_shift (input j) (8*(j-i)) d 0
  simpa only [he] using ht

/-- A row with eventual spatial period P cannot hide a defect delayed by
2^P or more family steps, regardless of its spatial transient. -/
theorem delay_lt_pow_period (j P : Nat) (hP : 0<P)
    (h : SpatialPeriod P (fun d => recon (input j) d 0)) : j<2^P := by
  apply Nat.lt_of_not_ge
  intro hj
  have hp : ∀ i, i≤2^P → SpatialPeriod P (fun d => recon (input i) d 0) := by
    intro i hi
    exact period_inherited (by omega) h
  obtain ⟨m,n,hmn,hn,he⟩ := collision_of_periodic_prefix _ P hP hp
  exact pairwise_tail_distinct m n hmn he

theorem pow_two_mono {p q : Nat} (h : p≤q) : 2^p≤2^q := by
  obtain ⟨r,rfl⟩ : ∃ r, q=p+r := ⟨q-p,by omega⟩
  induction r with
  | zero => exact Nat.le_refl _
  | succ r ih =>
    rw [show p+(r+1)=(p+r)+1 by omega,Nat.pow_succ]
    omega

/-- An explicit witness for every desired lower bound: put the one
white-to-black temporal defect at time 8*2^M+5. -/
theorem explicit_large_periods (M : Nat) :
    Rule30Jen.EventuallyPeriodic (fun d => recon (input (2^M)) d 0) ∧
    ∀ P, 0<P → P≤M → ¬SpatialPeriod P (fun d => recon (input (2^M)) d 0) := by
  refine ⟨family_spatial_periodic _,fun P hP hM hper => ?_⟩
  have hlt := delay_lt_pow_period (2^M) P hP hper
  have hle := pow_two_mono hM
  omega

theorem input_eq_alt (j : Nat) : input j=alt (free j) := by
  funext t
  obtain ⟨s,rfl|rfl⟩ : ∃ s, t=2*s ∨ t=2*s+1 := ⟨t/2,by omega⟩
  · rw [input_even]
    simp [alt]
  · simp [alt,free,show (2*s+1)/2=s by omega]

theorem theta_eq_recon (j : Nat) : Theta (free j)=(fun d => recon (input j) d 0) := by
  funext d
  unfold Theta lam
  rw [←input_eq_alt]

theorem theta_inX (j : Nat) : InX (Theta (free j)) := Theta_inX _

theorem theta_spatial_periodic (j : Nat) : Rule30Jen.EventuallyPeriodic (Theta (free j)) := by
  rw [theta_eq_recon]
  exact family_spatial_periodic j

theorem theta_delay_lt_pow_period (j P : Nat) (hP : 0<P)
    (h : SpatialPeriod P (Theta (free j))) : j<2^P := by
  rw [theta_eq_recon] at h
  exact delay_lt_pow_period j P hP h

theorem theta_explicit_large_periods (M : Nat) :
    Rule30Jen.EventuallyPeriodic (Theta (free (2^M))) ∧
    ∀ P, 0<P → P≤M → ¬SpatialPeriod P (Theta (free (2^M))) := by
  rw [theta_eq_recon]
  exact explicit_large_periods M


end Ruliology.CellularAutomata.Rule30DelayedDefectPeriods
