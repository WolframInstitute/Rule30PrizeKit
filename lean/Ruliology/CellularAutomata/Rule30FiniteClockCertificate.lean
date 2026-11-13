module

public import Ruliology.CellularAutomata.Rule30ControlledResponse

/-!
# Finite temporal-profile certificates for arbitrary finite spatial widths

A checked pool of temporal profile pairs is closed under adjoining a column
on the left. Starting from the finite zero tail therefore covers every finite
width at the specified full clock. A separately checked property can propagate
a shorter head clock to every spatial column. The clock size is explicit;
this module does not establish an arbitrary-clock induction or a prize result.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30FiniteClockCertificate

open Rule30ControlledResponse

structure Node where
  b : Nat
  c : Nat
  a0 : Nat
  a1 : Nat
deriving DecidableEq, Repr

def pat (P a t : Nat) : Bool := a.testBit (t%P)

def accum (u : Nat → Bool) : Nat → Bool
  | 0 => false
  | t+1 => xor (accum u t) (u t)

def forcing (P b c t : Nat) : Bool := pat P b t || pat P c t

def pairMem (pool : List Node) (b c : Nat) : Bool :=
  pool.any fun e => decide (e.b=b ∧ e.c=c)

theorem pairMem_iff (pool : List Node) (b c : Nat) :
    pairMem pool b c=true ↔ ∃ e, e∈pool ∧ e.b=b ∧ e.c=c := by
  simp [pairMem,List.any_eq_true]

def nodeCheck (P : Nat) (pool : List Node) (e : Node) : Bool :=
  ((List.range P).all fun t => decide (pat P e.a0 t=accum (forcing P e.b e.c) t)) &&
  ((List.range P).all fun t => decide (pat P e.a1 t= !accum (forcing P e.b e.c) t)) &&
  (if accum (forcing P e.b e.c) P then true
   else pairMem pool e.a0 e.b && pairMem pool e.a1 e.b)

def poolCheck (P : Nat) (pool : List Node) : Bool :=
  pairMem pool 0 0 && pool.all (nodeCheck P pool)

def Covered (P : Nat) (pool : List Node) (f g : Nat → Bool) : Prop :=
  ∃ e, e∈pool ∧ (∀ t, f t=pat P e.b t) ∧ (∀ t, g t=pat P e.c t)

theorem periodic_mod {P : Nat} {f : Nat → Bool}
    (h : ∀ t, f (t+P)=f t) : ∀ t, f t=f (t%P) := by
  intro t
  have key : ∀ n r, f (r+P*n)=f r := by
    intro n
    induction n with
    | zero => intro r; simp
    | succ n ih =>
        intro r
        rw [show r+P*(n+1)=(r+P*n)+P by rw [Nat.mul_add,Nat.mul_one,Nat.add_assoc],h,ih]
  simpa only [Nat.mod_add_div] using key (t/P) (t%P)

theorem periodic_add_mul {P : Nat} {f : Nat → Bool}
    (h : ∀ t, f (t+P)=f t) : ∀ n t, f (t+P*n)=f t := by
  intro n
  induction n with
  | zero => intro t; simp
  | succ n ih =>
      intro t
      rw [show t+P*(n+1)=(t+P*n)+P by rw [Nat.mul_add,Nat.mul_one,Nat.add_assoc],h,ih]

/-- On a purely periodic sequence an eventual period already holds from time zero. -/
theorem eventual_period_is_period (P H T : Nat) (hP : 0<P) (f : Nat → Bool)
    (hp : ∀ t, f (t+P)=f t) (he : ∀ t, T≤t → f (t+H)=f t) :
    ∀ t, f (t+H)=f t := by
  have bound : ∀ n, n≤P*n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.mul_succ]; omega
  intro t
  have h := he (t+P*T) (by have := bound T; omega)
  rw [show t+P*T+H=(t+H)+P*T by omega,periodic_add_mul hp,periodic_add_mul hp] at h
  exact h

theorem accum_solution (f u : Nat → Bool)
    (hf : ∀ t, f (t+1)=xor (f t) (u t)) :
    ∀ t, f t=xor (f 0) (accum u t) := by
  intro t
  induction t with
  | zero => simp [accum]
  | succ t ih =>
      rw [hf,accum,ih]
      cases f 0 <;> cases accum u t <;> cases u t <;> rfl

theorem accum_return_false (P : Nat) (f u : Nat → Bool)
    (hf : ∀ t, f (t+1)=xor (f t) (u t)) (hp : f P=f 0) :
    accum u P=false := by
  have h := accum_solution f u hf P
  rw [hp] at h
  cases ha : f 0 <;> cases hb : accum u P <;> simp [ha,hb] at h ⊢

theorem pat_mod (P a t : Nat) : pat P a (t%P)=pat P a t := by
  simp [pat]

theorem covered_zero (P : Nat) (pool : List Node) (h : pairMem pool 0 0=true) :
    Covered P pool (fun _ => false) (fun _ => false) := by
  obtain ⟨e,he,hb,hc⟩ := (pairMem_iff pool 0 0).mp h
  refine ⟨e,he,?_,?_⟩ <;> intro t
  · rw [hb]; simp [pat]
  · rw [hc]; simp [pat]

theorem covered_predecessor (P : Nat) (hP : 0<P) (pool : List Node)
    (hcheck : poolCheck P pool=true) (f g h : Nat → Bool)
    (hf : ∀ t, f (t+1)=xor (f t) (g t || h t))
    (hp : ∀ t, f (t+P)=f t) (hcover : Covered P pool g h) :
    Covered P pool f g := by
  obtain ⟨e,he,hg,hh⟩ := hcover
  have hchecks : pairMem pool 0 0=true ∧ pool.all (nodeCheck P pool)=true := by
    simpa only [poolCheck,Bool.and_eq_true] using hcheck
  have hall := hchecks.2
  have hc := List.all_eq_true.mp hall e he
  simp only [nodeCheck,Bool.and_eq_true] at hc
  have hforce : ∀ t, f (t+1)=xor (f t) (forcing P e.b e.c t) := by
    intro t
    rw [hf,hg,hh]
    rfl
  have hret : accum (forcing P e.b e.c) P=false :=
    accum_return_false P f _ hforce (by simpa using hp 0)
  have hclosed : pairMem pool e.a0 e.b=true ∧ pairMem pool e.a1 e.b=true := by
    simpa only [hret,Bool.false_eq_true,ite_false,Bool.and_eq_true] using hc.2
  have hsol := accum_solution f _ hforce
  cases hf0 : f 0 with
  | false =>
      obtain ⟨a,ha,ha0,hab⟩ := (pairMem_iff pool e.a0 e.b).mp hclosed.1
      refine ⟨a,ha,?_,?_⟩
      · intro t
        rw [ha0,periodic_mod hp t,hsol,hf0]
        have ht := List.all_eq_true.mp hc.1.1 (t%P) (List.mem_range.mpr (Nat.mod_lt _ hP))
        have heq := of_decide_eq_true ht
        simpa only [Bool.false_xor,pat_mod] using heq.symm
      · intro t; rw [hab,hg]
  | true =>
      obtain ⟨a,ha,ha1,hab⟩ := (pairMem_iff pool e.a1 e.b).mp hclosed.2
      refine ⟨a,ha,?_,?_⟩
      · intro t
        rw [ha1,periodic_mod hp t,hsol,hf0]
        have ht := List.all_eq_true.mp hc.1.2 (t%P) (List.mem_range.mpr (Nat.mod_lt _ hP))
        have heq := of_decide_eq_true ht
        simpa only [Bool.true_xor,pat_mod] using heq.symm
      · intro t; rw [hab,hg]

/-- Pool closure covers every spatial width; no width bound is part of the certificate. -/
theorem covers_finite_family (P : Nat) (hP : 0<P) (pool : List Node)
    (hcheck : poolCheck P pool=true) (x : Nat → Nat → Bool) (W : Nat)
    (hstep : ∀ k t, x k (t+1)=xor (x k t) (x (k+1) t || x (k+2) t))
    (hper : ∀ k t, x k (t+P)=x k t)
    (hzero : ∀ k, W≤k → ∀ t, x k t=false) :
    ∀ k, Covered P pool (x k) (x (k+1)) := by
  have descend : ∀ n k, W≤k+n → Covered P pool (x k) (x (k+1)) := by
    intro n
    induction n with
    | zero =>
        intro k hk
        have h0 : x k=(fun _ => false) := funext (hzero k (by omega))
        have h1 : x (k+1)=(fun _ => false) := funext (hzero (k+1) (by omega))
        rw [h0,h1]
        have hchecks : pairMem pool 0 0=true ∧ pool.all (nodeCheck P pool)=true := by
          simpa only [poolCheck,Bool.and_eq_true] using hcheck
        exact covered_zero P pool hchecks.1
    | succ n ih =>
        intro k hk
        apply covered_predecessor P hP pool hcheck (x k) (x (k+1)) (x (k+2))
          (hstep k) (hper k)
        simpa only [Nat.add_assoc] using ih (k+1) (by omega)
  intro k
  exact descend W k (by omega)

def periodCheck (P H a : Nat) : Bool :=
  (List.range P).all fun t => decide (pat P a (t+H)=pat P a t)

theorem periodCheck_iff (P H a : Nat) (hP : 0<P) :
    periodCheck P H a=true ↔ ∀ t, pat P a (t+H)=pat P a t := by
  constructor
  · intro h t
    have hh := List.all_eq_true.mp h (t%P) (List.mem_range.mpr (Nat.mod_lt _ hP))
    have heq := of_decide_eq_true hh
    simpa only [pat,Nat.add_mod,Nat.mod_mod] using heq
  · intro h
    apply List.all_eq_true.mpr
    intro t ht
    exact decide_eq_true (h t)

def detectionCheck (P H : Nat) (pool : List Node) : Bool :=
  pool.all fun e => if periodCheck P H e.b then periodCheck P H e.c else true

theorem periodCheck_mod_clock (P H a : Nat) :
    periodCheck P (H%P) a=periodCheck P H a := by
  simp [periodCheck,pat,Nat.add_mod]

theorem detectionCheck_mod_clock (P H : Nat) (pool : List Node) :
    detectionCheck P (H%P) pool=detectionCheck P H pool := by
  simp only [detectionCheck,periodCheck_mod_clock]

theorem covered_period_propagates (P H : Nat) (hP : 0<P) (pool : List Node)
    (hdetect : detectionCheck P H pool=true) {f g : Nat → Bool}
    (hcover : Covered P pool f g) (hf : ∀ t, f (t+H)=f t) :
    ∀ t, g (t+H)=g t := by
  obtain ⟨e,he,hfcode,hgcode⟩ := hcover
  have hb : periodCheck P H e.b=true := (periodCheck_iff P H e.b hP).mpr (by
    intro t
    rw [← hfcode,← hfcode,hf])
  have hc := List.all_eq_true.mp hdetect e he
  simp only [hb,ite_true] at hc
  have hcp := (periodCheck_iff P H e.c hP).mp hc
  intro t
  rw [hgcode,hgcode,hcp]

/-- A successful detection check turns one head clock into a clock for every column. -/
theorem finite_family_clock_detected (P H : Nat) (hP : 0<P) (pool : List Node)
    (hcheck : poolCheck P pool=true) (hdetect : detectionCheck P H pool=true)
    (x : Nat → Nat → Bool) (W : Nat)
    (hstep : ∀ k t, x k (t+1)=xor (x k t) (x (k+1) t || x (k+2) t))
    (hper : ∀ k t, x k (t+P)=x k t)
    (hzero : ∀ k, W≤k → ∀ t, x k t=false)
    (hhead : ∀ t, x 0 (t+H)=x 0 t) : ∀ k t, x k (t+H)=x k t := by
  have covered := covers_finite_family P hP pool hcheck x W hstep hper hzero
  intro k
  induction k with
  | zero => exact hhead
  | succ k ih => exact covered_period_propagates P H hP pool hdetect (covered k) ih

theorem iterate_restart (x : State) (a : Nat) :
    ∀ b, iterate (iterate x a) b=iterate x (a+b)
  | 0 => rfl
  | b+1 => by rw [iterate,iterate_restart x a b]; rfl

theorem iterate_period_of_return (x : State) (P : Nat) (hp : iterate x P=x) :
    ∀ t, iterate x (t+P)=iterate x t := by
  intro t
  rw [Nat.add_comm t P,← iterate_restart,hp]

theorem iterate_zero_tail (x : State) (W : Nat) (hx : ∀ k, W≤k → x k=false) :
    ∀ t k, W≤k → iterate x t k=false := by
  intro t
  induction t with
  | zero => exact hx
  | succ t ih =>
      intro k hk
      change xor (iterate x t k) (iterate x t (k+1) || iterate x t (k+2))=false
      rw [ih k hk,ih (k+1) (by omega),ih (k+2) (by omega)]
      rfl

/-- Specialization to the actual triangular map, with finite support and full clock explicit. -/
theorem finite_state_clock_detected (P H : Nat) (hP : 0<P) (pool : List Node)
    (hcheck : poolCheck P pool=true) (hdetect : detectionCheck P H pool=true)
    (x : State) (W : Nat) (hx : ∀ k, W≤k → x k=false)
    (hfull : iterate x P=x)
    (hhead : ∀ t, iterate x (t+H) 0=iterate x t 0) : iterate x H=x := by
  have hper := iterate_period_of_return x P hfull
  have hfin := iterate_zero_tail x W hx
  have hall := finite_family_clock_detected P H hP pool hcheck hdetect
    (fun k t => iterate x t k) W (fun _ _ => rfl)
    (fun k t => congrFun (hper t) k) (fun k hk t => hfin t k hk) hhead
  funext k
  simpa only [Nat.zero_add,iterate] using hall k 0

theorem finite_state_eventual_clock_detected (P H : Nat) (hP : 0<P) (pool : List Node)
    (hcheck : poolCheck P pool=true) (hdetect : detectionCheck P H pool=true)
    (x : State) (W T : Nat) (hx : ∀ k, W≤k → x k=false)
    (hfull : iterate x P=x)
    (hhead : ∀ t, T≤t → iterate x (t+H) 0=iterate x t 0) : iterate x H=x := by
  apply finite_state_clock_detected P H hP pool hcheck hdetect x W hx hfull
  exact eventual_period_is_period P H T hP (fun t => iterate x t 0)
    (fun t => congrFun (iterate_period_of_return x P hfull t) 0) hhead

/-! ## Multi-period shift invariance of `pat` and XOR-linearity of `accum` -/

/-- **Multi-Period Shift Invariance of `pat P a` and XOR-Linearity of `accum` (`pat_periodic_mul_and_accum_xor`).** -/
theorem pat_periodic_mul_and_accum_xor (P a t m : Nat) (u v : Nat → Bool) :
    pat P a (t + m * P) = pat P a t ∧
    accum (fun _ => false) t = false ∧
    accum (fun s => xor (u s) (v s)) t = xor (accum u t) (accum v t) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold pat
    rw [Nat.add_mul_mod_self_right]
  · induction t with
    | zero => rfl
    | succ t ih => simp [accum, ih]
  · induction t with
    | zero => rfl
    | succ t ih =>
      simp only [accum, ih]
      cases accum u t <;> cases accum v t <;> cases u t <;> cases v t <;> rfl

end Ruliology.CellularAutomata.Rule30FiniteClockCertificate
