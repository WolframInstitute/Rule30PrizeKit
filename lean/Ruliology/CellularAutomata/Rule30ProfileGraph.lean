module
public import Ruliology.CellularAutomata.Rule30RightPrefixBound

/-! Finite certificates for periodic right-diagonal profile graphs. A closed
graph is used at arbitrary spatial depth, under an explicit prefix-period bound.
No unbounded-period nonloss theorem is assumed. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30ProfileGraph
open Rule30RightProfiles Rule30RightPrefixClock Rule30RightPrefixBound
set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

def profile (q w t : Nat) : Bool := w.testBit (t%q)
def WordPer (q w p : Nat) : Prop :=
  ∀t:Fin q,w.testBit ((t.val+p)%q)=w.testBit t.val
def WordStep (q a b c : Nat) : Prop :=
  ∀t:Fin q,c.testBit ((t.val+1)%q)=xor (c.testBit t.val) (a.testBit t.val || b.testBit t.val)
instance (q w p : Nat) : Decidable (WordPer q w p) := by unfold WordPer;infer_instance
instance (q a b c : Nat) : Decidable (WordStep q a b c) := by unfold WordStep;infer_instance

theorem profile_period (q w : Nat) : Period (profile q w) q := by
  intro t
  simp [profile]

theorem wordPer_iff (q w p : Nat) (hq : 0<q) :
    WordPer q w p ↔ Period (profile q w) p := by
  constructor
  · intro h t
    have ht := h ⟨t%q,Nat.mod_lt t hq⟩
    simpa only [profile,Nat.add_mod,Nat.mod_mod] using ht
  · intro h t
    have ht := h t.val
    simpa only [profile,Nat.mod_eq_of_lt t.isLt] using ht

theorem wordStep_sound (q a b c : Nat) (hq : 0<q) (h : WordStep q a b c) :
    ∀t,profile q c (t+1)=xor (profile q c t) (profile q a t || profile q b t) := by
  intro t
  have ht := h ⟨t%q,Nat.mod_lt t hq⟩
  simpa only [profile,Nat.add_mod,Nat.mod_mod] using ht

structure Graph where
  q : Nat
  bound : Nat
  maxE : Nat
  a : Nat → Nat
  b : Nat → Nat
  next : Nat → Bool → Nat

def forcing (G : Graph) (i : Nat) (t : Nat) : Bool :=
  profile G.q (G.a i) t || profile G.q (G.b i) t

def NodeOK (G : Graph) (i : Nat) : Prop :=
  (xr (forcing G i) G.q=true ∨
    ∀c:Bool,let j:=G.next i c
      j<G.bound ∧ G.a j=G.b i ∧ profile G.q (G.b j) 0=c ∧
      WordStep G.q (G.a i) (G.b i) (G.b j)) ∧
  ∀e:Fin (G.maxE+1),WordPer G.q (G.b i) (2^e.val) → WordPer G.q (G.a i) (2^e.val)

instance (G : Graph) (i : Nat) : Decidable (NodeOK G i) := by
  unfold NodeOK
  infer_instance

def checkAll (G : Graph) : Nat → Bool
  | 0 => true
  | n+1 => checkAll G n && decide (NodeOK G n)

theorem checkAll_sound (G : Graph) : ∀n,checkAll G n=true → ∀i,i<n → NodeOK G i := by
  intro n
  induction n with
  | zero => intro _ i hi;omega
  | succ n ih =>
    intro h i hi
    have pair := Bool.and_eq_true_iff.mp h
    by_cases old : i<n
    · exact ih pair.1 i old
    · have eqi : i=n := by omega
      subst i
      exact of_decide_eq_true pair.2

def checkRange (G : Graph) (start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => checkRange G start n && decide (NodeOK G (start+n))

theorem checkRange_sound (G : Graph) (start : Nat) :
    ∀n,checkRange G start n=true → ∀i,start≤i → i<start+n → NodeOK G i := by
  intro n
  induction n with
  | zero => intro _ i hi htop;omega
  | succ n ih =>
    intro h i hi htop
    have pair := Bool.and_eq_true_iff.mp h
    by_cases old : i<start+n
    · exact ih pair.1 i hi old
    · have eqi : i=start+n := by omega
      subst i
      exact of_decide_eq_true pair.2

theorem next_sound (G : Graph) (hq : 0<G.q)
    (valid : ∀i,i<G.bound → NodeOK G i)
    (i : Nat) (hi : i<G.bound) (a b c : Nat → Bool)
    (ha : ∀t,a t=profile G.q (G.a i) t)
    (hb : ∀t,b t=profile G.q (G.b i) t)
    (hc : Period c G.q)
    (step : ∀t,c (t+1)=xor (c t) (a t || b t)) :
    ∃j,j<G.bound ∧ (∀t,b t=profile G.q (G.a j) t) ∧
      ∀t,c t=profile G.q (G.b j) t := by
  have equation : ∀t,c (t+1)=xor (c t) (forcing G i t) := by
    intro t
    rw [step,ha,hb]
    rfl
  have fp : ∀t,forcing G i (t+G.q)=forcing G i t := by
    intro t
    simp only [forcing,profile_period G.q (G.a i) t,profile_period G.q (G.b i) t]
  rcases (valid i hi).1 with bad | good
  · have shift := running_shift equation fp 0
    have ret := hc 0
    rw [Nat.zero_add] at ret shift
    rw [ret,bad] at shift
    cases h : c 0 <;> simp only [h] at shift <;> contradiction
  · let j := G.next i (c 0)
    have node := good (c 0)
    refine ⟨j,node.1,?_,?_⟩
    · intro t
      rw [hb,node.2.1]
    · intro t
      induction t with
      | zero => exact node.2.2.1.symm
      | succ t ih =>
        rw [step,wordStep_sound G.q (G.a i) (G.b i) (G.b j) hq node.2.2.2 t,ih,ha,hb]

theorem reachable_pair (G : Graph) (hq : 0<G.q) (hb : 0<G.bound)
    (rootA : G.a 0=0) (rootB : G.b 0=0)
    (valid : ∀i,i<G.bound → NodeOK G i)
    (P : Nat → Nat → Bool)
    (zero0 : ∀t,P 0 t=false) (zero1 : ∀t,P 1 t=false)
    (step : ∀j t,P (j+2) (t+1)=xor (P (j+2) t) (P (j+1) t || P j t))
    (n : Nat) (per : ∀j,j≤n+1 → Period (P j) G.q) :
    ∃i,i<G.bound ∧ (∀t,P n t=profile G.q (G.a i) t) ∧
      ∀t,P (n+1) t=profile G.q (G.b i) t := by
  induction n with
  | zero =>
    refine ⟨0,hb,?_,?_⟩
    · intro t;rw [rootA,zero0];simp [profile]
    · intro t;rw [rootB,zero1];simp [profile]
  | succ n ih =>
    obtain ⟨i,hi,ha,hb⟩ := ih (fun j hj => per j (by omega))
    have next := next_sound G hq valid i hi (P n) (P (n+1)) (P (n+2)) ha hb
      (per (n+2) (by omega)) (by intro t;simpa only [Bool.or_comm] using step n t)
    simpa only [Nat.succ_eq_add_one,show n+1+1=n+2 by omega] using next

theorem reachable_period_inherits (G : Graph) (hq : 0<G.q)
    (valid : ∀i,i<G.bound → NodeOK G i)
    (i : Nat) (hi : i<G.bound) (a b : Nat → Bool)
    (ha : ∀t,a t=profile G.q (G.a i) t)
    (hb : ∀t,b t=profile G.q (G.b i) t)
    (e : Nat) (he : e≤G.maxE) (per : Period b (2^e)) : Period a (2^e) := by
  have wp : WordPer G.q (G.b i) (2^e) := by
    apply (wordPer_iff _ _ _ hq).2
    intro t
    rw [← hb,← hb]
    exact per t
  have inherited := (valid i hi).2 ⟨e,by omega⟩ wp
  have ap := (wordPer_iff _ _ _ hq).1 inherited
  intro t
  rw [ha,ha]
  exact ap t

/-- The graph invariant applies to every actual right-bounded seed, at any
spatial depth whose whole-prefix period is q. No bound on seed width occurs. -/
theorem actual_period_inherits (G : Graph) (hq : 0<G.q) (hbound : 0<G.bound)
    (rootA : G.a 0=0) (rootB : G.b 0=0)
    (valid : ∀i,i<G.bound → NodeOK G i)
    (x : Int → Bool) (R : Int) (hx : ∀p,R<p → x p=false)
    (n e : Nat) (he : e≤G.maxE)
    (hpref : PrefixPer (rightDiag x) (-R+(n:Int)) G.q)
    (lastPer : Period (rightDiag x (-R+(n:Int))) (2^e)) :
    Period (rightDiag x (-R+(n:Int)-1)) (2^e) := by
  let P : Nat → Nat → Bool := fun j => rightDiag x (-R-2+(j:Int))
  have zero0 : ∀t,P 0 t=false := by
    intro t
    exact right_white x R hx t _ (by omega)
  have zero1 : ∀t,P 1 t=false := by
    intro t
    exact right_white x R hx t _ (by omega)
  have step : ∀j t,P (j+2) (t+1)=xor (P (j+2) t) (P (j+1) t || P j t) := by
    intro j t
    have h := rightDiag_step x (-R-2+((j+2:Nat):Int)) t
    simpa only [P,show -R-2+((j+2:Nat):Int)-1= -R-2+((j+1:Nat):Int) by omega,
      show -R-2+((j+2:Nat):Int)-2= -R-2+(j:Int) by omega] using h
  have allPer : ∀j,j≤n+1+1 → Period (P j) G.q := by
    intro j hj
    exact hpref _ (by omega)
  obtain ⟨i,hi,ha,hb⟩ := reachable_pair G hq hbound rootA rootB valid P zero0 zero1 step (n+1) allPer
  have index1 : -R-2+((n+1:Nat):Int)= -R+(n:Int)-1 := by omega
  have index2 : -R-2+((n+1+1:Nat):Int)= -R+(n:Int) := by omega
  have lastP : Period (P (n+1+1)) (2^e) := by
    simpa only [P,index2] using lastPer
  have previous := reachable_period_inherits G hq valid i hi (P (n+1)) (P (n+1+1)) ha hb e he lastP
  simpa only [P,index1] using previous

theorem period_pow_mono {f : Nat → Bool} {a b : Nat}
    (h : Period f (2^a)) (hab : a≤b) : Period f (2^b) := by
  have hp : PrefixPer (fun _ : Int => f) 0 (2^a) := fun _ _ => h
  exact prefix_pow_mono hp hab 0 (by omega)

/-- Under a checked graph, the last profile detects every smaller dyadic
period of the entire prefix, uniformly in the spatial depth. -/
theorem actual_prefix_from_last (G : Graph) (hq : 0<G.q) (hbound : 0<G.bound)
    (rootA : G.a 0=0) (rootB : G.b 0=0)
    (valid : ∀i,i<G.bound → NodeOK G i)
    (x : Int → Bool) (R : Int) (hx : ∀p,R<p → x p=false)
    (n e : Nat) (he : e≤G.maxE)
    (hpref : PrefixPer (rightDiag x) (-R+(n:Int)) G.q)
    (lastPer : Period (rightDiag x (-R+(n:Int))) (2^e)) :
    PrefixPer (rightDiag x) (-R+(n:Int)) (2^e) := by
  induction n with
  | zero =>
    have hp := right_boundary_prefix_one x R hx
    have lift := prefix_pow_mono (a:=0) (b:=e) (by simpa only [Nat.pow_zero] using hp) (by omega)
    simpa only [Int.ofNat_zero,Int.add_zero] using lift
  | succ n ih =>
    have index : -R+((n+1:Nat):Int)=(-R+(n:Int))+1 := by omega
    have oldprefix : PrefixPer (rightDiag x) (-R+(n:Int)) G.q := prefix_mono hpref (by omega)
    have oldlast := actual_period_inherits G hq hbound rootA rootB valid x R hx (n+1) e he hpref lastPer
    have previous : Period (rightDiag x (-R+(n:Int))) (2^e) := by
      simpa only [index,show (-R+(n:Int))+1-1= -R+(n:Int) by omega] using oldlast
    have old := ih oldprefix previous
    rw [index] at lastPer ⊢
    exact prefix_extend old lastPer

/-- If the whole-prefix exponent is at most the graph's checked maximum, the
last profile has that exact exponent too. Larger clocks remain outside scope. -/
theorem actual_last_minimal (G : Graph) (hpow : G.q=2^G.maxE)
    (hbound : 0<G.bound) (rootA : G.a 0=0) (rootB : G.b 0=0)
    (valid : ∀i,i<G.bound → NodeOK G i)
    (x : Int → Bool) (R : Int) (hx : ∀p,R<p → x p=false)
    (n E : Nat) (hE : E≤G.maxE)
    (clock : PrefixIsE (rightDiag x) (-R+(n:Int)) E) :
    ∀e,e<E → ¬Period (rightDiag x (-R+(n:Int))) (2^e) := by
  intro e he lastPer
  have hpref : PrefixPer (rightDiag x) (-R+(n:Int)) G.q := by
    rw [hpow]
    exact prefix_pow_mono clock.1 hE
  have hp := actual_prefix_from_last G (by rw [hpow];exact Nat.two_pow_pos _) hbound rootA rootB valid x R hx n e (by omega) hpref lastPer
  exact clock.2 e he hp

/-- A following profile cannot drop below a prefix clock within the checked
range, even if that following profile would otherwise enlarge the prefix. -/
theorem actual_no_small_clock_drop (G : Graph) (hpow : G.q=2^G.maxE)
    (hbound : 0<G.bound) (rootA : G.a 0=0) (rootB : G.b 0=0)
    (valid : ∀i,i<G.bound → NodeOK G i)
    (x : Int → Bool) (R : Int) (hx : ∀p,R<p → x p=false)
    (n E : Nat) (hE : E≤G.maxE)
    (clock : PrefixIsE (rightDiag x) (-R+(n:Int)) E) :
    ∀e,e<E → ¬Period (rightDiag x (-R+((n+1:Nat):Int))) (2^e) := by
  intro e he nextPer
  have oldQ : PrefixPer (rightDiag x) (-R+(n:Int)) G.q := by
    rw [hpow]
    exact prefix_pow_mono clock.1 hE
  have nextQ : Period (rightDiag x (-R+((n+1:Nat):Int))) G.q := by
    rw [hpow]
    exact period_pow_mono nextPer (by omega)
  have index : -R+((n+1:Nat):Int)=(-R+(n:Int))+1 := by omega
  have prefixQ : PrefixPer (rightDiag x) (-R+((n+1:Nat):Int)) G.q := by
    rw [index] at nextQ ⊢
    exact prefix_extend oldQ nextQ
  have previous := actual_period_inherits G (by rw [hpow];exact Nat.two_pow_pos _) hbound rootA rootB valid x R hx (n+1) e (by omega) prefixQ nextPer
  have oldPer : Period (rightDiag x (-R+(n:Int))) (2^e) := by
    simpa only [index,show (-R+(n:Int))+1-1= -R+(n:Int) by omega] using previous
  exact actual_last_minimal G hpow hbound rootA rootB valid x R hx n E hE clock e he oldPer

end Ruliology.CellularAutomata.Rule30ProfileGraph
