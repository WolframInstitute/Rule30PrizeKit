module
public import Ruliology.CellularAutomata.Rule30ResetFreeRuns

/-! Translating the five-row finite-state certificate to ordinary Rule30 strips. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30ResetFreeStrip
open Rule30ResetFreeCore Rule30ResetFreeRuns
set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

theorem five_cases : ∀ i : Fin 5,i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by decide +kernel
theorem fin0 : (0:Fin 5).val=0 := by decide +kernel
theorem fin1 : (1:Fin 5).val=1 := by decide +kernel
theorem fin2 : (2:Fin 5).val=2 := by decide +kernel
theorem fin3 : (3:Fin 5).val=3 := by decide +kernel
theorem fin4 : (4:Fin 5).val=4 := by decide +kernel

def pack (d0 d1 d2 d3 d4 : Nat) : Nat := d0+6*d1+36*d2+216*d3+1296*d4
def packFive (d : Fin 5 → Nat) : Nat := pack (d 0) (d 1) (d 2) (d 3) (d 4)

theorem packFive_lt (d : Fin 5 → Nat) (bounds : ∀ i,d i<6) : packFive d<7776 := by
  have h0 := bounds 0
  have h1 := bounds 1
  have h2 := bounds 2
  have h3 := bounds 3
  have h4 := bounds 4
  unfold packFive pack
  omega

theorem packFive_digit (d : Fin 5 → Nat) (bounds : ∀ i,d i<6) (i : Fin 5) :
    digit (packFive d) i.val=d i := by
  have h0 := bounds 0
  have h1 := bounds 1
  have h2 := bounds 2
  have h3 := bounds 3
  have h4 := bounds 4
  rcases five_cases i with h | h | h | h | h <;> subst i <;>
    simp only [packFive,pack,digit,fin0,fin1,fin2,fin3,fin4,Nat.pow_zero,Nat.pow_succ] <;> omega

theorem unpack (s : Nat) (bound : s<7776) : packFive (fun i => digit s i.val)=s := by
  simp only [packFive,pack,digit,fin0,fin1,fin2,fin3,fin4,Nat.pow_zero,Nat.pow_succ]
  omega

theorem digits_ext {s u : Nat} (hs : s<7776) (hu : u<7776)
    (eq : ∀ i : Fin 5,digit s i.val=digit u i.val) : s=u := by
  rw [← unpack s hs,← unpack u hu]
  congr 1
  funext i
  exact eq i

def inputBit (s : Nat) (top : Bool) (t : Nat) : Bool :=
  if t=4 then top else xor (currentBit (digit s (t+1)))
    (currentBit (digit s t) || prevBit (digit s t))
def NoReject (s : Nat) (top : Bool) : Prop :=
  ∀ i : Fin 5,¬(inputBit s top i.val=false ∧ runMod (digit s i.val)=1)
theorem nextAux_step (s : Nat) (top : Bool) (t total : Nat) :
    nextAux s top (t+1) total =
      if inputBit s top t=false ∧ runMod (digit s t)=1 then 7776
      else nextAux s top t (total+6^t*nextAtom (digit s t) (inputBit s top t)) := rfl

theorem transition_of_components {s u : Nat} (hu : u<7776) (top : Bool)
    (allowed : NoReject s top) (components : ∀ i : Fin 5,
      digit u i.val=nextAtom (digit s i.val) (inputBit s top i.val)) :
    nextState s top=u := by
  have a0 := allowed (0:Fin 5)
  have a1 := allowed (1:Fin 5)
  have a2 := allowed (2:Fin 5)
  have a3 := allowed (3:Fin 5)
  have a4 := allowed (4:Fin 5)
  have e0 := components (0:Fin 5)
  have e1 := components (1:Fin 5)
  have e2 := components (2:Fin 5)
  have e3 := components (3:Fin 5)
  have e4 := components (4:Fin 5)
  simp only [fin0,fin1,fin2,fin3,fin4] at a0 a1 a2 a3 a4 e0 e1 e2 e3 e4
  unfold nextState
  rw [nextAux_step,ite_eq_right a4,nextAux_step,ite_eq_right a3,nextAux_step,ite_eq_right a2,
    nextAux_step,ite_eq_right a1,nextAux_step,ite_eq_right a0]
  simp only [nextAux]
  rw [← e0,← e1,← e2,← e3,← e4]
  have recover := unpack u hu
  simp only [packFive,pack,fin0,fin1,fin2,fin3,fin4] at recover
  omega

def encodeAtom (p c : Bool) (r : Nat) : Nat :=
  if c then if p then 3+r else 2 else if p then 1 else 0
def AtomOK (p c : Bool) (r : Nat) : Prop :=
  (c=false → r=0) ∧ (p=false → c=true → r=1)

instance (p c : Bool) (r : Nat) : Decidable (AtomOK p c r) := by
  unfold AtomOK
  infer_instance

theorem atom_table : ∀ p c : Bool,∀ r : Fin 3,AtomOK p c r.val →
    prevBit (encodeAtom p c r.val)=p ∧ currentBit (encodeAtom p c r.val)=c ∧
    runMod (encodeAtom p c r.val)=r.val ∧ encodeAtom p c r.val<6 := by decide +kernel

theorem atom_step_table : ∀ p c e : Bool,∀ r u : Fin 3,
    AtomOK p c r.val → AtomOK c e u.val →
    (e=false → r.val≠1) → u.val=(if e then (r.val+1)%3 else 0) →
    nextAtom (encodeAtom p c r.val) e=encodeAtom c e u.val := by decide +kernel

def RowRecurrence (x : Fin 5 → Nat → Bool) : Prop := ∀ t : Fin 4,∀ p,1≤p →
  x ⟨t.val+1,by omega⟩ p = xor (x ⟨t.val,by omega⟩ (p+1))
    (x ⟨t.val,by omega⟩ p || x ⟨t.val,by omega⟩ (p-1))

def atomValue (x : Fin 5 → Nat → Bool) (r : Fin 5 → Nat → Nat) (p : Nat) (t : Fin 5) : Nat :=
  encodeAtom (x t (p-1)) (x t p) (r t p)
def vertex (x : Fin 5 → Nat → Bool) (r : Fin 5 → Nat → Nat) (p : Nat) : Nat :=
  packFive (atomValue x r p)

theorem atom_properties (x : Fin 5 → Nat → Bool) (r : Fin 5 → Nat → Nat) (K : Nat)
    (colors : ∀ t,ColoredFrom (x t) K (r t)) (p : Nat) (hp : K≤p) (t : Fin 5) :
    prevBit (atomValue x r p t)=x t (p-1) ∧ currentBit (atomValue x r p t)=x t p ∧
    runMod (atomValue x r p t)=r t p ∧ atomValue x r p t<6 := by
  have color := colors t p hp
  exact atom_table _ _ ⟨r t p,color.1⟩ ⟨color.2.1,color.2.2.1⟩

theorem vertex_bound (x : Fin 5 → Nat → Bool) (r : Fin 5 → Nat → Nat) (K : Nat)
    (colors : ∀ t,ColoredFrom (x t) K (r t)) (p : Nat) (hp : K≤p) : vertex x r p<7776 :=
  packFive_lt _ (fun t => (atom_properties x r K colors p hp t).2.2.2)

theorem vertex_digit (x : Fin 5 → Nat → Bool) (r : Fin 5 → Nat → Nat) (K : Nat)
    (colors : ∀ t,ColoredFrom (x t) K (r t)) (p : Nat) (hp : K≤p) (t : Fin 5) :
    digit (vertex x r p) t.val=atomValue x r p t :=
  packFive_digit _ (fun i => (atom_properties x r K colors p hp i).2.2.2) t

theorem vertex_current (x : Fin 5 → Nat → Bool) (r : Fin 5 → Nat → Nat) (K : Nat)
    (colors : ∀ t,ColoredFrom (x t) K (r t)) (p : Nat) (hp : K≤p) (t : Fin 5) :
    currentBit (digit (vertex x r p) t.val)=x t p := by
  rw [vertex_digit x r K colors p hp t]
  exact (atom_properties x r K colors p hp t).2.1

theorem vertex_prev (x : Fin 5 → Nat → Bool) (r : Fin 5 → Nat → Nat) (K : Nat)
    (colors : ∀ t,ColoredFrom (x t) K (r t)) (p : Nat) (hp : K≤p) (t : Fin 5) :
    prevBit (digit (vertex x r p) t.val)=x t (p-1) := by
  rw [vertex_digit x r K colors p hp t]
  exact (atom_properties x r K colors p hp t).1

theorem vertex_run (x : Fin 5 → Nat → Bool) (r : Fin 5 → Nat → Nat) (K : Nat)
    (colors : ∀ t,ColoredFrom (x t) K (r t)) (p : Nat) (hp : K≤p) (t : Fin 5) :
    runMod (digit (vertex x r p) t.val)=r t p := by
  rw [vertex_digit x r K colors p hp t]
  exact (atom_properties x r K colors p hp t).2.2.1

theorem xor_solve : ∀ a b c : Bool,a=xor b c → b=xor a c := by decide +kernel

theorem input_eq (x : Fin 5 → Nat → Bool) (r : Fin 5 → Nat → Nat) (K : Nat)
    (hK : 1≤K) (colors : ∀ t,ColoredFrom (x t) K (r t)) (recurrence : RowRecurrence x)
    (p : Nat) (hp : K≤p) (t : Fin 5) :
    inputBit (vertex x r p) (x 4 (p+1)) t.val=x t (p+1) := by
  by_cases last : t.val=4
  · have eq : t=4 := Fin.ext last
    subst t
    simp only [inputBit,fin4,↓reduceIte]
  · have ht : t.val<4 := by omega
    have solved : x t (p+1)=xor (x ⟨t.val+1,by omega⟩ p) (x t p || x t (p-1)) :=
      xor_solve _ _ _ (recurrence ⟨t.val,ht⟩ p (by omega))
    simp only [inputBit,ite_eq_right last]
    rw [vertex_current x r K colors p hp ⟨t.val+1,by omega⟩,
      vertex_current x r K colors p hp t,vertex_prev x r K colors p hp t]
    exact solved.symm

theorem vertex_step (x : Fin 5 → Nat → Bool) (r : Fin 5 → Nat → Nat) (K : Nat)
    (hK : 1≤K) (colors : ∀ t,ColoredFrom (x t) K (r t)) (recurrence : RowRecurrence x)
    (p : Nat) (hp : K≤p) : nextState (vertex x r p) (x 4 (p+1))=vertex x r (p+1) := by
  apply transition_of_components (vertex_bound x r K colors (p+1) (by omega)) (x 4 (p+1))
  · intro t forbidden
    rw [input_eq x r K hK colors recurrence p hp t,vertex_run x r K colors p hp t] at forbidden
    exact (colors t p hp).2.2.2.1 forbidden.1 forbidden.2
  · intro t
    rw [vertex_digit x r K colors (p+1) (by omega) t,
      vertex_digit x r K colors p hp t,input_eq x r K hK colors recurrence p hp t]
    have old := colors t p hp
    have new := colors t (p+1) (by omega)
    rw [show p+1-1=p by omega] at new
    dsimp only [atomValue]
    rw [show p+1-1=p by omega]
    exact (atom_step_table _ _ _ ⟨r t p,old.1⟩ ⟨r t (p+1),new.1⟩
      ⟨old.2.1,old.2.2.1⟩ ⟨new.2.1,new.2.2.1⟩ old.2.2.2.1 old.2.2.2.2).symm

theorem encoded_strip_path (x : Fin 5 → Nat → Bool) (r : Fin 5 → Nat → Nat) (K : Nat)
    (hK : 1≤K) (colors : ∀ t,ColoredFrom (x t) K (r t)) (recurrence : RowRecurrence x) :
    Path graph (fun k => vertex x r (K+k)) (fun k => x 4 (K+k+1)) := by
  intro k
  dsimp only [graph]
  refine ⟨vertex_bound x r K colors (K+k) (by omega),?_⟩
  have h := vertex_step x r K hK colors recurrence (K+k) (by omega)
  simpa only [show K+k+1=K+(k+1) by omega] using h

theorem colored_strip_five (x : Fin 5 → Nat → Bool) (r : Fin 5 → Nat → Nat) (K : Nat)
    (hK : 1≤K) (colors : ∀ t,ColoredFrom (x t) K (r t)) (recurrence : RowRecurrence x) :
    ∀ p,K+7≤p → x 0 (p+5)=x 0 p := by
  have encoded := encoded_strip_path x r K hK colors recurrence
  have period := encoded_path_five_from_seven _ _ encoded
  intro p hp
  let k := p-K
  have eq := period k (by dsimp [k];omega)
  dsimp only [graph] at eq
  have left := vertex_current x r K colors (K+(k+5)) (by omega) 0
  have right := vertex_current x r K colors (K+k) (by omega) 0
  simp only [fin0] at left right
  rw [left,right] at eq
  simpa only [show K+(k+5)=p+5 by dsimp [k];omega,
    show K+k=p by dsimp [k];omega] using eq

/-- Five consecutive reset-free Rule30 rows force an eventually5-periodic
spatial tail. This is a statement about ordinary rows, not assumed encodings. -/
theorem five_reset_free_rows (x : Fin 5 → Nat → Bool) (recurrence : RowRecurrence x)
    (avoid : ∀ t,AvoidReset (x t)) : ∃ M,∀ p,M≤p → x 0 (p+5)=x 0 p := by
  classical
  let witnesses := fun t => exists_coloring (x t) (avoid t)
  let Ks := fun t => Classical.choose (witnesses t)
  let rs := fun t => Classical.choose (Classical.choose_spec (witnesses t)).2
  have positive : ∀ t,1≤Ks t := fun t => (Classical.choose_spec (witnesses t)).1
  have individual : ∀ t,ColoredFrom (x t) (Ks t) (rs t) :=
    fun t => Classical.choose_spec (Classical.choose_spec (witnesses t)).2
  let K := Ks 0+Ks 1+Ks 2+Ks 3+Ks 4
  have bounds : ∀ t,Ks t≤K := by
    intro t
    rcases five_cases t with h | h | h | h | h <;> subst t <;> dsimp only [K] <;> omega
  have colors : ∀ t,ColoredFrom (x t) K (rs t) := by
    intro t p hp
    exact individual t p (by have lower := bounds t;omega)
  refine ⟨K+7,colored_strip_five x rs K (by have a := positive 0;have b := bounds 0;omega) colors recurrence⟩

theorem avoid_shift (f : Nat → Bool) (avoid : AvoidReset f) (K : Nat) :
    AvoidReset (fun p => f (K+p)) := by
  intro i n left right ones
  apply avoid (K+i) n
  · exact left
  · simpa only [Nat.add_assoc] using right
  · intro j hj
    simpa only [Nat.add_assoc] using ones j hj

def EventuallyAvoidReset (f : Nat → Bool) : Prop := ∃ K,AvoidReset (fun p => f (K+p))

/-- The classification also holds when all five rows have arbitrary finite
prefixes before their reset-free spatial tails. -/
theorem five_reset_free_tails (x : Fin 5 → Nat → Bool) (recurrence : RowRecurrence x)
    (avoid : ∀ t,EventuallyAvoidReset (x t)) : ∃ M,∀ p,M≤p → x 0 (p+5)=x 0 p := by
  classical
  let Ks := fun t => Classical.choose (avoid t)
  have individual : ∀ t,AvoidReset (fun p => x t (Ks t+p)) := fun t => Classical.choose_spec (avoid t)
  let K := Ks 0+Ks 1+Ks 2+Ks 3+Ks 4
  have bounds : ∀ t,Ks t≤K := by
    intro t
    rcases five_cases t with h | h | h | h | h <;> subst t <;> dsimp only [K] <;> omega
  let shifted := fun t p => x t (K+p)
  have shiftedAvoid : ∀ t,AvoidReset (shifted t) := by
    intro t
    have h := avoid_shift (fun p => x t (Ks t+p)) (individual t) (K-Ks t)
    have sum : Ks t+(K-Ks t)=K := by have lower := bounds t;omega
    simpa only [← Nat.add_assoc,sum] using h
  have shiftedRecurrence : RowRecurrence shifted := by
    intro t p hp
    have h := recurrence t (K+p) (by omega)
    simpa only [shifted,Nat.add_assoc,show K+p-1=K+(p-1) by omega] using h
  obtain ⟨M,period⟩ := five_reset_free_rows shifted shiftedRecurrence shiftedAvoid
  refine ⟨K+M,?_⟩
  intro p hp
  have h := period (p-K) (by omega)
  simpa only [shifted,show K+(p-K+5)=p+5 by omega,show K+(p-K)=p by omega] using h

/-! ## Shift equivalence for `EventuallyAvoidReset` and multi-period `p + 5 * k` strip periodicity -/

/-- **Shift Equivalence for `EventuallyAvoidReset` and Multi-Period Strip Periodicity (`eventuallyAvoidReset_shift_iff_and_colored_strip_five_mul`).** -/
theorem eventuallyAvoidReset_shift_iff_and_colored_strip_five_mul
    (f : Nat → Bool) (d K p m : Nat) (x : Fin 5 → Nat → Bool) (r : Fin 5 → Nat → Nat) :
    (EventuallyAvoidReset f ↔ EventuallyAvoidReset (fun i => f (d + i))) ∧
    (1 ≤ K → (∀ t, ColoredFrom (x t) K (r t)) → RowRecurrence x → K + 7 ≤ p →
      x 0 (p + 5 * m) = x 0 p) := by
  refine ⟨⟨fun ⟨K0, hK0⟩ => ⟨K0, ?_⟩, fun ⟨K0, hK0⟩ => ⟨d + K0, ?_⟩⟩,
          fun hK colors rec hp => ?_⟩
  · have h := avoid_shift (fun i => f (K0 + i)) hK0 d
    simpa only [show ∀ i, K0 + (d + i) = d + (K0 + i) from fun i => by omega] using h
  · simpa only [Nat.add_assoc] using hK0
  · induction m with
    | zero => simp
    | succ m ih =>
      rw [show p + 5 * (m + 1) = (p + 5 * m) + 5 by omega,
          colored_strip_five x r K hK colors rec (p + 5 * m) (by omega), ih]

end Ruliology.CellularAutomata.Rule30ResetFreeStrip
