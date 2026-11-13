module
public import Ruliology.CellularAutomata.Rule30ResetFreeStrip
public import Ruliology.CellularAutomata.Rule30ZeroBoundary

/-! Every nonzero finite zero-wall row produces an inverse reset by time2.
The adjacent black pair shows that two rows do not suffice. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30ResetFreeThree
open Rule30ResetFreeCore Rule30ResetFreeRuns Rule30ZeroBoundary
open Rule30ResetFreeStrip (encodeAtom AtomOK atom_table atom_step_table xor_solve)
set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

theorem three_cases : ∀ i : Fin 3,i=0 ∨ i=1 ∨ i=2 := by decide +kernel
theorem fin0 : (0:Fin 3).val=0 := by decide +kernel
theorem fin1 : (1:Fin 3).val=1 := by decide +kernel
theorem fin2 : (2:Fin 3).val=2 := by decide +kernel

def packThree (d : Fin 3 → Nat) : Nat := d 0+6*d 1+36*d 2
theorem packThree_lt (d : Fin 3 → Nat) (bounds : ∀ i,d i<6) : packThree d<216 := by
  have h0 := bounds 0
  have h1 := bounds 1
  have h2 := bounds 2
  unfold packThree
  omega
theorem packThree_digit (d : Fin 3 → Nat) (bounds : ∀ i,d i<6) (i : Fin 3) :
    digit (packThree d) i.val=d i := by
  have h0 := bounds 0
  have h1 := bounds 1
  have h2 := bounds 2
  rcases three_cases i with h | h | h <;> subst i <;>
    simp only [packThree,digit,fin0,fin1,fin2,Nat.pow_zero,Nat.pow_succ] <;> omega
theorem unpack (s : Nat) (hs : s<216) : packThree (fun i => digit s i.val)=s := by
  simp only [packThree,digit,fin0,fin1,fin2,Nat.pow_zero,Nat.pow_succ]
  omega

def inputBit (s : Nat) (top : Bool) (t : Nat) : Bool :=
  if t=2 then top else xor (currentBit (digit s (t+1)))
    (currentBit (digit s t) || prevBit (digit s t))
def nextAux (s : Nat) (top : Bool) : Nat → Nat → Nat
  | 0,total => total
  | t+1,total =>
    if inputBit s top t=false ∧ runMod (digit s t)=1 then 216
    else nextAux s top t (total+6^t*nextAtom (digit s t) (inputBit s top t))
def nextState (s : Nat) (top : Bool) : Nat := nextAux s top 3 0
def NoReject (s : Nat) (top : Bool) : Prop :=
  ∀ i : Fin 3,¬(inputBit s top i.val=false ∧ runMod (digit s i.val)=1)

theorem transition_of_components {s u : Nat} (hu : u<216) (top : Bool)
    (allowed : NoReject s top) (components : ∀ i : Fin 3,
      digit u i.val=nextAtom (digit s i.val) (inputBit s top i.val)) : nextState s top=u := by
  have a0 := allowed (0:Fin 3)
  have a1 := allowed (1:Fin 3)
  have a2 := allowed (2:Fin 3)
  have e0 := components (0:Fin 3)
  have e1 := components (1:Fin 3)
  have e2 := components (2:Fin 3)
  simp only [fin0,fin1,fin2] at a0 a1 a2 e0 e1 e2
  simp only [nextState,nextAux,ite_eq_right a2,ite_eq_right a1,ite_eq_right a0]
  rw [← e0,← e1,← e2]
  have h := unpack u hu
  simp only [packThree,fin0,fin1,fin2] at h
  omega

def RowRecurrence (x : Fin 3 → Nat → Bool) : Prop := ∀ t : Fin 2,∀ p,1≤p →
  x ⟨t.val+1,by omega⟩ p=xor (x ⟨t.val,by omega⟩ (p+1))
    (x ⟨t.val,by omega⟩ p || x ⟨t.val,by omega⟩ (p-1))
def atomValue (x : Fin 3 → Nat → Bool) (r : Fin 3 → Nat → Nat) (p : Nat) (t : Fin 3) : Nat :=
  encodeAtom (x t (p-1)) (x t p) (r t p)
def vertex (x : Fin 3 → Nat → Bool) (r : Fin 3 → Nat → Nat) (p : Nat) : Nat :=
  packThree (atomValue x r p)

theorem atom_properties (x : Fin 3 → Nat → Bool) (r : Fin 3 → Nat → Nat) (K : Nat)
    (colors : ∀ t,ColoredFrom (x t) K (r t)) (p : Nat) (hp : K≤p) (t : Fin 3) :
    prevBit (atomValue x r p t)=x t (p-1) ∧ currentBit (atomValue x r p t)=x t p ∧
    runMod (atomValue x r p t)=r t p ∧ atomValue x r p t<6 := by
  have c := colors t p hp
  exact atom_table _ _ ⟨r t p,c.1⟩ ⟨c.2.1,c.2.2.1⟩
theorem vertex_bound (x : Fin 3 → Nat → Bool) (r : Fin 3 → Nat → Nat) (K : Nat)
    (colors : ∀ t,ColoredFrom (x t) K (r t)) (p : Nat) (hp : K≤p) : vertex x r p<216 :=
  packThree_lt _ (fun t => (atom_properties x r K colors p hp t).2.2.2)
theorem vertex_digit (x : Fin 3 → Nat → Bool) (r : Fin 3 → Nat → Nat) (K : Nat)
    (colors : ∀ t,ColoredFrom (x t) K (r t)) (p : Nat) (hp : K≤p) (t : Fin 3) :
    digit (vertex x r p) t.val=atomValue x r p t :=
  packThree_digit _ (fun i => (atom_properties x r K colors p hp i).2.2.2) t
theorem vertex_current (x : Fin 3 → Nat → Bool) (r : Fin 3 → Nat → Nat) (K : Nat)
    (colors : ∀ t,ColoredFrom (x t) K (r t)) (p : Nat) (hp : K≤p) (t : Fin 3) :
    currentBit (digit (vertex x r p) t.val)=x t p := by
  rw [vertex_digit x r K colors p hp t]
  exact (atom_properties x r K colors p hp t).2.1

theorem vertex_step (x : Fin 3 → Nat → Bool) (r : Fin 3 → Nat → Nat) (K : Nat)
    (hK : 1≤K) (colors : ∀ t,ColoredFrom (x t) K (r t)) (recurrence : RowRecurrence x)
    (p : Nat) (hp : K≤p) : nextState (vertex x r p) (x 2 (p+1))=vertex x r (p+1) := by
  have bits : ∀ t : Fin 3,inputBit (vertex x r p) (x 2 (p+1)) t.val=x t (p+1) := by
    intro t
    by_cases last : t.val=2
    · have eq : t=2 := Fin.ext last
      subst t
      simp only [inputBit,fin2,↓reduceIte]
    · have ht : t.val<2 := by omega
      have solved : x t (p+1)=xor (x ⟨t.val+1,by omega⟩ p) (x t p || x t (p-1)) :=
        xor_solve _ _ _ (recurrence ⟨t.val,ht⟩ p (by omega))
      simp only [inputBit,ite_eq_right last]
      rw [vertex_digit x r K colors p hp ⟨t.val+1,by omega⟩,
        vertex_digit x r K colors p hp t]
      rw [(atom_properties x r K colors p hp ⟨t.val+1,by omega⟩).2.1,
        (atom_properties x r K colors p hp t).2.1,(atom_properties x r K colors p hp t).1]
      exact solved.symm
  apply transition_of_components (vertex_bound x r K colors (p+1) (by omega)) (x 2 (p+1))
  · intro t forbidden
    rw [bits t,vertex_digit x r K colors p hp t,
      (atom_properties x r K colors p hp t).2.2.1] at forbidden
    exact (colors t p hp).2.2.2.1 forbidden.1 forbidden.2
  · intro t
    rw [vertex_digit x r K colors (p+1) (by omega) t,vertex_digit x r K colors p hp t,bits t]
    have old := colors t p hp
    have new := colors t (p+1) (by omega)
    rw [show p+1-1=p by omega] at new
    dsimp only [atomValue]
    rw [show p+1-1=p by omega]
    exact (atom_step_table _ _ _ ⟨r t p,old.1⟩ ⟨r t (p+1),new.1⟩
      ⟨old.2.1,old.2.2.1⟩ ⟨new.2.1,new.2.2.1⟩ old.2.2.2.1 old.2.2.2.2).symm

def reachableStates : List Nat := [0, 2, 3, 4, 5, 12, 14, 32, 72, 74, 75, 76, 77, 84, 86, 104, 192, 195, 196, 197]

def ReachOK (s : Nat) : Prop := ∀ b : Bool,nextState s b<216 →
  nextState s b ∈ reachableStates ∧ (nextState s b=0 → s=0)
instance (s : Nat) : Decidable (ReachOK s) := by unfold ReachOK;infer_instance
theorem reach_checked : (reachableStates.all (fun s => decide (ReachOK s)))=true := by decide +kernel
theorem reach_node (s : Nat) (hs : s∈reachableStates) : ReachOK s :=
  of_decide_eq_true (List.all_eq_true.1 reach_checked s hs)

def wallStart (a b c : Bool) : Nat :=
  (if a then 2 else 0)+6*(if b then 2 else 0)+36*(if c then 2 else 0)
theorem wall_starts : ∀ a b c : Bool,wallStart a b c∈reachableStates := by decide +kernel
def FinitePath (v : Nat → Nat) (b : Nat → Bool) : Prop :=
  ∀ n,v n<216 ∧ nextState (v n) (b n)=v (n+1)

theorem path_to_zero (v : Nat → Nat) (b : Nat → Bool) (path : FinitePath v b)
    (start : v 0∈reachableStates) (N : Nat) (last : v N=0) : ∀ k,k≤N → v k=0 := by
  have reach : ∀ n,v n∈reachableStates := by
    intro n
    induction n with
    | zero => exact start
    | succ n ih =>
      have h := reach_node (v n) ih (b n) (by rw [(path n).2];exact (path (n+1)).1)
      simpa only [(path n).2] using h.1
  have backwards : ∀ m,v (m+1)=0 → v m=0 := by
    intro m zero
    have h := reach_node (v m) (reach m) (b m) (by rw [(path m).2];exact (path (m+1)).1)
    exact h.2 (by rw [(path m).2];exact zero)
  have all : ∀ m,v m=0 → ∀ k,k≤m → v k=0 := by
    intro m
    induction m with
    | zero =>
      intro h k hk
      have eqk : k=0 := by omega
      subst k
      exact h
    | succ m ih =>
      intro h k hk
      by_cases old : k≤m
      · exact ih (backwards m h) k old
      · have eqk : k=m+1 := by omega
        subst k
        exact h
  exact all N last

theorem vertex_zero (x : Fin 3 → Nat → Bool) (r : Fin 3 → Nat → Nat) (p : Nat)
    (previous : ∀ t,x t (p-1)=false) (current : ∀ t,x t p=false) : vertex x r p=0 := by
  simp [vertex,packThree,atomValue,encodeAtom,previous,current]

theorem finite_three_avoid_zero (L : Nat → Bool) (finite : FinSupp L)
    (avoid : ∀ t : Fin 3,AvoidReset (zrow L t.val)) : ∀ p,1≤p → L p=false := by
  obtain ⟨W,fin⟩ := finite
  let x := fun t : Fin 3 => zrow L t.val
  let r := fun t p => scan (x t) 0 p
  have wall : ∀ t : Fin 3,x t 0=false := fun t => zrow_wall L t.val
  have colors : ∀ t,ColoredFrom (x t) 1 (r t) := by
    intro t
    have h := colored_after_zero (x t) (avoid t) 0 (wall t)
    simpa only [r,Nat.zero_add,Nat.sub_zero] using h
  have recurrence : RowRecurrence x := by
    intro t p hp
    obtain ⟨k,hk⟩ : ∃ k,p=k+1 := ⟨p-1,by omega⟩
    subst p
    have h := zrow_succ L t.val k
    simpa only [x,show k+1+1=k+2 by omega,show k+1-1=k by omega] using h
  let v := fun k => vertex x r (1+k)
  let b := fun k => x 2 (1+k+1)
  have path : FinitePath v b := by
    intro k
    refine ⟨vertex_bound x r 1 colors (1+k) (by omega),?_⟩
    have h := vertex_step x r 1 (by decide) colors recurrence (1+k) (by omega)
    simpa only [v,b,show 1+k+1=1+(k+1) by omega] using h
  have startEq : vertex x r 1=wallStart (x 0 1) (x 1 1) (x 2 1) := by
    simp [vertex,packThree,atomValue,encodeAtom,wallStart,wall]
  have start : v 0∈reachableStates := by
    dsimp only [v,Nat.add_zero]
    rw [startEq]
    exact wall_starts _ _ _
  intro p hp
  let N := W+p+5
  have last : v N=0 := by
    apply vertex_zero
    · intro t
      exact zrow_fin fin t.val _ (by have bound := t.isLt;dsimp [N];omega)
    · intro t
      exact zrow_fin fin t.val _ (by have bound := t.isLt;dsimp [N];omega)
  have vz := path_to_zero v b path start N last (p-1) (by dsimp [N];omega)
  have vp : vertex x r p=0 := by
    simpa only [v,show 1+(p-1)=p by omega] using vz
  have output := vertex_current x r 1 colors p hp 0
  rw [vp] at output
  have zero : currentBit (digit 0 (0:Fin 3).val)=false := by decide +kernel
  rw [zero] at output
  simpa only [x,fin0,zrow_zero_of_pos L hp] using output.symm

theorem not_avoid_witness (f : Nat → Bool) (bad : ¬AvoidReset f) :
    ∃ i n,n%3=1 ∧ f i=false ∧ f (i+n+1)=false ∧ ∀ j,j<n → f (i+j+1)=true := by
  classical
  by_cases ex : ∃ i n,n%3=1 ∧ f i=false ∧ f (i+n+1)=false ∧ ∀ j,j<n → f (i+j+1)=true
  · exact ex
  · apply False.elim
    apply bad
    intro i n left right ones modone
    exact ex ⟨i,n,modone,left,right,ones⟩

/-- Every nonzero finite row produces an inverse-reset word at time0,1or2. -/
theorem finite_nonzero_reset_in_three (L : Nat → Bool) (finite : FinSupp L)
    (nonzero : ∃ p,1≤p ∧ L p=true) : ∃ t : Fin 3,∃ i n,n%3=1 ∧
      zrow L t.val i=false ∧ zrow L t.val (i+n+1)=false ∧
      ∀ j,j<n → zrow L t.val (i+j+1)=true := by
  classical
  by_cases ex : ∃ t : Fin 3,¬AvoidReset (zrow L t.val)
  · obtain ⟨t,ht⟩ := ex
    exact ⟨t,not_avoid_witness _ ht⟩
  · have every : ∀ t : Fin 3,AvoidReset (zrow L t.val) := by
      intro t
      by_cases h : AvoidReset (zrow L t.val)
      · exact h
      · exact False.elim (ex ⟨t,h⟩)
    obtain ⟨p,hp,black⟩ := nonzero
    rw [finite_three_avoid_zero L finite every p hp] at black
    cases black

def pairAt (a k : Nat) : Bool := decide (k=a ∨ k=a+1)

theorem pair_avoid (a : Nat) : AvoidReset (pairAt a) := by
  intro i n left right ones modone
  have positive : 0<n := by omega
  have first : i+1=a ∨ i+1=a+1 := of_decide_eq_true (ones 0 (by omega))
  have final : i+(n-1)+1=a ∨ i+(n-1)+1=a+1 := of_decide_eq_true (ones (n-1) (by omega))
  have leftNo : ¬(i=a ∨ i=a+1) := by
    intro h
    have truth : pairAt a i=true := decide_eq_true h
    rw [left] at truth
    cases truth
  have rightNo : ¬(i+n+1=a ∨ i+n+1=a+1) := by
    intro h
    have truth : pairAt a (i+n+1)=true := decide_eq_true h
    rw [right] at truth
    cases truth
  have final' : i+n=a ∨ i+n=a+1 := by
    simpa only [show i+(n-1)+1=i+n by omega] using final
  omega

theorem pair_finite : ∀ k,2<k → pairAt 1 k=false := by
  intro k hk
  simp [pairAt,show k≠1 by omega,show k≠1+1 by omega]

theorem pair_step_small : ∀ k : Fin 5,zrow (pairAt 1) 1 k.val=pairAt 2 k.val := by decide +kernel

theorem pair_step (k : Nat) : zrow (pairAt 1) 1 k=pairAt 2 k := by
  by_cases small : k<5
  · exact pair_step_small ⟨k,small⟩
  · rw [zrow_fin pair_finite 1 k (by omega)]
    simp [pairAt,show k≠2 by omega,show k≠2+1 by omega]

/-- The adjacent black pair and its first image both avoid reset words, so
the three-row production bound cannot be replaced by two rows. -/
theorem sharpness_two_rows : FinSupp (pairAt 1) ∧ pairAt 1 1=true ∧
    AvoidReset (zrow (pairAt 1) 0) ∧ AvoidReset (zrow (pairAt 1) 1) := by
  refine ⟨⟨2,pair_finite⟩,by decide,?_,?_⟩
  · rw [zrow_zero_self (show pairAt 1 0=false by decide)]
    exact pair_avoid 1
  · have eq : zrow (pairAt 1) 1=pairAt 2 := funext pair_step
    rw [eq]
    exact pair_avoid 2

/-! ## Exact equivalence for three-row reset-free `FinSupp` starts and forced reset at `t = 2` for `pairAt 1` -/

/-- **Exact Equivalence for Three-Row Reset-Free `FinSupp` Starts and Forced Reset at `t = 2` for `pairAt 1` (`finSupp_three_avoid_iff_zero_and_pairAt_reset_two`).** -/
theorem finSupp_three_avoid_iff_zero_and_pairAt_reset_two
    (L : Nat → Bool) (finite : FinSupp L) :
    ((∀ t : Fin 3, AvoidReset (zrow L t.val)) ↔ (∀ p, 1 ≤ p → L p = false)) ∧
    ¬ AvoidReset (zrow (pairAt 1) 2) := by
  have hzero_zrow : (∀ p, 1 ≤ p → L p = false) → ∀ t p, zrow L t p = false := by
    intro hL t
    induction t with
    | zero =>
      intro p
      cases p with
      | zero => rfl
      | succ k => exact hL (k + 1) (by omega)
    | succ t ih =>
      intro p
      cases p with
      | zero => rfl
      | succ k => simp [zrow, ih]
  refine ⟨⟨finite_three_avoid_zero L finite, fun hL t i n hi hn hones => ?_⟩, fun h2 => ?_⟩
  · cases n with
    | zero => decide
    | succ n =>
      have h0 := hones 0 (by omega)
      rw [hzero_zrow hL t.val (i + 0 + 1)] at h0
      cases h0
  · obtain ⟨hfin, h1, ha0, ha1⟩ := sharpness_two_rows
    have hall : ∀ t : Fin 3, AvoidReset (zrow (pairAt 1) t.val) := by
      intro ⟨t, ht⟩
      rcases (show t = 0 ∨ t = 1 ∨ t = 2 by omega) with rfl | rfl | rfl
      · exact ha0
      · exact ha1
      · exact h2
    have hfalse := finite_three_avoid_zero (pairAt 1) hfin hall 1 (by decide)
    rw [h1] at hfalse
    cases hfalse

end Ruliology.CellularAutomata.Rule30ResetFreeThree
