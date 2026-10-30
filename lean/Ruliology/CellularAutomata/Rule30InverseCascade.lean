module
public import Ruliology.CellularAutomata.Rule30Prize
public import Ruliology.CellularAutomata.Rule30Predecessors

/-!
# Uniform closing of finite inverse cascades, with infinite driver rows

Every finite height and every competing initial register are quantified.
Recurrent synchronizing segments suffice; no spatial or temporal periodicity,
uniform waiting bound, finite-state gate abstraction or probabilistic assumption
is used. The physical corollary assumes row closing at every relevant depth;
it does not establish that open condition for arbitrary legal Gate futures.

This generalizes the periodic synchronizing-carrier reduction to nonperiodic
drivers. The coinailyzer-swarm staircase handoff supplied the paper argument.
The scan and reset definitions follow the earlier checked RunClosing research
archive; transfer is the official Feynman predecessor map Rule30.T.
-/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30InverseCascade

abbrev State := Rule30.State
abbrev transfer := Rule30.T

def scan : List Bool → State → State
  | [],s => s
  | b::w,s => scan w (transfer b s)

def Synchronized (w : List Bool) : Prop :=
  ∀ a b c d : Bool,scan w (a,b)=scan w (c,d)

def segment (f : Nat → Bool) : Nat → Nat → List Bool
  | _,0 => []
  | a,n+1 => f a::segment f (a+1) n

def TailClosing (f : Nat → Bool) : Prop :=
  ∀ d,∃ a n,d≤a ∧ Synchronized (segment f a n)

theorem scan_append (u v : List Bool) (s : State) :
    scan (u++v) s=scan v (scan u s) := by
  induction u generalizing s with
  | nil => rfl
  | cons b u ih => simpa only [List.cons_append,scan] using ih (transfer b s)

theorem synchronized_context (u w v : List Bool) (h : Synchronized w) :
    Synchronized (u++w++v) := by
  intro a b c d
  simp only [scan_append]
  rw [h (scan u (a,b)).1 (scan u (a,b)).2 (scan u (c,d)).1 (scan u (c,d)).2]

theorem segment_add (f : Nat → Bool) (a m n : Nat) :
    segment f a (m+n)=segment f a m++segment f (a+m) n := by
  induction m generalizing a with
  | zero => simp [segment]
  | succ m ih =>
    rw [show (m+1)+n=(m+n)+1 by omega]
    simp only [segment,List.cons_append,ih]
    rw [show a+1+m=a+(m+1) by omega]

theorem tail_closing_iff (f : Nat → Bool) :
    TailClosing f ↔ ∀ d,∃ n,Synchronized (segment f d n) := by
  constructor
  · intro h d
    obtain ⟨a,n,ha,hs⟩ := h d
    refine ⟨(a-d)+n,?_⟩
    rw [segment_add,show d+(a-d)=a by omega]
    have he := synchronized_context (segment f d (a-d)) (segment f a n) [] hs
    simpa only [List.append_nil] using he
  · intro h d
    obtain ⟨n,hn⟩ := h d
    exact ⟨d,n,Nat.le_refl _,hn⟩

def forward (a : Nat → Bool) (k : Nat) : Bool :=
  Rule30.rule (a (k+2)) (a (k+1)) (a k)

theorem forward_transfer (a : Nat → Bool) (k : Nat) :
    transfer (forward a k) (a (k+1),a k)=(a (k+2),a (k+1)) := by
  simp only [transfer,Rule30.T,forward,Rule30.rule]
  cases a (k+2) <;> cases (a (k+1)||a k) <;> rfl

def RowClosing (a : Nat → Bool) : Prop := TailClosing (forward a)

theorem row_closing_iff (a : Nat → Bool) :
    RowClosing a ↔ TailClosing (forward a) := Iff.rfl

abbrev Trajectory := Nat → Nat → State

def input (m : Nat) (driver : Nat → Bool) (X : Trajectory) (i k : Nat) : Bool :=
  if i+1<m then (X (i+1) k).2 else driver k

def StackLaw (m : Nat) (driver : Nat → Bool) (X : Trajectory) : Prop :=
  ∀ i, i<m → ∀ k, X i (k+1)=transfer (input m driver X i k) (X i k)

def DriversClosing (m : Nat) (driver : Nat → Bool) (X : Trajectory) : Prop :=
  ∀ i, i<m → TailClosing (input m driver X i)

def suffix (X : Trajectory) : Trajectory := fun i k => X (i+1) k

theorem suffix_input (m : Nat) (driver : Nat → Bool) (X : Trajectory) (i k : Nat) :
    input m driver (suffix X) i k=input (m+1) driver X (i+1) k := by
  simp only [input,suffix]
  split <;> split <;> simp_all <;> omega

theorem suffix_law {m : Nat} {driver : Nat → Bool} {X : Trajectory}
    (h : StackLaw (m+1) driver X) : StackLaw m driver (suffix X) := by
  intro i hi k
  have hh := h (i+1) (by omega) k
  simpa only [suffix,← suffix_input] using hh

theorem suffix_closing {m : Nat} {driver : Nat → Bool} {X : Trajectory}
    (h : DriversClosing (m+1) driver X) : DriversClosing m driver (suffix X) := by
  intro i hi
  have hh := h (i+1) (by omega)
  have eq : input m driver (suffix X) i=input (m+1) driver X (i+1) :=
    funext (suffix_input m driver X i)
  rw [eq]
  exact hh

theorem trajectory_scan (f : Nat → Bool) (x : Nat → State)
    (h : ∀ k,x (k+1)=transfer (f k) (x k)) (d n : Nat) :
    scan (segment f d n) (x d)=x (d+n) := by
  induction n generalizing d with
  | zero => simp only [segment,scan,Nat.add_zero]
  | succ n ih =>
    simp only [segment,scan,← h]
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (d+1)

theorem segment_eq_tail {f g : Nat → Bool} {K : Nat}
    (h : ∀ k,K≤k → f k=g k) (d n : Nat) (hd : K≤d) :
    segment f d n=segment g d n := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih => simp only [segment,h d hd,ih (d+1) (by omega)]

/-- A selected synchronizing segment merges any two trajectories whose inputs
agree on the entire suffix. The cutoff does not depend on their initial states. -/
theorem merge_at_segment {f g : Nat → Bool} {x y : Nat → State} {K n : Nat}
    (hx : ∀ k,x (k+1)=transfer (f k) (x k))
    (hy : ∀ k,y (k+1)=transfer (g k) (y k))
    (inputs : ∀ k,K≤k → f k=g k)
    (sync : Synchronized (segment f K n)) :
    ∀ k,K+n≤k → x k=y k := by
  have at_end : x (K+n)=y (K+n) := by
    rw [← trajectory_scan f x hx K n,← trajectory_scan g y hy K n,
      ← segment_eq_tail inputs K n (by omega)]
    exact sync (x K).1 (x K).2 (y K).1 (y K).2
  have later : ∀ j,x (K+n+j)=y (K+n+j) := by
    intro j
    induction j with
    | zero => simpa only [Nat.add_zero] using at_end
    | succ j ih =>
      rw [show K+n+(j+1)=(K+n+j)+1 by omega,hx,hy,ih,inputs _ (by omega)]
  intro k hk
  have h := later (k-(K+n))
  simpa only [Nat.add_sub_of_le hk] using h

/-- Arbitrary height, arbitrary infinite driver, and ONE cutoff uniform over
all competing initial registers. No bound on the reset waiting times is used. -/
theorem finite_cascade_closes (m : Nat) (driver : Nat → Bool) (X : Trajectory)
    (law : StackLaw m driver X) (closing : DriversClosing m driver X) :
    ∃ K, ∀ Y : Trajectory, StackLaw m driver Y →
      ∀ i,i<m → ∀ k,K≤k → X i k=Y i k := by
  induction m generalizing X with
  | zero =>
    exact ⟨0,fun _ _ _ hi => by omega⟩
  | succ m ih =>
    obtain ⟨K,hK⟩ := ih (suffix X) (suffix_law law) (suffix_closing closing)
    obtain ⟨n,hn⟩ := (tail_closing_iff _).mp (closing 0 (by omega)) K
    refine ⟨K+n,?_⟩
    intro Y hY i hi k hk
    by_cases top : i=0
    · subst i
      apply merge_at_segment (law 0 (by omega)) (hY 0 (by omega)) ?_ hn k hk
      intro s hs
      unfold input
      by_cases hm : 1<m+1
      · simp only [hm,↓reduceIte]
        have he := hK (suffix Y) (suffix_law hY) 0 (by omega) s hs
        exact congrArg Prod.snd he
      · simp only [hm,↓reduceIte]
    · obtain ⟨j,rfl⟩ : ∃ j,i=j+1 := ⟨i-1,by omega⟩
      exact hK (suffix Y) (suffix_law hY) j (by omega) k (by omega)

def reference (a : Nat → Nat → Bool) : Trajectory :=
  fun i k => (a i (k+1),a i k)

theorem reference_input (a : Nat → Nat → Bool) (m i : Nat) (hi : i<m) :
    input m (a m) (reference a) i=a (i+1) := by
  funext k
  unfold input reference
  split
  · rfl
  · have eq : i+1=m := by omega
    rw [eq]

theorem reference_law (a : Nat → Nat → Bool)
    (recurrence : ∀ i,a (i+1)=forward (a i)) (m : Nat) :
    StackLaw m (a m) (reference a) := by
  intro i hi k
  rw [reference_input a m i hi,recurrence i]
  exact (forward_transfer (a i) k).symm

/-- The physical-row corollary suggested by swarm's staircase argument.
It assumes RowClosing at every depth and does not assert that hypothesis
for S-legal gates or for any other unresolved ancestry class. -/
theorem physical_block_closes (a : Nat → Nat → Bool)
    (recurrence : ∀ i,a (i+1)=forward (a i))
    (closing : ∀ i,RowClosing (a i)) (m : Nat) :
    ∃ K, ∀ Y : Trajectory, StackLaw m (a m) Y →
      ∀ i,i<m → ∀ k,K≤k → Y i k=(a i (k+1),a i k) := by
  have drivers : DriversClosing m (a m) (reference a) := by
    intro i hi
    rw [reference_input a m i hi,recurrence i]
    exact (row_closing_iff _).mp (closing i)
  obtain ⟨K,hK⟩ := finite_cascade_closes m (a m) (reference a)
    (reference_law a recurrence m) drivers
  exact ⟨K,fun Y hY i hi k hk => (hK Y hY i hi k hk).symm⟩


theorem ones_reduce (k : Nat) (s : State) :
    scan (List.replicate (3*k+1) true) s=transfer true s := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 3*(k+1)+1=(3*k+1)+3 by omega,
      ← List.replicate_append_replicate,scan_append,ih]
    rcases s with ⟨p,q⟩
    cases p <;> cases q <;> rfl

theorem run_resets (k : Nat) (last : Bool) :
    Synchronized ([false]++List.replicate (3*k+1) true++[false,last]) := by
  intro a b c d
  simp only [scan_append,scan,ones_reduce]
  cases a <;> cases b <;> cases c <;> cases d <;> cases last <;> rfl

/-- The concrete unbounded black-run criterion suffices. The following cell
is part of the reset word and must not be omitted. -/
theorem reset_runs_closing (f : Nat → Bool)
    (runs : ∀ d,∃ a k last,d≤a ∧
      segment f a (3*k+4)=[false]++List.replicate (3*k+1) true++[false,last]) :
    TailClosing f := by
  intro d
  obtain ⟨a,k,last,ha,he⟩ := runs d
  exact ⟨a,3*k+4,ha,he ▸ run_resets k last⟩

def ResetSchedule (m : Nat) (driver : Nat → Bool) (X : Trajectory)
    (K : Nat → Nat) : Prop :=
  ∀ j,j<m → K j≤K (j+1) ∧ Synchronized
    (segment (input m driver X (m-1-j)) (K j) (K (j+1)-K j))

/-- Each wait starts after the preceding wait ends. The cutoff is K m.
No growth rate is asserted: waits can depend on the preceding cutoff. -/
theorem scheduled_cascade_closes (m : Nat) (driver : Nat → Bool) (X : Trajectory)
    (law : StackLaw m driver X) (K : Nat → Nat)
    (schedule : ResetSchedule m driver X K) :
    ∀ Y : Trajectory,StackLaw m driver Y →
      ∀ i,i<m → ∀ k,K m≤k → X i k=Y i k := by
  have layer : ∀ j,j≤m → ∀ Y : Trajectory,StackLaw m driver Y →
      ∀ i,m-j≤i → i<m → ∀ k,K j≤k → X i k=Y i k := by
    intro j
    induction j with
    | zero => intro _ _ _ _ _ hi;omega
    | succ j ih =>
      intro hj Y hY i hlow hi k hk
      obtain ⟨mono,sync⟩ := schedule j (by omega)
      by_cases newrow : i=m-1-j
      · subst i
        have inputs : ∀ s,K j≤s →
            input m driver X (m-1-j) s=input m driver Y (m-1-j) s := by
          intro s hs
          unfold input
          by_cases inside : m-1-j+1<m
          · simp only [inside,↓reduceIte]
            exact congrArg Prod.snd (ih (by omega) Y hY (m-1-j+1)
              (by omega) (by omega) s hs)
          · simp only [inside,↓reduceIte]
        have merged := merge_at_segment (law (m-1-j) (by omega))
          (hY (m-1-j) (by omega)) inputs sync
        rw [Nat.add_sub_of_le mono] at merged
        exact merged k hk
      · exact ih (by omega) Y hY i (by omega) hi k (Nat.le_trans mono hk)
  intro Y hY i hi k hk
  exact layer m (Nat.le_refl m) Y hY i (by omega) hi k hk

/-- Recurrent resets provide a schedule from EVERY chosen starting column.
The selected schedule depends only on the reference and not on competitors. -/
theorem exists_reset_schedule (m : Nat) (driver : Nat → Bool) (X : Trajectory)
    (closing : DriversClosing m driver X) (start : Nat) :
    ∃ K : Nat → Nat,K 0=start ∧ ResetSchedule m driver X K := by
  classical
  have waits : ∀ i,i<m → ∀ d,∃ n,Synchronized (segment (input m driver X i) d n) :=
    fun i hi => (tail_closing_iff _).mp (closing i hi)
  let w : Nat → Nat → Nat := fun i d =>
    if hi : i<m then Classical.choose (waits i hi d) else 0
  have hw (i : Nat) (hi : i<m) (d : Nat) :
      Synchronized (segment (input m driver X i) d (w i d)) := by
    dsimp only [w]
    rw [dite_eq_left hi]
    exact Classical.choose_spec (waits i hi d)
  let K : Nat → Nat := Nat.rec start (fun j k => k+w (m-1-j) k)
  have stepK (j : Nat) : K (j+1)=K j+w (m-1-j) (K j) := rfl
  refine ⟨K,rfl,?_⟩
  intro j hj
  rw [stepK]
  refine ⟨by omega,?_⟩
  simpa only [Nat.add_sub_cancel_left] using hw (m-1-j) (by omega) (K j)

def zeroStack : Trajectory := fun _ _ => (false,false)
def oneStack : Trajectory := fun _ _ => (true,true)

/-- Dropping the reset hypothesis is false already at height one, for
infinite trajectories: a white driver preserves two different fixed states. -/
theorem missing_resets_counterexample :
    StackLaw 1 (fun _ => false) zeroStack ∧
    StackLaw 1 (fun _ => false) oneStack ∧
    ∀ k,zeroStack 0 k≠oneStack 0 k := by
  refine ⟨?_,?_,?_⟩
  · intro i hi k
    have he : i=0 := by omega
    subst i
    rfl
  · intro i hi k
    have he : i=0 := by omega
    subst i
    rfl
  · intro k h
    have impossible := congrArg Prod.fst h
    cases impossible

end Ruliology.CellularAutomata.Rule30InverseCascade
