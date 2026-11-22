module

public import Ruliology.CellularAutomata.Rule30MaskedJen
public import Ruliology.CellularAutomata.Rule30ZeroBoundaryBarriers
public import Ruliology.CellularAutomata.Rule30LateObservation
public import Ruliology.CellularAutomata.Rule30Window

/-!
# Counting masked futures at a fixed center clock

Column one at the next tick is the complement of the present center
whenever column one is black now. Use that single Rule 30 constraint to
enumerate possible OR readings for a specified center word. Over two
ticks the weighted size of the list of continuations increases by at
most a factor of two. A length-2n center word therefore admits at most
2^(n+1) candidate masked words, uniformly in the word.

For a proposed period P after T this gives genuine singleton forks at
phase spacing P*Q with later age at most 2*M + 2*(P*Q)*2^(n+1), M ≥ T.
The two masked words agree for 2n ticks and their previous white-center
readings are opposite. A sufficient scale-dependent reader is stated in
`problem1_of_read_scales`. Its hypothesis remains open. At two genuine
ages eight extra past center readings still leave a fork at a fixed scale.

Contributed by Troy Lowry with OpenAI Codex.
-/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30MaskedForkRate
open Rule30Jen Rule30MaskedJen Rule30Realization

inductive State where | free | white | black deriving DecidableEq
open State

def accepts : State → Bool → Prop
  | free, _ => True
  | white, b => b=false
  | black, b => b=true

def addBit (b : Bool) (ws : List (List Bool)) := ws.map (b :: ·)

def words : List Bool → State → List (List Bool)
  | [], _ => [[]]
  | b::c, s =>
    match s,b with
    | free,false => addBit false (words c free) ++ addBit true (words c black)
    | white,false => addBit false (words c free)
    | black,false => addBit true (words c black)
    | black,true => addBit true (words c white)
    | _,true => addBit true (words c free)

private def weight : State → Nat | free => 4 | white => 3 | black => 2
private def advance (b : Bool) (f : State → Nat) : State → Nat
  | free => if b then f free else f free + f black
  | white => f free
  | black => if b then f white else f black

private theorem length_cons (b : Bool) (c : List Bool) (s : State) :
    (words (b::c) s).length = advance b (fun u => (words c u).length) s := by
  cases s <;> cases b <;> simp [words,addBit,advance]
private theorem mono {f g : State → Nat} (h : ∀ s, f s≤g s) (b : Bool) (s : State) :
    advance b f s ≤ advance b g s := by
  have := h free; have := h black; have := h white
  cases s <;> cases b <;> simp [advance] <;> omega
private theorem scale (c : Nat) (b : Bool) (f : State → Nat) (s : State) :
    advance b (fun u => f u*c) s=advance b f s*c := by
  cases s <;> cases b <;> simp [advance,Nat.add_mul]
private theorem pair_budget (a b : Bool) (s : State) :
    advance a (advance b weight) s ≤ 2*weight s := by
  cases a <;> cases b <;> cases s <;> decide

private theorem bound (n : Nat) (c : List Bool) (hc : c.length=2*n) :
    ∀ s, (words c s).length*2 ≤ weight s * 2^n := by
  induction n generalizing c with
  | zero =>
    have h : c=[] := List.length_eq_zero_iff.mp (by omega)
    subst c
    intro s; cases s <;> decide
  | succ n ih =>
    obtain _|⟨a,tail⟩ := c
    · simp at hc
    obtain _|⟨b,rest⟩ := tail
    · simp at hc; omega
    have smaller := ih rest (by simp at hc; omega)
    intro s
    let f := fun u => (words rest u).length
    simp only [length_cons]
    change advance a (advance b f) s*2 ≤ _
    calc
      _ = advance a (advance b (fun u => f u*2)) s := by
        rw [show advance b (fun u => f u*2) = (fun u => advance b f u*2) from funext (scale 2 b f),scale]
      _ ≤ advance a (advance b (fun u => weight u*2^n)) s :=
        mono (mono smaller b) a s
      _ = advance a (advance b weight) s * 2^n := by
        rw [show advance b (fun u => weight u*2^n) = (fun u => advance b weight u*2^n)
          from funext (scale _ b weight),scale]
      _ ≤ (2*weight s)*2^n := Nat.mul_le_mul_right _ (pair_budget a b s)
      _ = _ := by simp [Nat.pow_succ,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc]

theorem masked_word_count (n : Nat) (c : List Bool) (hc : c.length=2*n) :
    (words c free).length ≤ 2^(n+1) := by
  have h := bound n c hc free
  simp only [Nat.pow_succ]
  simp only [weight] at h
  omega

def segment (f : Nat → Bool) (t : Nat) : Nat → List Bool
  | 0 => []
  | n+1 => f t :: segment f (t+1) n

private theorem segment_length (f : Nat → Bool) (t n : Nat) :
    (segment f t n).length=n := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih => simp [segment,ih]

private theorem allowed_cons {s : State} {b r u : Bool} {c v : List Bool}
    (hr : accepts s r)
    (h : ∀ q, accepts q (rule b r u) → v∈words c q) :
    ((b||r)::v) ∈ words (b::c) s := by
  have hf := h free trivial
  cases s <;> cases b <;> cases r <;>
    simp_all [accepts,words,addBit,rule]

/-- The candidate list covers all genuine right observations, including those
of a singleton or an arbitrary initial configuration. -/
theorem observations_mem (x : Int → Bool) (t n : Nat) (s : State)
    (hr : accepts s (evol x t 1)) :
    segment (fun i => evol x i 0 || evol x i 1) t n ∈
      words (segment (fun i => evol x i 0) t n) s := by
  induction n generalizing t s with
  | zero => simp [segment,words]
  | succ n ih =>
    apply allowed_cons (u:=evol x t 2) hr
    exact fun q h => ih (t+1) q h

private theorem seg_eq {f : Nat → Bool} {i j n : Nat}
    (h : ∀ k, k<n → f (i+k)=f (j+k)) : segment f i n=segment f j n := by
  induction n generalizing i j with
  | zero => rfl
  | succ n ih =>
    simp only [segment,List.cons.injEq]
    refine ⟨by simpa using h 0 (by omega), ih ?_⟩
    intro k hk
    simpa only [show i+1+k=i+(k+1) by omega,show j+1+k=j+(k+1) by omega] using h (k+1) (by omega)

private theorem seg_at {f : Nat → Bool} {i j n : Nat}
    (h : segment f i n=segment f j n) (k : Nat) (hk : k<n) : f (i+k)=f (j+k) := by
  induction n generalizing i j k with
  | zero => omega
  | succ n ih =>
    have hh := List.cons.inj h
    cases k with
    | zero => simpa using hh.1
    | succ k =>
      simpa only [show i+(k+1)=i+1+k by omega,show j+(k+1)=j+1+k by omega] using
        ih hh.2 k (by omega)

private theorem last_difference (f : Nat → Bool) (u d n : Nat) (h : f u≠f (u+d)) :
    ∃ i, u≤i ∧ i≤u+n ∧ f i≠f (i+d) ∧ ∀ t, i<t → t≤u+n → f t=f (t+d) := by
  induction n with
  | zero => exact ⟨u,by omega,by omega,h,by omega⟩
  | succ n ih =>
    by_cases e : f (u+(n+1))=f (u+(n+1)+d)
    · obtain ⟨i,hi,le,v,same⟩ := ih
      refine ⟨i,hi,by omega,v,fun t ht endt => ?_⟩
      by_cases small : t≤u+n
      · exact same _ ht small
      · simpa only [show t=u+(n+1) by omega] using e
    · exact ⟨_,by omega,by omega,e,by omega⟩

/-- Under any proposed center period, two ages in a common phase have
opposite readings and an identical masked future of length 2n. The age
bound has exponent n+1. -/
theorem fast_fork {T P : Nat} (hp : 0<P)
    (per : ∀ t, T≤t → cell (t+P) 0=cell t 0) (M Q n : Nat) (late : T≤M) (hq : 0<Q) :
    ∃ i j, M≤i ∧ i<j ∧ P*Q ∣ j-i ∧ j≤2*M+2*((P*Q)*2^(n+1)) ∧
      orCol 0 i ≠ orCol 0 j ∧ ∀ k, k<2*n → orCol 0 (i+1+k)=orCol 0 (j+1+k) := by
  classical
  let S := P*Q
  let C := 2^(n+1)
  let B := 2*M+S*C
  have align (t d : Nat) (ht : T≤t) (hd : P∣d) : cell (t+d) 0=cell t 0 := by
    obtain ⟨q,rfl⟩ := hd
    simpa [Nat.mul_comm] using periodic_mul (f:=fun i => cell i 0) per q t ht
  let age (k : Nat) := B+S*k+1
  let centerWord := segment (fun t => cell t 0) (B+1) (2*n)
  let key (k : Nat) := segment (orCol 0) (age k) (2*n)
  have common (k : Nat) : segment (fun t => cell t 0) (age k) (2*n)=centerWord := by
    apply seg_eq
    intro a _
    have e := align (B+1+a) (S*k) (by dsimp [B]; omega)
      (Nat.dvd_trans (Nat.dvd_mul_right P Q) (Nat.dvd_mul_right S k))
    rwa [show B+1+a+S*k=age k+a by dsimp [age]; omega] at e
  have mem (k : Nat) : key k ∈ words centerWord free := by
    have H := observations_mem seed (age k) (2*n) free trivial
    simp only [evol_seed,common] at H
    change segment (fun i => cell i 0 || cell i 1) (age k) (2*n) ∈ words centerWord free
    exact H
  obtain ⟨u,v,uv,cap,same⟩ := Rule30ZeroBoundaryBarriers.pigeonhole_gen _ key mem
  have vC : v≤C := Nat.le_trans cap (masked_word_count n _ (segment_length _ _ _))
  let d := S*(v-u)
  have pos : 0<d := Nat.mul_pos (Nat.mul_pos hp hq) (by omega)
  have delta : S*u+d=S*v := by unfold d; rw [← Nat.mul_add]; congr 1; omega
  have small := Nat.mul_le_mul_left S vC
  have divides : S∣d := Nat.dvd_mul_right _ _
  have pd : P∣d := Nat.dvd_trans (Nat.dvd_mul_right P Q) divides
  have ad : age u+d=age v := by dsimp [age]; omega
  have earlier : ∃ z, z<M+d ∧ orCol 0 (M+z)≠orCol 0 (M+z+d) := by
    apply Classical.byContradiction
    intro none
    apply window_jen (t₁:=M) (t₂:=M+d) (by omega)
    · intro k _
      rw [show M+d+k=M+k+d by omega]
      exact (align _ d (by omega) pd).symm
    · intro k hk
      rw [show M+d+k=M+k+d by omega]
      exact Classical.byContradiction fun he => none ⟨k,hk,he⟩
  obtain ⟨z,hz,hne⟩ := earlier
  have az : M+z<age u := by dsimp [age,B]; omega
  obtain ⟨i,lo,hi,ne,rest⟩ := last_difference (orCol 0) (M+z) d (age u-1-(M+z)) hne
  have eqend : M+z+(age u-1-(M+z))=age u-1 := by omega
  rw [eqend] at hi rest
  refine ⟨i,i+d,by omega,by omega,by simpa using divides,?_,ne,?_⟩
  · change i+d≤2*M+2*(S*C)
    dsimp [age,B] at hi
    omega
  · intro k hk
    by_cases early : i+1+k<age u
    · rw [show i+d+1+k=i+1+k+d by omega]
      exact rest _ (by omega) (by omega)
    · let a := i+1+k-age u
      have ha : a<2*n := by dsimp [a]; omega
      have eqv := seg_at same a ha
      rwa [show age u+a=i+1+k by dsimp [a]; omega,
          show age v+a=i+d+1+k by dsimp [a]; omega] at eqv

/-- A finite test on the actual singleton. It gives the reader the common
center segment from half the earlier age through the end of the forecast,
the clock phase and the next left window. Its conclusion is the previous
right bit. Each fixed A,n bounds both observed ages. -/
def ReadsAt (M Q A n : Nat) : Prop :=
  ∀ i j, M≤i → i<j → Q∣j-i → j≤A*2^n →
    cell i 0=false → cell j 0=false →
    (∀ t, i/2≤t → t≤i+2*n+1 → cell t 0=cell (t+(j-i)) 0) →
    Rule30LateObservation.Agree (cell (i+1)) (cell (j+1)) (-((2*n:Nat):Int)) 0 →
    cell i 1=cell j 1

/-- The scale n may be chosen separately for each multiplier A.
Proving the hypothesis on the singleton would establish Problem 1. -/
theorem problem1_of_read_scales (M Q : Nat) (hq : 0<Q)
    (reader : ∀ A, 0<A → ∃ n, 0<n ∧ ReadsAt M Q A n) : Rule30Prize.Problem1 := by
  rintro ⟨T,P,hp,per⟩
  let B := max M (2*T)
  let S := P*Q
  let A := 2*B+4*S
  have hS : 0<S := Nat.mul_pos hp hq
  obtain ⟨n,_,read⟩ := reader A (by dsimp [A]; omega)
  obtain ⟨i,j,lo,lt,hd,cap,diff,same⟩ := fast_fork hp per B Q n (by dsimp [B]; omega) hq
  have iT : 2*T≤i := by dsimp [B] at lo; omega
  have pd : P∣j-i := Nat.dvd_trans (Nat.dvd_mul_right P Q) hd
  have shift (t : Nat) (ht : T≤t) : cell t 0=cell (t+(j-i)) 0 := by
    obtain ⟨k,hk⟩ := pd
    rw [hk,Nat.mul_comm P k]
    exact (periodic_mul (f:=fun s => cell s 0) per k t ht).symm
  have cu (t : Nat) : cell (i+t) 0=cell (j+t) 0 := by
    simpa only [show i+t+(j-i)=j+t by omega] using shift (i+t) (by omega)
  have c0 : cell i 0=cell j 0 := by simpa using cu 0
  have wi : cell i 0=false := by
    cases v : cell i 0
    · rfl
    · exact False.elim (diff (by simp [orCol,← c0,v]))
  have wj := c0.symm.trans wi
  have obs : Rule30LateObservation.Observed (Rule30LateObservation.fromAge (i+1))
      (Rule30LateObservation.fromAge (j+1)) 0 (2*n) := by
    refine ⟨fun a _ => ?_,fun a ha => ?_⟩
    · simpa [Rule30LateObservation.fromAge,Nat.add_assoc] using cu (1+a)
    · simpa [Rule30LateObservation.fromAge,orCol] using same a ha
  have out := Rule30LateObservation.observed_row _ _ (Rule30LateObservation.singleton_history _)
    (Rule30LateObservation.singleton_history _) 0 _ obs
  have cap' : j≤A*2^n := by
    change j≤(2*B+4*S)*2^n
    have bb : 2*B≤2*B*2^n := by
      have := Nat.mul_le_mul_left (2*B) (show 1≤2^n from Nat.two_pow_pos n)
      simpa using this
    change j≤2*B+2*(S*2^(n+1)) at cap
    simp only [Nat.pow_succ] at cap
    rw [Nat.add_mul,show 4*S*2^n=2*(S*(2^n*2)) by
      change (2*2)*S*2^n=2*(S*(2^n*2)); ac_rfl]
    omega
  have rr := read i j (by dsimp [B] at lo; omega) lt (Nat.dvd_trans (Nat.dvd_mul_left Q P) hd)
    cap' wi wj (fun t h _ => shift t (by omega)) out
  exact diff (by simp [orCol,wi,wj,rr])

/-- Observation used in the finite test: eight center bits before the
fork, fourteen from the fork onwards, thirteen cells up to the center on
the next row, and the twelve subsequent OR readings. -/
def observation (t : Nat) :=
  (segment (fun i => cell i 0) (t-8) 22,
   (List.range 13).map (fun k : Nat => cell (t+1) (-(k:Int))),
   segment (orCol 0) (t+1) 12)

private def packed (t : Nat) (p : Int) :=
  (Rule30Window.row 2000 t).testBit (2000+p).toNat
private theorem read_packed {t : Nat} (ht : t≤2000) {p : Int} (hp : -2000≤p) :
    cell t p=packed t p := by
  have h := Rule30Window.row_testBit 2000 t ht (2000+p).toNat
  rw [show ((2000+p).toNat:Int)-(2000:Nat)=p by omega] at h
  exact h.symm
private theorem segment_replace {f g : Nat → Bool} {t n : Nat}
    (h : ∀ i, t≤i → i<t+n → f i=g i) : segment f t n=segment g t n := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    simp only [segment,List.cons.injEq]
    exact ⟨h t (by omega) (by omega),ih (fun i hl hu => h i (by omega) (by omega))⟩
private def packedObs (t : Nat) :=
  (segment (fun i => packed i 0) (t-8) 22,
   (List.range 13).map (fun k : Nat => packed (t+1) (-(k:Int))),
   segment (fun i => packed i 0 || packed i 1) (t+1) 12)
private theorem obs_packed (t : Nat) (hl : 8≤t) (ht : t+14≤2000) : observation t=packedObs t := by
  unfold observation packedObs
  have C := @segment_replace (fun i => cell i 0) (fun i => packed i 0) (t-8) 22
    (fun i _ h => read_packed (by omega) (by decide))
  have L := List.map_congr_left (l:=List.range 13) (f:=fun k : Nat => cell (t+1) (-(k:Int)))
    (g:=fun k : Nat => packed (t+1) (-(k:Int))) (by
      intro k hk; have := List.mem_range.mp hk
      exact read_packed (by omega) (by omega))
  have O := @segment_replace (orCol 0) (fun i => packed i 0 || packed i 1) (t+1) 12 (by
    intro i _ h
    simp only [orCol,read_packed (t:=i) (p:=0) (by omega) (by decide),
      show (0:Int)+1=1 by decide,read_packed (t:=i) (p:=1) (by omega) (by decide)])
  rw [C,L,O]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
/-- Actual singleton ages give a fork despite eight equal past center
ticks, fourteen equal center ticks from the fork, equal subsequent masks
and equal next left windows. This only excludes this fixed observation. -/
theorem singleton_eight_past :
    observation 214=observation 1981 ∧ cell 214 0=false ∧ cell 1981 0=false ∧
    cell 214 1=false ∧ cell 1981 1=true := by
  rw [obs_packed 214 (by decide) (by decide),obs_packed 1981 (by decide) (by decide),
    read_packed (t:=214) (p:=0) (by decide) (by decide),
    read_packed (t:=1981) (p:=0) (by decide) (by decide),
    read_packed (t:=214) (p:=1) (by decide) (by decide),
    read_packed (t:=1981) (p:=1) (by decide) (by decide)]
  decide +kernel

end Ruliology.CellularAutomata.Rule30MaskedForkRate
