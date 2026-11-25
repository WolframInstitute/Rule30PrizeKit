module

public import Ruliology.CellularAutomata.Rule30Certificates.HorizontalDiversityFive
public import Ruliology.CellularAutomata.Rule30CenterRuns

/-!
# Horizontal diversity at the center of Rule 30

For the singleton, let H(w) count the spatial words on sites 0,-1,...,-w over all ages.
A center of period P from T gives H(w) ≤ T + P floor(9(39/32)^w).
The five-cell certificate bounds the masked readings at every center phase. For
k = floor(w/39), the moving left edge forces at least w+k+1 words by age w+3k.
Growth sufficient for Problem 1 remains open. The original four-cell bound and
the earlier logarithmic surplus are also available at finite widths.
-/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30HorizontalDiversity
open Ruliology.CellularAutomata Rule30Jen Rule30MaskedJen Rule30Realization Ruliology.CellularAutomata.Rule30Certificates.HorizontalDiversity

theorem five_cell_count {T P : Nat} (hp : 0<P)
    (per : ∀ t, T≤t → cell (t+P) 0=cell t 0) (w : Nat) :
    H w ≤ T + P*(9*39^w/32^w) := by
  apply horizontal_count_of_channel (fun c => Rule30Certificates.HorizontalDiversityFive.words c 0)
    (budget:=fun n=>9*39^n/32^n) _ Rule30Certificates.HorizontalDiversityFive.observations_mem hp per w
  intro c
  exact (Nat.le_div_iff_mul_le (Nat.pow_pos (by decide : 0<32))).mpr
    (Rule30Certificates.HorizontalDiversityFive.masked_word_count c)

theorem problem1_of_five_cell_growth
    (growth : ∀ A : Nat, ∃ w, A*39^w < H w*32^w) : Rule30Prize.Problem1 := by
  rintro ⟨T,P,hp,per⟩
  obtain ⟨w,large⟩ := growth (T+9*P)
  have bound : H w*32^w ≤ (T+9*P)*39^w := by
    calc
      _ ≤ (T+P*(9*39^w/32^w))*32^w := Nat.mul_le_mul_right _ (five_cell_count hp per w)
      _ = T*32^w + P*((9*39^w/32^w)*32^w) := by rw [Nat.add_mul,Nat.mul_assoc]
      _ ≤ T*39^w + P*(9*39^w) := Nat.add_le_add
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by decide : 32≤39) w))
        (Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _))
      _ = _ := by rw [Nat.add_mul]; ac_rfl
  omega

/-- Pairwise distinct words sampled at finitely many ages can witness the five-cell criterion. -/
theorem problem1_of_five_cell_samples
    (samples : ∀ A : Nat, ∃ (w : Nat) (ages : List Nat), (ages.map (row w)).Nodup ∧
      A*39^w < ages.length*32^w) : Rule30Prize.Problem1 :=
  problem1_of_five_cell_growth ((growth_iff_samples 39 32).mpr samples)

end Ruliology.CellularAutomata.Rule30HorizontalDiversity

namespace Ruliology.CellularAutomata.Rule30HorizontalDiversity.Returns
open Ruliology.CellularAutomata Rule30Jen Rule30MaskedJen
open Ruliology.CellularAutomata.Rule30Certificates.HorizontalDiversity Ruliology.CellularAutomata.Rule30HorizontalDiversity

abbrev Tail := Nat → Bool

def push (b : Bool) (x : Tail) : Tail
  | 0 => rule b (x 0) (x 1)
  | n+1 => rule (x n) (x (n+1)) (x (n+2))

def drive : List Bool → Tail → Tail
  | [],x => x
  | b::bs,x => drive bs (push b x)

def Agree (n : Nat) (x y : Tail) : Prop := ∀ j, j<n → x j=y j

private theorem mono {n m : Nat} {x y : Tail} (h : Agree n x y) (hsmall : m≤n) : Agree m x y :=
  fun j hj => h j (by omega)

private theorem push_agree {m : Nat} {x y : Tail} (b : Bool) (h : Agree (m+1) x y) :
    Agree m (push b x) (push b y) := by
  intro j hj
  cases j with
  | zero => simp only [push,h 0 (by omega),h 1 (by omega)]
  | succ j => simp only [push,h j (by omega),h (j+1) (by omega),h (j+2) (by omega)]

private theorem drive_agree (c : List Bool) (m : Nat) {x y : Tail}
    (h : Agree (m+c.length) x y) : Agree m (drive c x) (drive c y) := by
  induction c generalizing x y with
  | nil => simpa [drive] using h
  | cons b bs ih =>
    apply ih
    apply push_agree
    simpa [Nat.add_assoc] using h

private theorem drive_append (a b : List Bool) (x : Tail) :
    drive (a++b) x=drive b (drive a x) := by
  induction a generalizing x with
  | nil => rfl
  | cons hd tl ih => exact ih _

private theorem front (a b : List Bool) {x y : Tail} (len : a.length=b.length) (j : Nat)
    (diff : x j≠y j) (right : ∀ p, j<p → x p=y p) :
    drive a x (j+a.length)≠drive b y (j+a.length) := by
  induction a generalizing b j x y with
  | nil => cases b with | nil => simpa [drive] using diff | cons _ _ => simp at len
  | cons hd tl ih =>
    cases b with
    | nil => simp at len
    | cons hd' tl' =>
      simp only [List.length_cons] at len ⊢
      rw [show j+(tl.length+1)=(j+1)+tl.length by omega]
      apply ih tl' (by omega) (j+1)
      · change rule (x j) (x (j+1)) (x (j+2))≠rule (y j) (y (j+1)) (y (j+2))
        simpa [rule,right (j+1) (by omega),right (j+2) (by omega)] using diff
      · intro p hp
        obtain ⟨q,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show p≠0 by omega)
        simp only [push,right q (by omega),right (q+1) (by omega),right (q+2) (by omega)]

/-- Given the initial eastern tail, the final n-bit prefix distinguishes all n-bit western inputs. -/
theorem drive_injective (a b : List Bool) (x : Tail) (len : a.length=b.length)
    (eq : Agree a.length (drive a x) (drive b x)) : a=b := by
  induction a generalizing b x with
  | nil => cases b with | nil => rfl | cons _ _ => simp at len
  | cons hd tl ih =>
    cases b with
    | nil => simp at len
    | cons hd' tl' =>
      simp only [List.length_cons] at len eq
      by_cases hh : hd=hd'
      · subst hd'
        exact congrArg (hd::·) (ih _ _ (by omega) (mono eq (by omega)))
      · exfalso
        have start : push hd x 0≠push hd' x 0 := by simpa [push,rule] using hh
        have split := front tl tl' (by omega) 0 start (by intro p hp;cases p with
          | zero => omega | succ p => rfl)
        exact split (by simpa [drive] using eq tl.length (by omega))

/-- Three observations with two equal subsequent returns force commutation of their drivers. -/
theorem commutation (A B : List Bool) (x : Tail) (n : Nat) (len : n=A.length+B.length)
    (h1 : Agree (2*n) x (drive A x)) (h2 : Agree (2*n) x (drive (A++B) x)) : A++B=B++A := by
  have afterB : Agree (n+A.length) (drive B x) x := by
    have m := drive_agree B (n+A.length) (x:=x) (y:=drive A x) (mono h1 (by omega))
    rw [←drive_append] at m
    intro j hj
    exact (m j hj).trans (h2 j (by omega)).symm
  apply drive_injective _ _ x (by simp [Nat.add_comm])
  rw [List.length_append,←len,drive_append B A]
  have m := drive_agree A n afterB
  intro j hj
  exact (h2 j (by omega)).symm.trans ((h1 j (by omega)).trans (m j hj).symm)

def east (i : Int) (t : Nat) : Tail := fun j => cell t (i+j)
def incoming (i : Int) (t n : Nat) := segment (fun u => cell u (i-1)) t n

private theorem seg_len (f : Nat→Bool) (t n : Nat) : (segment f t n).length=n := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih => simp [Ruliology.CellularAutomata.Rule30Certificates.HorizontalDiversity.segment,ih]

private theorem seg_append (f : Nat→Bool) (t m n : Nat) :
    segment f t (m+n)=segment f t m++segment f (t+m) n := by
  induction m generalizing t with
  | zero => simp [Ruliology.CellularAutomata.Rule30Certificates.HorizontalDiversity.segment]
  | succ m ih =>
    rw [show m+1+n=(m+n)+1 by omega,Rule30Certificates.HorizontalDiversity.segment,ih,Rule30Certificates.HorizontalDiversity.segment]
    simp only [List.cons_append,show t+1+m=t+(m+1) by omega]

private theorem driven (i : Int) (t n : Nat) : drive (incoming i t n) (east i t)=east i (t+n) := by
  have step (t : Nat) : push (cell t (i-1)) (east i t)=east i (t+1) := by
    funext j
    cases j with
    | zero => simp only [push,east,cell];congr 2 <;> omega
    | succ j =>
      simp only [push,east,cell]
      congr 2 <;> omega
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    change drive (incoming i (t+1) n) (push (cell t (i-1)) (east i t))= _
    rw [step,ih,show t+1+n=t+(n+1) by omega]

/-- Equal eastern snapshots on two return intervals force the first driver of length v
to equal the next driver's first v letters, up to its full observed length. -/
theorem shared_inputs (i : Int) (t u v : Nat)
    (e1 : Agree (2*(u+v)) (east i t) (east i (t+u)))
    (e2 : Agree (2*(u+v)) (east i t) (east i (t+u+v))) :
    incoming i t v=incoming i (t+u) v := by
  let A := incoming i t u
  let B := incoming i (t+u) v
  have aLen : A.length=u := seg_len _ _ _
  have bLen : B.length=v := seg_len _ _ _
  have eA : drive A (east i t)=east i (t+u) := driven _ _ _
  have eAB : drive (A++B) (east i t)=east i (t+u+v) := by rw [drive_append,eA,driven]
  have comm := commutation A B (east i t) (u+v) (by omega) (by rwa [eA]) (by rwa [eAB])
  have entire : incoming i t (u+v)=A++B := seg_append _ _ _ _
  have ev : incoming i t (u+v)=incoming i t v++incoming i (t+v) u := by
    rw [show u+v=v+u by omega];exact seg_append _ _ _ _
  have cut := congrArg (List.take v) (ev.symm.trans (entire.trans comm))
  simpa [incoming,seg_len,List.take_append,bLen,B,A] using cut

private theorem input_take (i : Int) (t n j : Nat) (hj : j≤n) :
    (incoming i t n).take j=incoming i t j := by
  rw [show n=j+(n-j) by omega]
  unfold incoming
  rw [seg_append,List.take_append,seg_len]
  simp [List.take_of_length_le,seg_len]

/-- At ages w+a, w+b, w+c, once c≥2b and the observed block reaches 2(c−a)
sites east from −w, all three windows cannot agree. -/
theorem three_snapshots (w a b c : Nat) (ab : a<b) (bc : b<c) (late : 2*b≤c)
    (room : 2*(c-a)≤w+1) (e1 : Agree (w+1) (east (-(w:Int)) (w+a)) (east (-(w:Int)) (w+b)))
    (e2 : Agree (w+1) (east (-(w:Int)) (w+a)) (east (-(w:Int)) (w+c))) : False := by
  let i := -(w:Int)
  let t := w+a
  let u := b-a
  let v := c-b
  have cu : t+u=w+b := by dsimp [t,u];omega
  have cv : t+u+v=w+c := by dsimp [t,u,v];omega
  have lim : 2*(u+v)≤w+1 := by dsimp [u,v];omega
  have once : Agree (w+1) (east i t) (east i (t+u)) := by rwa [cu]
  have eq := shared_inputs i t u v (mono once lim) (by rw [cv];exact mono e2 lim)
  have matchFuture (s : Nat) (hs : s≤b) : Agree 2 (east i (t+s)) (east i (t+u+s)) := by
    have short := congrArg (List.take s) eq
    rw [input_take i t v s (by dsimp [v];omega),input_take i (t+u) v s (by dsimp [v];omega)] at short
    rw [←driven,←driven i (t+u),←short]
    apply drive_agree
    apply mono once
    unfold incoming
    rw [seg_len]
    dsimp [u,v] at lim
    omega
  apply window_jen_col (t₁:=t) (t₂:=t+u) (i:=i) b (by dsimp [u];omega) (by dsimp [t,i,u];omega)
  · intro s hs
    simpa [east] using matchFuture s hs 0 (by omega)
  · intro s hs
    have a0 : cell (t+s) i=cell (t+u+s) i := by simpa [east] using matchFuture s (by omega) 0 (by omega)
    have a1 : cell (t+s) (i+1)=cell (t+u+s) (i+1) := by simpa [east] using matchFuture s (by omega) 1 (by omega)
    simp [orCol,a0,a1]

end Ruliology.CellularAutomata.Rule30HorizontalDiversity.Returns

namespace Ruliology.CellularAutomata.Rule30HorizontalDiversity.Lower
open Ruliology.CellularAutomata Rule30Jen Rule30Diagonals Rule30CenterRuns
open Ruliology.CellularAutomata.Rule30HorizontalDiversity Ruliology.CellularAutomata.Rule30HorizontalDiversity.Returns

private theorem least_witness {P : Nat → Prop} (h : ∃ n, P n) : ∃ n, P n ∧ ∀ m, m<n → ¬P m := by
  obtain ⟨n,hn⟩ := h
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases e : ∃ m, m<n ∧ P m
    · obtain ⟨m,hm,hp⟩ := e
      exact ih m hm hp
    · exact ⟨n,hn,fun m hm hp => e ⟨m,hm,hp⟩⟩

private theorem front_clock (i : Int) (a L : Nat) (white : ∀ t, a≤t → t<a+L → cell t i=false) :
    ∃ m, ∀ t, a≤t → t<a+L → cell t (i+1)=decide (a+m≤t) := by
  let P := fun m : Nat => m<L ∧ cell (a+m) (i+1)=true
  by_cases h : ∃ m, P m
  · obtain ⟨m,hit,minimal⟩ := least_witness h
    have up (s : Nat) (hs : a+m+s<a+L) : cell (a+m+s) (i+1)=true := by
      induction s with
      | zero => exact hit.2
      | succ s ih =>
        change rule (cell (a+m+s) (i+1-1)) (cell (a+m+s) (i+1)) _=true
        rw [show i+1-1=i by omega,white _ (by omega) (by omega),ih (by omega)];rfl
    refine ⟨m,?_⟩
    intro t ht last
    by_cases hm : a+m≤t
    · rw [decide_eq_true hm,←show a+m+(t-(a+m))=t by omega]
      exact up _ (by omega)
    · rw [decide_eq_false hm]
      apply Bool.eq_false_iff.mpr
      intro black
      apply minimal (t-a) (show t-a<m by omega)
      exact ⟨by omega,by simpa only [show a+(t-a)=t by omega] using black⟩
  · refine ⟨L,?_⟩
    intro t ht last
    rw [decide_eq_false (by omega)]
    apply Bool.eq_false_iff.mpr
    intro black
    exact h ⟨t-a,by omega,by simpa only [show a+(t-a)=t by omega] using black⟩

/-- The kit's zero-run reconstruction, translated to an arbitrary observing site. -/
private theorem triangle (i : Int) (a m L : Nat) (white : ∀ t, a≤t → t<a+L → cell t i=false)
    (clock : ∀ t, a≤t → t<a+L → cell t (i+1)=decide (a+m≤t)) :
    ∀ k t, a≤t → t+k<a+L → cell t (i-(k:Int))=preRow k (a+m-t)
  | 0,t,ht,last => by simp only [Int.natCast_zero,Int.sub_zero,white t ht (by omega)];rfl
  | k+1,t,ht,last => by
    have eq := cell_left t (i-(k:Int))
    rw [show i-(k:Int)-1=i-((k+1:Nat):Int) by omega,triangle i a m L white clock k (t+1) (by omega) (by omega),
      triangle i a m L white clock k t ht (by omega),show a+m-(t+1)=a+m-t-1 by omega] at eq
    rw [eq]
    cases k with
    | zero =>
      simp only [Int.natCast_zero,Int.sub_zero,clock t ht (by omega)]
      have z (m : Nat) : preRow 0 m=false := decide_eq_false (by omega)
      rw [z,z]
      by_cases p : a+m≤t
      · rw [decide_eq_true p,show preRow 1 (a+m-t)=true by apply decide_eq_true;omega];rfl
      · rw [decide_eq_false p,show preRow 1 (a+m-t)=false by apply decide_eq_false;omega];rfl
    | succ k =>
      rw [show i-((k+1:Nat):Int)+1=i-(k:Int) by omega,triangle i a m L white clock k t ht (by omega)]
      exact (preRow_step k (a+m-t)).symm

/-- At the site reached by the singleton's left edge at age w, a positive even relative
age a has a subsequent black observation no later than relative age 2a. -/
theorem black_window (w a : Nat) (ha : 0<a) (even : a%2=0) :
    ∃ t, a≤t ∧ t≤2*a ∧ cell (w+t) (-(w:Int))=true := by
  apply Classical.byContradiction
  intro missing
  have none (j : Nat) (hj : a≤j) (hj' : j≤2*a) (black : cell (w+j) (-(w:Int))=true) :=
    missing ⟨j,hj,hj',black⟩
  let i := -(w:Int)
  let t0 := w+a
  have white (t : Nat) (ht : t0≤t) (last : t<t0+(a+1)) : cell t i=false := by
    have e : t=w+(t-w) := by dsimp [t0] at ht;omega
    rw [e]
    exact Bool.eq_false_iff.mpr (none (t-w) (by dsimp [t0] at ht;omega) (by dsimp [t0] at last;omega))
  obtain ⟨m,hm⟩ := front_clock i t0 (a+1) white
  have rowAt (j : Nat) (hj : j≤a) : cell t0 (i-(j:Int))=preRow j m := by
    simpa only [show t0+m-t0=m by omega] using triangle i t0 m (a+1) white hm j t0 (by omega) (by omega)
  have p := rowAt a (by omega)
  rw [show i-(a:Int)=-(t0:Int) by dsimp [i,t0];omega,cell_left_edge] at p
  have q := rowAt (a-1) (by omega)
  have positive : 0<t0 := by dsimp [t0];omega
  have edgeBlack : cell t0 (i-((a-1:Nat):Int))=true := by
    have border := D_one (t0-1)
    rw [show t0-1+1=t0 by omega,D] at border
    change cell t0 ((1:Int)-(t0:Int))=true at border
    simpa only [show i-((a-1:Nat):Int)=(1:Int)-(t0:Int) by dsimp [i,t0];omega] using border
  rw [edgeBlack] at q
  have hp := preRow_eq_true p.symm
  have hq := preRow_eq_true q.symm
  omega

private theorem east_row (w a b : Nat) (h : row w a=row w b) :
    Agree (w+1) (east (-(w:Int)) a) (east (-(w:Int)) b) := by
  intro j hj
  have allCells : ∀ q, q≤w → cell a (-(q:Int))=cell b (-(q:Int)) := by
    have e : ∀ q, q<w+1 → cell a (-(q:Int))=cell b (-(q:Int)) := by
      simpa [row,List.map_inj_left] using h
    exact fun q hq => e q (by omega)
  have eq := allCells (w-j) (by omega)
  simpa [east,show -(w:Int)+(j:Int)=-((w-j:Nat):Int) by omega] using eq

private theorem westernBit (w a b : Nat) (h : row w a=row w b) :
    cell a (-(w:Int))=cell b (-(w:Int)) := by simpa [east] using east_row w a b h 0 (by omega)

private theorem seedWord_inj {w a b : Nat} (aa : a<w) (bb : b<w) (h : row w a=row w b) : a=b := by
  have allCells : ∀ q, q≤w → cell a (-(q:Int))=cell b (-(q:Int)) := by
    have e : ∀ q, q<w+1 → cell a (-(q:Int))=cell b (-(q:Int)) := by
      simpa [row,List.map_inj_left] using h
    exact fun q hq => e q (by omega)
  rcases Nat.lt_trichotomy a b with ab|ab|ab
  · have z := allCells b (by omega)
    rw [cell_eq_false_of_lt a _ (by omega),cell_left_edge] at z
    cases z
  · exact ab
  · have z := allCells a (by omega)
    rw [cell_left_edge,cell_eq_false_of_lt b _ (by omega)] at z
    cases z

private theorem split_length {α : Type} (p : α → Bool) (xs : List α) :
    (xs.filter p).length+(xs.filter (fun x => !(p x))).length=xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases h : p a <;> simp [h,List.filter] <;> omega

/-- A finite cover has size at least half that of a list whose fibers have size at most two. -/
private theorem bounded_fibers (f : Nat → List Bool) (xs : List Nat) (ys : List (List Bool))
    (cover : ∀ j ∈ xs, f j ∈ ys)
    (cap : ∀ v, (xs.filter (fun j => f j == v)).length≤2) : xs.length≤2*ys.length := by
  induction ys generalizing xs with
  | nil =>
    cases xs with
    | nil => simp
    | cons j js => cases cover j (by simp)
  | cons v vs ih =>
    let rest := xs.filter (fun j => !(f j == v))
    have cov (j : Nat) (hj : j∈rest) : f j∈vs := by
      obtain ⟨hin,out⟩ := List.mem_filter.mp hj
      have hv := cover j hin
      have neq : f j≠v := by simpa using out
      exact (List.mem_cons.mp hv).resolve_left neq
    have few (u : List Bool) : (rest.filter (fun j => f j == u)).length≤2 :=
      Nat.le_trans (List.Sublist.filter _ (List.filter_sublist (l:=xs))).length_le (cap u)
    have small := ih rest cov few
    have parts := split_length (fun j => f j == v) xs
    have c := cap v
    change xs.length≤2*(vs.length+1)
    dsimp [rest] at small
    omega

private theorem three_indices {xs : List Nat} (ord : xs.Pairwise (· < ·)) (size : 2<xs.length) :
    ∃ i∈xs, ∃ j∈xs, ∃ k∈xs, i<j ∧ j<k := by
  cases xs with
  | nil => simp at size
  | cons i tail => cases tail with
    | nil => simp at size
    | cons j tail => cases tail with
      | nil => simp at size
      | cons k more =>
        have a := List.pairwise_cons.mp ord
        have b := List.pairwise_cons.mp a.2
        exact ⟨i,by simp,j,by simp,k,by simp,a.1 j (by simp),b.1 k (by simp)⟩

/-- Retain one copy of each observed bit word. -/
def distinct : List (List Bool) → List (List Bool)
  | [] => []
  | v::vs => if v∈vs then distinct vs else v::distinct vs

private theorem mem_distinct (u : List Bool) (vs : List (List Bool)) : u∈distinct vs ↔ u∈vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    by_cases h : v∈vs
    · rw [distinct,ite_eq_left h,ih,List.mem_cons]
      exact ⟨Or.inr,fun e => e.elim (fun eq => eq ▸ h) id⟩
    · simp [distinct,h,ih]

private theorem distinct_nodup (vs : List (List Bool)) : (distinct vs).Nodup := by
  induction vs with
  | nil => simp [distinct]
  | cons v vs ih =>
    by_cases h : v∈vs
    · simpa [distinct,h] using ih
    · simp [distinct,h,List.nodup_cons,mem_distinct,ih]

/-- All distinct horizontal words observed at ages below N. -/
def seenBefore (w N : Nat) := distinct ((List.range N).map (row w))

private theorem mem_seen {w N : Nat} {v : List Bool} : v∈seenBefore w N ↔ ∃ t, t<N ∧ row w t=v := by
  simp [seenBefore,mem_distinct]

private theorem seen_nodup (w N : Nat) : (seenBefore w N).Nodup := distinct_nodup _

/-- Every sufficiently wide window realizes the claimed number of words by the explicit deadline. -/
theorem finite_vocabulary_lower (w r : Nat) (room : 2*16^r≤w+1) :
    w+r+1≤(seenBefore w (w+16^r+1)).length := by
  classical
  have pick (j : Nat) : ∃ t, 2*4^j≤t ∧ t≤4^(j+1) ∧ cell (w+t) (-(w:Int))=true := by
    obtain ⟨t,h1,h2,cellIsBlack⟩ := black_window w (2*4^j) (by have := Nat.pow_pos (n:=j) (by decide : 0<4);omega) (by omega)
    refine ⟨t,h1,?_,cellIsBlack⟩
    rw [Nat.pow_succ];omega
  let f := fun j => Classical.choose (pick j)
  have fsmall (j : Nat) : 2*4^j≤f j := (Classical.choose_spec (pick j)).1
  have fbig (j : Nat) : f j≤4^(j+1) := (Classical.choose_spec (pick j)).2.1
  have fblack (j : Nat) : cell (w+f j) (-(w:Int))=true := (Classical.choose_spec (pick j)).2.2
  have pos (j : Nat) : 0<f j := by
    have hh := fsmall j
    have pp : 0<(4:Nat)^j := Nat.pow_pos (by decide)
    omega
  have spread {i j : Nat} (h : i<j) : 2*f i ≤ f j := by
    have pp : 4^(i+1)≤4^j := Nat.pow_le_pow_right (by decide) h
    have lo := fsmall j
    have hi := fbig i
    omega
  have maxF {j : Nat} (hj : j<2*r) : f j≤16^r := by
    calc
      _ ≤ 4^(j+1) := fbig _
      _ ≤ 4^(2*r) := Nat.pow_le_pow_right (by decide) hj
      _ = 16^r := by rw [Nat.pow_mul]
  let age : Nat → Nat
    | 0 => 0
    | j+1 => f j
  have blackAge (j : Nat) : cell (w+age j) (-(w:Int))=true := by
    cases j with
    | zero => simpa [age] using cell_left_edge w
    | succ j => exact fblack j
  have strict {i j : Nat} (h : i<j) : age i<age j := by
    cases i with
    | zero => cases j with | zero => omega | succ j => exact pos j
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        change f i<f j
        have g := spread (show i<j by omega)
        have p := pos i
        omega
  have laterAge {i j : Nat} (h : i<j) : 2*age i≤age j := by
    cases i with
    | zero => simp [age]
    | succ i => cases j with | zero => omega | succ j => exact spread (by omega)
  have ageCap {j : Nat} (h : j<2*r+1) : age j≤16^r := by
    cases j with | zero => exact Nat.zero_le _ | succ j => exact maxF (by omega)
  let sample := fun j => row w (w+age j)
  let N := w+16^r+1
  let idx := List.range (2*r+1)
  let seen := seenBefore w N
  let extra := seen.filter (fun v => (idx.map sample).contains v)
  have member {j : Nat} (hj : j∈idx) : sample j ∈ seen := by
    apply mem_seen.mpr
    have bound := ageCap (List.mem_range.mp hj)
    exact ⟨w+age j,by dsimp [N];omega,rfl⟩
  have covers (j : Nat) (hj : j∈idx) : sample j∈extra :=
    List.mem_filter.mpr ⟨member hj,List.contains_iff_mem.mpr (List.mem_map.mpr ⟨j,hj,rfl⟩)⟩
  have cap (v : List Bool) : (idx.filter (fun j => sample j == v)).length≤2 := by
    apply Nat.le_of_not_lt
    intro big
    obtain ⟨i,hi,j,hj,k,hk,ij,jk⟩ := three_indices (List.Pairwise.filter _ List.pairwise_lt_range) big
    obtain ⟨_,e1⟩ := List.mem_filter.mp hi
    obtain ⟨_,e2⟩ := List.mem_filter.mp hj
    obtain ⟨hk',e3⟩ := List.mem_filter.mp hk
    have e1' := eq_of_beq e1
    have e2' := eq_of_beq e2
    have e3' := eq_of_beq e3
    have small := ageCap (List.mem_range.mp hk')
    exact three_snapshots w (age i) (age j) (age k) (strict ij) (strict jk) (laterAge jk) (by omega)
      (east_row w _ _ (e1'.trans e2'.symm)) (east_row w _ _ (e1'.trans e3'.symm))
  have extraCount := bounded_fibers sample idx extra covers cap
  have lenIdx : idx.length=2*r+1 := List.length_range
  let early := (List.range w).map (row w)
  have earlyNodup : early.Nodup := nodup_map_of_inj (row w) List.nodup_range
    (fun a ha b hb h => seedWord_inj (List.mem_range.mp ha) (List.mem_range.mp hb) h)
  have extraNodup : extra.Nodup := List.Pairwise.filter _ (seen_nodup _ _)
  have distinct : (early++extra).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨earlyNodup,extraNodup,?_⟩
    rintro v hv u hu same
    obtain ⟨a,ha,eq⟩ := List.mem_map.mp hv
    obtain ⟨_,hu'⟩ := List.mem_filter.mp hu
    obtain ⟨j,hj,eq'⟩ := List.mem_map.mp (List.contains_iff_mem.mp hu')
    have contradiction := westernBit w _ _ (eq'.trans (same.symm.trans eq.symm))
    rw [blackAge j,cell_eq_false_of_lt a _ (by have := List.mem_range.mp ha;omega)] at contradiction
    contradiction
  have sub (v : List Bool) (hv : v∈early++extra) : v∈seen := by
    rcases List.mem_append.mp hv with he | hx
    · obtain ⟨a,ha,eq⟩ := List.mem_map.mp he
      exact mem_seen.mpr ⟨a,by dsimp [N];have := List.mem_range.mp ha;omega,eq⟩
    · exact (List.mem_filter.mp hx).1
  have count := Rule30Jen.length_le_of_subset distinct sub
  rw [List.length_append,show early.length=w by simp [early]] at count
  change w+r+1≤seen.length
  omega

/-- All-age vocabulary bound on the same observable as the conditional upper estimate. -/
theorem vocabulary_lower (w r : Nat) (room : 2*16^r≤w+1) : w+r+1≤H w := by
  apply Nat.le_trans (finite_vocabulary_lower w r room)
  apply Rule30Jen.length_le_of_subset (seen_nodup _ _)
  intro v hv
  obtain ⟨t,_,eq⟩ := mem_seen.mp hv
  exact mem_language.mpr ⟨t,eq⟩

private theorem lookup {w a b : Nat} (h : row w a=row w b) {i : Int}
    (left : -(w:Int) ≤ i) (right : i ≤ 0) : cell a i=cell b i := by
  have eq : ∀ j, j≤w → cell a (-(j:Int))=cell b (-(j:Int)) := by
    have allCells : ∀ j, j<w+1 → cell a (-(j:Int))=cell b (-(j:Int)) := by
      simpa [row,List.map_inj_left] using h
    exact fun j hj => allCells j (by omega)
  have index : -(((-i).toNat:Nat):Int)=i := by omega
  simpa only [index] using eq (-i).toNat (by omega)

private theorem interior {w a b : Nat} (h : row w a=row w b) (d : Nat) {i : Int}
    (left : -(w:Int)+d ≤ i) (right : i ≤ -(d:Int)) : cell (a+d) i=cell (b+d) i := by
  induction d generalizing i with
  | zero => simpa using lookup h (by omega : -(w:Int)≤ i) (by omega)
  | succ d ih =>
    change rule (cell (a+d) (i-1)) (cell (a+d) i) (cell (a+d) (i+1))=_
    rw [ih (i:=i-1) (by omega) (by omega),ih (i:=i) (by omega) (by omega),
      ih (i:=i+1) (by omega) (by omega)]
    rfl

/-- Either read the row itself, or its pointwise disagreement with the row p ticks later. -/
def probe (lag : Option Nat) (s : Nat) (i : Int) : Bool :=
  match lag with
  | none => cell s i
  | some p => xor (cell s i) (cell (s+p) i)

def radius (lag : Option Nat) : Nat := lag.getD 0

private theorem detect {w a b : Nat} (h : row w a=row w b) (lag : Option Nat) {i : Int}
    (west : -(w:Int)+radius lag ≤ i) (east : i≤ -(radius lag:Int)) :
    probe lag a i = probe lag b i := by
  cases lag with
  | none => exact lookup h (by simpa [radius] using west) (by simpa [radius] using east)
  | some p =>
    simp [radius] at west east
    simp only [probe,interior h p (by omega : -(w:Int)+p≤ i) east,lookup h (by omega : -(w:Int)≤ i) (by omega : i≤0)]

private theorem supported {lag t i} (hit : probe lag t i=true) : -(t+radius lag : Nat)≤ i := by
  apply Int.le_of_not_gt
  intro left
  cases lag with
  | none => simp [radius] at left; simp [probe,cell_eq_false_of_lt _ _ left] at hit
  | some p =>
    simp only [radius,Option.getD_some] at left
    simp [probe,cell_eq_false_of_lt _ _ left,cell_eq_false_of_lt t i (by omega)] at hit

def Front (lag : Option Nat) (t : Nat) (q r : Int) : Prop :=
  probe lag t q=true ∧ ∀ i, q < i → i ≤ r → probe lag t i=false

private theorem advance {lag t q r} (h : Front lag t q r) (room : q+2≤r) :
    Front lag (t+1) (q+1) (r-1) := by
  cases lag with
  | none =>
    obtain ⟨hq,after⟩ := h
    change cell t q=true at hq
    change ∀ i,q < i → i≤r → cell t i=false at after
    constructor
    · change rule (cell t (q+1-1)) (cell t (q+1)) (cell t (q+1+1))=true
      rw [show q+1-1=q by omega,hq,after _ (by omega) (by omega),after _ (by omega) (by omega)]
      rfl
    · intro i lo hi
      change rule (cell t (i-1)) (cell t i) (cell t (i+1))=false
      rw [after _ (by omega) (by omega),after _ (by omega) (by omega),after _ (by omega) (by omega)]
      rfl
  | some p =>
    obtain ⟨hq,after⟩ := h
    simp [probe] at hq after
    have xt (a b : Bool) : xor a b = true ↔ a ≠ b := by cases a <;> cases b <;> decide
    have xf (a b : Bool) : xor a b = false ↔ a = b := by cases a <;> cases b <;> decide
    have next : t+1+p=t+p+1 := by omega
    constructor
    · simp only [probe,next,xt]
      change rule (cell t (q+1-1)) (cell t (q+1)) (cell t (q+1+1)) ≠
        rule (cell (t+p) (q+1-1)) (cell (t+p) (q+1)) (cell (t+p) (q+1+1))
      rw [show q+1-1=q by omega,after (q+1) (by omega) (by omega),after (q+1+1) (by omega) (by omega)]
      simpa [rule] using hq
    · intro i lo hi
      simp only [probe,next,xf]
      change rule (cell t (i-1)) (cell t i) (cell t (i+1)) =
        rule (cell (t+p) (i-1)) (cell (t+p) i) (cell (t+p) (i+1))
      rw [after _ (by omega) (by omega),after _ (by omega) (by omega),after _ (by omega) (by omega)]

theorem propagate {lag t q r} (h : Front lag t q r) (d : Nat) (room : q+2*(d:Int)≤r) :
    Front lag (t+d) (q+d) (r-d) := by
  induction d with
  | zero => simpa using h
  | succ d ih =>
    have step := advance (ih (by omega)) (by omega)
    simpa only [Nat.add_assoc, Int.natCast_succ, Int.add_assoc, Int.sub_sub] using step

/-- A front moved inside the window is visible in that snapshot for p steps.
A copy at an earlier age either contradicts the already moving front, or
creates a second front which reaches its initially blank interval. -/
theorem first_visit {w : Nat} {lag t q r} (base : Front lag t q r) (h : Nat)
    (room : q+2*(h:Int)≤r) (left : -(w:Int)+radius lag≤q+h)
    (east : q+h≤ -(radius lag:Int))
    (margin : q+h+2*(t+radius lag+(q+h))≤min (r-h) (-(radius lag:Int)))
    (positive : 0<h) :
    ∀ z<t+h, row w z ≠ row w (t+h) := by
  intro z hz same
  let f := q+(h:Int)
  have fh := propagate base h room
  have copied : Front lag z f (min (r-h) (-(radius lag:Int))) := by
    constructor
    · exact (detect same lag left east).trans fh.1
    · intro i lo hi
      rw [detect same lag (by dsimp [f] at lo;omega) (by omega)]
      exact fh.2 i lo (by omega)
  by_cases after : t≤z
  · have earlier := propagate base (z-t) (by omega)
    rw [Nat.add_sub_of_le after] at earlier
    have miss := earlier.2 f (by dsimp [f];omega) (by dsimp [f];omega)
    exact Bool.noConfusion (copied.1.symm.trans miss)
  · have bound := supported copied.1
    have again := propagate copied (t-z) (by dsimp [f] at *;omega)
    rw [Nat.add_sub_of_le (by omega : z≤t)] at again
    have miss := base.2 (f+(t-z:Nat)) (by dsimp [f];omega) (by dsimp [f] at *;omega)
    exact Bool.noConfusion (again.1.symm.trans miss)

/-- Locate the last marked cell west of the window if the left edge is
marked and all cells from the window boundary to r are unmarked. -/
private theorem locate {lag t w b r}
    (edge : probe lag t (-((w+b:Nat):Int))=true)
    (blank : ∀ i, -(w:Int)≤ i → i≤r → probe lag t i=false) (covers : -(w:Int)≤r) :
    ∃ q : Int, -((w+b:Nat):Int)≤q ∧ q< -(w:Int) ∧ Front lag t q r := by
  let yes (j : Nat) := w≤j ∧ probe lag t (-(j:Int))=true
  have existsYes : ∃ j, yes j := ⟨w+b,by dsimp [yes];exact ⟨by omega,edge⟩⟩
  obtain ⟨j,hit,minimal⟩ := least_witness existsYes
  have small : j≤w+b := by
    apply Nat.le_of_not_lt
    intro h
    exact minimal (w+b) h ⟨by omega,edge⟩
  have gt : w<j := by
    have ge := hit.1
    apply Nat.lt_of_not_ge
    intro no
    have eq : j=w := by omega
    have clear := blank (-(w:Int)) (Int.le_refl _) covers
    exact Bool.noConfusion (hit.2.symm.trans (by simpa [eq] using clear))
  refine ⟨-(j:Int),by omega,by omega,hit.2,?_⟩
  intro i lo hi
  by_cases hs : -(w:Int)≤ i
  · exact blank _ hs hi
  · have bound : (-i).toNat<j := by omega
    have nm : ¬yes (-i).toNat := minimal _ bound
    have eq : -(((-i).toNat:Nat):Int)=i := by omega
    apply Bool.eq_false_iff.mpr
    intro h
    exact nm ⟨by omega,by simpa only [eq] using h⟩

/-- Measuring the exact offset of the front leaves k+1 first visits before
age w+3k as soon as w≥39k. -/
theorem fresh_after_return {w k s b : Nat} (hk : 0<k) (space : 39*k≤w)
    (entry : b≤k) (order : s<w+b) (same : row w s=row w (w+b)) :
    ∃ start, w≤start ∧ start+k≤w+3*k ∧
      ∀ h≤k, ∀ z<start+h, row w z≠row w (start+h) := by
  let p := w+b-s
  have back : s+p=w+b := by dsimp [p];omega
  by_cases tiny : p≤8*k
  · have edge : probe (some p) s (-((w+b:Nat):Int))=true := by
      have left : -((w+b:Nat):Int) < -(s:Int) := by omega
      simp only [probe,back,cell_left_edge,cell_eq_false_of_lt s _ left]
      decide
    have blank (i : Int) (lo : -(w:Int)≤ i) (hi : i≤0) : probe (some p) s i=false := by
      simp [probe,back,lookup same lo hi]
    obtain ⟨q,lo,hi,base⟩ := locate edge blank (by omega)
    let j := (-(w:Int)-q).toNat
    have jq : q= -(w:Int)-(j:Int) := by dsimp [j];omega
    have jb : j ≤ b := by omega
    have pos : 0 < j := by omega
    refine ⟨w+b+j,by omega,by omega,?_⟩
    intro x hx z hz
    have run := first_visit (w:=w) base (j+p+x) (by omega) (by simp [radius];omega)
      (by simp [radius];omega) (by simp [radius];omega) (by omega)
    have clock : s+(j+p+x) = w+b+j+x := by omega
    rw [clock] at run
    exact run z hz
  · have edge : probe none (w+b) (-((w+b:Nat):Int))=true := cell_left_edge _
    have blank (i : Int) (lo : -(w:Int)≤ i) (hi : i≤ -(s:Int)-1) :
        probe none (w+b) i=false := by
      rw [probe,←lookup same lo (by omega)]
      exact cell_eq_false_of_lt s _ (by omega)
    obtain ⟨q,lo,hi,base⟩ := locate edge blank (by dsimp [p] at tiny;omega)
    let j := (-(w:Int)-q).toNat
    have jq : q= -(w:Int)-(j:Int) := by dsimp [j];omega
    have jb : j ≤ b := by omega
    have pos : 0 < j := by omega
    refine ⟨w+b+j,by omega,by omega,?_⟩
    intro x hx z hz
    have run := first_visit (w:=w) base (j+x) (by omega) (by simp [radius];omega)
      (by simp [radius];omega) (by simp [radius];omega) (by omega)
    simpa only [Nat.add_assoc] using run z (by omega)

private theorem earlyFresh {w n : Nat} (before : n≤w) :
    ∀ z<n, row w z ≠ row w n := by
  intro z hz eq
  have differs := lookup eq (i:=-(n:Int)) (by omega) (by omega)
  rw [cell_eq_false_of_lt z _ (by omega),cell_left_edge] at differs
  contradiction

/-- Consecutive first visits shortly after the left edge crosses the window. -/
theorem fresh_block {w k : Nat} (space : 39*k≤w) :
    ∃ start, w≤start ∧ start+k≤w+3*k ∧
      ∀ h≤k, ∀ z<start+h, row w z≠row w (start+h) := by
  by_cases zero : k=0
  · subst k
    refine ⟨w,Nat.le_refl _,by omega,?_⟩
    intro h hh
    have eq : h=0 := by omega
    simpa [eq] using earlyFresh (w:=w) (n:=w) (Nat.le_refl _)
  by_cases repeated : ∃ b, b≤k ∧ ∃ s, s<w+b ∧ row w s=row w (w+b)
  · obtain ⟨b,hb,s,hs,eq⟩ := repeated
    exact fresh_after_return (by omega) space hb hs eq
  · exact ⟨w,Nat.le_refl _,by omega,fun b hb s hs eq => repeated ⟨b,hb,s,hs,eq⟩⟩

/-- The inclusive deadline w+3k is represented by the exclusive length w+3k+1. -/
theorem finite_first_visit_bound (w k : Nat) (space : 39*k≤w) :
    w+k+1 ≤ (seenBefore w (w+3*k+1)).length := by
  obtain ⟨start,after,cap,fresh⟩ := fresh_block space
  let age (i : Nat) := if i<w then i else start+(i-w)
  have newAt {i : Nat} (hi : i<w+k+1) :
      ∀ z<age i, row w z≠row w (age i) := by
    by_cases h : i<w
    · simpa [age,h] using earlyFresh (w:=w) (n:=i) (by omega)
    · simpa [age,h] using fresh (i-w) (by omega)
  have inc {i j : Nat} (lt : i<j) : age i<age j := by
    dsimp [age]; split <;> split <;> omega
  let sample := (List.range (w+k+1)).map (fun i => row w (age i))
  have nodup : sample.Nodup := by
    apply nodup_map_of_inj _ List.nodup_range
    intro i hi j hj eq
    by_cases lt : i<j
    · exact False.elim (newAt (List.mem_range.mp hj) _ (inc lt) eq)
    by_cases gt : j < i
    · exact False.elim (newAt (List.mem_range.mp hi) _ (inc gt) eq.symm)
    omega
  have sub (v : List Bool) (hv : v∈sample) : v∈seenBefore w (w+3*k+1) := by
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hv
    have bound := List.mem_range.mp hi
    exact mem_seen.mpr ⟨age i,by dsimp [age]; split <;> omega,rfl⟩
  simpa [sample] using Rule30Jen.length_le_of_subset nodup sub

theorem linear_vocabulary_lower (w : Nat) : w+w/39+1 ≤ H w := by
  apply Nat.le_trans (finite_first_visit_bound w (w/39) (by omega))
  apply Rule30Jen.length_le_of_subset (seen_nodup _ _)
  intro v hv
  obtain ⟨t,_,eq⟩ := mem_seen.mp hv
  exact mem_language.mpr ⟨t,eq⟩

end Ruliology.CellularAutomata.Rule30HorizontalDiversity.Lower

namespace Ruliology.CellularAutomata.Rule30HorizontalDiversity
open Ruliology.CellularAutomata.Rule30Certificates.HorizontalDiversity
open Ruliology.CellularAutomata Rule30Jen Rule30Realization

/-- The first w+16^r+1 sampled ages give this lower bound without a periodicity assumption. -/
theorem finite_vocabulary_lower (w r : Nat) (room : 2*16^r≤w+1) :
    w+r+1 ≤ (Lower.seenBefore w (w+16^r+1)).length := Lower.finite_vocabulary_lower w r room

/-- The same lower bound on all ages. -/
theorem vocabulary_lower (w r : Nat) (room : 2*16^r≤w+1) : w+r+1≤H w :=
  Lower.vocabulary_lower w r room

/-- One list bounds the masked histories for all rows and ages sharing this center word. -/
theorem five_cell_mask_bound (c : List Bool) :
    ∃ candidates : List (List Bool), candidates.length * 32^c.length ≤ 9 * 39^c.length ∧
      ∀ (x : Int → Bool) (t : Nat), segment (fun k => evol x k 0) t c.length = c →
        segment (fun k => evol x k 0 || evol x k 1) t c.length ∈ candidates :=
  Rule30Certificates.HorizontalDiversityFive.genuine_channel_bound c

theorem finite_first_visit_bound (w k : Nat) (space : 39*k≤w) :
    w+k+1 ≤ (Lower.seenBefore w (w+3*k+1)).length := Lower.finite_first_visit_bound w k space

theorem linear_vocabulary_lower (w : Nat) : w+w/39+1 ≤ H w := Lower.linear_vocabulary_lower w

end Ruliology.CellularAutomata.Rule30HorizontalDiversity
