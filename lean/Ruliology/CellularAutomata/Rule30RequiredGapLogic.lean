module

public import Init.Data.List.OfFn
public import Init.Data.List.Perm
public import Ruliology.CellularAutomata.Rule30DrivenLeft
public import Ruliology.CellularAutomata.Rule30FastImage
public import Ruliology.CellularAutomata.Rule30FiniteStrips
public import Ruliology.CellularAutomata.Rule30MaskedJen
public import Ruliology.CellularAutomata.Rule30Prize
public import Ruliology.CellularAutomata.Rule30ResetMixtures
public import Ruliology.CellularAutomata.Rule30StripCertificates

/-!
Open-boundary strip and periodic-word lemmas for the compulsory (12, 10, 9) factor.
-/

@[expose] public section

-- Keep independent kernel checks sequential so their peak allocations do not overlap.
set_option Elab.async false


section
namespace Ruliology.CellularAutomata.Rule30RequiredGapLogic.RunFamilies
open Rule30Jen Rule30Realization Rule30StripCertificates Rule30ResetMixtures
abbrev Pred := Nat→Prop
def Driven (x:Int→Bool) (j:Int) (s:Nat) (w:List Bool) := ∀i,i<w.length→evol x (s+i) j=w.getD i false
def Tr (x:Int→Bool) (j:Int) (u v:Pred) (w:List Bool) := ∀s,u s→Driven x j s w→v (s+w.length)
def row (W:Nat) (x:Int→Bool) (j:Int) (s:Nat) := Rule30FiniteStrips.encRow x s j W
def atSet (W:Nat) (x:Int→Bool) (j:Int) (S:Nat) : Pred := fun s=>S.testBit (row W x j s)=true
abbrev low (x:Int→Bool) (j:Int) (S:Nat) := atSet 8 x j S
theorem seq {x j a b c u v} (l:Tr x j a b u) (r:Tr x j b c v) : Tr x j a c (u++v) := by
  intro s h drv
  have fst:Driven x j s u:=by intro i hi;simpa [List.getD_eq_getElem?_getD,List.getElem?_append_left,hi] using drv i (by simp;omega)
  have snd:Driven x j (s+u.length) v:=by intro i hi;simpa [List.getD_eq_getElem?_getD,List.getElem?_append_right,Nat.add_assoc] using drv (u.length+i) (by simp;omega)
  simpa only [List.length_append,Nat.add_assoc] using r _ (l s h fst) snd

private theorem enc_eq {x:Int→Bool} {W t r:Nat} {j:Int} (enc:Rule30FiniteStrips.Enc x W t j r) : row W x j t=r := by
  apply Nat.eq_of_testBit_eq;intro i;have e:=Rule30FiniteStrips.enc_encRow (x:=x) W t j
  by_cases h:i<W
  · exact (e.2 i h).trans (enc.2 i h).symm
  · have le:=Nat.pow_le_pow_right (by decide : 0<2) (show W≤i by omega)
    exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le e.1 le)).trans (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le enc.1 le)).symm

theorem set_move {x j W a b w} (sub:Rule30WhitePad10111.Sub (applyWord W w a) b) :
    Tr x j (atSet W x j a) (atSet W x j b) w := by
  intro s h drv;obtain ⟨r,enc,present⟩:=Rule30FiniteStrips.enc_applyWord w s _ a (Rule30FiniteStrips.enc_encRow (x:=x) W s j) h drv
  change b.testBit (row W x j (s+w.length))=true;rw [enc_eq enc];exact sub _ present

theorem projection (x:Int→Bool) (j:Int) (s W k:Nat) (le:k≤W) : row k x j s=row W x j s%2^k := by
  apply Nat.eq_of_testBit_eq;intro i;unfold row;rw [Nat.testBit_mod_two_pow,Rule30FiniteStrips.testBit_encRow,Rule30FiniteStrips.testBit_encRow]
  by_cases h:i<k
  · simp [h,show i<W by omega]
  · simp [h]

theorem actual_step (W:Nat) (x:Int→Bool) (j:Int) (s:Nat) :
    ∃z,row W x j (s+1)=stripStep W (evol x s j) z (row W x j s) :=
  ⟨evol x s (j+1+W),enc_eq (Rule30FiniteStrips.enc_step (Rule30FiniteStrips.enc_encRow (x:=x) W s j))⟩

/-- Local certificate interface: assign a predicate on W-bit rows to each tick of the gap,
and check both extreme exterior inputs from every retained row. A sparse support is enough. -/
theorem frame_route (W q:Nat) (layer:Nat→Pred)
    (advance:∀i,i<q+1→∀r,r<2^W→layer i r→∀z,layer (i+1) (stripStep W (decide (i=0)) z r)) (x:Int→Bool) (j:Int) :
    Tr x j (fun s=>layer 0 (row W x j s)) (fun s=>layer (q+1) (row W x j s)) (driver q) := by
  intro s ini drv
  have visit (i:Nat) (hi:i≤q+1) : layer i (row W x j (s+i)) :=by
    induction i with
    |zero=>exact ini
    |succ i ih=>
      obtain ⟨z,edge⟩:=actual_step W x j (s+i)
      have clock:=drv i (by rw [driver_length];omega)
      have bit:(driver q).getD i false=decide (i=0):=by
        cases i with
        |zero=>rfl
        |succ i=>simp [driver,List.getD_eq_getElem?_getD,show i<q by omega]
      rw [clock,bit] at edge;rw [show s+(i+1)=(s+i)+1 by omega,edge]
      exact advance i (by omega) _ (Rule30FiniteStrips.enc_encRow (x:=x) W (s+i) j).1 (ih (by omega)) z
  rw [driver_length];exact visit _ (by omega)

theorem keepG (x:Int→Bool) (j:Int) {q:Nat} (hq:9≤q) : Tr x j (low x j G) (low x j G) (driver q) :=
  set_move (by rw [←mac_eq];exact stageG hq)

/-- Surviving rows may be stored with the already-absorbed rows removed at each pulse. -/
theorem with_G {x j} {u v:Pred} {q:Nat} (hq:9≤q) (go:Tr x j u (fun s=>low x j G s ∨ v s) (driver q)) :
    Tr x j (fun s=>low x j G s ∨ u s) (fun s=>low x j G s ∨ v s) (driver q) := by
  intro s h d;rcases h with a|b
  · exact Or.inl (keepG x j hq s a d)
  · exact go s b d
end Ruliology.CellularAutomata.Rule30RequiredGapLogic.RunFamilies

end

section
namespace Ruliology.CellularAutomata.Rule30RequiredGapLogic.StripInclusion
open Ruliology.CellularAutomata Ruliology.CellularAutomata.Rule30RequiredGapLogic.RunFamilies Rule30StripCertificates Rule30FastImage Rule30ResetMixtures
abbrev Pred := Nat→Prop
def sub (a b:Nat) := a &&& b == a
theorem sub_mem {a b r:Nat} (h:sub a b=true) (mem:a.testBit r=true) : b.testBit r=true :=by
  have eq:a &&& b=a:=beq_iff_eq.mp h
  have bit:=congrArg (fun k:Nat=>k.testBit r) eq;simpa [Nat.testBit_and,mem] using bit

def checkRoute (src a b:Nat) (f:Nat→Nat) := sub src (f 0) &&
 ((List.range 11).all fun t=>fcovers 15 (decide (t=0)) (f t) (f (t+1))) &&
 sub (f 10) a && sub (f 11) b

def Physical (src a b:Nat) := ∀(x:Int→Bool) (j:Int) (q:Nat),q=9 ∨ q=10→
  Tr x j (atSet 15 x j src) (atSet 15 x j (if q=9 then a else b)) (driver q)

theorem route_sound {src a b:Nat} {f:Nat→Nat} (ok:checkRoute src a b f=true) : Physical src a b :=by
  simp only [checkRoute,Bool.and_eq_true] at ok
  intro x j q legal s mem pulse
  have bound:q+1≤11:=by rcases legal with rfl|rfl <;> decide
  have step (t:Nat) (ht:t<q+1) (r:Nat) (hr:r<2^15) (inside:(f t).testBit r=true) (z:Bool) :
      (f (t+1)).testBit (stripStep 15 (decide (t=0)) z r)=true :=by
    have valid:=List.all_eq_true.mp ok.1.1.2 t (List.mem_range.mpr (by omega))
    exact fcovers_sound valid _ (mem_imageAux inside z _ hr)
  have reached:=frame_route 15 q (fun i r=>(f i).testBit r=true) step x j s (sub_mem ok.1.1.1 mem) pulse
  rcases legal with rfl|rfl
  · exact sub_mem ok.1.2 reached
  · exact sub_mem ok.2 reached
end Ruliology.CellularAutomata.Rule30RequiredGapLogic.StripInclusion

end

section
namespace Ruliology.CellularAutomata.Rule30RequiredGapLogic
open Ruliology.CellularAutomata Ruliology.CellularAutomata.Rule30RequiredGapLogic.RunFamilies Rule30StripCertificates Rule30FastImage Rule30ResetMixtures
open Ruliology.CellularAutomata.Rule30RequiredGapLogic.StripInclusion (sub sub_mem)
def alphabet : List Nat := [9,10,11,12,13,14,15,16]
def next (h q:Nat) := if q=12 then 1 else if h=1 ∧ q=10 then 2 else 0
def legal (h:Nat) := alphabet.filter (fun q=>decide (¬(h=2 ∧ q=9)))
abbrev Supported (h q:Nat) := q∈legal h
theorem range_alphabet {q:Nat} (r:9≤q ∧ q≤16) : q∈alphabet :=by simp [alphabet];omega
theorem legal_range {h q:Nat} (hq:Supported h q):9≤q ∧ q≤16 :=by
  have mem: q∈alphabet := (List.mem_filter.mp hq).1
  simp [alphabet] at mem;omega
def checkRoute (src h:Nat) (dst f:Nat→Nat) := sub src (f 0) &&
 ((List.range 17).all fun t=>fcovers 19 (decide (t=0)) (f t) (f (t+1))) &&
 (legal h).all (fun q=>sub (f (q+1)) (dst q))
def Physical (src h:Nat) (dst:Nat→Nat) := ∀(x:Int→Bool) (j:Int) (q:Nat),Supported h q→
  Tr x j (atSet 19 x j src) (atSet 19 x j (dst q)) (driver q)
theorem empty_route (h:Nat) (dst:Nat→Nat) : Physical 0 h dst :=by
  intro x j q _ s mem; simp [atSet] at mem
theorem route_sound {src h:Nat} {dst f:Nat→Nat} (ok:checkRoute src h dst f=true) : Physical src h dst :=by
  simp only [checkRoute,Bool.and_eq_true] at ok
  intro x j q supp s mem pulse
  have bound:=legal_range supp
  have step (t:Nat) (ht:t<q+1) (r:Nat) (hr:r<2^19) (inside:(f t).testBit r=true) (z:Bool) :
      (f (t+1)).testBit (stripStep 19 (decide (t=0)) z r)=true :=by
    have valid:=List.all_eq_true.mp ok.1.2 t (List.mem_range.mpr (by omega))
    exact fcovers_sound valid _ (mem_imageAux inside z _ hr)
  have reached:=frame_route 19 q (fun i r=>(f i).testBit r=true) step x j s (sub_mem ok.1.1 mem) pulse
  exact sub_mem (List.all_eq_true.mp ok.2 q supp) reached
end Ruliology.CellularAutomata.Rule30RequiredGapLogic

end

namespace Ruliology.CellularAutomata.Rule30RequiredGapLogic
open Ruliology.CellularAutomata.Rule30FastImage
abbrev imageStep := fimage 19
theorem imageStep_spec (a : Bool) (S : Nat) : imageStep a S = fimage 19 a S := rfl
end Ruliology.CellularAutomata.Rule30RequiredGapLogic

namespace Ruliology.CellularAutomata.Rule30RequiredGapLogic
open Ruliology.CellularAutomata Ruliology.CellularAutomata.Rule30RequiredGapLogic.RunFamilies Rule30FastImage Rule30StripCertificates
open Ruliology.CellularAutomata.Rule30RequiredGapLogic.StripInclusion (sub sub_mem)
set_option maxHeartbeats 0

def images (src : Nat) : Nat → Nat
  | 0 => src
  | t + 1 => imageStep (decide (t = 0)) (images src t)

def scanImages (h : Nat) (dst : Nat → Nat) : Nat → Nat → Nat → Bool
  | 0, _, _ => true
  | fuel + 1, t, mask =>
    let z := imageStep (decide (t = 0)) mask
    (!(decide (t ∈ legal h)) || sub z (dst t)) && scanImages h dst fuel (t+1) z

theorem scanImages_at (src h : Nat) (dst : Nat → Nat) (fuel t : Nat)
    (ok : scanImages h dst fuel t (images src t) = true)
    (q : Nat) (lo : t ≤ q) (hi : q < t + fuel) (supported : Supported h q) :
    sub (images src (q+1)) (dst q) = true := by
  induction fuel generalizing t with
  | zero => omega
  | succ fuel ih =>
    change (_ && scanImages h dst fuel (t+1) (images src (t+1))) = true at ok
    simp only [Bool.and_eq_true] at ok
    have hv := ok
    by_cases same : q = t
    · subst q
      simpa only [supported, decide_true, Bool.not_true, Bool.false_or, images] using hv.1
    · exact ih (t+1) hv.2 (by omega) (by omega)

theorem routeByImage {src h : Nat} {dst : Nat → Nat}
    (ok : scanImages h dst 17 0 src = true) : Physical src h dst := by
  intro x j q supported s start pulse
  have lim := legal_range supported
  have path := frame_route 19 q (fun t r => (images src t).testBit r = true)
    (fun t _ r hr inside z => by
      rw [images, imageStep_spec]
      exact fimage_mem hr inside z) x j s start pulse
  apply sub_mem (scanImages_at src h dst 17 0 ok q (by omega) (by omega) supported) path
end Ruliology.CellularAutomata.Rule30RequiredGapLogic

section
namespace Ruliology.CellularAutomata.Rule30RequiredGapLogic.RunFamilies
def stamp (q:Nat→Nat) : Nat→Nat |0=>0 |n+1=>stamp q n+q n+1
def locate (q:Nat→Nat) : Nat→Nat×Nat
  |0=>(0,0)
  |t+1=>let z:=locate q t;if z.2<q z.1 then (z.1,z.2+1) else (z.1+1,0)
def clock (q:Nat→Nat) (t:Nat) := (locate q t).2
private theorem inside_block (q:Nat→Nat) (n s:Nat) (start:locate q s=(n,0)) (i:Nat) (small:i≤q n) :
    locate q (s+i)=(n,i) :=by
  induction i with
  |zero=>exact start
  |succ i ih=>
    rw [show s+(i+1)=(s+i)+1 by omega,locate,ih (by omega)];simp [show i<q n by omega]
theorem locate_stamp (q:Nat→Nat) (n:Nat) : locate q (stamp q n)=(n,0) :=by
  induction n with
  |zero=>rfl
  |succ n ih=>rw [stamp,locate,inside_block q n _ ih (q n) (by omega)];simp
theorem clock_at (q:Nat→Nat) (n i:Nat) (small:i≤q n) : clock q (stamp q n+i)=i :=
  congrArg Prod.snd (inside_block q n _ (locate_stamp q n) i small)
theorem locate_cover (q:Nat→Nat) (t:Nat) : ∃n i,t=stamp q n+i ∧ i≤q n :=by
  induction t with
  |zero=>exact ⟨0,0,rfl,by omega⟩
  |succ t ih=>
    obtain ⟨n,i,eq,le⟩:=ih;by_cases done_:i=q n
    · refine ⟨n+1,0,?_,by omega⟩;rw [stamp,←done_,eq]
    · exact ⟨n,i+1,by omega,by omega⟩
theorem stamp_ge (q:Nat→Nat) (n:Nat) : n≤stamp q n :=by induction n with |zero=>exact Nat.le_refl _ |succ n ih=>rw [stamp];omega
theorem stamp_mono (q:Nat→Nat) {a b:Nat} (h:a≤b) : stamp q a≤stamp q b :=by
  induction b with
  |zero=>have e:a=0:=by omega
         subst a;omega
  |succ b ih=>by_cases last:a=b+1
              · subst a;omega
              · have le:=ih (by omega);rw [stamp];omega
theorem label_mul (q:Nat→Nat) (m:Nat) (per:∀n,q (n+m)=q n) (d n:Nat) : q (n+d*m)=q n :=by
  induction d with |zero=>simp |succ d ih=>rw [Nat.succ_mul,←Nat.add_assoc,per,ih]
theorem stamp_shift (q:Nat→Nat) (m:Nat) (per:∀n,q (n+m)=q n) (n:Nat) :
    stamp q (n+m)=stamp q m+stamp q n :=by
  induction n with
  |zero=>simp [stamp]
  |succ n ih=>rw [show n+1+m=(n+m)+1 by omega,stamp,ih,per,stamp];omega

theorem clock_period (q:Nat→Nat) (m:Nat) (per:∀n,q (n+m)=q n) (t:Nat) :
    clock q (t+stamp q m)=clock q t :=by
  obtain ⟨n,i,rfl,le⟩:=locate_cover q t
  rw [clock_at _ _ _ le,show stamp q n+i+stamp q m=stamp q (n+m)+i by rw [stamp_shift q m per];omega,
    clock_at _ _ _ (by rw [per];exact le)]

/-- A physical tick in the t>=stamp(S) tail belongs to a pulse index n>=S. -/
theorem tail_index (q:Nat→Nat) {n i S:Nat} (hi:i≤q n) (late:stamp q S≤stamp q n+i) : S≤n :=by
  apply Classical.byContradiction;intro no;have up:=stamp_mono q (a:=n+1) (b:=S) (by omega)
  rw [stamp] at up;omega
end Ruliology.CellularAutomata.Rule30RequiredGapLogic.RunFamilies

end

section

namespace Ruliology.CellularAutomata.Rule30RequiredGapLogic.NoDiamond


variable {V I O : Type}

def PeriodicTail {A : Type _} (f : Nat→A) : Prop :=
  ∃ T P : Nat, 0<P ∧ ∀ t, T≤t → f (t+P)=f t

/-- A vertex path of L directed edges. Labels are sampled at the sources 0,...,L−1. -/
def Walk (E : V→V→Prop) (L : Nat) (x : Nat→V) : Prop := ∀ i, i<L → E (x i) (x (i+1))

def Reach (E : V→V→Prop) (a b : V) : Prop :=
  ∃ L x, Walk E L x ∧ x 0=a ∧ x L=b

def Component (E : V→V→Prop) (a v : V) := Reach E a v ∧ Reach E v a

/-- The finite-graph criterion is needed only on each recurrent strongly connected component.
It compares equal-observation paths of a common length between equal endpoints. -/
def NoDiamondOnCycles (E : V→V→Prop) (obs : V→I) (gate : V→O) : Prop :=
  ∀ (a : V), (∃ L x, 0<L ∧ Walk E L x ∧ x 0=a ∧ x L=a) →
  ∀ L x y, Walk E L x → Walk E L y →
    (∀ i, i≤L → Component E a (x i) ∧ Component E a (y i)) →
    x 0=y 0 → x L=y L → (∀ i, i<L → obs (x i)=obs (y i)) →
    ∀ i, i<L → gate (x i)=gate (y i)

private theorem loop_inside {E : V→V→Prop} {L x a} (walk : Walk E L x)
    (start : x 0=a) (finish : x L=a) (i : Nat) (hi : i≤L) : Component E a (x i) := by
  refine ⟨⟨i,x,fun j hj=>walk j (by omega),start,rfl⟩,
    ⟨L-i,fun j=>x (i+j),?_,by simp,?_⟩⟩
  · intro j hj
    exact walk (i+j) (by omega)
  · simpa only [show i+(L-i)=L by omega] using finish

/-- Traverse the first m edges of a returning path and then start that path again. -/
private def splice (x : Nat→V) (m i : Nat) : V := if i<m then x i else x (i-m)

private theorem splice_zero (x : Nat→V) (m : Nat) : splice x m 0=x 0 := by
  by_cases h : 0<m <;> simp [splice,h]

private theorem splice_walk {E : V→V→Prop} {x : Nat→V} (step : ∀ i,E (x i) (x (i+1)))
    {m : Nat} (ret : x m=x 0) : ∀ i, E (splice x m i) (splice x m (i+1)) := by
  intro i
  by_cases last : i+1<m
  · simpa [splice,last,show i<m by omega] using step i
  by_cases before : i<m
  · have eq : i+1=m := by omega
    simpa [splice,last,before,eq,ret] using step i
  · simpa [splice,last,before,show i+1-m=(i-m)+1 by omega] using step (i-m)

private theorem splice_obs {x : Nat→V} {obs : V→I} {m : Nat}
    (period : ∀ i, obs (x (i+m))=obs (x i)) (i : Nat) :
    obs (splice x m i)=obs (x i) := by
  by_cases before : i<m
  · simp [splice,before]
  · simpa only [splice,ite_eq_right before,show i-m+m=i by omega] using (period (i-m)).symm

/-- A fixed return of length m and arbitrarily long returns at the same observation phase
force the gate to repeat by m. Compare A·B with B·A, for a fixed loop A and a long loop B. -/
theorem compare_returns {E : V→V→Prop} {obs : V→I} {gate : V→O}
    (safe : NoDiamondOnCycles E obs gate) {x : Nat→V} (step : ∀ i,E (x i) (x (i+1)))
    {m : Nat} (hm : 0<m) (ret : x m=x 0) (per : ∀ i,obs (x (i+m))=obs (x i))
    (unbounded : ∀ B,∃ n,B<n ∧ x n=x 0 ∧ ∀ i,obs (x (i+n))=obs (x i)) :
    ∀ i, gate (x (i+m))=gate (x i) := by
  intro i
  obtain ⟨n,large,back,pern⟩:=unbounded (i+m)
  let X:=splice x m
  let Y:=splice x n
  have wx : Walk E (m+n) X:=fun j _=>splice_walk step ret j
  have wy : Walk E (m+n) Y:=fun j _=>splice_walk step back j
  have x0 : X 0=x 0:=splice_zero _ _
  have y0 : Y 0=x 0:=splice_zero _ _
  have xL : X (m+n)=x 0 := by simpa [X,splice,show ¬m+n<m by omega] using back
  have yL : Y (m+n)=x 0 := by simpa [Y,splice,show ¬m+n<n by omega] using ret
  have same:=safe (x 0) ⟨m,x,hm,fun j _=>step j,rfl,ret⟩ (m+n) X Y wx wy
    (fun j hj=>⟨loop_inside wx x0 xL j hj,loop_inside wy y0 yL j hj⟩)
    (x0.trans y0.symm) (xL.trans yL.symm)
    (fun j _=>(splice_obs per j).trans (splice_obs pern j).symm) (i+m) (by omega)
  simpa [X,Y,splice,large,show ¬i+m<m by omega] using same.symm

private theorem choose_recurrent (pool : List V) (x : Nat→V) (inside : ∀ t,x t∈pool) :
    ∃ a, ∀ bound, ∃ t,bound≤t ∧ x t=a := by
  classical
  induction pool generalizing x with
  | nil => exact False.elim (by simpa using inside 0)
  | cons a pool ih =>
    by_cases often : ∀ bound,∃ t,bound≤t ∧ x t=a
    · exact ⟨a,often⟩
    obtain ⟨bound,stop⟩:=Classical.not_forall.mp often
    have other : ∀ i,x (bound+i)∈pool := by
      intro i
      rcases List.mem_cons.mp (inside (bound+i)) with same | tail
      · exact False.elim (stop ⟨_,by omega,same⟩)
      · exact tail
    obtain ⟨b,freq⟩:=ih (fun i=>x (bound+i)) other
    refine ⟨b,fun n=>?_⟩
    obtain ⟨t,ht,e⟩:=freq n
    exact ⟨bound+t,by omega,e⟩

theorem periodic_gate_of_no_diamond {E : V→V→Prop} (obs : V→I) (gate : V→O)
    (safe : NoDiamondOnCycles E obs gate) (pool : List V) (x : Nat→V) (inside : ∀ t,x t∈pool)
    (step : ∀ t,E (x t) (x (t+1))) (period : PeriodicTail (fun t=>obs (x t))) :
    PeriodicTail (fun t=>gate (x t)) := by
  obtain ⟨T,p,hp,per⟩:=period
  change ∀t,T≤t → obs (x (t+p))=obs (x t) at per
  obtain ⟨v,recurs⟩:=choose_recurrent pool (fun k=>x (T+k*p)) (fun _=>inside _)
  obtain ⟨a,_,atA⟩:=recurs 0
  obtain ⟨b,after,atB⟩:=recurs (a+1)
  let start:=T+a*p
  let y:=fun i=>x (start+i)
  have toIndex (c : Nat) (hc : a≤c) : start+(c-a)*p=T+c*p := by
    dsimp [start]
    rw [Nat.add_assoc,←Nat.add_mul,show a+(c-a)=c by omega]
  have shifts (k i : Nat) : obs (y (i+k*p))=obs (y i) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have eqn : start+(i+(k+1)*p)=(start+(i+k*p))+p := by rw [Nat.succ_mul];omega
      change obs (x (start+(i+(k+1)*p)))=_
      rw [eqn,per _ (by dsimp [start];omega)]
      exact ih
  have entry (c : Nat) (hc : a≤c) (vc : x (T+c*p)=v) : y ((c-a)*p)=y 0 := by
    dsimp [y]
    rw [toIndex c hc,vc]
    exact atA.symm
  let m:=(b-a)*p
  have positive : 0<m:=Nat.mul_pos (by omega) hp
  have gy : ∀ i,gate (y (i+m))=gate (y i) := by
    apply compare_returns safe (fun i=>step (start+i)) positive (entry b (by omega) atB) (shifts (b-a))
    intro bound
    obtain ⟨c,hc,atC⟩:=recurs (a+bound+1)
    have lower : c-a≤(c-a)*p:=Nat.le_mul_of_pos_right _ hp
    exact ⟨(c-a)*p,by omega,entry c (by omega) atC,shifts (c-a)⟩
  refine ⟨start,m,positive,?_⟩
  intro t ht
  have e:=gy (t-start)
  simpa only [y,show start+(t-start+m)=t+m by omega,show start+(t-start)=t by omega] using e

end Ruliology.CellularAutomata.Rule30RequiredGapLogic.NoDiamond

end

section

namespace Ruliology.CellularAutomata.Rule30RequiredGapLogic.PeriodBound

open Ruliology.CellularAutomata.Rule30RequiredGapLogic.NoDiamond

variable {V I O : Type}

/-- More samples than elements of a covering list force two equal samples within the list length. -/
theorem short_return (pool : List V) (f : Nat → V) (inside : ∀ i, i ≤ pool.length → f i ∈ pool) :
    ∃ a b : Nat, a < b ∧ b ≤ pool.length ∧ f a = f b := by
  classical
  let samples := List.ofFn (fun i : Fin (pool.length + 1) => f i.val)
  have len : samples.length = pool.length + 1 := List.length_ofFn
  have subset : samples ⊆ pool := by
    intro v h
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp h
    exact inside i.val (by have h := i.isLt; omega)
  apply Classical.byContradiction
  intro none
  have distinct : samples.Nodup := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij eq
    apply none
    refine ⟨i,j,hij,by omega,?_⟩
    simpa only [samples,List.getElem_ofFn] using eq
  have impossible := distinct.length_le_of_subset subset
  omega

/-- In a finite list there is a last occurrence of every non-recurrent value that appears. -/
theorem eventually_only_recurrent (pool : List V) (f : Nat → V) :
    ∃ cutoff, ∀ n, cutoff ≤ n → f n ∈ pool → ∀ limit, ∃ k, limit ≤ k ∧ f k = f n := by
  classical
  induction pool with
  | nil => exact ⟨0,by simp⟩
  | cons v pool ih =>
    obtain ⟨b, tail⟩ := ih
    by_cases often : ∀ limit, ∃ k, limit ≤ k ∧ f k = v
    · refine ⟨b,fun n hn h => ?_⟩
      rcases List.mem_cons.mp h with atV | other
      · simpa [atV] using often
      · exact tail n hn other
    · obtain ⟨c, absent⟩ := Classical.not_forall.mp often
      refine ⟨max b c,fun n hn h => ?_⟩
      rcases List.mem_cons.mp h with atV | other
      · exact False.elim (absent ⟨n,by omega,atV⟩)
      · exact tail n (by omega) other

/-- A return at two equal input phases gives a gate period when that state/phase recurs forever. -/
theorem gate_of_phase_return {E : V → V → Prop} {obs : V → I} {gate : V → O}
    (safe : NoDiamondOnCycles E obs gate) (x : Nat → V) (step : ∀t, E (x t) (x (t+1)))
    {T p a b : Nat} (hp : 0<p) (per : ∀t, T≤t → obs (x (t+p))=obs (x t))
    (ab : a<b) (repeatState : x (T+a*p)=x (T+b*p))
    (often : ∀ bound, ∃ c, bound≤c ∧ x (T+c*p)=x (T+a*p)) :
    ∀t, T+a*p≤t → gate (x (t+(b-a)*p))=gate (x t) := by
  let start := T+a*p
  let y := fun i => x (start+i)
  have toIndex (c : Nat) (hc : a≤c) : start+(c-a)*p=T+c*p := by
    dsimp [start]
    rw [Nat.add_assoc,←Nat.add_mul,show a+(c-a)=c by omega]
  have shifts (k i : Nat) : obs (y (i+k*p))=obs (y i) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have eqn : start+(i+(k+1)*p)=(start+(i+k*p))+p := by rw [Nat.succ_mul]; omega
      change obs (x (start+(i+(k+1)*p)))=_
      rw [eqn,per _ (by dsimp [start]; omega)]
      exact ih
  have entry (c : Nat) (hc : a≤c) (h : x (T+c*p)=x (T+a*p)) : y ((c-a)*p)=y 0 := by
    simpa [y,toIndex c hc,start] using h
  let m := (b-a)*p
  have gp : ∀ i,gate (y (i+m))=gate (y i) := by
    apply compare_returns safe (fun i=>step (start+i)) (Nat.mul_pos (by omega) hp)
      (entry b (by omega) repeatState.symm) (shifts (b-a))
    intro bound
    obtain ⟨c,hc,ret⟩ := often (a+bound+1)
    have lower : c-a≤(c-a)*p := Nat.le_mul_of_pos_right _ hp
    exact ⟨(c-a)*p,by omega,entry c (by omega) ret,shifts (c-a)⟩
  intro t ht
  have le : start ≤ t := ht
  simpa only [y,m,show start+(t-start+m)=t+m by omega,show start+(t-start)=t by omega]
    using gp (t-start)

/-- From a cutoff B where all subsequent phase-zero samples are recurrent and covered by pool,
both the extra onset delay a and the period multiplier d are controlled by a+d ≤ pool.length. -/
theorem period_from_recurrent_pool {E : V → V → Prop} {obs : V → I} {gate : V → O}
    (safe : NoDiamondOnCycles E obs gate) (x : Nat → V) (step : ∀t, E (x t) (x (t+1)))
    {T p B : Nat} (hp : 0<p) (per : ∀t, T≤t → obs (x (t+p))=obs (x t))
    (pool : List V) (inside : ∀n, B≤n → x (T+n*p)∈pool)
    (recurrent : ∀n, B≤n → ∀bound, ∃k, bound≤k ∧ x (T+k*p)=x (T+n*p)) :
    ∃ a d, 0<d ∧ a+d≤pool.length ∧
      ∀ t, T+(B+a)*p≤t → gate (x (t+d*p))=gate (x t) := by
  obtain ⟨a,b,ab,cap,eq⟩ := short_return pool (fun n=>x (T+(B+n)*p))
    (fun n _=>inside (B+n) (by omega))
  refine ⟨a,b-a,by omega,by omega,?_⟩
  have periodic := gate_of_phase_return safe x step hp per
    (show B+a<B+b by omega) eq (recurrent (B+a) (by omega))
  simpa only [show B+b-(B+a)=b-a by omega] using periodic

/-- An eventual pool suffices. The cutoff B covers the finitely occurring phase-zero
states as well as the supplied lower bound; the start need not be the observation onset. -/
theorem period_from_eventual_pool {E : V → V → Prop} {obs : V → I} {gate : V → O}
    (safe : NoDiamondOnCycles E obs gate) (x : Nat → V) (step : ∀t, E (x t) (x (t+1)))
    {T p B₀ : Nat} (hp : 0<p) (per : ∀t, T≤t → obs (x (t+p))=obs (x t))
    (pool : List V) (inside : ∀n, B₀≤n → x (T+n*p)∈pool) :
    ∃ B a d, B₀≤B ∧ 0<d ∧ a+d≤pool.length ∧
      ∀t, T+(B+a)*p≤t → gate (x (t+d*p))=gate (x t) := by
  obtain ⟨c,recurs⟩ := eventually_only_recurrent pool (fun n=>x (T+n*p))
  let B := max B₀ c
  have covered (n : Nat) (hn : B≤n) := inside n (by dsimp [B] at hn; omega)
  obtain ⟨a,d,pos,small,period⟩ := period_from_recurrent_pool safe x step hp per pool covered
    (fun n hn=>recurs n (by dsimp [B] at hn; omega) (covered n hn))
  exact ⟨B,a,d,by dsimp [B]; omega,pos,small,period⟩

/-- A period p of the observations transfers to a gate period d*p with 1 ≤ d ≤ |pool|. -/
theorem period_bound {E : V → V → Prop} {obs : V → I} {gate : V → O}
    (safe : NoDiamondOnCycles E obs gate) (x : Nat → V) (step : ∀t, E (x t) (x (t+1)))
    {T p : Nat} (hp : 0<p) (per : ∀t, T≤t → obs (x (t+p))=obs (x t))
    (pool : List V) (inside : ∀t, x t∈pool) :
    ∃ S d, T≤S ∧ 0<d ∧ d≤pool.length ∧ ∀t, S≤t → gate (x (t+d*p))=gate (x t) := by
  obtain ⟨B,a,d,_,pos,small,period⟩ := period_from_eventual_pool safe x step hp per
    (B₀:=0) pool (fun n _=>inside (T+n*p))
  exact ⟨T+(B+a)*p,d,by omega,pos,by omega,period⟩

end Ruliology.CellularAutomata.Rule30RequiredGapLogic.PeriodBound

end

section
namespace Ruliology.CellularAutomata.Rule30RequiredGapLogic.EdgeDiamond
open Ruliology.CellularAutomata.Rule30RequiredGapLogic.NoDiamond Ruliology.CellularAutomata.Rule30RequiredGapLogic.PeriodBound
variable {V I O:Type}
abbrev Graph (V I:Type) := V→I→V→Prop
def bare (e:Graph V I) (u v:V) := ∃q,e u q v
def Lift (e:Graph V I) (u v:V×I) := e u.1 u.2 v.1
def Mixed (e:Graph V I) (color:V→O) (a:V) :=
  ∃u v,Component (bare e) a u ∧ Component (bare e) a v ∧ color u≠color v
def WalkWord (e:Graph V I) (L:Nat) (x:Nat→V) (q:Nat→I) := ∀i,i<L→e (x i) (q i) (x (i+1))
/-- Two trajectories inside the same mixed SCC, with the same input letters, start and end,
have the same sequence of output colors. Monochromatic SCCs need no certificate. -/
def MixedNoDiamond (e:Graph V I) (color:V→O) := ∀a,Mixed e color a→∀L x y q,
  WalkWord e L x q→WalkWord e L y q→
  (∀i,i≤L→Component (bare e) a (x i) ∧ Component (bare e) a (y i))→
  x 0=y 0→x L=y L→∀i,i<L→color (x i)=color (y i)
private theorem project_reach {e:Graph V I} {s t:V×I} (h:Reach (Lift e) s t) : Reach (bare e) s.1 t.1 :=by
  obtain ⟨n,f,step,first,last⟩:=h
  exact ⟨n,fun i=>(f i).1,fun i hi=>⟨(f i).2,step i hi⟩,congrArg Prod.fst first,congrArg Prod.fst last⟩
private theorem project_scc {e:Graph V I} {s t:V×I} (h:Component (Lift e) s t) : Component (bare e) s.1 t.1 :=
  ⟨project_reach h.1,project_reach h.2⟩

theorem lift_safe {e:Graph V I} {g:V→O} (safe:MixedNoDiamond e g) :
    NoDiamondOnCycles (Lift e) Prod.snd (fun z=>g z.1) :=by
  intro a _ L x y wf wg inside start finish labels i hi
  have mem (j:Nat) (hj:j≤L) := And.intro (project_scc (inside j hj).1) (project_scc (inside j hj).2)
  by_cases mixed:Mixed e g a.1
  · apply safe a.1 mixed L (fun j=>(x j).1) (fun j=>(y j).1) (fun j=>(x j).2) wf _ mem (congrArg Prod.fst start) (congrArg Prod.fst finish) i hi
    intro j hj;change e (y j).1 (x j).2 (y (j+1)).1;rw [show (x j).2=(y j).2 from labels j hj];exact wg j hj
  · exact Classical.byContradiction fun diff=>mixed ⟨_,_,(mem i (by omega)).1,(mem i (by omega)).2,diff⟩

/-- With p-periodic inputs, the eventual output period is d*p for 1≤d≤number of covering
rows. Only rows at one fixed input phase need be counted. -/
theorem output_bound {e:Graph V I} (g:V→O) (safe:MixedNoDiamond e g)
    (x:Nat→V) (q:Nat→I) (edges:∀t,e (x t) (q t) (x (t+1)))
    {T p:Nat} (hp:0<p) (per:∀t,T≤t→q (t+p)=q t) (pool:List V)
    (inside:∀n,x (T+n*p)∈pool) :
    ∃S d,T≤S ∧ 0<d ∧ d≤pool.length ∧ ∀t,S≤t→g (x (t+d*p))=g (x t) :=by
  let z:=fun t=>(x t,q t);let cover:=pool.map (fun v=>(v,q T))
  have obs (n:Nat) : q (T+n*p)=q T:=by
    induction n with |zero=>simp |succ n ih=>rw [Nat.succ_mul,←Nat.add_assoc,per _ (by omega),ih]
  have members (n:Nat) (_:0≤n) : z (T+n*p)∈cover:=by
    apply List.mem_map.mpr;exact ⟨_,inside n,by simp [z,obs]⟩
  obtain ⟨B,a,d,_,hd,limit,transfer⟩:=period_from_eventual_pool (lift_safe safe) z edges hp per cover members
  refine ⟨T+(B+a)*p,d,by omega,hd,?_,transfer⟩;simp [cover] at limit;omega
end Ruliology.CellularAutomata.Rule30RequiredGapLogic.EdgeDiamond

end

section
namespace Ruliology.CellularAutomata.Rule30RequiredGapLogic.EdgeDiamond
open Ruliology.CellularAutomata.Rule30RequiredGapLogic.NoDiamond
variable {V I O:Type}
structure Square (e:Graph V I) (g:V→O) (a:V) where
  F : V→V→Prop
  B : V→V→Prop
  diagF : ∀u,Component (bare e) a u→F u u
  diagB : ∀u,Component (bare e) a u→B u u
  forward : ∀{u v i j q},Component (bare e) a u→Component (bare e) a v→
    Component (bare e) a i→Component (bare e) a j→e u q i→e v q j→F u v→F i j
  backward : ∀{u v i j q},Component (bare e) a u→Component (bare e) a v→
    Component (bare e) a i→Component (bare e) a j→e u q i→e v q j→B i j→B u v
  agree : ∀{u v},Component (bare e) a u→Component (bare e) a v→F u v→B u v→g u=g v

theorem safe_of_squares {e:Graph V I} {g:V→O} (squares:∀a,Mixed e g a→Nonempty (Square e g a)) :
    MixedNoDiamond e g :=by
  intro a mixed L x y q pathX pathY inside fst last i hi;obtain ⟨c⟩:=squares a mixed
  have fwd (j:Nat) (hj:j≤L) : c.F (x j) (y j):=by
    induction j with
    |zero=>rw [fst];exact c.diagF _ (inside 0 (by omega)).2
    |succ j ih=>
      exact c.forward (inside j (by omega)).1 (inside j (by omega)).2
        (inside (j+1) hj).1 (inside (j+1) hj).2 (pathX _ (by omega)) (pathY _ (by omega)) (ih (by omega))
  have back (j:Nat) (hj:j≤L) : c.B (x (L-j)) (y (L-j)):=by
    induction j with
    |zero=>simp only [Nat.sub_zero,last];exact c.diagB _ (inside L (by omega)).2
    |succ j ih=>
      let n:=L-(j+1);have good:n<L:=by dsimp [n];omega
      have nex:n+1=L-j:=by dsimp [n];omega
      exact c.backward (inside n (by omega)).1 (inside n (by omega)).2 (inside (n+1) (by omega)).1
        (inside (n+1) (by omega)).2 (pathX _ good) (pathY _ good) (by rw [nex];exact ih (by omega))
  apply c.agree (inside i (by omega)).1 (inside i (by omega)).2 (fwd i (by omega))
  simpa only [show L-(L-i)=i by omega] using back (L-i) (by omega)
end Ruliology.CellularAutomata.Rule30RequiredGapLogic.EdgeDiamond

end

section
namespace Ruliology.CellularAutomata.Rule30RequiredGapLogic.SparseWarm
open Rule30StripCertificates
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def plane0 : Nat→Nat
  | 0=>31104046901108787144435665889206071397940821358361090478937513225543584367684
  | 1=>77647045935605670693766196478692014069582894103345100940743622879659745258411
  | 2=>452319777394873750995974874953422931238693749459057997226035729588736229632
  | 3=>31330210240679192530614904209142030054779786742013628745850844107782760973637
  | 4=>31330210240679192530614999990113334172833434138702825640174820278977897448772
  | 5=>32234835938056349890747802167047124804292601419734381113929323934340528489797
  | 6=>32234946365997898539768407109451627744078193924289564304436181828584094319940
  | 7=>32238480060128271632954248739919636946272673676867963856333082002328117462341
  | 8=>32238480060128271633150408169150470720153175920309482758819511066449861297605
  | 9=>32238493863619322923596751098900847684249932361168502891133646240997166958532
  | 10=>32238493863619322917319649363514166920414142937960836475012844052459422894021
  | 11=>32238493863619322917319649364975668557745045856243749470243391409708899387332
  | 12=>32238493863619322917711872442466031987431135298505031726925812453792765069253
  | 13=>32238493863198073725831157413662348059781978716466478147176135870652583397316
  | 14=>32238386886129711333481583324555204085896047112239563548344475012405527726021
  | 15=>31333761054374076250951372589893039952843170426282970623980051665899372038084
  | 16=>31335524477526026433865716095787665997636265556872290632471729028122775078725
  | _=>0
def plane1 : Nat→Nat
  | 0=>7720356053675940553993349264796153335703512234544625135508975382363209011473
  | 1=>452319750434925476907290819834630664926067816376398052529555625568874004737
  | 2=>7717705741795941659954720040349459296193768249690415246110898846841504272657
  | 3=>7717705742217190851737355730149356121380582073020873889122399889547712270608
  | 4=>7719472589281982091571293286644512953948727018728291647821093880027925188880
  | 5=>7719465687746259884344619856980365134132256185122508046222634386450537254929
  | 6=>7719465687746465572426544971974072259199173117527220236031829588177595666449
  | 7=>7719467413183881450098329563181322618522114767354785453364994897970572955668
  | 8=>7719467414026379783446787056764666883547621191788545419960484760573493514260
  | 9=>7726548605778186901893078988464835879180670592359072262431717799646826205716
  | 10=>7726548605778186901893078988464835879180670592359072262431717799646826205716
  | 11=>7726548605778188508831123245993609783811860015238761794126530708059830227476
  | 12=>7726548605778188508831123245993609783833127663171320448092991621024315740693
  | 13=>7726548605356939317048487931805342743459187657791325119558288949131357852181
  | 14=>7724785209165334322116015474757518443918033710055924495379232833266634854932
  | 15=>8629417915917994130325873136372316835569650062687253840273121014731697951508
  | 16=>8631181338227240292005993462920725264150824079879620594846542376746865857301
  | _=>0
def plane2 : Nat→Nat
  | 0=>3845601314866950039791350513697134402900070583908768868999373525170440407168
  | 1=>1766874025136433896750911497805567796640956260043310612149274219378704385
  | 2=>7238772451357398647869937474540799808626014997862578563078248274713949306881
  | 3=>7238772451778647839750652877494611883422177024630883662102416492227257761857
  | 4=>7238775902651834090536900853866957632885502973781026525199833947533257801793
  | 5=>8143408609404500326498936019129091129045246355766145590883527463466577232192
  | 6=>8369565033748789666519876692664498715619444822423020635568670248222152819008
  | 7=>8369565033748789666519876692664498715619444822423020635568670248222152819008
  | 8=>8369565033748789666519876692664498715619444822423020635568670248222152819009
  | 9=>8376646225500596784966168624364667710912211856072609014576528679863717036865
  | 10=>1139640648168334564715880325934992706247048391262407345989627490831402369856
  | 11=>1139640648168334564617800609858074182316176718179673362979240208952822170368
  | 12=>1139637197295161175612912846895518992687305065061683626591592624772020798209
  | 13=>1139637197084538174105435798250743675927627888673048639276463171222080946945
  | 14=>8376756654916724787552375762760883778107085279939176818151771097643169710849
  | 15=>10189562449039641895825753325392054576065648547034851891381024826746478888513
  | 16=>2724519692838016652956863297825591523176404493106380183156082551331213018688
  | _=>0
def plane3 : Nat→Nat
  | 0=>57896044618658097711785492504343953926805133516280751251460479307672448925696
  | 1=>0
  | 2=>7237005577332262220250288298429675004665163464810201668586901189032314667008
  | 3=>7237005577753513019069047961835264258754320751024022289766977029461875097664
  | 4=>7238775875691477654577293875141324592548131259940134005946978920904121122880
  | 5=>8143408582233519282093807731306905592655202206091102562159635360371248726336
  | 6=>8367908589139768386080255893003398706785673513495458817073985179611096449344
  | 7=>9276090303272527913932322791175061537148889435628367127464975545950454056004
  | 8=>12668491882407643142421916922718390276935819796700796587833294121280192253125
  | 9=>12668490156971882410935719185031142305291424662323661297047581033939729386689
  | 10=>12668490156971882410935719185031142305291424662323661297047581033939729386689
  | 11=>12668490156971882410935719185031142304951142295402722833584206426507961175233
  | 12=>12668490156971882404658617449644461541115352872195056417463404237970217110720
  | 13=>12668490157182505406166094124139108710393059148916141085532282677956383345856
  | 14=>5431370699350318792719154159628968608213601757650012906656974751535294581952
  | 15=>3618558003481053286943944529101531756673236846572556566593984654201577277568
  | 16=>1648718433409724022795430312108018843252061540523294116263493632
  | _=>0
def plane4 : Nat→Nat
  | 0=>57896044618658097714924043372037294308723028227884584459511657029904466182144
  | 1=>340282366920938463463374607431768211457
  | 2=>340282366920938463463374607431768211457
  | 3=>421249191782635688338395188196193271968484111244328292888499716097
  | 4=>1766847486040431616573244833552020764338217675901869943022283368712634369
  | 5=>906399553817457475795972347607162181586199794945924968599511100281526944001
  | 6=>1130789131096955575982975464647412935592253315895382254585959894556889612545
  | 7=>226158149781698789940548135245450989211266353719139323938128381075838369797
  | 8=>1726279907783268064955293387667662574311496024245848475458923183341572
  | 9=>842501547224546011563984551930485229251531163319300987373905772544
  | 10=>842501547224546011563984551930485229251531163319300987373905772544
  | 11=>842501547224546011563984551930485229251531163319300987373905772544
  | 12=>842501547224546011563984551930485229251531163319300987373905772544
  | 13=>842501547224546011563984551930485229251531163319300987373905772544
  | 14=>842501547224546011563984551930485229251531163319300987373905772544
  | 15=>842501547224546011563984551930485229251531163319300987373905772544
  | 16=>3213876088517980640286904978804817771196723811124770985213952
  | _=>0
def plane5 : Nat→Nat
  | 0=>842498333348457493583344265025506424433759966595489862602920558592
  | 1=>1606938044258990275541962092341162602526925360265662480515072
  | 2=>1607330363117451943089723096828045640331898218393905968185344
  | 3=>1607330363117451943089723096828045640331898218393905968185344
  | 4=>1607330363117451943089723096828045640331898218393905968185344
  | 5=>421250799112998805790338277579007733093185979679172079362699689984
  | 6=>1766847486042038946936362285495110147152678800603738377866069842912608256
  | 7=>906399554238708274908971153397500458824925161118172484815308572212458422528
  | 8=>1132555978582997614929911826932908045399123627775047529500451356968034009344
  | 9=>1132557704020407064849519288642951447695909147916373345290062345856528580868
  | 10=>1132557704020407064849519288642951447695909147916373345290062345856528580868
  | 11=>1132557704020405457911475029652675905733816806753770818364702080194048065796
  | 12=>1132557704020405457519156171191008357972812319870733013391843951950560395524
  | 13=>1132557703599156265736520482852613170116901414823187365610890266493828890884
  | 14=>1130790856534365025902582926357456337548756469115769606912196276013615972612
  | 15=>226158149781698789940548135245450988870983986798200860474753773644070158340
  | 16=>1725437409449919607461710043402296785520141325815789610988888494571524
  | _=>0
def height (z x : Nat) := 1*((plane0 z).testBit x).toNat + 2*((plane1 z).testBit x).toNat + 4*((plane2 z).testBit x).toNat + 8*((plane3 z).testBit x).toNat + 16*((plane4 z).testBit x).toNat + 32*((plane5 z).testBit x).toNat

def Allowed (z y : Nat) := (z<16 ∧ y=z+1) ∨ (9≤z ∧ y=0)
def good (z x : Nat) := z=2 ∨ x.testBit 0=decide (z≠1)
def room (z x y : Nat) := [false,true].all fun e=>
  let h:=height y (stripStep 8 (decide (z=0)) e x)
  decide (h=0 ∨ h<height z x)
def vertex (z x : Nat) := decide (height z x ≤ 41) && (decide (height z x ≠ 0) || decide (z=2 ∨ x.testBit 0=decide (z≠1))) &&
  (decide (16≤z) || room z x (z+1)) && (decide (z<9) || room z x 0)
private theorem raw : (List.range 17).all (fun z=>(List.range 256).all (fun x=>vertex z x))=true := by decide +kernel
theorem certified {z x : Nat} (hz:z≤16) (hx:x<256) : vertex z x=true :=
  List.all_eq_true.mp (List.all_eq_true.mp raw _ (List.mem_range.mpr (by omega))) _ (List.mem_range.mpr hx)
theorem unroll {z x y : Nat} (hz:z≤16) (hx:x<256) (move:Allowed z y) (e:Bool) :
    height z x≤41 ∧ (height z x=0 → good z x) ∧
    (height y (stripStep 8 (decide (z=0)) e x)=0 ∨ height y (stripStep 8 (decide (z=0)) e x)<height z x) := by
  have v:=certified hz hx
  simp only [vertex,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at v
  refine ⟨v.1.1.1,fun eq=>v.1.1.2.resolve_left (fun ne=>ne eq),?_⟩
  have h : room z x y=true := by
    rcases move with ⟨lt,rfl⟩ | ⟨ge,rfl⟩
    · exact v.1.2.resolve_left (by omega)
    · exact v.2.resolve_left (by omega)
  have a:=List.all_eq_true.mp h e (by cases e <;> simp)
  simpa using a

theorem forty_one (p x : Nat→Nat) (phase:∀t,p t≤16) (size:∀t,x t<256) (move:∀t,Allowed (p t) (p (t+1)))
    (step:∀t,∃e,x (t+1)=stripStep 8 (decide (p t=0)) e (x t)) (t:Nat) (ht:41≤t) : good (p t) (x t) := by
  have one (u:Nat) : height (p u) (x u)≤41 ∧ (height (p u) (x u)=0 → good (p u) (x u)) ∧ (height (p (u+1)) (x (u+1))=0 ∨ height (p (u+1)) (x (u+1))<height (p u) (x u)) := by
    obtain ⟨e,E⟩:=step u
    have v:=unroll (phase u) (size u) (move u) e
    rw [←E] at v
    exact v
  have h (u:Nat):height (p u) (x u)=0 ∨ height (p u) (x u)+u≤41 := by
    induction u with
    | zero => right;simpa using (one 0).1
    | succ u ih =>
      have a:=(one u).2.2
      rcases a with a|a
      · exact Or.inl a
      · right;omega
  apply (one t).2.1;have a:=h t;omega
end Ruliology.CellularAutomata.Rule30RequiredGapLogic.SparseWarm


end

section
namespace Ruliology.CellularAutomata.Rule30RequiredGapLogic.MixedLanguage
abbrev Graph := Nat → Nat → Nat → Prop
def Repeats (x : Nat → Nat) (a : Nat) := ∀T,∃t,T≤t ∧ x t=a
def Reach (e : Graph) (a b : Nat) :=
  ∃ (n : Nat) (u : Nat → Nat), u 0=a ∧ u n=b ∧ ∀i,i<n → ∃q,e (u i) q (u (i+1))
def Mixed (e : Graph) (color : Nat→Bool) (v : Nat) :=
  ∃ a b,Reach e v a ∧ Reach e a v ∧ Reach e v b ∧ Reach e b v ∧ color a≠color b
def Varies (x : Nat→Nat) (col : Nat→Bool) :=
  ∀T,∃a,T≤a ∧ ∃b,T≤b ∧ col (x a)≠col (x b)

theorem late_recurrence (x : Nat→Nat) (bound : Nat) :
    ∃T,∀t,T≤t → x t<bound → Repeats x (x t) := by
  classical
  induction bound with
  | zero => exact ⟨0, fun _ _ h=>by omega⟩
  | succ b ih =>
    obtain ⟨T,h⟩:=ih
    by_cases rec : Repeats x b
    · refine ⟨T, fun t ht hb=>?_⟩
      by_cases eq:x t=b
      · simpa [eq] using rec
      · exact h t ht (by omega)
    · unfold Repeats at rec
      have hh : ∃ U, ∀ t, U≤t → x t≠b := by
        apply Classical.byContradiction; intro hn; apply rec; intro u
        apply Classical.byContradiction; intro none; apply hn; refine ⟨u, fun t ht eq=>?_⟩; exact none ⟨t,ht,eq⟩
      obtain ⟨U,u⟩:=hh
      exact ⟨T+U, fun t ht hb=>h t (by omega) (by have ne:=u t (by omega);omega)⟩

theorem connects {e : Graph} {x q : Nat→Nat} (step : ∀t,e (x t) (q t) (x (t+1)))
    {a b} (ha : Repeats x a) (hb : Repeats x b) : Reach e a b := by
  obtain ⟨s,_,hs⟩:=ha 0
  obtain ⟨t,hst,ht⟩:=hb s
  refine ⟨t-s,fun n=>x (s+n),by simpa using hs,by simpa [show s+(t-s)=t by omega] using ht,?_⟩
  intro i _
  exact ⟨q (s+i),by simpa [Nat.add_assoc] using step (s+i)⟩

/-- A nonsettling observable on a finite strip eventually stays in a component with both colors. -/
theorem late_mixed {e : Graph} (x q : Nat→Nat) (color : Nat→Bool) (size : Nat) (bound : ∀t,x t<size)
    (step : ∀t,e (x t) (q t) (x (t+1))) (varies : Varies x color) :
    ∃T,∀t,T≤t → Mixed e color (x t) := by
  obtain ⟨T,h⟩:=late_recurrence x size
  obtain ⟨a,ha,b,hb,ne⟩:=varies T
  have ra:=h a ha (bound a)
  have rb:=h b hb (bound b)
  refine ⟨T,fun t ht=>?_⟩
  have rt:=h t ht (bound t)
  exact ⟨x a,x b,connects step rt ra,connects step ra rt,connects step rt rb,connects step rb rt,ne⟩

def Follows (e : Graph) (good : Nat→Prop) (letters : List Nat) (a : Nat) : Prop :=
  match letters with
  | [] => good a
  | q::rest => good a ∧ ∃b,e a q b ∧ Follows e good rest b

def segment (q : Nat→Nat) (t : Nat) : Nat→List Nat
  | 0=>[]
  | n+1=>q t :: segment q (t+1) n

theorem reads_segment {e : Graph} {x q : Nat→Nat} {good : Nat→Prop} (step : ∀t,e (x t) (q t) (x (t+1)))
    {T} (late : ∀t,T≤t → good (x t)) (s n : Nat) (hs:T≤s) :
    Follows e good (segment q s n) (x s) := by
  induction n generalizing s with
  | zero => exact late s hs
  | succ n ih => exact ⟨late s hs,x (s+1),step s,ih (s+1) (by omega)⟩

/-- Every factor sufficiently far along the input has a path in the mixed component. -/
theorem late_factors {e : Graph} (x q : Nat→Nat) (color : Nat→Bool) (size : Nat) (bound : ∀t,x t<size)
    (step : ∀t,e (x t) (q t) (x (t+1))) (varies : Varies x color) :
    ∃T,∀s,T≤s → ∀n, ∃a,Follows e (Mixed e color) (segment q s n) a := by
  obtain ⟨T,h⟩:=late_mixed x q color size bound step varies
  exact ⟨T,fun s hs n=>⟨x s,reads_segment step h s n hs⟩⟩
end Ruliology.CellularAutomata.Rule30RequiredGapLogic.MixedLanguage




end

section
namespace Ruliology.CellularAutomata.Rule30RequiredGapLogic.SparseWarm
open Rule30Realization Rule30StripCertificates

theorem physical_warm (x : Int→Bool) (j:Int) (s:Nat) (p:Nat→Nat)
    (phase:∀t,p t≤16) (move:∀t,Allowed (p t) (p (t+1)))
    (drive:∀t,evol x (s+t) j=decide (p t=0)) (t:Nat) (ht:41≤t) :
    p t=2 ∨ evol x (s+t) (j+1)=decide (p t≠1) := by
  let r:=fun u=>Rule30FiniteStrips.encRow x (s+u) j 8
  have step (u:Nat):∃e,r (u+1)=stripStep 8 (decide (p u=0)) e (r u) := by
    refine ⟨evol x (s+u) (j+1+8),?_⟩
    have n:=Rule30FiniteStrips.enc_step (Rule30FiniteStrips.enc_encRow (x:=x) 8 (s+u) j)
    have f:=Rule30FiniteStrips.enc_encRow (x:=x) 8 (s+u+1) j
    rw [drive u] at n
    apply Nat.eq_of_testBit_eq;intro i;by_cases h:i<8
    · exact (f.2 i h).trans (n.2 i h).symm
    · have up:=Nat.pow_le_pow_right (by decide : 0<2) (show 8≤i by omega)
      exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le f.1 up)).trans (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le n.1 up)).symm
  have law:=forty_one p r phase (fun u=>(Rule30FiniteStrips.enc_encRow (x:=x) 8 (s+u) j).1) move step t ht
  have obs:=(Rule30FiniteStrips.enc_encRow (x:=x) 8 (s+t) j).2 0 (by decide)
  unfold good at law;change p t=2 ∨ (Rule30FiniteStrips.encRow x (s+t) j 8).testBit 0=decide (p t≠1) at law
  rw [obs] at law;simpa only [Int.natCast_zero, Int.add_zero] using law

/-- Each temporal period must fail again in the right neighbor on the second white after a pulse. -/
theorem second_white_breaks {x : Int→Bool} {left:Int} (black:x left=true) (white:∀i,i<left → x i=false)
    (j:Int) (s:Nat) (p:Nat→Nat) (phase:∀t,p t≤16) (move:∀t,Allowed (p t) (p (t+1)))
    (drive:∀t,evol x (s+t) j=decide (p t=0)) (P:Nat) (pos:0<P) (per:∀t,p (t+P)=p t)
    (T:Nat) : ∃t,T≤t ∧ p t=2 ∧ evol x (s+t+P) (j+1)≠evol x (s+t) (j+1) := by
  apply Classical.byContradiction;intro none
  apply Rule30FiniteMaskedJen.masked_jen black white j (T:=s+T+41) pos
  · intro t ht;obtain ⟨u,rfl⟩:=Nat.exists_eq_add_of_le (show s≤t by omega)
    rw [Nat.add_assoc,drive,per,drive]
  · intro t ht _
    obtain ⟨u,rfl⟩:=Nat.exists_eq_add_of_le (show s≤t by omega)
    by_cases h:p u=2
    · apply Classical.byContradiction;intro bad;exact none ⟨u,by omega,h,bad⟩
    · have now:=(physical_warm x j s p phase move drive u (by omega)).resolve_left h
      have later:=physical_warm x j s p phase move drive (u+P) (by omega)
      rw [per] at later
      rw [Nat.add_assoc,later.resolve_left h,now]
end Ruliology.CellularAutomata.Rule30RequiredGapLogic.SparseWarm



end

section
namespace Ruliology.CellularAutomata.Rule30RequiredGapLogic.RunFamilies
open Rule30Jen Rule30Realization Rule30StripCertificates Ruliology.CellularAutomata.Rule30RequiredGapLogic.SparseWarm
def pulseColor (v:Nat) := !v.testBit 0 || (!v.testBit 1 && !v.testBit 2)

theorem pulse_color (x:Int→Bool) (j:Int) (s W:Nat) (width:3≤W)
    (pulse:evol x s j=true) (white:evol x (s+1) j=false) :
    pulseColor (row W x j s)=evol x (s+2) (j+1) :=by
  have enc:=Rule30FiniteStrips.enc_encRow (x:=x) W s j
  have b0:(row W x j s).testBit 0=evol x s (j+1):=by simpa only [row,Int.natCast_zero,Int.add_zero] using enc.2 0 (by omega)
  have b1:(row W x j s).testBit 1=evol x s (j+2):=by simpa only [row,Int.natCast_one,show j+1+1=j+2 by omega] using enc.2 1 (by omega)
  have b2:(row W x j s).testBit 2=evol x s (j+3):=by simpa only [row,show j+1+((2:Nat):Int)=j+3 by omega] using enc.2 2 (by omega)
  have step (t:Nat) (k:Int) : evol x (t+1) k=rule (evol x t (k-1)) (evol x t k) (evol x t (k+1)):=rfl
  rw [pulseColor,b0,b1,b2,show s+2=(s+1)+1 by omega,step,show j+1-1=j by omega,white,step,step,
    show j+1-1=j by omega,show j+1+1-1=j+1 by omega,pulse,show j+1+1=j+2 by omega,show j+2+1=j+3 by omega]
  cases evol x s (j+1) <;> cases evol x s (j+2) <;> cases evol x s (j+3) <;> decide

theorem clock_rules (q:Nat→Nat) (range:∀n,9≤q n ∧ q n≤16) :
  (∀t,clock q t≤16) ∧ (∀t,Allowed (clock q t) (clock q (t+1))) :=by
  constructor
  · intro t;obtain ⟨n,i,rfl,hi⟩:=locate_cover q t;rw [clock_at _ _ _ hi];exact Nat.le_trans hi (range n).2
  · intro t;obtain ⟨n,i,rfl,hi⟩:=locate_cover q t;rw [clock_at _ _ _ hi]
    by_cases last:i=q n
    · right;refine ⟨by have z:=(range n).1;omega,?_⟩
      rw [show stamp q n+i+1=stamp q (n+1)+0 by rw [stamp,last],clock_at _ _ _ (by omega)]
    · left;refine ⟨by have z:=(range n).2;omega,?_⟩
      rw [show stamp q n+i+1=stamp q n+(i+1) by omega,clock_at _ _ _ (by omega)]

def Fitted (x:Int→Bool) (j:Int) (s:Nat) (q:Nat→Nat) := ∀t,evol x (s+t) j=decide (clock q t=0)
def samples (x:Int→Bool) (j:Int) (s W:Nat) (q:Nat→Nat) (n:Nat) := row W x j (s+stamp q n)

theorem actual_color {x j s q} (f:Fitted x j s q) (range:∀n,9≤q n ∧ q n≤16) (W n:Nat) (size:3≤W) :
  pulseColor (samples x j s W q n)=evol x (s+stamp q n+2) (j+1) :=by
  apply pulse_color _ _ _ _ size
  · have z:=f (stamp q n+0);rw [clock_at _ _ _ (by omega),Nat.add_zero] at z;exact z
  · have z:=f (stamp q n+1);rw [clock_at _ _ _ (by have h:=(range n).1;omega)] at z
    simpa [Nat.add_assoc] using z

/-- Any persistent sampled period compatible with a repeated gap word contradicts finite-left
masked Jen. A period D in pulse counts corresponds to stamp(q,D) ordinary time steps. -/
theorem no_sample_period {x:Int→Bool} {lo j:Int} {s W:Nat} {q:Nat→Nat} (width:3≤W)
    (black:x lo=true) (left:∀i,i<lo→x i=false) (range:∀n,9≤q n ∧ q n≤16) (drive:Fitted x j s q)
    {D:Nat} (pos:0<D) (qp:∀n,q (n+D)=q n) (S:Nat) :
    ¬∀n,S≤n→pulseColor (samples x j s W q (n+D))=pulseColor (samples x j s W q n) :=by
  intro varies;obtain ⟨bound,allowed⟩:=clock_rules q range
  have per:=clock_period q D qp;have time:0<stamp q D:=Nat.lt_of_lt_of_le pos (stamp_ge _ _)
  obtain ⟨t,late,phase,ne⟩:=second_white_breaks black left j s _ bound allowed drive _ time per (stamp q S)
  obtain ⟨n,i,eq,hi⟩:=locate_cover q t
  rw [eq,clock_at _ _ _ hi] at phase;subst i
  have large:S≤n:=tail_index q hi (by simpa only [eq] using late)
  have p:=varies n large;rw [actual_color drive range _ _ width,actual_color drive range _ _ width,stamp_shift q D qp] at p
  apply ne;rw [eq,show s+(stamp q n+2)+stamp q D=s+(stamp q D+stamp q n)+2 by omega,show s+(stamp q n+2)=s+stamp q n+2 by omega];exact p

theorem finite_left_no_diamond {x:Int→Bool} {lo j:Int} {s W m:Nat} {q:Nat→Nat} (width:3≤W)
    (black:x lo=true) (left:∀i,i<lo→x i=false) (range:∀n,9≤q n ∧ q n≤16)
    (mpos:0<m) (qper:∀n,q (n+m)=q n) (e:Ruliology.CellularAutomata.Rule30RequiredGapLogic.EdgeDiamond.Graph Nat Nat)
    (safe:Ruliology.CellularAutomata.Rule30RequiredGapLogic.EdgeDiamond.MixedNoDiamond e pulseColor) (N:Nat)
    (edges:∀n,N≤n→e (samples x j s W q n) (q n) (samples x j s W q (n+1))) : ¬Fitted x j s q :=by
  intro fitted
  let z:=samples x j s W q
  have tail (n:Nat) : e (z (N+n)) (q (N+n)) (z (N+(n+1))):=by simpa only [Nat.add_assoc] using edges (N+n) (by omega)
  have each (n:Nat) (_:0≤n) : q (N+(n+m))=q (N+n):=by rw [←Nat.add_assoc,qper]
  have pool (n:Nat) : z (N+(0+n*m))∈List.range (2^W) :=
    List.mem_range.mpr (Rule30FiniteStrips.enc_encRow (x:=x) W _ j).1
  obtain ⟨S,d,_,hd,_,per⟩:=Ruliology.CellularAutomata.Rule30RequiredGapLogic.EdgeDiamond.output_bound pulseColor safe (fun n=>z (N+n)) (fun n=>q (N+n)) tail mpos each _ pool
  apply no_sample_period width black left range fitted (Nat.mul_pos hd mpos) (label_mul q m qper d) (N+S)
  intro n hn;obtain ⟨u,rfl⟩:=Nat.exists_eq_add_of_le (show N≤n by omega)
  simpa only [Nat.add_assoc] using per u (by omega)
end Ruliology.CellularAutomata.Rule30RequiredGapLogic.RunFamilies

end

section
namespace Ruliology.CellularAutomata.Rule30RequiredGapLogic
def state (q:Nat→Nat) : Nat→Nat |0=>0 |n+1=>next (state q n) (q n)
theorem state_bound (q:Nat→Nat) (n:Nat) : state q n<3 :=by
  cases n with
  |zero=>change 0<3;decide
  |succ n=>simp only [state,next];split <;> first | decide | (split <;> decide)
theorem state_one (q:Nat→Nat) (n:Nat) : state q (n+1)=1 ↔ q n=12 :=by
  simp only [state,next];split <;> rename_i h
  · simp [h]
  · simp only [h,iff_false];split <;> decide
theorem state_two (q:Nat→Nat) (n:Nat) : state q (n+2)=2 ↔ q n=12 ∧ q (n+1)=10 :=by
  change next (state q (n+1)) (q (n+1))=2 ↔ _
  unfold next;by_cases a:q (n+1)=12
  · simp [a]
  · rw [ite_eq_right a];by_cases b:state q (n+1)=1 ∧ q (n+1)=10
    · simpa [b,b.2] using (state_one q n).mp b.1
    · simp [b];rintro c d;exact b ⟨(state_one q n).mpr c,d⟩
theorem supported_state {q:Nat→Nat} (range:∀n,9≤q n ∧ q n≤16)
    (avoid:∀n,¬(q n=12 ∧ q (n+1)=10 ∧ q (n+2)=9)) (n:Nat) : Supported (state q n) (q n) :=by
  apply List.mem_filter.mpr;refine ⟨range_alphabet (range n),decide_eq_true ?_⟩
  rintro ⟨h,g⟩
  match n with
  |0=>simp [state] at h
  |1=>simp [state,next] at h;split at h <;> contradiction
  |n+2=>have z:=(state_two q n).mp h;exact avoid n ⟨z.1,z.2,g⟩
end Ruliology.CellularAutomata.Rule30RequiredGapLogic

end

section
namespace Ruliology.CellularAutomata.Rule30RequiredGapLogic.RunFamilies
open Rule30Realization Rule30ResetMixtures
def letters (qs:List Nat) (n:Nat) := qs.getD (n%qs.length) 0
def render (q:Nat→Nat) : Nat→Nat→List Bool
  |_,0=>[]
  |k,n+1=>driver (q k)++render q (k+1) n

private theorem render_length (q:Nat→Nat) (k n:Nat) : stamp q (k+n)=stamp q k+(render q k n).length :=by
  induction n generalizing k with
  |zero=>simp [render]
  |succ n ih=>rw [show k+(n+1)=(k+1)+n by omega,ih,render,List.length_append,driver_length,stamp];omega

private theorem render_bits (q:Nat→Nat) (k n t:Nat) (ht:t<(render q k n).length) :
    (render q k n).getD t false=decide (clock q (stamp q k+t)=0) :=by
  induction n generalizing k t with
  |zero=>simp [render] at ht
  |succ n ih=>
    rw [render,List.length_append,driver_length] at ht
    by_cases early:t≤q k
    · rw [clock_at _ _ _ early,render,List.getD_eq_getElem?_getD,List.getElem?_append_left (by rw [driver_length];omega)]
      cases t with |zero=>rfl |succ z=>simp [driver,show z<q k by omega]
    · have hlen:(driver (q k)).length≤t:=by rw [driver_length];omega
      rw [render,List.getD_eq_getElem?_getD,List.getElem?_append_right hlen,←List.getD_eq_getElem?_getD,driver_length,
        ih (k+1) (t-(q k+1)) (by omega)]
      congr 3;rw [stamp];omega

private theorem render_blocks (qs:List Nat) (q:Nat→Nat) (k:Nat) (fits:∀i,i<qs.length→q (k+i)=qs.getD i 0) :
    render q k qs.length=blocks qs :=by
  induction qs generalizing k with
  |nil=>rfl
  |cons a qs ih=>
    have zero:=fits 0 (by simp);simp at zero
    rw [List.length_cons,render,blocks_cons,zero]
    rw [ih (k+1) (fun i hi=>by simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using fits (i+1) (by simp;omega))]

theorem letters_period (qs:List Nat) (n:Nat) : letters qs (n+qs.length)=letters qs n :=by simp [letters]
theorem clock_block_word (qs:List Nat) (nonempty:qs≠[]) (t:Nat) :
    decide (clock (letters qs) t=0)=(blocks qs).getD (t%(blocks qs).length) false :=by
  let q:=letters qs
  have renderEq:=render_blocks qs q 0 (fun i hi=>by simp [q,letters,Nat.mod_eq_of_lt hi])
  have length:stamp q qs.length=(blocks qs).length:=by simpa [renderEq,stamp] using render_length q 0 qs.length
  let P:=(blocks qs).length;have pos:0<P:=blocks_length_pos qs nonempty
  have periodic (u:Nat):clock q (u+P)=clock q u:=by rw [show P=stamp q qs.length from length.symm];exact clock_period q qs.length (letters_period qs) u
  have mul (n u:Nat):clock q (u+n*P)=clock q u:=by
    induction n with |zero=>simp |succ n ih=>rw [Nat.succ_mul,←Nat.add_assoc,periodic,ih]
  have pad:t%P+(t/P)*P=t:=by rw [Nat.mul_comm,Nat.mod_add_div]
  have eq:=mul (t/P) (t%P);rw [pad] at eq
  have obs:=render_bits q 0 qs.length (t%P) (by rw [renderEq];exact Nat.mod_lt _ pos)
  rw [renderEq] at obs;simp only [stamp,Nat.zero_add] at obs
  exact (congrArg (fun v:Nat=>decide (v=0)) eq).trans obs.symm

theorem literal_gap_word {x j} (qs:List Nat) (ne:qs≠[]) (exclude:∀s,¬Fitted x j s (letters qs)) :
    ¬Rule30FiniteStrips.EventuallyWord x j (blocks qs) :=by
  rintro ⟨s,fit⟩;apply exclude s;intro t;rw [clock_block_word qs ne,fit _ (by omega),show s+t-s=t by omega]

theorem shifted_literal {x j} (qs:List Nat) (ne:qs≠[]) (exclude:∀s,¬Fitted x j s (letters qs)) (s d:Nat) :
    ¬∀t,evol x (s+t) j=(blocks qs).getD ((d+t)%(blocks qs).length) false :=by
  intro seen;let w:=blocks qs;let P:=w.length;let delta:=P-(d%P);have pos:0<P:=blocks_length_pos qs ne
  have align:d%P+delta=P:=by dsimp [delta];have h:=Nat.mod_lt d pos;omega
  apply literal_gap_word qs ne exclude
  refine ⟨s+delta,?_⟩;intro t large;obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le large
  rw [Nat.add_assoc,seen,show s+(delta+k)-(s+delta)=k by omega]
  have modEq:(d+(delta+k))%P=k%P:=by rw [←Nat.mod_add_mod d P (delta+k),←Nat.add_assoc,align,Nat.add_mod_left]
  rw [show (blocks qs).length=P from rfl,modEq]
end Ruliology.CellularAutomata.Rule30RequiredGapLogic.RunFamilies

end

section
namespace Ruliology.CellularAutomata.Rule30RequiredGapLogic.GapParity
open Rule30StripCertificates Rule30Jen

def Allowed (z y : Nat) := (z<16 ∧ y=z+1) ∨ (9≤z ∧ z≠10 ∧ z≤16 ∧ y=0)
def expected (z m : Nat) := decide (z=0 ∨ 3≤z ∨ (z=2 ∧ m=2))
def advance (z y m : Nat) : Nat := if m=0 then 0 else
  if y=0 then (if z=9 then 3-m else 1) else (if 10≤y then 1 else m)
abbrev Table := Nat→Nat→Nat
def look (z x : Nat) := decide (z=0) || x.testBit 0
def edgeOK (r m : Table) (z x y u : Nat) :=
  decide (r y u ≤ r z x) && ((r y u != r z x) ||
    ((look z x == expected z (m z x)) && (m y u == advance z y (m z x))))
def both (r m : Table) (z x y : Nat) := [false,true].all fun b=>
  edgeOK r m z x y (stripStep 12 (decide (z=0)) b x)
def vertex (r m : Table) (z x : Nat) :=
  decide (m z x≤2 ∧ r z x≤20) &&
  ((decide (16≤z) || both r m z x (z+1)) && (decide (z<9 ∨ z=10) || both r m z x 0))
def Certificate (r m : Table) := ∀z,z≤16 → ∀x,x<4096 → vertex r m z x=true

theorem unroll {r m} (c : Certificate r m) {z x y}
    (hz:z≤16) (hx:x<4096) (h:Allowed z y) (b : Bool) :
    let u:=stripStep 12 (decide (z=0)) b x
    m z x≤2 ∧ r z x≤20 ∧ r y u≤r z x ∧ (r y u=r z x →
      look z x=expected z (m z x) ∧ m y u=advance z y (m z x)) := by
  have cc:=c z hz x hx
  simp only [vertex,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at cc
  have hb:both r m z x y=true:=by
    rcases h with ⟨h,rfl⟩|⟨h,n,_,rfl⟩
    · exact cc.2.1.resolve_left (by omega)
    · exact cc.2.2.resolve_left (by omega)
  have e : edgeOK r m z x y (stripStep 12 (decide (z=0)) b x)=true :=
    List.all_eq_true.mp hb b (by cases b <;> simp)
  simp [edgeOK] at e
  exact ⟨cc.1.1,cc.1.2,e.1,fun he=>e.2.resolve_left (by intro hn;exact hn he)⟩

theorem flat_tail (v : Nat→Nat) (down : ∀t,v (t+1)≤v t) :
    ∃T,∀t,T≤t → v t=v T := by
  obtain ⟨l,⟨T,h⟩,least⟩:=Rule30DrivenLeft.exists_least_nat (P:=fun n=>∃t,v t=n) ⟨v 0,0,rfl⟩
  have bound (a:Nat) : v (T+a)≤v T := by
    induction a with | zero=>simp | succ a ih=>exact Nat.le_trans (down _) ih
  refine ⟨T,fun t ht=>?_⟩
  have up:=bound (t-T);rw [show T+(t-T)=t by omega] at up
  by_cases eq:v t=v T
  · exact eq
  · exact False.elim (least _ (by omega : v t<l) ⟨t,rfl⟩)

/-- The exterior can make a new choice on every tick. The eventual three-mode update is deterministic. -/
theorem transducer {r m} (c : Certificate r m) (p x : Nat→Nat) (phase : ∀t,p t≤16)
    (size : ∀t,x t<4096) (move : ∀t,Allowed (p t) (p (t+1)))
    (step : ∀t,∃b,x (t+1)=stripStep 12 (decide (p t=0)) b (x t)) :
    ∃T,∀t,T≤t → look (p t) (x t)=expected (p t) (m (p t) (x t)) ∧
      m (p (t+1)) (x (t+1))=advance (p t) (p (t+1)) (m (p t) (x t)) := by
  have localStep (t : Nat) : m (p t) (x t)≤2 ∧ r (p t) (x t)≤20 ∧ r (p (t+1)) (x (t+1))≤r (p t) (x t) ∧ (r (p (t+1)) (x (t+1))=r (p t) (x t) → look (p t) (x t)=expected (p t) (m (p t) (x t)) ∧ m (p (t+1)) (x (t+1))=advance (p t) (p (t+1)) (m (p t) (x t))) := by
    obtain ⟨b,st⟩:=step t
    have hh:=unroll c (phase t) (size t) (move t) b
    dsimp only at hh
    rw [←st] at hh
    exact hh
  obtain ⟨T,flat⟩:=flat_tail (fun t=>r (p t) (x t)) (fun t=>(localStep t).2.2.1)
  exact ⟨T,fun t ht=>(localStep t).2.2.2 ((flat (t+1) (by omega)).trans (flat t ht).symm)⟩
end Ruliology.CellularAutomata.Rule30RequiredGapLogic.GapParity


end

section
namespace Ruliology.CellularAutomata.Rule30RequiredGapLogic.GapFiniteFamily
open Ruliology.CellularAutomata.Rule30RequiredGapLogic.GapParity
def span : List Nat→Nat | []=>0 | q::qs=>q+1+span qs
def phaseIn : List Nat→Nat→Nat
 | [], _=>0
 | q::qs,t=>if t≤q then t else phaseIn qs (t-(q+1))
def gapClock (qs : List Nat) (t : Nat) := phaseIn qs (t%span qs)
def valid (qs : List Nat) := ∀q,q∈qs → 9≤q ∧ q≠10 ∧ q≤16
private theorem tail_ok {q : Nat} {qs : List Nat} (ok:valid (q::qs)) : valid qs := fun a h=>ok a (by simp [h])
private theorem atZero (qs : List Nat) : phaseIn qs 0=0 := by cases qs <;> simp [phaseIn]
private theorem atEnd (qs : List Nat) : phaseIn qs (span qs)=0 := by
  induction qs with
  | nil => rfl
  | cons q qs ih => unfold span;rw [phaseIn,ite_eq_right (by omega),show q+1+span qs-(q+1)=span qs by omega];exact ih
theorem phase_bound (qs : List Nat) (ok:valid qs) (t:Nat) : phaseIn qs t≤16 := by
  induction qs generalizing t with
  | nil => exact Nat.zero_le _
  | cons q qs ih => rw [phaseIn];split
                    · have z:=ok q (by simp);omega
                    · exact ih (tail_ok ok) _
private theorem stage_step (qs : List Nat) (ok:valid qs) (t : Nat) (before:t<span qs) :
    Allowed (phaseIn qs t) (phaseIn qs (t+1)) := by
  induction qs generalizing t with
  | nil => simp [span] at before
  | cons q qs ih =>
    simp only [span] at before; have f:=ok q (by simp)
    by_cases ins:t<q
    · simp only [phaseIn,ite_eq_left (show t≤q by omega),ite_eq_left (show t+1≤q by omega)]
      exact Or.inl ⟨by omega,rfl⟩
    · by_cases last:t=q
      · subst t;simp only [phaseIn,Nat.le_refl,ite_true,ite_eq_right (show ¬q+1≤q by omega),Nat.sub_self,atZero]
        exact Or.inr ⟨f.1,f.2.1,f.2.2,rfl⟩
      · simp only [phaseIn,ite_eq_right (show ¬t≤q by omega),ite_eq_right (show ¬t+1≤q by omega)]
        rw [show t+1-(q+1)=(t-(q+1))+1 by omega];exact ih (tail_ok ok) _ (by omega)
theorem clock_steps (qs : List Nat) (ok:valid qs) (pos:0<span qs) (t:Nat) :
    Allowed (gapClock qs t) (gapClock qs (t+1)) := by
  let P:=span qs;let j:=t%P;have hj:j<P:=Nat.mod_lt _ pos
  have rd:(t+1)%P=(j+1)%P := by dsimp [j];rw [Nat.add_mod t 1 P,Nat.add_mod (t%P) 1 P,Nat.mod_mod]
  have step:=stage_step qs ok j hj;change Allowed (phaseIn qs j) (phaseIn qs ((t+1)%P));rw [rd]
  by_cases wrap:j+1=P
  · rw [wrap,Nat.mod_self,atZero];rw [wrap,atEnd] at step;exact step
  · rw [Nat.mod_eq_of_lt (by omega : j+1<P)];exact step
theorem periodic (qs : List Nat) (t : Nat) : gapClock qs (t+span qs)=gapClock qs t := by simp [gapClock]
def blocks (qs : List Nat) := qs.flatMap (fun q=>true :: List.replicate q false)
theorem length_blocks (qs : List Nat) : (blocks qs).length=span qs := by
  induction qs with
  | nil => rfl
  | cons q qs ih => change ((true :: List.replicate q false) ++ blocks qs).length=q+1+span qs;simp [ih];omega
theorem entry (qs : List Nat) (t : Nat) (ht:t<span qs) : decide (phaseIn qs t=0)=(blocks qs).getD t false := by
  induction qs generalizing t with
  | nil => simp [span] at ht
  | cons q qs ih =>
    change decide ((if t≤q then t else phaseIn qs (t-(q+1)))=0)=((true :: List.replicate q false) ++ blocks qs).getD t false
    by_cases within:t≤q
    · rw [ite_eq_left within,List.getD_eq_getElem?_getD,List.getElem?_append_left (by simp;omega)]
      cases t with
      | zero => rfl
      | succ t => rw [List.getElem?_cons_succ,List.getElem?_replicate_of_lt (by omega)];rfl
    · rw [ite_eq_right within,List.getD_eq_getElem?_getD,List.getElem?_append_right (by simp;omega)]
      simp only [List.length_cons,List.length_replicate,←List.getD_eq_getElem?_getD]
      exact ih _ (by change t<q+1+span qs at ht;omega)


end Ruliology.CellularAutomata.Rule30RequiredGapLogic.GapFiniteFamily

end

section
namespace Ruliology.CellularAutomata.Rule30RequiredGapLogic.GapFiniteFamily
open Rule30StripCertificates Rule30Realization
open Rule30WhitePad10111 (Sub sub_trans sub_of_and word_mono)
private theorem below_intro (f : Nat→Bool) (k : Nat) (h:∀i,i<k → f i=true) : allBelow f k=true := by
  induction k with
  | zero=>rfl
  | succ k ih=>rw [allBelow,ih (fun i hi=>h i (by omega)),h k (by omega)];rfl

/-- The previously checked width-eight warm-up set of ResetMixtures supplies the ordinary
stripCert directly. This transfers it to every leftmost-black configuration via FiniteStrips. -/
theorem long_strip_cert (qs : List Nat) (ok:Rule30ResetMixtures.Admissible qs) (long:∃q,q∈qs ∧ 17≤q) :
    stripCert (blocks qs) 8 4=true := by
  let w:=Rule30ResetMixtures.blocks qs
  let S:=iterW 8 w 4 (fullSet 8)
  have ne:=Rule30ResetMixtures.nonempty_of_reset long
  have first:=Rule30ResetMixtures.blocks_progress Rule30ResetMixtures.A0 Rule30ResetMixtures.A1
    (fun _=>Rule30ResetMixtures.stage0) (fun _=>Rule30ResetMixtures.stable1) qs ne ok
  have one:Sub (applyWord 8 w (fullSet 8)) (fullSet 8) := by
    rw [Rule30ResetMixtures.full_A0];exact sub_trans first (sub_of_and (by decide +kernel))
  have closure:Sub (applyWord 8 w S) S := word_mono (word_mono (word_mono (word_mono one w) w) w) w
  have warm : Sub S Rule30ResetMixtures.G:=Rule30ResetMixtures.blocks_warm qs ok long
  change subsetB 8 (applyWord 8 w S) S && ((List.range w.length).all fun i=>w.getD i false || colConst 8 (applyWord 8 (w.take i) S) false || colConst 8 (applyWord 8 (w.take i) S) true)=true
  rw [Bool.and_eq_true];constructor
  · apply below_intro;intro r _;change (!((applyWord 8 w S).testBit r) || S.testBit r)=true
    cases a:(applyWord 8 w S).testBit r with
    | false=>rfl
    | true=>simp [closure r a]
  · apply List.all_eq_true.mpr;intro i hi;have hl:i<w.length:=List.mem_range.mp hi
    by_cases bl:w.getD i false=true
    · rw [bl];rfl
    · have wh:w.getD i false=false:=by cases he:w.getD i false <;> simp_all
      obtain ⟨g,controls⟩:=Rule30ResetMixtures.controlled_blocks qs ok i hl
      have cc : colConst 8 (applyWord 8 (w.take i) S) g=true := by
        apply below_intro;intro r hr;change (!((applyWord 8 (w.take i) S).testBit r) || (r.testBit 0==g))=true
        by_cases ins:(applyWord 8 (w.take i) S).testBit r=true
        · have actual:=controls r hr ((word_mono warm (w.take i)) r ins)
          change (w.getD i false || r.testBit 0)=g at actual;rw [wh,Bool.false_or] at actual;simp [ins,actual]
        · simp [ins]
      cases g <;> simp [cc]

private theorem shifted_word {x:Int→Bool} (j:Int) (s offset:Nat) (w:List Bool) (pos:0<w.length)
    (matchWord:∀t,evol x (s+t) j=w.getD ((offset+t)%w.length) false) : Rule30FiniteStrips.EventuallyWord x j w := by
  let n:=w.length;let d:=n-offset%n
  have sum:offset%n+d=n:=by dsimp [d];have hlt:offset%n<n:=Nat.mod_lt offset pos;omega
  refine ⟨s+d,fun t ht=>?_⟩;obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le ht
  rw [Nat.add_assoc,matchWord,show s+(d+k)-(s+d)=k by omega]
  have mm:(offset+(d+k))%n=k%n := by rw [←Nat.mod_add_mod offset n (d+k),←Nat.add_assoc,sum,Nat.add_mod_left]
  rw [mm]

theorem long_gap_all_sites {x:Int→Bool} {left:Int} (black:x left=true) (white:∀i,i<left → x i=false)
    (qs:List Nat) (ok:∀q,q∈qs → 9≤q) (long:∃q,q∈qs ∧ 17≤q) (j:Int) (s offset:Nat) :
    ¬∀t,evol x (s+t) j=(blocks qs).getD ((offset+t)%(blocks qs).length) false := by
  have pos:0<(blocks qs).length:=Rule30ResetMixtures.blocks_length_pos qs (Rule30ResetMixtures.nonempty_of_reset long)
  exact fun drive=>Rule30FiniteStrips.not_eventually_word_strip black white j (blocks qs) 8 4 (by decide) pos (long_strip_cert qs ok long) (shifted_word j s offset (blocks qs) pos drive)

theorem long_same_period (x:Int→Bool) (j:Int) (s offset:Nat)
    (qs:List Nat) (ok:∀q,q∈qs → 9≤q) (long:∃q,q∈qs ∧ 17≤q)
    (drive:∀t,evol x (s+t) j=(blocks qs).getD ((offset+t)%(blocks qs).length) false) :
    ∃T,∀t,T≤t → Rule30FiniteMaskedJen.orCol x j (s+t+span qs)=Rule30FiniteMaskedJen.orCol x j (s+t) := by
  have pos:0<(blocks qs).length:=Rule30ResetMixtures.blocks_length_pos qs (Rule30ResetMixtures.nonempty_of_reset long)
  obtain ⟨T,h⟩:=Rule30FiniteStrips.orCol_exact_period_of_word_strip j (blocks qs) 8 4 (by decide) pos (long_strip_cert qs ok long) (shifted_word j s offset _ pos drive)
  rw [length_blocks] at h;exact ⟨T,fun t ht=>h (s+t) (by omega)⟩
end Ruliology.CellularAutomata.Rule30RequiredGapLogic.GapFiniteFamily



end
