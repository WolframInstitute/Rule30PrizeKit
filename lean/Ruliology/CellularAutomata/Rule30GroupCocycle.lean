module
public import Ruliology.CellularAutomata.Rule30Prize

/-!
# Rule30: local group cocycles carry only background holonomy

For every finite window width and every (possibly noncommutative, infinite)
group, a homogeneous local zero-curvature equation for one Rule30 step forces
the spatial weight to be a vertex gauge of its vacuum value. The normalized transport
window has the one-cell halo specified by `Cocycle`. Independently placed
finite supports are covered by padding into a common container
(`arbitrary_local_supports`); minimal range is not an assumption. No identity-vacuum
normalization is assumed. Every algebraic law is a field of the quantified
standard group structure `GroupData`, not an additional global axiom.

Writing a=L(zeros), the classification is
`L(w) = g(tail w)^-1 * a * g(init w)`.
The canonical gauge also makes temporal transport constant at M(zeros),
and the two vacuum constants commute (`full_background_connection`).
Ordered cyclic products are therefore conjugate to a^length. Pure-gauge
examples establish that this does not assert pointwise constancy of L.
The Boolean specialization classifies exact local-flux laws as spatial
coboundaries plus a constant; it assumes the displayed flux identity, rather
than proving a cyclic-to-local-current equivalence.

The proof gauge-normalizes the edges beginning in white. Left-permutivity
realizes arbitrary middle outputs with two white right registers; independent
outer input bits then force the normalized weight to forget its final cell.
The transport forgets its final cell as well. Induction reduces to the six
one-cell equations in `cube_forces_equal`. Gauge construction and every
range-reduction step work without commutativity.

The existing Rule30LocalConservation and Rule30ProductParity classify additive
integer and mod-two scores for four steps. Here the new scope is group-valued,
ordered, possibly noncommutative transport for one step. This theorem does not
classify noninvertible semigroups, arbitrary nonlocal invariants, or all notions
of integrability, and does not settle a prize problem. The gauge is local in the chosen common container.
Unbounded-memory and noninvertible transport are outside the statement.

-/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30GroupCocycle

/-- Standard group data, kept explicit because the core catalog has no Mathlib. -/
class GroupData (G : Type u) extends Mul G, OfNat G 1, Inv G where
  assoc : ∀ a b c : G, (a*b)*c=a*(b*c)
  left_unit : ∀ a : G, 1*a=a
  right_unit : ∀ a : G, a*1=a
  left_inverse : ∀ a : G, Inv.inv a*a=1
  right_inverse : ∀ a : G, a*Inv.inv a=1

theorem mul_assoc {G : Type u} [GroupData G] (a b c : G) : (a*b)*c=a*(b*c) := GroupData.assoc a b c
@[simp] theorem one_mul {G : Type u} [GroupData G] (a : G) : 1*a=a := GroupData.left_unit a
@[simp] theorem mul_one {G : Type u} [GroupData G] (a : G) : a*1=a := GroupData.right_unit a
@[simp] theorem inv_mul_cancel {G : Type u} [GroupData G] (a : G) : a⁻¹*a=1 := GroupData.left_inverse a
@[simp] theorem mul_inv_cancel {G : Type u} [GroupData G] (a : G) : a*a⁻¹=1 := GroupData.right_inverse a
@[simp] theorem inv_mul_cancel_left {G : Type u} [GroupData G] (a b : G) : a⁻¹*(a*b)=b := by
  rw [←mul_assoc,inv_mul_cancel,one_mul]
@[simp] theorem mul_inv_cancel_left {G : Type u} [GroupData G] (a b : G) : a*(a⁻¹*b)=b := by
  rw [←mul_assoc,mul_inv_cancel,one_mul]
theorem mul_left_cancel {G : Type u} [GroupData G] {a b c : G} (h : a*b=a*c) : b=c := by
  have he := congrArg (fun q : G => a⁻¹*q) h
  simpa only [inv_mul_cancel_left] using he
theorem mul_right_cancel {G : Type u} [GroupData G] {a b c : G} (h : a*b=c*b) : a=c := by
  have he := congrArg (fun q : G => q*b⁻¹) h
  simpa only [mul_assoc,mul_inv_cancel,mul_one] using he

namespace WordOps
def cons {n : Nat} {α : Type u} (a : α) (v : Fin n → α) : Fin (n+1) → α := Fin.cases a v
def init {n : Nat} {α : Type u} (v : Fin (n+1) → α) : Fin n → α := fun i => v i.castSucc
def tail {n : Nat} {α : Type u} (v : Fin (n+1) → α) : Fin n → α := fun i => v i.succ
def snoc {n : Nat} {α : Type u} (v : Fin n → α) (a : α) : Fin (n+1) → α :=
  fun i => if h : i.val<n then v ⟨i.val,h⟩ else a
@[simp] theorem cons_zero {n : Nat} {α : Type u} (a : α) (v : Fin n → α) : cons a v 0=a := rfl
@[simp] theorem cons_succ {n : Nat} {α : Type u} (a : α) (v : Fin n → α) (i : Fin n) : cons a v i.succ=v i := rfl
@[simp] theorem tail_cons {n : Nat} {α : Type u} (a : α) (v : Fin n → α) : tail (cons a v)=v := rfl
@[simp] theorem init_snoc {n : Nat} {α : Type u} (v : Fin n → α) (a : α) : init (snoc v a)=v := by
  funext i
  simp [init,snoc]
@[simp] theorem snoc_castSucc {n : Nat} {α : Type u} (a : α) (v : Fin n → α) (i : Fin n) :
    snoc v a i.castSucc=v i := by simp [snoc]
@[simp] theorem snoc_last {n : Nat} {α : Type u} (v : Fin n → α) (a : α) : snoc v a (Fin.last n)=a := by
  simp [snoc,Fin.last]
@[simp] theorem snoc_apply_zero {n : Nat} {α : Type u} (v : Fin (n+1) → α) (a : α) : snoc v a 0=v 0 := by
  simp [snoc]
@[simp] theorem cons_self_tail {n : Nat} {α : Type u} (v : Fin (n+1) → α) : cons (v 0) (tail v)=v := by
  funext i
  cases i using Fin.cases <;> rfl
@[simp] theorem snoc_init_self {n : Nat} {α : Type u} (v : Fin (n+1) → α) : snoc (init v) (v (Fin.last n))=v := by
  funext i
  cases i using Fin.lastCases with
  | last => simp
  | cast i => simp [init]
theorem cons_snoc_eq_snoc_cons {n : Nat} {α : Type u} (a : α) (v : Fin n → α) (b : α) :
    cons a (snoc v b)=snoc (cons a v) b := by
  funext i
  cases i using Fin.cases with
  | zero => simp
  | succ i =>
    cases i using Fin.lastCases with
    | last => simp [snoc,Fin.last,cons]
    | cast i => simp [snoc,cons,show i.val+1<n+1 by omega]
end WordOps

def iterate {α : Type u} (f : α → α) : Nat → α → α
  | 0,x => x
  | k+1,x => f (iterate f k x)
theorem iterate_succ_apply' {α : Type u} (f : α → α) (k : Nat) (x : α) :
    iterate f (k+1) x=f (iterate f k x) := rfl
theorem iterate_succ_apply {α : Type u} (f : α → α) (k : Nat) (x : α) :
    iterate f (k+1) x=iterate f k (f x) := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg f ih

open Ruliology.CellularAutomata.Rule30Jen
abbrev Word (n : Nat) := Fin n → Bool

def image {n : Nat} (v : Word (n+2)) : Word n := fun i =>
  rule (v ⟨i.val,by omega⟩) (v ⟨i.val+1,by omega⟩) (v ⟨i.val+2,by omega⟩)
def middle {n : Nat} (v : Word (n+2)) : Word n := WordOps.init (WordOps.tail v)

theorem tail_snoc {n : Nat} (v : Word (n+1)) (b : Bool) :
    @WordOps.tail (n+1) Bool (@WordOps.snoc (n+1) Bool v b)=
      @WordOps.snoc n Bool (@WordOps.tail n Bool v) b := by
  funext i
  cases i using Fin.lastCases with
  | last => simp [WordOps.tail,WordOps.snoc]
  | cast i =>
    simp [WordOps.tail,WordOps.snoc,show i.val+1<n+1 by omega]
    congr 1

theorem init_cons {n : Nat} (a : Bool) (v : Word (n+1)) :
    @WordOps.init (n+1) Bool (@WordOps.cons (n+1) Bool a v)=
      @WordOps.cons n Bool a (@WordOps.init n Bool v) := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => rfl

theorem image_cons {n : Nat} (a : Bool) (v : Word (n+2)) :
    image (WordOps.cons a v)=WordOps.cons (rule a (v 0) (v 1)) (image v) := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => rfl

theorem image_snoc {n : Nat} (v : Word (n+2)) (b : Bool) :
    image (WordOps.snoc v b)=WordOps.snoc (image v)
      (rule (v ⟨n,by omega⟩) (v (Fin.last (n+1))) b) := by
  funext i
  cases i using Fin.lastCases with
  | last =>
    simp [image,WordOps.snoc,show n<n+2 by omega]
    rfl
  | cast i => simp [image,WordOps.snoc,show i.val<n+2 by omega,show i.val+1<n+2 by omega,show i.val+2<n+2 by omega]

def fill (a b : Bool) : List Bool → Nat → Bool
  | [],0 => a
  | [],_+1 => b
  | y::ys,0 => rule y (fill a b ys 0) (fill a b ys 1)
  | _::ys,i+1 => fill a b ys i

theorem fill_step (a b : Bool) (ys : List Bool) (i : Nat) (h : i<ys.length) :
    rule (fill a b ys i) (fill a b ys (i+1)) (fill a b ys (i+2))=ys[i] := by
  induction ys generalizing i with
  | nil => simp at h
  | cons y ys ih =>
    cases i with
    | zero =>
      simp only [fill,List.getElem_cons_zero]
      generalize fill a b ys 0=c
      generalize fill a b ys 1=d
      cases y <;> cases c <;> cases d <;> rfl
    | succ i => simpa only [fill,List.getElem_cons_succ] using ih i (by simpa using h)

theorem fill_right0 (a b : Bool) (ys : List Bool) : fill a b ys ys.length=a := by
  induction ys with
  | nil => rfl
  | cons y ys ih => simpa only [List.length_cons,fill] using ih
theorem fill_right1 (a b : Bool) (ys : List Bool) : fill a b ys (ys.length+1)=b := by
  induction ys with
  | nil => rfl
  | cons y ys ih => simpa only [List.length_cons,fill] using ih

/-- Every finite middle output word is realizable with two white right registers. -/
theorem image_surjective_white {n : Nat} (u : Word n) :
    ∃ z : Word (n+2), image z=u ∧ z ⟨n,by omega⟩=false ∧ z (Fin.last (n+1))=false := by
  let ys := List.ofFn u
  let z : Word (n+2) := fun i => fill false false ys i.val
  refine ⟨z,?_,?_,?_⟩
  · funext i
    have h := fill_step false false ys i.val (by simp [ys])
    simpa [image,z,ys] using h
  · have h := fill_right0 false false ys
    simpa [ys,z] using h
  · have h := fill_right1 false false ys
    simpa [ys,z] using h

def Cocycle {G : Type _} [GroupData G] {n : Nat}
    (L : Word n → G) (M : Word (n+1) → G) : Prop :=
  ∀ w : Word (n+2), L (image w)*M (WordOps.init w)=M (WordOps.tail w)*L (middle w)
def Anchored {G : Type _} [GroupData G] {n : Nat} (L : Word (n+1) → G) (vac : G) : Prop :=
  ∀ w, w 0=false → L w=vac

/-- Group-valued endpoint obstruction; no commutativity is assumed. -/
theorem rectangle_forgets_right {G : Type _} [GroupData G]
    (f : Bool → Bool → G) (A B : Bool → G) (C : G)
    (hf : ∀ r, f false r=f false false)
    (h : ∀ l r, f l r*A l=B r*C) : f true false=f true true := by
  have h00 := h false false
  have h01 := h false true
  rw [hf true] at h01
  have hb : B false=B true := mul_right_cancel (h00.symm.trans h01)
  have h10 := h true false
  have h11 := h true true
  rw [hb] at h10
  exact mul_right_cancel (h10.trans h11.symm)

def ForgetsLast {G : Type _} {n : Nat} (L : Word (n+1) → G) : Prop :=
  ∀ v : Word n, ∀ r, L (WordOps.snoc v r)=L (WordOps.snoc v false)

theorem normalized_forgets_last {G : Type _} [GroupData G] {n : Nat}
    (L : Word (n+2) → G) (M : Word (n+3) → G)
    {vac : G} (hN : Anchored L vac) (hC : Cocycle L M) : ForgetsLast L := by
  have htrue (u : Word n) :
      L (WordOps.cons true (WordOps.snoc u false))=L (WordOps.cons true (WordOps.snoc u true)) := by
    obtain ⟨z,hz,hz0,hz1⟩ := image_surjective_white u
    let b := z 0 || z 1
    have hframe (l r : Bool) :
        image (WordOps.cons l (WordOps.snoc z r))=WordOps.cons (xor l b) (WordOps.snoc u r) := by
      rw [image_cons,image_snoc,hz,hz0,hz1]
      have h0 : (WordOps.snoc z r : Word (n+3)) 0=z 0 :=
        @WordOps.snoc_castSucc (n+2) Bool r z 0
      have h1 : (WordOps.snoc z r : Word (n+3)) 1=z 1 :=
        @WordOps.snoc_castSucc (n+2) Bool r z 1
      rw [h0,h1]
      simp only [rule,Bool.false_or,Bool.false_xor,b]
    have hrect (l r : Bool) :
        L (WordOps.cons (xor l b) (WordOps.snoc u r))*M (WordOps.cons l z)=
          M (WordOps.snoc z r)*L z := by
      have h := hC (WordOps.cons l (WordOps.snoc z r))
      simpa only [hframe,init_cons,WordOps.init_snoc,WordOps.tail_cons,middle] using h
    apply rectangle_forgets_right
      (fun l r => L (WordOps.cons l (WordOps.snoc u r)))
      (fun l => M (WordOps.cons (xor l b) z)) (fun r => M (WordOps.snoc z r)) (L z)
    · intro r
      rw [hN _ rfl,hN _ rfl]
    · intro l r
      have h := hrect (xor l b) r
      have he : xor (xor l b) b=l := by cases l <;> cases b <;> rfl
      rw [he] at h
      exact h
  have hboth (a : Bool) (u : Word n) :
      L (WordOps.cons a (WordOps.snoc u false))=L (WordOps.cons a (WordOps.snoc u true)) := by
    cases a with
    | false => rw [hN _ rfl,hN _ rfl]
    | true => exact htrue u
  intro v r
  have h := hboth (v 0) (WordOps.tail v)
  simp only [WordOps.cons_snoc_eq_snoc_cons,WordOps.cons_self_tail] at h
  cases r with
  | false => rfl
  | true => exact h.symm

theorem flux_forgets_last {G : Type _} [GroupData G] {n : Nat}
    (L : Word (n+2) → G) (M : Word (n+3) → G)
    (hL : ForgetsLast L) (hC : Cocycle L M) : ForgetsLast M := by
  unfold ForgetsLast at hL ⊢
  have hframe (w : Word (n+3)) (r : Bool) :
      L (WordOps.snoc (image w) false)*M w=M (WordOps.snoc (WordOps.tail w) r)*L (WordOps.tail w) := by
    have h := hC (WordOps.snoc w r)
    simpa only [image_snoc,hL,WordOps.init_snoc,tail_snoc,middle] using h
  intro v r
  have hr := hframe (WordOps.cons false v) r
  have h0 := hframe (WordOps.cons false v) false
  have he := hr.symm.trans h0
  exact mul_right_cancel (by simpa only [WordOps.tail_cons] using he)

theorem cocycle_shrink {G : Type _} [GroupData G] {n : Nat}
    (L : Word (n+2) → G) (M : Word (n+3) → G)
    (hL : ForgetsLast L) (hM : ForgetsLast M) (hC : Cocycle L M) :
    Cocycle (fun v : Word (n+1) => L (WordOps.snoc v false))
      (fun v : Word (n+2) => M (WordOps.snoc v false)) := by
  unfold ForgetsLast at hL hM
  intro w
  have hm : M w=M (WordOps.snoc (WordOps.init w) false) := by
    have h := hM (WordOps.init w) (w (Fin.last (n+2)))
    simpa only [WordOps.snoc_init_self] using h
  have hl : L (WordOps.tail w)=L (WordOps.snoc (middle w) false) := by
    have h := hL (WordOps.init (WordOps.tail w)) ((WordOps.tail w) (Fin.last (n+1)))
    simpa only [WordOps.snoc_init_self,middle] using h
  have h := hC (WordOps.snoc w false)
  simpa only [image_snoc,hL,WordOps.init_snoc,tail_snoc,middle,hm,hl] using h

theorem cube_forces_equal {G : Type _} [GroupData G]
    (L : Bool → G) (M : Bool → Bool → G)
    (h : ∀ l c r, L (rule l c r)*M l c=M c r*L c) : L true=L false := by
  have h000 := h false false false
  have h001 := h false false true
  have h010 := h false true false
  have h011 := h false true true
  have h101 := h true false true
  have h110 := h true true false
  change L false*M false false=M false false*L false at h000
  change L true*M false false=M false true*L false at h001
  change L true*M false true=M true false*L true at h010
  change L true*M false true=M true true*L true at h011
  change L false*M true false=M false true*L false at h101
  change L false*M true true=M true false*L true at h110
  have hn : M true false=M true true := mul_right_cancel (h010.symm.trans h011)
  rw [←hn] at h110
  have hp : M false true=M false false :=
    mul_left_cancel (h010.trans (h110.symm.trans (h101.trans h001.symm)))
  rw [hp] at h001
  exact mul_right_cancel (h001.trans h000.symm)

theorem word1 (v : Word 1) : v=(fun _ => v 0) := by
  funext i
  have hi : i=0 := by apply Fin.ext;omega
  rw [hi]

theorem cocycle_one_equal {G : Type _} [GroupData G]
    (L : Word 1 → G) (M : Word 2 → G) (hC : Cocycle L M) :
    L (fun _ => true)=L (fun _ => false) := by
  apply cube_forces_equal (fun b => L (fun _ => b))
    (fun b c => M (WordOps.cons b (fun _ : Fin 1 => c)))
  intro l c r
  let w : Word 3 := WordOps.cons l (WordOps.cons c (fun _ : Fin 1 => r))
  have hi : image w=(fun _ : Fin 1 => rule l c r) := word1 _
  have hm : middle w=(fun _ : Fin 1 => c) := word1 _
  have hp : WordOps.init w=WordOps.cons l (fun _ : Fin 1 => c) := by
    rw [show w=WordOps.cons l (WordOps.cons c (fun _ : Fin 1 => r)) from rfl,init_cons]
    exact congrArg (fun v : Word 1 => @WordOps.cons 1 Bool l v) (word1 _)
  have h := hC w
  simpa only [hi,hm,hp,show WordOps.tail w=WordOps.cons c (fun _ : Fin 1 => r) from rfl] using h

theorem anchored_trivial {G : Type _} [GroupData G] :
    ∀ (n : Nat) (L : Word (n+1) → G) (M : Word (n+2) → G) (vac : G),
      Anchored L vac → Cocycle L M → ∀ w, L w=vac
  | 0,L,M,vac,hN,hC => by
    have ht := cocycle_one_equal L M hC
    intro w
    cases hb : w 0 with
    | false => exact hN w hb
    | true =>
      have hw : w=(fun _ : Fin 1 => true) := by
        funext i
        have hi : i=0 := by apply Fin.ext;omega
        simpa only [hi] using hb
      rw [hw]
      exact ht.trans (hN _ rfl)
  | n+1,L,M,vac,hN,hC => by
    have hL := normalized_forgets_last L M hN hC
    have hM := flux_forgets_last L M hL hC
    let L' (v : Word (n+1)) := L (WordOps.snoc v false)
    let M' (v : Word (n+2)) := M (WordOps.snoc v false)
    have hN' : Anchored L' vac := by
      intro v hv
      exact hN _ (by simpa using hv)
    have hC' : Cocycle L' M' := cocycle_shrink L M hL hM hC
    intro w
    have he := hL (WordOps.init w) (w (Fin.last (n+1)))
    rw [WordOps.snoc_init_self] at he
    exact he.trans (anchored_trivial n L' M' vac hN' hC' (WordOps.init w))

def zeros (n : Nat) : Word n := fun _ => false
def pad {n : Nat} (v : Word n) : Word n :=
  @WordOps.init n Bool (@WordOps.cons n Bool false v)

theorem pad_apply {n : Nat} (v : Word n) (i : Fin n) :
    pad v i=if i.val=0 then false else v ⟨i.val-1,by omega⟩ := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      simp [pad,WordOps.init,WordOps.cons]
      congr 1

theorem pad_bit_zero {n : Nat} (k : Nat) (v : Word n) (i : Fin n)
    (h : i.val<k) : (iterate pad k) v i=false := by
  induction k generalizing v i with
  | zero => omega
  | succ k ih =>
    rw [iterate_succ_apply',pad_apply]
    by_cases hi : i.val=0
    · simp only [hi,ite_true]
    · rw [ite_eq_right hi]
      have hidx : i.val-1<n := by omega
      have hk : i.val-1<k := by omega
      exact ih v ⟨i.val-1,hidx⟩ hk

theorem pad_all_zero {n : Nat} (v : Word n) : (iterate pad n) v=zeros n := by
  funext i
  exact pad_bit_zero n v i i.isLt

theorem cons_zero (n : Nat) : WordOps.cons false (zeros n)=zeros (n+1) := by
  funext i
  cases i using Fin.cases <;> rfl

def gaugePartial {G : Type _} [GroupData G] {n : Nat} (L : Word (n+1) → G) :
    Nat → Word n → G
  | 0,_ => 1
  | k+1,v => L (zeros (n+1))*gaugePartial L k (pad v)*(L (WordOps.cons false v))⁻¹

theorem gauge_stable {G : Type _} [GroupData G] {n : Nat} (L : Word (n+1) → G) :
    ∀ k v, (iterate pad k) v=zeros n → gaugePartial L (k+1) v=gaugePartial L k v
  | 0,v,h => by
    have hv : v=zeros n := h
    subst v
    simp [gaugePartial,cons_zero]
  | k+1,v,h => by
    change L (zeros (n+1))*gaugePartial L (k+1) (pad v)*(L (WordOps.cons false v))⁻¹=
      L (zeros (n+1))*gaugePartial L k (pad v)*(L (WordOps.cons false v))⁻¹
    rw [gauge_stable L k (pad v) (by simpa only [iterate_succ_apply] using h)]

def gauge {G : Type _} [GroupData G] {n : Nat} (L : Word (n+1) → G) : Word n → G :=
  gaugePartial L n

def edgeGauge {G : Type _} [GroupData G] {n : Nat}
    (g : Word n → G) (L : Word (n+1) → G) (w : Word (n+1)) : G :=
  g (WordOps.tail w)*L w*(g (WordOps.init w))⁻¹
def timeGauge {G : Type _} [GroupData G] {n : Nat}
    (g : Word n → G) (M : Word (n+2) → G) (w : Word (n+2)) : G :=
  g (image w)*M w*(g (middle w))⁻¹

theorem gauge_anchored {G : Type _} [GroupData G] {n : Nat} (L : Word (n+1) → G) :
    Anchored (edgeGauge (gauge L) L) (L (zeros (n+1))) := by
  intro w hw
  have he : w=WordOps.cons false (WordOps.tail w) := by
    have h := WordOps.cons_self_tail w
    rw [hw] at h
    exact h.symm
  rw [he]
  change gaugePartial L n (WordOps.tail w)*L (WordOps.cons false (WordOps.tail w))*
      (gaugePartial L n (pad (WordOps.tail w)))⁻¹=L (zeros (n+1))
  have hs := gauge_stable L n (WordOps.tail w) (pad_all_zero _)
  change L (zeros (n+1))*gaugePartial L n (pad (WordOps.tail w))*
      (L (WordOps.cons false (WordOps.tail w)))⁻¹=gaugePartial L n (WordOps.tail w) at hs
  rw [←hs]
  simp [mul_assoc]

theorem image_init {n : Nat} (w : Word (n+3)) :
    (image (WordOps.init w) : Word n)=WordOps.init (image w) := rfl
theorem image_tail {n : Nat} (w : Word (n+3)) :
    (image (WordOps.tail w) : Word n)=WordOps.tail (image w) := rfl
theorem middle_init {n : Nat} (w : Word (n+3)) :
    (middle (WordOps.init w) : Word n)=WordOps.init (middle w) := rfl
theorem middle_tail {n : Nat} (w : Word (n+3)) :
    (middle (WordOps.tail w) : Word n)=WordOps.tail (middle w) := rfl

theorem gauge_cocycle {G : Type _} [GroupData G] {n : Nat}
    (g : Word n → G) (L : Word (n+1) → G) (M : Word (n+2) → G)
    (hC : Cocycle L M) : Cocycle (edgeGauge g L) (timeGauge g M) := by
  intro w
  have h := congrArg (fun q : G => g (WordOps.tail (image w))*q*(g (WordOps.init (middle w)))⁻¹) (hC w)
  simpa only [edgeGauge,timeGauge,image_init,image_tail,middle_init,middle_tail,
    mul_assoc,inv_mul_cancel_left] using h

/-- Every homogeneous group-valued one-cell-halo Rule30 cocycle is a local
gauge of its constant vacuum connection. Neither finiteness nor commutativity
of the group is assumed. This is NOT center aperiodicity. -/
theorem cocycle_is_background_gauge {G : Type _} [GroupData G] {n : Nat}
    (L : Word (n+1) → G) (M : Word (n+2) → G) (hC : Cocycle L M) :
    ∃ g : Word n → G, ∀ w : Word (n+1),
      L w=(g (WordOps.tail w))⁻¹*L (zeros (n+1))*g (WordOps.init w) := by
  refine ⟨gauge L,?_⟩
  have hA := gauge_anchored L
  have hG := gauge_cocycle (gauge L) L M hC
  have ht := anchored_trivial n (edgeGauge (gauge L) L) (timeGauge (gauge L) M)
    (L (zeros (n+1))) hA hG
  intro w
  have he := congrArg (fun q : G => (gauge L (WordOps.tail w))⁻¹*q*gauge L (WordOps.init w)) (ht w)
  simpa only [edgeGauge,mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using he


/-- Pure-gauge examples exist: the classification does not say L is
pointwise constant before a change of vertex coordinates. -/
theorem background_gauges_are_cocycles {G : Type u} [GroupData G] {n : Nat}
    (g : Word n → G) (a : G) :
    Cocycle (edgeGauge g (fun _ : Word (n+1) => a))
      (timeGauge g (fun _ : Word (n+2) => 1)) := by
  apply gauge_cocycle
  intro w
  simp only [mul_one,one_mul]

def groupPower {G : Type u} [GroupData G] (a : G) : Nat → G
  | 0 => 1
  | k+1 => a*groupPower a k
def pathProduct {G : Type u} [GroupData G] {n : Nat}
    (L : Word (n+1) → G) (w : Nat → Word (n+1)) : Nat → G
  | 0 => 1
  | k+1 => L (w k)*pathProduct L w k

theorem path_background {G : Type u} [GroupData G] {n : Nat}
    (L : Word (n+1) → G) (g : Word n → G) (a : G)
    (hL : ∀ w, L w=(g (WordOps.tail w))⁻¹*a*g (WordOps.init w))
    (w : Nat → Word (n+1)) (v : Nat → Word n)
    (hs : ∀ i, WordOps.init (w i)=v i) (ht : ∀ i, WordOps.tail (w i)=v (i+1)) :
    ∀ N, pathProduct L w N=(g (v N))⁻¹*groupPower a N*g (v 0)
  | 0 => by simp [pathProduct,groupPower]
  | k+1 => by
    rw [pathProduct,hL,hs,ht,path_background L g a hL w v hs ht k]
    simp only [groupPower,mul_assoc,mul_inv_cancel_left]

/-- A cyclic product carries only the length and the vacuum conjugacy class. -/
theorem cyclic_products_background (G : Type) [GroupData G] (n : Nat)
    (L : Word (n+1) → G) (M : Word (n+2) → G) (hC : Cocycle L M)
    (w : Nat → Word (n+1)) (v : Nat → Word n)
    (hs : ∀ i, WordOps.init (w i)=v i) (ht : ∀ i, WordOps.tail (w i)=v (i+1))
    (N : Nat) (hc : v N=v 0) :
    ∃ h : G, pathProduct L w N=h⁻¹*groupPower (L (zeros (n+1))) N*h := by
  obtain ⟨g,hg⟩ := cocycle_is_background_gauge L M hC
  refine ⟨g (v 0),?_⟩
  have h := path_background L g (L (zeros (n+1))) hg w v hs ht N
  simpa only [hc] using h

/-- Multiplicative presentation of the two-element additive group. -/
@[instance_reducible] def xorGroup : GroupData Bool where
  mul := xor
  ofNat := false
  inv := id
  assoc := by intro a b c;cases a <;> cases b <;> cases c <;> rfl
  left_unit := by intro a;cases a <;> rfl
  right_unit := by intro a;cases a <;> rfl
  left_inverse := by intro a;cases a <;> rfl
  right_inverse := by intro a;cases a <;> rfl

theorem xor_flux_rearrange (a b c d : Bool) (h : xor a c=xor b d) :
    xor a b=xor d c := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases h <;> rfl

/-- The exact local-flux form of the additive F2 classification, for all
widths. No cyclic-to-local-flux equivalence is assumed or claimed here. -/
theorem boolean_flux_coboundary (n : Nat)
    (rho : Word (n+1) → Bool) (j : Word (n+2) → Bool)
    (h : ∀ w : Word (n+3), xor (rho (image w)) (rho (middle w))=
      xor (j (WordOps.init w)) (j (WordOps.tail w))) :
    ∃ g : Word n → Bool, ∀ w : Word (n+1), rho w=
      xor (xor (g (WordOps.tail w)) (rho (zeros (n+1)))) (g (WordOps.init w)) := by
  letI : GroupData Bool := xorGroup
  have hC : Cocycle rho j := by
    intro w
    exact xor_flux_rearrange _ _ _ _ (h w)
  obtain ⟨g,hg⟩ := cocycle_is_background_gauge rho j hC
  exact ⟨g,hg⟩

/-- A universe-zero headline for the official partial checker. No finiteness
or commutativity is assumed; the explicit GroupData are the standard laws. -/
theorem background_gauge_all_groups (G : Type) [GroupData G] (n : Nat)
    (L : Word (n+1) → G) (M : Word (n+2) → G) (hC : Cocycle L M) :
    ∃ g : Word n → G, ∀ w : Word (n+1),
      L w=(g (WordOps.tail w))⁻¹*L (zeros (n+1))*g (WordOps.init w) :=
  cocycle_is_background_gauge L M hC


/-- A twisted shift-constant function on finite words is constant: prepend
white cells until the entire word is white, and cancel the fixed twist. -/
theorem twisted_shift_constant {G : Type u} [GroupData G] (m : Nat)
    (a : G) (N : Word m → G)
    (h : ∀ w : Word (m+1), a*N (WordOps.init w)=N (WordOps.tail w)*a) :
    ∀ v, N v=N (zeros m) := by
  have hz : a*N (zeros m)=N (zeros m)*a := h (zeros (m+1))
  have descend : ∀ k v, iterate pad k v=zeros m → N v=N (zeros m) := by
    intro k
    induction k with
    | zero => intro v hv; exact congrArg N hv
    | succ k ih =>
      intro v hv
      have hp : iterate pad k (pad v)=zeros m := by
        simpa only [iterate_succ_apply] using hv
      have step := h (WordOps.cons false v)
      change a*N (pad v)=N v*a at step
      rw [ih (pad v) hp] at step
      exact mul_right_cancel (step.symm.trans hz)
  intro v
  exact descend m v (pad_all_zero v)

theorem gaugePartial_zero {G : Type u} [GroupData G] {n : Nat}
    (L : Word (n+1) → G) (k : Nat) : gaugePartial L k (zeros n)=1 := by
  have hp : pad (zeros n)=zeros n := congrArg WordOps.init (cons_zero n)
  induction k with
  | zero => rfl
  | succ k ih => simp only [gaugePartial,hp,ih,cons_zero,mul_one,mul_inv_cancel]

/-- Full spatial-and-temporal classification with the canonical gauge fixed
to the identity at the vacuum. The two vacuum constants commute. -/
theorem full_background_connection (G : Type) [GroupData G] (n : Nat)
    (L : Word (n+1) → G) (M : Word (n+2) → G) (hC : Cocycle L M) :
    ∃ g : Word n → G, g (zeros n)=1 ∧
      L (zeros (n+1))*M (zeros (n+2))=M (zeros (n+2))*L (zeros (n+1)) ∧
      (∀ w : Word (n+1), L w=(g (WordOps.tail w))⁻¹*L (zeros (n+1))*g (WordOps.init w)) ∧
      (∀ w : Word (n+2), M w=(g (image w))⁻¹*M (zeros (n+2))*g (middle w)) := by
  let g := gauge L
  have hzero : g (zeros n)=1 := gaugePartial_zero L n
  have ht := anchored_trivial n (edgeGauge g L) (timeGauge g M)
    (L (zeros (n+1))) (gauge_anchored L) (gauge_cocycle g L M hC)
  have hN : ∀ w : Word (n+3),
      L (zeros (n+1))*timeGauge g M (WordOps.init w)=
        timeGauge g M (WordOps.tail w)*L (zeros (n+1)) := by
    intro w
    have h := gauge_cocycle g L M hC w
    simpa only [ht] using h
  have hc := twisted_shift_constant (n+2) (L (zeros (n+1))) (timeGauge g M) hN
  have hzimage : image (zeros (n+2))=zeros n := by funext i; rfl
  have hzmiddle : middle (zeros (n+2))=zeros n := rfl
  have hzM : timeGauge g M (zeros (n+2))=M (zeros (n+2)) := by
    have hi : Inv.inv (1 : G)=1 := by simpa only [mul_one] using (inv_mul_cancel (1 : G))
    simp only [timeGauge,hzimage,hzmiddle,hzero,hi,one_mul,mul_one]
  refine ⟨g,hzero,hC (zeros (n+3)),?_,?_⟩
  · intro w
    have he := congrArg (fun q : G => (g (WordOps.tail w))⁻¹*q*g (WordOps.init w)) (ht w)
    simpa only [edgeGauge,mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using he
  · intro w
    have he := congrArg (fun q : G => (g (image w))⁻¹*q*g (middle w)) ((hc w).trans hzM)
    simpa only [timeGauge,mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using he

/-- Commuting constant backgrounds give honest positive controls for both
parts of the connection, with arbitrary local vertex gauge. -/
theorem commuting_backgrounds_are_cocycles {G : Type u} [GroupData G] {n : Nat}
    (g : Word n → G) (a b : G) (hab : a*b=b*a) :
    Cocycle (edgeGauge g (fun _ : Word (n+1) => a))
      (timeGauge g (fun _ : Word (n+2) => b)) := by
  apply gauge_cocycle
  intro w
  exact hab


/-- Place an independently chosen local support inside a common finite window.
Unused cells on either side are padding, not a minimal-range assumption. -/
def window (offset length : Nat) {ambient : Nat} (h : offset+length≤ambient)
    (w : Word ambient) : Word length := fun i => w ⟨offset+i.val,by omega⟩

@[simp] theorem window_zeros (offset length ambient : Nat)
    (h : offset+length≤ambient) : window offset length h (zeros ambient)=zeros length := rfl

/-- The spatial and temporal supports can be chosen independently, with arbitrary
offsets and unused padding in a common input window. This removes the apparent
minimal-halo restriction: any bounded local supports can be enlarged to this
container, without changing their functions. The gauge is local in that container.
This is still a group-valued homogeneous flat connection, not every invariant. -/
theorem arbitrary_local_supports (G : Type) [GroupData G]
    (N n m r s : Nat) (hr : r+(n+1)≤N+1) (hs : s+(m+1)≤N+2)
    (L : Word (n+1) → G) (M : Word (m+1) → G)
    (h : ∀ w : Word (N+3),
      L (window r (n+1) hr (image w))*M (window s (m+1) hs (WordOps.init w))=
      M (window s (m+1) hs (WordOps.tail w))*L (window r (n+1) hr (middle w))) :
    ∃ g : Word N → G, g (zeros N)=1 ∧
      L (zeros (n+1))*M (zeros (m+1))=M (zeros (m+1))*L (zeros (n+1)) ∧
      (∀ v : Word (N+1), L (window r (n+1) hr v)=
        (g (WordOps.tail v))⁻¹*L (zeros (n+1))*g (WordOps.init v)) ∧
      (∀ v : Word (N+2), M (window s (m+1) hs v)=
        (g (image v))⁻¹*M (zeros (m+1))*g (middle v)) := by
  have hc : Cocycle (fun v => L (window r (n+1) hr v))
      (fun v => M (window s (m+1) hs v)) := h
  simpa only [window_zeros] using
    full_background_connection G N (fun v => L (window r (n+1) hr v))
      (fun v => M (window s (m+1) hs v)) hc

/-! ## Inversion involution `(a⁻¹)⁻¹ = a` and anti-homomorphism `(a * b)⁻¹ = b⁻¹ * a⁻¹` for `GroupData` -/

/-- **Inversion Involution and Anti-Homomorphism Laws for `GroupData` (`groupData_inv_inv_and_mul_inv_rev`).** -/
theorem groupData_inv_inv_and_mul_inv_rev
    (G : Type) [GroupData G] (a b : G) :
    (1 : G)⁻¹ = 1 ∧
    (a⁻¹)⁻¹ = a ∧
    (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [mul_one] using inv_mul_cancel (1 : G)
  · apply mul_left_cancel (a := a⁻¹)
    rw [mul_inv_cancel, inv_mul_cancel]
  · apply mul_left_cancel (a := a * b)
    rw [mul_inv_cancel, mul_assoc, ← mul_assoc b, mul_inv_cancel, one_mul, mul_inv_cancel]

end Ruliology.CellularAutomata.Rule30GroupCocycle
