module

public import Init.Data.Fin.Lemmas
public import Ruliology.CellularAutomata.Rule30Prize

/-!
# Product parity conservation, uniformly in window width

All-width mod-two local conservation classification for any coordinatewise
product of Rule30. Every cyclically conserved finite-window parity score is
constant plus a spatial coboundary, and conversely. The conserved change is
for FOUR shrinking Rule30 steps, as the semantics theorem verifies.

No fixed window cutoff, local-current hypothesis, or finite-ring census is
a premise. This core-only specialization extends the integer scalar
range-reduction argument of Rule30LocalConservation to coordinatewise
products and Fin2 coefficients with their core modular addition/subtraction.
-/

@[expose] public section
universe u
namespace Ruliology.CellularAutomata.Rule30ProductParity
variable {ι : Type u}

theorem sub_eq_zero : ∀ {a b : Fin 2}, a-b=0 ↔ a=b := by decide +kernel
theorem sub_right_inj : ∀ {a b c : Fin 2}, a-b=a-c ↔ b=c := by decide +kernel
@[simp] theorem p_add_sub_cancel : ∀ a b : Fin 2, a+b-b=a := by decide +kernel
@[simp] theorem p_zero_add : ∀ a : Fin 2, 0+a=a := by decide +kernel
@[simp] theorem p_add_zero : ∀ a : Fin 2, a+0=a := by decide +kernel
@[simp] theorem p_sub_zero : ∀ a : Fin 2, a-0=a := by decide +kernel
@[simp] theorem p_sub_self : ∀ a : Fin 2, a-a=0 := by decide +kernel
theorem p_sub_as_add : ∀ a b : Fin 2, a-b=a+b := by decide +kernel
theorem p_add_assoc : ∀ a b c : Fin 2, (a+b)+c=a+(b+c) := by decide +kernel
theorem p_add_comm : ∀ a b : Fin 2, a+b=b+a := by decide +kernel
theorem p_add_left_comm : ∀ a b c : Fin 2, a+(b+c)=b+(a+c) := by decide +kernel
theorem p_cancel_pair : ∀ a b : Fin 2, a+(a+b)=b := by decide +kernel
theorem p_add_self : ∀ a : Fin 2, a+a=0 := by decide +kernel

macro "rule30_parity_nf" : tactic => `(tactic|
  simp only [p_sub_as_add,p_add_assoc,p_add_comm,p_add_left_comm,p_cancel_pair,
    p_add_self,p_add_zero,p_zero_add])

abbrev Cell (ι : Type u) := ι → Bool
def zeroCell : Cell ι := fun _ => false
def bxor (a b : Cell ι) : Cell ι := fun i => xor (a i) (b i)
theorem bxor_cancel (a b : Cell ι) : bxor (bxor a b) b=a := by
  funext i
  change xor (xor (a i) (b i)) (b i)=a i
  cases a i <;> cases b i <;> rfl
theorem bxor_self (a : Cell ι) : bxor a a=zeroCell := by
  funext i
  change xor (a i) (a i)=false
  cases a i <;> rfl
theorem bxor_zero_left (a : Cell ι) : bxor zeroCell a=a := by
  funext i
  change xor false (a i)=a i
  cases a i <;> rfl

namespace Corner
def rule (a b c : Cell ι) : Cell ι := fun i =>
  Ruliology.CellularAutomata.Rule30Jen.rule (a i) (b i) (c i)
def shrink : List (Cell ι) → List (Cell ι)
  | a::b::c::xs => rule a b c :: shrink (b::c::xs)
  | _ => []
def four (xs : List (Cell ι)) : List (Cell ι) := shrink (shrink (shrink (shrink xs)))
def scalarShrink : List Bool → List Bool
  | a::b::c::xs => Ruliology.CellularAutomata.Rule30Jen.rule a b c :: scalarShrink (b::c::xs)
  | _ => []
def scalarQ9 (a b c d e f g h i : Bool) : Bool :=
  (scalarShrink (scalarShrink (scalarShrink (scalarShrink [a,b,c,d,e,f,g,h,i])))).headD false
theorem scalar_left : ∀ a b c d e f g h i : Bool,
    scalarQ9 a b c d e f g h i=xor a (scalarQ9 false b c d e f g h i) := by decide +kernel
theorem scalar_right : ∀ a b : Bool,
    scalarQ9 a false false false false false false false b=xor a b := by decide +kernel
theorem scalar_diag : ∀ a : Bool, scalarQ9 a a a a a a a a a=false := by decide +kernel
def q9 (a b c d e f g h i : Cell ι) : Cell ι :=
  (four [a,b,c,d,e,f,g,h,i]).headD zeroCell
def q (a : Cell ι) (xs : List (Cell ι)) : Cell ι :=
  q9 a (xs.getD 0 zeroCell) (xs.getD 1 zeroCell) (xs.getD 2 zeroCell) (xs.getD 3 zeroCell)
    (xs.getD 4 zeroCell) (xs.getD 5 zeroCell) (xs.getD 6 zeroCell) (xs.getD 7 zeroCell)
theorem q9_left : ∀ a b c d e f g h i : Cell ι,
    q9 a b c d e f g h i=bxor a (q9 zeroCell b c d e f g h i) := by
  intro a b c d e f g h i
  funext j
  change scalarQ9 (a j) (b j) (c j) (d j) (e j) (f j) (g j) (h j) (i j)=
    xor (a j) (scalarQ9 false (b j) (c j) (d j) (e j) (f j) (g j) (h j) (i j))
  exact scalar_left _ _ _ _ _ _ _ _ _
theorem q_left (a : Cell ι) (xs : List (Cell ι)) : q a xs=bxor a (q zeroCell xs) :=
  q9_left a _ _ _ _ _ _ _ _
theorem q9_right_zero (a b : Cell ι) :
    q9 a zeroCell zeroCell zeroCell zeroCell zeroCell zeroCell zeroCell b=bxor a b := by
  funext j
  change scalarQ9 (a j) false false false false false false false (b j)=xor (a j) (b j)
  exact scalar_right _ _
theorem q9_diag (a : Cell ι) : q9 a a a a a a a a a=zeroCell := by
  funext j
  change scalarQ9 (a j) (a j) (a j) (a j) (a j) (a j) (a j) (a j) (a j)=false
  exact scalar_diag _

theorem getD_append_prefix (xs ys : List (Cell ι)) (i : Nat) (hi : i<xs.length) :
    (xs++ys).getD i zeroCell=xs.getD i zeroCell := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left hi]

theorem q_append (a b : Cell ι) (xs : List (Cell ι)) (hx : 8≤xs.length) :
    q a (xs++[b])=q a xs := by
  unfold q
  congr 1 <;> apply getD_append_prefix <;> omega

def image : List (Cell ι) → List (Cell ι)
  | [] => []
  | a::xs => if 8≤xs.length then q a xs :: image xs else []

def preimage : List (Cell ι) → List (Cell ι)
  | [] => List.replicate 8 zeroCell
  | b::xs => let tail:=preimage xs; bxor b (q zeroCell tail) :: tail

theorem preimage_length (xs : List (Cell ι)) : (preimage xs).length=xs.length+8 := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [preimage,ih]

/-- Constructive arbitrary-length preimages with eight trailing white cells. -/
theorem image_preimage (xs : List (Cell ι)) : image (preimage xs)=xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    have hp : 8≤(preimage xs).length := by rw [preimage_length]; omega
    have hq : q (bxor b (q zeroCell (preimage xs))) (preimage xs)=b := by
      rw [q_left]
      exact bxor_cancel _ _
    simp only [preimage,image,ite_eq_left hp,hq,ih]

theorem preimage_suffix (xs : List (Cell ι)) :
    ∃ u, preimage xs=u++List.replicate 8 zeroCell := by
  induction xs with
  | nil => exact ⟨[],rfl⟩
  | cons b xs ih =>
    obtain ⟨u,hu⟩ := ih
    exact ⟨bxor b (q zeroCell (preimage xs))::u,by simp only [preimage,hu,List.cons_append]⟩

theorem image_nine (a b : Cell ι) :
    image (a::(List.replicate 7 zeroCell++[b]))=[bxor a b] := by
  change [q9 a zeroCell zeroCell zeroCell zeroCell zeroCell zeroCell zeroCell b]=[bxor a b]
  rw [q9_right_zero]

theorem image_white_suffix (u : List (Cell ι)) (b : Cell ι) :
    image (u++List.replicate 8 zeroCell++[b])=
      image (u++List.replicate 8 zeroCell)++[b] := by
  induction u with
  | nil =>
    change image (zeroCell::(List.replicate 7 zeroCell++[b]))=[b]
    rw [image_nine,bxor_zero_left]
  | cons a u ih =>
    have hx : 8≤(u++List.replicate 8 zeroCell).length := by simp
    have hy : 8≤((u++List.replicate 8 zeroCell)++[b]).length := by simp
    simp only [List.cons_append,image,ite_eq_left hx,ite_eq_left hy,q_append a b _ hx,ih]

/-- Two freely chosen outer input cells vary only the two endpoint outputs;
the desired interior is arbitrary and has unbounded length. -/
theorem image_rectangle (a b : Cell ι) (ys : List (Cell ι)) :
    image (a::(preimage ys++[b]))=
      bxor a (q zeroCell (preimage ys)) :: (ys++[b]) := by
  obtain ⟨u,hu⟩ := preimage_suffix ys
  have hs := image_white_suffix (a::u) b
  simp only [List.cons_append,←hu] at hs
  rw [hs]
  have hp : 8≤(preimage ys).length := by rw [preimage_length]; omega
  simp only [image,ite_eq_left hp,image_preimage,List.cons_append]
  exact congrArg (fun z => z::(ys++[b])) (q_left a (preimage ys))

/-- Local conservation with a potential on the maximal proper input window.
Input length m+8 represents the exact four-step radius-four light cone.
The old density's window omits the two outer input cells. -/
def Conserved (m : Nat) (h p : List (Cell ι) → (Fin 2)) : Prop :=
  ∀ mid : List (Cell ι), mid.length=m+6 → ∀ a b : Cell ι,
    h (image (a::(mid++[b])))=
      h ((mid.drop 3).take m)+p (a::mid)-p (mid++[b])

/-- Every conserved density at ANY window length >=2 has zero endpoint
mixed difference. This is the uniform range-reduction obstruction. -/
theorem conserved_rectangle (ys : List (Cell ι)) (h p : List (Cell ι) → (Fin 2))
    (hc : Conserved (ys.length+2) h p) (a b : Cell ι) :
    h (a::(ys++[b]))=h (a::(ys++[zeroCell]))+
      h (zeroCell::(ys++[b]))-h (zeroCell::(ys++[zeroCell])) := by
  let q0 := q zeroCell (preimage ys)
  have hl : (preimage ys).length=ys.length+2+6 := by rw [preimage_length]
  have h00 := hc (preimage ys) hl q0 zeroCell
  have h01 := hc (preimage ys) hl q0 b
  have h10 := hc (preimage ys) hl (bxor a q0) zeroCell
  have h11 := hc (preimage ys) hl (bxor a q0) b
  rw [image_rectangle] at h00 h01 h10 h11
  change h (bxor q0 q0::(ys++[zeroCell]))=_ at h00
  change h (bxor q0 q0::(ys++[b]))=_ at h01
  change h (bxor (bxor a q0) q0::(ys++[zeroCell]))=_ at h10
  change h (bxor (bxor a q0) q0::(ys++[b]))=_ at h11
  simp only [bxor_self,bxor_cancel] at h00 h01 h10 h11
  rw [h11,h10,h01,h00]
  rule30_parity_nf

def potential (h : List (Cell ι) → (Fin 2)) (u : List (Cell ι)) : (Fin 2) := h (zeroCell::u)

def shorter (h : List (Cell ι) → (Fin 2)) (u : List (Cell ι)) : (Fin 2) :=
  h (u++[zeroCell])-h (zeroCell::(u.tail++[zeroCell]))+h (zeroCell::u)

/-- Explicit cohomology to a shorter local density. No positivity assumption
on the score or on the potential is used. -/
theorem shorten_density (ys : List (Cell ι)) (h p : List (Cell ι) → (Fin 2))
    (hc : Conserved (ys.length+2) h p) (a b : Cell ι) :
    h (a::(ys++[b]))=shorter h (a::ys)+
      potential h (ys++[b])-potential h (a::ys) := by
  have hr := conserved_rectangle ys h p hc a b
  unfold shorter potential
  simp only [List.cons_append,List.tail_cons]
  apply sub_eq_zero.mp
  simpa only [p_sub_as_add,p_add_assoc,p_add_comm,p_add_left_comm,p_cancel_pair,p_add_self,p_add_zero,p_zero_add] using (sub_eq_zero.mpr hr)

end Corner

/-! Word semantics, compact conservation potentials, and the one-cell base
case for the uniform conservation-law range-reduction argument. -/
namespace Word
open Corner

theorem shrink_length (xs : List (Cell ι)) : (shrink xs).length=xs.length-2 := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases xs with
    | nil => rfl
    | cons b xs =>
      cases xs with
      | nil => rfl
      | cons c xs =>
        change (shrink (b::c::xs)).length+1=(xs.length+3)-2
        have hh : (shrink (b::c::xs)).length=xs.length := by simpa using ih
        rw [hh]
        omega

theorem four_length (xs : List (Cell ι)) : (four xs).length=xs.length-8 := by
  simp only [four,shrink_length]
  omega

theorem four_cons (a : Cell ι) (xs : List (Cell ι)) (hx : 8≤xs.length) :
    four (a::xs)=q a xs::four xs := by
  cases xs with
  | nil => simp at hx
  | cons b xs =>
    cases xs with
    | nil => simp at hx
    | cons c xs =>
      cases xs with
      | nil => simp at hx
      | cons d xs =>
        cases xs with
        | nil => simp at hx
        | cons e xs =>
          cases xs with
          | nil => simp at hx
          | cons f xs =>
            cases xs with
            | nil => simp at hx
            | cons g xs =>
              cases xs with
              | nil => simp at hx
              | cons h xs =>
                cases xs with
                | nil => simp at hx
                | cons i xs => rfl

/-- The sliding nine-cell rule is exactly four physical Rule30 updates
on the whole input word, retaining its complete interior light cone. -/
theorem image_eq_four (xs : List (Cell ι)) : image xs=four xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    by_cases hx : 8≤xs.length
    · rw [image,ite_eq_left hx,four_cons a xs hx,ih]
    · have he : four (a::xs)=[] := by
        apply List.eq_nil_of_length_eq_zero
        rw [four_length]
        simp only [List.length_cons]
        omega
      simp only [image,ite_eq_right hx,he]

theorem image_length (xs : List (Cell ι)) : (image xs).length=xs.length-8 := by
  rw [image_eq_four,four_length]

theorem image_tail (xs : List (Cell ι)) : (image xs).tail=image xs.tail := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    by_cases hx : 8≤xs.length
    · simp only [image,ite_eq_left hx,List.tail_cons]
    · have he : image xs=[] := by
        apply List.eq_nil_of_length_eq_zero
        rw [image_length]
        omega
      simp only [image,ite_eq_right hx,List.tail_cons,List.tail_nil,he]

theorem image_append_dropLast (xs : List (Cell ι)) (b : Cell ι) :
    (image (xs++[b])).dropLast=image xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    by_cases hx : 8≤xs.length
    · have hy : 8≤(xs++[b]).length := by simp only [List.length_append,List.length_singleton]; omega
      have hn : image (xs++[b])≠[] := by
        intro he
        have hl := image_length (xs++[b])
        rw [he] at hl
        simp only [List.length_nil,List.length_append,List.length_singleton] at hl
        omega
      simp only [List.cons_append,image,ite_eq_left hx,ite_eq_left hy,q_append a b xs hx]
      rw [List.dropLast_cons_of_ne_nil hn,ih]
    · have he : (image ((a::xs)++[b])).dropLast=[] := by
        apply List.eq_nil_of_length_eq_zero
        rw [List.length_dropLast,image_length]
        simp only [List.length_append,List.length_cons,List.length_nil]
        omega
      rw [he]
      simp only [image,ite_eq_right hx]

theorem image_dropLast (xs : List (Cell ι)) : image xs.dropLast=(image xs).dropLast := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    have he := List.dropLast_concat_getLast (List.cons_ne_nil a xs)
    have hh := image_append_dropLast (a::xs).dropLast ((a::xs).getLast (List.cons_ne_nil a xs))
    rw [he] at hh
    exact hh.symm

def crop (m : Nat) (xs : List (Cell ι)) : List (Cell ι) := (xs.drop 4).take m

theorem crop_outer (m : Nat) (mid : List (Cell ι)) (hm : mid.length=m+6) (a b : Cell ι) :
    crop m (a::(mid++[b]))=(mid.drop 3).take m := by
  unfold crop
  rw [List.drop_succ_cons,List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by simp only [List.length_drop]; omega)]

theorem conserved_word (m : Nat) (h p : List (Cell ι) → (Fin 2)) (hc : Conserved m h p)
    (xs : List (Cell ι)) (hx : xs.length=m+8) :
    h (image xs)=h (crop m xs)+p xs.dropLast-p xs.tail := by
  cases xs with
  | nil => simp at hx
  | cons a xs =>
    have hn : xs≠[] := by intro he; simp [he] at hx
    let b:=xs.getLast hn
    let mid:=xs.dropLast
    have he : mid++[b]=xs := List.dropLast_concat_getLast hn
    have hm : mid.length=m+6 := by simp only [mid,List.length_dropLast] at *; simp only [List.length_cons] at hx; omega
    have hh := hc mid hm a b
    rw [←crop_outer m mid hm a b] at hh
    simpa only [List.dropLast_concat,List.tail_cons,List.dropLast_cons_of_ne_nil hn,mid,he] using hh

theorem conserved_one_constant (h p : List (Cell ι) → (Fin 2)) (hc : Conserved 1 h p)
    (a : Cell ι) : h [zeroCell]=h [a] := by
  have old := hc (List.replicate 7 a) (by simp) a a
  have himg : image (a::(List.replicate 7 a++[a]))=[zeroCell] := by
    change [q9 a a a a a a a a a]=[zeroCell]
    rw [q9_diag]
  rw [himg] at old
  change h [zeroCell]=h [a]+p (List.replicate 8 a)-p (List.replicate 8 a) at old
  simpa using old

end Word

/-! Preserve the conservation equation while shortening its density. The
potential is compressed by proving independence of its final input bit. -/
namespace Descent
open Corner Word

theorem crop_length (m : Nat) (xs : List (Cell ι)) (hx : m+4≤xs.length) :
    (crop m xs).length=m := by
  simp only [crop,List.length_take,List.length_drop]
  omega

theorem tail_take_succ (m : Nat) (xs : List (Cell ι)) :
    (xs.take (m+1)).tail=xs.tail.take m := by cases xs <;> simp

theorem crop_tail (m : Nat) (xs : List (Cell ι)) :
    (crop (m+1) xs).tail=crop m xs.tail := by
  unfold crop
  rw [tail_take_succ,List.tail_drop,List.drop_tail]

theorem crop_dropLast (m : Nat) (xs : List (Cell ι)) (hx : m+5≤xs.length) :
    (crop (m+1) xs).dropLast=crop m xs := by
  unfold crop
  have hi : m<(xs.drop 4).length := by simp only [List.length_drop]; omega
  rw [List.take_succ_eq_append_getElem hi,List.dropLast_concat]

theorem crop_append (m : Nat) (xs : List (Cell ι)) (hx : xs.length=m+8) (b : Cell ι) :
    crop m (xs++[b])=crop m xs := by
  unfold crop
  rw [List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by simp only [List.length_drop]; omega)]

theorem conserved_of_word (m : Nat) (h p : List (Cell ι) → (Fin 2))
    (hc : ∀ xs, xs.length=m+8 →
      h (image xs)=h (crop m xs)+p xs.dropLast-p xs.tail) : Conserved m h p := by
  intro mid hm a b
  have hx : (a::(mid++[b])).length=m+8 := by simp [hm,Nat.add_assoc]
  have hh:=hc (a::(mid++[b])) hx
  have hp : (a::(mid++[b])).dropLast=a::mid := by
    change ((a::mid)++[b]).dropLast=a::mid
    exact List.dropLast_concat
  simpa only [crop_outer m mid hm a b,hp,List.tail_cons] using hh

theorem shorten_word (m : Nat) (hm : 1≤m) (h p : List (Cell ι) → (Fin 2))
    (hc : Conserved (m+1) h p) (xs : List (Cell ι)) (hx : xs.length=m+1) :
    h xs=shorter h xs.dropLast+potential h xs.tail-potential h xs.dropLast := by
  cases xs with
  | nil => simp at hx
  | cons a xs =>
    have hn : xs≠[] := by intro he; simp [he] at hx; omega
    let b:=xs.getLast hn
    let ys:=xs.dropLast
    have he : ys++[b]=xs := List.dropLast_concat_getLast hn
    have hl : ys.length+2=m+1 := by simp only [ys,List.length_dropLast,List.length_cons] at *; omega
    have hc' : Conserved (ys.length+2) h p := by rw [hl]; exact hc
    have hh:=shorten_density ys h p hc' a b
    simpa only [List.dropLast_concat,List.tail_cons,List.dropLast_cons_of_ne_nil hn,ys,he] using hh

def transport (m : Nat) (h p : List (Cell ι) → (Fin 2)) (xs : List (Cell ι)) : (Fin 2) :=
  p xs+potential h (image xs)-potential h (crop m xs)

theorem transport_identity (m : Nat) (hm : 1≤m) (h p : List (Cell ι) → (Fin 2))
    (hc : Conserved (m+1) h p) (xs : List (Cell ι)) (hx : xs.length=m+8) (b : Cell ι) :
    shorter h (image xs)=shorter h (crop m xs)+
      transport m h p xs-transport m h p (xs.tail++[b]) := by
  let w:=xs++[b]
  have hw : w.length=(m+1)+8 := by simp [w,hx,Nat.add_assoc]
  have hn : xs≠[] := by intro he; simp [he] at hx
  have ht : w.tail=xs.tail++[b] := by cases xs <;> simp_all [w]
  have old:=conserved_word (m+1) h p hc w hw
  have hi:=shorten_word m hm h p hc (image w) (by rw [image_length,hw]; omega)
  have hcword:=shorten_word m hm h p hc (crop (m+1) w) (crop_length _ _ (by omega))
  rw [hi,hcword] at old
  have ip : (image w).dropLast=image xs := image_append_dropLast xs b
  have it : (image w).tail=image (xs.tail++[b]) := by rw [image_tail,ht]
  have cp : (crop (m+1) w).dropLast=crop m xs := by
    rw [crop_dropLast m w (by omega),crop_append m xs hx b]
  have ct : (crop (m+1) w).tail=crop m (xs.tail++[b]) := by rw [crop_tail,ht]
  have wp : w.dropLast=xs := List.dropLast_concat
  rw [ip,it,cp,ct,wp,ht] at old
  unfold transport
  apply sub_eq_zero.mp
  simpa only [p_sub_as_add,p_add_assoc,p_add_comm,p_add_left_comm,p_cancel_pair,p_add_self,p_add_zero,p_zero_add] using (sub_eq_zero.mpr old)

theorem transport_last_independent (m : Nat) (hm : 1≤m) (h p : List (Cell ι) → (Fin 2))
    (hc : Conserved (m+1) h p) (xs : List (Cell ι)) (hx : xs.length=m+7) (b : Cell ι) :
    transport m h p (xs++[zeroCell])=transport m h p (xs++[b]) := by
  have hl : (zeroCell::xs).length=m+8 := by simp [hx,Nat.add_assoc]
  have h0 := transport_identity m hm h p hc (zeroCell::xs) hl zeroCell
  have h1 := transport_identity m hm h p hc (zeroCell::xs) hl b
  simp only [List.tail_cons] at h0 h1
  exact sub_right_inj.mp (h0.symm.trans h1)

def reducedPotential (m : Nat) (h p : List (Cell ι) → (Fin 2)) (xs : List (Cell ι)) : (Fin 2) :=
  transport m h p (xs++[zeroCell])

theorem transport_reduced (m : Nat) (hm : 1≤m) (h p : List (Cell ι) → (Fin 2))
    (hc : Conserved (m+1) h p) (xs : List (Cell ι)) (hx : xs.length=m+8) :
    transport m h p xs=reducedPotential m h p xs.dropLast := by
  have hn : xs≠[] := by intro he; simp [he] at hx
  let b:=xs.getLast hn
  have he : xs.dropLast++[b]=xs := List.dropLast_concat_getLast hn
  have hl : xs.dropLast.length=m+7 := by rw [List.length_dropLast,hx]; omega
  have hi := transport_last_independent m hm h p hc xs.dropLast hl b
  unfold reducedPotential
  rw [←he]
  simp only [List.dropLast_concat]
  exact hi.symm

/-- The explicit shorter density again has a potential of the proper compact
window length. This is the induction step, uniformly for every m>=1. -/
theorem shorter_conserved (m : Nat) (hm : 1≤m) (h p : List (Cell ι) → (Fin 2))
    (hc : Conserved (m+1) h p) :
    Conserved m (shorter h) (reducedPotential m h p) := by
  apply conserved_of_word
  intro xs hx
  have hh:=transport_identity m hm h p hc xs hx zeroCell
  rw [transport_reduced m hm h p hc xs hx] at hh
  exact hh

end Descent

/-! All parity local densities satisfying the explicit compact four-step
conservation equation are constant plus a shift coboundary, at every width.
The passage from a Rule30 ranking premise to conservation remains separate. -/
namespace Triviality
open Corner Word
open Descent

def Trivial (m : Nat) (h : List (Cell ι) → (Fin 2)) : Prop :=
  ∃ c : (Fin 2), ∃ p : List (Cell ι) → (Fin 2), ∀ xs, xs.length=m →
    h xs=c+p xs.tail-p xs.dropLast

theorem trivial_one (h p : List (Cell ι) → (Fin 2)) (hc : Conserved 1 h p) : Trivial 1 h := by
  refine ⟨h [zeroCell],fun _=>0,?_⟩
  intro xs hx
  cases xs with
  | nil => simp at hx
  | cons a xs =>
    have he : xs=[] := by
      apply List.eq_nil_of_length_eq_zero
      simp only [List.length_cons] at hx
      omega
    subst xs
    simpa using (conserved_one_constant h p hc a).symm

/-- No fixed cutoff on m: the local-potential equation has only constant and
telescoping solutions at every positive window length. -/
theorem conserved_trivial : ∀ m : Nat, 0<m → ∀ h p : List (Cell ι) → (Fin 2),
    Conserved m h p → Trivial m h := by
  intro m
  induction m with
  | zero => intro hm; omega
  | succ m ih =>
    intro _ h p hc
    by_cases hz : m=0
    · subst m; exact trivial_one h p hc
    have hm : 0<m := by omega
    have hs:=shorter_conserved m (by omega) h p hc
    obtain ⟨c,b,hb⟩:=ih hm (shorter h) (reducedPotential m h p) hs
    refine ⟨c,fun u=>potential h u+b u.dropLast,?_⟩
    intro xs hx
    have hh:=shorten_word m (by omega) h p hc xs hx
    have hl : xs.dropLast.length=m := by rw [List.length_dropLast,hx]; omega
    rw [hb xs.dropLast hl,List.tail_dropLast] at hh
    dsimp only
    apply sub_eq_zero.mp
    simpa only [p_sub_as_add,p_add_assoc,p_add_comm,p_add_left_comm,p_cancel_pair,p_add_self,p_add_zero,p_zero_add] using (sub_eq_zero.mpr hh)

end Triviality

namespace Cycle
open Corner Word
open Descent Triviality

def shift (xs : List (Cell ι)) (b : Cell ι) : List (Cell ι) := (xs++[b]).drop 1

def run : List (Cell ι) → List (Cell ι) → List (Cell ι)
  | xs, [] => xs
  | xs, b::bs => run (shift xs b) bs

def weight (cost : List (Cell ι) → (Fin 2)) : List (Cell ι) → List (Cell ι) → (Fin 2)
  | _, [] => 0
  | xs, b::bs => cost (xs++[b])+weight cost (shift xs b) bs

theorem shift_length (xs : List (Cell ι)) (b : Cell ι) : (shift xs b).length=xs.length := by
  simp [shift]

theorem run_append (xs bs cs : List (Cell ι)) : run xs (bs++cs)=run (run xs bs) cs := by
  induction bs generalizing xs with
  | nil => rfl
  | cons b bs ih => exact ih (shift xs b)

theorem weight_append (cost : List (Cell ι) → (Fin 2)) (xs bs cs : List (Cell ι)) :
    weight cost xs (bs++cs)=weight cost xs bs+weight cost (run xs bs) cs := by
  induction bs generalizing xs with
  | nil => simp [weight,run]
  | cons b bs ih => simp only [List.cons_append,weight,run,ih]; rule30_parity_nf

theorem run_formula (xs bs : List (Cell ι)) : run xs bs=(xs++bs).drop bs.length := by
  induction bs generalizing xs with
  | nil => simp [run]
  | cons b bs ih =>
    rw [run,ih]
    unfold shift
    rw [← List.drop_append_of_le_length (by simp : 1≤(xs++[b]).length)]
    rw [List.drop_drop]
    simp only [List.append_assoc,List.singleton_append,List.length_cons]
    congr 1
    omega

theorem run_reset (xs bs : List (Cell ι)) (hl : xs.length=bs.length) : run xs bs=bs := by
  rw [run_formula,←hl,List.drop_append_length]

def Balanced (n : Nat) (cost : List (Cell ι) → (Fin 2)) : Prop :=
  ∀ xs, xs.length=n → ∀ bs, run xs bs=xs → weight cost xs bs=0

/-- Compare two closed walks through a common all-white state. Every width is
handled at once; no finite graph census is a premise. -/
theorem balanced_gradient (n : Nat) (cost : List (Cell ι) → (Fin 2)) (hc : Balanced n cost) :
    ∃ p : List (Cell ι) → (Fin 2), ∀ xs, xs.length=n → ∀ b,
      cost (xs++[b])=p xs-p (shift xs b) := by
  let z : List (Cell ι) := List.replicate n zeroCell
  let p := fun xs=>weight cost xs z
  refine ⟨p,?_⟩
  intro xs hl b
  have hz : z.length=n := List.length_replicate
  have hs : (shift xs b).length=n := by rw [shift_length,hl]
  have hr : run xs z=z := run_reset xs z (hl.trans hz.symm)
  have hsr : run (shift xs b) z=z := run_reset _ _ (hs.trans hz.symm)
  have hzx : run z xs=xs := run_reset _ _ (hz.trans hl.symm)
  have h0 : weight cost xs (z++xs)=0 := hc xs hl _ (by rw [run_append,hr,hzx])
  have h1 : weight cost xs (b::(z++xs))=0 := hc xs hl _ (by
    change run (shift xs b) (z++xs)=xs
    rw [run_append,hsr,hzx])
  rw [weight_append,hr] at h0
  change cost (xs++[b])+weight cost (shift xs b) (z++xs)=0 at h1
  rw [weight_append,hsr] at h1
  dsimp only [p]
  have hh : (cost (xs++[b])+(weight cost (shift xs b) z+weight cost z xs))-
      (weight cost xs z+weight cost z xs)=(0 : Fin 2)-0 := by rw [h1,h0]
  apply sub_eq_zero.mp
  simpa only [p_sub_as_add,p_add_assoc,p_add_comm,p_add_left_comm,p_cancel_pair,p_add_self,p_add_zero,p_zero_add] using hh

def change (m : Nat) (h : List (Cell ι) → (Fin 2)) (xs : List (Cell ι)) : (Fin 2) :=
  h (image xs)-h (crop m xs)

/-- Global conservation along all closed walks of overlapping input windows. -/
def CyclicConserved (m : Nat) (h : List (Cell ι) → (Fin 2)) : Prop := Balanced (m+7) (change m h)

theorem cyclic_conserved_local (m : Nat) (h : List (Cell ι) → (Fin 2))
    (hc : CyclicConserved m h) : ∃ p, Conserved m h p := by
  obtain ⟨p,hp⟩:=balanced_gradient (m+7) (change m h) hc
  refine ⟨p,conserved_of_word m h p ?_⟩
  intro xs hl
  have hn : xs≠[] := by intro he; simp [he] at hl
  have hx := List.dropLast_concat_getLast hn
  have hh:=hp xs.dropLast (by rw [List.length_dropLast,hl]; omega) (xs.getLast hn)
  rw [hx] at hh
  unfold shift at hh
  rw [hx] at hh
  change h (image xs)-h (crop m xs)=p xs.dropLast-p (xs.drop 1) at hh
  have result : h (image xs)=h (crop m xs)+p xs.dropLast-p (xs.drop 1) := by
    apply sub_eq_zero.mp
    simpa only [p_sub_as_add,p_add_assoc,p_add_comm,p_add_left_comm,p_cancel_pair,p_add_self,p_add_zero,p_zero_add] using (sub_eq_zero.mpr hh)
  simpa only [List.drop_one] using result

theorem cyclic_conserved_trivial (m : Nat) (hm : 0<m) (h : List (Cell ι) → (Fin 2))
    (hc : CyclicConserved m h) : Trivial m h := by
  obtain ⟨p,hp⟩:=cyclic_conserved_local m h hc
  exact conserved_trivial m hm h p hp

end Cycle

/-! Both directions of the exact all-width parity classification. -/
namespace Classification
open Corner Word
open Descent Triviality
open Ruliology.CellularAutomata.Rule30ProductParity.Cycle

theorem run_length (xs bs : List (Cell ι)) : (run xs bs).length=xs.length := by
  induction bs generalizing xs with
  | nil => rfl
  | cons b bs ih => rw [run,ih,shift_length]

theorem gradient_weight (n : Nat) (cost p : List (Cell ι) → (Fin 2))
    (hp : ∀ xs, xs.length=n → ∀ b, cost (xs++[b])=p xs-p (shift xs b))
    (xs bs : List (Cell ι)) (hl : xs.length=n) :
    weight cost xs bs=p xs-p (run xs bs) := by
  induction bs generalizing xs with
  | nil => simp [weight,run]
  | cons b bs ih =>
    rw [weight,hp xs hl b,ih _ (by rw [shift_length,hl])]
    change p xs-p (shift xs b)+(p (shift xs b)-p (run (shift xs b) bs))=
      p xs-p (run (shift xs b) bs)
    rule30_parity_nf

theorem local_conserved_cyclic (m : Nat) (h p : List (Cell ι) → (Fin 2))
    (hc : Conserved m h p) : CyclicConserved m h := by
  have hp : ∀ xs, xs.length=m+7 → ∀ b,
      change m h (xs++[b])=p xs-p (shift xs b) := by
    intro xs hl b
    have hh := conserved_word m h p hc (xs++[b]) (by simp [hl])
    rw [List.dropLast_concat] at hh
    unfold change shift
    rw [List.drop_one]
    apply sub_eq_zero.mp
    simpa only [p_sub_as_add,p_add_assoc,p_add_comm,p_add_left_comm,p_cancel_pair,p_add_self,p_add_zero,p_zero_add] using (sub_eq_zero.mpr hh)
  intro xs hl bs hb
  have hh := gradient_weight (m+7) (change m h) p hp xs bs hl
  rw [hb] at hh
  simpa using hh

theorem trivial_conserved (m : Nat) (hm : 0<m) (h : List (Cell ι) → (Fin 2))
    (ht : Trivial m h) : ∃ p, Conserved m h p := by
  obtain ⟨c,b,hb⟩:=ht
  let p := fun xs=>b (crop (m-1) xs)-b (image xs)
  refine ⟨p,conserved_of_word m h p ?_⟩
  intro xs hl
  have hi : (image xs).length=m := by rw [image_length,hl]; omega
  have hj : (crop m xs).length=m := crop_length m xs (by omega)
  have h1:=hb (image xs) hi
  have h2:=hb (crop m xs) hj
  have hit:=image_tail xs
  have hid:=image_dropLast xs
  have hct:=crop_tail (m-1) xs
  have hcd:=crop_dropLast (m-1) xs (by omega)
  have hm1 : m-1+1=m := by omega
  rw [hm1] at hct hcd
  have hn : xs≠[] := by intro he; simp [he] at hl
  have hc0:=crop_append (m-1) xs.dropLast
    (by rw [List.length_dropLast,hl]; omega) (xs.getLast hn)
  rw [List.dropLast_concat_getLast hn] at hc0
  rw [h1,h2,hit,←hid,hct,hcd]
  dsimp only [p]
  rw [←hc0]
  rule30_parity_nf

/-- No hidden local-current premise and no bound on window width. -/
theorem cyclic_conserved_iff_trivial (m : Nat) (hm : 0<m) (h : List (Cell ι) → (Fin 2)) :
    CyclicConserved m h ↔ Trivial m h := by
  constructor
  · exact cyclic_conserved_trivial m hm h
  · intro ht
    obtain ⟨p,hp⟩:=trivial_conserved m hm h ht
    exact local_conserved_cyclic m h p hp

theorem local_conserved_iff_trivial (m : Nat) (hm : 0<m) (h : List (Cell ι) → (Fin 2)) :
    (∃ p, Conserved m h p) ↔ Trivial m h := by
  constructor
  · rintro ⟨p,hp⟩; exact conserved_trivial m hm h p hp
  · exact trivial_conserved m hm h

end Classification

/-- All widths, any family of Rule30 coordinates, and mod-two coefficients.
The assumption is the exact four-step compact local-current equation. -/
theorem all_widths (m : Nat) (hm : 0<m) (h p : List (Cell ι) → (Fin 2))
    (hc : Corner.Conserved m h p) :
    ∃ c : (Fin 2), ∃ b : List (Cell ι) → (Fin 2), ∀ xs, xs.length=m →
      h xs=c+b xs.tail-b xs.dropLast :=
  Triviality.conserved_trivial m hm h p hc

/-- The mixed-pair mod-two specialization; no finite width cutoff. -/
theorem paired_F2 (m : Nat) (hm : 0<m)
    (h p : List (Cell (Fin 2)) → Fin 2) (hc : Corner.Conserved m h p) :
    ∃ c : Fin 2, ∃ b : List (Cell (Fin 2)) → Fin 2, ∀ xs, xs.length=m →
      h xs=c+b xs.tail-b xs.dropLast := all_widths m hm h p hc

/-- Arbitrarily many Boolean coordinates and every positive window width.
The concrete headline is monomorphic; the library above permits any universe. -/
theorem all_ensembles (I : Type) (m : Nat) (hm : 0<m)
    (h : List (Cell I) → Fin 2) :
    Cycle.CyclicConserved m h ↔ Triviality.Trivial m h :=
  Classification.cyclic_conserved_iff_trivial m hm h

/-- Every mixed pair parity density, at EVERY width. -/
theorem paired_F2_exact (m : Nat) (hm : 0<m) (h : List (Cell (Fin 2)) → Fin 2) :
    Cycle.CyclicConserved m h ↔
      ∃ c : Fin 2, ∃ b : List (Cell (Fin 2)) → Fin 2, ∀ xs, xs.length=m →
        h xs=c+b xs.tail-b xs.dropLast :=
  Classification.cyclic_conserved_iff_trivial m hm h

/-- The image in the classification is exactly four shrinking Rule30
updates on each coordinate; it is not an independently fitted map. -/
theorem paired_F2_semantics (xs : List (Cell (Fin 2))) :
    Corner.image xs=Corner.four xs := Word.image_eq_four xs

end Ruliology.CellularAutomata.Rule30ProductParity
