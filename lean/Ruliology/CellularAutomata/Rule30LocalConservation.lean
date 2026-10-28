module

public import Ruliology.CellularAutomata.Rule30Prize

/-!
# Integer local conservation for four Rule 30 steps, uniformly in width

For an input word X of length m+8, `Corner.image X` is exactly four shrinking
Rule30 updates (`Word.image_eq_four`), while `Word.crop m X` is the old m-cell
window at offset4. `CyclicConserved m h` says that the sum of
`h (image X) - h (crop m X)` vanishes along every closed walk of overlapping
input windows. It does not assume an explicitly supplied local current.

For EVERY positive m, `cyclic_conserved_iff_shift_coboundary` classifies these
integer densities as exactly a constant plus a shift coboundary:
`h v = c + B v.tail - B v.dropLast` for every word v of length m.
The local-current formulation has the same classification. Both directions
are proved, and every cyclic rolling-window score reduces to c times its
length. No positivity or boundedness of the potential is assumed.

The proof constructs arbitrary-length preimages with eight white trailing
cells. Independently varying the two outer input bits forces zero mixed
endpoint difference of the density. A gauge shortens the density while
preserving conservation. Induction reaches the one-cell case. A generic
closed-word-walk gradient construction supplies the local current.

This is an integer, four-step, finite-word conservation theorem. It makes no
claim about every kind of invariant, physical ranking or real-valued density,
and does not settle a Rule30 prize problem. Absence-of-conservation results
and local-current constructions have a substantial prior literature; no
literature novelty is claimed for this direct formalization.

References:
* T. Hattori and S. Takesue, Additive conserved quantities in discrete-time
  lattice dynamical systems, Physica D49(1991),295-322.
  https://doi.org/10.1016/0167-2789(91)90150-8
* S. Takesue, Staggered Invariants in Cellular Automata,
  Complex Systems9(1995),149-168.
* J. Kari and S. Taati, Statistical Mechanics of Surjective Cellular Automata,
  Theorem47 (under strong transitivity). That dynamical hypothesis is not
  established here. https://arxiv.org/abs/1311.2319
-/

@[expose] public section
namespace Ruliology.CellularAutomata.Rule30LocalConservation

/-! Uniform finite-word ingredients for conserved local scores of four Rule30
steps. No finite-window census or optimization solver is a premise. -/
namespace Corner
open Ruliology.CellularAutomata

def shrink : List Bool → List Bool
  | a::b::c::xs => Rule30Jen.rule a b c :: shrink (b::c::xs)
  | _ => []

def four (xs : List Bool) : List Bool := shrink (shrink (shrink (shrink xs)))

def q9 (a b c d e f g h i : Bool) : Bool :=
  (four [a,b,c,d,e,f,g,h,i]).headD false

def q (a : Bool) (xs : List Bool) : Bool :=
  q9 a (xs.getD 0 false) (xs.getD 1 false) (xs.getD 2 false) (xs.getD 3 false)
    (xs.getD 4 false) (xs.getD 5 false) (xs.getD 6 false) (xs.getD 7 false)

theorem q9_left : ∀ a b c d e f g h i : Bool,
    q9 a b c d e f g h i = xor a (q9 false b c d e f g h i) := by decide +kernel

theorem q_left (a : Bool) (xs : List Bool) : q a xs=xor a (q false xs) :=
  q9_left a _ _ _ _ _ _ _ _

theorem q9_right_zero : ∀ a b : Bool,
    q9 a false false false false false false false b=xor a b := by decide +kernel

theorem getD_append_prefix (xs ys : List Bool) (i : Nat) (hi : i<xs.length) :
    (xs++ys).getD i false=xs.getD i false := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left hi]

theorem q_append (a b : Bool) (xs : List Bool) (hx : 8≤xs.length) :
    q a (xs++[b])=q a xs := by
  unfold q
  congr 1 <;> apply getD_append_prefix <;> omega

def image : List Bool → List Bool
  | [] => []
  | a::xs => if 8≤xs.length then q a xs :: image xs else []

def preimage : List Bool → List Bool
  | [] => List.replicate 8 false
  | b::xs => let tail:=preimage xs; xor b (q false tail) :: tail

theorem preimage_length (xs : List Bool) : (preimage xs).length=xs.length+8 := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [preimage,ih]

/-- Constructive arbitrary-length preimages with eight trailing white cells. -/
theorem image_preimage (xs : List Bool) : image (preimage xs)=xs := by
  induction xs with
  | nil => decide +kernel
  | cons b xs ih =>
    have hp : 8≤(preimage xs).length := by rw [preimage_length]; omega
    have hq : q (xor b (q false (preimage xs))) (preimage xs)=b := by
      rw [q_left]
      cases b <;> cases q false (preimage xs) <;> rfl
    simp only [preimage,image,ite_eq_left hp,hq,ih]

theorem preimage_suffix (xs : List Bool) :
    ∃ u, preimage xs=u++List.replicate 8 false := by
  induction xs with
  | nil => exact ⟨[],rfl⟩
  | cons b xs ih =>
    obtain ⟨u,hu⟩ := ih
    exact ⟨xor b (q false (preimage xs))::u,by simp only [preimage,hu,List.cons_append]⟩

theorem image_white_suffix (u : List Bool) (b : Bool) :
    image (u++List.replicate 8 false++[b])=
      image (u++List.replicate 8 false)++[b] := by
  induction u with
  | nil => cases b <;> decide +kernel
  | cons a u ih =>
    have hx : 8≤(u++List.replicate 8 false).length := by simp
    have hy : 8≤((u++List.replicate 8 false)++[b]).length := by simp
    simp only [List.cons_append,image,ite_eq_left hx,ite_eq_left hy,q_append a b _ hx,ih]

/-- Two freely chosen outer input cells vary only the two endpoint outputs;
the desired interior is arbitrary and has unbounded length. -/
theorem image_rectangle (a b : Bool) (ys : List Bool) :
    image (a::(preimage ys++[b]))=
      xor a (q false (preimage ys)) :: (ys++[b]) := by
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
def Conserved (m : Nat) (h p : List Bool → Int) : Prop :=
  ∀ mid : List Bool, mid.length=m+6 → ∀ a b : Bool,
    h (image (a::(mid++[b])))=
      h ((mid.drop 3).take m)+p (a::mid)-p (mid++[b])

/-- Every conserved density at ANY window length >=2 has zero endpoint
mixed difference. This is the uniform range-reduction obstruction. -/
theorem conserved_rectangle (ys : List Bool) (h p : List Bool → Int)
    (hc : Conserved (ys.length+2) h p) :
    h (false::(ys++[false]))+h (true::(ys++[true]))=
      h (false::(ys++[true]))+h (true::(ys++[false])) := by
  have hl : (preimage ys).length=ys.length+2+6 := by rw [preimage_length]
  have h00 := hc (preimage ys) hl false false
  have h01 := hc (preimage ys) hl false true
  have h10 := hc (preimage ys) hl true false
  have h11 := hc (preimage ys) hl true true
  rw [image_rectangle] at h00 h01 h10 h11
  cases hh : q false (preimage ys) <;> simp only [hh] at h00 h01 h10 h11 <;>
    change _ at h00 h01 h10 h11 <;> simp only [Bool.false_xor,Bool.true_xor,
      Bool.not_false,Bool.not_true] at h00 h01 h10 h11 <;> omega

def potential (h : List Bool → Int) (u : List Bool) : Int := h (false::u)

def shorter (h : List Bool → Int) (u : List Bool) : Int :=
  h (u++[false])-h (false::(u.tail++[false]))+h (false::u)

/-- Explicit cohomology to a shorter local density. No positivity assumption
on the score or on the potential is used. -/
theorem shorten_density (ys : List Bool) (h p : List Bool → Int)
    (hc : Conserved (ys.length+2) h p) (a b : Bool) :
    h (a::(ys++[b]))=shorter h (a::ys)+
      potential h (ys++[b])-potential h (a::ys) := by
  have hr := conserved_rectangle ys h p hc
  unfold shorter potential
  simp only [List.cons_append,List.tail_cons]
  cases a <;> cases b <;> omega

end Corner

/-! Word semantics, compact conservation potentials, and the one-cell base
case for the uniform conservation-law range-reduction argument. -/
namespace Word
open Corner

theorem shrink_length (xs : List Bool) : (shrink xs).length=xs.length-2 := by
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

theorem four_length (xs : List Bool) : (four xs).length=xs.length-8 := by
  simp only [four,shrink_length]
  omega

theorem four_cons (a : Bool) (xs : List Bool) (hx : 8≤xs.length) :
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
theorem image_eq_four (xs : List Bool) : image xs=four xs := by
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

theorem image_length (xs : List Bool) : (image xs).length=xs.length-8 := by
  rw [image_eq_four,four_length]

theorem image_tail (xs : List Bool) : (image xs).tail=image xs.tail := by
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

theorem image_append_dropLast (xs : List Bool) (b : Bool) :
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

theorem image_dropLast (xs : List Bool) : image xs.dropLast=(image xs).dropLast := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    have he := List.dropLast_concat_getLast (List.cons_ne_nil a xs)
    have hh := image_append_dropLast (a::xs).dropLast ((a::xs).getLast (List.cons_ne_nil a xs))
    rw [he] at hh
    exact hh.symm

def crop (m : Nat) (xs : List Bool) : List Bool := (xs.drop 4).take m

theorem crop_outer (m : Nat) (mid : List Bool) (hm : mid.length=m+6) (a b : Bool) :
    crop m (a::(mid++[b]))=(mid.drop 3).take m := by
  unfold crop
  rw [List.drop_succ_cons,List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by simp only [List.length_drop]; omega)]

theorem conserved_word (m : Nat) (h p : List Bool → Int) (hc : Conserved m h p)
    (xs : List Bool) (hx : xs.length=m+8) :
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

theorem conserved_one_constant (h p : List Bool → Int) (hc : Conserved 1 h p) :
    h [false]=h [true] := by
  have img : ∀ a b : Bool, image (a::(List.replicate 7 false++[b]))=[xor a b] := by decide +kernel
  have h00:=hc (List.replicate 7 false) (by decide) false false
  have h01:=hc (List.replicate 7 false) (by decide) false true
  have h10:=hc (List.replicate 7 false) (by decide) true false
  have h11:=hc (List.replicate 7 false) (by decide) true true
  rw [img] at h00 h01 h10 h11
  simp only [Bool.false_xor,Bool.true_xor,Bool.not_false,Bool.not_true] at h00 h01 h10 h11
  omega

end Word

/-! Preserve the conservation equation while shortening its density. The
potential is compressed by proving independence of its final input bit. -/
namespace Descent
open Corner Word

theorem crop_length (m : Nat) (xs : List Bool) (hx : m+4≤xs.length) :
    (crop m xs).length=m := by
  simp only [crop,List.length_take,List.length_drop]
  omega

theorem tail_take_succ (m : Nat) (xs : List Bool) :
    (xs.take (m+1)).tail=xs.tail.take m := by cases xs <;> simp

theorem crop_tail (m : Nat) (xs : List Bool) :
    (crop (m+1) xs).tail=crop m xs.tail := by
  unfold crop
  rw [tail_take_succ,List.tail_drop,List.drop_tail]

theorem crop_dropLast (m : Nat) (xs : List Bool) (hx : m+5≤xs.length) :
    (crop (m+1) xs).dropLast=crop m xs := by
  unfold crop
  have hi : m<(xs.drop 4).length := by simp only [List.length_drop]; omega
  rw [List.take_succ_eq_append_getElem hi,List.dropLast_concat]

theorem crop_append (m : Nat) (xs : List Bool) (hx : xs.length=m+8) (b : Bool) :
    crop m (xs++[b])=crop m xs := by
  unfold crop
  rw [List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by simp only [List.length_drop]; omega)]

theorem conserved_of_word (m : Nat) (h p : List Bool → Int)
    (hc : ∀ xs, xs.length=m+8 →
      h (image xs)=h (crop m xs)+p xs.dropLast-p xs.tail) : Conserved m h p := by
  intro mid hm a b
  have hx : (a::(mid++[b])).length=m+8 := by simp [hm,Nat.add_assoc]
  have hh:=hc (a::(mid++[b])) hx
  have hp : (a::(mid++[b])).dropLast=a::mid := by
    change ((a::mid)++[b]).dropLast=a::mid
    exact List.dropLast_concat
  simpa only [crop_outer m mid hm a b,hp,List.tail_cons] using hh

theorem shorten_word (m : Nat) (hm : 1≤m) (h p : List Bool → Int)
    (hc : Conserved (m+1) h p) (xs : List Bool) (hx : xs.length=m+1) :
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

def transport (m : Nat) (h p : List Bool → Int) (xs : List Bool) : Int :=
  p xs+potential h (image xs)-potential h (crop m xs)

theorem transport_identity (m : Nat) (hm : 1≤m) (h p : List Bool → Int)
    (hc : Conserved (m+1) h p) (xs : List Bool) (hx : xs.length=m+8) (b : Bool) :
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
  omega

theorem transport_last_independent (m : Nat) (hm : 1≤m) (h p : List Bool → Int)
    (hc : Conserved (m+1) h p) (xs : List Bool) (hx : xs.length=m+7) :
    transport m h p (xs++[false])=transport m h p (xs++[true]) := by
  have hl : (false::xs).length=m+8 := by simp [hx,Nat.add_assoc]
  have h0:=transport_identity m hm h p hc (false::xs) hl false
  have h1:=transport_identity m hm h p hc (false::xs) hl true
  simp only [List.tail_cons] at h0 h1
  omega

def reducedPotential (m : Nat) (h p : List Bool → Int) (xs : List Bool) : Int :=
  transport m h p (xs++[false])

theorem transport_reduced (m : Nat) (hm : 1≤m) (h p : List Bool → Int)
    (hc : Conserved (m+1) h p) (xs : List Bool) (hx : xs.length=m+8) :
    transport m h p xs=reducedPotential m h p xs.dropLast := by
  have hn : xs≠[] := by intro he; simp [he] at hx
  let b:=xs.getLast hn
  have he : xs.dropLast++[b]=xs := List.dropLast_concat_getLast hn
  have hl : xs.dropLast.length=m+7 := by rw [List.length_dropLast,hx]; omega
  have hi:=transport_last_independent m hm h p hc xs.dropLast hl
  unfold reducedPotential
  rw [←he]
  simp only [List.dropLast_concat]
  cases hb : b
  · rfl
  · exact hi.symm

/-- The explicit shorter density again has a potential of the proper compact
window length. This is the induction step, uniformly for every m>=1. -/
theorem shorter_conserved (m : Nat) (hm : 1≤m) (h p : List Bool → Int)
    (hc : Conserved (m+1) h p) :
    Conserved m (shorter h) (reducedPotential m h p) := by
  apply conserved_of_word
  intro xs hx
  have hh:=transport_identity m hm h p hc xs hx false
  rw [transport_reduced m hm h p hc xs hx] at hh
  exact hh

end Descent

/-! All integer local densities satisfying the explicit compact four-step
conservation equation are constant plus a shift coboundary, at every width.
The passage from a Rule30 ranking premise to conservation remains separate. -/
namespace Triviality
open Corner Word
open Descent

def Trivial (m : Nat) (h : List Bool → Int) : Prop :=
  ∃ c : Int, ∃ p : List Bool → Int, ∀ xs, xs.length=m →
    h xs=c+p xs.tail-p xs.dropLast

theorem trivial_one (h p : List Bool → Int) (hc : Conserved 1 h p) : Trivial 1 h := by
  have hh:=conserved_one_constant h p hc
  refine ⟨h [false],fun _=>0,?_⟩
  intro xs hx
  cases xs with
  | nil => simp at hx
  | cons a xs =>
    have he : xs=[] := by
      apply List.eq_nil_of_length_eq_zero
      simp only [List.length_cons] at hx
      omega
    subst xs
    cases a <;> simp [hh]

/-- No fixed cutoff on m: the local-potential equation has only constant and
telescoping solutions at every positive window length. -/
theorem conserved_trivial : ∀ m : Nat, 0<m → ∀ h p : List Bool → Int,
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
    omega

def score (h : List Bool → Int) (windows : Nat → List Bool) : Nat → Int
  | 0 => 0
  | n+1 => score h windows n+h (windows n)

theorem trivial_chain (m : Nat) (h : List Bool → Int) (c : Int) (p : List Bool → Int)
    (ht : ∀ xs, xs.length=m → h xs=c+p xs.tail-p xs.dropLast)
    (windows : Nat → List Bool) (hl : ∀ i, (windows i).length=m)
    (ho : ∀ i, (windows i).tail=(windows (i+1)).dropLast) (n : Nat) :
    score h windows n=(n:Int)*c+p (windows n).dropLast-p (windows 0).dropLast := by
  induction n with
  | zero => simp [score]
  | succ n ih =>
    have hh:=ht (windows n) (hl n)
    rw [ho n] at hh
    have hm : ((n+1:Nat):Int)*c=(n:Int)*c+c := by
      change ((n:Int)+1)*c=(n:Int)*c+c
      rw [Int.add_mul,Int.one_mul]
    rw [score,ih,hm]
    omega

/-- Every cyclic rolling-window score from this class is just c times the
cycle length. A boundary potential contributes no bulk conserved charge. -/
theorem conserved_cycle_score (m : Nat) (hm : 0<m) (h p : List Bool → Int)
    (hc : Conserved m h p) : ∃ c : Int, ∀ windows : Nat → List Bool,
    (∀ i, (windows i).length=m) →
    (∀ i, (windows i).tail=(windows (i+1)).dropLast) →
    ∀ n, windows n=windows 0 → score h windows n=(n:Int)*c := by
  obtain ⟨c,b,hb⟩:=conserved_trivial m hm h p hc
  refine ⟨c,?_⟩
  intro windows hl ho n he
  have hh:=trivial_chain m h c b hb windows hl ho n
  rw [he] at hh
  omega

end Triviality

/-! A uniform directed-word coboundary construction. The hypothesis is stated
directly as zero change of total density on every closed overlapping-word walk;
it does not assume the existence of a local current. -/
namespace Cycle
open Corner Word
open Descent Triviality

def shift (xs : List Bool) (b : Bool) : List Bool := (xs++[b]).drop 1

def run : List Bool → List Bool → List Bool
  | xs, [] => xs
  | xs, b::bs => run (shift xs b) bs

def weight (cost : List Bool → Int) : List Bool → List Bool → Int
  | _, [] => 0
  | xs, b::bs => cost (xs++[b])+weight cost (shift xs b) bs

theorem shift_length (xs : List Bool) (b : Bool) : (shift xs b).length=xs.length := by
  simp [shift]

theorem run_append (xs bs cs : List Bool) : run xs (bs++cs)=run (run xs bs) cs := by
  induction bs generalizing xs with
  | nil => rfl
  | cons b bs ih => exact ih (shift xs b)

theorem weight_append (cost : List Bool → Int) (xs bs cs : List Bool) :
    weight cost xs (bs++cs)=weight cost xs bs+weight cost (run xs bs) cs := by
  induction bs generalizing xs with
  | nil => simp [weight,run]
  | cons b bs ih => simp only [List.cons_append,weight,run,ih]; omega

theorem run_formula (xs bs : List Bool) : run xs bs=(xs++bs).drop bs.length := by
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

theorem run_reset (xs bs : List Bool) (hl : xs.length=bs.length) : run xs bs=bs := by
  rw [run_formula,←hl,List.drop_append_length]

def Balanced (n : Nat) (cost : List Bool → Int) : Prop :=
  ∀ xs, xs.length=n → ∀ bs, run xs bs=xs → weight cost xs bs=0

/-- Compare two closed walks through a common all-white state. Every width is
handled at once; no finite graph census is a premise. -/
theorem balanced_gradient (n : Nat) (cost : List Bool → Int) (hc : Balanced n cost) :
    ∃ p : List Bool → Int, ∀ xs, xs.length=n → ∀ b,
      cost (xs++[b])=p xs-p (shift xs b) := by
  let z := List.replicate n false
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
  omega

def change (m : Nat) (h : List Bool → Int) (xs : List Bool) : Int :=
  h (image xs)-h (crop m xs)

/-- Global conservation along all closed walks of overlapping input windows. -/
def CyclicConserved (m : Nat) (h : List Bool → Int) : Prop := Balanced (m+7) (change m h)

theorem cyclic_conserved_local (m : Nat) (h : List Bool → Int)
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
  simpa only [List.drop_one] using (show h (image xs)=h (crop m xs)+p xs.dropLast-p (xs.drop 1) by omega)

theorem cyclic_conserved_trivial (m : Nat) (hm : 0<m) (h : List Bool → Int)
    (hc : CyclicConserved m h) : Trivial m h := by
  obtain ⟨p,hp⟩:=cyclic_conserved_local m h hc
  exact conserved_trivial m hm h p hp

end Cycle

/-! Both directions of the exact all-width integer classification. -/
namespace Classification
open Corner Word
open Descent Triviality
open Cycle

theorem run_length (xs bs : List Bool) : (run xs bs).length=xs.length := by
  induction bs generalizing xs with
  | nil => rfl
  | cons b bs ih => rw [run,ih,shift_length]

theorem gradient_weight (n : Nat) (cost p : List Bool → Int)
    (hp : ∀ xs, xs.length=n → ∀ b, cost (xs++[b])=p xs-p (shift xs b))
    (xs bs : List Bool) (hl : xs.length=n) :
    weight cost xs bs=p xs-p (run xs bs) := by
  induction bs generalizing xs with
  | nil => simp [weight,run]
  | cons b bs ih =>
    rw [weight,hp xs hl b,ih _ (by rw [shift_length,hl])]
    change p xs-p (shift xs b)+(p (shift xs b)-p (run (shift xs b) bs))=
      p xs-p (run (shift xs b) bs)
    omega

theorem local_conserved_cyclic (m : Nat) (h p : List Bool → Int)
    (hc : Conserved m h p) : CyclicConserved m h := by
  have hp : ∀ xs, xs.length=m+7 → ∀ b,
      change m h (xs++[b])=p xs-p (shift xs b) := by
    intro xs hl b
    have hh:=conserved_word m h p hc (xs++[b]) (by simp [hl])
    rw [List.dropLast_concat] at hh
    unfold change shift
    rw [List.drop_one]
    omega
  intro xs hl bs hb
  have hh:=gradient_weight (m+7) (change m h) p hp xs bs hl
  rw [hb] at hh
  omega

theorem trivial_conserved (m : Nat) (hm : 0<m) (h : List Bool → Int)
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
  omega

/-- No hidden local-current premise and no bound on window width. -/
theorem cyclic_conserved_iff_trivial (m : Nat) (hm : 0<m) (h : List Bool → Int) :
    CyclicConserved m h ↔ Trivial m h := by
  constructor
  · exact cyclic_conserved_trivial m hm h
  · intro ht
    obtain ⟨p,hp⟩:=trivial_conserved m hm h ht
    exact local_conserved_cyclic m h p hp

theorem local_conserved_iff_trivial (m : Nat) (hm : 0<m) (h : List Bool → Int) :
    (∃ p, Conserved m h p) ↔ Trivial m h := by
  constructor
  · rintro ⟨p,hp⟩; exact conserved_trivial m hm h p hp
  · exact trivial_conserved m hm h

end Classification


/-- Conservation on every closed walk of overlapping m+8-cell input words. -/
abbrev CyclicConserved := Cycle.CyclicConserved

/-- A constant plus a telescoping boundary difference on words of length m. -/
abbrev ShiftCoboundary := Triviality.Trivial

/-- The equivalent four-step local-current equation. -/
abbrev LocalConserved := Corner.Conserved

theorem cyclic_conserved_iff_shift_coboundary (m : Nat) (hm : 0<m)
    (h : List Bool → Int) : CyclicConserved m h ↔ ShiftCoboundary m h :=
  Classification.cyclic_conserved_iff_trivial m hm h

theorem local_conserved_iff_shift_coboundary (m : Nat) (hm : 0<m)
    (h : List Bool → Int) : (∃ p, LocalConserved m h p) ↔ ShiftCoboundary m h :=
  Classification.local_conserved_iff_trivial m hm h

end Ruliology.CellularAutomata.Rule30LocalConservation
