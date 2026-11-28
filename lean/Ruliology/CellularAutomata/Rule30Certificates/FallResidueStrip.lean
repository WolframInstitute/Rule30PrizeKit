module

public import Ruliology.CellularAutomata.Rule30StripCertificates

/-!
# The strip with free exterior cells and one permitted fall residue per site

Support for `Rule30FallResidues`. A node is a row of `w` cells, and an edge is one Rule 30 update with both exterior
cells free in which only the sites assigned to the current slot of an `m`-slot calendar may fall (`Run`). `Good`
says that on every such path some adjacent pair eventually repeats every `m` ticks.

* `quiet_eq`: among three successive quiet updates of a six-cell strip, the first is idle.
* `good_of_dvd`: one residue modulo `m` is one residue modulo a divisor, and a repeating pair lifts back.
* The rank check (`check`, `Certificate`): each node has a rank that no edge raises, and each rank names an adjacent
  pair with its reading at each slot.
* `Classifies`: the assignments still possible at a width, built from the two narrower restrictions.
-/

@[expose] public section

/-! A strip with both exterior cells free and one permitted fall phase per site. -/
namespace Ruliology.CellularAutomata.Rule30FallResidues

open Ruliology.CellularAutomata Rule30StripCertificates

def fallMask (s d : Nat) : Nat := s &&& (s ^^^ d)

def fits (a s d : Nat) : Bool := (fallMask s d &&& a) == fallMask s d

def permit (w : Nat) (a : Nat → Nat) (p : Nat) : Nat :=
  (List.range w).foldl (fun m j => if a j = p then m ||| (1 <<< j) else m) 0

theorem permit_bit (w : Nat) (a : Nat → Nat) (p j : Nat) :
    (permit w a p).testBit j = decide (j < w ∧ a j = p) := by
  classical
  have go (is : List Nat) (b : Nat) :
      ((is.foldl (fun m k => if a k = p then m ||| (1 <<< k) else m) b).testBit j) =
        (b.testBit j || decide (j ∈ is ∧ a j = p)) := by
    induction is generalizing b with
    | nil => simp
    | cons k ks ih =>
      simp only [List.foldl_cons, ih]
      by_cases h : a k = p
      · by_cases e : k = j
        · subst k
          simp [h, Nat.testBit_or, Nat.testBit_shiftLeft]
        · have shift : (1 <<< k).testBit j = false := by
            rw [Nat.testBit_shiftLeft]
            by_cases hh : k ≤ j
            · have pow : 2 ≤ 2^(j-k) := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ j-k)
              simp [hh, Nat.testBit_lt_two_pow (show 1 < 2^(j-k) by omega)]
            · simp [hh]
          simp [h, Ne.symm e, Nat.testBit_or, shift]
      · by_cases e : k = j
        · subst k
          simp [h]
        · simp [h, Ne.symm e]
  simpa [permit] using go (List.range w) 0

theorem fits_iff (a s d : Nat) :
    fits a s d = true ↔
      ∀ j, s.testBit j = true → d.testBit j = false → a.testBit j = true := by
  rw [fits, beq_iff_eq]
  constructor
  · intro h j on off
    have hb := congrArg (fun z : Nat => z.testBit j) h
    simp [fallMask, Nat.testBit_and, Nat.testBit_xor, on, off] at hb
    exact hb
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases on : s.testBit j = true <;> by_cases off : d.testBit j = false <;>
      simp_all [fallMask, Nat.testBit_and, Nat.testBit_xor]

def successors (w s : Nat) : List Nat :=
  [stripStep w false false s, stripStep w false true s,
    stripStep w true false s, stripStep w true true s]

theorem mem_successors {w s d : Nat} :
    d ∈ successors w s ↔ ∃ l r : Bool, d = stripStep w l r s := by
  constructor
  · simp only [successors, List.mem_cons, List.not_mem_nil, or_false]
    rintro (h | h | h | h)
    · exact ⟨false,false,h⟩
    · exact ⟨false,true,h⟩
    · exact ⟨true,false,h⟩
    · exact ⟨true,true,h⟩
  · rintro ⟨l,r,rfl⟩
    cases l <;> cases r <;> simp [successors]

def Edge (w a s d : Nat) : Prop := d ∈ successors w s ∧ fits a s d = true

structure Run (w m : Nat) (a x : Nat → Nat) : Prop where
  bounded : ∀ t, x t < 2 ^ w
  edge : ∀ t, Edge w (permit w a (t % m)) (x t) (x (t+1))

/-- Some fixed adjacent pair repeats every full round of the calendar. -/
def Pair (w m : Nat) (x : Nat → Nat) : Prop :=
  ∃ j N, j + 1 < w ∧ ∀ t, N ≤ t →
    (x (t + m) >>> j) % 4 = (x t >>> j) % 4

def Good (w m : Nat) (a : Nat → Nat) : Prop :=
  ∀ x, Run w m a x → Pair w m x

private def quietTriple (s : Nat) : Bool :=
  (successors 6 s).all fun d =>
    if fits 0 s d && s != d then
      (successors 6 d).all fun e =>
        !(fits 0 d e) || (successors 6 e).all fun f => !(fits 0 e f)
    else true

private theorem quietTriple_ok : (List.range 64).all quietTriple = true := by decide +kernel

/-- Among three consecutive quiet updates of a six-site strip, the first is idle.
The exterior bits at all three ticks are unrestricted. -/
theorem quiet_eq {s d e f : Nat} (hs : s < 64)
    (h₀ : Edge 6 0 s d) (h₁ : Edge 6 0 d e) (h₂ : Edge 6 0 e f) : d = s := by
  apply Classical.byContradiction
  intro hne
  have a := List.all_eq_true.mp (List.all_eq_true.mp quietTriple_ok _ (List.mem_range.mpr hs)) d h₀.1
  have b := List.all_eq_true.mp (by simpa [h₀.2, Ne.symm hne] using a :
    (successors 6 d).all (fun e => !(fits 0 d e) || (successors 6 e).all fun f => !(fits 0 e f)) = true) e h₁.1
  simp only [h₁.2, Bool.not_true, Bool.false_or] at b
  have c := List.all_eq_true.mp b f h₂.1
  simp [h₂.2] at c

def rotate (m q r : Nat) : Nat := if q ≤ r then r-q else r+(m-q)

theorem rotate_lt {m q r : Nat} (hq : q < m) (hr : r < m) : rotate m q r < m := by
  unfold rotate
  split <;> omega

theorem rotate_add_iff {m q r u : Nat} (hq : q < m) (hr : r < m) (hu : u < m) :
    (u+q)%m = r ↔ u = rotate m q r := by
  have hm : u+q < 2*m := by omega
  by_cases b : u+q < m
  · rw [Nat.mod_eq_of_lt b]
    unfold rotate
    split <;> omega
  · rw [Nat.mod_eq_sub_mod (by omega : m ≤ u+q), Nat.mod_eq_of_lt (by omega : u+q-m < m)]
    unfold rotate
    split <;> omega

theorem good_of_rotated {w m q : Nat} {a : Nat → Nat} (hq : q < m)
    (ha : ∀ j, j < w → a j < m)
    (good : Good w m (fun j => rotate m q (a j))) : Good w m a := by
  intro x hx
  let y (t : Nat) := x (t+q)
  have hy : Run w m (fun j => rotate m q (a j)) y := by
    refine ⟨fun t => hx.bounded _, fun t => ?_⟩
    have e := hx.edge (t+q)
    change Edge w _ (x (t+q)) (x (t+1+q))
    rw [show t+1+q = t+q+1 by omega]
    have same : permit w (fun j => rotate m q (a j)) (t%m) = permit w a ((t+q)%m) := by
      apply Nat.eq_of_testBit_eq
      intro j
      rw [permit_bit, permit_bit]
      by_cases hj : j < w
      · simp only [hj, true_and, Nat.add_mod t q m, Nat.mod_eq_of_lt hq]
        rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
        exact ⟨fun e => (rotate_add_iff hq (ha j hj) (Nat.mod_lt _ (by omega))).mpr e.symm |>.symm,
          fun e => (rotate_add_iff hq (ha j hj) (Nat.mod_lt _ (by omega))).mp e.symm |>.symm⟩
      · simp [hj]
    rwa [same]
  obtain ⟨j,N,hj,per⟩ := good y hy
  refine ⟨j,N+q,hj,fun t ht => ?_⟩
  simpa only [y, show t-q+m+q=t+m by omega, show t-q+q=t by omega] using
    per (t-q) (by omega)

theorem good_of_dvd {w d m : Nat} {a : Nat → Nat} (h : d ∣ m)
    (good : Good w d (fun j => a j % d)) : Good w m a := by
  intro x hx
  have hsmall : Run w d (fun j => a j % d) x := by
    refine ⟨hx.bounded, fun t => ?_⟩
    refine ⟨(hx.edge t).1, (fits_iff _ _ _).mpr ?_⟩
    intro j on off
    have he := (fits_iff _ _ _).mp (hx.edge t).2 j on off
    rw [permit_bit, decide_eq_true_eq] at he ⊢
    exact ⟨he.1, by rw [he.2, Nat.mod_mod_of_dvd _ h]⟩
  obtain ⟨j,N,hj,per⟩ := good x hsmall
  obtain ⟨k, rfl⟩ := h
  refine ⟨j,N,hj,fun t ht => ?_⟩
  clear hx
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc, per (t+d*k) (by omega)]
    exact ih

end Ruliology.CellularAutomata.Rule30FallResidues

namespace Ruliology.CellularAutomata.Rule30FallResidues

open Ruliology.CellularAutomata Rule30StripCertificates

def slice (w k s : Nat) : Nat := (s >>> k) % 2^w

theorem slice_bit {w k s j : Nat} (hj : j < w) :
    (slice w k s).testBit j = s.testBit (k+j) := by
  simp [slice, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, hj]

private theorem slice_step {w v k s : Nat} (hk : k+v ≤ w)
    (hs : s < 2^w) (l r : Bool) :
    slice v k (stripStep w l r s) =
      stripStep v (if k = 0 then l else s.testBit (k-1))
        (if k+v = w then r else s.testBit (k+v)) (slice v k s) := by
  apply Nat.eq_of_testBit_eq
  intro j
  have small : slice v k s < 2^v := Nat.mod_lt _ (Nat.two_pow_pos v)
  by_cases hj : j < v
  · rw [slice_bit hj, testBit_stripStep _ _ _ _ hs _ (by omega),
      testBit_stripStep _ _ _ _ small _ hj, slice_bit hj]
    congr 1
    · by_cases h : j=0
      · subst j
        simp
      · rw [ite_eq_right h, slice_bit (show j-1 < v by omega)]
        rw [ite_eq_right (show k+j ≠ 0 by omega), show k+(j-1)=k+j-1 by omega]
    · by_cases h : j+1=v
      · rw [ite_eq_left h, show k+j+1=k+v by omega]
      · rw [ite_eq_right h, slice_bit (show j+1 < v by omega)]
        rw [ite_eq_right (show k+j+1 ≠ w by omega), Nat.add_assoc]
  · have le : 2^v ≤ 2^j := Nat.pow_le_pow_right (by decide : 0<2) (by omega)
    have left : slice v k (stripStep w l r s) < 2^j :=
      Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos v)) le
    have right := Nat.lt_of_lt_of_le (stripStep_lt v
      (if k = 0 then l else s.testBit (k-1))
      (if k+v = w then r else s.testBit (k+v)) (slice v k s)) le
    rw [Nat.testBit_lt_two_pow left, Nat.testBit_lt_two_pow right]

theorem slice_run {w v k m : Nat} {a x : Nat → Nat} (hk : k+v ≤ w)
    (run : Run w m a x) : Run v m (fun j => a (k+j)) (fun t => slice v k (x t)) := by
  refine ⟨fun _ => Nat.mod_lt _ (Nat.two_pow_pos v), fun t => ?_⟩
  obtain ⟨l,r,lr⟩ := mem_successors.mp (run.edge t).1
  refine ⟨mem_successors.mpr ⟨_,_,lr ▸ slice_step hk (run.bounded t) l r⟩,
    (fits_iff _ _ _).mpr ?_⟩
  intro j on off
  by_cases hj : j < v
  · rw [slice_bit hj] at on off
    have e := (fits_iff _ _ _).mp (run.edge t).2 (k+j) on off
    rw [permit_bit, decide_eq_true_eq] at e ⊢
    exact ⟨hj,e.2⟩
  · have no : (slice v k (x t)).testBit j = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos v))
        (Nat.pow_le_pow_right (by decide : 0<2) (by omega : v ≤ j)))
    simp [no] at on

theorem pair_bits {s d j : Nat} (h : (s >>> j) % 4 = (d >>> j) % 4) :
    s.testBit j = d.testBit j ∧ s.testBit (j+1) = d.testBit (j+1) := by
  change (s >>> j)%(2^2) = (d >>> j)%(2^2) at h
  constructor
  · simpa only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.add_zero,
      decide_eq_true (by decide : 0<2), Bool.true_and] using
      congrArg (fun n : Nat => n.testBit 0) h
  · simpa only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
      decide_eq_true (by decide : 1<2), Bool.true_and] using
      congrArg (fun n : Nat => n.testBit 1) h

private theorem pair_eq_of_bits {s d j : Nat} (h₁ : s.testBit j = d.testBit j)
    (h₂ : s.testBit (j+1) = d.testBit (j+1)) : (s >>> j)%4 = (d >>> j)%4 := by
  change (s >>> j)%(2^2) = (d >>> j)%(2^2)
  apply Nat.eq_of_testBit_eq
  intro k
  cases k with
  | zero => simpa only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.add_zero,
      decide_eq_true (by decide : 0<2), Bool.true_and] using h₁
  | succ k =>
    cases k with
    | zero => simpa only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
        decide_eq_true (by decide : 1<2), Bool.true_and] using h₂
    | succ k =>
      simp only [Nat.testBit_mod_two_pow, decide_eq_false (show ¬ (k+1+1 < 2) by omega), Bool.false_and]

/-- A certificate on any contiguous substrip supplies a pair in the full strip. -/
theorem good_of_slice {w v k m : Nat} {a : Nat → Nat} (hk : k+v ≤ w)
    (good : Good v m (fun j => a (k+j))) : Good w m a := by
  intro x hx
  obtain ⟨j,N,hj,h⟩ := good _ (slice_run hk hx)
  refine ⟨k+j,N,by omega,fun t ht => ?_⟩
  obtain ⟨p,q⟩ := pair_bits (h t ht)
  rw [slice_bit (show j < v by omega), slice_bit (show j < v by omega)] at p
  rw [slice_bit hj, slice_bit hj, ← Nat.add_assoc] at q
  exact pair_eq_of_bits p q

end Ruliology.CellularAutomata.Rule30FallResidues

namespace Ruliology.CellularAutomata.Rule30FallResidues

open Ruliology.CellularAutomata Rule30StripCertificates

/-- A rank identifies an adjacent pair and its reading at each tick of a period. -/
structure Certificate where
  labels : List Nat
  ranks : Array Nat
  reads : Array Nat

def label (c : Certificate) (j : Nat) : Nat := c.labels.getD j 0

def rankAt (packed s : Nat) : Nat := (packed >>> (6*s)) % 64

def readPair (g : Nat) : Nat := g % 8

def prediction (g p : Nat) : Nat := (g >>> (3+2*p)) % 4

def layer (w a p here next : Nat) (reads : Array Nat) : Bool :=
  (List.range (2^w)).all fun s =>
    let rk := rankAt here s
    let word := reads.getD rk 0
    let j := readPair word
    (j+1 < w && (s >>> j)%4 == prediction word p) &&
      (successors w s).all fun d => !(fits a s d) || rankAt next d ≤ rk

def check (w m : Nat) (c : Certificate) : Bool :=
  (List.range m).all fun p => layer w (permit w (label c) p) p
    (c.ranks.getD p 0) (c.ranks.getD ((p+1)%m) 0) c.reads

private theorem node {w m : Nat} {c : Certificate} (ok : check w m c = true)
    {p s : Nat} (hp : p < m) (hs : s < 2^w) :
    let rk := rankAt (c.ranks.getD p 0) s
    let word := c.reads.getD rk 0
    let j := readPair word
    (j+1 < w ∧ (s >>> j)%4 = prediction word p) ∧
      ∀ d, Edge w (permit w (label c) p) s d →
        rankAt (c.ranks.getD ((p+1)%m) 0) d ≤ rk := by
  have yes := List.all_eq_true.mp (List.all_eq_true.mp ok p (List.mem_range.mpr hp))
    s (List.mem_range.mpr hs)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at yes
  refine ⟨yes.1,fun d hd => ?_⟩
  have h := List.all_eq_true.mp yes.2 d hd.1
  simpa [hd.2] using h

theorem good_of_check {w m : Nat} {c : Certificate} (hm : 0 < m) (ok : check w m c = true) :
    Good w m (label c) := by
  intro x hx
  let rk (t : Nat) := rankAt (c.ranks.getD (t%m) 0) (x t)
  let g (t : Nat) := c.reads.getD (rk t) 0
  have reads (t : Nat) : (readPair (g t))+1 < w ∧
      (x t >>> readPair (g t))%4 = prediction (g t) (t%m) :=
    (node ok (Nat.mod_lt _ hm) (hx.bounded t)).1
  have noninc (t : Nat) : rk (t+1) ≤ rk t := by
    have he : (t%m+1)%m=(t+1)%m := by
      calc (t%m+1)%m = (t%m+1%m)%m := by rw [Nat.add_mod (t%m) 1 m, Nat.mod_mod]
        _ = (t+1)%m := (Nat.add_mod t 1 m).symm
    simpa only [rk,he] using
      (node ok (Nat.mod_lt _ hm) (hx.bounded t)).2 _ (hx.edge t)
  obtain ⟨N,_,stable⟩ := antitone_eventually_const rk 0 (fun t _ => noninc t)
  refine ⟨readPair (g N),N,(reads N).1,fun t ht => ?_⟩
  have eq (u : Nat) (hu : N ≤ u) : g u = g N := congrArg (fun k => c.reads.getD k 0) (stable u hu)
  have a := (reads t).2
  have b := (reads (t+m)).2
  rw [eq t ht] at a
  rw [eq (t+m) (by omega), Nat.add_mod_right] at b
  exact b.trans a.symm

end Ruliology.CellularAutomata.Rule30FallResidues

/-! A failure of the adjacent-pair conclusion on a strip forces failure on
its two immediate substrips. Generate just the compatible extensions. -/
namespace Ruliology.CellularAutomata.Rule30FallResidues

def labelsOf (w : Nat) (a : Nat → Nat) := (List.range w).map a

def norm (m : Nat) (xs : List Nat) : List Nat :=
  xs.map (rotate m (xs.headD 0))

def extend (m : Nat) (bad : List (List Nat)) : List (List Nat) :=
  bad.flatMap fun xs => (List.range m).filterMap fun p =>
    let ys := xs ++ [p]
    if bad.contains (norm m ys.tail) then some ys else none

def ruledOut (m : Nat) (previous remaining : List (List Nat)) : List (List Nat) :=
  (extend m previous).filter (fun xs => !(remaining.contains xs))

def pairs (m : Nat) := (List.range m).map fun q => [0,q]

abbrev Valid (w m : Nat) (a : Nat → Nat) := ∀ j, j < w → a j < m

def Classifies (w m : Nat) (bad : List (List Nat)) : Prop :=
  ∀ a, Valid w m a → a 0 = 0 → Good w m a ∨ labelsOf w a ∈ bad

theorem pairs_classify (m : Nat) : Classifies 2 m (pairs m) := by
  intro a ha zero
  exact Or.inr (List.mem_map.mpr ⟨a 1,List.mem_range.mpr (ha 1 (by decide)),by
    simp [labelsOf, zero, show List.range 2 = [0,1] by decide]⟩)

theorem good_congr {w m : Nat} {a b : Nat → Nat}
    (h : ∀ j, j < w → a j = b j) (good : Good w m a) : Good w m b := by
  intro x hx
  apply good x
  refine ⟨hx.bounded,fun t => ?_⟩
  have eq : permit w a (t%m) = permit w b (t%m) := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [permit_bit,permit_bit]
    by_cases hj : j < w
    · rw [h j hj]
    · simp [hj]
  rw [eq]
  exact hx.edge t

private theorem sound_label {c : Certificate} {w : Nat} {a : Nat → Nat} (h : c.labels = labelsOf w a)
    (j : Nat) (hj : j < w) : label c j = a j := by
  unfold label
  rw [h,List.getD_eq_getElem?_getD]
  have bound : j < (List.range w).length := by simpa using hj
  simp only [labelsOf,List.getElem?_map,List.getElem?_eq_getElem bound,List.getElem_range,Option.map_some,Option.getD_some]

private theorem phase_extend {w m : Nat} {a : Nat → Nat} {bad : List (List Nat)} (hw : 0 < w)
    (leftWord : labelsOf w a ∈ bad)
    (rightWord : labelsOf w (fun j => rotate m (a 1) (a (j+1))) ∈ bad) (last : a w < m) :
    labelsOf (w+1) a ∈ extend m bad := by
  have endWord : labelsOf w a ++ [a w] = labelsOf (w+1) a := by
    simp only [labelsOf,List.range_succ (n:=w),List.map_append,List.map_cons,List.map_nil]
  have tailWord : norm m (labelsOf (w+1) a).tail =
      labelsOf w (fun j => rotate m (a 1) (a (j+1))) := by
    have head : ((List.range w).map (fun j => a (j+1))).headD 0 = a 1 := by
      obtain ⟨v,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : w ≠ 0)
      simp [List.range_succ_eq_map]
    simp only [labelsOf,List.range_succ_eq_map (n:=w),List.map_cons,List.tail_cons,
      List.map_map,Function.comp_def,Nat.succ_eq_add_one,norm,head]
  apply List.mem_flatMap.mpr
  refine ⟨labelsOf w a,leftWord,List.mem_filterMap.mpr ⟨a w,List.mem_range.mpr last,?_⟩⟩
  simp [endWord,tailWord,rightWord]

theorem classify_step {w m : Nat} {previous remaining : List (List Nat)} {cs : List Certificate}
    (hw : 0 < w) (hm : 0 < m)
    (prev : Classifies w m previous)
    (certs : cs.all (check (w+1) m) = true)
    (complete : ruledOut m previous remaining = cs.map Certificate.labels) :
    Classifies (w+1) m remaining := by
  intro a ha zero
  rcases prev a (fun j h => ha j (by omega)) zero with good | leftWord
  · exact Or.inl (good_of_slice (k:=0) (v:=w) (w:=w+1) (by omega) (by simpa using good))
  have ha1 := ha 1 (by omega)
  let b (j : Nat) := rotate m (a 1) (a (j+1))
  have hb : Valid w m b := fun j hj => rotate_lt ha1 (ha (j+1) (by omega))
  have b0 : b 0 = 0 := by simp [b,rotate]
  rcases prev b hb b0 with good | rightWord
  · have good' := good_of_rotated ha1 (fun j hj => ha (1+j) (by omega))
      (show Good w m (fun j => rotate m (a 1) (a (1+j))) by simpa [b,Nat.add_comm] using good)
    exact Or.inl (good_of_slice (k:=1) (w:=w+1) (by omega) good')
  by_cases bad : labelsOf (w+1) a ∈ remaining
  · exact Or.inr bad
  have h := phase_extend hw leftWord rightWord (ha w (by omega))
  have member : labelsOf (w+1) a ∈ ruledOut m previous remaining := by
    unfold ruledOut
    exact List.mem_filter.mpr ⟨h,by simp [List.contains_eq_mem,bad]⟩
  rw [complete] at member
  obtain ⟨c,hc,eq⟩ := List.mem_map.mp member
  exact Or.inl (good_congr (sound_label eq) (good_of_check hm (List.all_eq_true.mp certs c hc)))

theorem of_empty {m : Nat} (classified : Classifies 6 m []) {a : Nat → Nat} (ha : Valid 6 m a) : Good 6 m a := by
  have h0 := ha 0 (by decide)
  apply good_of_rotated h0 ha
  have e := classified (fun j => rotate m (a 0) (a j))
    (fun j hj => rotate_lt h0 (ha j hj)) (by simp [rotate])
  simpa only [List.not_mem_nil, or_false] using e

end Ruliology.CellularAutomata.Rule30FallResidues
