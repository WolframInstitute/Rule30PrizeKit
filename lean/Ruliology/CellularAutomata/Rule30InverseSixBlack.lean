module

public import Ruliology.CellularAutomata.Rule30InverseSpatialPeriod

/-!
# Six black cells in a two-step Rule 30 image

Scan from right to left, carrying two successive predecessor registers.
After six black input letters, with arbitrary white gaps, the sixteen
possible initial registers have at most three distinct images. Five black
letters can leave four. The small certificate lists only subsets with
at least four surviving states. Each transition is checked by reduction.

`three_left_windows` applies this to finite pieces of physical rows with
arbitrary exterior. On the whole line, a nonconstant p-periodic target
can only have 2p-periodic two-tick ancestors. This rules out two successive
period doublings anywhere in such an ancestry. Spatial periodicity of an
output row is a distinct hypothesis from temporal periodicity at the center.

Contributed by Troy Lowry with OpenAI Codex.
-/

@[expose] public section
namespace Ruliology.CellularAutomata.Rule30InverseSixBlack
open Rule30Realization Rule30InverseSpatialPeriod

abbrev Reg := (Bool × Bool) × (Bool × Bool)
def jump (b : Bool) (s : Reg) : Reg :=
  let a := xor b (s.1.1 || s.1.2)
  ((a,s.1.1),(xor a (s.2.1 || s.2.2),s.2.1))
def scan (w : List Bool) (s : Reg) : Reg := w.foldl (fun q b => jump b q) s

def unpack (i : Nat) : Reg :=
  ((i.testBit 0,i.testBit 1),(i.testBit 2,i.testBit 3))
def allRegs := (List.range 16).map unpack
private theorem mem_all (s : Reg) : s ∈ allRegs := by
  obtain ⟨⟨a,b⟩,c,d⟩ := s
  cases a <;> cases b <;> cases c <;> cases d <;> decide
private def members (m : Nat) : List Reg := ((List.range 16).filter m.testBit).map unpack
private def entry (n : Nat) (ms : List Nat) := ms.map fun m => (n,members m)
private def table : List (Nat × List Reg) :=
  entry 0 [6281,6843,65535] ++ entry 1 [2600,6281,6825,16996,21111] ++
  entry 2 [2600,6281,6697,16996,20545,21093] ++
  entry 3 [2600,4233,6153,6273,6665,16996,20545,21089] ++
  entry 4 [612,2600,6664,16932,16992,20545,21088] ++ entry 5 [20545,21056]
private def next (s : List Reg) (b : Bool) :=
  allRegs.filter fun q => (s.map (jump b)).contains q
private theorem next_mem {s : List Reg} {q : Reg} (hq : q ∈ s) (b : Bool) :
    jump b q ∈ next s b := by
  apply List.mem_filter.mpr
  exact ⟨mem_all _,List.contains_iff_mem.mpr (List.mem_map.mpr ⟨q,hq,rfl⟩)⟩
private def cost (b : Bool) : Nat := if b then 1 else 0
private def ok (e : Nat × List Reg) (b : Bool) : Bool :=
  let v := next e.2 b
  decide (v.length≤3 ∨ (e.1+cost b,v) ∈ table)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
private theorem table_ok : table.all (fun e => ok e false && ok e true) = true := by decide
private theorem table_small : table.all (fun e => decide (e.1<6)) = true := by decide
private theorem next_ok {n s} (h : (n,s) ∈ table) (b : Bool) :
    (next s b).length≤3 ∨ (n+cost b,next s b)∈table := by
  have hz := List.all_eq_true.mp table_ok _ h
  simp only [Bool.and_eq_true] at hz
  cases b
  · exact of_decide_eq_true hz.1
  · exact of_decide_eq_true hz.2

private def Small (f : Reg → Reg) := ∃ s : List Reg, s.length≤3 ∧ ∀ q, f q∈s
private def Tracked (n : Nat) (f : Reg → Reg) := Small f ∨
  ∃ s : List Reg, (n,s)∈table ∧ ∀ q, f q ∈ s
private theorem advance {n f} (h : Tracked n f) (b : Bool) :
    Tracked (n+cost b) (fun q => jump b (f q)) := by
  rcases h with ⟨s,hs,hf⟩|⟨s,hs,hf⟩
  · exact Or.inl ⟨s.map (jump b),by simpa using hs,fun q => List.mem_map.mpr ⟨_,hf q,rfl⟩⟩
  · have hmem := fun q => next_mem (hf q) b
    rcases next_ok hs b with hlen|ht
    · exact Or.inl ⟨_,hlen,hmem⟩
    · exact Or.inr ⟨_,ht,hmem⟩

private theorem tracked_scan (w : List Bool) : Tracked (w.count true) (scan w) := by
  have run (v : List Bool) (n : Nat) (f : Reg → Reg) (h : Tracked n f) :
      Tracked (n+v.count true) (fun q => scan v (f q)) := by
    induction v generalizing n f with
    | nil => simpa [scan] using h
    | cons b xs ih =>
      have h' := ih _ _ (advance h b)
      cases b <;> simpa [scan,cost,List.count_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h'
  simpa using run w 0 id (Or.inr ⟨allRegs,by decide,mem_all⟩)

/-- Any number of white letters may be interspersed among the six black ones. -/
theorem six_black (w : List Bool) (hw : 6≤w.count true) :
    ∃ s : List Reg, s.length≤3 ∧ ∀ q, scan w q∈s := by
  rcases tracked_scan w with h|⟨s,hs,_⟩
  · exact h
  · have hh := of_decide_eq_true (List.all_eq_true.mp table_small _ hs)
    omega

/-- The numerical threshold six is sharp for arbitrary input words. -/
theorem five_black_sharp :
    ((allRegs.map (scan (List.replicate 5 true))).eraseDups).length=4 := by decide

private def regAt (x : Row) (j : Int) : Reg :=
  ((evol x 1 j,evol x 1 (j+1)),(x (j-1),x j))

private theorem jump_at (x : Row) (j : Int) :
    jump (evol x 2 j) (regAt x j)=regAt x (j-1) := by
  have h : xor (evol x 2 j) (evol x 1 j || evol x 1 (j+1))=evol x 1 (j-1) :=
    (rule_left _ _ _).symm
  have k : xor (evol x 1 (j-1)) (x (j-1) || x (j-1+1))=x (j-1-1) :=
    (rule_left _ _ _).symm
  simp only [show j-1+1=j by omega] at k
  simp only [jump,regAt,h,k,show j-1+1=j by omega]

def word (y : Row) (j : Int) (n : Nat) :=
  (List.range n).map fun (k : Nat) => y (j-k)
private theorem scan_at (x : Row) (j : Int) (n : Nat) :
    scan (word (evol x 2) j n) (regAt x j)=regAt x (j-n) := by
  induction n with
  | zero => simp [scan,word]
  | succ n ih =>
    have eq : word (evol x 2) j (n+1) = word (evol x 2) j n ++ [evol x 2 (j-n)] := by
      simp [word,List.range_succ]
    rw [eq]
    change (List.foldl _ _ _) = _
    simp only [List.foldl_append,List.foldl_cons,List.foldl_nil]
    change jump _ (scan _ _) = _
    rw [ih,jump_at,show j-((n+1:Nat):Int)=j-n-1 by omega]

private theorem word_add (y : Row) (j : Int) (a b : Nat) :
    word y j (a+b)=word y j a ++ word y (j-a) b := by
  simp only [word,List.range_add,List.map_append,List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp [Int.sub_sub]

private theorem rich {y : Row} (black : ∀ a : Int, ∃ j, a≤j ∧ y j=true)
    (a : Int) (k : Nat) : ∃ j n, a≤j-(n:Nat) ∧ k≤(word y j n).count true := by
  induction k with
  | zero => exact ⟨a,0,by simp,by omega⟩
  | succ k ih =>
    obtain ⟨j,n,hl,hn⟩ := ih
    obtain ⟨r,hr,hb⟩ := black (j+1)
    let d := (r-j).toNat
    have hd : r-(d:Int)=j := by dsimp [d]; omega
    have hx : true ∈ word y r d :=
      List.mem_map.mpr ⟨0,List.mem_range.mpr (by dsimp [d]; omega),by simpa using hb⟩
    have hh := List.count_pos_iff.mpr hx
    refine ⟨r,d+n,by omega,?_⟩
    rw [word_add,hd,List.count_append]
    omega

private def Duplicate {α : Type} (a b c d : α) :=
  a=b ∨ a=c ∨ a=d ∨ b=c ∨ b=d ∨ c=d

private theorem small_collision {s : List Reg} {a b c d : Reg} (hs : s.length≤3)
    (ha : a∈s) (hb : b∈s) (hc : c∈s) (hd : d∈s) : Duplicate a b c d := by
  have inj {u v : Reg} (hu : u∈s) (hv : v∈s) (e : s.idxOf u=s.idxOf v) : u=v := by
    have eu := List.getElem_idxOf (List.idxOf_lt_length_of_mem hu)
    have ev := List.getElem_idxOf (List.idxOf_lt_length_of_mem hv)
    grind
  have bound {u : Reg} (hu : u∈s) : s.idxOf u<3 := Nat.lt_of_lt_of_le (List.idxOf_lt_length_of_mem hu) hs
  have eqs : Duplicate (s.idxOf a) (s.idxOf b) (s.idxOf c) (s.idxOf d) := by
    have := bound ha; have := bound hb; have := bound hc; have := bound hd
    unfold Duplicate
    omega
  unfold Duplicate at *
  rcases eqs with e|e|e|e|e|e <;> solve
    | exact Or.inl (inj ha hb e)
    | exact Or.inr (Or.inl (inj ha hc e))
    | exact Or.inr (Or.inr (Or.inl (inj ha hd e)))
    | exact Or.inr (Or.inr (Or.inr (Or.inl (inj hb hc e))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (inj hb hd e)))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (inj hc hd e)))))

private theorem reg_left {x z : Row} (he : evol x 2=evol z 2) {j : Int}
    (h : regAt x j=regAt z j) (k : Int) (hk : k≤j) : x k=z k := by
  have hz := scan_at z j (j-k).toNat
  rw [← he,← h,scan_at,show j-((j-k).toNat:Int)=k by omega] at hz
  exact congrArg (fun s : Reg => s.2.2) hz

private theorem common_piece {x z : Row} {r : Int} {n m : Nat}
    (base : regAt x r=regAt z r)
    (h : word (evol x 2) r m=word (evol z 2) r m) (hn : n≤m) :
    x (r-n)=z (r-n) := by
  have takeWord (y : Row) : (word y r m).take n=word y r n := by
    rw [show m=n+(m-n) by omega,word_add]
    have hl : (word y r n).length=n := by simp [word]
    simpa only [hl] using (List.take_left (l₁:=word y r n) (l₂:=word y (r-n) (m-n)))
  have v := congrArg (List.take n) h
  simp only [takeWord] at v
  have H := scan_at x r n
  rw [v,base,scan_at] at H
  exact congrArg (fun s : Reg => s.2.2) H.symm

/-- If four two-step images share a finite window, and its rightmost `n`
cells contain six black cells, two of the four original rows have identical
left pieces all the way down to depth `m` beyond the scanned register. -/
theorem three_left_windows {r : Int} {n m : Nat} {w v : List Bool}
    (hw : 6≤w.count true) (a b c d : Row)
    (H : ∀ x ∈ [a,b,c,d], word (evol x 2) r n=w ∧ word (evol x 2) (r-n) m=v) :
    ∃ x ∈ [(a,b),(a,c),(a,d),(b,c),(b,d),(c,d)],
      ∀ k : Nat, k≤m → x.1 (r-n-k)=x.2 (r-n-k) := by
  obtain ⟨s,hs,hm⟩ := six_black _ hw
  have inside (x : Row) (hx : x∈[a,b,c,d]) : regAt x (r-n)∈s := by
    have h := scan_at x r n
    rw [(H _ hx).1] at h
    exact h ▸ hm _
  have finish {x z : Row} (hx : x∈[a,b,c,d]) (hz : z∈[a,b,c,d])
      (e : regAt x (r-n)=regAt z (r-n)) :
      ∀ k : Nat, k≤m → x (r-n-k)=z (r-n-k) := fun _ hk =>
    common_piece e ((H _ hx).2.trans (H _ hz).2.symm) hk
  rcases small_collision hs (inside a (by simp)) (inside b (by simp)) (inside c (by simp))
      (inside d (by simp)) with e|e|e|e|e|e
  · exact ⟨(a,b),by simp,finish (by simp) (by simp) e⟩
  · exact ⟨(a,c),by simp,finish (by simp) (by simp) e⟩
  · exact ⟨(a,d),by simp,finish (by simp) (by simp) e⟩
  · exact ⟨(b,c),by simp,finish (by simp) (by simp) e⟩
  · exact ⟨(b,d),by simp,finish (by simp) (by simp) e⟩
  · exact ⟨(c,d),by simp,finish (by simp) (by simp) e⟩

/-- At most three two-tick ancestors on the whole line, provided the
target contains black cells arbitrarily far to the right. -/
theorem three_ancestors {y a b c d : Row}
    (hb : ∀ i : Int, ∃ j, i≤j ∧ y j=true)
    (A : evol a 2=y) (B : evol b 2=y) (C : evol c 2=y) (D : evol d 2=y) :
    a=b ∨ a=c ∨ a=d ∨ b=c ∨ b=d ∨ c=d := by
  classical
  apply Classical.byContradiction
  intro hn
  have w {v u : Row} (h : v ≠ u) : ∃ i, v i ≠ u i :=
    Classical.byContradiction fun he => h (funext fun i => Classical.byContradiction fun hh => he ⟨i,hh⟩)
  obtain ⟨i,hi⟩ := w (v:=a) (u:=b) (by grind)
  obtain ⟨j,hj⟩ := w (v:=a) (u:=c) (by grind)
  obtain ⟨k,hk⟩ := w (v:=a) (u:=d) (by grind)
  obtain ⟨l,hl⟩ := w (v:=b) (u:=c) (by grind)
  obtain ⟨m,hm⟩ := w (v:=b) (u:=d) (by grind)
  obtain ⟨n,hn'⟩ := w (v:=c) (u:=d) (by grind)
  obtain ⟨r,len,far,hw⟩ := rich hb (max i (max j (max k (max l (max m n))))) 6
  obtain ⟨s,hs,hmem⟩ := six_black _ hw
  have inside (x : Row) (h : evol x 2=y) : regAt x (r-len)∈s := by
    have H := scan_at x r len
    rw [h] at H
    exact H ▸ hmem (regAt x r)
  rcases small_collision hs (inside a A) (inside b B) (inside c C) (inside d D) with e|e|e|e|e|e
  · exact hi (reg_left (A.trans B.symm) e i (by omega))
  · exact hj (reg_left (A.trans C.symm) e j (by omega))
  · exact hk (reg_left (A.trans D.symm) e k (by omega))
  · exact hl (reg_left (B.trans C.symm) e l (by omega))
  · exact hm (reg_left (B.trans D.symm) e m (by omega))
  · exact hn' (reg_left (C.trans D.symm) e n (by omega))

private def shift (p : Nat) (x : Row) : Row := fun i => x (i+p)

private theorem commute (p : Nat) (x : Row) :
    evol (shift p x) 2=shift p (evol x 2) := by
  have h (v : Row) : evol (shift p v) 1=shift p (evol v 1) := funext (translated v p)
  change evol (evol (shift p x) 1) 1=_
  rw [h,h]
  rfl

/-- An arbitrary two-tick ancestor of a nonconstant p-periodic whole-line
row is already 2p-periodic. Two successive strict period doublings are impossible. -/
theorem period_two_step {x : Row} {p : Nat} (hp : 0<p) (h : Period (evol x 2) p)
    (hn : Nonconstant (evol x 2)) : Period x (2*p) := by
  have H := period_ancestor x 2 hp h hn
  have four : shift p (shift p (shift p (shift p x)))=x := by
    funext i
    change x (i+p+p+p+p)=x i
    rw [show i+p+p+p+p=i+((2^2*p:Nat):Int) by omega]
    exact H i
  have black : ∃ i, evol x 2 i=true := by
    obtain ⟨i,j,ne⟩ := hn
    cases hi : evol x 2 i <;> cases hj : evol x 2 j
    · exact False.elim (ne (hi.trans hj.symm))
    · exact ⟨j,hj⟩
    · exact ⟨i,hi⟩
    · exact ⟨i,hi⟩
  obtain ⟨i,hi⟩ := black
  have cy : shift p (evol x 2)=evol x 2 := funext h
  have A : evol (shift p x) 2=evol x 2 := (commute p x).trans cy
  have B : evol (shift p (shift p x)) 2=evol x 2 := by rw [commute,A,cy]
  have C : evol (shift p (shift p (shift p x))) 2=evol x 2 := by rw [commute,B,cy]
  have dup := three_ancestors (frequent_of_period hp h hi) (a:=x) rfl A B C
  have two : shift p (shift p x)=x := by
    rcases dup with e|e|e|e|e|e <;> grind
  intro j
  simpa [shift,Nat.two_mul,← Int.add_assoc] using congrFun two j

/-- A nonconstant p-periodic target, pulled back by `2*k` updates, has
only `2^k*p`-periodic ancestors. -/
theorem even_ancestor (x : Row) (k : Nat) {p : Nat} (hp : 0<p)
    (h : Period (evol x (2*k)) p) (hn : Nonconstant (evol x (2*k))) :
    Period x (2^k*p) := by
  induction k generalizing p with
  | zero => simpa [evol] using h
  | succ k ih =>
    rw [show 2*(k+1)=2*k+2 by omega] at h hn
    change Nonconstant (evol (evol x (2*k)) 2) at hn
    change Period (evol (evol x (2*k)) 2) p at h
    have nc : Nonconstant (evol x (2*k)) :=
      nonconstant_before (nonconstant_before (x:=evol (evol x (2*k)) 1) hn)
    have v := ih (p:=2*p) (by omega) (period_two_step hp h hn) nc
    simpa [Nat.pow_succ,Nat.mul_assoc] using v

end Ruliology.CellularAutomata.Rule30InverseSixBlack
